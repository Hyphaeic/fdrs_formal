//! Plans for exact DFT circuits and the dynamic-programming planner.
//!
//! A plan for length `N` is one of
//! - `Dense`: every output a linear combination of all inputs (`±1` terms skip the
//!   scale gate);
//! - `Pair`: for odd `N = 2h + 1`, pair `x_j` with `x_{N-j}` — sums feed the cosine
//!   parts, differences the sine parts — `N² − 1` gates;
//! - `CT(n1)`: Cooley–Tukey on `N = n1 · n2` with explicit twiddles, trivial ones
//!   skipped (the staged transform of Theorem 120, one split at a time);
//! - `CTFold(n1)`: Cooley–Tukey with the twiddles folded into the outer combinations
//!   (Theorem 123's move);
//! - `PFA(n1)`: Good–Thomas on coprime `n1, n2` — residue chart in, Good's chart out,
//!   no twiddles (Corollary 33).
//!
//! The planner takes, for each `N`, the cheapest plan over all of these with the
//! best sub-plans — a search over ordered factorizations, i.e. over radix schedules
//! together with a chart (positional or residue) at every split.

use crate::circuit::{Builder, Coef};
use crate::complex::{root, C64};
use std::f64::consts::PI;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Choice {
    Identity,
    Dense,
    Pair,
    CT { n1: usize },
    CTFold { n1: usize },
    PFA { n1: usize },
}

pub struct Limits {
    pub dense_max: usize,
    pub pair_max: usize,
    pub fold_max: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Limits { dense_max: 64, pair_max: usize::MAX, fold_max: 16 }
    }
}

pub struct Planner {
    pub best: Vec<usize>,
    pub choice: Vec<Choice>,
}

pub fn gcd(a: usize, b: usize) -> usize {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/// Gates of the dense plan: output `k` starts from the `j = 0` term (coefficient 1)
/// and folds `j = 1, …, N−1`.
pub fn dense_cost(n: usize) -> usize {
    (0..n)
        .map(|k| (1..n).map(|j| Coef::of_root(n, j * k).fold_cost()).sum::<usize>())
        .sum()
}

/// `N² − 1` for odd `N` (checked against the builder in the tests).
pub fn pair_cost(n: usize) -> usize {
    assert!(n % 2 == 1);
    n * n - 1
}

/// Nontrivial twiddles of the split `N = n1 · n2`: pairs `(a, p)` with `N ∤ a p`.
pub fn twiddle_count(n1: usize, n2: usize) -> usize {
    let n = n1 * n2;
    let mut c = 0;
    for a in 0..n1 {
        for p in 0..n2 {
            if (a * p) % n != 0 {
                c += 1;
            }
        }
    }
    c
}

/// Gates of the folded outer combinations of the split `N = n1 · n2`.
pub fn fold_outer_cost(n1: usize, n2: usize) -> usize {
    let n = n1 * n2;
    (0..n)
        .map(|k| (1..n1).map(|a| Coef::of_root(n, a * k).fold_cost()).sum::<usize>())
        .sum()
}

impl Planner {
    pub fn run(max: usize, lim: &Limits) -> Planner {
        let mut best = vec![0usize; max + 1];
        let mut choice = vec![Choice::Identity; max + 1];
        for n in 2..=max {
            let mut cand: Vec<(usize, Choice)> = Vec::new();
            if n <= lim.dense_max {
                cand.push((dense_cost(n), Choice::Dense));
            }
            if n % 2 == 1 && n <= lim.pair_max {
                cand.push((pair_cost(n), Choice::Pair));
            }
            for n1 in 2..n {
                if n % n1 != 0 {
                    continue;
                }
                let n2 = n / n1;
                let sub = n1 * best[n2] + n2 * best[n1];
                cand.push((sub + twiddle_count(n1, n2), Choice::CT { n1 }));
                if n1 <= lim.fold_max {
                    cand.push((n1 * best[n2] + fold_outer_cost(n1, n2), Choice::CTFold { n1 }));
                }
                if gcd(n1, n2) == 1 {
                    cand.push((sub, Choice::PFA { n1 }));
                }
            }
            let (c, ch) = cand
                .into_iter()
                .min_by_key(|&(c, _)| c)
                .expect("no plan for this length (raise --dense-max or --pair-max)");
            best[n] = c;
            choice[n] = ch;
        }
        Planner { best, choice }
    }

    /// Emit the plan for length `n` on the given input addresses; outputs in
    /// natural frequency order.
    pub fn build(&self, n: usize, b: &mut Builder, x: &[usize]) -> Vec<usize> {
        assert_eq!(x.len(), n);
        match self.choice[n] {
            Choice::Identity => x.to_vec(),
            Choice::Dense => build_dense(n, b, x),
            Choice::Pair => build_pair(n, b, x),
            Choice::CT { n1 } => self.build_ct(n1, n / n1, b, x, false),
            Choice::CTFold { n1 } => self.build_ct(n1, n / n1, b, x, true),
            Choice::PFA { n1 } => self.build_pfa(n1, n / n1, b, x),
        }
    }

    /// `X[p + n2 q] = Σ_a ζ_{n1}^{aq} ζ_N^{ap} Σ_c ζ_{n2}^{cp} x[n1 c + a]`.
    fn build_ct(&self, n1: usize, n2: usize, b: &mut Builder, x: &[usize], fold: bool) -> Vec<usize> {
        let n = n1 * n2;
        // inner: n1 transforms of length n2
        let inner: Vec<Vec<usize>> = (0..n1)
            .map(|a| {
                let ya: Vec<usize> = (0..n2).map(|c| x[n1 * c + a]).collect();
                self.build(n2, b, &ya)
            })
            .collect();
        let mut out = vec![usize::MAX; n];
        if fold {
            for k in 0..n {
                let p = k % n2;
                let terms: Vec<(Coef, usize)> =
                    (0..n1).map(|a| (Coef::of_root(n, a * k), inner[a][p])).collect();
                out[k] = b.lincomb(&terms);
            }
        } else {
            for p in 0..n2 {
                let z: Vec<usize> = (0..n1)
                    .map(|a| {
                        let e = (a * p) % n;
                        if e == 0 {
                            inner[a][p]
                        } else {
                            b.scale(root(n, e), inner[a][p])
                        }
                    })
                    .collect();
                let o = self.build(n1, b, &z);
                for q in 0..n1 {
                    out[p + n2 * q] = o[q];
                }
            }
        }
        out
    }

    /// Ruritanian input `n = n2 a + n1 c (mod N)`, CRT output `k ≡ (k1, k2)`.
    fn build_pfa(&self, n1: usize, n2: usize, b: &mut Builder, x: &[usize]) -> Vec<usize> {
        let n = n1 * n2;
        let inner: Vec<Vec<usize>> = (0..n1)
            .map(|a| {
                let ya: Vec<usize> = (0..n2).map(|c| x[(n2 * a + n1 * c) % n]).collect();
                self.build(n2, b, &ya)
            })
            .collect();
        let mut out = vec![usize::MAX; n];
        for k2 in 0..n2 {
            let z: Vec<usize> = (0..n1).map(|a| inner[a][k2]).collect();
            let o = self.build(n1, b, &z);
            for k1 in 0..n1 {
                // the k < N with k ≡ k1 (mod n1), k ≡ k2 (mod n2)
                let k = (0..n).find(|&k| k % n1 == k1 && k % n2 == k2).unwrap();
                out[k] = o[k1];
            }
        }
        out
    }

    /// The plan tree, e.g. `PFA(P3, CT(P3, P3))`.
    pub fn describe(&self, n: usize) -> String {
        match self.choice[n] {
            Choice::Identity => "1".to_string(),
            Choice::Dense => format!("D{n}"),
            Choice::Pair => format!("P{n}"),
            Choice::CT { n1 } => format!("CT({}, {})", self.describe(n1), self.describe(n / n1)),
            Choice::CTFold { n1 } => format!("CTF({}, {})", self.describe(n1), self.describe(n / n1)),
            Choice::PFA { n1 } => format!("PFA({}, {})", self.describe(n1), self.describe(n / n1)),
        }
    }
}

pub fn build_dense(n: usize, b: &mut Builder, x: &[usize]) -> Vec<usize> {
    (0..n)
        .map(|k| {
            let terms: Vec<(Coef, usize)> = (0..n).map(|j| (Coef::of_root(n, j * k), x[j])).collect();
            b.lincomb(&terms)
        })
        .collect()
}

pub fn build_pair(n: usize, b: &mut Builder, x: &[usize]) -> Vec<usize> {
    let h = (n - 1) / 2;
    let s: Vec<usize> = (1..=h).map(|j| b.add(x[j], x[n - j])).collect();
    let d: Vec<usize> = (1..=h).map(|j| b.sub(x[j], x[n - j])).collect();
    let mut out = vec![usize::MAX; n];
    let mut t0 = vec![(Coef::One, x[0])];
    t0.extend(s.iter().map(|&a| (Coef::One, a)));
    out[0] = b.lincomb(&t0);
    for m in 1..=h {
        let mut ta = vec![(Coef::One, x[0])];
        ta.extend((1..=h).map(|j| {
            let th = 2.0 * PI * ((m * j) % n) as f64 / n as f64;
            (Coef::General(C64::new(th.cos(), 0.0)), s[j - 1])
        }));
        let tb: Vec<(Coef, usize)> = (1..=h)
            .map(|j| {
                let th = 2.0 * PI * ((m * j) % n) as f64 / n as f64;
                (Coef::General(C64::new(0.0, th.sin())), d[j - 1])
            })
            .collect();
        let a = b.lincomb(&ta);
        let bb = b.lincomb(&tb);
        out[m] = b.add(a, bb);
        out[n - m] = b.sub(a, bb);
    }
    out
}
