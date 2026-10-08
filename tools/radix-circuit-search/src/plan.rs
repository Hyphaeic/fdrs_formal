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
//!   no twiddles (Corollary 33);
//! - `Rader` (extended grammar, prime `N`): a cyclic convolution of length `N − 1`
//!   through two DFTs of length `N − 1`;
//! - `Bluestein(M)` (extended grammar, any `N`): a chirp turns the DFT into a cyclic
//!   convolution of length `M ≥ 2N − 1`, through two DFTs of length `M` planned
//!   without Bluestein.
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
    Rader,
    Bluestein { m: usize },
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
    /// For the extended grammar: the grammar-only planner Bluestein draws its
    /// convolution lengths from.
    pub base: Option<Box<Planner>>,
}

pub fn is_prime(n: usize) -> bool {
    n >= 2 && (2..).take_while(|d| d * d <= n).all(|d| n % d != 0)
}

/// Smallest primitive root modulo a prime `p`.
pub fn primitive_root(p: usize) -> usize {
    let phi = p - 1;
    let mut fs = Vec::new();
    let mut m = phi;
    let mut d = 2;
    while d * d <= m {
        if m % d == 0 {
            fs.push(d);
            while m % d == 0 {
                m /= d;
            }
        }
        d += 1;
    }
    if m > 1 {
        fs.push(m);
    }
    let pow = |mut b: usize, mut e: usize| {
        let mut r = 1usize;
        b %= p;
        while e > 0 {
            if e & 1 == 1 {
                r = r * b % p;
            }
            b = b * b % p;
            e >>= 1;
        }
        r
    };
    (2..p).find(|&g| fs.iter().all(|&q| pow(g, phi / q) != 1)).unwrap_or(1)
}

/// Naive DFT of a numeric vector (used for Rader/Bluestein filter constants).
pub fn dft_numeric(v: &[C64]) -> Vec<C64> {
    let n = v.len();
    (0..n).map(|k| (0..n).fold(C64::ZERO, |acc, j| acc + root(n, j * k) * v[j])).collect()
}

/// Chirp scales `ζ_{2N}^{j²}` that are not 1, for `j < N`.
pub fn chirp_nontrivial(n: usize) -> usize {
    (0..n).filter(|&j| (j * j) % (2 * n) != 0).count()
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
        Planner { best, choice, base: None }
    }

    /// Grammar plus Rader (primes) and Bluestein (any length, convolution length
    /// `2N − 1 ≤ M ≤ 4N` from a grammar-only pass).
    pub fn run_extended(max: usize, lim: &Limits) -> Planner {
        let base = Planner::run(4 * max.max(2), lim);
        let mut pl = Planner::run(max, lim);
        for n in 3..=max {
            let mut cand: Vec<(usize, Choice)> = vec![(pl.best[n], pl.choice[n])];
            // splits again, now over extended sub-plans
            for n1 in 2..n {
                if n % n1 != 0 {
                    continue;
                }
                let n2 = n / n1;
                let sub = n1 * pl.best[n2] + n2 * pl.best[n1];
                cand.push((sub + twiddle_count(n1, n2), Choice::CT { n1 }));
                if gcd(n1, n2) == 1 {
                    cand.push((sub, Choice::PFA { n1 }));
                }
            }
            if is_prime(n) {
                cand.push((2 * pl.best[n - 1] + 2 * n - 1, Choice::Rader));
            }
            let chirp = 2 * chirp_nontrivial(n);
            if let Some((c, m)) = (2 * n - 1..=4 * n)
                .map(|m| (chirp + 2 * base.best[m] + m, m))
                .min()
            {
                cand.push((c, Choice::Bluestein { m }));
            }
            let (c, ch) = cand.into_iter().min_by_key(|&(c, _)| c).unwrap();
            pl.best[n] = c;
            pl.choice[n] = ch;
        }
        pl.base = Some(Box::new(base));
        pl
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
            Choice::Rader => self.build_rader(n, b, x),
            Choice::Bluestein { m } => self.build_bluestein(n, m, b, x),
        }
    }

    /// `X_{g^r} = x_0 + (a' ⊛ b)_r`, `a'_q = x_{g^{−q}}`, `b_t = ζ_p^{g^t}`; the cyclic
    /// convolution as `F^{-1}(F a' · F b)` with the inverse read off a forward DFT.
    fn build_rader(&self, p: usize, b: &mut Builder, x: &[usize]) -> Vec<usize> {
        let n = p - 1;
        let g = primitive_root(p);
        let mut gp = vec![1usize; n]; // g^q mod p
        for q in 1..n {
            gp[q] = gp[q - 1] * g % p;
        }
        let a: Vec<usize> = (0..n).map(|q| x[gp[(n - q) % n]]).collect();
        let fa = self.build(n, b, &a);
        let x0 = b.add(x[0], fa[0]);
        let bv: Vec<C64> = (0..n).map(|t| root(p, gp[t])).collect();
        let fb = dft_numeric(&bv);
        let inv = 1.0 / n as f64;
        let c: Vec<usize> = (0..n).map(|k| b.scale(C64::new(fb[k].re * inv, fb[k].im * inv), fa[k])).collect();
        let fc = self.build(n, b, &c);
        let mut out = vec![usize::MAX; p];
        out[0] = x0;
        for r in 0..n {
            out[gp[r]] = b.add(x[0], fc[(n - r) % n]);
        }
        out
    }

    /// `X_k = ζ_{2N}^{k²} Σ_j (ζ_{2N}^{j²} x_j) ζ_{2N}^{−(k−j)²}`, the linear convolution
    /// done cyclically at length `M`.
    fn build_bluestein(&self, n: usize, m: usize, b: &mut Builder, x: &[usize]) -> Vec<usize> {
        let base = self.base.as_ref().expect("Bluestein needs the base planner");
        let zero = b.zero();
        let mut u = vec![zero; m];
        for j in 0..n {
            let e = (j * j) % (2 * n);
            u[j] = if e == 0 { x[j] } else { b.scale(root(2 * n, e), x[j]) };
        }
        let fu = base.build(m, b, &u);
        let mut h = vec![C64::ZERO; m];
        for d in 0..n {
            let w = root(2 * n, (2 * n - (d * d) % (2 * n)) % (2 * n));
            h[d] = w;
            h[(m - d) % m] = w;
        }
        let fh = dft_numeric(&h);
        let inv = 1.0 / m as f64;
        let pv: Vec<usize> = (0..m).map(|k| b.scale(C64::new(fh[k].re * inv, fh[k].im * inv), fu[k])).collect();
        let fp = base.build(m, b, &pv);
        (0..n)
            .map(|k| {
                let v = fp[(m - k) % m];
                let e = (k * k) % (2 * n);
                if e == 0 { v } else { b.scale(root(2 * n, e), v) }
            })
            .collect()
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

    /// The plan as a Lean `Plan` term (fdrs.md Corollary 37), or `None` if it uses a
    /// move outside the proven grammar (dense `N > 2`, folded twiddles).
    pub fn lean_term(&self, n: usize) -> Option<String> {
        Some(match self.choice[n] {
            Choice::Identity => return None,
            Choice::Dense if n == 2 => ".two".to_string(),
            Choice::Dense | Choice::CTFold { .. } | Choice::Rader | Choice::Bluestein { .. } => {
                return None
            }
            Choice::Pair => format!("(.pair {})", (n - 1) / 2),
            Choice::CT { n1 } => format!("(.ct {} {})", self.lean_term(n1)?, self.lean_term(n / n1)?),
            Choice::PFA { n1 } => format!("(.pfa {} {})", self.lean_term(n1)?, self.lean_term(n / n1)?),
        })
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
            Choice::Rader => format!("Rader{n}({})", self.describe(n - 1)),
            Choice::Bluestein { m } => format!(
                "Bluestein{n}[{m}]({})",
                self.base.as_ref().map(|b| b.describe(m)).unwrap_or_default()
            ),
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
