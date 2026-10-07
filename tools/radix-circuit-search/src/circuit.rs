//! Family 130's gate model (fdrs.md Definition 216): add, subtract, and scale by a
//! predetermined constant each cost one gate; the `n` inputs sit at addresses
//! `0..n`, the constant `0` at address `n`, and gate `j` at `n + 1 + j`. Outputs
//! are named addresses, so permutations and fan-out are free.

use crate::complex::{root, C64};

#[derive(Clone, Copy, Debug)]
pub enum Gate {
    Add(usize, usize),
    Sub(usize, usize),
    Scale(C64, usize),
}

/// A coefficient, classified so that `±1` never costs a scale gate.
#[derive(Clone, Copy, Debug)]
pub enum Coef {
    One,
    MinusOne,
    General(C64),
}

impl Coef {
    /// The class of `ζ_n^e`.
    pub fn of_root(n: usize, e: usize) -> Coef {
        let e = e % n;
        if e == 0 {
            Coef::One
        } else if 2 * e == n {
            Coef::MinusOne
        } else {
            Coef::General(root(n, e))
        }
    }

    /// Gates needed to fold one further term with this coefficient into a running sum.
    pub fn fold_cost(self) -> usize {
        match self {
            Coef::One | Coef::MinusOne => 1,
            Coef::General(_) => 2,
        }
    }
}

pub struct Builder {
    n_inputs: usize,
    gates: Vec<Gate>,
}

impl Builder {
    pub fn new(n_inputs: usize) -> Self {
        Builder { n_inputs, gates: Vec::new() }
    }

    fn push(&mut self, g: Gate) -> usize {
        self.gates.push(g);
        self.n_inputs + self.gates.len()
    }

    pub fn add(&mut self, a: usize, b: usize) -> usize {
        self.push(Gate::Add(a, b))
    }

    pub fn sub(&mut self, a: usize, b: usize) -> usize {
        self.push(Gate::Sub(a, b))
    }

    pub fn scale(&mut self, c: C64, a: usize) -> usize {
        self.push(Gate::Scale(c, a))
    }

    /// `Σ c_j · v(a_j)`. Starts from a `+1` term when there is one (free), then folds
    /// each further term with one gate for `±1` and two otherwise.
    pub fn lincomb(&mut self, terms: &[(Coef, usize)]) -> usize {
        assert!(!terms.is_empty(), "empty linear combination");
        let start = terms.iter().position(|(c, _)| matches!(c, Coef::One)).unwrap_or(0);
        let mut acc = match terms[start] {
            (Coef::One, a) => a,
            (Coef::MinusOne, a) => self.scale(C64::new(-1.0, 0.0), a),
            (Coef::General(c), a) => self.scale(c, a),
        };
        for (j, &(c, a)) in terms.iter().enumerate() {
            if j == start {
                continue;
            }
            acc = match c {
                Coef::One => self.add(acc, a),
                Coef::MinusOne => self.sub(acc, a),
                Coef::General(w) => {
                    let t = self.scale(w, a);
                    self.add(acc, t)
                }
            };
        }
        acc
    }

    pub fn finish(self, outputs: Vec<usize>) -> Program {
        Program { n_inputs: self.n_inputs, gates: self.gates, outputs }
    }
}

pub struct Program {
    pub n_inputs: usize,
    pub gates: Vec<Gate>,
    pub outputs: Vec<usize>,
}

impl Program {
    pub fn size(&self) -> usize {
        self.gates.len()
    }

    /// Evaluate with the topological-order check of the model: every gate reads only
    /// the inputs, the constant, and earlier gates.
    pub fn eval(&self, x: &[C64]) -> Vec<C64> {
        assert_eq!(x.len(), self.n_inputs);
        let mut v: Vec<C64> = Vec::with_capacity(self.n_inputs + 1 + self.gates.len());
        v.extend_from_slice(x);
        v.push(C64::ZERO);
        for g in &self.gates {
            let avail = v.len();
            let r = match *g {
                Gate::Add(a, b) => {
                    assert!(a < avail && b < avail);
                    v[a] + v[b]
                }
                Gate::Sub(a, b) => {
                    assert!(a < avail && b < avail);
                    v[a] - v[b]
                }
                Gate::Scale(c, a) => {
                    assert!(a < avail);
                    c * v[a]
                }
            };
            v.push(r);
        }
        self.outputs.iter().map(|&o| v[o]).collect()
    }
}
