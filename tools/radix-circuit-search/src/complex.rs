//! Minimal complex arithmetic (f64), enough to evaluate circuits numerically.

use std::f64::consts::PI;
use std::ops::{Add, Mul, Sub};

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct C64 {
    pub re: f64,
    pub im: f64,
}

impl C64 {
    pub const ZERO: C64 = C64 { re: 0.0, im: 0.0 };

    pub fn new(re: f64, im: f64) -> Self {
        C64 { re, im }
    }

    /// `e^{iθ}`.
    pub fn cis(theta: f64) -> Self {
        C64::new(theta.cos(), theta.sin())
    }

    pub fn abs(self) -> f64 {
        self.re.hypot(self.im)
    }
}

impl Add for C64 {
    type Output = C64;
    fn add(self, o: C64) -> C64 {
        C64::new(self.re + o.re, self.im + o.im)
    }
}

impl Sub for C64 {
    type Output = C64;
    fn sub(self, o: C64) -> C64 {
        C64::new(self.re - o.re, self.im - o.im)
    }
}

impl Mul for C64 {
    type Output = C64;
    fn mul(self, o: C64) -> C64 {
        C64::new(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)
    }
}

/// `ζ_n^e = exp(2πi e / n)` — the corpus sign convention (fdrs.md Phase 3 §1.1).
pub fn root(n: usize, e: usize) -> C64 {
    C64::cis(2.0 * PI * ((e % n) as f64) / (n as f64))
}
