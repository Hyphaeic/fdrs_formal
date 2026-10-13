//! limb-schedule — product coefficients, defects and Christoffel schedules for multi-limb
//! arithmetic modulo `B − c`.
//!
//! Companion to the FDRS Lean development:
//! * §3.12 `CarryQuotient.lean`    — limb vectors modulo carries are `ℤ/(B − c)`;
//! * §3.13 `MixedRingProduct.lean` — product coefficients `κ(m,j) = B_m B_j / B_{m+j}`;
//! * §3.14 `ProductSpread.lean`    — the landing criterion `gcd(ε·B_t, M) | B_m B_j`;
//! * §3.23 `ChristoffelSchedule.lean` — the ceiling schedule `⌈q k / N⌉` is the unique
//!   power-of-two schedule whose product coefficients are all 1 or 2.
//!
//! Commands:
//!   table                              evaluation table for standard moduli
//!   sweep  --q Q --c C --word W        ceiling schedules for every limb count N
//!   check  --q Q --c C (--ceil N | --widths w0,w1,...) [--slack S] [--word W]
//!                                      analyse one power-of-two schedule
//!   verify [--max-n N]                 brute-force check of Theorems 174–175 and the cost law
//!   radices --r r0,r1,... --c C        general (non-power-of-two) ring: κ and landing

use std::collections::HashMap;
use std::env;

// ---------------------------------------------------------------------------------------
// Power-of-two schedules
// ---------------------------------------------------------------------------------------

/// A power-of-two limb schedule: bit positions `W_0 = 0 < W_1 < … < W_{N-1}` and lap `q`
/// (`W_{k+N} = W_k + q`). Limb `k` has width `W_{k+1} − W_k`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Schedule {
    q: i64,
    w: Vec<i64>,
}

impl Schedule {
    fn n(&self) -> usize {
        self.w.len()
    }

    /// The ceiling schedule `W_k = ⌈q k / N⌉`.
    fn ceiling(q: i64, n: usize) -> Self {
        let nn = n as i64;
        Schedule { q, w: (0..nn).map(|k| (q * k + nn - 1).div_euclid(nn)).collect() }
    }

    /// The schedule with the given limb widths (lap = sum of widths).
    fn from_widths(widths: &[i64]) -> Self {
        let mut w = Vec::with_capacity(widths.len());
        let mut acc = 0;
        for &x in widths {
            w.push(acc);
            acc += x;
        }
        Schedule { q: acc, w }
    }

    /// Bit position of place `k` on the periodic extension.
    fn pos(&self, k: usize) -> i64 {
        let n = self.n();
        self.w[k % n] + (k / n) as i64 * self.q
    }

    fn widths(&self) -> Vec<i64> {
        (0..self.n()).map(|k| self.pos(k + 1) - self.pos(k)).collect()
    }

    /// Defect `d(a,b) = W_a + W_b − W_{a+b}`; the product coefficient is `2^d`.
    fn defect(&self, a: usize, b: usize) -> i64 {
        self.pos(a) + self.pos(b) - self.pos(a + b)
    }

    fn defects(&self) -> Vec<i64> {
        let n = self.n();
        (0..n).flat_map(|m| (0..n).map(move |j| (m, j))).map(|(m, j)| self.defect(m, j)).collect()
    }

    fn min_defect(&self) -> i64 {
        self.defects().into_iter().min().unwrap()
    }

    fn max_defect(&self) -> i64 {
        self.defects().into_iter().max().unwrap()
    }

    fn product_closed(&self) -> bool {
        self.min_defect() >= 0
    }

    /// Number of partial products whose coefficient is not 1.
    fn scaled_products(&self) -> usize {
        self.defects().into_iter().filter(|&d| d != 0).count()
    }

    /// Largest column of a schoolbook product, in bits: every input limb at most
    /// `2^{width + slack}`, partial products scaled by `κ` and by `c` on wrap.
    fn column_bits(&self, c: i64, slack: i64) -> f64 {
        let n = self.n();
        let widths = self.widths();
        let mut worst = 0.0f64;
        for k in 0..n {
            let mut sum = 0.0f64;
            for m in 0..n {
                let j = (k + n - m) % n;
                let wrap = m + j >= n;
                let mut bits = self.defect(m, j) as f64
                    + (widths[m] + slack) as f64
                    + (widths[j] + slack) as f64;
                if wrap {
                    bits += (c.unsigned_abs() as f64).log2();
                }
                sum += bits.exp2();
            }
            worst = worst.max(sum.log2());
        }
        worst
    }
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/// The cost law: the ceiling schedule has `N²(b−1)/(2b)` scaled partial products,
/// `b = N / gcd(q, N)`. Returned as an exact fraction `(num, den)`.
fn cost_law(q: i64, n: usize) -> (u64, u64) {
    let nn = n as u64;
    let b = nn / gcd(q as u64, nn);
    let num = nn * nn * (b - 1);
    let den = 2 * b;
    let g = gcd(num, den).max(1);
    (num / g, den / g)
}

fn fmt_frac((a, b): (u64, u64)) -> String {
    if b == 1 {
        a.to_string()
    } else {
        format!("{a}/{b}")
    }
}

/// Widths as counts, largest first: `26×5 25×5`.
fn fmt_widths(w: &[i64]) -> String {
    let mut distinct: Vec<i64> = w.to_vec();
    distinct.sort_unstable_by(|a, b| b.cmp(a));
    distinct.dedup();
    distinct
        .iter()
        .map(|d| format!("{}×{}", d, w.iter().filter(|x| *x == d).count()))
        .collect::<Vec<_>>()
        .join(" ")
}

// ---------------------------------------------------------------------------------------
// Brute-force verification (Theorems 174–175, cost law)
// ---------------------------------------------------------------------------------------

#[derive(Default, Debug)]
struct VerifyStats {
    schedules: u64,
    product_closed: u64,
    unique_violations: u64,
    lower_violations: u64,
    upper_violations: u64,
    cost_law_violations: u64,
    cases: u64,
}

fn for_each_schedule(q: i64, n: usize, f: &mut dyn FnMut(&Schedule)) {
    fn rec(q: i64, n: usize, w: &mut Vec<i64>, f: &mut dyn FnMut(&Schedule)) {
        if w.len() == n {
            f(&Schedule { q, w: w.clone() });
            return;
        }
        let last = *w.last().unwrap();
        let remaining = (n - w.len()) as i64;
        // leave at least one bit for each remaining limb
        for next in (last + 1)..=(q - remaining) {
            w.push(next);
            rec(q, n, w, f);
            w.pop();
        }
    }
    let mut w = vec![0];
    rec(q, n, &mut w, f);
}

fn verify(max_n: usize) -> VerifyStats {
    let mut st = VerifyStats::default();
    for n in 2..=max_n {
        for q in (n as i64)..=(3 * n as i64 + 1) {
            st.cases += 1;
            let ceil = Schedule::ceiling(q, n);
            let (num, den) = cost_law(q, n);
            if den != 1 || ceil.scaled_products() as u64 != num {
                st.cost_law_violations += 1;
            }
            for_each_schedule(q, n, &mut |s| {
                st.schedules += 1;
                if !s.product_closed() {
                    return;
                }
                st.product_closed += 1;
                let delta = s.max_defect();
                if delta <= 1 && *s != ceil {
                    st.unique_violations += 1;
                }
                for k in 0..n {
                    let nk = n as i64 * s.w[k];
                    if nk < q * k as i64 {
                        st.lower_violations += 1;
                    }
                    if nk > q * k as i64 + (n as i64 - 1) * delta {
                        st.upper_violations += 1;
                    }
                }
            });
        }
    }
    st
}

// ---------------------------------------------------------------------------------------
// General rings (any radices): κ and the landing criterion
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Landing {
    /// Lands exactly with integer coefficient κ (times the wrap gain on wrap).
    Exact(u128),
    /// Not integral, but lands modulo M with coefficient x.
    Residue(u128),
    /// Blocked: gcd(ε B_t, M) does not divide B_m B_j.
    Blocked,
}

struct Ring {
    radices: Vec<u128>,
    c: i128,
}

fn gcd_u(a: u128, b: u128) -> u128 {
    if b == 0 {
        a
    } else {
        gcd_u(b, a % b)
    }
}

/// Extended Euclid on i128.
fn egcd(a: i128, b: i128) -> (i128, i128, i128) {
    if b == 0 {
        (a, 1, 0)
    } else {
        let (g, x, y) = egcd(b, a.rem_euclid(b));
        (g, y, x - (a.div_euclid(b)) * y)
    }
}

impl Ring {
    fn n(&self) -> usize {
        self.radices.len()
    }

    /// Place values `B_0..B_{2N}` of the periodic schedule.
    fn place_values(&self) -> Vec<u128> {
        let n = self.n();
        let mut b = vec![1u128];
        for k in 0..2 * n {
            let next = b[k].checked_mul(self.radices[k % n]).expect("place value overflow");
            b.push(next);
        }
        b
    }

    fn lap(&self) -> u128 {
        self.place_values()[self.n()]
    }

    fn modulus(&self) -> u128 {
        (self.lap() as i128 - self.c).unsigned_abs()
    }

    /// Where the product of places `m` and `j` lands (target `(m+j) mod N`).
    fn landing(&self, m: usize, j: usize) -> Landing {
        let n = self.n();
        let b = self.place_values();
        let idx = m + j;
        let t = idx % n;
        let num = b[m] * b[j];
        let den = b[idx];
        if num % den == 0 {
            return Landing::Exact(num / den);
        }
        let modulus = self.modulus();
        if modulus == 0 {
            return Landing::Blocked;
        }
        let mi = modulus as i128;
        let eps: i128 = if idx >= n { self.c } else { 1 };
        let a = (eps * b[t] as i128).rem_euclid(mi);
        let rhs = (num as i128).rem_euclid(mi);
        let g = gcd_u(a as u128, modulus) as i128;
        if g == 0 || rhs % g != 0 {
            return Landing::Blocked;
        }
        let m2 = mi / g;
        let (_, inv, _) = egcd((a / g).rem_euclid(m2), m2);
        let x = ((rhs / g) * inv).rem_euclid(m2);
        Landing::Residue(x as u128)
    }
}

// ---------------------------------------------------------------------------------------
// Command line
// ---------------------------------------------------------------------------------------

fn parse_args(args: &[String]) -> HashMap<String, String> {
    let mut map = HashMap::new();
    let mut i = 0;
    while i < args.len() {
        if let Some(key) = args[i].strip_prefix("--") {
            let val = args.get(i + 1).cloned().unwrap_or_default();
            map.insert(key.to_string(), val);
            i += 2;
        } else {
            i += 1;
        }
    }
    map
}

fn get_i64(map: &HashMap<String, String>, key: &str, default: i64) -> i64 {
    map.get(key).map(|v| v.parse().expect("integer argument")).unwrap_or(default)
}

fn parse_list<T: std::str::FromStr>(s: &str) -> Vec<T>
where
    T::Err: std::fmt::Debug,
{
    s.split(',').map(|x| x.trim().parse().expect("list of integers")).collect()
}

fn report_schedule(s: &Schedule, c: i64, slack: i64, word: i64) {
    let n = s.n();
    println!("q = {}, N = {}, c = {}", s.q, n, c);
    println!("widths          : {:?}", s.widths());
    println!("bit positions   : {:?}", s.w);
    let closed = s.product_closed();
    println!("product-closed  : {}", if closed { "yes" } else { "NO (some κ = 2^d with d < 0)" });
    println!("defect range    : [{}, {}]  (κ ∈ [2^{}, 2^{}])", s.min_defect(), s.max_defect(), s.min_defect(), s.max_defect());
    let ceil = Schedule::ceiling(s.q, n);
    if *s == ceil {
        println!("ceiling schedule: yes — the unique schedule with all κ ∈ {{1,2}} (Thm 175)");
    } else {
        println!("ceiling schedule: no (ceiling widths would be {:?})", ceil.widths());
        if closed {
            let above = (0..n).all(|k| s.w[k] >= ceil.w[k]);
            println!("above ceiling   : {} (Thm 174 predicts yes)", above);
        }
    }
    println!("scaled products : {} of {}", s.scaled_products(), n * n);
    println!("product coefficients κ·ε (row m, column j; ε = c on wrap):");
    for m in 0..n {
        let row: Vec<String> = (0..n)
            .map(|j| {
                let d = s.defect(m, j);
                let base = if d >= 0 { (1i64 << d).to_string() } else { format!("2^{d}") };
                if m + j >= n {
                    if d >= 0 {
                        ((1i64 << d) * c).to_string()
                    } else {
                        format!("{base}·{c}")
                    }
                } else {
                    base
                }
            })
            .collect();
        println!("  {:>2}: {}", m, row.join("\t"));
    }
    let bits = s.column_bits(c, slack);
    println!(
        "largest column  : {:.2} bits (input slack {} bits); accumulator {} bits: {}",
        bits,
        slack,
        2 * word,
        if bits <= (2 * word) as f64 { "fits" } else { "OVERFLOWS" }
    );
}

fn cmd_table() {
    let rows: &[(&str, i64, i64, usize, i64)] = &[
        ("Curve25519, 64-bit", 255, 19, 5, 64),
        ("Curve25519, 32-bit", 255, 19, 10, 32),
        ("Curve25519, 9 limbs", 255, 19, 9, 32),
        ("Curve25519, 11 limbs", 255, 19, 11, 32),
        ("Poly1305, 64-bit", 130, 5, 3, 64),
        ("Poly1305, 32-bit", 130, 5, 5, 32),
        ("M127 = 2^127-1, 64-bit", 127, 1, 3, 64),
        ("Curve41417, 64-bit", 414, 17, 8, 64),
        ("M-336 = 2^336-3, 64-bit", 336, 3, 7, 64),
        ("P-521 = 2^521-1, 64-bit", 521, 1, 9, 64),
        ("P-521 = 2^521-1, 32-bit", 521, 1, 19, 32),
    ];
    println!(
        "{:<26} {:>4} {:>3} {:>3}  {:<14} {:>9} {:>9} {:>8} {:>6}",
        "modulus / layout", "q", "c", "N", "ceiling widths", "scaled", "cost law", "col bits", "fits"
    );
    for &(name, q, c, n, word) in rows {
        let s = Schedule::ceiling(q, n);
        let bits = s.column_bits(c, 0);
        println!(
            "{:<26} {:>4} {:>3} {:>3}  {:<14} {:>9} {:>9} {:>8.1} {:>6}",
            name,
            q,
            c,
            n,
            fmt_widths(&s.widths()),
            format!("{}/{}", s.scaled_products(), n * n),
            fmt_frac(cost_law(q, n)),
            bits,
            if bits <= (2 * word) as f64 { "yes" } else { "no" }
        );
    }
    println!();
    println!("Real-world schedules that are not ceiling schedules:");
    let donna64 = Schedule::from_widths(&[44, 44, 42]);
    println!(
        "  poly1305-donna-64 (44,44,42): defects [{}, {}] → largest gain 2^{}·5 = {} (ceiling 44,43,43 would need at most 10)",
        donna64.min_defect(),
        donna64.max_defect(),
        donna64.max_defect(),
        (1 << donna64.max_defect()) * 5
    );
}

fn cmd_sweep(map: &HashMap<String, String>) {
    let q = get_i64(map, "q", 255);
    let c = get_i64(map, "c", 19);
    let word = get_i64(map, "word", 64);
    let slack = get_i64(map, "slack", 0);
    println!("Ceiling schedules for 2^{q} - {c}, {word}-bit limbs, input slack {slack} bits:");
    println!("{:>3}  {:<14} {:>9} {:>9} {:>9} {:>6}", "N", "widths", "scaled", "cost law", "col bits", "fits");
    let lo = (q + word - 1) / word;
    for n in lo.max(1)..=(lo * 4).min(64) {
        let n = n as usize;
        let s = Schedule::ceiling(q, n);
        let ws = s.widths();
        let (wmin, wmax) = (ws.iter().min().unwrap(), ws.iter().max().unwrap());
        if *wmax > word {
            continue;
        }
        let bits = s.column_bits(c, slack);
        println!(
            "{:>3}  {:<14} {:>9} {:>9} {:>9.1} {:>6}",
            n,
            if wmin == wmax { format!("{wmin}") } else { format!("{wmin}-{wmax}") },
            format!("{}/{}", s.scaled_products(), n * n),
            fmt_frac(cost_law(q, n)),
            bits,
            if bits <= (2 * word) as f64 { "yes" } else { "no" }
        );
    }
}

fn cmd_check(map: &HashMap<String, String>) {
    let c = get_i64(map, "c", 19);
    let slack = get_i64(map, "slack", 0);
    let word = get_i64(map, "word", 64);
    let s = if let Some(w) = map.get("widths") {
        Schedule::from_widths(&parse_list::<i64>(w))
    } else {
        let q = get_i64(map, "q", 255);
        let n = get_i64(map, "ceil", 10) as usize;
        Schedule::ceiling(q, n)
    };
    report_schedule(&s, c, slack, word);
}

fn cmd_verify(map: &HashMap<String, String>) {
    let max_n = get_i64(map, "max-n", 8) as usize;
    let st = verify(max_n);
    println!("Brute force over N = 2..{max_n}, q = N..3N+1 ({} cases):", st.cases);
    println!("  schedules enumerated          : {}", st.schedules);
    println!("  product-closed schedules      : {}", st.product_closed);
    println!("  Thm 175 (κ ≤ 2 ⇒ ceiling)     : {} violations", st.unique_violations);
    println!("  Thm 174 lower bound           : {} violations", st.lower_violations);
    println!("  Thm 174 upper bound           : {} violations", st.upper_violations);
    println!("  cost law N²(b−1)/(2b)         : {} violations", st.cost_law_violations);
}

fn cmd_radices(map: &HashMap<String, String>) {
    let radices = parse_list::<u128>(map.get("r").map(String::as_str).unwrap_or("2,3,2"));
    let c = get_i64(map, "c", -3) as i128;
    let ring = Ring { radices, c };
    let n = ring.n();
    let b = ring.place_values();
    println!("radices {:?}, wrap gain c = {}", ring.radices, c);
    println!("place values B_0..B_{} = {:?}", 2 * n, b);
    println!("lap B = {}, modulus M = |B − c| = {}", ring.lap(), ring.modulus());
    println!("landing of products (row m, column j): κ exact | ~x residue mod M | BLOCKED");
    for m in 0..n {
        let row: Vec<String> = (0..n)
            .map(|j| match ring.landing(m, j) {
                Landing::Exact(k) => format!("{k}"),
                Landing::Residue(x) => format!("~{x}"),
                Landing::Blocked => "BLOCKED".to_string(),
            })
            .collect();
        println!("  {:>2}: {}", m, row.join("\t"));
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let cmd = args.get(1).map(String::as_str).unwrap_or("table");
    let map = parse_args(&args[2.min(args.len())..]);
    match cmd {
        "table" => cmd_table(),
        "sweep" => cmd_sweep(&map),
        "check" => cmd_check(&map),
        "verify" => cmd_verify(&map),
        "radices" => cmd_radices(&map),
        _ => {
            eprintln!("usage: limb-schedule [table | sweep | check | verify | radices] [--options]");
            std::process::exit(2);
        }
    }
}

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn curve25519_ladder_is_ceiling() {
        let s = Schedule::from_widths(&[26, 25, 26, 25, 26, 25, 26, 25, 26, 25]);
        assert_eq!(s, Schedule::ceiling(255, 10));
        assert_eq!((s.min_defect(), s.max_defect()), (0, 1));
        assert_eq!(s.scaled_products(), 25);
    }

    #[test]
    fn theorems_174_175_small() {
        let st = verify(6);
        assert!(st.product_closed > 0);
        assert_eq!(st.unique_violations, 0);
        assert_eq!(st.lower_violations, 0);
        assert_eq!(st.upper_violations, 0);
        assert_eq!(st.cost_law_violations, 0);
    }

    #[test]
    fn cost_law_real_moduli() {
        for &(q, n) in &[(255, 10), (255, 5), (521, 9), (521, 19), (255, 12), (130, 3)] {
            let (num, den) = cost_law(q, n as usize);
            assert_eq!(den, 1);
            assert_eq!(Schedule::ceiling(q, n as usize).scaled_products() as u64, num);
        }
    }

    #[test]
    fn poly1305_donna64_has_defect_two() {
        let s = Schedule::from_widths(&[44, 44, 42]);
        assert!(s.product_closed());
        assert_eq!(s.max_defect(), 2); // the ×20 = 4·5 constant in poly1305-donna-64
        let ceil = Schedule::ceiling(130, 3);
        assert_eq!(ceil.widths(), vec![44, 43, 43]);
        assert_eq!(ceil.max_defect(), 1);
    }

    #[test]
    fn ring232_landing() {
        // §3.14 / §3.15 witnesses
        let r1 = Ring { radices: vec![2, 3, 2], c: 1 };
        assert_eq!(r1.modulus(), 11);
        assert_eq!(r1.landing(1, 1), Landing::Residue(8)); // 4/6 = 8 mod 11
        let r3 = Ring { radices: vec![2, 3, 2], c: 3 };
        assert_eq!(r3.modulus(), 9);
        assert_eq!(r3.landing(1, 1), Landing::Blocked); // gcd(6, 9) = 3 ∤ 4
        let r25519 = Ring { radices: vec![4, 2], c: 3 };
        assert!(matches!(r25519.landing(1, 1), Landing::Exact(_)));
    }
}
