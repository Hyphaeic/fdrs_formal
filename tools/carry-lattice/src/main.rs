//! Carry routes on the radix lattice of two schedules (fdrs.md §3.8).
//!
//! `x` in schedule `b`, `y` in schedule `c`; the outer digit product lives on the
//! grid of cells `(i, j)` with weight `B_i · C_j`. Row lines `(i,j) → (i+1,j)` have
//! ratio `b_i`, column lines `(i,j) → (i,j+1)` ratio `c_j`. Every route conserves the
//! value (Theorem 137); the ledger (Theorem 138) records how much moved on each line.

use std::collections::BTreeMap;

type Grid = Vec<Vec<u128>>;
type Line = ((usize, usize), (usize, usize), u128);

fn parse_list(s: &str) -> Vec<u128> {
    s.split(',').map(|t| t.trim().parse().expect("number list")).collect()
}

fn place_values(b: &[u128], n: usize) -> Vec<u128> {
    let mut p = vec![1u128; n + 1];
    for i in 0..n {
        p[i + 1] = p[i] * b[i % b.len()];
    }
    p
}

fn radix(b: &[u128], i: usize) -> u128 {
    b[i % b.len()]
}

fn digits(mut v: u128, b: &[u128]) -> Vec<u128> {
    let mut d = Vec::new();
    let mut i = 0;
    while v > 0 || d.is_empty() {
        d.push(v % radix(b, i));
        v /= radix(b, i);
        i += 1;
    }
    d
}

struct Lattice {
    pb: Vec<u128>,
    pc: Vec<u128>,
    b: Vec<u128>,
    c: Vec<u128>,
    d: Grid,
    ledger: BTreeMap<String, u128>,
}

impl Lattice {
    fn value(&self) -> u128 {
        let mut v = 0;
        for (i, row) in self.d.iter().enumerate() {
            for (j, &x) in row.iter().enumerate() {
                v += x * self.pb[i] * self.pc[j];
            }
        }
        v
    }
    fn carry(&mut self, l: Line) {
        let ((i, j), (i2, j2), rho) = l;
        let q = self.d[i][j] / rho;
        if q == 0 {
            return;
        }
        self.d[i][j] %= rho;
        self.d[i2][j2] += q;
        let key = if i2 > i { format!("row ({i},{j})→({i2},{j2}) ρ={rho}") } else {
            format!("col ({i},{j})→({i2},{j2}) ρ={rho}")
        };
        *self.ledger.entry(key).or_insert(0) += q;
    }
    fn row_line(&self, i: usize, j: usize) -> Line {
        ((i, j), (i + 1, j), radix(&self.b, i))
    }
    fn col_line(&self, i: usize, j: usize) -> Line {
        ((i, j), (i, j + 1), radix(&self.c, j))
    }
}

fn build(b: &[u128], c: &[u128], x: u128, y: u128) -> Lattice {
    let dx = digits(x, b);
    let dy = digits(y, c);
    // one spare row and column receive the overflow
    let (ni, nj) = (dx.len() + 1, dy.len() + 1);
    let mut d = vec![vec![0u128; nj]; ni];
    for (i, &xi) in dx.iter().enumerate() {
        for (j, &yj) in dy.iter().enumerate() {
            d[i][j] = xi * yj;
        }
    }
    Lattice { pb: place_values(b, ni), pc: place_values(c, nj), b: b.to_vec(), c: c.to_vec(), d,
        ledger: BTreeMap::new() }
}

/// Route: sweep every column along the b-lines, then the top row along the c-lines.
fn route_rows(l: &mut Lattice) {
    let (ni, nj) = (l.d.len(), l.d[0].len());
    for j in 0..nj {
        for i in 0..ni - 1 {
            let e = l.row_line(i, j);
            l.carry(e);
        }
    }
    for j in 0..nj - 1 {
        let e = l.col_line(ni - 1, j);
        l.carry(e);
    }
}

/// Route: sweep every row along the c-lines, then the last column along the b-lines.
fn route_cols(l: &mut Lattice) {
    let (ni, nj) = (l.d.len(), l.d[0].len());
    for i in 0..ni {
        for j in 0..nj - 1 {
            let e = l.col_line(i, j);
            l.carry(e);
        }
    }
    for i in 0..ni - 1 {
        let e = l.row_line(i, nj - 1);
        l.carry(e);
    }
}

/// Route: alternate one row step and one column step from every cell, repeated until
/// nothing moves (each cell sheds along the line with the smaller ratio first).
fn route_greedy(l: &mut Lattice) {
    let (ni, nj) = (l.d.len(), l.d[0].len());
    loop {
        let before = l.d.clone();
        for i in 0..ni {
            for j in 0..nj {
                let rb = if i + 1 < ni { Some(radix(&l.b, i)) } else { None };
                let rc = if j + 1 < nj { Some(radix(&l.c, j)) } else { None };
                match (rb, rc) {
                    (Some(p), Some(q)) if p <= q => { let e = l.row_line(i, j); l.carry(e); }
                    (Some(_), Some(_)) => { let e = l.col_line(i, j); l.carry(e); }
                    (Some(_), None) => { let e = l.row_line(i, j); l.carry(e); }
                    (None, Some(_)) => { let e = l.col_line(i, j); l.carry(e); }
                    (None, None) => {}
                }
            }
        }
        if l.d == before {
            break;
        }
    }
}

fn show(name: &str, l: &Lattice, target: u128) {
    println!("── route: {name}");
    for (i, row) in l.d.iter().enumerate().rev() {
        let cells: Vec<String> = row.iter().map(|x| format!("{x:>4}")).collect();
        println!("  i={i:<2} b={:<3} {}", radix(&l.b, i), cells.join(""));
    }
    let heads: Vec<String> = (0..l.d[0].len()).map(|j| format!("{:>4}", radix(&l.c, j))).collect();
    println!("        c=   {}", heads.join(""));
    let moved: u128 = l.ledger.values().sum();
    let lines = l.ledger.len();
    println!("  value = {} (target {target}) {}", l.value(), if l.value() == target { "✓ conserved" } else { "✗" });
    println!("  ledger: {lines} active lines, {moved} units carried");
    for (k, v) in &l.ledger {
        println!("    {k:<28} {v}");
    }
}


/// Carry streams on one schedule (fdrs.md §3.9): run a history of additions by three
/// different routes and compare the per-line totals with ⌊V_{≤i} / B_{i+1}⌋.
fn streams(b: &[u128], nums: &[u128]) {
    let k = nums.iter().map(|&x| digits(x, b).len()).max().unwrap_or(1) + 4;
    let pb = place_values(b, k + 1);
    let mut stacked = vec![0u128; k + 1];
    for &x in nums {
        for (i, d) in digits(x, b).into_iter().enumerate() {
            stacked[i] += d;
        }
    }
    // route A: stack everything, one sweep
    let sweep = |d: &mut Vec<u128>, f: &mut Vec<u128>| {
        for i in 0..k {
            let q = d[i] / radix(b, i);
            d[i] %= radix(b, i);
            d[i + 1] += q;
            f[i] += q;
        }
    };
    let mut fa = vec![0u128; k];
    let mut da = stacked.clone();
    sweep(&mut da, &mut fa);
    // route B: add one number at a time, sweep after each
    let mut fb = vec![0u128; k];
    let mut db = vec![0u128; k + 1];
    for &x in nums {
        for (i, d) in digits(x, b).into_iter().enumerate() {
            db[i] += d;
        }
        sweep(&mut db, &mut fb);
    }
    // route C: carry lines in reverse order, repeatedly, until canonical
    let mut fc = vec![0u128; k];
    let mut dc = stacked.clone();
    loop {
        let mut moved = false;
        for i in (0..k).rev() {
            let q = dc[i] / radix(b, i);
            if q > 0 {
                dc[i] %= radix(b, i);
                dc[i + 1] += q;
                fc[i] += q;
                moved = true;
            }
        }
        if !moved {
            break;
        }
    }
    let total: u128 = nums.iter().sum();
    println!("history: {} numbers on schedule {b:?}, total {total}", nums.len());
    println!("  line  radix  stack-sweep  one-by-one  reverse  ⌊V≤i/B(i+1)⌋");
    for i in 0..k {
        let v: u128 = (0..=i).map(|u| stacked[u] * pb[u]).sum();
        let pred = v / pb[i + 1];
        let ok = fa[i] == pred && fb[i] == pred && fc[i] == pred;
        println!("  {i:>4}  {:>5}  {:>11}  {:>10}  {:>7}  {:>12} {}", radix(b, i), fa[i], fb[i], fc[i],
            pred, if ok { "✓" } else { "✗" });
    }
    assert!(da == db && db == dc, "all routes end in the same canonical digits");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |flag: &str, default: &str| -> String {
        args.iter().position(|a| a == flag).and_then(|p| args.get(p + 1).cloned())
            .unwrap_or_else(|| default.to_string())
    };
    if let Some(p) = args.iter().position(|a| a == "--streams") {
        let b = parse_list(&get("--b", "2,3,5"));
        let nums = parse_list(args.get(p + 1).map(|s| s.as_str()).unwrap_or("29,50,77,13,99"));
        streams(&b, &nums);
        return;
    }
    let b = parse_list(&get("--b", "2,3,5"));
    let c = parse_list(&get("--c", "3,4,7"));
    let x: u128 = get("--x", "29").parse().unwrap();
    let y: u128 = get("--y", "50").parse().unwrap();
    println!("x = {x} on schedule b = {b:?}: digits {:?}", digits(x, &b));
    println!("y = {y} on schedule c = {c:?}: digits {:?}", digits(y, &c));
    let target = x * y;
    for (name, f) in [("rows, then top row", route_rows as fn(&mut Lattice)),
                      ("columns, then last column", route_cols),
                      ("greedy (smaller ratio first)", route_greedy)] {
        let mut l = build(&b, &c, x, y);
        let v0 = l.value();
        assert_eq!(v0, target, "outer product value (Theorem 139)");
        f(&mut l);
        assert_eq!(l.value(), target, "conservation (Theorem 137)");
        show(name, &l, target);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn routes_conserve_value() {
        for (b, c) in [(vec![2, 3, 5], vec![3, 4, 7]), (vec![10], vec![10]), (vec![2, 3], vec![5])] {
            for x in [0u128, 1, 7, 29, 123, 1000] {
                for y in [0u128, 3, 50, 999] {
                    for f in [route_rows as fn(&mut Lattice), route_cols, route_greedy] {
                        let mut l = build(&b, &c, x, y);
                        assert_eq!(l.value(), x * y);
                        f(&mut l);
                        assert_eq!(l.value(), x * y);
                    }
                }
            }
        }
    }
}
