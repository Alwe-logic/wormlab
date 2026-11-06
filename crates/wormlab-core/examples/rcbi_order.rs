//! 実験：W_BI のランダムな式で、Pakhomov–Lazar の主定理（Thm 4.11 の線形性）と
//! 基本列 (A)_n の共終性を大量に確かめる。
//!
//! - ランダムな組 (A, B) について <¹₁・>・≡¹₁ のどれか 1 つだけが成り立つか
//! - A が極限形で B <¹₁ A のとき、B ≤¹₁ (A)_n となる最小の n はいくつか
//!
//!   cargo run --release -p wormlab-core --example rcbi_order [組の数]

use std::cmp::Ordering;
use std::collections::BTreeMap;
use wormlab_core::rcbi::Formula;
use wormlab_core::rcbi_order::{approx, compare, is_limit};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// 記号の数がおよそ size の W_BI の式
fn random(r: &mut Rng, size: usize) -> Formula {
    if size <= 1 {
        return Formula::Top;
    }
    match r.below(10) {
        0 | 1 => {
            let left = 1 + r.below((size - 1) as u64) as usize;
            Formula::and(random(r, left), random(r, size - left))
        }
        2..=5 => Formula::one(1 + r.below(3) as u32, random(r, size - 1)),
        6 | 7 => Formula::two(2 + r.below(2) as u32, random(r, size - 1)),
        _ => Formula::down(random(r, size - 1)),
    }
}

fn main() {
    let pairs: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(20_000);
    let mut r = Rng(2026);
    let (mut less, mut greater, mut equal, mut incomparable) = (0, 0, 0, 0);
    let mut first_n: BTreeMap<u32, usize> = BTreeMap::new();
    let mut not_found = 0;
    for _ in 0..pairs {
        let (sa, sb) = (2 + r.below(9) as usize, 2 + r.below(9) as usize);
        let (a, b) = (random(&mut r, sa), random(&mut r, sb));
        match compare(&a, &b) {
            Some(Ordering::Less) => less += 1,
            Some(Ordering::Greater) => greater += 1,
            Some(Ordering::Equal) => equal += 1,
            None => {
                incomparable += 1;
                println!("比較できない：{a} と {b}");
            }
        }
        // 共終性：b < a（a は極限形）なら、b ≤ (a)_n となる最小の n
        if is_limit(&a) && compare(&b, &a) == Some(Ordering::Less) {
            match (1..=8).find(|&n| compare(&b, &approx(&a, n).unwrap()) != Some(Ordering::Greater)) {
                Some(n) => *first_n.entry(n).or_default() += 1,
                None => {
                    not_found += 1;
                    println!("(A)_1..8 では届かない：{b} < {a}");
                }
            }
        }
    }
    eprintln!("{pairs} 組：< {less}、> {greater}、≡ {equal}、比較できない {incomparable}");
    let shown: Vec<String> = first_n.iter().map(|(n, c)| format!("n={n}: {c}")).collect();
    eprintln!("共終性（B ≤ (A)_n となる最小の n）：{}、n ≤ 8 で届かない {not_found}", shown.join("、"));
}
