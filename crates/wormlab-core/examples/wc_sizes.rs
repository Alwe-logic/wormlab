//! 実験：WC 証明の大きさが worm の長さに対してどう増えるか。
//!
//! 長さ L のランダムな worm の組 (A, B) で B <_0 A となるものについて、
//! WC 証明を作り（検査器も通し）、DAG のノード数（共有あり）と
//! 木に展開したノード数（共有なし＝素朴な証明）を CSV で出力する。
//!
//!   cargo run --release -p wormlab-core --example wc_sizes > sizes.csv
//!   引数で最大長・1 長さあたりの個数・文字の上限を変えられる：
//!   cargo run --release -p wormlab-core --example wc_sizes -- 40 200 4

use std::time::Instant;
use wormlab_core::{Worm, wc};

/// 依存を増やさないための簡単な疑似乱数（xorshift）
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u32) -> u32 {
        (self.next() % n as u64) as u32
    }
}

fn main() {
    let args: Vec<usize> = std::env::args().skip(1).filter_map(|s| s.parse().ok()).collect();
    let max_len = *args.first().unwrap_or(&24);
    let per_len = *args.get(1).unwrap_or(&100);
    let letters = *args.get(2).unwrap_or(&4) as u32;

    let mut rng = Rng(0x9E3779B97F4A7C15);
    println!("len,dag_size,tree_size,height,micros");
    for len in 1..=max_len {
        let mut done = 0;
        while done < per_len {
            let a = Worm::new((0..len).map(|_| rng.below(letters)).collect());
            let b = Worm::new((0..len).map(|_| rng.below(letters)).collect());
            let (small, big) = if b.lt_n(&a, 0) { (b, a) } else if a.lt_n(&b, 0) { (a, b) } else { continue };
            let t = Instant::now();
            let p = wc::prove_lt(0, &small, &big).expect("成り立つはず");
            let micros = t.elapsed().as_micros();
            wc::check(&p).expect("検査を通るはず");
            println!("{len},{},{},{},{micros}", p.dag_size(), p.tree_size(), p.height());
            done += 1;
        }
    }
}
