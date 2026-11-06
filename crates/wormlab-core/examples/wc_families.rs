//! 実験：証明器の出力が大きくなりやすい worm の族で、証明の大きさと時間を測る。
//!
//!   cargo run --release -p wormlab-core --example wc_families
//!   cargo run --release -p wormlab-core --example wc_families -- 16 64 256
//!
//! 族（algorithms.md §1, §1c）：
//! - dec ：L L−1 … 0 ⊢ 0 L−1 … 0（A3 一発で済む）
//! - t54 ：(5 4)^k 3 2 1 0 ⊢ 0 (4 0)^k（以前は木が Θ(n²)）
//! - hb  ：0^k 2 0^k ⊢ 0^(2k+1) 1 0（比較の状態数が |A|·|B|）
//! - 12  ：1^k 2^k ⊢ 1 (2 0)^k

use std::time::Instant;
use wormlab_core::{Worm, wc};

fn family(name: &str, k: u32) -> (Worm, Worm) {
    let w = |v: Vec<u32>| Worm::new(v);
    match name {
        "dec" => (w((0..=k).rev().collect()), w(std::iter::once(0).chain((0..k).rev()).collect())),
        "t54" => (
            w((0..k).flat_map(|_| [5, 4]).chain([3, 2, 1, 0]).collect()),
            w(std::iter::once(0).chain((0..k).flat_map(|_| [4, 0])).collect()),
        ),
        "hb" => (
            w((0..k).map(|_| 0).chain([2]).chain((0..k).map(|_| 0)).collect()),
            w((0..2 * k + 1).map(|_| 0).chain([1, 0]).collect()),
        ),
        _ => (
            w((0..k).map(|_| 1).chain((0..k).map(|_| 2)).collect()),
            w(std::iter::once(1).chain((0..k).flat_map(|_| [2, 0])).collect()),
        ),
    }
}

fn main() {
    let ks: Vec<u32> = std::env::args().skip(1).filter_map(|s| s.parse().ok()).collect();
    let ks = if ks.is_empty() { vec![16, 64, 256] } else { ks };
    println!("family,k,n,dag_size,tree_size,height,millis");
    let only = std::env::var("FAMILY").ok();
    for name in ["dec", "t54", "hb", "12"] {
        if only.as_deref().is_some_and(|o| o != name) {
            continue;
        }
        for &k in &ks {
            let (a, b) = family(name, k);
            let n = a.len() + b.len();
            let t = Instant::now();
            let p = wc::prove(&a, &b).expect("成り立つはず");
            let ms = t.elapsed().as_secs_f64() * 1000.0;
            wc::check(&p).expect("検査を通るはず");
            println!("{name},{k},{n},{},{},{},{ms:.1}", p.dag_size(), p.tree_size(), p.height());
        }
    }
}
