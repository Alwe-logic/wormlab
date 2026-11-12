//! 論文 §3・§4 の直接の証明を、有限の語の集合 U の上で機械的に検査する。
//!
//! cargo run --release --example bc_direct -- 5
//!
//! - 正準モデル（条件 R1′・R2′・R3）：U の語 x, b について x ⊢ b と x ⊢ ()b の正準モデルを作り、
//!   (B1)〜(B3)（U のすべての添字の組）、真理補題、完全性、保存性（BC[S]）を確かめる
//! - μ_n の非反射性の 2 点フレームが BC-フレームで、μ_n ⊢ ()μ_n を偽にすること

use std::time::Instant;
use wormlab_core::bcfix::{self, Oracle, Universe};
use wormlab_core::Bracket;

fn main() {
    let n: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(4);
    let u = Universe::upto_pairs(n);
    let t0 = Instant::now();
    let t = bcfix::least_fixed_point(&u).theory;
    let full = Oracle::new(&t);
    let index: Vec<usize> = (0..u.len()).collect();
    println!("括弧の対 {n} 個以下：{} 語（不動点 {:.1} 秒）", u.len(), t0.elapsed().as_secs_f64());

    let t1 = Instant::now();
    let (mut seqs, mut max_phi, mut max_worlds, mut skipped) = (0usize, 0usize, 0usize, 0usize);
    for x in 0..u.len() {
        for b in 0..u.len() {
            let mut goals = vec![b];
            if let Some(tb) = u.id(&u.word(b).prepend(Bracket::top())) {
                goals.push(tb);
            }
            for g in goals {
                match bcfix::check_canonical(&u, &t, &full, x, g, &index) {
                    Ok(r) => {
                        seqs += 1;
                        max_phi = max_phi.max(r.phi);
                        max_worlds = max_worlds.max(r.worlds);
                    }
                    Err(e) if e.starts_with("Φ が大きすぎます") => skipped += 1,
                    Err(e) => panic!("{} ⊢ {}：{e}", u.word(x), u.word(g)),
                }
            }
        }
    }
    println!(
        "正準モデル：{seqs} 個のシーケントで違反 0（Φ 最大 {max_phi}、点 最大 {max_worlds}、Φ が大きく省略 {skipped}、{:.1} 秒）",
        t1.elapsed().as_secs_f64()
    );

    let mut k = 1;
    while u.mu(k).is_some() {
        bcfix::check_mu_frame(&u, &t, k, &index).unwrap_or_else(|e| panic!("μ_{k}：{e}"));
        k += 1;
    }
    println!("μ_n の 2 点フレーム：n = 1〜{} で BC-フレームの条件を満たし、μ_n ⊢ ()μ_n を偽にする", k - 1);
}
