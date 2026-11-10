//! 実験：RC_BI の有限モデル M_A の点の数は ↓ の入れ子について指数的に増える（algorithms.md §6.3）。
//! それが意味の上で必要なのかを見るため、M_A の最大の双模倣（すべての関係について）で
//! 点をまとめた商の大きさを測る。変数のない式の真偽は双模倣で保たれるので、商でも判定は同じ。
//!
//!   cargo run --release -p wormlab-core --example rcbi_bisim [random]

use std::time::Instant;
use wormlab_core::rcbi::{Formula, Model};

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

/// 記号の数がおよそ size のランダムな閉じた式（rcbi_sizes と同じ作り方、↓ を少し多めに）
fn random(r: &mut Rng, size: usize) -> Formula {
    if size <= 1 {
        return Formula::Top;
    }
    match r.below(10) {
        0 | 1 => {
            let left = 1 + r.below((size - 1) as u64) as usize;
            Formula::and(random(r, left), random(r, size - left))
        }
        2 | 3 => Formula::one(1 + r.below(3) as u32, random(r, size - 1)),
        4 => Formula::one_omega(random(r, size - 1)),
        5 | 6 => Formula::two(2 + r.below(2) as u32, random(r, size - 1)),
        7 | 8 => Formula::down(random(r, size - 1)),
        _ => Formula::nabla(random(r, size - 1)),
    }
}

fn bisim_classes(m: &Model) -> usize {
    let c = m.bisim_classes();
    1 + c.iter().copied().max().unwrap_or(0)
}

fn report(name: &str, k: usize, a: &Formula, unshared: bool) {
    let t = Instant::now();
    let ms_ = Model::of(a, 2);
    let ms_share = t.elapsed().as_secs_f64() * 1000.0;
    let qs = bisim_classes(&ms_);
    if !unshared {
        println!("{name},{k},{},-,{},{qs},-,{ms_share:.1},-", a.size(), ms_.num_points());
        return;
    }
    let t = Instant::now();
    let mu = Model::of_unshared(a, 2);
    let ms_un = t.elapsed().as_secs_f64() * 1000.0;
    let q = bisim_classes(&mu);
    let bis = mu.bisimilar_roots(&ms_);
    println!("{name},{k},{},{},{},{q},{qs},{bis},{ms_share:.1},{ms_un:.1}", a.size(), mu.num_points(), ms_.num_points());
    assert!(bis, "根が双模倣でない：{a}");
}

fn main() {
    // `random` を付けたときだけ：ランダムな式で、まとめた M_A と論文どおりの M_A の根が双模倣か（約 10 分）
    if std::env::args().any(|a| a == "random") {
        random_check();
    }
    families();
}

fn random_check() {
    let mut r = Rng(0x6c63_2026);
    let (mut n, mut full_pts, mut shared_pts, mut max_full) = (0usize, 0usize, 0usize, 0usize);
    let t = Instant::now();
    for size in [5usize, 10, 15, 20, 25, 30] {
        for _ in 0..500 {
            let a = random(&mut r, size);
            let full = Model::of_unshared(&a, 3);
            if full.num_points() > 1500 {
                continue;
            }
            let shared = Model::of(&a, 3);
            assert!(shared.bisimilar_roots(&full), "根が双模倣でない：{a}");
            n += 1;
            full_pts += full.num_points();
            shared_pts += shared.num_points();
            max_full = max_full.max(full.num_points());
        }
    }
    println!(
        "random: {n} 個の式で根が双模倣（点の合計 {full_pts} → {shared_pts}、最大 {max_full} 点、{:.1} 秒）",
        t.elapsed().as_secs_f64()
    );
}

fn families() {
    println!("family,k,size,points,points_shared,quotient,quotient_shared,bisimilar,shared_ms,unshared_ms");
    let lim = |k: usize, max: usize| k <= max;
    // (↓⟨1⟩₁)^k ⊤：Def 3.9 そのままだと点は 2^{k+2} − 3
    for k in 1..=24 {
        let a = (0..k).fold(Formula::Top, |acc, _| Formula::down(Formula::one(1, acc)));
        report("down_one", k, &a, lim(k, 8));
    }
    // (↓(⟨1⟩₁X ∧ ⟨1⟩₂X))^k（式の木は指数的に大きい）
    for k in 1..=7 {
        let a = (0..k).fold(Formula::Top, |acc, _| {
            Formula::down(Formula::and(Formula::one(1, acc.clone()), Formula::one(2, acc)))
        });
        report("down_branch", k, &a, lim(k, 5));
    }
    // (↓⟨2⟩₂)^k ⊤
    for k in 1..=16 {
        let a = (0..k).fold(Formula::Top, |acc, _| Formula::down(Formula::two(2, acc)));
        report("down_two", k, &a, lim(k, 6));
    }
    // ↓^k ⊤
    for k in 1..=24 {
        let a = (0..k).fold(Formula::Top, |acc, _| Formula::down(acc));
        report("down_only", k, &a, lim(k, 8));
    }
}
