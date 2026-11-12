//! BC の自律的な意味論（不動点 Ψ）を、括弧の対が n 個以下の語すべての上で計算する。
//!
//! cargo run --release --example bc_fixpoint -- 6 [--gfp] [--no-compare]
//!
//! - ∅ から Ψ を不動点まで回し、各段の大きさと、深さごとに比較が出そろう段を表示
//! - 最小不動点の ◁ を、BracketOrder（順序数なし）と Veblen 経由の比較と全組で照合
//! - --no-compare：照合を省く（大きい n で時間がかかるので）
//! - --gfp：全体の集合から下向きに回した最大不動点が、最小不動点と一致するか

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::time::Instant;
use wormlab_core::bcfix::{self, Universe};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let n: usize = args.iter().find_map(|s| s.parse().ok()).unwrap_or(6);
    let gfp = args.iter().any(|s| s == "--gfp");
    let compare = !args.iter().any(|s| s == "--no-compare");
    let u = Universe::upto_pairs(n);
    println!("括弧の対 {n} 個以下：{} 語", u.len());

    let t0 = Instant::now();
    let l = bcfix::least_fixed_point(&u);
    println!("最小不動点：段ごとの大きさ {:?}（{:.1} 秒）", l.sizes, t0.elapsed().as_secs_f64());
    let t = &l.theory;
    println!("  シーケント {}、≡ の類 {}、順序の違反（非反射・推移・三分）{:?}", t.len(), t.classes().len(), t.order_violations());

    let mut last: BTreeMap<usize, u16> = BTreeMap::new();
    for a in 0..u.len() {
        for b in 0..u.len() {
            if t.below(b, a) {
                let d = u.word(a).depth().max(u.word(b).depth());
                let e = last.entry(d).or_insert(0);
                *e = (*e).max(l.first_lt[a][b]);
            }
        }
    }
    println!("  深さ d の ◁ の比較が出そろう段：{last:?}");
    let mono = (0..u.len())
        .flat_map(|a| (0..u.len()).map(move |b| (a, b)))
        .filter(|&(a, b)| u.word(b).depth() < u.word(a).depth() && !t.below(b, a))
        .count();
    println!("  深さの単調性（depth(b) < depth(a) ⇒ b ◁ a）の違反：{mono}");

    if compare {
    let t1 = Instant::now();
    let (mut bad_syn, mut bad_ord) = (0usize, 0usize);
    for a in 0..u.len() {
        for b in 0..u.len() {
            let (wa, wb) = (u.word(a), u.word(b));
            let got = t.below(b, a);
            if got != (wb.cmp_syntactic(wa) == Ordering::Less) {
                bad_syn += 1;
            }
            if got != (wb.cmp_ordinal(wa) == Ordering::Less) {
                bad_ord += 1;
            }
        }
    }
    println!(
        "  全 {} 組で照合：BracketOrder と不一致 {bad_syn}、Veblen 経由と不一致 {bad_ord}（{:.1} 秒）",
        u.len() * u.len(),
        t1.elapsed().as_secs_f64()
    );
    }

    if gfp {
        let t2 = Instant::now();
        let (g, sizes) = bcfix::greatest_fixed_point(&u);
        println!(
            "最大不動点：段ごとの大きさ {sizes:?}（{:.1} 秒）。最小不動点と{}",
            t2.elapsed().as_secs_f64(),
            if g == l.theory { "一致" } else { "不一致" }
        );
    }
}
