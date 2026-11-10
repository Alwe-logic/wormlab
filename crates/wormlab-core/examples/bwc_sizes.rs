//! 実験：括弧語どうしのシーケントを、BWC（WC の BC 版）と BC で導出したときの大きさの比較。
//!
//! BC は RC の導出（∧ に事実を書き足す構成）を括弧語の上で作り、BWC は WC の証明（worm の
//! まま）を作る。どちらも文字の比較を副条件として再帰的に導出する。
//!
//!   cargo run --release -p wormlab-core --example bwc_sizes
//!
//! 出力は CSV：family,param,bwc_dag,bwc_tree,bwc_side,bc_dag,bc_tree,bc_side,bwc_ms,bc_ms

use std::time::Instant;
use wormlab_core::bc::{self, Formula};
use wormlab_core::bwc::{self, BwSeq};
use wormlab_core::{Bracket, Veblen};

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

fn nested(d: usize) -> Bracket {
    (0..d).fold(Bracket::top(), |acc, _| Bracket::new(vec![acc]))
}

fn veblen(r: &mut Rng, d: u32) -> Veblen {
    if d == 0 || r.below(3) == 0 {
        return Veblen::nat(r.below(4));
    }
    match r.below(4) {
        0 => veblen(r, d - 1) + veblen(r, d - 1),
        1 => Veblen::phi(veblen(r, d - 1), veblen(r, d - 1)),
        2 => Veblen::omega_pow(veblen(r, d - 1)),
        _ => veblen(r, d - 1).mul_nat(1 + r.below(3)),
    }
}

fn report(family: &str, param: usize, s: &BwSeq) {
    let t = Instant::now();
    let (p, st) = bwc::prove(&s.lhs, &s.rhs).expect("成り立つはず");
    let bwc_ms = t.elapsed().as_secs_f64() * 1000.0;
    bwc::check(&p).expect("検査を通るはず");
    let t = Instant::now();
    let (q, sq) = bc::derive(&Formula::worm(&s.lhs), &Formula::worm(&s.rhs)).expect("BC でも成り立つはず");
    let bc_ms = t.elapsed().as_secs_f64() * 1000.0;
    bc::check(&q).expect("検査を通るはず");
    println!(
        "{family},{param},{},{},{},{},{},{},{bwc_ms:.1},{bc_ms:.1}",
        p.dag_size(),
        p.tree_size(),
        st.side_conditions,
        q.dag_size(),
        q.tree_size(),
        sq.side_conditions
    );
}

fn main() {
    println!("family,param,bwc_dag,bwc_tree,bwc_side,bc_dag,bc_tree,bc_side,bwc_ms,bc_ms");
    for d in [3, 6, 9, 12] {
        report("nested", d, &BwSeq::lt(&nested(d - 1), &nested(d)));
    }
    for m in [3, 5, 7] {
        report("thm52", m, &BwSeq::lt(&Bracket::thm52(m - 1), &Bracket::thm52(m)));
    }
    // 長い worm：文字が ()^i（i を表す）の減少列と、1 つ短いもの
    for k in [4, 8, 16, 32] {
        let word = |k: usize| Bracket::new((1..=k).rev().map(|i| Bracket::new(vec![Bracket::top(); i])).collect());
        report("decreasing", k, &BwSeq::lt(&word(k - 1), &word(k)));
        let inc = |k: usize| Bracket::new((1..=k).map(|i| Bracket::new(vec![Bracket::top(); i])).collect());
        report("increasing", k, &BwSeq::lt(&inc(k - 1), &inc(k)));
    }
    // ランダムな順序数の正規形どうし
    let mut r = Rng(0xb3c_2026);
    for depth in 3..=5u32 {
        let mut done = 0;
        while done < 8 {
            let (x, y) = (Bracket::from_ordinal(&veblen(&mut r, depth)), Bracket::from_ordinal(&veblen(&mut r, depth)));
            let (a, b) = match x.cmp_syntactic(&y) {
                std::cmp::Ordering::Greater => (x, y),
                std::cmp::Ordering::Less => (y, x),
                std::cmp::Ordering::Equal => continue,
            };
            report("random_nf", depth as usize, &BwSeq::lt(&b, &a));
            done += 1;
        }
    }
}
