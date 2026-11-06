//! 実験：括弧語どうしの比較 b ◁ a（a ⊢ ()b）を BC で導出したときの大きさを、
//! τ で翻訳した RC_Γ0 のシーケント ⟨o*(a_1)⟩… ⊢ ⟨0⟩⟨o*(b_1)⟩… の RC の導出と比べる。
//!
//! RC_Γ0 では「モダリティの大小」は順序数の比較で一瞬で決まる（規則の副条件 α > β）。
//! BC ではそれを括弧語の導出で示さなければならないので、その分だけ導出が大きくなる。
//! 括弧の入れ子が深くなるほど、副条件の中の副条件…と入れ子が増える。その増え方を見る。
//!
//!   cargo run --release -p wormlab-core --example bc_sizes

use wormlab_core::Bracket;
use wormlab_core::bc::{self, BSeq};
use wormlab_core::rcproof;

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

/// 入れ子の深さがちょうど depth、文字が高々 3 個のランダムな括弧語
/// （どこか 1 つの文字は深さ depth − 1、ほかの文字はそれ以下）
fn random_bracket(r: &mut Rng, depth: usize) -> Bracket {
    if depth == 0 {
        return Bracket::top();
    }
    let k = 1 + r.below(3) as usize;
    let deep = r.below(k as u64) as usize;
    let mut letters = Vec::with_capacity(k);
    for i in 0..k {
        let d = if i == deep { depth - 1 } else { r.below(depth as u64) as usize };
        letters.push(random_bracket(r, d));
    }
    Bracket::new(letters)
}

fn main() {
    let mut r = Rng(2026);
    println!("depth,bc_dag,rc_dag,side_conditions,max_side_depth");
    for depth in 1..=5usize {
        let (mut n, mut bc_sum, mut rc_sum, mut side_sum, mut sd_max) = (0usize, 0usize, 0usize, 0usize, 0usize);
        while n < 40 {
            let (x, y) = (random_bracket(&mut r, depth), random_bracket(&mut r, depth));
            let (a, b) = match x.cmp_syntactic(&y) {
                std::cmp::Ordering::Greater => (x, y),
                std::cmp::Ordering::Less => (y, x),
                std::cmp::Ordering::Equal => continue,
            };
            // BC の導出（順序数なし）
            let (p, st) = bc::derive_lt(&b, &a).expect("b ◁ a なので導出できるはず");
            bc::check(&p).expect("検査を通るはず");
            // 同じシーケントを τ で翻訳して RC_Γ0 で導出（順序数を使う）
            let t = BSeq::lt(&b, &a).tau();
            let (q, _) = rcproof::derive(&t.lhs, &t.rhs).expect("RC_Γ0 でも成り立つはず");
            println!("{depth},{},{},{},{}", p.dag_size(), q.dag_size(), st.side_conditions, st.max_side_depth);
            n += 1;
            bc_sum += p.dag_size();
            rc_sum += q.dag_size();
            side_sum += st.side_conditions;
            sd_max = sd_max.max(st.max_side_depth);
        }
        eprintln!(
            "深さ {depth}: BC の導出 平均 {:.1} ノード / RC_Γ0 の導出 平均 {:.1} ノード（{:.2} 倍）、副条件 平均 {:.1} 個、入れ子 最大 {sd_max} 段",
            bc_sum as f64 / n as f64,
            rc_sum as f64 / n as f64,
            bc_sum as f64 / rc_sum as f64,
            side_sum as f64 / n as f64,
        );
    }
}
