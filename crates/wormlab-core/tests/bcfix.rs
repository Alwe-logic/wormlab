//! BC の自律的な意味論（不動点 Ψ）のテスト。研究メモ bc-semantics-note.md の定理 3・4。
//!
//! - 最小不動点の ◁・⊢ が、順序数を使わない比較（BracketOrder）・Veblen 経由の比較・
//!   BC の判定器（RC の閉包モデル）と一致する（4 つの独立な方法）
//! - 深さ d の比較は段 d までに出る（定理 3）
//! - 最大不動点 = 最小不動点（定理 4 の、有限の U の中での確認）
//! - Ψ は単調

use proptest::prelude::*;
use std::cmp::Ordering;
use wormlab_core::bc::{self, Formula};
use wormlab_core::bcfix::{self, Theory, Universe};
use wormlab_core::Bracket;

#[test]
fn lfp_agrees_with_other_methods() {
    let u = Universe::upto_pairs(5);
    assert_eq!(u.len(), 65);
    let l = bcfix::least_fixed_point(&u);
    let t = &l.theory;
    assert_eq!(t.order_violations(), (0, 0, 0));
    for a in 0..u.len() {
        for b in 0..u.len() {
            let (wa, wb) = (u.word(a), u.word(b));
            let syn = wb.cmp_syntactic(wa);
            assert_eq!(syn, wb.cmp_ordinal(wa), "{wb} と {wa}");
            assert_eq!(t.below(b, a), syn == Ordering::Less, "{wb} ◁ {wa}");
            // a ⊢ b と a ⊢ ()b を BC の判定器で
            let fa = Formula::worm(wa);
            assert_eq!(t.entails(a, b), bc::decide(&fa, &Formula::worm(wb)), "{wa} ⊢ {wb}");
            let ob = wb.prepend(Bracket::top());
            assert_eq!(t.below(b, a), bc::decide(&fa, &Formula::worm(&ob)), "{wa} ⊢ (){wb}");
        }
    }
}

#[test]
fn comparisons_appear_by_depth() {
    let u = Universe::upto_pairs(5);
    let l = bcfix::least_fixed_point(&u);
    for a in 0..u.len() {
        for b in 0..u.len() {
            let d = u.word(a).depth().max(u.word(b).depth()).max(1) as u16;
            if l.theory.below(b, a) {
                assert!(l.first_lt[a][b] <= d, "{} ◁ {} が段 {} で出た", u.word(b), u.word(a), l.first_lt[a][b]);
            }
            if l.theory.entails(a, b) {
                assert!(l.first_le[a][b] <= d, "{} ⊢ {} が段 {} で出た", u.word(a), u.word(b), l.first_le[a][b]);
            }
        }
    }
}

#[test]
fn greatest_equals_least() {
    let u = Universe::upto_pairs(4);
    let l = bcfix::least_fixed_point(&u);
    let (g, _) = bcfix::greatest_fixed_point(&u);
    assert_eq!(g, l.theory);
}

#[test]
fn naive_degenerate_theory_is_not_fixed() {
    // ⊤ 以外の左辺の比較をすべて入れた T は不動点にならない（R_⊤ に J が課されないので () ⊢ ()() が破れる）
    let u = Universe::upto_pairs(3);
    let n = u.len();
    let mut t = Theory::empty(n);
    for a in 0..n {
        for b in 0..n {
            if a != u.top() {
                t.insert_entails(a, b);
                t.insert_below(b, a);
            }
        }
    }
    t.insert_entails(u.top(), u.top());
    assert_ne!(bcfix::psi(&u, &t), t);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    /// T1 ⊆ T2 ⇒ Ψ(T1) ⊆ Ψ(T2)
    #[test]
    fn psi_is_monotone(bits in prop::collection::vec((0usize..9, 0usize..9, any::<bool>(), any::<bool>()), 0..40)) {
        let u = Universe::upto_pairs(3);
        prop_assert_eq!(u.len(), 9);
        let n = u.len();
        let (mut t1, mut t2) = (Theory::empty(n), Theory::empty(n));
        for (a, b, lt, both) in bits {
            if lt { t2.insert_below(b, a) } else { t2.insert_entails(a, b) }
            if both { if lt { t1.insert_below(b, a) } else { t1.insert_entails(a, b) } }
        }
        prop_assert!(t1.is_subset(&t2));
        prop_assert!(bcfix::psi(&u, &t1).is_subset(&bcfix::psi(&u, &t2)));
    }
}

/// 深さは ◁ について単調：depth(v) < depth(w) ⇒ v ◁ w。
/// 定理 4（不動点の一意性）を、◁ の整礎性ではなく深さの帰納法で示すときの鍵。
#[test]
fn depth_is_monotone() {
    let u = Universe::upto_pairs(6);
    let l = bcfix::least_fixed_point(&u);
    for a in 0..u.len() {
        for b in 0..u.len() {
            if u.word(b).depth() < u.word(a).depth() {
                assert!(l.theory.below(b, a), "{} ◁ {}", u.word(b), u.word(a));
            }
        }
    }
}

/// 論文 §3 の正準モデル（条件 R1′・R2′・R3）：BC-フレームの条件 (B1)〜(B3)、真理補題、
/// 完全性、保存性（副条件を S どうしの比較に限ってよいこと）を、対 3 個以下の語のすべての
/// x ⊢ b と x ⊢ ()b で確かめる。
#[test]
fn canonical_model_direct_completeness() {
    let u = Universe::upto_pairs(3);
    let t = bcfix::least_fixed_point(&u).theory;
    let full = bcfix::Oracle::new(&t);
    let index: Vec<usize> = (0..u.len()).collect();
    let mut count = 0;
    for x in 0..u.len() {
        for b in 0..u.len() {
            let mut goals = vec![b];
            if let Some(tb) = u.id(&u.word(b).prepend(Bracket::top())) {
                goals.push(tb);
            }
            for g in goals {
                bcfix::check_canonical(&u, &t, &full, x, g, &index)
                    .unwrap_or_else(|e| panic!("{} ⊢ {}：{e}", u.word(x), u.word(g)));
                count += 1;
            }
        }
    }
    assert_eq!(count, 117);
}

/// 論文 §4 の 2 点フレーム：μ_n ⊢ ()μ_n を偽にする BC-フレーム（n = 1〜6）。
#[test]
fn mu_frames_refute_reflexivity() {
    let u = Universe::upto_pairs(6);
    let t = bcfix::least_fixed_point(&u).theory;
    let index: Vec<usize> = (0..u.len()).collect();
    for n in 1..=6 {
        bcfix::check_mu_frame(&u, &t, n, &index).unwrap_or_else(|e| panic!("μ_{n}：{e}"));
    }
}
