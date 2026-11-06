//! RC 判定器の性質ベースのテスト。
//!
//! - 判定器が RC の規則で閉じていること（導けるべきものを導く）
//! - 判定器が言いすぎないこと（主張した A ⊢ B が他の RC モデルでも成り立つ）
//! - worm について、順序数 o による比較と独立に一致すること

use proptest::prelude::*;
use std::cmp::Ordering;
use wormlab_core::rc::{decide, entails, equivalent, Model};
use wormlab_core::{Spf, Worm};

/// 変数 p, q とモダリティ 0〜2 からなるランダムな強正値式
fn spf() -> impl Strategy<Value = Spf> {
    let leaf = prop_oneof![
        Just(Spf::Top),
        Just(Spf::var("p")),
        Just(Spf::var("q")),
    ];
    leaf.prop_recursive(4, 16, 2, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Spf::and(a, b)),
            (0u32..3, inner).prop_map(|(n, a)| Spf::dia(n, a)),
        ]
    })
}

/// 少し大きめ・モダリティ 0〜4 の式（2 つの判定法の突き合わせ用）
fn spf_big() -> impl Strategy<Value = Spf> {
    let leaf = prop_oneof![Just(Spf::Top), Just(Spf::var("p")), Just(Spf::var("q"))];
    leaf.prop_recursive(6, 40, 2, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Spf::and(a, b)),
            (0u32..5, inner).prop_map(|(n, a)| Spf::dia(n, a)),
        ]
    })
}

fn worm() -> impl Strategy<Value = Worm> {
    prop::collection::vec(0u32..4, 0..8).prop_map(Worm::new)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(400))]

    // ---- 規則で閉じている ----

    #[test]
    fn reflexive(a in spf()) {
        prop_assert!(entails(&a, &a));
    }

    #[test]
    fn transitive(a in spf(), b in spf(), c in spf()) {
        if entails(&a, &b) && entails(&b, &c) {
            prop_assert!(entails(&a, &c));
        }
    }

    #[test]
    fn diamond_monotone(a in spf(), b in spf(), n in 0u32..3) {
        if entails(&a, &b) {
            prop_assert!(entails(&Spf::dia(n, a), &Spf::dia(n, b)));
        }
    }

    #[test]
    fn modal_axioms(a in spf(), b in spf(), n in 0u32..3, m in 0u32..3) {
        // ⟨n⟩⟨n⟩A ⊢ ⟨n⟩A
        prop_assert!(entails(&Spf::dia(n, Spf::dia(n, a.clone())), &Spf::dia(n, a.clone())));
        if n > m {
            // ⟨n⟩A ⊢ ⟨m⟩A
            prop_assert!(entails(&Spf::dia(n, a.clone()), &Spf::dia(m, a.clone())));
            // ⟨n⟩A ∧ ⟨m⟩B ⊢ ⟨n⟩(A ∧ ⟨m⟩B)
            let lhs = Spf::and(Spf::dia(n, a.clone()), Spf::dia(m, b.clone()));
            let rhs = Spf::dia(n, Spf::and(a, Spf::dia(m, b)));
            prop_assert!(entails(&lhs, &rhs));
        }
    }

    // ---- 言いすぎない ----

    /// A ⊢ B と判定したなら、別の RC モデル（ランダムな式 C の閉包モデル）の
    /// どの点でも、A が真なら B も真。
    #[test]
    fn sound_in_other_models(a in spf(), b in spf(), c in spf()) {
        if entails(&a, &b) {
            let mut sig = a.modalities();
            sig.extend(b.modalities());
            sig.extend(c.modalities());
            let m = Model::canonical(&c, &sig);
            let ta = m.truth_set(&a);
            let tb = m.truth_set(&b);
            for x in ta.iter() {
                prop_assert!(tb.contains(x), "{} ⊢ {} だが、{} のモデルの点 {} で破れる", a, b, c, x);
            }
        }
    }

    // ---- 2 つの判定法（閉包モデルと局所規則）が一致 ----

    #[test]
    fn local_rules_match_closure(a in spf_big(), b in spf_big()) {
        prop_assert_eq!(decide(&a, &b).holds, entails(&a, &b), "{} ⊢ {}", a, b);
    }

    #[test]
    fn local_rules_match_closure_on_weakenings(a in spf_big(), n in 0u32..5) {
        // 右辺を左辺の一部から作る（真の例を増やす）
        let parts = [a.clone(), Spf::dia(n, a.clone()), Spf::and(a.clone(), Spf::dia(n, Spf::Top))];
        for b in parts {
            prop_assert_eq!(decide(&a, &b).holds, entails(&a, &b), "{} ⊢ {}", a, b);
        }
    }

    // ---- worm：順序数による比較と RC による比較が一致 ----

    #[test]
    fn worm_order_matches_ordinals(a in worm(), b in worm()) {
        let by_ordinal = a.cmp0(&b) == Ordering::Less;
        prop_assert_eq!(a.lt_n(&b, 0), by_ordinal, "{} vs {}", a, b);
    }

    #[test]
    fn worm_equivalence_matches_ordinals(a in worm(), b in worm()) {
        prop_assert_eq!(equivalent(&Spf::from(&a), &Spf::from(&b)), a.equiv(&b), "{} vs {}", a, b);
    }

    #[test]
    fn n_worm_order_matches_ordinals(a in worm(), b in worm(), n in 1u32..3) {
        let (a, b) = (a.up(n), b.up(n));
        prop_assert_eq!(a.lt_n(&b, n), a.cmp_n(&b, n) == Some(Ordering::Less));
    }

    /// 標準形の worm は元の worm と GLP で同値
    #[test]
    fn normal_form_equivalent(a in worm()) {
        prop_assert!(equivalent(&Spf::from(&a), &Spf::from(&a.normal_form())), "{}", a);
    }
}
