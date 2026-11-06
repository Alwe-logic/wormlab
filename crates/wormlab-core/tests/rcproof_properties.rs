//! RC の導出器の性質ベースのテスト。
//!
//! - 導出が作れる ⟺ 閉包モデルで成り立つ（2 つの独立な方法の突き合わせ）
//! - 作った導出はすべて検査器を通り、結論が正しい
//! - モダリティが順序数でも同じ

use proptest::prelude::*;
use wormlab_core::rc::entails;
use wormlab_core::rcproof::{RSeq, check, derive};
use wormlab_core::{Spf, Veblen};

/// 変数 p, q とモダリティ 0〜2 からなるランダムな強正値式
fn spf() -> impl Strategy<Value = Spf> {
    let leaf = prop_oneof![Just(Spf::Top), Just(Spf::var("p")), Just(Spf::var("q"))];
    leaf.prop_recursive(4, 16, 2, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Spf::and(a, b)),
            (0u32..3, inner).prop_map(|(n, a)| Spf::dia(n, a)),
        ]
    })
}

/// モダリティが順序数のランダムな強正値式
fn ospf() -> impl Strategy<Value = Spf<Veblen>> {
    let pool: Vec<Veblen> = ["0", "1", "ω", "ω + 1", "ε_0"].iter().map(|s| s.parse().unwrap()).collect();
    let leaf = prop_oneof![Just(Spf::Top), Just(Spf::var("p")), Just(Spf::var("q"))];
    leaf.prop_recursive(4, 16, 2, move |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Spf::and(a, b)),
            (prop::sample::select(pool.clone()), inner).prop_map(|(n, a)| Spf::dia(n, a)),
        ]
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(400))]

    #[test]
    fn derivations_match_closure(a in spf(), b in spf()) {
        let holds = entails(&a, &b);
        match derive(&a, &b) {
            Ok((p, _)) => {
                prop_assert!(holds, "{} ⊢ {} は閉包では偽なのに導出ができた", a, b);
                let c = check(&p).map_err(|e| TestCaseError::fail(format!("{a} ⊢ {b}: {e}")))?;
                prop_assert_eq!(c, &RSeq { lhs: a, rhs: b });
            }
            Err(_) => prop_assert!(!holds, "{} ⊢ {} は閉包では真なのに導出ができない", a, b),
        }
    }

    /// 右辺を左辺から作った「成り立ちやすい」組でも試す（真の例を増やす）
    #[test]
    fn derivations_for_weakened_rhs(a in spf(), n in 0u32..3) {
        // ⟨n⟩A ∧ A ⊢ ⟨n⟩A、A ⊢ A ∧ ⊤ などは常に真
        let lhs = Spf::and(Spf::dia(n, a.clone()), a.clone());
        for rhs in [Spf::dia(n, a.clone()), Spf::and(a.clone(), Spf::Top), Spf::dia(0, a.clone())] {
            let (p, _) = derive(&lhs, &rhs).map_err(TestCaseError::fail)?;
            prop_assert!(check(&p).is_ok());
        }
    }

    #[test]
    fn ordinal_modalities(a in ospf(), b in ospf()) {
        let holds = entails(&a, &b);
        match derive(&a, &b) {
            Ok((p, _)) => {
                prop_assert!(holds);
                prop_assert!(check(&p).is_ok(), "{} ⊢ {}", a, b);
            }
            Err(_) => prop_assert!(!holds, "{} ⊢ {}", a, b),
        }
    }
}
