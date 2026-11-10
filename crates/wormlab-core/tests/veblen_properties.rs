//! Veblen 表記の性質ベースのテスト。
//!
//! 比較・正規化・加法が順序数の基本法則を満たすか、
//! ε0 未満では今までの Cantor 標準形（Ordinal）と一致するかを確かめる。

use proptest::prelude::*;
use std::cmp::Ordering;
use wormlab_core::{Veblen, Worm};

/// ランダムな Γ0 未満の順序数（φ・ω^x・加法・自然数倍を組み合わせて作る）
fn veblen() -> impl Strategy<Value = Veblen> {
    let leaf = (0u64..4).prop_map(Veblen::nat);
    leaf.prop_recursive(4, 32, 3, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| a + b),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Veblen::phi(a, b)),
            inner.clone().prop_map(Veblen::omega_pow),
            (inner, 1u64..4).prop_map(|(a, n)| a.mul_nat(n)),
        ]
    })
}

fn worm() -> impl Strategy<Value = Worm> {
    prop::collection::vec(0u32..4, 0..8).prop_map(Worm::new)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(400))]

    // ---- 比較は全順序 ----

    #[test]
    fn comparison_antisymmetric(x in veblen(), y in veblen()) {
        prop_assert_eq!(x.cmp(&y), y.cmp(&x).reverse());
        prop_assert_eq!(x.cmp(&y) == Ordering::Equal, x == y);
    }

    #[test]
    fn comparison_transitive(x in veblen(), y in veblen(), z in veblen()) {
        if x < y && y < z {
            prop_assert!(x < z, "{} < {} < {}", x, y, z);
        }
    }

    // ---- Veblen 関数の性質 ----

    /// a1 < a2 なら φ(a2, b) は φ(a1, ·) の不動点
    #[test]
    fn phi_fixed_points(a1 in veblen(), a2 in veblen(), b in veblen()) {
        if a1 < a2 {
            let y = Veblen::phi(a2, b);
            prop_assert_eq!(Veblen::phi(a1, y.clone()), y);
        }
    }

    /// φ(a, ·) は狭義単調増加
    #[test]
    fn phi_monotone(a in veblen(), b1 in veblen(), b2 in veblen()) {
        if b1 < b2 {
            prop_assert!(Veblen::phi(a.clone(), b1) < Veblen::phi(a, b2));
        }
    }

    /// a < φ(a, b)、b ≤ φ(a, b)（Γ0 未満では φ(a, 0) > a）
    #[test]
    fn phi_bounds(a in veblen(), b in veblen()) {
        let y = Veblen::phi(a.clone(), b.clone());
        prop_assert!(a < y, "{} < {}", a, y);
        prop_assert!(b <= y);
    }

    // ---- 加法 ----

    #[test]
    fn addition_associative(x in veblen(), y in veblen(), z in veblen()) {
        prop_assert_eq!((x.clone() + y.clone()) + z.clone(), x + (y + z));
    }

    #[test]
    fn addition_monotone(x in veblen(), y in veblen(), z in veblen()) {
        if y < z {
            prop_assert!(x.clone() + y.clone() < x.clone() + z.clone()); // 左から足すと狭義
            prop_assert!(y + x.clone() <= z + x);                         // 右から足すと広義
        }
    }

    #[test]
    fn left_subtraction(mu in veblen(), d in veblen(), alpha in veblen()) {
        prop_assert_eq!(mu.sub_left(&(mu.clone() + d.clone())), Some(d));
        match mu.sub_left(&alpha) {
            Some(delta) => prop_assert_eq!(mu + delta, alpha),
            None => prop_assert!(mu > alpha),
        }
    }

    #[test]
    fn mul_nat_is_repeated_addition(x in veblen(), n in 0u64..5) {
        let rep = (0..n).fold(Veblen::zero(), |acc, _| acc + x.clone());
        prop_assert_eq!(x.mul_nat(n), rep);
    }

    /// α の最後の主項は ω^{ℓα}
    #[test]
    fn last_exponent(x in veblen()) {
        if let Some((a, b, _)) = x.terms().last() {
            prop_assert_eq!(Veblen::phi(a, b), Veblen::omega_pow(x.last_exponent()));
        }
    }

    // ---- 表示とパース ----

    #[test]
    fn display_parse_roundtrip(x in veblen()) {
        let s = x.to_string();
        prop_assert_eq!(s.parse::<Veblen>().unwrap(), x, "{}", s);
    }

    // ---- ε0 未満では Cantor 標準形と一致 ----

    #[test]
    fn agrees_with_cnf(a in worm(), b in worm()) {
        let (x, y) = (a.ordinal(), b.ordinal());
        let (vx, vy) = (Veblen::from(&x), Veblen::from(&y));
        prop_assert_eq!(vx.cmp(&vy), x.cmp(&y));
        prop_assert_eq!(Veblen::from(&(x.clone() + y.clone())), vx.clone() + vy);
        prop_assert_eq!(vx.to_cnf(), Some(x.clone()));
        prop_assert_eq!(vx.to_string(), x.to_string());
    }
}
