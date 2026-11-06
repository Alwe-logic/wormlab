//! 性質ベースのテスト：ランダムな worm を大量に生成して、
//! 理論上成り立つはずの関係を機械的に確かめる。

use proptest::prelude::*;
use wormlab_core::{Ordinal, Worm};

/// 長さ 0〜9、文字 0〜3 のランダムな worm
fn worm() -> impl Strategy<Value = Worm> {
    prop::collection::vec(0u32..4, 0..10).prop_map(Worm::new)
}

proptest! {
    /// o の逆写像は本当に逆になっている
    #[test]
    fn from_ordinal_is_inverse(a in worm()) {
        let alpha = a.ordinal();
        prop_assert_eq!(Worm::from_ordinal(&alpha).ordinal(), alpha);
    }

    /// 標準形は冪等
    #[test]
    fn normal_form_is_idempotent(a in worm()) {
        let nf = a.normal_form();
        prop_assert_eq!(nf.normal_form(), nf);
    }

    /// o(0 A) = o(A) + 1
    #[test]
    fn zero_prefix_is_successor(a in worm()) {
        let za = Worm::new(vec![0]).concat(&a);
        prop_assert_eq!(za.ordinal(), a.ordinal() + Ordinal::nat(1));
    }

    /// 空でない B について A <_0 B A（⟨n⟩ を前に付けると真に強くなる）
    #[test]
    fn nonempty_prefix_increases(a in worm(), b in worm()) {
        prop_assume!(!b.is_top());
        prop_assert!(a.lt0(&b.concat(&a)));
    }

    /// A B → A なので o(A) ≤ o(A B)
    #[test]
    fn suffix_does_not_decrease(a in worm(), b in worm()) {
        prop_assert!(a.ordinal() <= a.concat(&b).ordinal());
    }

    /// worm battle の 1 ステップで順序数は真に減る
    #[test]
    fn battle_step_decreases(a in worm(), m in 0usize..5) {
        prop_assume!(!a.is_top());
        let next = a.battle_step(m).unwrap();
        prop_assert!(next.ordinal() < a.ordinal(),
            "{} (o = {}) -> {} (o = {})", a, a.ordinal(), next, next.ordinal());
    }

    /// 順序数の加法は結合的
    #[test]
    fn ordinal_addition_associative(a in worm(), b in worm(), c in worm()) {
        let (x, y, z) = (a.ordinal(), b.ordinal(), c.ordinal());
        prop_assert_eq!((x.clone() + y.clone()) + z.clone(), x + (y + z));
    }

    /// Ω_{n+1}(A) = ℓ(Ω_n(A))（Fernández-Duque & Joosten II, Thm 6.5）
    #[test]
    fn pi_ordinals_last_exponent(a in worm(), n in 0u32..4) {
        prop_assert_eq!(a.pi_ordinal(n + 1), a.pi_ordinal(n).last_exponent(), "A = {}, n = {}", a, n);
    }

    /// Ω_0 = o
    #[test]
    fn pi_ordinal_zero_is_o(a in worm()) {
        prop_assert_eq!(a.pi_ordinal(0), a.ordinal());
    }

    /// 表示 → パースで元に戻る
    #[test]
    fn display_parse_roundtrip(a in worm()) {
        prop_assert_eq!(a.to_string().parse::<Worm>().unwrap(), a.clone());
        prop_assert_eq!(a.to_formula().parse::<Worm>().unwrap(), a);
    }
}
