//! RC_BI の順序 <¹₁ と基本列の性質ベースのテスト（Pakhomov–Lazar, arXiv:2610.20115, §4）。
//!
//! - Thm 4.11：W_BI の任意の 2 式は比較できる（線形性）。<¹₁ は推移的で、≡¹₁ と両立する
//! - Lemma 4.7：極限形 A の近似は A より下
//! - 近似は（≤¹₁ について）増加し、A より下の式はいずれかの近似以下になる（共終性）
//! - 後続形 A と直前 B の間には何もない
//! - ⟨1⟩ だけの worm の順序は、RC の worm の順序（文字を 1 ずらす）と一致する

use proptest::prelude::*;
use std::cmp::Ordering;
use wormlab_core::Worm;
use wormlab_core::rcbi::Formula;
use wormlab_core::rcbi_order::{Form, approx, compare, equiv, form, is_limit, lt};

/// W_BI のランダムな式（⟨1⟩₁₋₃、⟨2⟩₂₋₃、↓、∧）
fn wbi() -> impl Strategy<Value = Formula> {
    let leaf = Just(Formula::Top);
    leaf.prop_recursive(4, 9, 2, |inner| {
        prop_oneof![
            2 => (inner.clone(), inner.clone()).prop_map(|(a, b)| Formula::and(a, b)),
            4 => (1u32..4, inner.clone()).prop_map(|(k, a)| Formula::one(k, a)),
            2 => (2u32..4, inner.clone()).prop_map(|(k, a)| Formula::two(k, a)),
            2 => inner.prop_map(Formula::down),
        ]
    })
}

/// 極限形のランダムな式
fn limit() -> impl Strategy<Value = Formula> {
    wbi().prop_filter("極限形", is_limit)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// Thm 4.11（線形性）と、<・>・≡ が排他的であること
    #[test]
    fn linear(a in wbi(), b in wbi()) {
        let c = compare(&a, &b);
        prop_assert!(c.is_some(), "比較できない：{} と {}", a, b);
        let (l, g, e) = (lt(&a, &b), lt(&b, &a), equiv(&a, &b));
        prop_assert_eq!(u8::from(l) + u8::from(g) + u8::from(e), 1, "{} と {}：< {} > {} ≡ {}", a, b, l, g, e);
    }

    /// 推移性と ≡ との両立（Prop 4.2）
    #[test]
    fn transitive(a in wbi(), b in wbi(), c in wbi()) {
        let (ab, bc) = (compare(&a, &b).unwrap(), compare(&b, &c).unwrap());
        let ac = compare(&a, &c).unwrap();
        if ab != Ordering::Greater && bc != Ordering::Greater {
            let expect = if ab == Ordering::Equal && bc == Ordering::Equal { Ordering::Equal } else { Ordering::Less };
            prop_assert_eq!(ac, expect, "{} {:?} {} {:?} {}", a, ab, b, bc, c);
        }
    }

    /// Lemma 4.7 と、近似が増加すること
    #[test]
    fn approximations_below_and_increasing(a in limit()) {
        let xs: Vec<Formula> = (1..=4).map(|n| approx(&a, n).unwrap()).collect();
        for (n, x) in xs.iter().enumerate() {
            prop_assert!(lt(x, &a), "({})_{} = {} が下にない", a, n + 1, x);
        }
        for w in xs.windows(2) {
            prop_assert!(compare(&w[0], &w[1]) != Some(Ordering::Greater), "{} の近似が減る：{} > {}", a, w[0], w[1]);
        }
    }

    /// 共終性：A より下の式 B は、いずれかの近似 (A)_n（n ≤ 8）以下
    /// （ランダムな 2 万組の実験では n = 8 までですべて届いた。examples/rcbi_order.rs）
    #[test]
    fn approximations_cofinal(a in limit(), b in wbi()) {
        if lt(&b, &a) {
            let found = (1..=8).any(|n| compare(&b, &approx(&a, n).unwrap()) != Some(Ordering::Greater));
            prop_assert!(found, "{} < {} なのに (A)_1..8 のどれよりも上", b, a);
        }
    }

    /// 後続形 A と直前 P の間には式がない
    #[test]
    fn successor_has_no_gap(a in wbi(), c in wbi()) {
        if let Ok(Form::Successor(p)) = form(&a) {
            prop_assert!(lt(&p, &a), "直前 {} が {} より下にない", p, a);
            prop_assert!(!(lt(&p, &c) && lt(&c, &a)), "{} < {} < {}", p, c, a);
        }
    }
}

/// ⟨1⟩ だけの worm（文字 1〜3、長さ 5 以下）の順序は、RC の worm（文字 0〜2）の順序と一致
#[test]
fn one_worms_match_rc_worms() {
    let mut worms = Vec::new();
    for len in 0..=4u32 {
        for code in 0..3u32.pow(len) {
            let mut c = code;
            let letters: Vec<u32> = (0..len)
                .map(|_| {
                    let x = c % 3;
                    c /= 3;
                    x
                })
                .collect();
            worms.push(Worm::new(letters));
        }
    }
    let to_bi = |w: &Worm| w.letters().iter().rev().fold(Formula::Top, |acc, &k| Formula::one(k + 1, acc));
    for x in &worms {
        for y in &worms {
            assert_eq!(compare(&to_bi(x), &to_bi(y)), Some(x.cmp0(y)), "{x} と {y}");
        }
    }
}

/// §6 の値の順と、それぞれの形
#[test]
fn section6_forms() {
    let f = |s: &str| s.parse::<Formula>().unwrap();
    assert_eq!(form(&f("⊤")).unwrap(), Form::Zero);
    assert_eq!(form(&f("⟨1⟩₁⊤")).unwrap(), Form::Successor(f("⊤")));
    for s in ["⟨1⟩₂⊤", "↓⊤", "⟨2⟩₂⊤", "⟨2⟩₃⊤", "⟨2⟩₂⟨2⟩₃⊤", "⟨2⟩₂⟨2⟩₃⊤ ∧ ↓⊤"] {
        assert_eq!(form(&f(s)).unwrap(), Form::Limit, "{s}");
    }
}

/// 回帰テスト：論文の Def 4.6 の α = i = 2 の場合は (A)_{n+1} = ⟨1⟩₁(A′ ∧ ↓(A)_n)。
/// 括弧を落として ⟨1⟩₁A′ ∧ ↓(A)_n と読むと、⟨1⟩₃⟨2⟩₃⊤（< Γ₀）に近似が届かなくなる。
#[test]
fn gamma0_approximations_reach_reflection() {
    let f = |s: &str| s.parse::<Formula>().unwrap();
    let a = f("⟨2⟩₂⟨2⟩₃⊤"); // Γ₀
    let b = f("⟨1⟩₃⟨2⟩₃⊤");
    assert!(lt(&b, &a));
    assert_eq!(approx(&a, 2), Some(f("⟨1⟩₁(⟨2⟩₃⊤ ∧ ↓⟨2⟩₃⊤)")));
    assert_eq!(compare(&b, &approx(&a, 2).unwrap()), Some(Ordering::Less));
}
