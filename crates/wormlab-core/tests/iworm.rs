//! Impredicative autonomous worm（Worms and spiders §6.5）の性質ベースのテスト。
//!
//! - 値 p(w) は可算で ψ(e_{Ω+1}1) 未満
//! - 逆写像：p(from_value(ξ)) = ξ（Thm 6.36 の構成）、表示と読み直し
//! - Lemma 6.27：w が Ω を含めば p((w)) = p(w)
//! - π は Ω 以上の worm の上で ◁ について単調：o(w^π) ≤ o(v^π) なら p(w) ≤ p(v)

use proptest::prelude::*;
use wormlab_core::Veblen;
use wormlab_core::iworm::{self, ILetter, IWorm};

/// ランダムな W_Ω の worm（入れ子 3 段、各段の長さ 0〜3）
fn iw() -> impl Strategy<Value = IWorm> {
    let leaf = prop_oneof![Just(IWorm::top()), Just(IWorm::new(vec![ILetter::Omega]))];
    leaf.prop_recursive(3, 20, 3, |inner| {
        prop::collection::vec(
            prop_oneof![1 => Just(ILetter::Omega), 3 => inner.prop_map(ILetter::Br)],
            0..4,
        )
        .prop_map(IWorm::new)
    })
}

/// ψ(e_{Ω+1}1) 未満のランダムな可算な数
fn small_countable() -> impl Strategy<Value = Veblen> {
    let leaf = prop_oneof![
        (0u64..3).prop_map(Veblen::nat),
        Just(Veblen::omega()),
        Just(Veblen::big_omega()),
    ];
    let t = leaf.prop_recursive(3, 16, 3, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| a + b),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Veblen::phi(a, b)),
            inner.prop_map(Veblen::psi),
        ]
    });
    (t.clone(), t).prop_map(|(a, b)| {
        // 可算な部分だけを使う：ψ(a) と、φ・加法で組んだもの
        let pa = Veblen::psi(a);
        let pb = Veblen::psi(b);
        if pa < pb { Veblen::phi(pa, pb + Veblen::one()) } else { pa + pb }
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    #[test]
    fn values_are_countable_and_bounded(w in iw()) {
        let p = w.value();
        prop_assert!(p.is_countable());
        prop_assert!(p < Veblen::psi(iworm::top()));
        prop_assert!(w.ordinal() < iworm::top());
        // 表示と読み直し
        prop_assert_eq!(w.to_string().parse::<IWorm>().unwrap(), w.clone());
        // 標準形は同じ値
        let nf = w.normal_form();
        prop_assert_eq!(nf.value(), p, "{} ↦ {}", w, nf);
    }

    /// Thm 6.36：ψ(e_{Ω+1}1) 未満の可算な数はどれも p(w) になる
    #[test]
    fn every_value_is_reached(x in small_countable()) {
        if x < Veblen::psi(iworm::top()) {
            let w = IWorm::from_value(&x).expect("表せるはず");
            prop_assert_eq!(w.value(), x.clone(), "{} ↦ {}", x, w);
        } else {
            prop_assert!(IWorm::from_value(&x).is_none());
        }
    }

    /// Lemma 6.27：o(⟨πw⟩⊤) = πw（w^π が Ω を含むとき）
    #[test]
    fn bracketing_a_collapse(w in iw()) {
        if !w.ordinal().is_countable() {
            let b = IWorm::new(vec![ILetter::Br(w.clone())]);
            prop_assert_eq!(b.value(), w.value());
        }
    }

    /// π は Ω 以上の worm の上で単調：o(w^π) ≤ o(v^π) ⇒ p(w) ≤ p(v)（U(w) ⊆ U(v) なので）。
    /// 可算と非可算をまたぐと成り立たない：o(()(Ω)) = Γ0 + 1 < Ω = o(Ω) だが p は Γ0 + 1 > Γ0
    #[test]
    fn projection_is_monotone(w in iw(), v in iw()) {
        let (ow, ov) = (w.ordinal(), v.ordinal());
        if ow <= ov && ow.is_countable() == ov.is_countable() {
            prop_assert!(w.value() <= v.value(), "{} ≤ {} なのに p が逆", w, v);
        }
    }
}
