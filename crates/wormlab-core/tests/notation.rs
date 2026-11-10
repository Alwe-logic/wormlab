//! 標準形の書き方（notation）のテスト：どの書き方の文字も読み直すと同じ順序数になること、
//! 超指数標準形が Worms and spiders Prop 5.14 の条件（β は 1 か加法的に分解できる数）を満たすこと。

use proptest::prelude::*;
use std::collections::HashMap;
use wormlab_core::Veblen;
use wormlab_core::bracket::Bracket;
use wormlab_core::expr;
use wormlab_core::iworm::IWorm;
use wormlab_core::notation::{self, Notation, hyper_degree, render};
use wormlab_core::transfinite;
use wormlab_core::worm::Worm;

/// Ω・ψ も含む数（係数は小さめ）
fn wide() -> impl Strategy<Value = Veblen> {
    let leaf = prop_oneof![
        (0u64..4).prop_map(Veblen::nat),
        Just(Veblen::omega()),
        Just(Veblen::big_omega()),
        Just(Veblen::psi(Veblen::zero())),
    ];
    leaf.prop_recursive(3, 16, 3, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| a + b),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Veblen::phi(a, b)),
            inner.clone().prop_map(Veblen::omega_pow),
            inner.clone().prop_map(Veblen::psi),
            (inner, 1u64..3).prop_map(|(a, n)| a.mul_nat(n)),
        ]
    })
}

fn eval(s: &str) -> Veblen {
    expr::eval_str(s).unwrap_or_else(|e| panic!("{s}: {e}")).value
}

/// 加法的に分解できる数（2 つ以上の項か、係数が 2 以上）
fn decomposable(x: &Veblen) -> bool {
    !x.is_zero() && !x.is_principal()
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 500, ..ProptestConfig::default() })]

    /// Veblen 形（略記つき・φ だけ）と超指数関数の形は、式として読み直すと同じ数
    #[test]
    fn expression_forms_read_back(x in wide()) {
        for n in [Notation::Veblen, Notation::Phi, Notation::Hyper] {
            let r = render(&x, n);
            prop_assert!(r.note.is_none());
            prop_assert_eq!(eval(&r.text), x.clone(), "{:?}: {}", n, r.text);
        }
    }

    /// 超指数標準形：ξ = e^α(β)、β は 1 か分解できる数。強臨界数でなければ α < ξ
    #[test]
    fn hyper_degree_is_prop_5_14(x in wide()) {
        prop_assume!(!x.is_zero());
        let (a, b) = hyper_degree(&x);
        prop_assert!(b == Veblen::one() || decomposable(&b), "{} = e^{}({})", x, a, b);
        prop_assert_eq!(transfinite::hyperexp(&a, &b), x.clone());
        let critical = x.is_principal() && x.as_phi().is_none();
        prop_assert_eq!(a < x, !critical);
    }

    /// worm・括弧語・impredicative worm：書けるときは読み直すと同じ数（まとめていない形で）
    #[test]
    fn worm_forms_read_back(x in wide()) {
        let r = render(&x, Notation::Worm);
        if r.note.is_none() {
            let w = Worm::from_veblen(&x);
            prop_assert_eq!(notation::worm_len(&x, &mut HashMap::new()), w.letters().len() as u128);
            if w.letters().len() <= 40 {
                let back: Worm<Veblen> = if w.letters().is_empty() { "⊤".parse().unwrap() } else { r.text.parse().unwrap() };
                prop_assert_eq!(back.ordinal(), x.clone());
            }
        }
        let r = render(&x, Notation::Bracket);
        prop_assert_eq!(r.note.is_none(), x.is_predicative());
        if r.note.is_none() && !r.text.contains('^') {
            let b: Bracket = r.text.parse().unwrap();
            prop_assert_eq!(b.ordinal(), x.clone());
        }
        let r = render(&x, Notation::IWorm);
        if r.note.is_none() {
            let w: IWorm = r.text.parse().unwrap();
            prop_assert_eq!(w.value(), x.clone());
        }
    }
}

#[test]
fn every_notation_is_listed() {
    let keys: Vec<&str> = notation::notations().iter().map(|n| n.key).collect();
    assert_eq!(keys, Notation::ALL.map(|n| n.key()));
    for n in Notation::ALL {
        assert_eq!(Notation::parse(n.key()), Some(n));
    }
}

#[test]
fn compact_forms() {
    // 長い worm・括弧語は繰り返しでまとめる
    let x: Veblen = "ω^ω·30".parse().unwrap();
    let r = render(&x, Notation::Worm);
    assert!(r.text.contains('^') && r.note.is_none(), "{}", r.text);
    let r = render(&"ε_0·30".parse().unwrap(), Notation::Bracket);
    assert!(r.text.contains("^30") || r.text.contains("^{30}") || r.text.contains('^'), "{}", r.text);
}
