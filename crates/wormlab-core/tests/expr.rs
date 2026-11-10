//! 順序数の式（expr）のテスト。
//!
//! - 決まった値：Veblen 関数の不動点、超指数関数の既知の値、ψ の崩し、足し算の吸収
//! - 超指数関数が hyperation の法則を満たす：e^0 = id、e^1 = e、e^{α+β} = e^α ∘ e^β
//!   （α + β は演算（arith）で独立に計算する。1 + ω = ω のような吸収があっても成り立つこと）、
//!   e^α(0) = 0、引数について狭義増加、指数について単調、e ∘ e^{ω^γ} = e^{ω^γ}（γ ≥ 1）
//! - 書き方：Veblen の表示はそのまま式として読め、同じ数になる。式の表示も読み直すと同じ値
//! - 計算の過程：最後の段の式全体が結果、各段の値は標準形

use proptest::prelude::*;
use wormlab_core::Veblen;
use wormlab_core::arith;
use wormlab_core::expr::{self, Expr, ExprError};
use wormlab_core::transfinite;

fn v(s: &str) -> Veblen {
    s.parse().unwrap()
}

fn ev(s: &str) -> expr::Eval {
    expr::eval_str(s).unwrap_or_else(|e| panic!("{s}: {e}"))
}

#[test]
fn known_values() {
    for (input, want) in [
        ("φ(1, φ(2, 0))", "φ(2, 0)"),
        ("ω^ε_0", "ε_0"),
        ("φ(Ω, 0)", "Ω"),
        ("φ(0, 0) + φ(0, 1)", "ω"),
        ("e(0)", "0"),
        ("e(1)", "ω"),
        ("e^2(1)", "ω^ω"),
        ("e^ω(1)", "ε_0"),
        ("e^ω(2)", "ε_1"),
        ("e^(ω + 1)(1)", "ε_ω"),
        ("e^(ω^2)(1)", "φ(2, 0)"),
        ("e^(ω^ω)(1)", "φ(ω, 0)"),
        ("e^Ω(2)", "φ(Ω, 1)"),
        ("e^0(ω + 5)", "ω + 5"),
        ("ψ(Ω + ψ(Ω·2 + 1))", "ψ(Ω·2)"),
        ("ψ(0) + ψ(0)·2", "ψ(0)·3"),
        ("1 + ω", "ω"),
        ("(ω + 1)·ω", "ω^2"),
        ("2^ω", "ω"),
        ("ε_(ω + 1) + ω^(ε_(ω + 1) + 1)", "ω^(ε_(ω + 1) + 1)"),
        ("{ω}^{2}", "ω^2"),
    ] {
        assert_eq!(ev(input).value.to_string(), want, "{input}");
    }
}

#[test]
fn rules_name_the_definition_used() {
    let r = ev("φ(1, φ(2, 0))");
    assert!(r.steps.last().unwrap().rule.contains("不動点"));
    let r = ev("φ(Ω, 0)");
    assert!(r.steps[0].rule.contains("φ(s, 0) = s"));
    let r = ev("1 + ω");
    assert!(r.steps[0].rule.contains("吸収"));
    let r = ev("ψ(Ω + ψ(Ω·2 + 1))");
    let last = r.steps.last().unwrap();
    assert!(last.rule.contains("ξ ∉ C(ξ)"), "{}", last.rule);
    assert!(ev("ψ(0)").steps[0].rule.contains("K(ξ) = ∅"));
    let r = ev("e^(ω + 1)(1)");
    let d = &r.steps.last().unwrap().details;
    assert_eq!(d, &["e(1) = ω（e(ξ) = −1 + ω^ξ）", "e^ω(ω) = ε_ω（e^{ω^γ}(1 + β) = φ(γ, β)）"]);
}

#[test]
fn whole_expression_is_rewritten_step_by_step() {
    let r = ev("e^ω(φ(1, 0)) + ψ(0)");
    assert_eq!(r.input, "e^ω(φ(1, 0)) + ψ(0)");
    let wholes: Vec<&str> = r.steps.iter().map(|s| s.whole.as_str()).collect();
    assert_eq!(wholes, ["e^ω(ε_0) + ψ(0)", "ε_(ε_0) + ψ(0)", "ε_(ε_0) + ψ(0)", "ψ(0)"]);
    assert_eq!(r.value.to_string(), "ψ(0)");
    let tex = r.latex();
    assert!(tex.starts_with("\\begin{align*}") && tex.contains("\\psi(0)"));
}

#[test]
fn limits() {
    assert!(matches!(expr::evaluate(&"e^1000000(1)".parse::<Expr>().unwrap()), Err(ExprError::TooManyApplications(1_000_000))));
    assert!(expr::eval_str("(ω + 1)^1000000000").is_err());
    assert!(expr::eval_str(&"1 + ".repeat(600)).is_err());
    assert!(expr::eval_str("e^ω").is_err());
}

#[test]
fn definitions_are_listed_once() {
    let d = expr::definitions();
    let mut keys: Vec<&str> = d.iter().map(|x| x.key).collect();
    keys.sort();
    keys.dedup();
    assert_eq!(keys.len(), d.len());
    assert!(d.iter().all(|x| !x.lines.is_empty() && !x.source.is_empty()));
}

// ----------------------------------------------------------------------
// ランダムな数と式
// ----------------------------------------------------------------------

/// 小さめの数（係数は小さく、超指数関数の適用回数が多くなりすぎないように）
fn small() -> impl Strategy<Value = Veblen> {
    let leaf = (0u64..3).prop_map(Veblen::nat);
    leaf.prop_recursive(3, 12, 3, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| a + b),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Veblen::phi(a, b)),
            inner.clone().prop_map(Veblen::omega_pow),
            (inner, 1u64..3).prop_map(|(a, n)| a.mul_nat(n)),
        ]
    })
}

/// Ω・ψ も含む数
fn wide() -> impl Strategy<Value = Veblen> {
    let leaf = prop_oneof![
        (0u64..3).prop_map(Veblen::nat),
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

/// ランダムな式（演算・φ・ε・e^α・ψ を混ぜる）
fn arb_expr() -> impl Strategy<Value = Expr> {
    let leaf = prop_oneof![(0u64..4).prop_map(Expr::Nat), Just(Expr::Omega), Just(Expr::BigOmega)];
    leaf.prop_recursive(4, 24, 2, |inner| {
        let b = |e: Expr| Box::new(e);
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(move |(x, y)| Expr::Add(b(x), b(y))),
            (inner.clone(), inner.clone()).prop_map(move |(x, y)| Expr::Mul(b(x), b(y))),
            (inner.clone(), (0u64..3).prop_map(Expr::Nat)).prop_map(move |(x, y)| Expr::Pow(b(x), b(y))),
            (inner.clone(), inner.clone()).prop_map(move |(x, y)| Expr::Phi(b(x), b(y))),
            inner.clone().prop_map(move |x| Expr::Eps(b(x))),
            (inner.clone(), inner.clone()).prop_map(move |(x, y)| Expr::Hyp(b(x), b(y))),
            inner.prop_map(move |x| Expr::Psi(b(x))),
        ]
    })
}

fn e(alpha: &Veblen, x: &Veblen) -> Veblen {
    transfinite::hyperexp(alpha, x)
}

fn hyp(alpha: &Veblen, x: &Veblen) -> Result<Veblen, TestCaseError> {
    let s = format!("e^({alpha})({x})");
    match expr::eval_str(&s) {
        Ok(r) => Ok(r.value),
        Err(_) => Err(TestCaseError::reject("大きすぎる")),
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 400, max_global_rejects: 4000, ..ProptestConfig::default() })]

    /// Veblen の表示は式として読め、同じ数になる
    #[test]
    fn veblen_display_is_an_expression(x in wide()) {
        prop_assert_eq!(ev(&x.to_string()).value, x);
    }

    /// 式の表示を読み直しても同じ値。計算の過程の最後の式全体が結果
    #[test]
    fn expressions_reparse_and_steps_end_in_the_value(t in arb_expr()) {
        let Ok(r) = expr::evaluate(&t) else { return Err(TestCaseError::reject("大きすぎる")) };
        let again = expr::eval_str(&t.to_string()).expect("表示は読める");
        prop_assert_eq!(&again.value, &r.value);
        if let Some(last) = r.steps.last() {
            prop_assert_eq!(&last.whole, &r.value.to_string());
            prop_assert_eq!(&last.value, &r.value);
        }
        for st in &r.steps {
            // 各段の値は標準形（表示を読み直すと同じ数）
            prop_assert_eq!(&st.value.to_string().parse::<Veblen>().unwrap(), &st.value);
        }
    }

    /// e^0 = id、e^1 = e（e(ξ) = −1 + ω^ξ）、e^α(0) = 0
    #[test]
    fn hyperexp_basics(a in small(), x in small()) {
        prop_assert_eq!(hyp(&Veblen::zero(), &x)?, x.clone());
        let ex = if x.is_zero() { Veblen::zero() } else { Veblen::omega_pow(x.clone()) };
        prop_assert_eq!(hyp(&Veblen::one(), &x)?, ex);
        prop_assert_eq!(hyp(&a, &Veblen::zero())?, Veblen::zero());
        prop_assert_eq!(hyp(&a, &x)?, e(&a, &x));
    }

    /// e^{α+β} = e^α ∘ e^β（α + β は arith で計算。吸収があっても成り立つ）
    #[test]
    fn hyperexp_is_additive(a in small(), b in small(), x in small()) {
        let Ok(ab) = arith::add(&a, &b) else { return Err(TestCaseError::reject("大きすぎる")) };
        let left = hyp(&ab, &x)?;
        let right = hyp(&a, &hyp(&b, &x)?)?;
        prop_assert_eq!(left, right);
    }

    /// 引数について狭義増加、指数について単調（x ≥ 1）
    #[test]
    fn hyperexp_is_monotone(a in small(), b in small(), x in small(), y in small()) {
        if x < y {
            prop_assert!(hyp(&a, &x)? < hyp(&a, &y)?);
        }
        if a <= b {
            prop_assert!(hyp(&a, &x)? <= hyp(&b, &x)?);
        }
    }

    /// γ ≥ 1 なら e^{ω^γ}(1 + β) = φ(γ, β)、e^{ω^γ} の値は e の不動点
    #[test]
    fn hyperexp_and_veblen(g in small(), b in small()) {
        prop_assume!(!g.is_zero());
        let w = Veblen::omega_pow(g.clone());
        let one_plus_b = Veblen::one() + b.clone();
        let val = hyp(&w, &one_plus_b)?;
        prop_assert_eq!(&val, &Veblen::phi(g, b));
        prop_assert_eq!(hyp(&Veblen::one(), &val)?, val);
    }
}

#[test]
fn veblen_samples() {
    // ψ・Ω を含む決まった数も、表示がそのまま式として読める
    for s in ["ψ(ε_(Ω + 1))", "φ(Ω, ω)", "ω^(ψ(0) + 1)·3 + ε_Ω + 2", "ε_ω^2"] {
        let x = v(s);
        assert_eq!(ev(&x.to_string()).value, x, "{s}");
        assert_eq!(ev(s).value, x, "{s}");
    }
    // 掛け算・べき乗は Veblen の書き方にない（Ω^Ω など）。演算で計算した値と同じ
    let om = Veblen::big_omega();
    assert_eq!(ev("ψ(Ω^Ω)").value, Veblen::psi(arith::pow(&om, &om).unwrap()));
    assert_eq!(ev("(ε_0)^2").value, arith::pow(&v("ε_0"), &Veblen::nat(2)).unwrap());
}
