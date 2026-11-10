//! 順序数の演算（arith）のテスト。
//!
//! 演算は Cantor 標準形の公式で計算しているので、公式を使わない独立な性質と突き合わせる：
//! - 有限の数どうしでは自然数の計算と一致する
//! - 定義の再帰式：α + (β+1) = (α + β) + 1、α·(β+1) = α·β + α、α^(β+1) = α^β·α
//! - 極限での連続性：β が極限なら α∘β = sup α∘β[n]。標準の基本列 β[n] で、
//!   「どの n でも α∘β[n] < α∘β」と「α∘β の基本列のどの項も、ある α∘β[n] 以下」を確かめる
//!   （0 での値・後続・極限の 3 つで演算は一意に決まる）
//! - 代数の法則（結合・分配・指数法則・単調性）を Ω・ψ を含む数でも

use proptest::prelude::*;
use wormlab_core::Veblen;
use wormlab_core::arith::{ArithError, Op, add, apply, calc, mul, pow};

/// ランダムな Γ0 未満の順序数（小さめ）
fn small() -> impl Strategy<Value = Veblen> {
    let leaf = (0u64..4).prop_map(Veblen::nat);
    leaf.prop_recursive(3, 16, 3, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| a + b),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Veblen::phi(a, b)),
            inner.clone().prop_map(Veblen::omega_pow),
            (inner, 1u64..4).prop_map(|(a, n)| a.mul_nat(n)),
        ]
    })
}

/// Ω・ψ も含むランダムな数
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

fn op() -> impl Strategy<Value = Op> {
    prop_oneof![Just(Op::Add), Just(Op::Mul), Just(Op::Pow)]
}

/// 大きすぎて計算できない組は、その例を飛ばす
fn ok(r: Result<Veblen, ArithError>) -> Result<Veblen, TestCaseError> {
    match r {
        Ok(v) => Ok(v),
        Err(_) => Err(TestCaseError::reject("大きすぎる")),
    }
}

/// 極限 β について、v = α∘β が α∘β[n] の上限になっているか
fn continuous(op: Op, a: &Veblen, b: &Veblen, v: &Veblen) -> Result<(), TestCaseError> {
    let at = |n: u64| ok(apply(op, a, &b.fundamental(n).expect("極限")));
    for n in 0..6 {
        let x = at(n)?;
        prop_assert!(x < *v, "{a} {op:?} {b}[{n}] = {x} が {v} 未満でない");
    }
    for k in 1..4 {
        let target = v.fundamental(k).expect("値も極限");
        let mut found = false;
        for n in 0..(3 * k + 10) {
            if target <= at(n)? {
                found = true;
                break;
            }
        }
        prop_assert!(found, "{v}[{k}] = {target} を超える {a} {op:?} {b}[n] がない");
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 400, max_global_rejects: 4000, ..ProptestConfig::default() })]

    #[test]
    fn finite_agrees(a in 0u64..50, b in 0u64..50, e in 0u64..12) {
        let (va, vb) = (Veblen::nat(a), Veblen::nat(b));
        prop_assert_eq!(add(&va, &vb).unwrap(), Veblen::nat(a + b));
        prop_assert_eq!(mul(&va, &vb).unwrap(), Veblen::nat(a * b));
        prop_assert_eq!(pow(&va, &Veblen::nat(e)).unwrap(), Veblen::nat(a.pow(e as u32)));
    }

    // ---- 定義の再帰式（0・後続・極限） ----

    #[test]
    fn zero_cases(a in small()) {
        prop_assert_eq!(add(&a, &Veblen::zero()).unwrap(), a.clone());
        prop_assert_eq!(mul(&a, &Veblen::zero()).unwrap(), Veblen::zero());
        prop_assert_eq!(pow(&a, &Veblen::zero()).unwrap(), Veblen::one());
    }

    #[test]
    fn successor_equations(a in small(), b in small()) {
        let b1 = b.clone() + Veblen::one();
        prop_assert_eq!(ok(add(&a, &b1))?, ok(add(&a, &b))? + Veblen::one());
        prop_assert_eq!(ok(mul(&a, &b1))?, ok(mul(&a, &b))? + a.clone());
        let p = ok(pow(&a, &b))?;
        prop_assert_eq!(ok(pow(&a, &b1))?, ok(mul(&p, &a))?);
    }

    #[test]
    fn limit_continuity(op in op(), a in small(), b in small()) {
        prop_assume!(b.is_limit());
        // α + λ（α は何でも）、α·λ（α > 0）、α^λ（α > 1）が連続
        let trivial = match op { Op::Add => false, Op::Mul => a.is_zero(), Op::Pow => a.as_nat().is_some_and(|n| n <= 1) };
        prop_assume!(!trivial);
        let v = ok(apply(op, &a, &b))?;
        continuous(op, &a, &b, &v)?;
    }

    // ---- 代数の法則（Ω・ψ を含む数でも） ----

    #[test]
    fn associativity(a in wide(), b in wide(), c in wide()) {
        prop_assert_eq!(ok(add(&ok(add(&a, &b))?, &c))?, ok(add(&a, &ok(add(&b, &c))?))?);
        prop_assert_eq!(ok(mul(&ok(mul(&a, &b))?, &c))?, ok(mul(&a, &ok(mul(&b, &c))?))?);
    }

    #[test]
    fn left_distributive(a in wide(), b in wide(), c in wide()) {
        // α·(β + γ) = α·β + α·γ（右からの分配 (β + γ)·α は一般には成り立たない）
        prop_assert_eq!(ok(mul(&a, &ok(add(&b, &c))?))?, ok(add(&ok(mul(&a, &b))?, &ok(mul(&a, &c))?))?);
    }

    #[test]
    fn exponent_laws(a in wide(), b in small(), c in small()) {
        // α^(β + γ) = α^β·α^γ、(α^β)^γ = α^(β·γ)
        prop_assert_eq!(ok(pow(&a, &ok(add(&b, &c))?))?, ok(mul(&ok(pow(&a, &b))?, &ok(pow(&a, &c))?))?);
        prop_assert_eq!(ok(pow(&ok(pow(&a, &b))?, &c))?, ok(pow(&a, &ok(mul(&b, &c))?))?);
    }

    #[test]
    fn repeated(a in wide(), n in 1u64..5) {
        // α·n = α + … + α、α^n = α·…·α（掛け算・べき乗の公式と、足し算の繰り返しの突き合わせ）
        let mut s = Veblen::zero();
        let mut p = Veblen::one();
        for _ in 0..n {
            s = ok(add(&s, &a))?;
            p = ok(mul(&p, &a))?;
        }
        prop_assert_eq!(ok(mul(&a, &Veblen::nat(n)))?, s);
        prop_assert_eq!(ok(pow(&a, &Veblen::nat(n)))?, p);
    }

    #[test]
    fn monotone(a in wide(), b in wide(), c in wide()) {
        // 右の引数について狭義単調（α > 0、α > 1 のとき）、左の引数について広義単調
        let (lo, hi) = if b <= c { (b, c) } else { (c, b) };
        prop_assume!(lo < hi);
        prop_assert!(ok(add(&a, &lo))? < ok(add(&a, &hi))?);
        if !a.is_zero() {
            prop_assert!(ok(mul(&a, &lo))? < ok(mul(&a, &hi))?);
        }
        if a > Veblen::one() {
            prop_assert!(ok(pow(&a, &lo))? < ok(pow(&a, &hi))?);
        }
        for o in [Op::Add, Op::Mul, Op::Pow] {
            prop_assert!(ok(apply(o, &lo, &a))? <= ok(apply(o, &hi, &a))?);
        }
    }

    #[test]
    fn steps_end_with_result(o in op(), a in wide(), b in small()) {
        let Ok(c) = calc(o, &a, &b) else { return Err(TestCaseError::reject("大きすぎる")) };
        prop_assert_eq!(&c.steps.last().unwrap().plain, &c.result.to_string());
        // 表示した結果を読み直すと同じ数
        prop_assert_eq!(c.result.to_string().parse::<Veblen>().unwrap(), c.result.clone());
    }
}
