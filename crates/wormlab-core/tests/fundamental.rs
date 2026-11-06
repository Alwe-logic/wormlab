//! 順序数の標準基本列 α[n] と、Hardy 階層・急増加関数のテスト。

use proptest::prelude::*;
use wormlab_core::Veblen;
use wormlab_core::hierarchy::{Budget, fast_growing, hardy};

fn v(s: &str) -> Veblen {
    s.parse().unwrap()
}

fn fs(s: &str, n: u64) -> String {
    v(s).fundamental(n).unwrap().to_string()
}

#[test]
fn known_fundamental_sequences() {
    assert_eq!(fs("ω", 3), "3");
    assert_eq!(fs("ω + 5", 3), "ω + 4"); // 後続順序数なら直前
    assert_eq!(fs("ω·2", 3), "ω + 3");
    assert_eq!(fs("ω^2", 3), "ω·3");
    assert_eq!(fs("ω^ω", 3), "ω^3");
    assert_eq!(fs("ε_0", 1), "1");
    assert_eq!(fs("ε_0", 3), "ω^ω");
    assert_eq!(fs("ε_0", 4), "ω^ω^ω");
    assert_eq!(fs("ε_1", 1), "ω^(ε_0 + 1)");
    assert_eq!(fs("ε_ω", 3), "ε_3");
    assert_eq!(fs("φ(2, 0)", 2), "ε_(ε_0)");
    assert_eq!(fs("φ(ω, 0)", 3), "φ(3, 0)");
    assert_eq!(fs("φ(ω, 1)", 2), "φ(2, φ(ω, 0) + 1)");
    assert_eq!(fs("φ(ε_0, 0)", 3), "φ(ω^ω, 0)");
    assert!(v("0").fundamental(3).is_none());
}

/// 直接の定義による急増加関数（突き合わせ用）：
/// f_0(n) = n+1、f_{α+1}(n) = f_α^n(n)、f_λ(n) = f_{λ[n]}(n)。
/// 定義どおり 1 ずつ数えるので、引数が大きくなったら諦めて None を返す。
fn f_direct(alpha: &Veblen, n: u128) -> Option<u128> {
    if n > 100_000 {
        return None;
    }
    if alpha.is_zero() {
        return Some(n + 1);
    }
    if let Some(p) = alpha.pred() {
        let mut x = n;
        for _ in 0..n {
            x = f_direct(&p, x)?;
        }
        return Some(x);
    }
    f_direct(&alpha.fundamental(n as u64)?, n)
}

#[test]
fn fast_growing_matches_direct_definition() {
    let mut checked = 0;
    for s in ["0", "1", "2", "3", "ω", "ω + 1", "ω·2", "ω^2"] {
        for n in 0..5u128 {
            let a = v(s);
            if let Some(x) = f_direct(&a, n) {
                assert_eq!(fast_growing(&a, n, Budget::default()), Some(x), "f_{s}({n})");
                checked += 1;
            }
        }
    }
    assert!(checked >= 25, "比べた数が少なすぎる: {checked}");
}

#[test]
fn hardy_known_values() {
    let h = |s: &str, n: u128| hardy(&v(s), n, Budget::default());
    for n in 0..20u128 {
        assert_eq!(h("ω", n), Some(2 * n));
        assert_eq!(h("ω·3", n), Some(8 * n));
        assert_eq!(h("ω^2", n), Some(n << n));
    }
}

/// ランダムな Γ0 未満の順序数
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

proptest! {
    #![proptest_config(ProptestConfig::with_cases(400))]

    /// α[n] < α、極限なら n について狭義増加、後続なら直前の数
    #[test]
    fn fundamental_sequence_laws(x in veblen(), n in 0u64..6) {
        if x.is_zero() {
            prop_assert!(x.fundamental(n).is_none());
        } else if x.is_successor() {
            let p = x.fundamental(n).unwrap();
            prop_assert_eq!(p + Veblen::one(), x);
        } else {
            let a = x.fundamental(n).unwrap();
            let b = x.fundamental(n + 1).unwrap();
            prop_assert!(a < x, "{}[{}] = {} が {} より小さくない", x, n, a, x);
            prop_assert!(a < b, "{}[{}] = {} < {}[{}] = {} でない", x, n, a, x, n + 1, b);
        }
    }

    /// 極限 λ の基本列は、λ より小さい「途中の値」をいずれ超える：
    /// λ[m] + 1 も λ より小さく、十分先の λ[n] はそれを超える
    #[test]
    fn fundamental_sequence_is_cofinal_locally(x in veblen(), m in 0u64..4) {
        if x.is_limit() {
            let target = x.fundamental(m).unwrap() + Veblen::one();
            prop_assert!(target < x);
            prop_assert!((m + 1..m + 8).any(|n| x.fundamental(n).unwrap() >= target));
        }
    }
}
