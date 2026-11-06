//! 文字が順序数（Γ0 未満）の worm のテスト。
//!
//! head/body 比較・RC・構文的判定・WC 証明は、文字の大小比較しか使わない。
//! 文字を順序数にしても、独立な方法どうしが一致し続けるかを確かめる。
//! （順序数 o(A) による 3 本目の方法は、次の段階で加える。）

use proptest::prelude::*;
use std::cmp::Ordering;
use wormlab_core::rc::{entails, equivalent};
use wormlab_core::wc::{self, WSeq};
use wormlab_core::{Spf, Veblen, Worm, headbody};

fn v(s: &str) -> Veblen {
    s.parse().unwrap()
}

/// 文字の候補（ε0 をまたぐように選ぶ）
fn pool() -> Vec<Veblen> {
    [
        "0", "1", "2", "ω", "ω + 1", "ω·2", "ω^2", "ω^ω", "ε_0", "ε_0 + 1", "ε_1",
        "φ(2, 0)", "φ(ω, 0)",
    ]
    .iter()
    .map(|s| v(s))
    .collect()
}

fn letter() -> impl Strategy<Value = Veblen> {
    prop::sample::select(pool())
}

fn oworm() -> impl Strategy<Value = Worm<Veblen>> {
    prop::collection::vec(letter(), 0..6).prop_map(Worm::new)
}

fn nworm() -> impl Strategy<Value = Worm> {
    prop::collection::vec(0u32..4, 0..7).prop_map(Worm::new)
}

/// 順序を保つ付け替え 0 ↦ 0, 1 ↦ ω, 2 ↦ ε_0, 3 ↦ φ(2, 0)
fn relabel(a: &Worm) -> Worm<Veblen> {
    let table = [v("0"), v("ω"), v("ε_0"), v("φ(2, 0)")];
    a.map(|&n| table[n as usize].clone())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// head/body と RC が <_0 で一致
    #[test]
    fn headbody_matches_rc(a in oworm(), b in oworm()) {
        let by_rc = a.lt_n(&b, Veblen::zero());
        prop_assert_eq!(headbody::lt(Veblen::zero(), &a, &b), Some(by_rc), "{} vs {}", a, b);
        prop_assert_eq!(headbody::equiv(&a, &b), equivalent(&Spf::from(&a), &Spf::from(&b)));
    }

    /// μ 以上の文字だけの worm で、<_μ について head/body と RC が一致
    #[test]
    fn headbody_matches_rc_above_mu(
        mu in letter(),
        xs in prop::collection::vec(letter(), 0..5),
        ys in prop::collection::vec(letter(), 0..5),
    ) {
        let lift = |zs: &[Veblen]| Worm::new(zs.iter().map(|z| mu.clone() + z.clone()).collect());
        let (a, b) = (lift(&xs), lift(&ys));
        prop_assert_eq!(headbody::lt(mu.clone(), &a, &b), Some(a.lt_n(&b, mu.clone())), "{} <_{} {}", a, mu, b);
    }

    /// 構文的判定と RC が一致
    #[test]
    fn decide_matches_rc(a in oworm(), b in oworm()) {
        let holds = entails(&Spf::from(&a), &Spf::from(&b));
        prop_assert_eq!(wc::decide(&a, &b), holds, "{} ⊢ {}", a, b);
    }

    /// WC 証明は RC で成り立つものにだけ出て、必ず検査を通る
    #[test]
    fn wc_proofs_check(a in oworm(), b in oworm(), n in letter()) {
        let target = Worm::new(std::iter::once(n).chain(b.letters().iter().cloned()).collect());
        let holds = entails(&Spf::from(&a), &Spf::from(&target));
        match wc::prove(&a, &target) {
            Ok(p) => {
                prop_assert!(holds);
                let c = wc::check(&p).map_err(|e| TestCaseError::fail(format!("{a} ⊢ {target}: {e}")))?;
                prop_assert_eq!(c, &WSeq { lhs: a, rhs: target });
            }
            Err(_) => prop_assert!(!holds),
        }
    }

    /// 順序を保つ付け替えをしても、どの方法の答えも変わらない。
    /// さらに自然数の worm の o(A) による比較とも一致する。
    #[test]
    fn relabeling_invariance(a in nworm(), b in nworm()) {
        let (ra, rb) = (relabel(&a), relabel(&b));
        let by_o = a.cmp0(&b) == Ordering::Less;
        prop_assert_eq!(ra.lt_n(&rb, Veblen::zero()), by_o);
        prop_assert_eq!(headbody::lt(Veblen::zero(), &ra, &rb), Some(by_o));
        prop_assert_eq!(wc::decide(&ra, &rb), wc::decide(&a, &b));
    }

    /// 表示 → パースで元に戻る
    #[test]
    fn display_parse_roundtrip(a in oworm()) {
        prop_assert_eq!(a.to_string().parse::<Worm<Veblen>>().unwrap(), a.clone());
        prop_assert_eq!(a.to_formula().parse::<Worm<Veblen>>().unwrap(), a);
    }
}

#[test]
fn examples() {
    let w = |s: &str| s.parse::<Worm<Veblen>>().unwrap();
    // ⟨ω⟩⊤ はすべての有限 worm より大きい（ここでは ⟨3⟩⟨3⟩⟨3⟩⊤ と比べる）
    assert!(w("3, 3, 3").lt_n(&w("ω"), Veblen::zero()));
    // ⟨ε_0⟩⊤ ⊢ ⟨ω⟩⟨ω⟩⊤
    assert!(wc::decide(&w("ε_0"), &w("ω, ω")));
    let p = wc::prove(&w("ε_0"), &w("ω, ω")).unwrap();
    assert!(wc::check(&p).is_ok());
    // ⟨ω⟩⟨0⟩⟨ω⟩⊤ と ⟨ω + 1⟩⊤ は比較すると後者が大きい
    assert!(w("ω, 0, ω").lt_n(&w("ω + 1"), Veblen::zero()));
}
