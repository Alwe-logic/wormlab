//! head/body 比較と WC 証明器の性質ベースのテスト。
//!
//! - head/body 再帰（Thm 3.17）は o(A) とも RC とも独立な方法。3 者が一致するか。
//! - WC 証明器は、RC で成り立つ worm シーケントにはすべて証明を出し、
//!   出した証明は検査器を通り、成り立たないものは拒否するか。
//!   （デバッグビルドでは、証明器が再帰の途中で立てる部分目標がすべて
//!   RC で成り立つことも assert で確かめている。）

use proptest::prelude::*;
use std::cmp::Ordering;
use wormlab_core::rc::entails;
use wormlab_core::wc::{self, WSeq};
use wormlab_core::{Spf, Worm, headbody};

fn worm() -> impl Strategy<Value = Worm> {
    prop::collection::vec(0u32..4, 0..8).prop_map(Worm::new)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    #[test]
    fn headbody_matches_ordinals(a in worm(), b in worm()) {
        let by_o = a.cmp0(&b) == Ordering::Less;
        prop_assert_eq!(headbody::lt(0, &a, &b), Some(by_o), "{} vs {}", a, b);
        prop_assert_eq!(headbody::equiv(&a, &b), a.equiv(&b), "{} vs {}", a, b);
    }

    #[test]
    fn headbody_matches_rc_on_n_worms(a in worm(), b in worm(), n in 0u32..3, extra in 0u32..3) {
        // 文字を n + extra だけ上げて n-worm にし、<_n を RC と比べる
        let (a, b) = (a.up(n + extra), b.up(n + extra));
        prop_assert_eq!(headbody::lt(n, &a, &b), Some(a.lt_n(&b, n)), "{} <_{} {}", a, n, b);
    }

    #[test]
    fn wc_proves_exactly_rc_theorems(a in worm(), b in worm()) {
        let holds = entails(&Spf::from(&a), &Spf::from(&b));
        match wc::prove(&a, &b) {
            Ok(p) => {
                prop_assert!(holds);
                let c = wc::check(&p).map_err(|e| TestCaseError::fail(format!("{a} ⊢ {b}: {e}")))?;
                prop_assert_eq!(c, &WSeq { lhs: a, rhs: b });
            }
            Err(_) => prop_assert!(!holds),
        }
    }

    #[test]
    fn wc_proves_worm_order(a in worm(), b in worm(), n in 0u32..3) {
        if a.lt_n(&b, n) {
            let p = wc::prove_lt(n, &a, &b).unwrap();
            prop_assert!(wc::check(&p).is_ok());
        } else {
            prop_assert!(wc::prove_lt(n, &a, &b).is_err());
        }
    }
}
