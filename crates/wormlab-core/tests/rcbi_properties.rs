//! RC_BI（Pakhomov–Lazar, arXiv:2610.20115）の判定器の性質ベースのテスト。
//!
//! 判定は「M_A の根で B が真」（Thm 3.19）。これを次の方向から確かめる：
//! - M_A は本当に RC_BIω モデルで（フレーム条件 I〜IV、Prop 3.15）、根で A が真（Prop 3.10）
//! - 公理（Def 2.5 の 15 個）のランダムな実例はすべて真と判定される
//! - 判定した関係は規則（Mod₁・Mod₂・Mod₃・Cut・∧）で閉じている
//! - ⟨1⟩ だけの式では、既存の RC の判定（添字を 1 ずらす）と一致する
//! - 持つ添字の範囲（N）を広げても答えは変わらない
//! - Lemma 3.16：⟨2⟩_α A ⊢ ⟨2⟩_α(A ∧ ⟨1⟩_ω A)

use proptest::prelude::*;
use wormlab_core::rc;
use wormlab_core::rcbi::{Formula, Model, Rank, entails};
use wormlab_core::Spf;

/// ランダムな閉じた式（⟨1⟩₁₋₃、⟨1⟩_ω、⟨2⟩₂₋₃、↓、∇、∧）
fn formula() -> impl Strategy<Value = Formula> {
    let leaf = Just(Formula::Top);
    leaf.prop_recursive(4, 10, 2, |inner| {
        prop_oneof![
            2 => (inner.clone(), inner.clone()).prop_map(|(a, b)| Formula::and(a, b)),
            3 => (1u32..4, inner.clone()).prop_map(|(k, a)| Formula::one(k, a)),
            1 => inner.clone().prop_map(Formula::one_omega),
            2 => (2u32..4, inner.clone()).prop_map(|(k, a)| Formula::two(k, a)),
            2 => inner.clone().prop_map(Formula::down),
            1 => inner.prop_map(Formula::nabla),
        ]
    })
}

/// ∇ と ⟨1⟩_ω を含まない式（W_BI）
fn wbi() -> impl Strategy<Value = Formula> {
    let leaf = Just(Formula::Top);
    leaf.prop_recursive(4, 10, 2, |inner| {
        prop_oneof![
            2 => (inner.clone(), inner.clone()).prop_map(|(a, b)| Formula::and(a, b)),
            3 => (1u32..4, inner.clone()).prop_map(|(k, a)| Formula::one(k, a)),
            2 => (2u32..4, inner.clone()).prop_map(|(k, a)| Formula::two(k, a)),
            2 => inner.prop_map(Formula::down),
        ]
    })
}

/// モダリティ ⟨i⟩_α（i = 1 なら α ∈ {1, 2, 3, ω}、i = 2 なら α ∈ {2, 3}）
fn modality() -> impl Strategy<Value = (u8, Rank)> {
    prop_oneof![
        (1u32..4).prop_map(|k| (1u8, Rank::Fin(k))),
        Just((1u8, Rank::Omega)),
        (2u32..4).prop_map(|k| (2u8, Rank::Fin(k))),
    ]
}

fn dia((i, r): (u8, Rank), a: Formula) -> Formula {
    Formula::dia(i, r, a)
}

/// 変数のない RC の式（モダリティ 0〜2）
fn rc_formula() -> impl Strategy<Value = Spf> {
    let leaf = Just(Spf::Top);
    leaf.prop_recursive(4, 12, 2, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Spf::and(a, b)),
            (0u32..3, inner).prop_map(|(n, a)| Spf::dia(n, a)),
        ]
    })
}

/// RC の式 ⟨n⟩ を ⟨1⟩_{n+1} に直す
fn from_rc(a: &Spf) -> Formula {
    match a {
        Spf::Top => Formula::Top,
        Spf::Var(p) => Formula::var(p),
        Spf::And(x, y) => Formula::and(from_rc(x), from_rc(y)),
        Spf::Dia(n, x) => Formula::one(n + 1, from_rc(x)),
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// Prop 3.15・3.10：M_A は RC_BIω モデルで、根で A が真
    #[test]
    fn m_a_is_a_model(a in formula()) {
        let m = Model::of(&a, 3);
        let v = m.frame_violations();
        prop_assert!(v.is_empty(), "{}: {:?}\n{}", a, v, m);
        prop_assert!(m.holds(0, &a), "{} が M_A の根で偽", a);
    }

    /// 公理 1〜15 のランダムな実例
    #[test]
    fn axioms_hold(a in formula(), b in formula(), m1 in modality(), m2 in modality()) {
        let t = Formula::Top;
        let mut cases: Vec<(String, Formula, Formula)> = Vec::new();
        let mut add = |name: &str, l: Formula, r: Formula| cases.push((name.to_string(), l, r));
        let ((i, al), (j, be)) = (m1, m2);
        // 1. ⟨i⟩_α A ⊢ ⟨i⟩_β A（β < α）
        if be < al && wormlab_core::rcbi::valid_modality(i, be) {
            add("1", dia(m1, a.clone()), Formula::dia(i, be, a.clone()));
        }
        // 2. ⟨2⟩_α A ⊢ ⟨1⟩_α A
        if i == 2 {
            add("2", dia(m1, a.clone()), Formula::dia(1, al, a.clone()));
        }
        add("3", a.clone(), Formula::nabla(a.clone()));
        add("4", Formula::one(1, a.clone()), Formula::nabla(a.clone()));
        add("5", Formula::down(a.clone()), Formula::nabla(a.clone()));
        // 6. ⟨i⟩_α⟨j⟩_α A ⊢ ⟨j⟩_α A
        if wormlab_core::rcbi::valid_modality(j, al) {
            add("6", dia(m1, Formula::dia(j, al, a.clone())), Formula::dia(j, al, a.clone()));
        }
        add("7", Formula::nabla(Formula::nabla(a.clone())), Formula::nabla(a.clone()));
        add("8", Formula::nabla(Formula::one(1, a.clone())), Formula::one(1, a.clone()));
        add("9", Formula::one(1, Formula::nabla(a.clone())), Formula::one(1, a.clone()));
        add("10", Formula::down(Formula::nabla(a.clone())), Formula::down(a.clone()));
        // 11. ⟨2⟩_α A ∧ ⟨1⟩₁B ⊢ ⟨2⟩_α(A ∧ ↓B)
        if i == 2 {
            add("11", Formula::and(dia(m1, a.clone()), Formula::one(1, b.clone())),
                dia(m1, Formula::and(a.clone(), Formula::down(b.clone()))));
        }
        // 12. ⟨i⟩_α A ∧ ⟨j⟩_β B ⊢ ⟨i⟩_α(A ∧ ⟨j⟩_β B)（β < α または α = β = ω）
        if be < al || (al == Rank::Omega && be == Rank::Omega) {
            add("12", Formula::and(dia(m1, a.clone()), dia(m2, b.clone())),
                dia(m1, Formula::and(a.clone(), dia(m2, b.clone()))));
        }
        add("13", Formula::down(t.clone()), Formula::one_omega(t.clone()));
        add("14", Formula::down(Formula::one(1, a.clone())), Formula::one_omega(Formula::down(a.clone())));
        add("15", Formula::and(a.clone(), Formula::two(2, b.clone())),
            Formula::nabla(Formula::and(Formula::down(a.clone()), b.clone())));
        // 自明な公理
        add("Id", a.clone(), a.clone());
        add("⊤", a.clone(), t);
        for (name, l, r) in cases {
            prop_assert!(entails(&l, &r), "公理 {}: {} ⊢ {} が偽と判定された", name, l, r);
        }
    }

    /// 判定した関係が規則で閉じている（Mod₁・Mod₂・Mod₃・L∧・R∧）
    #[test]
    fn closed_under_rules(a in formula(), b in formula(), c in formula(), m in modality()) {
        if entails(&a, &b) {
            prop_assert!(entails(&dia(m, a.clone()), &dia(m, b.clone())), "Mod₁");
            prop_assert!(entails(&Formula::down(a.clone()), &Formula::down(b.clone())), "Mod₂");
            prop_assert!(entails(&Formula::nabla(a.clone()), &Formula::nabla(b.clone())), "Mod₃");
            prop_assert!(entails(&Formula::and(a.clone(), c.clone()), &b), "L∧₁");
            prop_assert!(entails(&Formula::and(c.clone(), a.clone()), &b), "L∧₂");
            if entails(&a, &c) {
                prop_assert!(entails(&a, &Formula::and(b.clone(), c.clone())), "R∧");
            }
        }
    }

    /// Cut：A ⊢ B かつ B ⊢ C なら A ⊢ C（B は A を弱めて作り、真の例を増やす）
    #[test]
    fn closed_under_cut(a in formula(), m in modality(), c in formula()) {
        // A ∧ ⟨m⟩A ⊢ ⟨m⟩A は常に真
        let lhs = Formula::and(a.clone(), dia(m, a.clone()));
        let mid = dia(m, a.clone());
        prop_assert!(entails(&lhs, &mid));
        if entails(&mid, &c) {
            prop_assert!(entails(&lhs, &c), "Cut: {} ⊢ {} ⊢ {}", lhs, mid, c);
        }
    }

    /// ⟨1⟩ だけの式では、RC の判定（⟨n⟩ ↦ ⟨1⟩_{n+1}）と一致する
    #[test]
    fn one_fragment_is_rc(a in rc_formula(), b in rc_formula()) {
        prop_assert_eq!(entails(&from_rc(&a), &from_rc(&b)), rc::entails(&a, &b), "{} ⊢ {}", a, b);
    }

    /// 持つ添字の範囲を広げても答えは変わらない
    #[test]
    fn rank_bound_is_enough(a in formula(), b in formula()) {
        let n = a.max_rank().max(b.max_rank()).max(2);
        let small = Model::of(&a, n).holds(0, &b);
        let large = Model::of(&a, n + 2).holds(0, &b);
        prop_assert_eq!(small, large, "{} ⊢ {}", a, b);
    }

    /// Lemma 3.16
    #[test]
    fn lemma_3_16(a in formula(), k in 2u32..4) {
        let l = Formula::two(k, a.clone());
        let r = Formula::two(k, Formula::and(a.clone(), Formula::one_omega(a.clone())));
        prop_assert!(entails(&l, &r), "{} ⊢ {}", l, r);
    }

    /// W_BI の式どうしの比較が反射的にならない（A <¹₁ A は偽）。整礎性の最小限の確認
    #[test]
    fn irreflexive(a in wbi()) {
        prop_assert!(!entails(&a, &Formula::one(1, a.clone())), "{} <¹₁ {}", a, a);
    }
}

/// ⟨1⟩ だけの worm（文字 1〜3）はすべて ↓⊤（ε₀）より下
#[test]
fn one_worms_below_down_top() {
    let down = Formula::down(Formula::Top);
    for code in 0..3u32.pow(6) {
        let mut letters = Vec::new();
        let mut c = code;
        for _ in 0..6 {
            letters.push(1 + c % 3);
            c /= 3;
        }
        let w = letters.iter().rev().fold(Formula::Top, |acc, &k| Formula::one(k, acc));
        assert!(entails(&down, &Formula::one(1, w.clone())), "{w} は ↓⊤ より下のはず");
    }
}
