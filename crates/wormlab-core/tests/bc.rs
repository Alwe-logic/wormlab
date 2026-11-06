//! Bracket Calculus と、順序数を使わない括弧語の比較のテスト。
//!
//! - 段階1：順序数を使わない比較・正規形が、Veblen 表記を経由する版と一致するか
//!   （小さい括弧語は全部、大きいものはランダムに）
//! - 段階2：BC の判定（順序数なし）が、τ で RC_Γ0 に翻訳した判定と一致するか（Thm 38）
//! - 段階3：BC の導出がいつも検査を通り、結論が目標のシーケントか。
//!   さらに、導出の各行を τ で翻訳すると RC_Γ0 で正しいか（Lemma 30 の健全性）

use proptest::prelude::*;
use wormlab_core::bc::{self, BSeq, BcRule, Formula};
use wormlab_core::rc::entails;
use wormlab_core::Bracket;

/// 括弧の対がちょうど k 個の括弧語すべて（個数はカタラン数）。
fn all_brackets(k: usize) -> Vec<Bracket> {
    if k == 0 {
        return vec![Bracket::top()];
    }
    let mut out = Vec::new();
    for j in 0..k {
        for first in all_brackets(j) {
            for rest in all_brackets(k - 1 - j) {
                out.push(rest.prepend(first.clone()));
            }
        }
    }
    out
}

fn upto(k: usize) -> Vec<Bracket> {
    (0..=k).flat_map(all_brackets).collect()
}

/// ランダムな括弧語（入れ子は 4 段まで）
fn bracket() -> impl Strategy<Value = Bracket> {
    let leaf = Just(Bracket::top());
    leaf.prop_recursive(4, 24, 3, |inner| prop::collection::vec(inner, 0..4).prop_map(Bracket::new))
}

#[test]
fn catalan_counts() {
    let counts: Vec<usize> = (0..7).map(|k| all_brackets(k).len()).collect();
    assert_eq!(counts, [1, 1, 2, 5, 14, 42, 132]);
}

/// 対が 6 個以下の括弧語（197 個）のすべての組で、比較が一致する。
#[test]
fn syntactic_comparison_exhaustive() {
    let ws = upto(6);
    let ords: Vec<_> = ws.iter().map(|a| a.ordinal()).collect();
    for (a, oa) in ws.iter().zip(&ords) {
        for (b, ob) in ws.iter().zip(&ords) {
            assert_eq!(a.cmp_syntactic(b), oa.cmp(ob), "{a} と {b}（o* = {oa}, {ob}）");
        }
    }
}

/// 対が 8 個以下の括弧語（2,056 個）すべてで、正規形が一致する。
#[test]
fn syntactic_normal_form_exhaustive() {
    let mut normal = 0;
    for a in upto(8) {
        let nf = a.normal_form_syntactic();
        assert_eq!(nf, a.normal_form(), "{a}");
        assert_eq!(a.is_normal_syntactic(), a.is_normal(), "{a}");
        if nf == a {
            normal += 1;
        }
    }
    // 正規形の語は「表す順序数」と 1 対 1（Thm 32）なので、ここで数えた個数は
    // 対が 8 個以下の正規形で表せる順序数の個数
    assert!(normal > 0);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// 大きめのランダムな括弧語でも比較が一致する
    #[test]
    fn syntactic_comparison_random(a in bracket(), b in bracket()) {
        prop_assert_eq!(a.cmp_syntactic(&b), a.ordinal().cmp(&b.ordinal()), "{} と {}", a, b);
    }

    /// 大きめのランダムな括弧語でも正規形が一致する
    #[test]
    fn syntactic_normal_form_random(a in bracket()) {
        prop_assert_eq!(a.normal_form_syntactic(), a.normal_form(), "{}", a);
    }
}

// ----------------------------------------------------------------------
// 段階2・3：BC の判定と導出
// ----------------------------------------------------------------------

/// モダリティに使う括弧語（正規形でないもの (())() ≡ (()) と ((())()) ≡ ((())) も混ぜる）
const POOL: [&str; 9] = ["", "()", "()()", "(())", "(())()", "()(())", "(()())", "((()))", "((())())"];

fn modality() -> impl Strategy<Value = Bracket> {
    prop::sample::select(POOL.to_vec()).prop_map(|s| s.parse::<Bracket>().unwrap())
}

/// 変数 p, q と上のモダリティからなるランダムな BC の式
fn formula() -> impl Strategy<Value = Formula> {
    let leaf = prop_oneof![Just(Formula::Top), Just(Formula::var("p")), Just(Formula::var("q"))];
    leaf.prop_recursive(4, 14, 2, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Formula::and(a, b)),
            (modality(), inner).prop_map(|(m, a)| Formula::dia(m, a)),
        ]
    })
}

/// 導出を検査し、結論が目標と一致することを確かめる。
fn checked(p: &bc::BcProof, goal: &BSeq) -> Result<(), TestCaseError> {
    let c = bc::check(p).map_err(|e| TestCaseError::fail(format!("{goal}: {e}")))?;
    prop_assert_eq!(c, goal);
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// Thm 38：順序数を使わない判定と、τ で RC_Γ0 に翻訳した判定が一致し、
    /// 成り立つときに限り導出ができて検査を通る
    #[test]
    fn decision_matches_tau_and_derivations(a in formula(), b in formula()) {
        let holds = bc::decide(&a, &b);
        prop_assert_eq!(holds, bc::decide_tau(&a, &b), "{} ⊢ {}", a, b);
        let goal = BSeq::new(a.clone(), b.clone());
        match bc::derive(&a, &b) {
            Ok((p, _)) => {
                prop_assert!(holds, "{} は偽なのに導出ができた", goal);
                checked(&p, &goal)?;
            }
            Err(_) => prop_assert!(!holds, "{} は真なのに導出ができない", goal),
        }
    }

    /// 真になりやすい組（右辺を左辺から作る）でも導出が検査を通る
    #[test]
    fn derivations_for_weakened_rhs(a in formula(), m in modality(), k in modality()) {
        let lhs = Formula::and(Formula::dia(m.clone(), a.clone()), Formula::dia(k.clone(), a.clone()));
        let rhs = Formula::dia(Bracket::top(), a.clone());
        let goal = BSeq::new(lhs.clone(), rhs.clone());
        let (p, _) = bc::derive(&lhs, &rhs).map_err(TestCaseError::fail)?;
        checked(&p, &goal)?;
    }

    /// 括弧語どうしの比較 b ◁ a の導出：作れる ⟺ 順序数を使わない比較で b < a
    #[test]
    fn worm_comparisons(a in modality(), b in modality()) {
        let less = b.cmp_syntactic(&a) == std::cmp::Ordering::Less;
        match bc::derive_lt(&b, &a) {
            Ok((p, _)) => {
                prop_assert!(less, "{} ◁ {} ではないのに導出ができた", b, a);
                checked(&p, &BSeq::lt(&b, &a))?;
            }
            Err(_) => prop_assert!(!less, "{} ◁ {} なのに導出ができない", b, a),
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(40))]

    /// Lemma 30（健全性）：導出の各行を τ で翻訳すると RC_Γ0 で成り立ち、
    /// 副条件 a ⊢ ()b は本当に o*(b) < o*(a) を表している
    #[test]
    fn every_line_is_sound_under_tau(a in formula(), b in formula()) {
        if let Ok((p, _)) = bc::derive(&a, &b) {
            for node in &p.nodes {
                let t = node.conclusion.tau();
                prop_assert!(entails(&t.lhs, &t.rhs), "τ で偽：{}", node.conclusion);
                if node.rule == BcRule::R4 {
                    let s = &p.nodes[node.premises[0]].conclusion;
                    let (x, y) = (s.lhs.as_worm().unwrap(), s.rhs.as_worm().unwrap());
                    // s は x ⊢ ()z の形で、z = y の先頭の () を外したもの
                    let z = Bracket::new(y.letters()[1..].to_vec());
                    prop_assert!(z.ordinal() < x.ordinal(), "副条件 {}", s);
                }
            }
        }
    }
}

/// 論文の例：ε_0 > ω^ω、ε_1 > ε_0 などを、括弧語のシーケントとして BC で導出する。
#[test]
fn paper_style_examples() {
    for (b, a) in [("(()())", "((()))"), ("((()))", "((()))((()))"), ("((()))((()))", "((())(()))"), ("(((())))", "((((()))))")] {
        let (b, a): (Bracket, Bracket) = (b.parse().unwrap(), a.parse().unwrap());
        let (p, st) = bc::derive_lt(&b, &a).unwrap_or_else(|e| panic!("{e}"));
        let c = bc::check(&p).unwrap_or_else(|e| panic!("{b} ◁ {a}: {e}"));
        assert_eq!(c, &BSeq::lt(&b, &a));
        assert!(st.max_side_depth >= 1, "{b} ◁ {a}");
    }
}
