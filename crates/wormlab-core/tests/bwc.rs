//! BWC（括弧語だけの体系、WC の BC 版）の性質ベースのテスト。
//!
//! - 判定が BC（RC 経由）・τ 経由の RC_Γ0 と一致する（3 つの独立な方法）
//! - 導出が作れる ⟺ 判定が真。作った導出はすべて検査器を通り、結論が入力と一致する
//! - 導出の全行を τ で翻訳すると RC で真（健全性）。副条件の行は文字の比較として正しい

use proptest::prelude::*;
use wormlab_core::bc::{self, Formula};
use wormlab_core::bwc::{self, BwRule, BwSeq};
use wormlab_core::{Bracket, Spf, rc};

/// 正規形でない括弧語も混ぜた文字の候補
const POOL: [&str; 10] = ["", "()", "()()", "(())", "(())()", "()(())", "(()())", "((()))", "((())())", "(()(()))"];

fn letter() -> impl Strategy<Value = Bracket> {
    prop::sample::select(POOL.to_vec()).prop_map(|s| s.parse::<Bracket>().unwrap())
}

/// 文字が上の候補の括弧語（長さ 0〜6）
fn word() -> impl Strategy<Value = Bracket> {
    prop::collection::vec(letter(), 0..7).prop_map(Bracket::new)
}

/// ランダムな括弧語（入れ子は 4 段まで）
fn bracket() -> impl Strategy<Value = Bracket> {
    let leaf = Just(Bracket::top());
    leaf.prop_recursive(4, 24, 3, |inner| prop::collection::vec(inner, 0..4).prop_map(Bracket::new))
}

/// τ で翻訳した worm シーケントが RC で成り立つか（順序数を使う、照合用）。
fn tau_holds(s: &BwSeq) -> bool {
    rc::entails(&Spf::from(&s.lhs.to_worm()), &Spf::from(&s.rhs.to_worm()))
}

fn check_all(a: &Bracket, b: &Bracket) -> Result<(), TestCaseError> {
    let holds = bwc::decide(a, b);
    // 3 つの方法で一致
    prop_assert_eq!(holds, bc::decide(&Formula::worm(a), &Formula::worm(b)), "BC と食い違い：{} ⊢ {}", a, b);
    prop_assert_eq!(holds, tau_holds(&BwSeq::new(a.clone(), b.clone())), "τ 経由と食い違い：{} ⊢ {}", a, b);
    match bwc::prove(a, b) {
        Ok((p, _)) => {
            prop_assert!(holds);
            let c = bwc::check(&p).map_err(|e| TestCaseError::fail(format!("{a} ⊢ {b}: {e}")))?;
            prop_assert_eq!(c, &BwSeq::new(a.clone(), b.clone()));
            // すべての行が τ で健全
            for node in &p.nodes {
                prop_assert!(tau_holds(&node.conclusion), "健全でない行：{}", node.conclusion);
            }
            // A3・R3 の副条件の行は、文字の比較として正しい（τ の健全性からも従うが、念のため直接）
            for node in &p.nodes {
                let sides: &[usize] = match node.rule {
                    BwRule::A3 => &node.premises[..],
                    BwRule::R3 => &node.premises[2..],
                    _ => &[],
                };
                for &s in sides {
                    let c = &p.nodes[s].conclusion;
                    prop_assert!(c.lhs.ordinal() >= c.rhs.ordinal() || tau_holds(c));
                }
            }
        }
        Err(_) => prop_assert!(!holds, "成り立つのに導出できない：{} ⊢ {}", a, b),
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    #[test]
    fn words_over_pool(a in word(), b in word()) {
        check_all(&a, &b)?;
    }

    /// b ◁ a の形（a ⊢ ()b）。成り立つ例を増やすため、大小を見てから並べる
    #[test]
    fn comparisons(x in bracket(), y in bracket()) {
        let (a, b) = if x.cmp_syntactic(&y) == std::cmp::Ordering::Less { (y, x) } else { (x, y) };
        let s = BwSeq::lt(&b, &a);
        check_all(&s.lhs, &s.rhs)?;
    }

    /// 左辺を弱めた右辺（成り立ちやすい）
    #[test]
    fn weakened(a in word(), k in 0usize..4) {
        let n = a.letters().len();
        let b = Bracket::new(a.letters()[..k.min(n)].to_vec());
        check_all(&a, &b)?;
    }
}
