//! 括弧記法（Beklemishev の autonomous worm）の性質ベースのテスト。
//!
//! 論文（Fernández-Duque & Hermo Reyes, arXiv:2008.13445）の主張を、
//! ランダムな括弧語で機械的に確かめる：
//! - Prop. 23：深さ N(a) = n なら h(n) ≤ o*(a) < h(n+1)
//! - Thm 11 / Thm 32：正規形はちょうど 1 つ（こちらの逆写像が論文の正規形を作るか）
//! - Prop. 41：a ≠ ⊤ なら基本列 a{n} は a より小さい
//! - 文字が有限なら、基本列はこれまでの worm battle と一致する

use proptest::prelude::*;
use std::cmp::Ordering;
use wormlab_core::bracket::depth_bound;
use wormlab_core::headbody::is_bnf;
use wormlab_core::{Bracket, Veblen, Worm, headbody};

/// ランダムな括弧語（入れ子は 4 段まで）
fn bracket() -> impl Strategy<Value = Bracket> {
    let leaf = Just(Bracket::top());
    leaf.prop_recursive(4, 24, 3, |inner| prop::collection::vec(inner, 0..4).prop_map(Bracket::new))
}

fn nworm() -> impl Strategy<Value = Worm> {
    prop::collection::vec(0u32..4, 0..7).prop_map(Worm::new)
}

fn vworm() -> impl Strategy<Value = Worm<Veblen>> {
    let pool: Vec<Veblen> = ["0", "1", "2", "ω", "ω + 1", "ω^2", "ε_0", "ε_0 + 1", "φ(2, 0)"]
        .iter()
        .map(|s| s.parse().unwrap())
        .collect();
    prop::collection::vec(prop::sample::select(pool), 0..5).prop_map(Worm::new)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// Prop. 23：入れ子の深さで順序数の範囲が決まる
    #[test]
    fn depth_bounds_ordinal(a in bracket()) {
        let (n, x) = (a.depth(), a.ordinal());
        prop_assert!(depth_bound(n) <= x && x < depth_bound(n + 1),
            "{}：深さ {}、o* = {}、範囲 [{}, {})", a, n, x, depth_bound(n), depth_bound(n + 1));
    }

    /// 逆写像で作った括弧語は同じ順序数を表し、論文の意味で正規形
    #[test]
    fn normal_form_is_normal(a in bracket()) {
        let nf = a.normal_form();
        prop_assert_eq!(nf.ordinal(), a.ordinal(), "{} ↦ {}", a, nf);
        prop_assert!(nf.is_normal(), "{} の正規形 {} が Def. 31 を満たさない", a, nf);
    }

    /// 正規形の一意性（Thm 32）：正規形の語は自分自身が正規形
    #[test]
    fn normal_form_unique(a in bracket()) {
        if a.is_normal() {
            prop_assert_eq!(a.normal_form(), a);
        }
    }

    /// worm の標準形（逆写像の出力）は BNF で、BNF の worm は自分自身が標準形（Thm 11）
    #[test]
    fn bnf_finite(a in nworm()) {
        prop_assert!(is_bnf(&a.normal_form()), "{} の標準形 {}", a, a.normal_form());
        if is_bnf(&a) {
            prop_assert_eq!(a.normal_form(), a);
        }
    }

    #[test]
    fn bnf_transfinite(a in vworm()) {
        prop_assert!(is_bnf(&a.normal_form()), "{} の標準形 {}", a, a.normal_form());
        if is_bnf(&a) {
            prop_assert_eq!(a.normal_form(), a);
        }
    }

    /// Prop. 41：基本列は真に小さくなる
    #[test]
    fn fundamental_decreases(a in bracket(), n in 0usize..4) {
        if let Some(next) = a.fundamental(n) {
            prop_assert!(next.ordinal() < a.ordinal(), "{}{{{}}} = {}", a, n, next);
        }
    }

    /// 文字が有限なら、括弧語の基本列はこれまでの worm battle の 1 ステップと同じ
    #[test]
    fn agrees_with_finite_battle(a in nworm(), n in 0usize..4) {
        let via_bracket = Bracket::from_nat_worm(&a).fundamental(n);
        let via_worm = a.battle_step(n).map(|w| Bracket::from_nat_worm(&w));
        prop_assert_eq!(via_bracket, via_worm);
    }

    /// 比較：o* による比較と、翻訳した worm の head/body 比較が一致
    #[test]
    fn comparison_matches_headbody(a in bracket(), b in bracket()) {
        let by_o = a.cmp_ordinal(&b) == Ordering::Less;
        prop_assert_eq!(headbody::lt(Veblen::zero(), &a.to_worm(), &b.to_worm()), Some(by_o));
    }

    /// 表示 → パースで元に戻る
    #[test]
    fn display_parse_roundtrip(a in bracket()) {
        prop_assert_eq!(a.to_string().parse::<Bracket>().unwrap(), a);
    }
}

/// 小さな括弧語の battle は実際に ⊤ まで届く（Thm 42 の小さな例）
#[test]
fn small_battles_terminate() {
    for s in ["()()", "(())", "(())()", "()(())"] {
        let a: Bracket = s.parse().unwrap();
        let steps: Vec<Bracket> = a.battle().take(10_000).collect();
        assert_eq!(steps.last(), Some(&Bracket::top()), "{s} の battle が 1 万ステップで終わらない");
        // 各ステップで順序数は真に減る
        for w in steps.windows(2) {
            assert!(w[1].ordinal() < w[0].ordinal());
        }
    }
}
