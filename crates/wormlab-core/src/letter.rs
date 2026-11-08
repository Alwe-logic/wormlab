//! worm の「文字」（モダリティの番号）として使える型。
//!
//! RC の判定・head/body 比較・WC の証明は、文字どうしの**大小比較しか使わない**。
//! そこで「比較できて、表示・読み込みができる型」を [`Letter`] trait としてまとめ、
//! 自然数 `u32` でも順序数 [`Veblen`] でも同じコードが動くようにする。
//!
//! 【Rust メモ】trait に `Clone + Ord + …` と書くと「これらの trait も全部
//! 実装している型だけが Letter になれる」という意味になる（スーパートレイト）。
//! 関数を `fn f<L: Letter>(x: &L)` と書けば、u32 用と Veblen 用の 2 つの版を
//! コンパイラが自動で作ってくれる（ジェネリクス、単相化）。

use crate::latex::ToLatex;
use crate::veblen::Veblen;
use serde::Serialize;
use std::fmt::{Debug, Display};
use std::hash::Hash;

pub trait Letter: Clone + Ord + Eq + Hash + Debug + Display + Serialize + ToLatex + 'static {
    /// 最小の文字 0。
    fn zero() -> Self;

    /// 文字 1 つを文字列から読む。
    fn parse_letter(s: &str) -> Option<Self>;

    /// worm 全体の表示。既定は ⟨α⟩⟨β⟩… の形（⊤ は省略）。
    fn fmt_worm(letters: &[Self]) -> String {
        letters.iter().map(|x| format!("⟨{x}⟩")).collect()
    }

    /// worm 全体の LaTeX。既定は `\langle α\rangle\langle β\rangle…\top`。
    fn latex_worm(letters: &[Self]) -> String {
        let mut s: String = letters.iter().map(|x| format!("\\langle {}\\rangle", x.to_latex())).collect();
        s.push_str("\\top");
        s
    }

    /// 区切りの空白だけで文字を並べてよいか（"1 0 2" のような書き方）。
    const SPACE_SEPARATED: bool = false;
}

impl Letter for u32 {
    fn zero() -> Self {
        0
    }

    fn parse_letter(s: &str) -> Option<Self> {
        s.trim().parse().ok()
    }

    /// 自然数の worm は今まで通り "1 0 2" と表示する。
    fn fmt_worm(letters: &[Self]) -> String {
        let s: Vec<String> = letters.iter().map(|n| n.to_string()).collect();
        s.join(" ")
    }

    const SPACE_SEPARATED: bool = true;
}

impl Letter for Veblen {
    fn zero() -> Self {
        Veblen::zero()
    }

    fn parse_letter(s: &str) -> Option<Self> {
        s.trim().parse().ok()
    }
}
