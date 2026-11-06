//! Beklemishev の括弧記法（autonomous worm）。
//!
//! worm の文字そのものを worm で書く記法。順序数を一切使わずに、括弧だけで
//! Γ0 未満のすべての順序数を表せる。
//!
//! 出典：D. Fernández-Duque & E. Hermo Reyes, "Deducibility and Independence in
//! Beklemishev's Autonomous Provability Calculus" (arXiv:2008.13445)。
//!
//! # 定義（Def. 19）
//! - 括弧語は ⊤ と、括弧語 a, b から作る (a)b。最後の ⊤ は省略して
//!   (a_1)(a_2)…(a_k) と書く。括弧の中の ⊤ も省略するので、() = (⊤)⊤。
//! - 翻訳：⊤* = ⊤、((a)b)* = ⟨o(a*)⟩b*。つまり各文字 a_i を、それ自身が表す
//!   順序数 o*(a_i) = o(a_i*) に置き換えた worm。
//!
//! 例：() = ⟨0⟩⊤ で 1、()() で 2、(()) = ⟨1⟩⊤ で ω、((())) = ⟨ω⟩⊤ で ε_0、
//!     (((()))) = ⟨ε_0⟩⊤ で φ(ε_0, 0)。入れ子の深さが 1 増えるごとに
//!     h(n+1) = e^{h(n)}(1) まで届き（Prop. 23）、その上限が Γ0。
//!
//! # 基本列と battle（§8, Thm 42, Thm 52）
//! a = (a_1)…(a_k) に対し a{n} を
//! - a_1 = ⊤ なら (a_2)…(a_k)
//! - そうでなければ、a_1 より小さい文字が最初に現れる位置 ℓ で区切り、
//!   b = (a_1{n})(a_2)…(a_{ℓ−1})、c = (a_ℓ)…(a_k) として a{n} = b^{n+1} c
//!
//! と定める（先頭の文字そのものも再帰的に基本列で下げる）。文字が有限なら
//! これまでの worm battle と同じ。a⦃0⦄ = a、a⦃n+1⦄ = a⦃n⦄{n+1} はいつか必ず ⊤ に
//! なる（Thm 42）が、この事実は ATR₀ では証明できない（Thm 52）。

use crate::headbody::is_bnf;
use crate::transfinite::hyperexp;
use crate::veblen::Veblen;
use crate::worm::Worm;
use std::cmp::Ordering;
use std::fmt;
use std::str::FromStr;

/// 括弧語。中身は文字（それ自身も括弧語）の列で、空なら ⊤。
///
/// 【Rust メモ】`Vec<Bracket>` の中に自分自身の型が入る再帰的な型。
/// `Vec` が中身をヒープに置くので、`Box` を挟まなくても定義できる。
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Bracket(Vec<Bracket>);

impl Bracket {
    /// ⊤
    pub fn top() -> Self {
        Bracket(Vec::new())
    }

    pub fn new(letters: Vec<Bracket>) -> Self {
        Bracket(letters)
    }

    pub fn letters(&self) -> &[Bracket] {
        &self.0
    }

    pub fn is_top(&self) -> bool {
        self.0.is_empty()
    }

    /// (a) を先頭に付けた語 (a)b。
    pub fn prepend(&self, a: Bracket) -> Bracket {
        let mut v = vec![a];
        v.extend(self.0.iter().cloned());
        Bracket(v)
    }

    /// 括弧の入れ子の深さ N(a)。⊤ は 0、() は 1、(()) は 2。
    pub fn depth(&self) -> usize {
        self.0.iter().map(|a| a.depth() + 1).max().unwrap_or(0)
    }

    /// 翻訳 a*：各文字を、それが表す順序数に置き換えた worm。
    pub fn to_worm(&self) -> Worm<Veblen> {
        Worm::new(self.0.iter().map(|a| a.ordinal()).collect())
    }

    /// o*(a) = o(a*) < Γ0。
    pub fn ordinal(&self) -> Veblen {
        self.to_worm().ordinal()
    }

    /// α < Γ0 を表す括弧語（正規形）。
    /// α を表す標準形の worm を作り、その各文字を再帰的に括弧語にする。
    pub fn from_ordinal(alpha: &Veblen) -> Bracket {
        let w = Worm::from_veblen(alpha);
        Bracket(w.letters().iter().map(Bracket::from_ordinal).collect())
    }

    /// 同じ順序数を表す正規形の括弧語。
    pub fn normal_form(&self) -> Bracket {
        Bracket::from_ordinal(&self.ordinal())
    }

    /// 論文の意味での正規形（Def. 31）か：各文字が正規形で、a* が Beklemishev 標準形。
    pub fn is_normal(&self) -> bool {
        self.0.iter().all(Bracket::is_normal) && is_bnf(&self.to_worm())
    }

    /// 表す順序数どうしの比較。
    pub fn cmp_ordinal(&self, other: &Bracket) -> Ordering {
        self.ordinal().cmp(&other.ordinal())
    }

    /// 基本列 a{n}（⊤ なら `None`）。
    pub fn fundamental(&self, n: usize) -> Option<Bracket> {
        let (a1, _) = self.0.split_first()?;
        if a1.is_top() {
            return Some(Bracket(self.0[1..].to_vec()));
        }
        let o1 = a1.ordinal();
        let l = self.0[1..]
            .iter()
            .position(|x| x.ordinal() < o1)
            .map_or(self.0.len(), |p| p + 1);
        let mut b = vec![a1.fundamental(n).expect("a_1 ≠ ⊤")];
        b.extend(self.0[1..l].iter().cloned());
        let mut out = Vec::with_capacity(b.len() * (n + 1) + self.0.len() - l);
        for _ in 0..=n {
            out.extend(b.iter().cloned());
        }
        out.extend(self.0[l..].iter().cloned());
        Some(Bracket(out))
    }

    /// a⦃0⦄ = a、a⦃n+1⦄ = a⦃n⦄{n+1} を順に返すイテレータ（⊤ で終わる）。
    pub fn battle(&self) -> BracketBattle {
        BracketBattle { current: Some(self.clone()), step: 0 }
    }

    /// 自然数の worm を括弧語にする（文字 n は ()^n）。
    pub fn from_nat_worm(a: &Worm) -> Bracket {
        let nat = |n: u32| Bracket(vec![Bracket::top(); n as usize]);
        Bracket(a.letters().iter().map(|&n| nat(n)).collect())
    }

    /// Thm 52 の列：a_0 = ⊤、a_1 = ()、a_{n+2} = (((a_n)))。
    pub fn thm52_a(n: usize) -> Bracket {
        match n {
            0 => Bracket::top(),
            1 => Bracket(vec![Bracket::top()]),
            _ => {
                let inner = Bracket::thm52_a(n - 2);
                Bracket(vec![Bracket(vec![Bracket(vec![inner])])])
            }
        }
    }

    /// Thm 52 の a'_m = ()a_m。ここから始めた battle の長さ G(m) は、
    /// ATR₀ で全域性を証明できるどんな関数よりも速く増える。
    pub fn thm52(m: usize) -> Bracket {
        Bracket::thm52_a(m).prepend(Bracket::top())
    }
}

/// 深さの評価に使う h(n)：h(0) = 0、h(n+1) = e^{h(n)}(1)。h(n) → Γ0。
/// Prop. 23：N(a) = n なら h(n) ≤ o*(a) < h(n+1)。
pub fn depth_bound(n: usize) -> Veblen {
    (0..n).fold(Veblen::zero(), |h, _| hyperexp(&h, &Veblen::one()))
}

/// 括弧語の battle。
pub struct BracketBattle {
    current: Option<Bracket>,
    step: usize,
}

impl Iterator for BracketBattle {
    type Item = Bracket;

    fn next(&mut self) -> Option<Bracket> {
        let cur = self.current.take()?;
        self.step += 1;
        self.current = cur.fundamental(self.step);
        Some(cur)
    }
}

// ----------------------------------------------------------------------
// 表示とパース
// ----------------------------------------------------------------------

impl Bracket {
    /// 最後の ⊤ を省いた中身（⊤ なら空文字列）。
    fn body(&self) -> String {
        self.0.iter().map(|a| format!("({})", a.body())).collect()
    }
}

impl fmt::Display for Bracket {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_top() { write!(f, "⊤") } else { write!(f, "{}", self.body()) }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseBracketError(pub String);

impl fmt::Display for ParseBracketError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "括弧語として読めません: {}", self.0)
    }
}

impl std::error::Error for ParseBracketError {}

/// `"((()))"`, `"()(())"`, `"⊤"`, `""` などを読む（空白と末尾の ⊤ / T は無視）。
impl FromStr for Bracket {
    type Err = ParseBracketError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let chars: Vec<char> = s.chars().filter(|c| !c.is_whitespace()).collect();
        let mut pos = 0;
        let w = parse_word(&chars, &mut pos);
        // 末尾の ⊤ は許す
        while pos < chars.len() && matches!(chars[pos], '⊤' | 'T') {
            pos += 1;
        }
        if pos != chars.len() {
            return Err(ParseBracketError(s.to_string()));
        }
        w.ok_or_else(|| ParseBracketError(s.to_string()))
    }
}

/// word := ('(' word ')')*
fn parse_word(chars: &[char], pos: &mut usize) -> Option<Bracket> {
    let mut letters = Vec::new();
    while *pos < chars.len() && chars[*pos] == '(' {
        *pos += 1;
        let inner = parse_word(chars, pos)?;
        if *pos >= chars.len() || chars[*pos] != ')' {
            return None;
        }
        *pos += 1;
        letters.push(inner);
    }
    Some(Bracket(letters))
}

impl serde::Serialize for Bracket {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.collect_str(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn b(s: &str) -> Bracket {
        s.parse().unwrap_or_else(|e| panic!("{s}: {e}"))
    }

    fn o(s: &str) -> String {
        b(s).ordinal().to_string()
    }

    #[test]
    fn known_values() {
        assert_eq!(o("⊤"), "0");
        assert_eq!(o("()"), "1");
        assert_eq!(o("()()()"), "3");
        assert_eq!(o("(())"), "ω");
        assert_eq!(o("()(())"), "ω + 1");
        assert_eq!(o("(())(())"), "ω^2");
        assert_eq!(o("(()())"), "ω^ω");
        assert_eq!(o("((()))"), "ε_0");
        assert_eq!(o("((()))((()))"), "ε_1");
        assert_eq!(o("((())(()))"), "φ(2, 0)"); // 文字 (())(()) = ω^2
        assert_eq!(o("((()()))"), "φ(ω, 0)"); // 文字 (()()) = ω^ω
        assert_eq!(o("(((())))"), "φ(ε_0, 0)");
    }

    #[test]
    fn parse_and_display() {
        for s in ["⊤", "()", "(())()", "((()))(()())"] {
            assert_eq!(b(s).to_string(), s);
        }
        assert_eq!(b("(())⊤"), b("(())"));
        assert_eq!(b(""), Bracket::top());
        assert!("(()".parse::<Bracket>().is_err());
        assert!("())".parse::<Bracket>().is_err());
    }

    #[test]
    fn normal_forms() {
        // ⟨1⟩⟨0⟩⊤ ≡ ⟨1⟩⊤ なので (())() の正規形は (())
        assert_eq!(b("(())()").normal_form(), b("(())"));
        assert!(b("(())").is_normal());
        assert!(!b("(())()").is_normal());
        for s in ["()", "(())", "((()))", "(((())))", "()((()))"] {
            assert!(b(s).is_normal(), "{s}");
            assert_eq!(b(s).normal_form(), b(s));
        }
    }

    #[test]
    fn depth_bounds() {
        assert_eq!(depth_bound(1).to_string(), "1");
        assert_eq!(depth_bound(2).to_string(), "ω");
        assert_eq!(depth_bound(3).to_string(), "ε_0");
        assert_eq!(depth_bound(4).to_string(), "φ(ε_0, 0)");
    }

    #[test]
    fn fundamental_sequence() {
        // (())  = ω：(()){n} = ()^{n+1}
        assert_eq!(b("(())").fundamental(2), Some(b("()()()")));
        // ((())) = ε_0：先頭の文字 (()) = ω を ()() = 2 に下げて n+1 回並べる
        assert_eq!(b("((()))").fundamental(1), Some(b("(()())(()())")));
        assert_eq!(b("((()))").fundamental(1).unwrap().ordinal().to_string(), "ω^ω^2");
        assert_eq!(Bracket::top().fundamental(3), None);
    }

    #[test]
    fn thm52_sequence() {
        let os: Vec<String> = (0..5).map(|m| Bracket::thm52(m).ordinal().to_string()).collect();
        assert_eq!(os, ["1", "2", "ε_0 + 1", "φ(ε_0, 0) + 1", "φ(φ(φ(ε_0, 0), 0), 0) + 1"]);
    }
}
