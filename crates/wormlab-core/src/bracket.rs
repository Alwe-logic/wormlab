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
//!
//! # 順序数を使わない比較と正規形
//! `ordinal`・`cmp_ordinal`・`normal_form` は、いったん Veblen 表記の順序数に
//! 直して計算する。これとは別に、括弧語だけで完結する版
//! [`Bracket::cmp_syntactic`]・[`Bracket::normal_form_syntactic`] も用意する
//! （仕組みは [`BracketOrder`] を参照）。両者が一致することはテストで確かめる。
//! 正規形の括弧語は [`NfBracket`] として worm・RC の「文字」に使える。

use crate::headbody::is_bnf;
use crate::letter::Letter;
use crate::transfinite::hyperexp;
use crate::veblen::Veblen;
use crate::worm::Worm;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
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
// 順序数を使わない比較と正規形
// ----------------------------------------------------------------------
//
// o*(a) < o*(b) は「a*, b* を worm として <_0 で比べる」ことと同じ。worm の比較は
// head/body 再帰（headbody.rs、Worms & spiders Thm 3.17）により「文字どうしの大小」
// だけから決まる。括弧語では文字もまた括弧語なので、文字の比較に同じ比較を
// 再帰的に使えばよい。こうすると Veblen 表記を一度も通らずに比較できる。
//
// 停止性：文字の比較に降りるたびに括弧の入れ子が 1 段浅くなり、worm の比較の
// 再帰では長さの和が減る。

/// 順序数を使わない括弧語の比較器。部分問題の答えを覚えておく（メモ化）。
///
/// 等しさは「同じ順序数を表す」という意味（語として違ってもよい）。
/// 例：(())() と (()) はどちらも ω を表すので `Equal`。
#[derive(Default)]
pub struct BracketOrder {
    letters: HashMap<(Bracket, Bracket), Ordering>,
    worms: HashMap<(Vec<Bracket>, Vec<Bracket>, bool), bool>,
    normal: HashMap<Bracket, Bracket>,
}

impl BracketOrder {
    pub fn new() -> Self {
        Self::default()
    }

    /// o*(a) と o*(b) の大小。
    pub fn cmp(&mut self, a: &Bracket, b: &Bracket) -> Ordering {
        if a == b {
            return Ordering::Equal;
        }
        let key = (a.clone(), b.clone());
        if let Some(&o) = self.letters.get(&key) {
            return o;
        }
        let o = if self.worm_rel(&a.0, &b.0, true) {
            Ordering::Less
        } else if self.worm_rel(&b.0, &a.0, true) {
            Ordering::Greater
        } else {
            Ordering::Equal
        };
        self.letters.insert((b.clone(), a.clone()), o.reverse());
        self.letters.insert(key, o);
        o
    }

    /// worm として w ◁ v（`strict`）または w ⊴ v。文字の大小は [`Self::cmp`] で比べる。
    /// 中身は headbody.rs の `HeadBody::rec` と同じ再帰。
    fn worm_rel(&mut self, w: &[Bracket], v: &[Bracket], strict: bool) -> bool {
        if v.is_empty() {
            return !strict && w.is_empty();
        }
        if w.is_empty() {
            return true;
        }
        let key = (w.to_vec(), v.to_vec(), strict);
        if let Some(&ans) = self.worms.get(&key) {
            return ans;
        }
        // λ = 両方に現れる最小の文字
        let mut lambda = &w[0];
        for x in w.iter().chain(v) {
            if self.cmp(x, lambda) == Ordering::Less {
                lambda = x;
            }
        }
        let lambda = lambda.clone();
        let (hw, bw) = self.head_body(w, &lambda);
        let (hv, bv) = self.head_body(v, &lambda);
        let ans = self.worm_rel(w, bv, false) || (self.worm_rel(bw, v, true) && self.worm_rel(hw, hv, strict));
        self.worms.insert(key, ans);
        ans
    }

    /// h_λ(w)（λ より大きい文字の最長の先頭部分）と b_λ(w)（最初の λ の後ろ）。
    fn head_body<'a>(&mut self, w: &'a [Bracket], lambda: &Bracket) -> (&'a [Bracket], &'a [Bracket]) {
        for (i, x) in w.iter().enumerate() {
            match self.cmp(x, lambda) {
                Ordering::Greater => {}
                Ordering::Equal => return (&w[..i], &w[i + 1..]),
                Ordering::Less => return (&w[..i], &[]), // λ は最小なので起こらない
            }
        }
        (w, &[])
    }

    /// 正規形（Def. 31）：文字を再帰的に正規形にしてから、worm を Beklemishev
    /// 標準形（BNF）にする。
    ///
    /// BNF への直し方：最小の文字 α ですべて区切った A_k α … α A_0 の各成分を
    /// 再帰的に BNF にし、**自分より左に自分より大きい成分があるような成分**を、
    /// 隣の α ごと取り除く。順序数で書けば 1 + o(A) = ω^{o(A_0)} + … + ω^{o(A_k)}
    /// （右の成分から足す）で、右に大きい項が来ると左の項が吸収されることに当たる。
    /// 例：(())() は α = ⊤ で成分 [()]、[⊤]。右の ⊤ は左の () より小さいので消えて (())。
    pub fn normal_form(&mut self, a: &Bracket) -> Bracket {
        if let Some(nf) = self.normal.get(a) {
            return nf.clone();
        }
        let letters: Vec<Bracket> = a.0.iter().map(|x| self.normal_form(x)).collect();
        let nf = Bracket(self.bnf(&letters));
        self.normal.insert(a.clone(), nf.clone());
        nf
    }

    /// 文字がすべて正規形の worm を BNF にする。正規形どうしなら
    /// 「同じ順序数 ⟺ 語として同じ」なので、文字の等しさは == で判定できる。
    fn bnf(&mut self, w: &[Bracket]) -> Vec<Bracket> {
        let Some(first) = w.first() else {
            return Vec::new();
        };
        let mut alpha = first;
        for x in w {
            if self.cmp(x, alpha) == Ordering::Less {
                alpha = x;
            }
        }
        let alpha = alpha.clone();
        // 左から A_k, …, A_0。それぞれを BNF に
        let comps: Vec<Vec<Bracket>> = w.split(|x| *x == alpha).map(|c| self.bnf(c)).collect();
        let mut kept: Vec<&Vec<Bracket>> = Vec::new();
        for (t, c) in comps.iter().enumerate() {
            // 左側（添字 s < t）の成分のどれかより真に小さければ吸収される
            let absorbed = (0..t).any(|s| self.worm_rel(c, &comps[s], true));
            if !absorbed {
                kept.push(c);
            }
        }
        let mut out = Vec::new();
        for (i, c) in kept.into_iter().enumerate() {
            if i > 0 {
                out.push(alpha.clone());
            }
            out.extend(c.iter().cloned());
        }
        out
    }

    /// メモが大きくなりすぎたら捨てる（答えには影響しない）。
    fn trim(&mut self) {
        const LIMIT: usize = 1 << 20;
        if self.letters.len() + self.worms.len() + self.normal.len() > LIMIT {
            *self = Self::default();
        }
    }
}

// 【Rust メモ】`thread_local!` はスレッドごとに 1 つずつある変数。ここでは比較の
// メモをプログラム全体で使い回すために使う。`RefCell` は「実行時に借用を検査する
// 箱」で、`borrow_mut()` で中身を書き換えられる。
thread_local! {
    static ORDER: RefCell<BracketOrder> = RefCell::new(BracketOrder::new());
}

impl Bracket {
    /// 順序数を使わない比較（結果は `cmp_ordinal` と一致する）。
    pub fn cmp_syntactic(&self, other: &Bracket) -> Ordering {
        ORDER.with(|o| {
            let mut o = o.borrow_mut();
            o.trim();
            o.cmp(self, other)
        })
    }

    /// 順序数を使わずに求めた正規形（結果は `normal_form` と一致する）。
    pub fn normal_form_syntactic(&self) -> Bracket {
        ORDER.with(|o| {
            let mut o = o.borrow_mut();
            o.trim();
            o.normal_form(self)
        })
    }

    /// 順序数を使わない正規形の判定（結果は `is_normal` と一致する）。
    pub fn is_normal_syntactic(&self) -> bool {
        self.normal_form_syntactic() == *self
    }
}

/// 正規形の括弧語。worm・RC の「文字」（[`Letter`]）として使える。
///
/// 正規形どうしなら「同じ順序数を表す ⟺ 語として同じ」（Thm 32 の一意性）。
/// そこで等しさ（==）とハッシュは語のまま比べ、大小（Ord）だけを
/// 順序数を使わない比較 [`Bracket::cmp_syntactic`] で決める。
/// これで RC の判定器・導出器を、Veblen 表記を通さずに括弧語の上で動かせる。
///
/// 【Rust メモ】中身のフィールドを `pub` にしていないので、外からは
/// [`NfBracket::new`]（必ず正規形に直す）でしか作れない。こうして
/// 「中身はいつも正規形」という約束を型で守る。
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct NfBracket(Bracket);

impl NfBracket {
    /// 括弧語を正規形にして包む。
    pub fn new(a: &Bracket) -> NfBracket {
        NfBracket(a.normal_form_syntactic())
    }

    pub fn bracket(&self) -> &Bracket {
        &self.0
    }

    pub fn into_bracket(self) -> Bracket {
        self.0
    }
}

impl Ord for NfBracket {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp_syntactic(&other.0)
    }
}

impl PartialOrd for NfBracket {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for NfBracket {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl serde::Serialize for NfBracket {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.collect_str(self)
    }
}

impl Letter for NfBracket {
    fn zero() -> Self {
        NfBracket(Bracket::top())
    }

    fn parse_letter(s: &str) -> Option<Self> {
        s.parse::<Bracket>().ok().map(|b| NfBracket::new(&b))
    }

    /// 括弧語を文字に持つ worm は、それ自体が括弧語 (a_1)(a_2)… として表示する。
    fn fmt_worm(letters: &[Self]) -> String {
        Bracket(letters.iter().map(|x| x.0.clone()).collect()).to_string()
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
    fn syntactic_comparison() {
        use Ordering::*;
        let c = |x: &str, y: &str| b(x).cmp_syntactic(&b(y));
        assert_eq!(c("()", "(())"), Less); // 1 < ω
        assert_eq!(c("((()))", "(()())(())"), Greater); // ε_0 > ω^ω
        assert_eq!(c("(())()", "(())"), Equal); // 語は違うが同じ ω
        assert_eq!(c("((()))((()))", "((())(()))"), Less); // ε_1 < φ(2, 0)
        assert_eq!(b("(())()").normal_form_syntactic(), b("(())"));
        assert!(!b("(())()").is_normal_syntactic());
        assert!(b("((()))").is_normal_syntactic());
    }

    #[test]
    fn nf_bracket_letters() {
        // 括弧語を文字にした worm：((()))(()) は ⟨ε_0⟩… ではなく文字 (()) = ω と () = 1 の worm
        let x = NfBracket::new(&b("(())()")); // 正規形 (()) に直る
        assert_eq!(x.bracket(), &b("(())"));
        let y = NfBracket::new(&b("()"));
        assert!(y < x);
        assert_eq!(NfBracket::fmt_worm(&[x, y]), "((()))(())");
    }

    #[test]
    fn thm52_sequence() {
        let os: Vec<String> = (0..5).map(|m| Bracket::thm52(m).ordinal().to_string()).collect();
        assert_eq!(os, ["1", "2", "ε_0 + 1", "φ(ε_0, 0) + 1", "φ(φ(φ(ε_0, 0), 0), 0) + 1"]);
    }
}
