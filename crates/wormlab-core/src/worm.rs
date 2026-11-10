//! Beklemishev の worm。
//!
//! worm A = n_1 n_2 … n_k は閉じた式 ⟨n_1⟩⟨n_2⟩…⟨n_k⟩⊤ を表す
//! （左端が一番外側のモダリティ）。空の worm は ⊤。
//!
//! 順序：A <_n B :⟺ GLP ⊢ B → ⟨n⟩A。
//!
//! # 順序数への写像 o
//!
//! A を文字 0 で区切って A = A_1 0 A_2 0 … 0 A_k（各 A_i は 0 を含まない、
//! 空でもよい）と書き、A↓ を全文字から 1 を引いた worm とすると
//!
//! ```text
//!   1 + o(A) = ω^{o(A_k↓)} + … + ω^{o(A_2↓)} + ω^{o(A_1↓)}
//! ```
//!
//! （内側の成分から順に足す。順序数の加法は非可換なので順番が重要）。
//! Beklemishev の定理により、o は (worm/≡, <_0) から ε0 への順序同型を与える。
//! 特に A, B が GLP で同値 ⟺ o(A) = o(B)。
//!
//! 例：o(⊤)=0, o(0)=1, o(1)=ω, o(0 1)=ω+1, o(1 0)=ω（1 0 ≡ 1）,
//!     o(1 0 1)=ω·2, o(1 1)=ω², o(2)=ω^ω。

use crate::i18n::tr;
use crate::latex::ToLatex;
use crate::letter::Letter;
use crate::ordinal::Ordinal;
use std::cmp::Ordering;
use std::fmt;
use std::str::FromStr;

/// worm（文字の有限列）。文字の型 `L` の既定は自然数 `u32`。
///
/// 【Rust メモ】`struct Worm<L = u32>(Vec<L>)` は「タプル構造体」で、
/// 中身は `self.0` で取り出せる。`<L = u32>` は型引数の既定値で、
/// 単に `Worm` と書けば `Worm<u32>`、順序数を文字にするなら `Worm<Veblen>`。
#[derive(Clone, PartialEq, Eq, Hash, Debug, serde::Serialize)]
pub struct Worm<L = u32>(Vec<L>);

impl<L> Default for Worm<L> {
    fn default() -> Self {
        Worm(Vec::new())
    }
}

// ----------------------------------------------------------------------
// どんな文字型でも使える操作（大小比較しか使わない）
// ----------------------------------------------------------------------

impl<L: Letter> Worm<L> {
    /// 空の worm ⊤
    pub fn top() -> Self {
        Worm(Vec::new())
    }

    pub fn new(letters: Vec<L>) -> Self {
        Worm(letters)
    }

    pub fn letters(&self) -> &[L] {
        &self.0
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_top(&self) -> bool {
        self.0.is_empty()
    }

    /// `is_top` と同じ（Rust の慣習で `len` と対にする）。
    pub fn is_empty(&self) -> bool {
        self.is_top()
    }

    /// 最小の文字（⊤ なら `None`）。
    pub fn min_letter(&self) -> Option<&L> {
        self.0.iter().min()
    }

    /// 全文字が n 以上か（「n-worm」か）。⊤ は任意の n について真。
    pub fn is_n_worm(&self, n: L) -> bool {
        self.0.iter().all(|x| *x >= n)
    }

    /// h_n(A)：文字がすべて n 以上であるような A の最長の先頭部分。
    pub fn head(&self, n: L) -> Worm<L> {
        Worm(self.0.iter().take_while(|x| **x >= n).cloned().collect())
    }

    /// r_n(A)：A = h_n(A) r_n(A) となる残りの部分。
    pub fn rest(&self, n: L) -> Worm<L> {
        Worm(self.0.iter().skip_while(|x| **x >= n).cloned().collect())
    }

    /// 連結 A B（式としては A の一番内側の ⊤ を B で置き換えたもの）。
    pub fn concat(&self, other: &Worm<L>) -> Worm<L> {
        let mut v = self.0.clone();
        v.extend_from_slice(&other.0);
        Worm(v)
    }

    /// 各文字を f で写した worm（例：自然数の worm を順序数の worm にする）。
    pub fn map<M: Letter>(&self, f: impl Fn(&L) -> M) -> Worm<M> {
        Worm(self.0.iter().map(f).collect())
    }

    /// 式としての表示 ⟨1⟩⟨0⟩⟨2⟩⊤。
    pub fn to_formula(&self) -> String {
        let mut s: String = self.0.iter().map(|n| format!("⟨{n}⟩")).collect();
        s.push('⊤');
        s
    }

    /// 一般の worm に対する A <_n B（GLP ⊢ B → ⟨n⟩A）。
    ///
    /// n 未満の文字を含んでいてもよい。内部では RC の判定器を使う
    /// （worm は強正値式であり、RC は強正値式について GLP と一致する）。
    pub fn lt_n(&self, other: &Worm<L>, n: L) -> bool {
        crate::rc::worm_lt(n, self, other)
    }
}

// ----------------------------------------------------------------------
// 自然数の worm だけの操作（文字の足し算・引き算や ε0 未満の順序数を使うもの）
// ----------------------------------------------------------------------

impl Worm<u32> {
    /// 全文字に k を足す（A↑^k）。
    pub fn up(&self, k: u32) -> Worm {
        Worm(self.0.iter().map(|&x| x + k).collect())
    }

    /// 全文字から k を引く（A↓^k）。k 未満の文字があれば `None`。
    pub fn down(&self, k: u32) -> Option<Worm> {
        if self.is_n_worm(k) {
            Some(Worm(self.0.iter().map(|&x| x - k).collect()))
        } else {
            None
        }
    }

    // ------------------------------------------------------------------
    // 順序数
    // ------------------------------------------------------------------

    /// o(A) ∈ ε0。モジュール冒頭の公式をそのまま実装している。
    pub fn ordinal(&self) -> Ordinal {
        if self.is_top() {
            return Ordinal::zero(); // 再帰の底：o(⊤) = 0
        }
        one_plus_o(&self.0)
            .minus_one_plus()
            .expect("1 + o(A) は 1 以上")
    }

    /// α < ε0 を表す標準的な worm（o の逆写像）。
    ///
    /// 1 + α = ω^{β_1} + … + ω^{β_m}（β_1 ≥ … ≥ β_m）と展開し、
    /// A = (w(β_m))↑ 0 … 0 (w(β_1))↑ とする。
    pub fn from_ordinal(alpha: &Ordinal) -> Worm {
        if alpha.is_zero() {
            return Worm::top(); // 再帰の底
        }
        let betas = alpha.one_plus().exponents_with_multiplicity();
        let mut letters = Vec::new();
        for (i, beta) in betas.iter().rev().enumerate() {
            if i > 0 {
                letters.push(0);
            }
            letters.extend(Worm::from_ordinal(beta).up(1).0);
        }
        Worm(letters)
    }

    /// 同じ順序数を持つ標準形の worm。
    pub fn normal_form(&self) -> Worm {
        Worm::from_ordinal(&self.ordinal())
    }

    /// GLP ⊢ A ↔ B か。
    pub fn equiv(&self, other: &Worm) -> bool {
        self.ordinal() == other.ordinal()
    }

    /// <_0 に関する比較（≡ を同一視した全順序）。
    pub fn cmp0(&self, other: &Worm) -> Ordering {
        self.ordinal().cmp(&other.ordinal())
    }

    /// A <_0 B、つまり GLP ⊢ B → ⟨0⟩A か。
    pub fn lt0(&self, other: &Worm) -> bool {
        self.cmp0(other) == Ordering::Less
    }

    /// n-worm 同士の <_n 比較。どちらかが n-worm でなければ `None`。
    ///
    /// n-worm 全体の <_n は、全体を n だけ下げた 0-worm の <_0 と同型。
    /// n 未満の文字を含む worm には [`Worm::lt_n`] を使う。
    pub fn cmp_n(&self, other: &Worm, n: u32) -> Option<Ordering> {
        let a = self.down(n)?; // 【Rust メモ】`?` は None なら即 return None
        let b = other.down(n)?;
        Some(a.cmp0(&b))
    }

    // ------------------------------------------------------------------
    // Π 順序数（n-順序型）
    // ------------------------------------------------------------------

    /// Ω_n(A) = o(n↓h_n(A))：A の n-順序型。
    ///
    /// h_n(A) は文字が n 以上の最長の先頭部分。Ω_0 = o。A を理論とみたとき、
    /// 列 (Ω_0(A), Ω_1(A), …) が Π_{n+1} 順序数の列（Turing–Taylor 展開）に当たる。
    /// 出典：Fernández-Duque & Joosten, "Well-orders in the transfinite Japaridze
    /// algebra" I (Cor. 4.16), II (Lemma 6.2)。
    ///
    /// 性質：Ω_{n+1}(A) = ℓ(Ω_n(A))（II, Thm 6.5。ℓ は CNF の最後の指数）。
    pub fn pi_ordinal(&self, n: u32) -> Ordinal {
        self.head(n).down(n).expect("h_n(A) の文字は n 以上").ordinal()
    }

    /// (Ω_0(A), …, Ω_k(A))。k = 最大の文字 + 1 にすると、最後が 0 になるところまで出る。
    pub fn pi_ordinals(&self, k: u32) -> Vec<Ordinal> {
        (0..=k).map(|n| self.pi_ordinal(n)).collect()
    }

    // ------------------------------------------------------------------
    // Worm battle
    // ------------------------------------------------------------------

    /// Worm battle の 1 ステップ next(A, m)。A = ⊤ なら `None`（worm は死んだ）。
    ///
    /// Beklemishev の定義を、このライブラリの「左端が外側」という記法に
    /// 合わせて左右反転したもの：
    /// - A = 0 B なら next = B。
    /// - 先頭の文字 h > 0 なら、h 未満の文字が最初に現れる位置で
    ///   A = V U と分け（V の文字はすべて h 以上）、V の先頭を h−1 にした V'
    ///   を m+1 回並べて next = V' V' … V' U。
    ///
    /// どの m についても o(next(A, m)) < o(A) となる（テストで確認）。
    /// これが worm がいつか必ず死ぬこと（Worm principle）の理由であり、
    /// その主張自体は PA では証明できない。
    pub fn battle_step(&self, m: usize) -> Option<Worm> {
        let (&h, tail) = self.0.split_first()?;
        if h == 0 {
            return Some(Worm(tail.to_vec()));
        }
        let cut = self.0.iter().position(|&x| x < h).unwrap_or(self.0.len());
        let (v, u) = self.0.split_at(cut);
        let mut v_dec = v.to_vec();
        v_dec[0] = h - 1;
        let mut out = Vec::with_capacity(v_dec.len() * (m + 1) + u.len());
        for _ in 0..=m {
            out.extend_from_slice(&v_dec);
        }
        out.extend_from_slice(u);
        Some(Worm(out))
    }

    /// m = 1, 2, 3, … として battle_step を繰り返すイテレータ。
    /// 最初の要素は元の worm 自身。
    pub fn battle(&self) -> Battle {
        Battle { current: Some(self.clone()), step: 0 }
    }

    /// battle（m = 1, 2, 3, … で battle_step を繰り返す）が ⊤ に着くまでのステップ数。
    /// `max_steps` を超えたら `None`。
    ///
    /// [`Worm::battle`] を数えるのと同じ値だが、worm を逆順（外側が末尾）の Vec で持つ。
    /// 先頭の 0 を外すのは pop、展開は先頭の V の部分だけを書き換えるので、1 ステップの
    /// 手間は「変わった文字の数」で済む（battle_step は毎回 worm 全体をコピーする）。
    pub fn battle_length(&self, max_steps: u64) -> Option<u64> {
        self.battle_length_capped(max_steps, usize::MAX).ok()
    }

    /// [`Worm::battle_length`] に、worm の長さ（文字の数）の上限 `max_len` を付けたもの。
    /// ⊤ に着いたら `Ok(ステップ数)`、回数か長さの上限で止めたら `Err(そこまでのステップ数)`
    /// （1 ステップの手間が小さいので、回数より先にメモリが尽きないように）。
    pub fn battle_length_capped(&self, max_steps: u64, max_len: usize) -> Result<u64, u64> {
        let mut v: Vec<u32> = self.0.iter().rev().copied().collect();
        let mut steps = 0u64;
        while let Some(&h) = v.last() {
            if steps == max_steps || v.len() > max_len {
                return Err(steps);
            }
            steps += 1;
            if h == 0 {
                v.pop();
                continue;
            }
            // 末尾から見て、h 未満の文字が最初に現れる手前までが V（逆順）
            let cut = v.iter().rposition(|&x| x < h).map_or(0, |p| p + 1);
            let mut v_dec = v.split_off(cut);
            *v_dec.last_mut().expect("V は空でない") = h - 1;
            let m = usize::try_from(steps).map_err(|_| steps)?;
            let grow = v_dec.len().checked_mul(m + 1).filter(|g| v.len() + g <= max_len).ok_or(steps)?;
            v.reserve(grow);
            for _ in 0..=m {
                v.extend_from_slice(&v_dec);
            }
        }
        Ok(steps)
    }
}

/// `1 + o(A)` を計算する補助関数（再帰の本体）。
///
/// 【Rust メモ】`&[u32]` は「スライス」＝配列の一部を借りて見るための型。
/// コピーせずに部分列を渡せる。`split(|&x| x == 0)` は 0 で区切った
/// 部分スライスを順に返すイテレータ（空の成分も返す）。
fn one_plus_o(letters: &[u32]) -> Ordinal {
    let mut sum = Ordinal::zero();
    // 内側（右側）の成分から順に足す
    for component in letters.split(|&x| x == 0).collect::<Vec<_>>().into_iter().rev() {
        let lowered = Worm(component.iter().map(|&x| x - 1).collect());
        sum = sum + Ordinal::omega_pow(lowered.ordinal());
    }
    sum
}

/// Worm battle の進行を表すイテレータ。
///
/// 【Rust メモ】`Iterator` trait を実装すると `for` 文や `.take(n)`,
/// `.count()` などのアダプタがすべて使えるようになる。
pub struct Battle {
    current: Option<Worm>,
    step: usize,
}

impl Iterator for Battle {
    type Item = Worm;

    fn next(&mut self) -> Option<Worm> {
        let cur = self.current.take()?;
        self.step += 1;
        self.current = cur.battle_step(self.step);
        Some(cur)
    }
}

// ----------------------------------------------------------------------
// 文字列との相互変換
// ----------------------------------------------------------------------

impl<L: Letter> fmt::Display for Worm<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            return write!(f, "⊤");
        }
        write!(f, "{}", L::fmt_worm(&self.0))
    }
}

impl<L: Letter> ToLatex for Worm<L> {
    /// `\langle 2\rangle\langle 0\rangle\top`（括弧語の worm は括弧語そのもの）。空の worm は `\top`。
    fn to_latex(&self) -> String {
        if self.0.is_empty() { "\\top".to_string() } else { L::latex_worm(&self.0) }
    }
}

/// パースエラー。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseWormError(pub String);

impl fmt::Display for ParseWormError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", tr("worm として読めません", "cannot read as a worm"), self.0)
    }
}

impl std::error::Error for ParseWormError {}

/// 次のどれでも読める（⊤・T・空文字列は空の worm）：
/// - 括弧：`"<1><0><2>T"`, `"⟨ω + 1⟩⟨0⟩⟨ε_0⟩⊤"`
/// - カンマ区切り：`"1,0,2"`, `"ω+1, 0, ε_0"`（φ(2, 0) の中のカンマは区切りとみなさない）
/// - 空白区切り（自然数のみ）：`"1 0 2"`
///
/// 【Rust メモ】`FromStr` を実装すると `"1 0 2".parse::<Worm>()` と書ける。
/// 失敗しうる処理は `Result<成功時の型, エラー型>` を返すのが Rust の流儀。
impl<L: Letter> FromStr for Worm<L> {
    type Err = ParseWormError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let err = || ParseWormError(s.to_string());
        let is_top = |t: &str| matches!(t.trim(), "" | "⊤" | "T" | "top");
        let mut tokens: Vec<String> = Vec::new();
        if s.contains(['<', '⟨']) {
            // 括弧の中身を取り出す。括弧の外は空白か ⊤ だけ許す
            let mut cur: Option<String> = None;
            let mut outside = String::new();
            for c in s.chars() {
                match (c, &mut cur) {
                    ('<' | '⟨', None) => cur = Some(String::new()),
                    ('>' | '⟩', Some(t)) => {
                        tokens.push(std::mem::take(t));
                        cur = None;
                    }
                    (_, Some(t)) => t.push(c),
                    (_, None) => outside.push(c),
                }
            }
            if cur.is_some() || !outside.split_whitespace().all(is_top) {
                return Err(err());
            }
        } else if s.contains(',') {
            // 括弧の深さ 0 のカンマで区切る
            let (mut depth, mut cur) = (0i32, String::new());
            for c in s.chars() {
                match c {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    ',' if depth == 0 => {
                        tokens.push(std::mem::take(&mut cur));
                        continue;
                    }
                    _ => {}
                }
                cur.push(c);
            }
            tokens.push(cur);
        } else if L::SPACE_SEPARATED {
            tokens = s.split_whitespace().map(String::from).collect();
        } else if !is_top(s) {
            tokens.push(s.to_string());
        }
        let mut letters = Vec::new();
        for t in tokens.iter().filter(|t| !is_top(t)) {
            let t = t.trim().trim_end_matches(['⊤', 'T']);
            letters.push(L::parse_letter(t).ok_or_else(err)?);
        }
        Ok(Worm(letters))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn w(s: &str) -> Worm {
        s.parse().unwrap()
    }

    fn o(s: &str) -> String {
        w(s).ordinal().to_string()
    }

    #[test]
    fn known_ordinals() {
        assert_eq!(o("⊤"), "0");
        assert_eq!(o("0"), "1");
        assert_eq!(o("0 0 0"), "3");
        assert_eq!(o("1"), "ω");
        assert_eq!(o("1 0"), "ω"); // 1 0 ≡ 1
        assert_eq!(o("0 1"), "ω + 1");
        assert_eq!(o("1 0 1"), "ω·2");
        assert_eq!(o("1 1"), "ω^2");
        assert_eq!(o("2"), "ω^ω");
        assert_eq!(o("3"), "ω^ω^ω");
        assert_eq!(o("2 0 1 1 0 0"), "ω^ω"); // 内側の小さい成分は吸収される
        assert_eq!(o("0 0 1 1 0 2"), "ω^ω + ω^2 + 2");
    }

    #[test]
    fn parsing_variants() {
        let a = w("1 0 2");
        assert_eq!(w("1,0,2"), a);
        assert_eq!(w("<1><0><2>T"), a);
        assert_eq!(w("⟨1⟩⟨0⟩⟨2⟩⊤"), a);
        assert_eq!(w("⊤"), Worm::top());
        assert_eq!(w(""), Worm::top());
        assert!("1 x".parse::<Worm>().is_err());
        assert_eq!(a.to_formula(), "⟨1⟩⟨0⟩⟨2⟩⊤");
    }

    #[test]
    fn head_and_rest() {
        let a = w("2 3 1 4 0 2");
        assert_eq!(a.head(2), w("2 3"));
        assert_eq!(a.rest(2), w("1 4 0 2"));
        assert_eq!(a.head(1).concat(&a.rest(1)), a);
    }

    #[test]
    fn pi_ordinals() {
        let show = |s: &str| -> Vec<String> {
            w(s).pi_ordinals(4).iter().map(|x| x.to_string()).collect()
        };
        assert_eq!(show("3"), ["ω^ω^ω", "ω^ω", "ω", "1", "0"]);
        assert_eq!(show("2 0 1"), ["ω^ω", "ω", "1", "0", "0"]);
        assert_eq!(show("1 0 1"), ["ω·2", "1", "0", "0", "0"]);
        assert_eq!(show("0 2"), ["ω^ω + 1", "0", "0", "0", "0"]);
    }

    #[test]
    fn ordinal_letters() {
        use crate::veblen::Veblen;
        // 括弧・カンマのどちらでも読める（φ(2, 0) の中のカンマは区切りではない）
        let a: Worm<Veblen> = "⟨ω + 1⟩⟨0⟩⟨φ(2, 0)⟩⊤".parse().unwrap();
        let b: Worm<Veblen> = "w+1, 0, phi(2,0)".parse().unwrap();
        assert_eq!(a, b);
        assert_eq!(a.len(), 3);
        assert_eq!(a.to_string(), "⟨ω + 1⟩⟨0⟩⟨φ(2, 0)⟩");
        assert_eq!(a.to_string().parse::<Worm<Veblen>>().unwrap(), a);
        assert_eq!("<e_0>".parse::<Worm<Veblen>>().unwrap().len(), 1);
        assert_eq!("⊤".parse::<Worm<Veblen>>().unwrap(), Worm::top());
        assert!("<ω".parse::<Worm<Veblen>>().is_err());
        // 自然数の worm を順序数の worm に写す
        let c = w("1 0 2").map(|&n| Veblen::nat(n as u64));
        assert_eq!(c.to_string(), "⟨1⟩⟨0⟩⟨2⟩");
    }

    #[test]
    fn small_battle_dies() {
        // 1 1 (= ω^2) の battle は有限ステップで ⊤ に達する
        let steps = w("1 1").battle().count();
        assert!(steps > 3);
        assert_eq!(w("1 1").battle().last(), Some(Worm::top()));
    }

    #[test]
    fn battle_length_matches_iterator() {
        // 長さ ≤ 4・文字 ≤ 2 の worm をすべて試す（終わるものは数え切り、長いものは打ち切りの一致を見る）
        let mut worms = vec![vec![]];
        for _ in 0..4 {
            let mut next = vec![];
            for x in &worms {
                for c in 0..3u32 {
                    let mut y: Vec<u32> = x.clone();
                    y.push(c);
                    next.push(y);
                }
            }
            worms.extend(next.clone());
            worms.dedup();
        }
        worms.sort();
        worms.dedup();
        for letters in worms {
            let a = Worm::new(letters);
            for max in [0u64, 1, 5, 40] {
                let by_iter = a.battle().skip(1).take(max as usize + 1).count() as u64;
                let expect = if by_iter <= max { Some(by_iter) } else { None };
                assert_eq!(a.battle_length(max), expect, "{a} max {max}");
            }
        }
        assert_eq!(w("1 1").battle_length(u64::MAX), Some(w("1 1").battle().count() as u64 - 1));
        assert_eq!(Worm::top().battle_length(0), Some(0));
    }
}
