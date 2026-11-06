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

use crate::ordinal::Ordinal;
use std::cmp::Ordering;
use std::fmt;
use std::str::FromStr;

/// worm（自然数の有限列）。
///
/// 【Rust メモ】`struct Worm(Vec<u32>)` は「タプル構造体」。中身は
/// `self.0` で取り出せる。ただの `Vec<u32>` に名前を付けて別の型に
/// しておくと、うっかり普通のリストと混同するのを型検査が防いでくれる。
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default, serde::Serialize)]
pub struct Worm(Vec<u32>);

impl Worm {
    /// 空の worm ⊤
    pub fn top() -> Self {
        Worm(Vec::new())
    }

    pub fn new(letters: Vec<u32>) -> Self {
        Worm(letters)
    }

    pub fn letters(&self) -> &[u32] {
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
    pub fn min_letter(&self) -> Option<u32> {
        self.0.iter().copied().min()
    }

    /// 全文字が n 以上か（「n-worm」か）。⊤ は任意の n について真。
    pub fn is_n_worm(&self, n: u32) -> bool {
        self.0.iter().all(|&x| x >= n)
    }

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

    /// h_n(A)：文字がすべて n 以上であるような A の最長の先頭部分。
    pub fn head(&self, n: u32) -> Worm {
        Worm(self.0.iter().copied().take_while(|&x| x >= n).collect())
    }

    /// r_n(A)：A = h_n(A) r_n(A) となる残りの部分。
    pub fn rest(&self, n: u32) -> Worm {
        Worm(self.0.iter().copied().skip_while(|&x| x >= n).collect())
    }

    /// 連結 A B（式としては A の一番内側の ⊤ を B で置き換えたもの）。
    pub fn concat(&self, other: &Worm) -> Worm {
        let mut v = self.0.clone();
        v.extend_from_slice(&other.0);
        Worm(v)
    }

    /// 式としての表示 ⟨1⟩⟨0⟩⟨2⟩⊤。
    pub fn to_formula(&self) -> String {
        let mut s: String = self.0.iter().map(|n| format!("⟨{n}⟩")).collect();
        s.push('⊤');
        s
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

    /// 一般の worm に対する A <_n B（GLP ⊢ B → ⟨n⟩A）。
    ///
    /// n 未満の文字を含んでいてもよい。内部では RC の判定器を使う
    /// （worm は強正値式であり、RC は強正値式について GLP と一致する）。
    pub fn lt_n(&self, other: &Worm, n: u32) -> bool {
        crate::rc::worm_lt(n, self, other)
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

impl fmt::Display for Worm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            return write!(f, "⊤");
        }
        let s: Vec<String> = self.0.iter().map(|n| n.to_string()).collect();
        write!(f, "{}", s.join(" "))
    }
}

/// パースエラー。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseWormError(pub String);

impl fmt::Display for ParseWormError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "worm として読めません: {}", self.0)
    }
}

impl std::error::Error for ParseWormError {}

/// `"1 0 2"`, `"1,0,2"`, `"<1><0><2>T"`, `"⟨1⟩⟨0⟩⟨2⟩⊤"`, `"⊤"`, `""` などを受け付ける。
///
/// 【Rust メモ】`FromStr` を実装すると `"1 0 2".parse::<Worm>()` と書ける。
/// 失敗しうる処理は `Result<成功時の型, エラー型>` を返すのが Rust の流儀。
impl FromStr for Worm {
    type Err = ParseWormError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let cleaned: String = s
            .chars()
            .map(|c| match c {
                '<' | '>' | '⟨' | '⟩' | ',' => ' ',
                _ => c,
            })
            .collect();
        let mut letters = Vec::new();
        for tok in cleaned.split_whitespace() {
            match tok {
                "⊤" | "T" | "top" => continue,
                _ => {
                    let tok = tok.trim_end_matches(['⊤', 'T']);
                    let n = tok
                        .parse::<u32>()
                        .map_err(|_| ParseWormError(s.to_string()))?;
                    letters.push(n);
                }
            }
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
    fn small_battle_dies() {
        // 1 1 (= ω^2) の battle は有限ステップで ⊤ に達する
        let steps = w("1 1").battle().count();
        assert!(steps > 3);
        assert_eq!(w("1 1").battle().last(), Some(Worm::top()));
    }
}
