//! 繰り返しでまとめた書き方：長い列のうち、同じ部分が隣り合って続く所を (ab)^k と書く。
//!
//! battle では worm が「先頭の部分 V' を m+1 回並べる」形で伸びていくので、長くなった worm も
//! 繰り返しでまとめると、どこが何回複製されたのかが見える。例（worm 3 から 32 ステップ、3730 文字）：
//!
//! ```text
//!   (1^16 2 0)^32 (1^17 2 0)^29 (1^18 2 0)^27 … (1^6 2 1 2 0)^6 ((2 1)^2 2 0)^2 (2 1)^2 2
//! ```
//!
//! # まとめ方
//!
//! 左から順に、今の位置から始まる繰り返し u^k（k ≥ 2）のうち、覆う長さ k·|u| が最大のもの
//! （同じ長さなら u が短い方）を選んでまとめ、その後ろへ進む。繰り返しが始まらない位置は
//! 1 文字だけ書いて進む。まとめた u の中も同じ方法でまとめる（入れ子になる）。
//!
//! 各位置の最大の繰り返しは、周期 p ごとに「t[j] = t[j+p] が続く長さ」を後ろから数えて求める
//! （手間は列の長さ n について n²/2 回の比較）。[`MAX_TOKENS`] を超える列はまとめない。

use crate::bracket::Bracket;
use crate::worm::Worm;
use std::collections::HashMap;

/// まとめる列の長さの上限（手間が n² なので、これより長ければまとめずに返す）。
pub const MAX_TOKENS: usize = 6_000;

/// まとめた列の 1 つの部分。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Piece {
    /// 元の列の i 番目の文字 1 つ
    One(usize),
    /// 中身を k 回繰り返す（中身の位置は、1 回目の位置を指す）
    Rep(Vec<Piece>, usize),
}

/// 列を繰り返しでまとめる。
///
/// 【Rust メモ】`T: PartialEq` は「== で比べられる型なら何でも」という意味（ジェネリクス）
pub fn compress<T: PartialEq>(t: &[T]) -> Vec<Piece> {
    if t.len() > MAX_TOKENS {
        return (0..t.len()).map(Piece::One).collect();
    }
    compress_range(t, 0, t.len())
}

/// t[lo..hi] をまとめる（位置は t の中の位置で返す）。
fn compress_range<T: PartialEq>(t: &[T], lo: usize, hi: usize) -> Vec<Piece> {
    let best = best_repeats(&t[lo..hi]);
    let mut out = Vec::new();
    let mut i = 0;
    while i < hi - lo {
        let (p, k) = best[i];
        if k >= 2 {
            out.push(Piece::Rep(compress_range(t, lo + i, lo + i + p), k));
            i += p * k;
        } else {
            out.push(Piece::One(lo + i));
            i += 1;
        }
    }
    out
}

/// 各位置 i から始まる繰り返し u^k のうち、覆う長さ k·|u| が最大のもの (|u|, k)。
/// 繰り返しがなければ (0, 1)。
fn best_repeats<T: PartialEq>(t: &[T]) -> Vec<(usize, usize)> {
    let n = t.len();
    let mut best = vec![(0usize, 1usize); n];
    // eq[j] = t[j] = t[j+p]、t[j+1] = t[j+1+p]、… と等しいのが何個続くか
    let mut eq = vec![0usize; n + 1];
    for p in 1..=n / 2 {
        eq[n - p] = 0;
        for j in (0..n - p).rev() {
            eq[j] = if t[j] == t[j + p] { eq[j + 1] + 1 } else { 0 };
        }
        for (i, b) in best.iter_mut().enumerate().take(n - p) {
            if eq[i] >= p {
                let k = 1 + eq[i] / p;
                // 覆う長さが真に長いときだけ取り替える（p は小さい順なので、同じなら短い u が残る）
                if k * p > b.0 * b.1 {
                    *b = (p, k);
                }
            }
        }
    }
    best
}

/// まとめた列の長さ（書いた文字の数。繰り返しの中身は 1 回分）。
pub fn shown_len(pieces: &[Piece]) -> usize {
    pieces
        .iter()
        .map(|p| match p {
            Piece::One(_) => 1,
            Piece::Rep(inner, _) => shown_len(inner),
        })
        .sum()
}

/// まとめた形の書き方：文字の書き方 `one` と、繰り返しのくくり方を決めて文字列にする。
struct Style<'a> {
    one: &'a dyn Fn(usize) -> String,
    /// 文字どうしの区切り
    sep: &'a str,
    /// 2 文字以上の中身をくくる括弧
    open: &'a str,
    close: &'a str,
    /// 繰り返しの回数の書き方（`^3` や `^{3}`）
    power: &'a dyn Fn(usize) -> String,
}

fn render(pieces: &[Piece], st: &Style) -> String {
    let parts: Vec<String> = pieces
        .iter()
        .map(|p| match p {
            Piece::One(i) => (st.one)(*i),
            Piece::Rep(inner, k) => {
                let body = render(inner, st);
                if matches!(inner.as_slice(), [Piece::One(_)]) {
                    format!("{body}{}", (st.power)(*k))
                } else {
                    format!("{}{body}{}{}", st.open, st.close, (st.power)(*k))
                }
            }
        })
        .collect();
    parts.join(st.sep)
}

/// 繰り返しでまとめた書き方（ふつうの文字と LaTeX）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Compact {
    /// 例 `(2 0 1)^3 1^5`（括弧語なら `[(())()]^3(())`）
    pub text: String,
    /// 例 `\left(\langle 2\rangle\langle 0\rangle\right)^{3}\top`
    pub latex: String,
    /// まとめた形で書いた文字の数（元の文字の数より少なければ、まとめた効果がある）
    pub shown: usize,
}

/// 文字が自然数の worm をまとめる。例：`2 0 1 2 0 1 2 0 1 1 1` → `(2 0 1)^3 1^2`。
pub fn worm(w: &Worm) -> Compact {
    let ls = w.letters();
    if ls.is_empty() {
        return Compact { text: "⊤".into(), latex: "\\top".into(), shown: 0 };
    }
    let pieces = compress(ls);
    let text = render(
        &pieces,
        &Style { one: &|i| ls[i].to_string(), sep: " ", open: "(", close: ")", power: &|k| format!("^{k}") },
    );
    let latex = render(
        &pieces,
        &Style {
            one: &|i| format!("\\langle {}\\rangle", ls[i]),
            sep: "",
            open: "\\left(",
            close: "\\right)",
            power: &|k| format!("^{{{k}}}"),
        },
    );
    Compact { text, latex: format!("{latex}\\top"), shown: shown_len(&pieces) }
}

/// 括弧語をまとめる。文字（いちばん外側の括弧の対）の並びを繰り返しでまとめ、各文字の中身も
/// 同じようにまとめる。2 文字以上の繰り返しは [ ] でくくる（( ) は括弧語そのものの記号なので）。
/// 例：`(())(())(())()` → `(())^3()`、`(()()()())` → `(()^4)`。
pub fn bracket(b: &Bracket) -> Compact {
    if b.is_top() {
        return Compact { text: "⊤".into(), latex: "\\top".into(), shown: 0 };
    }
    let mut memo = HashMap::new();
    let (text, latex, shown) = bracket_body(b, &mut memo);
    Compact { text, latex, shown }
}

/// 括弧語の中身をまとめた (文字, LaTeX, 書いた文字の数)。同じ文字が何度も出てくるので覚えておく。
fn bracket_body(b: &Bracket, memo: &mut HashMap<Bracket, (String, String, usize)>) -> (String, String, usize) {
    if let Some(r) = memo.get(b) {
        return r.clone();
    }
    // 文字を番号に置き換えてから比べる（括弧語どうしを毎回比べると遅い）
    let mut ids: HashMap<&Bracket, usize> = HashMap::new();
    let mut letters: Vec<&Bracket> = Vec::new();
    let tokens: Vec<usize> = b
        .letters()
        .iter()
        .map(|l| {
            *ids.entry(l).or_insert_with(|| {
                letters.push(l);
                letters.len() - 1
            })
        })
        .collect();
    // 文字 (x) の書き方：中身 x もまとめる
    let shown_letters: Vec<(String, String, usize)> = letters
        .iter()
        .map(|l| {
            let (t, x, s) = bracket_body(l, memo);
            (format!("({t})"), format!("({x})"), s + 1)
        })
        .collect();
    let pieces = compress(&tokens);
    let text = render(
        &pieces,
        &Style { one: &|i| shown_letters[tokens[i]].0.clone(), sep: "", open: "[", close: "]", power: &|k| format!("^{k}") },
    );
    let latex = render(
        &pieces,
        &Style {
            one: &|i| shown_letters[tokens[i]].1.clone(),
            sep: "",
            open: "\\bigl[",
            close: "\\bigr]",
            power: &|k| format!("^{{{k}}}"),
        },
    );
    let shown = count(&pieces, &|i| shown_letters[tokens[i]].2);
    let r = (text, latex, shown);
    memo.insert(b.clone(), r.clone());
    r
}

/// まとめた形で書いた記号の数（文字 i は `size(i)` 個と数える）。
fn count(pieces: &[Piece], size: &dyn Fn(usize) -> usize) -> usize {
    pieces
        .iter()
        .map(|p| match p {
            Piece::One(i) => size(*i),
            Piece::Rep(inner, _) => count(inner, size),
        })
        .sum()
}

/// まとめた形を元の列に戻す（テスト用：元と一致するか確かめる）。
pub fn expand(pieces: &[Piece]) -> Vec<usize> {
    let mut out = Vec::new();
    for p in pieces {
        match p {
            Piece::One(i) => out.push(*i),
            Piece::Rep(inner, k) => {
                let once = expand(inner);
                for _ in 0..*k {
                    out.extend_from_slice(&once);
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn w(s: &str) -> Worm {
        s.parse().unwrap()
    }

    #[test]
    fn worms() {
        assert_eq!(worm(&w("2 0 1 2 0 1 2 0 1 1 1")).text, "(2 0 1)^3 1^2");
        assert_eq!(worm(&w("1 2 1 2 1 2 0 1 2 1 2 1 2 0")).text, "((1 2)^3 0)^2");
        assert_eq!(worm(&w("3 2 1")).text, "3 2 1");
        assert_eq!(worm(&w("1 1 1 1")).latex, "\\langle 1\\rangle^{4}\\top");
        assert_eq!(worm(&Worm::new(vec![])).text, "⊤");
    }

    #[test]
    fn brackets() {
        let b = |s: &str| -> Bracket { s.parse().unwrap() };
        assert_eq!(bracket(&b("(())(())(())()")).text, "(())^3()");
        assert_eq!(bracket(&b("(()()()())")).text, "(()^4)");
        assert_eq!(bracket(&b("(())()(())()")).text, "[(())()]^2");
        assert_eq!(bracket(&b("(())()(())()")).latex, "\\bigl[(())()\\bigr]^{2}");
    }

    #[test]
    fn expand_restores() {
        let t = [1, 2, 1, 2, 1, 2, 0, 1, 2, 1, 2, 1, 2, 0, 3, 3, 3];
        let p = compress(&t);
        let back: Vec<i32> = expand(&p).into_iter().map(|i| t[i]).collect();
        assert_eq!(back, t);
    }
}
