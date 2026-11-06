//! worm の順序の構文的な判定（head/body 分解による再帰）。
//!
//! 出典：D. Fernández-Duque, "Worms and spiders: Reflection calculi and
//! ordinal notation systems" (arXiv:1605.08867), Def. 3.11, Thm. 3.17。
//!
//! 記法（このライブラリの規約に合わせて）：
//! - w ◁_μ v  :⟺  v ⊢ ⟨μ⟩w     （= w <_μ v）
//! - w ⊴_μ v  :⟺  w ◁_μ v または w ≡ v
//! - λ = min(w v)（w と v に現れる最小の文字）
//! - h_λ(w)：文字がすべて λ より**真に大きい**ような w の最長の先頭部分
//! - b_λ(w)：w に λ があれば w = h_λ(w) λ b_λ(w) となる残り、なければ ⊤
//!
//! Thm 3.17（μ ≤ λ, w, v ≠ ⊤）：
//! 1. w ◁_μ v ⟺ (a) w ⊴_μ b_λ(v)，または (b) b_λ(w) ◁_μ v かつ h_λ(w) ◁_μ h_λ(v)
//! 2. w ⊴_μ v ⟺ (a) w ⊴_μ b_λ(v)，または (b) b_λ(w) ◁_μ v かつ h_λ(w) ⊴_μ h_λ(v)
//!
//! 再帰のたびに |w| + |v| が減るので停止する。μ は基底の場合にしか
//! 効かない（μ ≤ min なら答えは μ によらない）。つまり W_μ 上では
//! <_μ と <_0 が一致する、という事実がこの再帰から読み取れる。
//!
//! o(A)（順序数）と RC（モデル）に続く、3 本目の独立な判定法。
//! 順序数を使わないので、文字が順序数の worm にもそのまま一般化できる。

use crate::letter::Letter;
use crate::worm::Worm;
use std::collections::HashMap;

/// 比較のメモ（同じ部分問題を何度も解かないため）。文字は自然数でも順序数でもよい。
///
/// 【Rust メモ】`HashMap<K, V>` は辞書。キーにタプルを使える。
pub struct HeadBody<L = u32> {
    memo: HashMap<(Vec<L>, Vec<L>, bool), bool>,
}

impl<L> Default for HeadBody<L> {
    fn default() -> Self {
        HeadBody { memo: HashMap::new() }
    }
}

/// h_λ(w)（λ より大きい文字の最長の先頭部分）と b_λ(w)（最初の λ の後ろ）。
pub fn head_body<'a, L: Ord>(w: &'a [L], lambda: &L) -> (&'a [L], &'a [L]) {
    match w.iter().position(|x| x <= lambda) {
        None => (w, &[]),
        Some(i) if w[i] == *lambda => (&w[..i], &w[i + 1..]),
        // λ 未満の文字は来ない前提（λ は最小値）
        Some(i) => (&w[..i], &[]),
    }
}

impl<L: Letter> HeadBody<L> {
    pub fn new() -> Self {
        Self::default()
    }

    /// w ◁ v（μ ≤ min(w v) の範囲では μ によらない）
    pub fn lt(&mut self, w: &[L], v: &[L]) -> bool {
        self.rec(w, v, true)
    }

    /// w ⊴ v
    pub fn le(&mut self, w: &[L], v: &[L]) -> bool {
        self.rec(w, v, false)
    }

    fn rec(&mut self, w: &[L], v: &[L], strict: bool) -> bool {
        // 基底：⊤ が絡む場合
        if v.is_empty() {
            return !strict && w.is_empty(); // w ◁ ⊤ は偽、w ⊴ ⊤ ⟺ w = ⊤
        }
        if w.is_empty() {
            return true; // ⊤ ◁ v（v ≠ ⊤）
        }
        let key = (w.to_vec(), v.to_vec(), strict);
        if let Some(&ans) = self.memo.get(&key) {
            return ans;
        }
        let lambda = w.iter().chain(v).min().unwrap().clone();
        let (hw, bw) = head_body(w, &lambda);
        let (hv, bv) = head_body(v, &lambda);
        // (a) w ⊴ b_λ(v)
        let ans = self.rec(w, bv, false)
            // (b) b_λ(w) ◁ v かつ h_λ(w) ◁ h_λ(v)（2 では ⊴）
            || (self.rec(bw, v, true) && self.rec(hw, hv, strict));
        self.memo.insert(key, ans);
        ans
    }
}

/// w <_μ v（v ⊢ ⟨μ⟩w）を head/body 再帰で判定する。
/// 前提 μ ≤ min(w v) を満たさなければ `None`。
pub fn lt<L: Letter>(mu: L, w: &Worm<L>, v: &Worm<L>) -> Option<bool> {
    if !w.is_n_worm(mu.clone()) || !v.is_n_worm(mu) {
        return None;
    }
    Some(HeadBody::new().lt(w.letters(), v.letters()))
}

/// GLP ⊢ w ↔ v を head/body 再帰で判定する（μ = 0 として）。
pub fn equiv<L: Letter>(w: &Worm<L>, v: &Worm<L>) -> bool {
    let mut hb = HeadBody::new();
    hb.le(w.letters(), v.letters()) && hb.le(v.letters(), w.letters())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn w(s: &str) -> Worm {
        s.parse().unwrap()
    }

    #[test]
    fn decomposition() {
        assert_eq!(head_body(&[2u32, 3, 1, 4, 1, 2], &1), (&[2u32, 3][..], &[4u32, 1, 2][..]));
        assert_eq!(head_body(&[2u32, 3], &1), (&[2u32, 3][..], &[][..]));
    }

    #[test]
    fn small_cases() {
        assert_eq!(lt(0, &w("0"), &w("1")), Some(true)); // 1 < ω
        assert_eq!(lt(0, &w("1"), &w("0")), Some(false));
        assert_eq!(lt(0, &w("0 1"), &w("1 0 1")), Some(true)); // ω+1 < ω·2
        assert_eq!(lt(0, &w("1 1"), &w("2")), Some(true)); // ω² < ω^ω
        assert!(equiv(&w("1 0"), &w("1")));
        assert!(!equiv(&w("0 1"), &w("1")));
        assert_eq!(lt(1, &w("0"), &w("1")), None); // 前提を満たさない
    }
}
