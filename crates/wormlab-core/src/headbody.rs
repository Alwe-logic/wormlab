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
//!
//! # 速い版：標準木のノード番号でメモする（[`CtCompare`]）
//! 再帰に現れる w は元の w の**標準木**（最初の最小文字で h | λ | b と割ることを
//! 繰り返した木、Cartesian tree）のノードに限られ、v も同様（algorithms.md §1 の
//! 補題1）。λ = min(wv) が w に無ければ w はそのまま、あれば w の子に進むからである。
//! そこで両方の標準木を前もって作り、状態を (w のノード番号, v のノード番号, ◁/⊴)
//! にすると、状態数は ≤ 2·(2|w|+1)·(2|v|+1)、1 状態 O(1) で、全体 O(|w|·|v|)。
//! スライスをキーにする [`HeadBody`] は、キーのハッシュに O(n) かかる。

use crate::letter::Letter;
use crate::worm::Worm;
use std::collections::HashMap;
use std::rc::Rc;

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

/// worm の標準木（Cartesian tree）。
///
/// - ノード番号 0 は空の worm ⊤。番号 k ≥ 1 のノードは、位置 k−1 の文字を
///   「最初の最小文字」に持つ区間（＝その位置を根とする部分木の範囲）。
/// - `h[k]`, `b[k]`：そのノードを h | λ | b と割ったときの h（左）と b（右）の番号。
///
/// 作り方は Cartesian tree の定番のスタック法：左から文字を読み、スタックの上に
/// **真に大きい**文字がある間は降ろす。等しい文字は降ろさないので、後から来た
/// 等しい文字は右（b の側）の子孫になり、「最初の最小文字が根」になる。
pub struct CanonTree {
    pub h: Vec<u32>,
    pub b: Vec<u32>,
    /// ノード k の区間 [start, end)
    pub start: Vec<u32>,
    pub end: Vec<u32>,
    pub root: u32,
    by_range: HashMap<(u32, u32), u32>,
}

impl CanonTree {
    pub fn new<L: Ord>(s: &[L]) -> Self {
        let n = s.len();
        let (mut h, mut b) = (vec![0u32; n + 1], vec![0u32; n + 1]);
        let mut stack: Vec<usize> = Vec::new();
        for i in 0..n {
            let mut last = None;
            while let Some(&t) = stack.last() {
                if s[t] > s[i] {
                    last = stack.pop();
                } else {
                    break;
                }
            }
            if let Some(l) = last {
                h[i + 1] = (l + 1) as u32;
            }
            if let Some(&t) = stack.last() {
                b[t + 1] = (i + 1) as u32;
            }
            stack.push(i);
        }
        let root = stack.first().map_or(0, |&r| (r + 1) as u32);
        // 区間を根から配る（再帰の代わりに明示的なスタック）
        let (mut start, mut end) = (vec![0u32; n + 1], vec![0u32; n + 1]);
        let mut by_range = HashMap::new();
        by_range.insert((0, 0), 0); // 空の区間は ⊤（位置は問わないので lookup 側でも扱う）
        let mut todo = vec![(root, 0u32, n as u32)];
        while let Some((k, l, r)) = todo.pop() {
            if k == 0 {
                continue;
            }
            start[k as usize] = l;
            end[k as usize] = r;
            by_range.insert((l, r), k);
            let p = k - 1; // 根の位置
            todo.push((h[k as usize], l, p));
            todo.push((b[k as usize], p + 1, r));
        }
        CanonTree { h, b, start, end, root, by_range }
    }

    /// 区間 [l, r) のノード番号（空なら 0）。標準木のノードでなければ `None`。
    pub fn node(&self, l: usize, r: usize) -> Option<u32> {
        if l == r { Some(0) } else { self.by_range.get(&(l as u32, r as u32)).copied() }
    }

    pub fn len(&self) -> usize {
        self.h.len() - 1
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// head/body 比較の速い版。w 側と v 側の元の worm を固定し、状態を標準木の
/// ノード番号で持つ。w 側のノードは常に w 側の木から、v 側は v 側の木から来る
/// （Thm 3.17 の再帰は左右を入れ替えない）。
///
/// 【Rust メモ】`Rc<[L]>` は参照カウントつきの共有スライス。複製しても中身は
/// コピーされないので、`&mut self` のメソッドを呼びながら中身を読むのに便利。
pub struct CtCompare<L> {
    w: Rc<[L]>,
    v: Rc<[L]>,
    tw: CanonTree,
    tv: CanonTree,
    memo: HashMap<(u32, u32, bool), bool>,
}

impl<L: Letter> CtCompare<L> {
    pub fn new(w: &[L], v: &[L]) -> Self {
        CtCompare {
            tw: CanonTree::new(w),
            tv: CanonTree::new(v),
            w: w.into(),
            v: v.into(),
            memo: HashMap::new(),
        }
    }

    /// w 側の区間 [l, r) のノード番号。
    pub fn node_w(&self, l: usize, r: usize) -> u32 {
        self.tw.node(l, r).expect("w 側の区間が標準木のノードでない（algorithms.md §1 の補題に反する）")
    }

    /// v 側の区間 [l, r) のノード番号。
    pub fn node_v(&self, l: usize, r: usize) -> u32 {
        self.tv.node(l, r).expect("v 側の区間が標準木のノードでない（algorithms.md §1 の補題に反する）")
    }

    pub fn root_w(&self) -> u32 {
        self.tw.root
    }

    pub fn root_v(&self) -> u32 {
        self.tv.root
    }

    /// 調べた状態の数（実験用）。
    pub fn states(&self) -> usize {
        self.memo.len()
    }

    /// w ◁ v（ノード番号で）
    pub fn lt(&mut self, w: u32, v: u32) -> bool {
        self.rec(w, v, true)
    }

    /// w ⊴ v（ノード番号で）
    pub fn le(&mut self, w: u32, v: u32) -> bool {
        self.rec(w, v, false)
    }

    /// [`HeadBody::rec`] と同じ再帰を、ノード番号の上でたどる。
    fn rec(&mut self, w: u32, v: u32, strict: bool) -> bool {
        if v == 0 {
            return !strict && w == 0;
        }
        if w == 0 {
            return true;
        }
        if let Some(&ans) = self.memo.get(&(w, v, strict)) {
            return ans;
        }
        // ノード k の最小文字は位置 k−1 の文字
        let (ws, vs) = (Rc::clone(&self.w), Rc::clone(&self.v));
        let (mw, mv) = (&ws[w as usize - 1], &vs[v as usize - 1]);
        let lambda = if mw <= mv { mw } else { mv };
        // λ があれば子へ、なければ (w, ⊤)
        let (hw, bw) = if mw == lambda { (self.tw.h[w as usize], self.tw.b[w as usize]) } else { (w, 0) };
        let (hv, bv) = if mv == lambda { (self.tv.h[v as usize], self.tv.b[v as usize]) } else { (v, 0) };
        let ans = self.rec(w, bv, false) || (self.rec(bw, v, true) && self.rec(hw, hv, strict));
        self.memo.insert((w, v, strict), ans);
        ans
    }
}

/// w <_μ v（v ⊢ ⟨μ⟩w）を head/body 再帰で判定する。
/// 前提 μ ≤ min(w v) を満たさなければ `None`。
pub fn lt<L: Letter>(mu: L, w: &Worm<L>, v: &Worm<L>) -> Option<bool> {
    if !w.is_n_worm(mu.clone()) || !v.is_n_worm(mu) {
        return None;
    }
    let mut c = CtCompare::new(w.letters(), v.letters());
    let (rw, rv) = (c.root_w(), c.root_v());
    Some(c.lt(rw, rv))
}

/// GLP ⊢ w ↔ v を head/body 再帰で判定する（μ = 0 として）。
pub fn equiv<L: Letter>(w: &Worm<L>, v: &Worm<L>) -> bool {
    let le = |x: &Worm<L>, y: &Worm<L>| {
        let mut c = CtCompare::new(x.letters(), y.letters());
        let (rx, ry) = (c.root_w(), c.root_v());
        c.le(rx, ry)
    };
    le(w, v) && le(v, w)
}

/// Beklemishev 標準形（BNF）か。
///
/// 出典：Fernández-Duque & Hermo Reyes, arXiv:2008.13445, Def. 10 / Thm 11
/// （どの worm にも、同値な BNF の worm がちょうど 1 つある）。
///
/// A = ⊤、または α = min A として最小文字 α のすべての出現で区切った
/// A = A_k α A_{k−1} α … α A_0 について、各 A_i が BNF で、
/// 左の成分ほど小さい（A_{i+1} ⊴ A_i）こと。
pub fn is_bnf<L: Letter>(w: &Worm<L>) -> bool {
    is_bnf_rec(&mut HeadBody::new(), w.letters())
}

fn is_bnf_rec<L: Letter>(hb: &mut HeadBody<L>, a: &[L]) -> bool {
    let Some(alpha) = a.iter().min().cloned() else {
        return true;
    };
    let comps: Vec<&[L]> = a.split(|x| *x == alpha).collect(); // 左から A_k, …, A_0
    comps.iter().all(|c| is_bnf_rec(hb, c)) && comps.windows(2).all(|p| hb.le(p[0], p[1]))
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

    #[test]
    fn canon_tree_shape() {
        // 2 0 1 0 3：根は最初の 0（位置 1）、h = "2"、b = "1 0 3"、その根は位置 3 の 0
        let t = CanonTree::new(&[2u32, 0, 1, 0, 3]);
        assert_eq!(t.root, 2);
        assert_eq!((t.start[2], t.end[2]), (0, 5));
        assert_eq!(t.h[2], 1);
        assert_eq!(t.b[2], 4);
        assert_eq!((t.start[4], t.end[4]), (2, 5));
        assert_eq!(t.node(2, 5), Some(4));
        assert_eq!(t.node(1, 3), None); // "0 1" はノードでない
        assert_eq!(t.node(3, 3), Some(0));
    }

    #[test]
    fn ct_compare_agrees_with_slices() {
        // 長さ 4 までの 0..2 の worm すべての組で、ノード番号版とスライス版が一致
        let mut all: Vec<Vec<u32>> = vec![vec![]];
        for len in 1..=4 {
            let mut next = Vec::new();
            for x in all.iter().filter(|x| x.len() == len - 1) {
                for c in 0..3 {
                    let mut y = x.clone();
                    y.push(c);
                    next.push(y);
                }
            }
            all.extend(next);
        }
        for a in &all {
            for b in &all {
                let mut c = CtCompare::new(a, b);
                let (ra, rb) = (c.root_w(), c.root_v());
                let mut hb = HeadBody::new();
                assert_eq!(c.lt(ra, rb), hb.lt(a, b), "{a:?} ◁ {b:?}");
                assert_eq!(c.le(ra, rb), hb.le(a, b), "{a:?} ⊴ {b:?}");
            }
        }
    }
}
