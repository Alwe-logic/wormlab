//! BC の「自律的な」意味論：副条件の大小を、意味論そのものの妥当性で決める不動点。
//!
//! 研究メモ bc-semantics.md §7-3 と bc-semantics-note.md の定理 3・4 の計算機での裏づけ。
//!
//! # 定義
//! 括弧語 a, b についてのシーケント a ⊢ b と a ⊢ ()b を**比較のシーケント**と呼ぶ。
//! 比較のシーケントの集合 T について、フレーム (W, (R_c)_{c ∈ B}) が **T-フレーム**とは
//! ```text
//!   (a ⊢ b) ∈ T または (a ⊢ ()b) ∈ T  ⇒  R_a ⊆ R_b かつ R_a ∘ R_b ⊆ R_b   （規則 3。a = b で推移性）
//!   (a ⊢ ()b) ∈ T                      ⇒  x R_a y, x R_b z ⇒ y R_b z       （規則 4：J）
//! ```
//! を満たすこと。Ψ(T) = 「T-フレームすべてで妥当な比較のシーケント」の集合とおく。
//! T が大きいほどフレームが減るので Ψ は単調。
//!
//! - 定理 3：Ψ の最小不動点 ⋃_n Ψ^n(∅) は、BC で導出できる比較のシーケントの全体。
//!   入れ子の深さ d ≥ 1 の語どうしの比較は Ψ^d(∅) で出そろう。
//! - 定理 4：不動点はただ 1 つ（最大不動点も同じ）。T ⊆ Ψ(T) なら T ⊆ T_BC を、左辺の入れ子の深さの
//!   帰納法で示す（深さは ◁ について単調なので、◁ の整礎性は要らない）。下向きの反復は n + 1 段で着く。
//!
//! 定義に出てくるのは括弧語と妥当性だけで、順序数も、前もって与える順序 ◁ も、RC も使わない。
//!
//! あわせて、直接の証明の 2 つの部品を有限の U の上で検査する関数を置く。
//! - [`check_canonical`]：BC の正準モデル（条件 R1′・R2′・R3。⊴・◁ は BC 自身の導出可能性）が
//!   BC-フレームになり、真理補題・完全性・保存性（副条件をシーケントの様相どうしの比較に限ってよい）
//!   を満たすこと。線形性も RC も使わない完全性証明（論文 §3）の裏づけ。
//! - [`check_mu_frame`]：μ_n ⊢ ()μ_n を偽にする 2 点の BC-フレーム（論文 §4、深さの単調性に使う非反射性）。
//!
//! # 計算
//! 条件はすべて Horn なので、a ⊢ γ が T-フレームすべてで妥当かは、a の木モデル
//! （根 0 から 0 R_{a_1} 1 R_{a_2} … k）を T の条件で閉じた最小のモデルの根で γ が真かでわかる
//! （強正値の式は、関係を保つ写像で真が保たれる）。
//!
//! 計算は、文字について閉じた有限の語の集合 U（[`Universe`]）の中で行い、T も U の語どうしの
//! 比較に限る。U が文字について閉じていれば、深さ ≤ d の比較は U の中だけで正しく出る
//! （必要な条件が U の語どうしの比較だけだから）。
//!
//! 閉包では、関係を「辺 (x, y) ごとに、その辺をもつ添字 c の集合」（ビット列）で持つ。
//! T の条件は添字の上の関係なので、辺ごとに「上の添字から届く添字」をまとめて計算できる。

use crate::bracket::Bracket;
use std::collections::HashMap;

/// 固定長のビット列（添字の集合）。
#[derive(Clone, PartialEq, Eq, Debug)]
struct Bits(Vec<u64>);

impl Bits {
    fn new(n: usize) -> Bits {
        Bits(vec![0; n.div_ceil(64)])
    }

    fn full(n: usize) -> Bits {
        let mut b = Bits(vec![!0; n.div_ceil(64)]);
        if n & 63 != 0 {
            let last = b.0.len() - 1;
            b.0[last] = (1u64 << (n % 64)) - 1;
        }
        b
    }

    fn get(&self, i: usize) -> bool {
        self.0[i / 64] >> (i % 64) & 1 == 1
    }

    fn set(&mut self, i: usize) {
        self.0[i / 64] |= 1 << (i % 64);
    }

    fn is_empty(&self) -> bool {
        self.0.iter().all(|&w| w == 0)
    }

    fn count(&self) -> usize {
        self.0.iter().map(|w| w.count_ones() as usize).sum()
    }

    fn is_subset(&self, o: &Bits) -> bool {
        self.0.iter().zip(&o.0).all(|(a, b)| a & !b == 0)
    }

    /// self |= o。変わったら true。
    fn or_assign(&mut self, o: &Bits) -> bool {
        let mut ch = false;
        for (a, b) in self.0.iter_mut().zip(&o.0) {
            let n = *a | b;
            ch |= n != *a;
            *a = n;
        }
        ch
    }

    /// self |= p & q。変わったら true。
    fn or_and_assign(&mut self, p: &Bits, q: &Bits) -> bool {
        let mut ch = false;
        for ((a, b), c) in self.0.iter_mut().zip(&p.0).zip(&q.0) {
            let n = *a | (b & c);
            ch |= n != *a;
            *a = n;
        }
        ch
    }

    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.0.iter().enumerate().flat_map(|(i, &w)| {
            let mut w = w;
            std::iter::from_fn(move || {
                if w == 0 {
                    return None;
                }
                let t = w.trailing_zeros() as usize;
                w &= w - 1;
                Some(i * 64 + t)
            })
        })
    }
}

/// 文字について閉じた、有限の括弧語の集合（⊤ を含む）。語には 0, 1, … の番号を振る。
pub struct Universe {
    words: Vec<Bracket>,
    letters: Vec<Vec<u32>>,
    ids: HashMap<Bracket, u32>,
    top: u32,
}

impl Universe {
    /// 括弧の対がちょうど k 個の語すべて（カタラン数個）。
    pub fn exact_pairs(k: usize) -> Vec<Bracket> {
        if k == 0 {
            return vec![Bracket::top()];
        }
        let mut out = Vec::new();
        for j in 0..k {
            for first in Self::exact_pairs(j) {
                for rest in Self::exact_pairs(k - 1 - j) {
                    out.push(rest.prepend(first.clone()));
                }
            }
        }
        out
    }

    /// 括弧の対が n 個以下の語すべて（文字について自動的に閉じている）。
    pub fn upto_pairs(n: usize) -> Universe {
        let ws: Vec<Bracket> = (0..=n).flat_map(Self::exact_pairs).collect();
        Universe::closure(&ws)
    }

    /// 与えた語と、その文字・文字の文字…と ⊤ からなる集合。
    pub fn closure(words: &[Bracket]) -> Universe {
        let mut u = Universe { words: Vec::new(), letters: Vec::new(), ids: HashMap::new(), top: 0 };
        u.top = u.add(&Bracket::top());
        for w in words {
            u.add(w);
        }
        u
    }

    fn add(&mut self, w: &Bracket) -> u32 {
        if let Some(&i) = self.ids.get(w) {
            return i;
        }
        let ls: Vec<u32> = w.letters().iter().map(|l| self.add(l)).collect();
        let i = self.words.len() as u32;
        self.words.push(w.clone());
        self.letters.push(ls);
        self.ids.insert(w.clone(), i);
        i
    }

    pub fn len(&self) -> usize {
        self.words.len()
    }

    pub fn is_empty(&self) -> bool {
        self.words.is_empty()
    }

    pub fn words(&self) -> &[Bracket] {
        &self.words
    }

    pub fn word(&self, i: usize) -> &Bracket {
        &self.words[i]
    }

    pub fn id(&self, w: &Bracket) -> Option<usize> {
        self.ids.get(w).map(|&i| i as usize)
    }

    /// ⊤ の番号。
    pub fn top(&self) -> usize {
        self.top as usize
    }
}

/// 比較のシーケントの集合 T（U の語どうし）。
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Theory {
    /// le[a] ∋ b ⟺ (a ⊢ b) ∈ T
    le: Vec<Bits>,
    /// lt[a] ∋ b ⟺ (a ⊢ ()b) ∈ T、つまり T の中で b ◁ a
    lt: Vec<Bits>,
}

impl Theory {
    pub fn empty(n: usize) -> Theory {
        Theory { le: vec![Bits::new(n); n], lt: vec![Bits::new(n); n] }
    }

    /// すべての比較のシーケント。
    pub fn full(n: usize) -> Theory {
        Theory { le: vec![Bits::full(n); n], lt: vec![Bits::full(n); n] }
    }

    /// (a ⊢ b) ∈ T か。
    pub fn entails(&self, a: usize, b: usize) -> bool {
        self.le[a].get(b)
    }

    /// (a ⊢ ()b) ∈ T か（T の中で b ◁ a か）。
    pub fn below(&self, b: usize, a: usize) -> bool {
        self.lt[a].get(b)
    }

    pub fn insert_entails(&mut self, a: usize, b: usize) {
        self.le[a].set(b);
    }

    pub fn insert_below(&mut self, b: usize, a: usize) {
        self.lt[a].set(b);
    }

    /// 入っているシーケントの数。
    pub fn len(&self) -> usize {
        self.le.iter().chain(&self.lt).map(Bits::count).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn is_subset(&self, o: &Theory) -> bool {
        self.le.iter().zip(&o.le).all(|(a, b)| a.is_subset(b))
            && self.lt.iter().zip(&o.lt).all(|(a, b)| a.is_subset(b))
    }

    /// ≡（互いに a ⊢ b, b ⊢ a）の類に分け、◁ の小さいほうから並べる。
    /// T が線形な前順序を定めていることを前提にする（[`Theory::order_violations`] で確かめる）。
    pub fn classes(&self) -> Vec<Vec<usize>> {
        let n = self.le.len();
        // 自分より ◁ で小さい語の数で並べる
        let mut idx: Vec<usize> = (0..n).collect();
        idx.sort_by_key(|&a| self.lt[a].count());
        let mut out: Vec<Vec<usize>> = Vec::new();
        for a in idx {
            match out.last_mut() {
                Some(cl) if self.le[a].get(cl[0]) && self.le[cl[0]].get(a) => cl.push(a),
                _ => out.push(vec![a]),
            }
        }
        out
    }

    /// ◁ が強い弱順序（非反射・推移・三分で、どちらでもない ⟺ 互いに ⊢）になっているかの違反の数。
    /// 返り値は（非反射、推移、三分）の違反の数。
    pub fn order_violations(&self) -> (usize, usize, usize) {
        let n = self.le.len();
        let irr = (0..n).filter(|&a| self.lt[a].get(a)).count();
        let mut trans = 0;
        for a in 0..n {
            for b in self.lt[a].iter() {
                // b ◁ a、c ◁ b ⇒ c ◁ a
                if !self.lt[b].is_subset(&self.lt[a]) {
                    trans += 1;
                }
            }
        }
        let mut tri = 0;
        for a in 0..n {
            for b in 0..n {
                let comparable = self.lt[a].get(b) || self.lt[b].get(a);
                let equiv = self.le[a].get(b) && self.le[b].get(a);
                if comparable == equiv {
                    tri += 1;
                }
            }
        }
        (irr, trans, tri)
    }
}

/// a の木モデルを T の条件で閉じた最小のモデル。
/// 点は 0..=k（k は a の文字数）。`edge[x * m + y]` は、辺 x → y をもつ添字の集合。
struct ClosureModel {
    m: usize,
    edge: Vec<Bits>,
}

impl ClosureModel {
    /// `up_any[c]` = {d : (c ⊢ d) ∈ T か (c ⊢ ()d) ∈ T}、`up_lt[c]` = {d : (c ⊢ ()d) ∈ T}。
    fn build(u: &Universe, a: usize, up_any: &[Bits], up_lt: &[Bits]) -> ClosureModel {
        Self::build_conj(u, &[a], up_any, up_lt)
    }

    /// 連言 a_1 ∧ … ∧ a_r（どれも worm）の木モデル：根 0 から各 a_i の鎖を伸ばしたもの。
    fn build_conj(u: &Universe, worms: &[usize], up_any: &[Bits], up_lt: &[Bits]) -> ClosureModel {
        let n = u.len();
        let m = 1 + worms.iter().map(|&a| u.letters[a].len()).sum::<usize>();
        assert!(m <= 64, "文字が多すぎます");
        let mut edge = vec![Bits::new(n); m * m];
        let mut next = 1;
        for &a in worms {
            let mut prev = 0;
            for &c in &u.letters[a] {
                edge[prev * m + next].set(c as usize);
                prev = next;
                next += 1;
            }
        }
        let mut ua = vec![Bits::new(n); m * m];
        let mut ul = vec![Bits::new(n); m * m];
        loop {
            // 辺ごとに、上の添字から T の条件で届く添字をまとめる
            for e in 0..m * m {
                ua[e] = Bits::new(n);
                ul[e] = Bits::new(n);
                for c in edge[e].iter() {
                    ua[e].or_assign(&up_any[c]);
                    ul[e].or_assign(&up_lt[c]);
                }
            }
            let mut changed = false;
            for x in 0..m {
                for y in 0..m {
                    let xy = x * m + y;
                    if ua[xy].is_empty() {
                        continue;
                    }
                    // 包含：x R_c y ⇒ x R_d y
                    changed |= edge[xy].or_assign(&ua[xy]);
                    if x == y {
                        // x = y のとき合成・J は新しい辺を生まない
                        continue;
                    }
                    for z in 0..m {
                        let (yz, xz) = (y * m + z, x * m + z);
                        // 合成：x R_c y, y R_d z ⇒ x R_d z
                        changed |= or_and_at(&mut edge, xz, &ua[xy], yz);
                        // J：x R_c y, x R_d z（(c ⊢ ()d) ∈ T）⇒ y R_d z
                        if !ul[xy].is_empty() {
                            changed |= or_and_at(&mut edge, yz, &ul[xy], xz);
                        }
                    }
                }
            }
            if !changed {
                return ClosureModel { m, edge };
            }
        }
    }

    /// 添字 c の辺で、集合 s（点のビット）のどれかに行ける点の集合。
    fn pre(&self, c: usize, s: u64) -> u64 {
        let mut out = 0;
        for x in 0..self.m {
            for y in 0..self.m {
                if s >> y & 1 == 1 && self.edge[x * self.m + y].get(c) {
                    out |= 1 << x;
                    break;
                }
            }
        }
        out
    }

    /// worm b が真になる点の集合。
    fn sat(&self, u: &Universe, b: usize) -> u64 {
        let mut s: u64 = if self.m == 64 { !0 } else { (1u64 << self.m) - 1 };
        for &c in u.letters[b].iter().rev() {
            s = self.pre(c as usize, s);
            if s == 0 {
                break;
            }
        }
        s
    }
}

/// edge[dst] |= p & edge[src]（dst ≠ src）。変わったら true。
fn or_and_at(edge: &mut [Bits], dst: usize, p: &Bits, src: usize) -> bool {
    debug_assert_ne!(dst, src);
    let (d, s) = if dst < src {
        let (l, r) = edge.split_at_mut(src);
        (&mut l[dst], &r[0])
    } else {
        let (l, r) = edge.split_at_mut(dst);
        (&mut r[0], &l[src])
    };
    d.or_and_assign(p, s)
}

/// Ψ(T)：T-フレームすべてで妥当な比較のシーケント（U の語どうし）。
pub fn psi(u: &Universe, t: &Theory) -> Theory {
    let n = u.len();
    let up_any: Vec<Bits> = (0..n)
        .map(|c| {
            let mut b = t.le[c].clone();
            b.or_assign(&t.lt[c]);
            b
        })
        .collect();
    let mut out = Theory::empty(n);
    let top = u.top();
    for a in 0..n {
        let model = ClosureModel::build(u, a, &up_any, &t.lt);
        for b in 0..n {
            let s = model.sat(u, b);
            if s & 1 == 1 {
                out.le[a].set(b);
            }
            if s != 0 && model.pre(top, s) & 1 == 1 {
                out.lt[a].set(b);
            }
        }
    }
    out
}

/// 最小不動点の計算結果。
pub struct LeastFixedPoint {
    pub theory: Theory,
    /// 各段 Ψ^1(∅), Ψ^2(∅), … の大きさ（最後の 2 つが等しい）
    pub sizes: Vec<usize>,
    /// (a ⊢ ()b) が初めて入った段（入らなければ 0）。`first_lt[a][b]`
    pub first_lt: Vec<Vec<u16>>,
    /// (a ⊢ b) が初めて入った段（入らなければ 0）。`first_le[a][b]`
    pub first_le: Vec<Vec<u16>>,
}

/// ∅ から Ψ を不動点まで繰り返す。
pub fn least_fixed_point(u: &Universe) -> LeastFixedPoint {
    let n = u.len();
    let mut t = Theory::empty(n);
    let mut sizes = Vec::new();
    let mut first_lt = vec![vec![0u16; n]; n];
    let mut first_le = vec![vec![0u16; n]; n];
    let mut stage = 0u16;
    loop {
        stage += 1;
        let t2 = psi(u, &t);
        assert!(t.is_subset(&t2), "Ψ の反復が増加列になっていません");
        for a in 0..n {
            for b in 0..n {
                if t2.below(b, a) && first_lt[a][b] == 0 {
                    first_lt[a][b] = stage;
                }
                if t2.entails(a, b) && first_le[a][b] == 0 {
                    first_le[a][b] = stage;
                }
            }
        }
        sizes.push(t2.len());
        if t2 == t {
            return LeastFixedPoint { theory: t, sizes, first_lt, first_le };
        }
        t = t2;
    }
}

/// 全体の集合から下向きに Ψ を繰り返して最大不動点を求める。各段の大きさも返す。
pub fn greatest_fixed_point(u: &Universe) -> (Theory, Vec<usize>) {
    let n = u.len();
    let mut t = Theory::full(n);
    let mut sizes = Vec::new();
    loop {
        let t2 = psi(u, &t);
        assert!(t2.is_subset(&t), "下向きの反復が減少列になっていません");
        sizes.push(t2.len());
        if t2 == t {
            return (t, sizes);
        }
        t = t2;
    }
}

// ---------------------------------------------------------------------------
// 直接の完全性証明（論文 §3）と、深さの単調性の非反射性（論文 §4）の検査
// ---------------------------------------------------------------------------

/// T についての b ⊴ a：(a ⊢ b) ∈ T か (a ⊢ ()b) ∈ T。
pub fn le(t: &Theory, b: usize, a: usize) -> bool {
    t.entails(a, b) || t.below(b, a)
}

impl Theory {
    /// 左辺も右辺も `s` に入る比較だけを残した理論 T ∩ Cmp(S)。
    pub fn restrict(&self, s: &[usize]) -> Theory {
        let n = self.le.len();
        let mut mask = Bits::new(n);
        for &x in s {
            mask.set(x);
        }
        let mut out = Theory::empty(n);
        for &a in s {
            out.le[a] = Bits(self.le[a].0.iter().zip(&mask.0).map(|(p, q)| p & q).collect());
            out.lt[a] = Bits(self.lt[a].0.iter().zip(&mask.0).map(|(p, q)| p & q).collect());
        }
        out
    }
}

/// T の条件を添字の上の関係にしたもの（閉包モデルを何度も作るときに使い回す）。
pub struct Oracle {
    up_any: Vec<Bits>,
    up_lt: Vec<Bits>,
}

impl Oracle {
    pub fn new(t: &Theory) -> Oracle {
        let n = t.le.len();
        let up_any = (0..n)
            .map(|c| {
                let mut b = t.le[c].clone();
                b.or_assign(&t.lt[c]);
                b
            })
            .collect();
        Oracle { up_any, up_lt: t.lt.clone() }
    }

    /// 連言 ⋀lhs ⊢ rhs（どれも U の worm）が T-フレームすべてで妥当か。
    pub fn derives(&self, u: &Universe, lhs: &[usize], rhs: usize) -> bool {
        let m = ClosureModel::build_conj(u, lhs, &self.up_any, &self.up_lt);
        m.sat(u, rhs) & 1 == 1
    }
}

impl Universe {
    /// 語 w の k 文字目以降（接尾辞）の番号。U が接尾辞について閉じていなければ `None`。
    pub fn suffix(&self, w: usize, k: usize) -> Option<usize> {
        let ls = &self.letters[w][k..];
        let b = Bracket::new(ls.iter().map(|&l| self.words[l as usize].clone()).collect());
        self.id(&b)
    }

    /// 文字の番号の列。
    pub fn letter_ids(&self, w: usize) -> Vec<usize> {
        self.letters[w].iter().map(|&l| l as usize).collect()
    }

    /// μ_0 = ⊤、μ_{k+1} = (μ_k) の番号（U に入っていれば）。
    pub fn mu(&self, k: usize) -> Option<usize> {
        let mut w = Bracket::top();
        for _ in 0..k {
            w = Bracket::new(vec![w]);
        }
        self.id(&w)
    }
}

/// 正準モデルの検査の結果。
#[derive(Debug, Clone, Copy, Default)]
pub struct CanonReport {
    /// Φ の大きさ
    pub phi: usize,
    /// 点（Φ の中の理論）の数
    pub worlds: usize,
    /// 検査した添字の数
    pub indices: usize,
}

/// シーケント x ⊢ g（x, g は U の worm）について、論文 §3 の正準モデルを作って検査する。
///
/// - Φ = x と g の接尾辞全体、S = Φ に出る様相。点は、T ∩ Cmp(S) で閉じた Φ の部分集合（理論）。
/// - 関係 R_c は、`index` のすべての添字 c について条件 R1′・R2′・R3 で定める（⊴・◁ は T 全体で判定）。
/// - 検査：(B1)〜(B3)（`index` のすべての組）、真理補題、完全性（g ∈ cl({x}) ⟺ T で導出できる）、
///   保存性（Φ の中の連言の導出可能性が T ∩ Cmp(S) と T で同じ）。
pub fn check_canonical(
    u: &Universe,
    t: &Theory,
    full: &Oracle,
    x: usize,
    g: usize,
    index: &[usize],
) -> Result<CanonReport, String> {
    // Φ
    let mut phi: Vec<usize> = Vec::new();
    for &w in &[x, g] {
        for k in 0..=u.letters[w].len() {
            let s = u.suffix(w, k).ok_or("U が接尾辞について閉じていません")?;
            if !phi.contains(&s) {
                phi.push(s);
            }
        }
    }
    let np = phi.len();
    if np > 14 {
        return Err(format!("Φ が大きすぎます（{np}）"));
    }
    // S と、Φ の元 (c)A の (c, A)
    let head_tail: Vec<Option<(usize, usize)>> = phi
        .iter()
        .map(|&w| {
            if u.letters[w].is_empty() {
                None
            } else {
                Some((u.letters[w][0] as usize, u.suffix(w, 1).unwrap()))
            }
        })
        .collect();
    let mut s: Vec<usize> = head_tail.iter().flatten().map(|&(c, _)| c).collect();
    s.sort_unstable();
    s.dedup();
    let restricted = Oracle::new(&t.restrict(&s));
    let pos = |w: usize| phi.iter().position(|&p| p == w);

    // 理論：cl(Y) = Y となる Y ⊆ Φ（ビットで表す）
    let cl = |y: u32, o: &Oracle| -> u32 {
        let lhs: Vec<usize> = (0..np).filter(|&i| y >> i & 1 == 1).map(|i| phi[i]).collect();
        (0..np).filter(|&i| o.derives(u, &lhs, phi[i])).fold(0u32, |acc, i| acc | 1 << i)
    };
    let mut worlds: Vec<u32> = Vec::new();
    for y in 0u32..(1 << np) {
        let c1 = cl(y, &restricted);
        // 保存性：S に制限した理論と全体の理論で閉包が同じ
        let c2 = cl(y, full);
        if c1 != c2 {
            return Err(format!("保存性が破れました：Y = {y:b}、制限 {c1:b}、全体 {c2:b}"));
        }
        if c1 == y {
            worlds.push(y);
        }
    }
    let nw = worlds.len();
    let mem = |w: u32, i: usize| w >> i & 1 == 1;

    // 関係 R_c
    let rel = |c: usize, wx: u32, wy: u32| -> bool {
        for (i, ht) in head_tail.iter().enumerate() {
            let Some((c1, a1)) = *ht else { continue };
            // R1′(c)：c1 ⊴ c、A ∈ y ⇒ (c1)A ∈ x
            if le(t, c1, c) && pos(a1).is_some_and(|ja| mem(wy, ja)) && !mem(wx, i) {
                return false;
            }
            // R2′(c)：c1 ⊴ e、c1 ⊴ c、(e)A ∈ y ⇒ (c1)A ∈ x
            if le(t, c1, c) && !mem(wx, i) {
                for (j, ht2) in head_tail.iter().enumerate() {
                    let Some((e, a2)) = *ht2 else { continue };
                    if a2 == a1 && mem(wy, j) && le(t, c1, e) {
                        return false;
                    }
                }
            }
            // R3(c)：c1 ◁ c、(c1)A ∈ x ⇒ (c1)A ∈ y
            if t.below(c1, c) && mem(wx, i) && !mem(wy, i) {
                return false;
            }
        }
        true
    };
    let mut r: Vec<Vec<bool>> = Vec::with_capacity(index.len());
    for &c in index {
        let mut m = vec![false; nw * nw];
        for p in 0..nw {
            for q in 0..nw {
                m[p * nw + q] = rel(c, worlds[p], worlds[q]);
            }
        }
        r.push(m);
    }
    let ri = |c: usize| index.iter().position(|&i| i == c);

    // (B1)〜(B3)
    for (ia, &a) in index.iter().enumerate() {
        let ra = &r[ia];
        for p in 0..nw {
            for q in 0..nw {
                if !ra[p * nw + q] {
                    continue;
                }
                for z in 0..nw {
                    if ra[q * nw + z] && !ra[p * nw + z] {
                        return Err(format!("(B1) が破れました：添字 {}", u.word(a)));
                    }
                }
            }
        }
        for (ib, &b) in index.iter().enumerate() {
            let rb = &r[ib];
            if le(t, b, a) {
                for k in 0..nw * nw {
                    if ra[k] && !rb[k] {
                        return Err(format!("(B2) が破れました：{} ⊴ {}", u.word(b), u.word(a)));
                    }
                }
            }
            if t.below(b, a) {
                for p in 0..nw {
                    for q in 0..nw {
                        if !ra[p * nw + q] {
                            continue;
                        }
                        for z in 0..nw {
                            if rb[p * nw + z] && !rb[q * nw + z] {
                                return Err(format!("(B3) が破れました：{} ◁ {}", u.word(b), u.word(a)));
                            }
                        }
                    }
                }
            }
        }
    }

    // 真理補題：w ⊨ θ ⟺ θ ∈ w（θ ∈ Φ）。θ の真偽を短い順に計算する。
    let mut order: Vec<usize> = (0..np).collect();
    order.sort_by_key(|&i| u.letters[phi[i]].len());
    let mut truth = vec![vec![false; nw]; np];
    for &i in &order {
        for p in 0..nw {
            truth[i][p] = match head_tail[i] {
                None => true,
                Some((c, a)) => {
                    let ja = pos(a).unwrap();
                    let ic = ri(c).ok_or("index に S が入っていません")?;
                    (0..nw).any(|q| r[ic][p * nw + q] && truth[ja][q])
                }
            };
            if truth[i][p] != mem(worlds[p], i) {
                return Err(format!("真理補題が破れました：{}", u.word(phi[i])));
            }
        }
    }

    // 完全性：g ∈ cl({x}) ⟺ T で x ⊢ g
    let x0 = cl(1 << pos(x).unwrap(), &restricted);
    let in_x0 = mem(x0, pos(g).unwrap());
    if in_x0 != full.derives(u, &[x], g) {
        return Err("完全性の判定が食い違いました".into());
    }
    Ok(CanonReport { phi: np, worlds: nw, indices: index.len() })
}

/// μ_n の非反射性を示す 2 点のフレーム（論文 §4）が、`index` の添字の上で BC-フレームの条件を満たし、
/// 点 1 で μ_n が真、(⊤)μ_n が偽であることを確かめる。n ≥ 1。
pub fn check_mu_frame(u: &Universe, t: &Theory, n: usize, index: &[usize]) -> Result<(), String> {
    let mu1 = u.mu(n - 1).ok_or("μ_{n-1} が U にありません")?;
    let top = u.top();
    // 関係（点 0, 1、辺のビット：bit0 = (1,0)、bit1 = (0,0)）
    let r = |c: usize| -> u8 {
        if t.below(c, mu1) {
            0b11
        } else if le(t, c, mu1) {
            0b01
        } else {
            0
        }
    };
    let pairs = |m: u8| -> Vec<(usize, usize)> {
        let mut v = Vec::new();
        if m & 1 == 1 {
            v.push((1, 0));
        }
        if m & 2 == 2 {
            v.push((0, 0));
        }
        v
    };
    for &a in index {
        let ra = pairs(r(a));
        // (B1)
        for &(x, y) in &ra {
            for &(y2, z) in &ra {
                if y == y2 && !ra.contains(&(x, z)) {
                    return Err(format!("(B1) が破れました：{}", u.word(a)));
                }
            }
        }
        for &b in index {
            let rb = pairs(r(b));
            if le(t, b, a) && ra.iter().any(|e| !rb.contains(e)) {
                return Err(format!("(B2) が破れました：{} ⊴ {}", u.word(b), u.word(a)));
            }
            if t.below(b, a) {
                for &(x, y) in &ra {
                    for &(x2, z) in &rb {
                        if x == x2 && !rb.contains(&(y, z)) {
                            return Err(format!("(B3) が破れました：{} ◁ {}", u.word(b), u.word(a)));
                        }
                    }
                }
            }
        }
    }
    // 点 1 で μ_n = (μ_{n-1})⊤ が真、(⊤)μ_n が偽
    let succ = |c: usize, x: usize| -> Vec<usize> { pairs(r(c)).into_iter().filter(|&(p, _)| p == x).map(|(_, q)| q).collect() };
    let mu_true = |x: usize| !succ(mu1, x).is_empty();
    if !mu_true(1) {
        return Err("点 1 で μ_n が偽です".into());
    }
    if succ(top, 1).into_iter().any(mu_true) {
        return Err("点 1 で (⊤)μ_n が真です".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn b(s: &str) -> Bracket {
        s.parse().unwrap()
    }

    #[test]
    fn small_lfp() {
        let u = Universe::upto_pairs(4);
        assert_eq!(u.len(), 23);
        let l = least_fixed_point(&u);
        assert_eq!(l.theory.len(), 504);
        assert_eq!(l.theory.order_violations(), (0, 0, 0));
        assert_eq!(l.theory.classes().len(), 17);
        let id = |s: &str| u.id(&b(s)).unwrap();
        // (())() ≡ (())、(()) ◁ ()(())、(())(()) ◁ (()())
        assert!(l.theory.entails(id("(())()"), id("(())")) && l.theory.entails(id("(())"), id("(())()")));
        assert!(l.theory.below(id("(())"), id("()(())")));
        assert!(l.theory.below(id("(())(())"), id("(()())")));
    }

    #[test]
    fn empty_theory_gives_prefixes() {
        // Ψ(∅)：条件のないフレームで妥当なのは、恒等式と「接頭辞を取る」ものだけ
        let u = Universe::upto_pairs(3);
        let t = psi(&u, &Theory::empty(u.len()));
        let id = |s: &str| u.id(&b(s)).unwrap();
        assert!(t.entails(id("()()"), id("()")));
        assert!(t.below(id("()"), id("()()")));
        assert!(!t.below(id("()"), id("(())"))); // 単調性の条件がまだない
    }
}
