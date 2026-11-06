//! Worm Calculus (WC) の証明・検査・証明構成。
//!
//! 出典：A. de Almeida Borges, J. J. Joosten, "The Worm Calculus"
//! (arXiv:1803.10543), Def. 3.1, Thm. 6.1。
//!
//! # 体系（A, B, C は worm、⊤ は省略して書く）
//! - A1：A ⊢ ⊤
//! - A2：ααA ⊢ αA
//! - A3：αA ⊢ βA（α > β）
//! - R1（Cut）：A ⊢ B, B ⊢ C ⇒ A ⊢ C
//! - R2（Nec）：A ⊢ B ⇒ αA ⊢ αB
//! - R3：A ⊢ B, A ⊢ αC ⇒ A ⊢ BαC（B の文字はすべて α より大きい）
//!
//! # 証明の構成法
//! 論文の Thm 6.1（RC は WC 上保存的）の証明の構造に沿うが、細部は
//! このライブラリ独自の構成である。正しさは証明器ではなく、独立した
//! 検査器 [`check`] が保証する。
//!
//! `prove(A, αB)`：
//! 1. A = h r，B = h' r'（h, h' は文字が α 以上の最長の先頭部分）と分ける。
//!    r' が空でなければ（論文の Lemma 4.5 の分解）A ⊢ αh' と A ⊢ r' を
//!    それぞれ部分目標として証明し、R3 で A ⊢ αh'r' を組み立てる。
//!    r' が空で r が空でなければ、A ⊢ h（先頭部分の補題）と h ⊢ αh' を Cut。
//! 2. A, B ∈ W_α なら `prove_lt(α, B, A)`：Thm 3.17 の分岐 (a)/(b) に
//!    従い、接尾部分の補題（XαY ⊢ αY）・Nec・A2・A3・R3 で組み立てる。
//!    最小の文字 λ が α より大きいときは、まず A ⊢ λB を示して A3 で下げる。
//! 3. どの部分目標でも、**局所断片**（文字の引き下げ・消去・尾の切り捨てだけ）
//!    で済む証明を DP で探し、木として小さければそちらに差し替える
//!    （[`Prover::local`]。例：`L…0 ⊢ 0(L−1…0)` は A3 一発）。
//!
//! 部分証明は判断ごとにメモ化して共有するので、証明は DAG になる。
//! 木に展開した大きさは O(n³)、比較（head/body）は標準木のノード番号で
//! メモするので判定は O(|A|·|B|) 時間（algorithms.md §1, §1c）。

use crate::headbody::CtCompare;
use crate::letter::Letter;
use crate::proof::{self, Builder, Calculus, FxBuild, Proof};
use crate::rc;
use crate::spf::Spf;
use crate::worm::Worm;
use serde::Serialize;
use std::collections::HashMap;
use std::fmt;
use std::marker::PhantomData;
use std::rc::Rc;

/// worm のシーケント A ⊢ B（文字は自然数でも順序数でもよい）。
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize)]
pub struct WSeq<L = u32> {
    pub lhs: Worm<L>,
    pub rhs: Worm<L>,
}

impl<L: Letter> WSeq<L> {
    fn new(lhs: &[L], rhs: &[L]) -> Self {
        WSeq { lhs: Worm::new(lhs.to_vec()), rhs: Worm::new(rhs.to_vec()) }
    }
}

impl<L: Letter> fmt::Display for WSeq<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ⊢ {}", self.lhs, self.rhs)
    }
}

/// WC の規則。
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize)]
pub enum WcRule {
    A1,
    A2,
    A3,
    Cut,
    Nec,
    R3,
}

impl fmt::Display for WcRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            WcRule::A1 => "A1",
            WcRule::A2 => "A2",
            WcRule::A3 => "A3",
            WcRule::Cut => "Cut",
            WcRule::Nec => "Nec",
            WcRule::R3 => "R3",
        };
        write!(f, "{s}")
    }
}

/// WC という証明体系（検査の規則だけを定める）。文字の型ごとに 1 つ。
///
/// 【Rust メモ】`PhantomData<L>` は「中身は持たないが、型 L に関係している」
/// ことをコンパイラに伝えるための印。
pub struct Wc<L = u32>(PhantomData<L>);

pub type WcProof<L = u32> = Proof<WSeq<L>, WcRule>;

impl<L: Letter> Calculus for Wc<L> {
    type Judgment = WSeq<L>;
    type Rule = WcRule;

    fn check_step(rule: &WcRule, prem: &[&WSeq<L>], c: &WSeq<L>) -> Result<(), String> {
        let (l, r) = (c.lhs.letters(), c.rhs.letters());
        let fail = |msg: &str| Err(msg.to_string());
        match (rule, prem) {
            (WcRule::A1, []) => {
                if r.is_empty() { Ok(()) } else { fail("A1 の右辺は ⊤ でなければならない") }
            }
            (WcRule::A2, []) => match (l, r) {
                ([a, b, x @ ..], [c0, y @ ..]) if a == b && b == c0 && x == y => Ok(()),
                _ => fail("A2 の形 ααX ⊢ αX ではない"),
            },
            (WcRule::A3, []) => match (l, r) {
                ([a, x @ ..], [b, y @ ..]) if a > b && x == y => Ok(()),
                _ => fail("A3 の形 αX ⊢ βX（α > β）ではない"),
            },
            (WcRule::Cut, [p, q]) => {
                if p.lhs == c.lhs && p.rhs == q.lhs && q.rhs == c.rhs {
                    Ok(())
                } else {
                    fail("Cut の前提と結論が噛み合わない")
                }
            }
            (WcRule::Nec, [p]) => match (l, r) {
                ([g, x @ ..], [h, y @ ..]) if g == h && x == p.lhs.letters() && y == p.rhs.letters() => {
                    Ok(())
                }
                _ => fail("Nec の形 A ⊢ B ⇒ αA ⊢ αB ではない"),
            },
            (WcRule::R3, [p, q]) => {
                let Some(alpha) = q.rhs.letters().first() else {
                    return fail("R3 の第 2 前提の右辺が αC の形ではない");
                };
                let b = p.rhs.letters();
                let ok = p.lhs == c.lhs
                    && q.lhs == c.lhs
                    && b.iter().all(|x| x > alpha)
                    && r.len() == b.len() + q.rhs.len()
                    && r[..b.len()] == *b
                    && r[b.len()..] == *q.rhs.letters();
                if ok { Ok(()) } else { fail("R3 の条件を満たさない") }
            }
            _ => fail("規則と前提の個数が合わない"),
        }
    }
}

/// 証明を検査し、結論を返す。
pub fn check<L: Letter>(p: &WcProof<L>) -> Result<&WSeq<L>, String> {
    proof::check::<Wc<L>>(p)
}

/// RC（＝ GLP）で A ⊢ B か。証明器の前提条件の確認に使う。
fn rc_holds<L: Letter>(a: &[L], b: &[L]) -> bool {
    rc::entails(&Spf::from(&Worm::new(a.to_vec())), &Spf::from(&Worm::new(b.to_vec())))
}

fn cons<L: Clone>(x: L, rest: &[L]) -> Vec<L> {
    let mut v = Vec::with_capacity(rest.len() + 1);
    v.push(x);
    v.extend_from_slice(rest);
    v
}

/// 最小の文字（空でないことが前提）。
fn min_of<L: Letter>(a: &[L], b: &[L]) -> L {
    a.iter().chain(b).min().expect("空でない").clone()
}

/// 元の worm の中の区間 [start, end)。
///
/// 証明器と判定器の再帰に現れる worm は、左辺はすべて元の A の、右辺は
/// すべて元の B の連続部分なので、中身をコピーせず区間で持てる。
/// 比較（head/body）に渡すものは、さらに標準木のノードになっている。
type Seg = (usize, usize);

/// worm シーケント A ⊢ B の構文的な判定器（RC のモデルを使わない）。
///
/// - B = ⊤ なら真。
/// - B = αB₀ とし、A = hA rA, B₀ = hB rB（h は文字が α 以上の最長の先頭部分）。
///   - rA, rB がともに空なら、head/body 比較（Thm 3.17）で B₀ ◁ A か。
///   - そうでなければ hA ⊢ αhB かつ A ⊢ rB（Lemma 4.5 の分解）。
///
/// 比較は [`CtCompare`]（標準木のノード番号でメモ）で行うので、全体で
/// O(|A|·|B|) 時間（algorithms.md §1）。正しさは Lemma 4.5 と Thm 3.17 に依拠し、
/// テストでは RC と突き合わせている。
pub struct Decider<L = u32> {
    cmp: CtCompare<L>,
    left: Rc<[L]>,
    right: Rc<[L]>,
    memo: HashMap<(Seg, Seg), bool>,
}

impl<L: Letter> Decider<L> {
    /// A ⊢ B を調べる判定器（比較の木は B を w 側、A を v 側にして作る）。
    pub fn new(a: &[L], b: &[L]) -> Self {
        Decider { cmp: CtCompare::new(b, a), left: a.into(), right: b.into(), memo: HashMap::new() }
    }

    /// 元の A ⊢ B か。
    pub fn decide_root(&mut self) -> bool {
        let (na, nb) = (self.left.len(), self.right.len());
        self.decide((0, na), (0, nb))
    }

    fn decide(&mut self, a: Seg, b: Seg) -> bool {
        if b.0 == b.1 {
            return true;
        }
        if let Some(&ans) = self.memo.get(&(a, b)) {
            return ans;
        }
        let (left, right) = (Rc::clone(&self.left), Rc::clone(&self.right));
        let (xa, xb) = (&left[a.0..a.1], &right[b.0..b.1]);
        let alpha = &xb[0];
        let ka = xa.iter().position(|x| x < alpha).unwrap_or(xa.len());
        let kb = xb[1..].iter().position(|x| x < alpha).unwrap_or(xb.len() - 1);
        let ans = if ka == xa.len() && kb == xb.len() - 1 {
            let (nw, nv) = (self.cmp.node_w(b.0 + 1, b.1), self.cmp.node_v(a.0, a.1));
            self.cmp.lt(nw, nv) // B₀ ◁ A
        } else {
            // hA ⊢ α hB（α hB は B の区間 [b.0, b.0+1+kb)）かつ A ⊢ rB
            self.decide((a.0, a.0 + ka), (b.0, b.0 + 1 + kb)) && self.decide(a, (b.0 + 1 + kb, b.1))
        };
        self.memo.insert((a, b), ans);
        ans
    }

    /// 比較のメモごと証明器に渡す（同じ比較を 2 回しないため）。
    fn into_compare(self) -> CtCompare<L> {
        self.cmp
    }
}

/// WC（＝ RC ＝ GLP）で worm シーケント A ⊢ B が成り立つか（構文的判定）。
pub fn decide<L: Letter>(a: &Worm<L>, b: &Worm<L>) -> bool {
    Decider::new(a.letters(), b.letters()).decide_root()
}

/// WC の証明を組み立てる。
///
/// 各部分目標について、まず Lemma 4.5 / Thm 3.17 に沿った証明を作り（モジュールの
/// 説明を参照）、局所断片 [`Prover::local`]（文字の引き下げ・消去・尾の切り捨て）
/// だけで済む証明の方が木として小さければ、そちらに差し替える。
/// 前者は常に作るので、証明の木の大きさは O(n³) の上界（algorithms.md §1）を保つ。
pub struct Prover<L = u32> {
    b: Builder<WSeq<L>, WcRule>,
    cmp: CtCompare<L>,
    left: Rc<[L]>,
    right: Rc<[L]>,
    /// 済んだ部分目標（判断の中身で引く。同じ中身の目標は位置が違っても共有）
    goals: HashMap<WSeq<L>, usize, FxBuild>,
    /// 局所断片の DP の作業領域（呼ぶたびに確保し直さない）
    dp_cost: Vec<u128>,
    dp_how: Vec<u8>,
}

impl<L: Letter> Prover<L> {
    /// A ⊢ B の証明器。
    pub fn new(a: &[L], b: &[L]) -> Self {
        Self::with_compare(a, b, CtCompare::new(b, a))
    }

    fn with_compare(a: &[L], b: &[L], cmp: CtCompare<L>) -> Self {
        Prover {
            b: Builder::new(),
            cmp,
            left: a.into(),
            right: b.into(),
            goals: HashMap::default(),
            dp_cost: Vec::new(),
            dp_how: Vec::new(),
        }
    }

    // ---------------- 規則を 1 回使うだけの小さな部品 ----------------

    fn axiom(&mut self, rule: WcRule, l: &[L], r: &[L]) -> usize {
        self.b.add(rule, vec![], WSeq::new(l, r))
    }

    /// p: A ⊢ B, q: B ⊢ C から A ⊢ C（恒等式との Cut は省く）
    fn cut(&mut self, p: usize, q: usize) -> usize {
        let (cp, cq) = (self.b.conclusion(p).clone(), self.b.conclusion(q).clone());
        debug_assert_eq!(cp.rhs, cq.lhs);
        if cp.lhs == cp.rhs {
            return q;
        }
        if cq.lhs == cq.rhs {
            return p;
        }
        self.b.add(WcRule::Cut, vec![p, q], WSeq { lhs: cp.lhs, rhs: cq.rhs })
    }

    /// p: A ⊢ B から γA ⊢ γB
    fn nec(&mut self, g: &L, p: usize) -> usize {
        let c = self.b.conclusion(p).clone();
        let seq = WSeq::new(&cons(g.clone(), c.lhs.letters()), &cons(g.clone(), c.rhs.letters()));
        self.b.add(WcRule::Nec, vec![p], seq)
    }

    /// p: A ⊢ B, q: A ⊢ αC から A ⊢ BαC
    fn r3(&mut self, p: usize, q: usize) -> usize {
        let (cp, cq) = (self.b.conclusion(p).clone(), self.b.conclusion(q).clone());
        let rhs = cp.rhs.concat(&cq.rhs);
        self.b.add(WcRule::R3, vec![p, q], WSeq { lhs: cp.lhs, rhs })
    }

    /// A3 を使って λX ⊢ μX（λ > μ）を足す：p: A ⊢ λX から A ⊢ μX
    fn lower(&mut self, p: usize, mu: &L) -> usize {
        let c = self.b.conclusion(p).clone();
        let r = c.rhs.letters();
        if r[0] == *mu {
            return p;
        }
        let a3 = self.axiom(WcRule::A3, r, &cons(mu.clone(), &r[1..]));
        self.cut(p, a3)
    }

    // ---------------- 補題 ----------------

    /// 恒等式 A ⊢ A（論文 Cor. 3.4）。Nec を |A| 回。
    /// Cut の相手になったときは [`Prover::cut`] が省くので、証明には残らない。
    pub fn identity(&mut self, a: &[L]) -> usize {
        let mut p = self.axiom(WcRule::A1, &[], &[]);
        for g in a.iter().rev() {
            p = self.nec(g, p);
        }
        p
    }

    /// 先頭部分の補題（論文 Lemma 3.3）：full ⊢ full[..k]。
    /// 内側を A1 で捨て、Nec を k 回（局所断片の中で最小）。
    fn prefix(&mut self, full: &[L], k: usize) -> usize {
        if k == full.len() {
            return self.identity(full);
        }
        if let Some(id) = self.b.lookup(&WSeq::new(full, &full[..k])) {
            return id;
        }
        if k == 0 {
            return self.axiom(WcRule::A1, full, &[]);
        }
        let p = self.prefix(&full[1..], k - 1);
        self.nec(&full[0], p)
    }

    /// 接尾部分の補題（論文 Lemma 3.5）：v = X μ Y（X の文字は μ より大）のとき v ⊢ μY。
    /// `i` は v[i] = μ となる位置。X の文字を内側から 1 つずつ A3＋A2 で吸収する。
    /// 一番内側は γμY ⊢ μμY ⊢ μY の 3 ノードで、恒等式 μY ⊢ μY は作らない。
    fn suffix(&mut self, v: &[L], i: usize) -> usize {
        if i == 0 {
            return self.identity(v);
        }
        if let Some(id) = self.b.lookup(&WSeq::new(v, &v[i..])) {
            return id;
        }
        let (mu, tail) = (&v[i], &v[i..]); // tail = μY
        // v ⊢ γ μY（γ = v[0]）
        let n = if i == 1 {
            None
        } else {
            let p = self.suffix(&v[1..], i - 1); // v[1..] ⊢ μY
            Some(self.nec(&v[0], p))
        };
        let a3 = self.axiom(WcRule::A3, &cons(v[0].clone(), tail), &cons(mu.clone(), tail)); // γμY ⊢ μμY
        let a2 = self.axiom(WcRule::A2, &cons(mu.clone(), tail), tail); // μμY ⊢ μY
        let c = match n {
            Some(n) => self.cut(n, a3),
            None => a3,
        };
        self.cut(c, a2)
    }

    /// 局所断片：X ⊢ Y を次の手だけで示す証明のうち、木として一番小さいもの。
    ///
    /// 外側から 1 文字ずつ見て、
    /// - **残す**：a ≥ b なら aX' ⊢ bY'（X' ⊢ Y' から Nec、a > b なら A3 で下げる）
    /// - **消す**：a ≥ b なら aX' ⊢ bY'（X' ⊢ bY' から Nec・A3・A2 で a を吸収）
    /// - 内側の尾は A1 で捨てる／そっくり同じ尾からはタダで始める
    ///   （αT ⊢ βT は A3 一発、ααT ⊢ αT は A2 一発）。
    ///
    /// 候補は 2 つ：
    /// 1. A1 で尾を捨て、全部「残す」（Y が X の先頭と文字ごとに ≤ のとき）。
    ///    A1 で始めるなら「消す」は得にならないので、これで最小。
    /// 2. 最長の共通の尾 T から始め、X = P T, Y = Q T の P → Q を「残す・消す」の
    ///    DP で最小化（O(|P|·|Q|)。大きすぎるときは省く）。
    ///
    /// まず大きさだけを計算し、`bound` より小さいときだけ実際に組み立てる。
    /// `L…0 ⊢ 0(L−1…0)` のような「同じ尾を A3 一発で下げる」証明もこの特別な場合。
    fn local(&mut self, x: &[L], y: &[L], bound: u128) -> Option<usize> {
        let (nx, ny) = (x.len(), y.len());
        if ny > nx || x == y {
            return None;
        }
        // 候補 1 の大きさ（Cut が恒等式を省く分も、組み立てたときと同じに数える）
        let c1 = if x.iter().zip(y).all(|(a, b)| b <= a) {
            let (mut ident, mut c) = (nx == ny, 1u128); // A1：⊤ ⊢ ⊤ なら恒等式
            for j in (0..ny).rev() {
                c += 1; // Nec
                if x[j] > y[j] {
                    if ident {
                        (c, ident) = (1, false); // 恒等式との Cut は省かれ、A3 だけが残る
                    } else {
                        c += 2; // A3 と Cut
                    }
                }
            }
            Some(c)
        } else {
            None
        };
        // 候補 2：共通の尾 T から始める
        let t = x.iter().rev().zip(y.iter().rev()).take_while(|(a, b)| a == b).count();
        let (np, nq) = (nx - t, ny - t);
        // DP の下限：Q の各文字に Nec が 1 つ、消す文字 1 つに少なくとも 3（一番内側だけ 1）
        const BUDGET: usize = 1 << 18;
        let lower_bound = if np >= nq { (nq + 3 * (np - nq)).saturating_sub(2).max(1) as u128 } else { u128::MAX };
        let target = c1.map_or(bound, |c| c.min(bound));
        let c2 = if nq <= np && lower_bound < target && (np + 1) * (nq + 1) <= BUDGET {
            self.local_plan(x, y, np, nq)
        } else {
            None
        };
        match (c1, c2) {
            (Some(a), Some((b, path))) if b < a => (b < bound).then(|| self.build_plan(x, y, &path)),
            (Some(a), _) => (a < bound).then(|| self.build_keep_all(x, y)),
            (None, Some((b, path))) => (b < bound).then(|| self.build_plan(x, y, &path)),
            (None, None) => None,
        }
    }

    /// 候補 1 を組み立てる：x[|y|..] ⊢ ⊤（A1）から、外側へ Nec（必要なら A3 で下げる）。
    fn build_keep_all(&mut self, x: &[L], y: &[L]) -> usize {
        let mut p = self.axiom(WcRule::A1, &x[y.len()..], &[]);
        for j in (0..y.len()).rev() {
            p = self.nec(&x[j], p);
            p = self.lower(p, &y[j]);
        }
        p
    }

    /// 候補 2 の DP：x = P T, y = Q T（|P| = np, |Q| = nq）。g(q, i) は x[q..] ⊢ y[i..] の
    /// 木のノード数で、(np, nq)（共通の尾 T）は 0。大きさと、外側からの手の列を返す。
    #[allow(clippy::type_complexity)]
    fn local_plan(&mut self, x: &[L], y: &[L], np: usize, nq: usize) -> Option<(u128, Vec<(usize, usize, u8)>)> {
        const INF: u128 = u128::MAX;
        let ny = y.len();
        let w = nq + 1;
        let at = |q: usize, i: usize| q * w + i;
        let (g, how) = (&mut self.dp_cost, &mut self.dp_how); // 2 = 残す、3 = 消す
        g.clear();
        g.resize((np + 1) * w, INF);
        how.clear();
        how.resize((np + 1) * w, 0);
        g[at(np, nq)] = 0;
        for q in (0..np).rev() {
            for i in (0..=nq).rev() {
                // y が尽きていたら x の文字はもう処理できない（A1 で捨てるのは候補 1）
                if i == ny || x[q] < y[i] {
                    continue;
                }
                let lowered = if x[q] > y[i] { 2 } else { 0 };
                let keep = if i < nq {
                    match g[at(q + 1, i + 1)] {
                        INF => INF,
                        0 => if lowered > 0 { 1 } else { INF }, // A3 一発
                        s => s + 1 + lowered,
                    }
                } else {
                    INF
                };
                let del = match g[at(q + 1, i)] {
                    INF => INF,
                    0 => if lowered == 0 { 1 } else { 3 }, // A2 一発 / A3＋A2
                    s => s + 3 + lowered,
                };
                if keep <= del && keep < INF {
                    (g[at(q, i)], how[at(q, i)]) = (keep, 2);
                } else if del < INF {
                    (g[at(q, i)], how[at(q, i)]) = (del, 3);
                }
            }
        }
        if g[at(0, 0)] == INF {
            return None;
        }
        let mut path = Vec::new();
        let (mut q, mut i) = (0, 0);
        while (q, i) != (np, nq) {
            let h = how[at(q, i)];
            path.push((q, i, h));
            if h == 2 {
                i += 1;
            }
            q += 1;
        }
        Some((g[at(0, 0)], path))
    }

    /// 候補 2 を、手の列 `path`（外側から）に従って内側から組み立てる。
    fn build_plan(&mut self, x: &[L], y: &[L], path: &[(usize, usize, u8)]) -> usize {
        let mut p: Option<usize> = None; // None = 共通の尾（恒等式、作らない）
        for &(q, i, h) in path.iter().rev() {
            let (a, b) = (&x[q], &y[i]);
            p = Some(match (h, p) {
                (2, None) => self.axiom(WcRule::A3, &x[q..], &y[i..]), // aT ⊢ bT（a > b）
                (2, Some(s)) => {
                    let n = self.nec(a, s); // x[q..] ⊢ a y[i+1..]
                    self.lower(n, b)
                }
                (_, None) => {
                    // a y[i..] ⊢ y[i..]
                    if a == b {
                        self.axiom(WcRule::A2, &x[q..], &y[i..])
                    } else {
                        let a3 = self.axiom(WcRule::A3, &x[q..], &cons(b.clone(), &y[i..]));
                        let a2 = self.axiom(WcRule::A2, &cons(b.clone(), &y[i..]), &y[i..]);
                        self.cut(a3, a2)
                    }
                }
                (_, Some(s)) => {
                    let n = self.nec(a, s); // x[q..] ⊢ a y[i..]
                    let l = self.lower(n, b); //        ⊢ b y[i..] = b b y[i+1..]
                    let a2 = self.axiom(WcRule::A2, &cons(b.clone(), &y[i..]), &y[i..]);
                    self.cut(l, a2)
                }
            });
        }
        p.expect("手が 1 つはある")
    }

    // ---------------- 本体 ----------------

    /// 元の A ⊢ B の証明。
    pub fn prove_root(&mut self) -> usize {
        let (na, nb) = (self.left.len(), self.right.len());
        self.prove((0, na), (0, nb))
    }

    /// A ⊢ B の証明（A は左辺側、B は右辺側の区間。RC で成り立つことが前提）。
    fn prove(&mut self, a: Seg, b: Seg) -> usize {
        let (left, right) = (Rc::clone(&self.left), Rc::clone(&self.right));
        let (xa, xb) = (&left[a.0..a.1], &right[b.0..b.1]);
        let goal = WSeq::new(xa, xb);
        if let Some(&id) = self.goals.get(&goal) {
            return id;
        }
        debug_assert!(rc_holds(xa, xb), "前提違反: {:?} ⊢ {:?}", xa, xb);
        let id = if xa == xb {
            self.identity(xa)
        } else if xb.is_empty() {
            self.axiom(WcRule::A1, xa, &[])
        } else {
            // A = hA rA, B = α hB rB（h は文字が α 以上の最長の先頭部分）
            let alpha = &xb[0];
            let ka = xa.iter().position(|x| x < alpha).unwrap_or(xa.len());
            let kb = xb[1..].iter().position(|x| x < alpha).unwrap_or(xb.len() - 1);
            let c = if ka == xa.len() && kb == xb.len() - 1 {
                self.prove_lt(alpha, (b.0 + 1, b.1), a)
            } else if kb < xb.len() - 1 {
                // Lemma 4.5 の分解：A ⊢ α hB（独立の目標）と A ⊢ rB を R3 で
                let p1 = self.prove(a, (b.0, b.0 + 1 + kb));
                let p2 = self.prove(a, (b.0 + 1 + kb, b.1));
                self.r3(p1, p2)
            } else {
                // rB = ⊤, rA ≠ ⊤：A ⊢ hA ⊢ α hB
                let pre = self.prefix(xa, ka);
                let p1 = self.prove((a.0, a.0 + ka), b);
                self.cut(pre, p1)
            };
            // 局所断片の方が小さければそちら
            let bound = self.b.tree_size(c);
            self.local(xa, xb, bound).unwrap_or(c)
        };
        self.goals.insert(goal, id);
        id
    }

    /// v ⊢ μw の証明（w は右辺側、v は左辺側の区間。文字はすべて μ 以上、
    /// RC で成り立つことが前提）。
    fn prove_lt(&mut self, mu: &L, w: Seg, v: Seg) -> usize {
        let (left, right) = (Rc::clone(&self.left), Rc::clone(&self.right));
        let (xw, xv) = (&right[w.0..w.1], &left[v.0..v.1]);
        let target = cons(mu.clone(), xw);
        let goal = WSeq::new(xv, &target);
        if let Some(&id) = self.goals.get(&goal) {
            return id;
        }
        debug_assert!(rc_holds(xv, &target), "前提違反: {:?} ⊢ {:?}", xv, target);
        let c = if xw.is_empty() {
            // v ⊢ γ（γ は v の先頭）から A3 で v ⊢ μ
            let p = self.prefix(xv, 1);
            self.lower(p, mu)
        } else {
            let lambda = min_of(xw, xv);
            if lambda > *mu {
                let p = self.prove_lt(&lambda, w, v); // v ⊢ λw
                self.lower(p, mu)
            } else {
                self.thm317(mu, w, v)
            }
        };
        let bound = self.b.tree_size(c);
        let id = self.local(xv, &target, bound).unwrap_or(c);
        self.goals.insert(goal, id);
        id
    }

    /// λ = μ のとき：Thm 3.17 の分岐 (a)/(b) に沿って v ⊢ μw を組み立てる。
    fn thm317(&mut self, mu: &L, w: Seg, v: Seg) -> usize {
        let (left, right) = (Rc::clone(&self.left), Rc::clone(&self.right));
        let (xw, xv) = (&right[w.0..w.1], &left[v.0..v.1]);
        let target = cons(mu.clone(), xw);
        // w = h(w) μ b(w)、v = h(v) μ b(v)（μ が無ければ b は ⊤）
        let iw = xw.iter().position(|x| x == mu);
        let iv = xv.iter().position(|x| x == mu);
        let hw = (w.0, w.0 + iw.unwrap_or(xw.len()));
        let bw = iw.map_or((w.1, w.1), |i| (w.0 + i + 1, w.1));
        let hv = (v.0, v.0 + iv.unwrap_or(xv.len()));
        let bv = iv.map_or((v.1, v.1), |i| (v.0 + i + 1, v.1));
        let (nw, nbv) = (self.cmp.node_w(w.0, w.1), self.cmp.node_v(bv.0, bv.1));
        if self.cmp.le(nw, nbv) {
            // (a) w ⊴ b(v)。v = h(v) μ b(v) なので v ⊢ μ b(v)
            let s = self.suffix(xv, hv.1 - hv.0);
            if self.cmp.lt(nw, nbv) {
                let q = self.prove_lt(mu, w, bv); // b(v) ⊢ μw
                let n = self.nec(mu, q); // μ b(v) ⊢ μμw
                let a2 = self.axiom(WcRule::A2, &cons(mu.clone(), &target), &target);
                let c = self.cut(s, n);
                self.cut(c, a2)
            } else {
                let q = self.prove(bv, w); // b(v) ⊢ w（同値）
                let n = self.nec(mu, q); // μ b(v) ⊢ μw
                self.cut(s, n)
            }
        } else if iw.is_none() {
            // (b) で μ ∉ w：v ⊢ h(v) ⊢ μ' w ⊢ μw
            let mu2 = min_of(xw, &left[hv.0..hv.1]);
            let p1 = self.prove_lt(&mu2, w, hv);
            let pre = self.prefix(xv, hv.1 - hv.0);
            let c = self.cut(pre, p1);
            self.lower(c, mu)
        } else {
            // (b) で w = h(w) μ b(w)
            let (shw, shv) = (&right[hw.0..hw.1], &left[hv.0..hv.1]);
            let mu2 = if shw.is_empty() { shv[0].clone() } else { min_of(shw, shv) };
            let p1 = self.prove_lt(&mu2, hw, hv); // h(v) ⊢ μ' h(w)
            let pre = self.prefix(xv, hv.1 - hv.0); // v ⊢ h(v)
            let c = self.cut(pre, p1); // v ⊢ μ' h(w)
            let p2 = self.prove_lt(mu, bw, v); // v ⊢ μ b(w)
            let r = self.r3(c, p2); // v ⊢ μ' h(w) μ b(w)
            self.lower(r, mu) // v ⊢ μ h(w) μ b(w) = μw
        }
    }

    /// 比較で調べた状態の数（実験用）。
    pub fn compare_states(&self) -> usize {
        self.cmp.states()
    }

    /// 組み立てた DAG から `root` の証明を取り出す。
    pub fn finish(self, root: usize) -> WcProof<L> {
        self.b.finish(root)
    }
}

/// A ⊢ B の WC 証明を作る。成り立たなければ `Err`。
pub fn prove<L: Letter>(a: &Worm<L>, b: &Worm<L>) -> Result<WcProof<L>, String> {
    let mut d = Decider::new(a.letters(), b.letters());
    if !d.decide_root() {
        return Err(format!("{a} ⊢ {b} は成り立たない（WC でも RC でも証明できない）"));
    }
    let mut p = Prover::with_compare(a.letters(), b.letters(), d.into_compare());
    let root = p.prove_root();
    Ok(p.finish(root))
}

/// A <_n B（B ⊢ ⟨n⟩A）の WC 証明を作る。
pub fn prove_lt<L: Letter>(n: L, a: &Worm<L>, b: &Worm<L>) -> Result<WcProof<L>, String> {
    prove(b, &Worm::new(cons(n, a.letters())))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn w(s: &str) -> Worm {
        s.parse().unwrap()
    }

    fn proves(a: &str, b: &str) {
        let p = prove(&w(a), &w(b)).unwrap();
        let c = check(&p).unwrap_or_else(|e| panic!("{a} ⊢ {b}: {e}\n{p}"));
        assert_eq!(c, &WSeq { lhs: w(a), rhs: w(b) });
    }

    #[test]
    fn simple_proofs() {
        proves("1", "0");
        proves("1", "0 0 0");
        proves("1 0", "1");
        proves("1", "1 0");
        proves("1 1", "0 1 0 1");
        proves("2", "1 1 1");
        proves("2 0 1", "1 0 1");
        proves("2 0 1", "0 1 1");
        proves("0 1 1 0 2", "0 1 1");
        proves("0 1 1 0 2", "0 0 1 0 1");
    }

    /// 無駄を削った証明器の大きさ（algorithms.md §1c）
    #[test]
    fn small_proofs_for_easy_families() {
        let size = |a: &str, b: &str| {
            let p = prove(&w(a), &w(b)).unwrap();
            assert!(check(&p).is_ok());
            (p.dag_size(), p.tree_size())
        };
        // L X ⊢ 0 X は A3 一発（以前は L = 24 で 507 ノード、L = 64 で 2647 ノード）
        let dec: Vec<String> = (0..=24).rev().map(|i| i.to_string()).collect();
        let a = dec.join(" ");
        let b = format!("0 {}", dec[1..].join(" "));
        assert_eq!(size(&a, &b), (1, 1));
        // 2 1 0 ⊢ 1 0：A3（2·10 ⊢ 1·10）と A2（1 1 0 ⊢ 1 0）と Cut
        assert_eq!(size("2 1 0", "1 0"), (3, 3));
        // (5 4)^k 3 2 1 0 ⊢ 0 (4 0)^k：以前は木が Θ(n²)、いまは線形
        let k = 12;
        let a = format!("{}3 2 1 0", "5 4 ".repeat(k));
        let b = format!("0{}", " 4 0".repeat(k));
        let (dag, tree) = size(&a, &b);
        assert!(tree <= 4 * k as u128 + 4, "tree = {tree}");
        assert!(dag <= 4 * k + 4, "dag = {dag}");
    }

    #[test]
    fn refuses_false_sequents() {
        assert!(prove(&w("0"), &w("1")).is_err());
        assert!(prove(&w("0 1"), &w("1 0 1")).is_err());
    }

    #[test]
    fn checker_rejects_bad_steps() {
        let bad = Proof {
            nodes: vec![proof::Node {
                rule: WcRule::A3,
                premises: vec![],
                conclusion: WSeq { lhs: w("0 1"), rhs: w("1 1") },
            }],
            root: 0,
        };
        assert!(check(&bad).is_err());
        let bad_r3 = Proof {
            nodes: vec![
                proof::Node { rule: WcRule::A1, premises: vec![], conclusion: WSeq { lhs: w("1"), rhs: w("") } },
                proof::Node { rule: WcRule::A1, premises: vec![], conclusion: WSeq { lhs: w("1"), rhs: w("") } },
                proof::Node {
                    rule: WcRule::R3,
                    premises: vec![0, 1],
                    conclusion: WSeq { lhs: w("1"), rhs: w("") },
                },
            ],
            root: 2,
        };
        assert!(check(&bad_r3).is_err());
    }
}
