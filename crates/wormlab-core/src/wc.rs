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
//!    （[`Prover::local_cost`]。例：`L…0 ⊢ 0(L−1…0)` は A3 一発）。
//!
//! 部分証明は判断ごとにメモ化して共有するので、証明は DAG になる。
//! 木に展開した大きさは O(n³)、比較（head/body）は標準木のノード番号で
//! メモするので判定は O(|A|·|B|) 時間（algorithms.md §1, §1c）。

use crate::latex::ToLatex;
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

impl<L: Letter> ToLatex for WSeq<L> {
    fn to_latex(&self) -> String {
        format!("{} \\vdash {}", self.lhs.to_latex(), self.rhs.to_latex())
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

impl ToLatex for WcRule {
    fn to_latex(&self) -> String {
        crate::latex::rule_name(&self.to_string())
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
    memo: HashMap<(Seg, Seg), bool, FxBuild>,
}

impl<L: Letter> Decider<L> {
    /// A ⊢ B を調べる判定器（比較の木は B を w 側、A を v 側にして作る）。
    pub fn new(a: &[L], b: &[L]) -> Self {
        Decider { cmp: CtCompare::new(b, a), left: a.into(), right: b.into(), memo: HashMap::default() }
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

/// WC の証明を組み立てる。2 段構え：
///
/// 1. **計画**：各部分目標について、Lemma 4.5 / Thm 3.17 に沿った作り方（モジュールの
///    説明を参照）と、局所断片 [`Prover::local_cost`]（文字の引き下げ・消去・尾の
///    切り捨て）だけで済む作り方の、木としての大きさを**ノードを作らずに**計算し、
///    小さい方を選ぶ。
/// 2. **組み立て**：根から、選んだ作り方に従ってノードを作る。使われない候補の
///    ノードは作らない。
///
/// 前者の作り方は常に候補に入るので、証明の木の大きさは O(n³) の上界
/// （algorithms.md §1）を保つ。2 つの段階は同じ構成のコード（[`Sink`] で抽象化）を
/// 共有するので、計画した大きさと実際の大きさは一致する（デバッグビルドで確認）。
pub struct Prover<L = u32> {
    b: Builder<WSeq<L>, WcRule>,
    cmp: CtCompare<L>,
    left: Rc<[L]>,
    right: Rc<[L]>,
    /// 計画段階：部分目標（判断の中身で引く）→ 木の大きさと選んだ作り方
    plans: HashMap<WSeq<L>, Plan, FxBuild>,
    /// 組み立て段階：部分目標 → 作ったノード
    built: HashMap<WSeq<L>, usize, FxBuild>,
    /// 局所断片の DP の作業領域（呼ぶたびに確保し直さない）
    dp_cost: Vec<u32>,
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
            plans: HashMap::default(),
            built: HashMap::default(),
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
    /// 内側を A1 で捨て、Nec を k 回（局所断片の中で最小）。木の大きさは k + 1。
    /// （同じ形のノードは Builder が共有するので、メモは要らない。）
    fn prefix(&mut self, full: &[L], k: usize) -> usize {
        if k == full.len() {
            return self.identity(full);
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
    /// 木の大きさは 3 + 5(i − 1)。
    fn suffix(&mut self, v: &[L], i: usize) -> usize {
        if i == 0 {
            return self.identity(v);
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
    ///    DP で最小化（消す数 D = |P| − |Q| の帯だけ見るので O(|P|·(D+1))。
    ///    下限が `bound` 以上のときや、大きすぎるときは省く）。
    ///
    /// 大きさだけを計算し、`bound` より小さければ（大きさ, 作り方）を返す。
    /// `L…0 ⊢ 0(L−1…0)` のような「同じ尾を A3 一発で下げる」証明もこの特別な場合。
    fn local_cost(&mut self, x: &[L], y: &[L], bound: u128) -> Option<(u128, Choice)> {
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
        let c2 = if nq <= np && lower_bound < target && (np + 1) * (np - nq + 1) <= BUDGET {
            self.local_plan(x, y, np, nq)
        } else {
            None
        };
        let best = match (c1, c2) {
            (Some(a), Some((b, path))) if b < a => (b, Choice::Dp(path)),
            (Some(a), _) => (a, Choice::KeepAll),
            (None, Some((b, path))) => (b, Choice::Dp(path)),
            (None, None) => return None,
        };
        (best.0 < bound).then_some(best)
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

    /// 候補 2 の DP：x = P T, y = Q T（|P| = np, |Q| = nq）で、位置 (np, nq)（共通の尾 T）
    /// から外側へ「残す・消す」を選ぶ。大きさと、外側からの手の列を返す。
    ///
    /// 消す文字の数は D = np − nq に決まっているので、状態 (q, i) は d = q − i ∈ [0, D]
    /// の帯にしか現れない。帯だけを表に持つので O(np·(D+1))。
    /// g(q, d) は x[q..] ⊢ y[q−d..] の木のノード数で、(np, D)（共通の尾）は 0。
    #[allow(clippy::type_complexity)]
    fn local_plan(&mut self, x: &[L], y: &[L], np: usize, nq: usize) -> Option<(u128, Vec<(usize, usize, u8)>)> {
        const INF: u32 = u32::MAX;
        let ny = y.len();
        let dd = np - nq; // 消す文字の数 D
        let w = dd + 1;
        let at = |q: usize, d: usize| q * w + d;
        let (g, how) = (&mut self.dp_cost, &mut self.dp_how); // how：2 = 残す、3 = 消す
        g.clear();
        g.resize((np + 1) * w, INF);
        how.clear();
        how.resize((np + 1) * w, 0);
        g[at(np, dd)] = 0;
        for q in (0..np).rev() {
            for d in q.saturating_sub(nq)..=dd.min(q) {
                let i = q - d;
                // y が尽きていたら x の文字はもう処理できない（A1 で捨てるのは候補 1）
                if i == ny || x[q] < y[i] {
                    continue;
                }
                let lowered = if x[q] > y[i] { 2 } else { 0 };
                let keep = if i < nq {
                    match g[at(q + 1, d)] {
                        INF => INF,
                        0 => if lowered > 0 { 1 } else { INF }, // A3 一発
                        s => s + 1 + lowered,
                    }
                } else {
                    INF
                };
                let del = if d < dd {
                    match g[at(q + 1, d + 1)] {
                        INF => INF,
                        0 => if lowered == 0 { 1 } else { 3 }, // A2 一発 / A3＋A2
                        s => s + 3 + lowered,
                    }
                } else {
                    INF
                };
                if keep <= del && keep < INF {
                    (g[at(q, d)], how[at(q, d)]) = (keep, 2);
                } else if del < INF {
                    (g[at(q, d)], how[at(q, d)]) = (del, 3);
                }
            }
        }
        if g[at(0, 0)] == INF {
            return None;
        }
        let mut path = Vec::new();
        let (mut q, mut d) = (0, 0);
        while q < np {
            let h = how[at(q, d)];
            path.push((q, q - d, h));
            if h == 3 {
                d += 1;
            }
            q += 1;
        }
        Some((g[at(0, 0)] as u128, path))
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

    /// 元の A ⊢ B の証明（計画してから組み立てる）。
    pub fn prove_root(&mut self) -> usize {
        let (a, b) = ((0, self.left.len()), (0, self.right.len()));
        let planned = prove_with(&mut Planner { pr: self }, a, b).size;
        let id = prove_with(&mut Assembler { pr: self }, a, b);
        debug_assert_eq!(self.b.tree_size(id), planned, "計画した大きさと実際の大きさが違う");
        id
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

/// 部分目標の作り方（計画段階で選び、組み立て段階で従う）。
#[derive(Clone)]
enum Choice {
    /// Lemma 4.5 / Thm 3.17 に沿った構成
    Main,
    /// 局所断片の候補 1（A1 で尾を捨てて全部残す）
    KeepAll,
    /// 局所断片の候補 2（共通の尾から。外側からの手の列）
    Dp(Vec<(usize, usize, u8)>),
}

/// 計画：木の大きさと作り方。
struct Plan {
    size: u128,
    choice: Choice,
}

/// 構成のコードを「大きさだけ計算する（計画）」と「ノードを作る（組み立て）」の
/// 両方で使うための抽象。規則の部品と、部分目標の呼び出しを提供する。
///
/// 【Rust メモ】`type P` は関連型。計画では [`Virt`]（大きさと判断）、組み立てでは
/// ノード番号 `usize` になる。下の `prove_with` などは `S: Sink<L>` について
/// ジェネリックなので、同じコードが 2 通りにコンパイルされる。
trait Sink<L: Letter> {
    type P;
    fn pr(&mut self) -> &mut Prover<L>;
    fn axiom(&mut self, rule: WcRule, l: &[L], r: &[L]) -> Self::P;
    fn cut(&mut self, p: Self::P, q: Self::P) -> Self::P;
    fn nec(&mut self, g: &L, p: Self::P) -> Self::P;
    fn r3(&mut self, p: Self::P, q: Self::P) -> Self::P;
    fn lower(&mut self, p: Self::P, mu: &L) -> Self::P;
    fn prefix(&mut self, full: &[L], k: usize) -> Self::P;
    fn suffix(&mut self, v: &[L], i: usize) -> Self::P;
    fn identity(&mut self, a: &[L]) -> Self::P;
    /// 部分目標 A ⊢ B（Lemma 4.5 で分解する場合）。メモと候補の選択はここで。
    fn goal(&mut self, a: Seg, b: Seg) -> Self::P;
    /// 部分目標 v ⊢ μw。
    fn goal_lt(&mut self, mu: &L, w: Seg, v: Seg) -> Self::P;
}

fn bufs<L: Letter>(pr: &Prover<L>) -> (Rc<[L]>, Rc<[L]>) {
    (Rc::clone(&pr.left), Rc::clone(&pr.right))
}

/// A ⊢ B の証明（A は左辺側、B は右辺側の区間。RC で成り立つことが前提）。
/// 恒等式・A1・prove_lt への委譲を先に片づけ、残りを [`Sink::goal`] に回す。
fn prove_with<L: Letter, S: Sink<L>>(s: &mut S, a: Seg, b: Seg) -> S::P {
    let (left, right) = bufs(s.pr());
    let (xa, xb) = (&left[a.0..a.1], &right[b.0..b.1]);
    if xa == xb {
        return s.identity(xa);
    }
    let Some(alpha) = xb.first() else {
        return s.axiom(WcRule::A1, xa, &[]);
    };
    let ka = xa.iter().position(|x| x < alpha).unwrap_or(xa.len());
    let kb = xb[1..].iter().position(|x| x < alpha).unwrap_or(xb.len() - 1);
    if ka == xa.len() && kb == xb.len() - 1 {
        return s.goal_lt(alpha, (b.0 + 1, b.1), a); // A, B₀ ∈ W_α
    }
    s.goal(a, b)
}

/// Lemma 4.5 の分解（rA か rB が ⊤ でない）。
fn lemma45<L: Letter, S: Sink<L>>(s: &mut S, a: Seg, b: Seg) -> S::P {
    let (left, right) = bufs(s.pr());
    let (xa, xb) = (&left[a.0..a.1], &right[b.0..b.1]);
    let alpha = &xb[0];
    let ka = xa.iter().position(|x| x < alpha).unwrap_or(xa.len());
    let kb = xb[1..].iter().position(|x| x < alpha).unwrap_or(xb.len() - 1);
    if kb < xb.len() - 1 {
        // A ⊢ α hB（独立の目標）と A ⊢ rB を R3 で
        let p1 = prove_with(s, a, (b.0, b.0 + 1 + kb));
        let p2 = prove_with(s, a, (b.0 + 1 + kb, b.1));
        s.r3(p1, p2)
    } else {
        // rB = ⊤, rA ≠ ⊤：A ⊢ hA ⊢ α hB
        let pre = s.prefix(xa, ka);
        let p1 = prove_with(s, (a.0, a.0 + ka), b);
        s.cut(pre, p1)
    }
}

/// v ⊢ μw の構成（w は右辺側、v は左辺側の区間。文字はすべて μ 以上）。
fn lt_main<L: Letter, S: Sink<L>>(s: &mut S, mu: &L, w: Seg, v: Seg) -> S::P {
    let (left, right) = bufs(s.pr());
    let (xw, xv) = (&right[w.0..w.1], &left[v.0..v.1]);
    if xw.is_empty() {
        // v ⊢ γ（γ は v の先頭）から A3 で v ⊢ μ
        let p = s.prefix(xv, 1);
        return s.lower(p, mu);
    }
    let lambda = min_of(xw, xv);
    if lambda > *mu {
        let p = s.goal_lt(&lambda, w, v); // v ⊢ λw
        return s.lower(p, mu);
    }
    thm317(s, mu, w, v)
}

/// λ = μ のとき：Thm 3.17 の分岐 (a)/(b) に沿って v ⊢ μw を組み立てる。
fn thm317<L: Letter, S: Sink<L>>(s: &mut S, mu: &L, w: Seg, v: Seg) -> S::P {
    let (left, right) = bufs(s.pr());
    let (xw, xv) = (&right[w.0..w.1], &left[v.0..v.1]);
    let target = cons(mu.clone(), xw);
    // w = h(w) μ b(w)、v = h(v) μ b(v)（μ が無ければ b は ⊤）
    let iw = xw.iter().position(|x| x == mu);
    let iv = xv.iter().position(|x| x == mu);
    let hw = (w.0, w.0 + iw.unwrap_or(xw.len()));
    let bw = iw.map_or((w.1, w.1), |i| (w.0 + i + 1, w.1));
    let hv = (v.0, v.0 + iv.unwrap_or(xv.len()));
    let bv = iv.map_or((v.1, v.1), |i| (v.0 + i + 1, v.1));
    let cmp = &mut s.pr().cmp;
    let (nw, nbv) = (cmp.node_w(w.0, w.1), cmp.node_v(bv.0, bv.1));
    if cmp.le(nw, nbv) {
        // (a) w ⊴ b(v)。v = h(v) μ b(v) なので v ⊢ μ b(v)
        let strict = s.pr().cmp.lt(nw, nbv);
        let sfx = s.suffix(xv, hv.1 - hv.0);
        if strict {
            let q = s.goal_lt(mu, w, bv); // b(v) ⊢ μw
            let n = s.nec(mu, q); // μ b(v) ⊢ μμw
            let a2 = s.axiom(WcRule::A2, &cons(mu.clone(), &target), &target);
            let c = s.cut(sfx, n);
            s.cut(c, a2)
        } else {
            let q = prove_with(s, bv, w); // b(v) ⊢ w（同値）
            let n = s.nec(mu, q); // μ b(v) ⊢ μw
            s.cut(sfx, n)
        }
    } else if iw.is_none() {
        // (b) で μ ∉ w：v ⊢ h(v) ⊢ μ' w ⊢ μw
        let mu2 = min_of(xw, &left[hv.0..hv.1]);
        let p1 = s.goal_lt(&mu2, w, hv);
        let pre = s.prefix(xv, hv.1 - hv.0);
        let c = s.cut(pre, p1);
        s.lower(c, mu)
    } else {
        // (b) で w = h(w) μ b(w)
        let (shw, shv) = (&right[hw.0..hw.1], &left[hv.0..hv.1]);
        let mu2 = if shw.is_empty() { shv[0].clone() } else { min_of(shw, shv) };
        let p1 = s.goal_lt(&mu2, hw, hv); // h(v) ⊢ μ' h(w)
        let pre = s.prefix(xv, hv.1 - hv.0); // v ⊢ h(v)
        let c = s.cut(pre, p1); // v ⊢ μ' h(w)
        let p2 = s.goal_lt(mu, bw, v); // v ⊢ μ b(w)
        let r = s.r3(c, p2); // v ⊢ μ' h(w) μ b(w)
        s.lower(r, mu) // v ⊢ μ h(w) μ b(w) = μw
    }
}

/// 計画段階の「証明」：木の大きさと判断だけ（ノードは作らない）。
struct Virt<L> {
    size: u128,
    lhs: Rc<[L]>,
    rhs: Rc<[L]>,
}

impl<L: Letter> Virt<L> {
    fn new(size: u128, lhs: &[L], rhs: &[L]) -> Self {
        Virt { size, lhs: lhs.into(), rhs: rhs.into() }
    }
    fn is_identity(&self) -> bool {
        self.lhs == self.rhs
    }
}

/// 計画段階：大きさを数えるだけの [`Sink`]。数え方は [`Prover`] の部品と同じ
/// （恒等式との Cut を省く、など）。
struct Planner<'a, L> {
    pr: &'a mut Prover<L>,
}

impl<L: Letter> Sink<L> for Planner<'_, L> {
    type P = Virt<L>;

    fn pr(&mut self) -> &mut Prover<L> {
        self.pr
    }
    fn axiom(&mut self, _rule: WcRule, l: &[L], r: &[L]) -> Virt<L> {
        Virt::new(1, l, r)
    }
    fn cut(&mut self, p: Virt<L>, q: Virt<L>) -> Virt<L> {
        debug_assert!(p.rhs == q.lhs);
        if p.is_identity() {
            return q;
        }
        if q.is_identity() {
            return p;
        }
        Virt { size: p.size.saturating_add(q.size).saturating_add(1), lhs: p.lhs, rhs: q.rhs }
    }
    fn nec(&mut self, g: &L, p: Virt<L>) -> Virt<L> {
        Virt::new(p.size.saturating_add(1), &cons(g.clone(), &p.lhs), &cons(g.clone(), &p.rhs))
    }
    fn r3(&mut self, p: Virt<L>, q: Virt<L>) -> Virt<L> {
        let mut rhs = p.rhs.to_vec();
        rhs.extend_from_slice(&q.rhs);
        Virt { size: p.size.saturating_add(q.size).saturating_add(1), lhs: p.lhs, rhs: rhs.into() }
    }
    fn lower(&mut self, p: Virt<L>, mu: &L) -> Virt<L> {
        if p.rhs[0] == *mu {
            return p;
        }
        let a3 = Virt::new(1, &p.rhs, &cons(mu.clone(), &p.rhs[1..]));
        self.cut(p, a3)
    }
    fn prefix(&mut self, full: &[L], k: usize) -> Virt<L> {
        if k == full.len() {
            return self.identity(full);
        }
        Virt::new(k as u128 + 1, full, &full[..k])
    }
    fn suffix(&mut self, v: &[L], i: usize) -> Virt<L> {
        if i == 0 {
            return self.identity(v);
        }
        Virt::new(3 + 5 * (i as u128 - 1), v, &v[i..])
    }
    fn identity(&mut self, a: &[L]) -> Virt<L> {
        Virt::new(a.len() as u128 + 1, a, a)
    }
    fn goal(&mut self, a: Seg, b: Seg) -> Virt<L> {
        let (left, right) = bufs(self.pr);
        let (xa, xb) = (&left[a.0..a.1], &right[b.0..b.1]);
        let key = WSeq::new(xa, xb);
        if let Some(p) = self.pr.plans.get(&key) {
            return Virt::new(p.size, xa, xb);
        }
        debug_assert!(rc_holds(xa, xb), "前提違反: {:?} ⊢ {:?}", xa, xb);
        let main = lemma45(self, a, b).size;
        let plan = match self.pr.local_cost(xa, xb, main) {
            Some((size, choice)) => Plan { size, choice },
            None => Plan { size: main, choice: Choice::Main },
        };
        let size = plan.size;
        self.pr.plans.insert(key, plan);
        Virt::new(size, xa, xb)
    }
    fn goal_lt(&mut self, mu: &L, w: Seg, v: Seg) -> Virt<L> {
        let (left, right) = bufs(self.pr);
        let (xw, xv) = (&right[w.0..w.1], &left[v.0..v.1]);
        let target = cons(mu.clone(), xw);
        let key = WSeq::new(xv, &target);
        if let Some(p) = self.pr.plans.get(&key) {
            return Virt::new(p.size, xv, &target);
        }
        debug_assert!(rc_holds(xv, &target), "前提違反: {:?} ⊢ {:?}", xv, target);
        let main = lt_main(self, mu, w, v).size;
        let plan = match self.pr.local_cost(xv, &target, main) {
            Some((size, choice)) => Plan { size, choice },
            None => Plan { size: main, choice: Choice::Main },
        };
        let size = plan.size;
        self.pr.plans.insert(key, plan);
        Virt::new(size, xv, &target)
    }
}

/// 組み立て段階：計画に従ってノードを作る [`Sink`]。
struct Assembler<'a, L> {
    pr: &'a mut Prover<L>,
}

impl<L: Letter> Assembler<'_, L> {
    /// 計画済みの部分目標 `key`（x ⊢ y）を、選んだ作り方 `main` か局所断片で作る。
    fn assemble(&mut self, key: WSeq<L>, main: impl FnOnce(&mut Self) -> usize) -> usize {
        if let Some(&id) = self.pr.built.get(&key) {
            return id;
        }
        let plan = self.pr.plans.get(&key).expect("組み立てる目標は計画済みのはず");
        let (size, choice) = (plan.size, plan.choice.clone());
        let (x, y) = (key.lhs.letters(), key.rhs.letters());
        let id = match &choice {
            Choice::Main => main(self),
            Choice::KeepAll => self.pr.build_keep_all(x, y),
            Choice::Dp(path) => self.pr.build_plan(x, y, path),
        };
        debug_assert_eq!(self.pr.b.tree_size(id), size, "{key}: 計画と実際の大きさが違う");
        self.pr.built.insert(key, id);
        id
    }
}

impl<L: Letter> Sink<L> for Assembler<'_, L> {
    type P = usize;

    fn pr(&mut self) -> &mut Prover<L> {
        self.pr
    }
    fn axiom(&mut self, rule: WcRule, l: &[L], r: &[L]) -> usize {
        self.pr.axiom(rule, l, r)
    }
    fn cut(&mut self, p: usize, q: usize) -> usize {
        self.pr.cut(p, q)
    }
    fn nec(&mut self, g: &L, p: usize) -> usize {
        self.pr.nec(g, p)
    }
    fn r3(&mut self, p: usize, q: usize) -> usize {
        self.pr.r3(p, q)
    }
    fn lower(&mut self, p: usize, mu: &L) -> usize {
        self.pr.lower(p, mu)
    }
    fn prefix(&mut self, full: &[L], k: usize) -> usize {
        self.pr.prefix(full, k)
    }
    fn suffix(&mut self, v: &[L], i: usize) -> usize {
        self.pr.suffix(v, i)
    }
    fn identity(&mut self, a: &[L]) -> usize {
        self.pr.identity(a)
    }
    fn goal(&mut self, a: Seg, b: Seg) -> usize {
        let (left, right) = bufs(self.pr);
        let key = WSeq::new(&left[a.0..a.1], &right[b.0..b.1]);
        self.assemble(key, |s| lemma45(s, a, b))
    }
    fn goal_lt(&mut self, mu: &L, w: Seg, v: Seg) -> usize {
        let (left, right) = bufs(self.pr);
        let key = WSeq::new(&left[v.0..v.1], &cons(mu.clone(), &right[w.0..w.1]));
        let mu = mu.clone();
        self.assemble(key, move |s| lt_main(s, &mu, w, v))
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
