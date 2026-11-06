//! Reflection Calculus の**導出**（証明）を作り、検査する。
//!
//! [`crate::rc`] は閉包モデルで「成り立つか」を判定する。ここでは、成り立つ
//! シーケント A ⊢ B に対して、RC の規則だけからなる導出を実際に組み立てる。
//! 変数と ∧ を含む一般の強正値式に対応し、モダリティは自然数でも順序数でもよい。
//!
//! # RC の規則（Beklemishev 2014 の形）
//! ```text
//! Id    A ⊢ A                 Top   A ⊢ ⊤
//! ∧E1   A ∧ B ⊢ A             ∧E2   A ∧ B ⊢ B
//! ∧I    A ⊢ B, A ⊢ C ⇒ A ⊢ B ∧ C
//! Cut   A ⊢ B, B ⊢ C ⇒ A ⊢ C
//! Nec   A ⊢ B ⇒ ⟨n⟩A ⊢ ⟨n⟩B
//! 4     ⟨n⟩⟨n⟩A ⊢ ⟨n⟩A
//! Mono  ⟨n⟩A ⊢ ⟨m⟩A                         （n > m）
//! J     ⟨n⟩A ∧ ⟨m⟩B ⊢ ⟨n⟩(A ∧ ⟨m⟩B)          （n > m）
//! ```
//!
//! # 導出の作り方（algorithms.md §1b の構成）
//! 1. A を構文木として見る（各 ⟨k⟩ の位置が 1 つのノード、根が A 全体）。
//! 2. B の部分式 ⟨m⟩β ∈ Sub(B) について、各ノード x で成り立つものを、次の 2 つの
//!    局所規則の最小不動点として求める（[`crate::rc`] の判定法 2 と同じ計算。O(|A|·|B|)）：
//!    - 辺：木の辺 x →k y（k ≥ m）で、y で β か ⟨m⟩β が成り立てば x で ⟨m⟩β
//!      （導出は Nec・Mono・4）
//!    - 押し下げ：木の辺 t →k x（k > m）で、t で ⟨m⟩β が成り立てば x でも ⟨m⟩β
//!      （導出は t での J）
//!
//!    ∧ は両方成り立てば成り立つ。変数は A に書いてあるものだけ。
//!    ⟨m⟩β を結論とする規則の前提は ⟨m⟩β と β だけなので、目標は Sub(B) で足りる。
//!    作業リストを先着順で回し、各事実を最初に得た規則を理由として残す。
//! 3. 根で B が成り立たなければ導出は無い（閉包モデルの判定と一致することをテストで確認）。
//! 4. 成り立つなら、B に必要な事実だけを、求めた順に 1 つずつ A のノードに「∧ ⟨m⟩β」として
//!    書き足していく：A ⊢ A¹ ⊢ A² ⊢ … ⊢ A*。各ステップは局所的な導出を Nec と ∧ の
//!    組み直しで文脈全体に持ち上げたもの。最後に A* から B を取り出す。
//!
//! 導出は DAG として持ち、同じ部分導出は共有する。正しさは検査器 [`check`] が保証する。

use crate::letter::Letter;
use crate::proof::{self, Builder, Calculus, Proof};
use crate::rc::{self, ATree, Facts, SubDag, SubNode, Why};
use crate::spf::Spf;
use serde::Serialize;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::marker::PhantomData;

// ----------------------------------------------------------------------
// 判断・規則・検査器
// ----------------------------------------------------------------------

/// シーケント A ⊢ B（RC の判断）。
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize)]
#[serde(bound(serialize = "L: Letter"))]
pub struct RSeq<L = u32> {
    pub lhs: Spf<L>,
    pub rhs: Spf<L>,
}

impl<L: Letter> fmt::Display for RSeq<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ⊢ {}", self.lhs, self.rhs)
    }
}

/// RC の規則。
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize)]
pub enum RcRule {
    Id,
    Top,
    AndE1,
    AndE2,
    AndI,
    Cut,
    Nec,
    Four,
    Mono,
    J,
}

impl fmt::Display for RcRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            RcRule::Id => "Id",
            RcRule::Top => "⊤",
            RcRule::AndE1 => "∧E1",
            RcRule::AndE2 => "∧E2",
            RcRule::AndI => "∧I",
            RcRule::Cut => "Cut",
            RcRule::Nec => "Nec",
            RcRule::Four => "4",
            RcRule::Mono => "Mono",
            RcRule::J => "J",
        };
        write!(f, "{s}")
    }
}

/// RC という証明体系（検査の規則だけを定める）。
pub struct Rc<L = u32>(PhantomData<L>);

pub type RcProof<L = u32> = Proof<RSeq<L>, RcRule>;

impl<L: Letter> Calculus for Rc<L> {
    type Judgment = RSeq<L>;
    type Rule = RcRule;

    fn check_step(rule: &RcRule, prem: &[&RSeq<L>], c: &RSeq<L>) -> Result<(), String> {
        use Spf::{And, Dia, Top};
        let ok = match (rule, prem) {
            (RcRule::Id, []) => c.lhs == c.rhs,
            (RcRule::Top, []) => c.rhs == Top,
            (RcRule::AndE1, []) => matches!(&c.lhs, And(a, _) if **a == c.rhs),
            (RcRule::AndE2, []) => matches!(&c.lhs, And(_, b) if **b == c.rhs),
            (RcRule::AndI, [p, q]) => {
                p.lhs == c.lhs && q.lhs == c.lhs && c.rhs == Spf::and(p.rhs.clone(), q.rhs.clone())
            }
            (RcRule::Cut, [p, q]) => p.lhs == c.lhs && p.rhs == q.lhs && q.rhs == c.rhs,
            (RcRule::Nec, [p]) => match (&c.lhs, &c.rhs) {
                (Dia(n, a), Dia(m, b)) => n == m && **a == p.lhs && **b == p.rhs,
                _ => false,
            },
            (RcRule::Four, []) => match (&c.lhs, &c.rhs) {
                (Dia(n, inner), Dia(m, b)) => {
                    matches!(&**inner, Dia(n2, a) if n2 == n && a == b) && n == m
                }
                _ => false,
            },
            (RcRule::Mono, []) => match (&c.lhs, &c.rhs) {
                (Dia(n, a), Dia(m, b)) => n > m && a == b,
                _ => false,
            },
            (RcRule::J, []) => match (&c.lhs, &c.rhs) {
                (And(l, r), Dia(n2, inner)) => match (&**l, &**r, &**inner) {
                    (Dia(n, a), Dia(m, b), And(a2, rb)) => {
                        n > m && n == n2 && a == a2 && matches!(&**rb, Dia(m2, b2) if m2 == m && b2 == b)
                    }
                    _ => false,
                },
                _ => false,
            },
            _ => return Err("規則と前提の個数が合わない".to_string()),
        };
        if ok { Ok(()) } else { Err(format!("{rule} の形になっていない")) }
    }
}

/// 導出を検査し、結論を返す。
pub fn check<L: Letter>(p: &RcProof<L>) -> Result<&RSeq<L>, String> {
    proof::check::<Rc<L>>(p)
}

// ----------------------------------------------------------------------
// A の構文木
// ----------------------------------------------------------------------

struct TNode<L> {
    vars: Vec<String>,
    children: Vec<(L, usize)>,
    parent: Option<(usize, L)>,
    /// 導出の途中で書き足した事実 ⟨m⟩β
    extra: Vec<Spf<L>>,
}

/// 左に入れ子にした連言 ((l1 ∧ l2) ∧ l3) …。空なら ⊤。
fn conj<L: Letter>(leaves: Vec<Spf<L>>) -> Spf<L> {
    leaves.into_iter().reduce(Spf::and).unwrap_or(Spf::Top)
}

/// 導出を組み立てる道具。
pub struct Deriver<L = u32> {
    b: Builder<RSeq<L>, RcRule>,
    nodes: Vec<TNode<L>>,
}

impl<L: Letter> Deriver<L> {
    fn new(lhs: &Spf<L>) -> Self {
        let mut d = Deriver { b: Builder::new(), nodes: Vec::new() };
        d.nodes.push(TNode { vars: vec![], children: vec![], parent: None, extra: vec![] });
        d.build(lhs, 0);
        d
    }

    fn build(&mut self, a: &Spf<L>, x: usize) {
        match a {
            Spf::Top => {}
            Spf::Var(p) => self.nodes[x].vars.push(p.clone()),
            Spf::And(l, r) => {
                self.build(l, x);
                self.build(r, x);
            }
            Spf::Dia(k, b) => {
                let y = self.nodes.len();
                self.nodes.push(TNode { vars: vec![], children: vec![], parent: Some((x, k.clone())), extra: vec![] });
                self.nodes[x].children.push((k.clone(), y));
                self.build(b, y);
            }
        }
    }

    /// ノード x の現在の式（変数・子・書き足した事実の連言）。
    fn render(&self, x: usize) -> Spf<L> {
        let n = &self.nodes[x];
        let mut leaves: Vec<Spf<L>> = n.vars.iter().map(|v| Spf::Var(v.clone())).collect();
        leaves.extend(n.children.iter().map(|(k, y)| Spf::dia(k.clone(), self.render(*y))));
        leaves.extend(n.extra.iter().cloned());
        conj(leaves)
    }

    // ---------------- 事実の飽和（どの事実が成り立つか） ----------------

    /// 局所規則の最小不動点（[`rc`] の判定法 2）を、理由つきで求める。
    fn saturate(&self, rhs: &Spf<L>) -> (SubDag<L>, Facts) {
        let t = ATree {
            vars: self.nodes.iter().map(|n| n.vars.clone()).collect(),
            kids: self.nodes.iter().map(|n| n.children.clone()).collect(),
            parent: self.nodes.iter().map(|n| n.parent.clone()).collect(),
        };
        let d = SubDag::new(rhs);
        let f = rc::saturate(&t, &d, true);
        (d, f)
    }

    /// (x, 部分式 i) を導くのに必要な ⟨m⟩β の事実を `need` に集める。
    fn collect_needed(&self, d: &SubDag<L>, f: &Facts, x: usize, i: usize, need: &mut HashSet<(usize, usize)>) {
        match &d.node[i] {
            SubNode::Top | SubNode::Var(_) => {}
            SubNode::And(a, b) => {
                self.collect_needed(d, f, x, *a, need);
                self.collect_needed(d, f, x, *b, need);
            }
            SubNode::Dia(_, beta) => {
                if !need.insert((x, i)) {
                    return;
                }
                match f.why(x, i) {
                    Why::Edge { child, via_dia: true } => self.collect_needed(d, f, child, i, need),
                    Why::Edge { child, via_dia: false } => self.collect_needed(d, f, child, *beta, need),
                    Why::Push { parent } => self.collect_needed(d, f, parent, i, need),
                    Why::Base | Why::And => unreachable!("⟨m⟩β は辺か押し下げで得る"),
                }
            }
        }
    }

    /// 木の辺 parent →k child のラベル k。
    fn label(&self, child: usize) -> L {
        self.nodes[child].parent.as_ref().expect("根以外").1.clone()
    }

    // ---------------- 小さな導出の部品 ----------------

    fn axiom(&mut self, rule: RcRule, lhs: Spf<L>, rhs: Spf<L>) -> usize {
        self.b.add(rule, vec![], RSeq { lhs, rhs })
    }

    fn concl(&self, p: usize) -> RSeq<L> {
        self.b.conclusion(p).clone()
    }

    fn cut(&mut self, p: usize, q: usize) -> usize {
        let (cp, cq) = (self.concl(p), self.concl(q));
        debug_assert_eq!(cp.rhs, cq.lhs);
        if cp.lhs == cp.rhs {
            return q;
        }
        if cq.lhs == cq.rhs {
            return p;
        }
        self.b.add(RcRule::Cut, vec![p, q], RSeq { lhs: cp.lhs, rhs: cq.rhs })
    }

    fn and_i(&mut self, p: usize, q: usize) -> usize {
        let (cp, cq) = (self.concl(p), self.concl(q));
        self.b.add(RcRule::AndI, vec![p, q], RSeq { lhs: cp.lhs, rhs: Spf::and(cp.rhs, cq.rhs) })
    }

    fn nec(&mut self, k: &L, p: usize) -> usize {
        let c = self.concl(p);
        let seq = RSeq { lhs: Spf::dia(k.clone(), c.lhs), rhs: Spf::dia(k.clone(), c.rhs) };
        self.b.add(RcRule::Nec, vec![p], seq)
    }

    /// src の連言の葉 leaf を取り出す導出 src ⊢ leaf（∧E の連鎖。⟨k⟩ の中は再構成）。
    fn find_leaf(&mut self, src: &Spf<L>, leaf: &Spf<L>) -> Option<usize> {
        if src == leaf {
            return Some(self.axiom(RcRule::Id, src.clone(), src.clone()));
        }
        match (src, leaf) {
            (Spf::And(a, b), _) => {
                if let Some(p) = self.find_leaf(a, leaf) {
                    let e = self.axiom(RcRule::AndE1, src.clone(), (**a).clone());
                    return Some(self.cut(e, p));
                }
                let p = self.find_leaf(b, leaf)?;
                let e = self.axiom(RcRule::AndE2, src.clone(), (**b).clone());
                Some(self.cut(e, p))
            }
            (Spf::Dia(k, s), Spf::Dia(k2, t)) if k == k2 => {
                let inner = self.rebuild(s, t, &HashMap::new())?;
                Some(self.nec(k, inner))
            }
            _ => None,
        }
    }

    /// src ⊢ target。target の葉は、hints（src ⊢ 葉 の導出）か src から構造的に取り出す。
    fn rebuild(&mut self, src: &Spf<L>, target: &Spf<L>, hints: &HashMap<Spf<L>, usize>) -> Option<usize> {
        if let Some(&h) = hints.get(target) {
            return Some(h);
        }
        match target {
            Spf::Top => Some(self.axiom(RcRule::Top, src.clone(), Spf::Top)),
            Spf::And(a, b) => {
                let p = self.rebuild(src, a, hints)?;
                let q = self.rebuild(src, b, hints)?;
                Some(self.and_i(p, q))
            }
            _ => self.find_leaf(src, target),
        }
    }

    /// ノード x の現在の式 G から τ（x で成り立つ事実）を導く：G ⊢ τ。
    fn fact_proof(&mut self, x: usize, t: &Spf<L>) -> usize {
        let g = self.render(x);
        self.fact_from(&g, t)
    }

    fn fact_from(&mut self, g: &Spf<L>, t: &Spf<L>) -> usize {
        match t {
            Spf::Top => self.axiom(RcRule::Top, g.clone(), Spf::Top),
            Spf::And(a, b) => {
                let p = self.fact_from(g, a);
                let q = self.fact_from(g, b);
                self.and_i(p, q)
            }
            _ => self.find_leaf(g, t).expect("事実は葉として書き足してある"),
        }
    }

    // ---------------- 1 ステップ（事実を 1 つ書き足す） ----------------

    /// ノード z の式を G_z から G'_z に変えた導出 `local`（G_z ⊢ G'_z）を、根まで持ち上げる。
    /// `olds[i]` は z から根までの各ノードの変更前の式。
    fn lift(&mut self, z: usize, local: usize, olds: &[Spf<L>]) -> usize {
        let (mut cur, mut child, mut i) = (local, z, 0);
        while let Some((p, k)) = self.nodes[child].parent.clone() {
            let (child_old, p_old) = (olds[i].clone(), olds[i + 1].clone());
            let (child_new, p_new) = (self.render(child), self.render(p));
            let proj = self.find_leaf(&p_old, &Spf::dia(k.clone(), child_old)).expect("子は葉");
            let lifted = self.nec(&k, cur);
            let leaf_proof = self.cut(proj, lifted);
            let hints = HashMap::from([(Spf::dia(k, child_new), leaf_proof)]);
            cur = self.rebuild(&p_old, &p_new, &hints).expect("1 つの葉だけ変わる");
            child = p;
            i += 1;
        }
        cur
    }

    /// z から根までの式（変更前の記録用）。
    fn path_renders(&self, z: usize) -> Vec<Spf<L>> {
        let mut out = vec![self.render(z)];
        let mut x = z;
        while let Some((p, _)) = &self.nodes[x].parent {
            out.push(self.render(*p));
            x = *p;
        }
        out
    }

    /// 事実 (x, τ = ⟨m⟩β) を書き足すステップ：根の式の「前 ⊢ 後」の導出を返す。
    fn add_fact(&mut self, x: usize, t: &Spf<L>, why: Why) -> usize {
        let Spf::Dia(m, beta) = t else { unreachable!("事実は ⟨m⟩β の形") };
        match why {
            Why::Edge { child, via_dia } => {
                let k = &self.label(child);
                // G_x ⊢ ⟨k⟩G_y ⊢ ⟨k⟩β（または ⟨k⟩⟨m⟩β）⊢ ⟨m⟩β
                let gy = self.render(child);
                let py = if via_dia { self.fact_proof(child, t) } else { self.fact_proof(child, beta) };
                let olds = self.path_renders(x);
                let gx = olds[0].clone();
                let proj = self.find_leaf(&gx, &Spf::dia(k.clone(), gy)).expect("子は葉");
                let n = self.nec(k, py);
                let mut q = self.cut(proj, n);
                if via_dia {
                    if k > m {
                        let mono = self.axiom(RcRule::Mono, Spf::dia(k.clone(), t.clone()), Spf::dia(m.clone(), t.clone()));
                        q = self.cut(q, mono);
                    }
                    let four = self.axiom(RcRule::Four, Spf::dia(m.clone(), t.clone()), t.clone());
                    q = self.cut(q, four);
                } else if k > m {
                    let mono = self.axiom(RcRule::Mono, Spf::dia(k.clone(), (**beta).clone()), t.clone());
                    q = self.cut(q, mono);
                }
                self.nodes[x].extra.push(t.clone());
                let gx_new = self.render(x);
                let local = self.rebuild(&gx, &gx_new, &HashMap::from([(t.clone(), q)])).expect("葉が 1 つ増えるだけ");
                self.lift(x, local, &olds)
            }
            Why::Push { parent } => {
                let k = &self.label(x);
                // G_t ⊢ ⟨k⟩G_x ∧ ⟨m⟩β ⊢ ⟨k⟩(G_x ∧ ⟨m⟩β) ⊢ ⟨k⟩G'_x
                let olds = self.path_renders(parent);
                let (gt, gx) = (olds[0].clone(), self.render(x));
                let dia_gx = Spf::dia(k.clone(), gx.clone());
                let pa = self.find_leaf(&gt, &dia_gx).expect("子は葉");
                let pb = self.fact_from(&gt, t);
                let both = self.and_i(pa, pb);
                let j = self.axiom(RcRule::J, Spf::and(dia_gx, t.clone()), Spf::dia(k.clone(), Spf::and(gx.clone(), t.clone())));
                let r = self.cut(both, j);
                self.nodes[x].extra.push(t.clone());
                let gx_new = self.render(x);
                let inner = self.rebuild(&Spf::and(gx, t.clone()), &gx_new, &HashMap::new()).expect("並べ替えだけ");
                let n = self.nec(k, inner);
                let leaf_proof = self.cut(r, n);
                let gt_new = self.render(parent);
                let hints = HashMap::from([(Spf::dia(k.clone(), gx_new), leaf_proof)]);
                let local = self.rebuild(&gt, &gt_new, &hints).expect("1 つの葉だけ変わる");
                self.lift(parent, local, &olds)
            }
            Why::Base | Why::And => unreachable!("⟨m⟩β は辺か押し下げで得る"),
        }
    }
}

/// 導出の大きさなどの情報。
#[derive(Clone, Debug, Serialize)]
pub struct DeriveStats {
    /// 飽和で得た事実 ⟨m⟩β（⟨m⟩β ∈ Sub(B)）の数
    pub facts_total: usize,
    /// 導出に使った（書き足した）事実の数
    pub facts_used: usize,
}

/// RC で A ⊢ B の導出を作る。成り立たなければ `Err`。
pub fn derive<L: Letter>(lhs: &Spf<L>, rhs: &Spf<L>) -> Result<(RcProof<L>, DeriveStats), String> {
    let mut d = Deriver::new(lhs);
    let (sub, facts) = d.saturate(rhs);
    if !facts.holds(0, sub.root) {
        return Err(format!("RC ⊬ {lhs} ⊢ {rhs}"));
    }
    let mut need = HashSet::new();
    d.collect_needed(&sub, &facts, 0, sub.root, &mut need);

    // 書き足す前の状態から、必要な事実だけを得た順に書き足す
    let start = d.render(0);
    let mut proof = d.rebuild(lhs, &start, &HashMap::new()).expect("A ⊢ 並べ替えた A");
    let mut used = 0;
    for &(x, i) in &facts.order {
        if need.contains(&(x, i)) {
            let t = &sub.form[i];
            // すでに式の葉から構造的に取り出せる事実（例：子 ⟨m⟩β そのもの）は書き足さない
            let gx = d.render(x);
            if d.find_leaf(&gx, t).is_some() {
                continue;
            }
            let step = d.add_fact(x, t, facts.why(x, i));
            proof = d.cut(proof, step);
            used += 1;
        }
    }
    let end = d.render(0);
    let last = d.fact_from(&end, rhs);
    let root = d.cut(proof, last);
    let facts_total = facts.order.iter().filter(|&&(_, i)| matches!(sub.node[i], SubNode::Dia(..))).count();
    let stats = DeriveStats { facts_total, facts_used: used };
    Ok((d.b.finish(root), stats))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn proves(s: &str) -> RcProof {
        let (l, r) = s.split_once("⊢").unwrap();
        let (lhs, rhs): (Spf, Spf) = (l.parse().unwrap(), r.parse().unwrap());
        let (p, _) = derive(&lhs, &rhs).unwrap_or_else(|e| panic!("{e}"));
        let c = check(&p).unwrap_or_else(|e| panic!("{s}: {e}\n{p}"));
        assert_eq!(c, &RSeq { lhs, rhs });
        p
    }

    #[test]
    fn axioms_and_examples() {
        proves("p ⊢ p");
        proves("p ∧ q ⊢ q ∧ p");
        proves("<0><0>p ⊢ <0>p");
        proves("<2>p ⊢ <0>p");
        proves("<1>p ∧ <0>q ⊢ <1>(p ∧ <0>q)");
        proves("<2><1>p ∧ <0>q ⊢ <2>(<1>p ∧ <0>q)");
        proves("<2>p ⊢ <0><1>p");
        proves("<1>p ⊢ <1>(p ∧ <0>p)");
        proves("<2>(p ∧ <1>q) ∧ <0>r ⊢ <0>(<1>(p ∧ <0>r) ∧ <0>q)");
    }

    #[test]
    fn non_theorems_have_no_derivation() {
        for s in ["p ⊢ <0>p", "<0>p ⊢ <1>p", "<0>p ∧ <0>q ⊢ <0>(p ∧ q)", "<1>p ∧ <1>q ⊢ <1>(p ∧ <1>q)"] {
            let (l, r) = s.split_once("⊢").unwrap();
            assert!(derive::<u32>(&l.parse().unwrap(), &r.parse().unwrap()).is_err(), "{s}");
        }
    }

    #[test]
    fn checker_rejects_bad_steps() {
        let s = |x: &str| x.parse::<Spf>().unwrap();
        let bad = Proof {
            nodes: vec![proof::Node { rule: RcRule::Mono, premises: vec![], conclusion: RSeq { lhs: s("<0>p"), rhs: s("<1>p") } }],
            root: 0,
        };
        assert!(check(&bad).is_err());
        let bad_j = Proof {
            nodes: vec![proof::Node {
                rule: RcRule::J,
                premises: vec![],
                conclusion: RSeq { lhs: s("<1>p ∧ <1>q"), rhs: s("<1>(p ∧ <1>q)") },
            }],
            root: 0,
        };
        assert!(check(&bad_j).is_err());
    }
}
