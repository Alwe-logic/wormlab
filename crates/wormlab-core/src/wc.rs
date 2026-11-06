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
//!    r か r' が空でなければ（論文の Lemma 4.5 の分解）
//!    h ⊢ αh' と A ⊢ r' を再帰的に証明し、A ⊢ h（先頭部分の補題）との
//!    Cut と R3 で A ⊢ αh'r' を組み立てる。
//! 2. A, B ∈ W_α なら `prove_lt(α, B, A)`：Thm 3.17 の分岐 (a)/(b) に
//!    従い、接尾部分の補題（XαY ⊢ αY）・Nec・A2・A3・R3 で組み立てる。
//!    最小の文字 λ が α より大きいときは、まず A ⊢ λB を示して A3 で下げる。
//!
//! 部分証明は判断ごとにメモ化して共有するので、証明は DAG になる。

use crate::headbody::{HeadBody, head_body};
use crate::letter::Letter;
use crate::proof::{self, Builder, Calculus, Proof};
use crate::rc;
use crate::spf::Spf;
use crate::worm::Worm;
use serde::Serialize;
use std::collections::HashMap;
use std::fmt;
use std::marker::PhantomData;

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

/// WC の証明を組み立てる。
pub struct Prover<L = u32> {
    b: Builder<WSeq<L>, WcRule>,
    hb: HeadBody<L>,
}

impl<L: Letter> Default for Prover<L> {
    fn default() -> Self {
        Prover { b: Builder::new(), hb: HeadBody::new() }
    }
}

impl<L: Letter> Prover<L> {
    pub fn new() -> Self {
        Self::default()
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

    // ---------------- 補題 ----------------

    /// 先頭部分の補題（論文 Lemma 3.3）：full ⊢ full[..k]
    fn prefix(&mut self, full: &[L], k: usize) -> usize {
        if let Some(id) = self.b.lookup(&WSeq::new(full, &full[..k])) {
            return id;
        }
        if k == 0 {
            return self.axiom(WcRule::A1, full, &[]);
        }
        let p = self.prefix(&full[1..], k - 1);
        self.nec(&full[0], p)
    }

    /// 恒等式 A ⊢ A（論文 Cor. 3.4）
    pub fn identity(&mut self, a: &[L]) -> usize {
        self.prefix(a, a.len())
    }

    /// 接尾部分の補題（論文 Lemma 3.5）：v = X μ Y（X の文字は μ より大）のとき v ⊢ μY。
    /// `i` は v[i] = μ となる位置。
    fn suffix(&mut self, v: &[L], i: usize) -> usize {
        if let Some(id) = self.b.lookup(&WSeq::new(v, &v[i..])) {
            return id;
        }
        if i == 0 {
            return self.identity(v);
        }
        let mu = &v[i];
        let p = self.suffix(&v[1..], i - 1); // v[1..] ⊢ μY
        let n = self.nec(&v[0], p); // v ⊢ γμY
        let tail = &v[i..]; // μY
        let a3 = self.axiom(WcRule::A3, &cons(v[0].clone(), tail), &cons(mu.clone(), tail)); // γμY ⊢ μμY
        let a2 = self.axiom(WcRule::A2, &cons(mu.clone(), tail), tail); // μμY ⊢ μY
        let c = self.cut(n, a3);
        self.cut(c, a2)
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

    // ---------------- 本体 ----------------

    /// A ⊢ B の証明（RC で成り立つことが前提）。
    pub fn prove(&mut self, a: &[L], b: &[L]) -> usize {
        debug_assert!(rc_holds(a, b), "前提違反: {:?} ⊢ {:?}", a, b);
        if let Some(id) = self.b.lookup(&WSeq::new(a, b)) {
            return id;
        }
        let Some((alpha, b0)) = b.split_first() else {
            return self.axiom(WcRule::A1, a, &[]);
        };
        // A = hA rA, b0 = hB rB（h は文字が α 以上の最長の先頭部分）
        let ka = a.iter().position(|x| x < alpha).unwrap_or(a.len());
        let kb = b0.iter().position(|x| x < alpha).unwrap_or(b0.len());
        let (h_a, r_a) = a.split_at(ka);
        let (h_b, r_b) = b0.split_at(kb);
        if r_a.is_empty() && r_b.is_empty() {
            return self.prove_lt(alpha, b0, a);
        }
        // Lemma 4.5 の分解
        let p1 = self.prove(h_a, &cons(alpha.clone(), h_b)); // hA ⊢ α hB
        let pre = self.prefix(a, ka); // A ⊢ hA
        let c = self.cut(pre, p1); // A ⊢ α hB
        if r_b.is_empty() {
            return c;
        }
        let p2 = self.prove(a, r_b); // A ⊢ rB（rB の先頭は α 未満）
        self.r3(c, p2) // A ⊢ α hB rB
    }

    /// v ⊢ μw の証明（v, w の文字はすべて μ 以上、RC で成り立つことが前提）。
    fn prove_lt(&mut self, mu: &L, w: &[L], v: &[L]) -> usize {
        let goal = cons(mu.clone(), w);
        debug_assert!(rc_holds(v, &goal), "前提違反: {:?} ⊢ {:?}", v, goal);
        if let Some(id) = self.b.lookup(&WSeq::new(v, &goal)) {
            return id;
        }
        if w.is_empty() {
            // v ⊢ γ（γ は v の先頭）から A3 で v ⊢ μ
            let p = self.prefix(v, 1);
            return self.lower(p, mu);
        }
        let lambda = min_of(w, v);
        if lambda > *mu {
            let p = self.prove_lt(&lambda, w, v); // v ⊢ λw
            return self.lower(p, mu);
        }
        // λ = μ：Thm 3.17 の分岐
        let (hw, bw) = head_body(w, mu);
        let (hv, bv) = head_body(v, mu);
        if self.hb.le(w, bv) {
            // (a) w ⊴ b(v)。v = h(v) μ b(v) なので v ⊢ μ b(v)
            let i = hv.len();
            let s = self.suffix(v, i);
            if self.hb.lt(w, bv) {
                let q = self.prove_lt(mu, w, bv); // b(v) ⊢ μw
                let n = self.nec(mu, q); // μ b(v) ⊢ μμw
                let a2 = self.axiom(WcRule::A2, &cons(mu.clone(), &goal), &goal);
                let c = self.cut(s, n);
                self.cut(c, a2)
            } else {
                let q = self.prove(bv, w); // b(v) ⊢ w（同値）
                let n = self.nec(mu, q); // μ b(v) ⊢ μw
                self.cut(s, n)
            }
        } else if bw.is_empty() && hw.len() == w.len() {
            // (b) で μ ∉ w：v ⊢ h(v) ⊢ μ' w ⊢ μw
            let mu2 = min_of(w, hv);
            let p1 = self.prove_lt(&mu2, w, hv);
            let pre = self.prefix(v, hv.len());
            let c = self.cut(pre, p1);
            self.lower(c, mu)
        } else {
            // (b) で w = h(w) μ b(w)
            let mu2 = if hw.is_empty() { hv[0].clone() } else { min_of(hw, hv) };
            let p1 = self.prove_lt(&mu2, hw, hv); // h(v) ⊢ μ' h(w)
            let pre = self.prefix(v, hv.len()); // v ⊢ h(v)
            let c = self.cut(pre, p1); // v ⊢ μ' h(w)
            let p2 = self.prove_lt(mu, bw, v); // v ⊢ μ b(w)
            let r = self.r3(c, p2); // v ⊢ μ' h(w) μ b(w)
            self.lower(r, mu) // v ⊢ μ h(w) μ b(w) = μw
        }
    }

    /// 組み立てた DAG から `root` の証明を取り出す。
    pub fn finish(self, root: usize) -> WcProof<L> {
        self.b.finish(root)
    }
}

/// worm シーケント A ⊢ B の構文的な判定器（RC のモデルを使わない）。
///
/// `prove` と同じ分解をたどり、真偽だけを返す：
/// - B = ⊤ なら真。
/// - B = αB₀ とし、A = hA rA, B₀ = hB rB（h は文字が α 以上の最長の先頭部分）。
///   - rA, rB がともに空なら、head/body 比較（Thm 3.17）で B₀ ◁ A か。
///   - そうでなければ hA ⊢ αhB かつ A ⊢ rB（Lemma 4.5 の分解）。
///
/// 現れる部分問題は限られていて、メモ化しているので多項式時間で終わる
/// （`algorithms.md` §1 参照）。正しさは Lemma 4.5 と Thm 3.17 に依拠する。
/// テストでは RC と突き合わせている。
pub struct Decider<L = u32> {
    hb: HeadBody<L>,
    memo: HashMap<(Vec<L>, Vec<L>), bool>,
}

impl<L: Letter> Default for Decider<L> {
    fn default() -> Self {
        Decider { hb: HeadBody::new(), memo: HashMap::new() }
    }
}

impl<L: Letter> Decider<L> {
    pub fn new() -> Self {
        Self::default()
    }

    /// A ⊢ B か。
    pub fn decide(&mut self, a: &[L], b: &[L]) -> bool {
        let Some((alpha, b0)) = b.split_first() else {
            return true;
        };
        let key = (a.to_vec(), b.to_vec());
        if let Some(&ans) = self.memo.get(&key) {
            return ans;
        }
        let ka = a.iter().position(|x| x < alpha).unwrap_or(a.len());
        let kb = b0.iter().position(|x| x < alpha).unwrap_or(b0.len());
        let (h_a, r_a) = a.split_at(ka);
        let (h_b, r_b) = b0.split_at(kb);
        let ans = if r_a.is_empty() && r_b.is_empty() {
            self.hb.lt(b0, a)
        } else {
            self.decide(h_a, &cons(alpha.clone(), h_b)) && self.decide(a, r_b)
        };
        self.memo.insert(key, ans);
        ans
    }
}

/// WC（＝ RC ＝ GLP）で worm シーケント A ⊢ B が成り立つか（構文的判定）。
pub fn decide<L: Letter>(a: &Worm<L>, b: &Worm<L>) -> bool {
    Decider::new().decide(a.letters(), b.letters())
}

/// A ⊢ B の WC 証明を作る。成り立たなければ `Err`。
pub fn prove<L: Letter>(a: &Worm<L>, b: &Worm<L>) -> Result<WcProof<L>, String> {
    if !decide(a, b) {
        return Err(format!("{a} ⊢ {b} は成り立たない（WC でも RC でも証明できない）"));
    }
    let mut p = Prover::new();
    let root = p.prove(a.letters(), b.letters());
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
