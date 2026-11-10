//! BWC：括弧語だけの体系（Worm Calculus の Bracket Calculus 版）。
//!
//! 判断は括弧語どうしのシーケント a ⊢ b だけ（変数も ∧ もない）。括弧語 a = (a_1)…(a_k)
//! は worm (a_1)…(a_k)⊤ と読む。規則は WC（de Almeida Borges & Joosten, arXiv:1803.10543）と
//! 同じ形で、文字の大小（A3 の α > β、R3 の「B の文字はすべて α より大きい」）を、
//! 順序数ではなく**この体系自身の導出**で正当化する。文字 x, y の比較 y ◁ x は括弧語の
//! シーケント x ⊢ ()y なので、副条件もまた BWC の判断になり、体系が閉じる
//! （Bracket Calculus の R3・R4 と同じ考え方。BC との関係は bc.md §2）。
//!
//! # 規則
//! ```text
//! A1   a ⊢ ⊤
//! A2   (x)(x)c ⊢ (x)c
//! A3   y ≤ x ⇒ (x)c ⊢ (y)c                          副条件：x ⊢ ()y（y ◁ x）か x ⊢ y
//! Cut  a ⊢ b, b ⊢ c ⇒ a ⊢ c
//! Nec  a ⊢ b ⇒ (x)a ⊢ (x)b
//! R3   a ⊢ b, a ⊢ (x)c, b の各文字 y で x ◁ y ⇒ a ⊢ b(x)c    副条件：y ⊢ ()x
//! ```
//! WC の A3 は α > β（厳密）だけだが、ここでは正規形でない括弧語（同じ順序数を表す別の語）
//! も扱うので、副条件 x ⊢ y による「等しいか小さい」も許す（BC の ≤ と同じ）。
//! 証明 DAG では副条件の導出をふつうの前提として持つ：A3 は [副条件]、R3 は
//! [a ⊢ b, a ⊢ (x)c, 副条件…]（b の異なる文字ごとに 1 つ）。
//!
//! # 健全性と完全性
//! - 健全性：τ（文字 x を順序数 o*(x) に置き換える）で、各規則は WC の規則（または恒等式）に
//!   移る。副条件 x ⊢ ()y が導出できれば（帰納法の仮定で）τ の世界で y* <_0 x*、
//!   つまり o*(y) < o*(x)。x ⊢ y なら o*(y) ≤ o*(x)（worm で A ⊢ B なら o(B) ≤ o(A)）。
//!   よって BWC ⊢ a ⊢ b ⇒ RC ⊢ a^τ ⊢ b^τ ⟺ BC ⊢ a ⊢ b（BC の Thm 38）。
//! - 完全性（[`prove`] の構成）：文字を正規形にした worm で WC の証明を作り（[`wc::prove`]、
//!   文字は [`NfBracket`]）、A3・R3 の文字の比較を副条件として同じ方法で再帰的に導出する。
//!   副条件の括弧語は入れ子が浅くなるので止まる。正規形でない文字は A3（副条件 x ⊢ nf(x)）
//!   と Nec で書き換える。
//! - 判定 [`decide`]：文字を正規形にした worm で [`wc::decide`]（head/body。文字の比較は
//!   順序数を使わない括弧語の比較）。RC もモデルも順序数も使わない。

use crate::i18n::tr;
use crate::bracket::{Bracket, NfBracket};
use crate::latex::ToLatex;
use crate::proof::{self, Builder, Calculus, Proof};
use crate::wc::{self, WSeq, WcProof, WcRule};
use crate::worm::Worm;
use serde::Serialize;
use std::collections::HashSet;
use std::fmt;
use std::str::FromStr;

/// 括弧語どうしのシーケント a ⊢ b。
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize)]
pub struct BwSeq {
    pub lhs: Bracket,
    pub rhs: Bracket,
}

impl BwSeq {
    pub fn new(lhs: Bracket, rhs: Bracket) -> BwSeq {
        BwSeq { lhs, rhs }
    }

    /// 「b ◁ a」を表すシーケント a ⊢ ()b。
    pub fn lt(b: &Bracket, a: &Bracket) -> BwSeq {
        BwSeq::new(a.clone(), b.prepend(Bracket::top()))
    }
}

impl fmt::Display for BwSeq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ⊢ {}", self.lhs, self.rhs)
    }
}

impl ToLatex for BwSeq {
    fn to_latex(&self) -> String {
        format!("{} \\vdash {}", self.lhs.to_latex(), self.rhs.to_latex())
    }
}

/// `"a |- b"` または `"a ⊢ b"` を読む（⊤ は空、"⊤"、"T" のどれでもよい）。
impl FromStr for BwSeq {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (l, r) = s.split_once("⊢").or_else(|| s.split_once("|-")).ok_or(tr("'⊢' または '|-' が必要です", "expected '⊢' or '|-'"))?;
        let p = |x: &str| x.parse::<Bracket>().map_err(|e| e.to_string());
        Ok(BwSeq::new(p(l)?, p(r)?))
    }
}

/// BWC の規則。
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize)]
pub enum BwRule {
    A1,
    A2,
    A3,
    Cut,
    Nec,
    R3,
}

impl fmt::Display for BwRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            BwRule::A1 => "A1",
            BwRule::A2 => "A2",
            BwRule::A3 => "A3",
            BwRule::Cut => "Cut",
            BwRule::Nec => "Nec",
            BwRule::R3 => "R3",
        };
        write!(f, "{s}")
    }
}

impl ToLatex for BwRule {
    fn to_latex(&self) -> String {
        crate::latex::rule_name(&self.to_string())
    }
}

/// BWC という証明体系（検査の規則だけを定める）。
pub struct Bwc;

pub type BwProof = Proof<BwSeq, BwRule>;

/// 副条件 s が「y ◁ x」（x ⊢ ()y）の証拠か。
fn is_lt(s: &BwSeq, y: &Bracket, x: &Bracket) -> bool {
    s.lhs == *x && s.rhs == y.prepend(Bracket::top())
}

impl Calculus for Bwc {
    type Judgment = BwSeq;
    type Rule = BwRule;

    fn check_step(rule: &BwRule, prem: &[&BwSeq], c: &BwSeq) -> Result<(), String> {
        let (l, r) = (c.lhs.letters(), c.rhs.letters());
        let fail = |msg: &str| Err(msg.to_string());
        match (rule, prem) {
            (BwRule::A1, []) => {
                if r.is_empty() { Ok(()) } else { fail(tr("A1 の右辺は ⊤ でなければならない", "the right side of A1 must be ⊤")) }
            }
            (BwRule::A2, []) => match (l, r) {
                ([a, b, x @ ..], [c0, y @ ..]) if a == b && b == c0 && x == y => Ok(()),
                _ => fail(tr("A2 の形 (x)(x)c ⊢ (x)c ではない", "not of the A2 form (x)(x)c ⊢ (x)c")),
            },
            // 副条件は x ⊢ ()y（y ◁ x）か x ⊢ y（y ≤ x）
            (BwRule::A3, [s]) => match (l, r) {
                ([x, tx @ ..], [y, ty @ ..]) if tx == ty && (is_lt(s, y, x) || (s.lhs == *x && s.rhs == *y)) => Ok(()),
                _ => fail(tr("A3 の形 (x)c ⊢ (y)c（副条件 x ⊢ ()y か x ⊢ y）ではない", "not of the A3 form (x)c ⊢ (y)c (side condition x ⊢ ()y or x ⊢ y)")),
            },
            (BwRule::Cut, [p, q]) => {
                if p.lhs == c.lhs && p.rhs == q.lhs && q.rhs == c.rhs {
                    Ok(())
                } else {
                    fail(tr("Cut の前提と結論が噛み合わない", "the premises of Cut do not match the conclusion"))
                }
            }
            (BwRule::Nec, [p]) => match (l, r) {
                ([g, x @ ..], [h, y @ ..]) if g == h && x == p.lhs.letters() && y == p.rhs.letters() => Ok(()),
                _ => fail(tr("Nec の形 a ⊢ b ⇒ (x)a ⊢ (x)b ではない", "not of the Nec form a ⊢ b ⇒ (x)a ⊢ (x)b")),
            },
            (BwRule::R3, [p, q, sides @ ..]) => {
                let Some(alpha) = q.rhs.letters().first() else {
                    return fail(tr("R3 の第 2 前提の右辺が (x)c の形ではない", "the right side of the second premise of R3 is not of the form (x)c"));
                };
                let b = p.rhs.letters();
                let shape = p.lhs == c.lhs
                    && q.lhs == c.lhs
                    && r.len() == b.len() + q.rhs.letters().len()
                    && r[..b.len()] == *b
                    && r[b.len()..] == *q.rhs.letters();
                if !shape {
                    return fail(tr("R3 の前提と結論が噛み合わない", "the premises of R3 do not match the conclusion"));
                }
                // b の各文字 y について副条件 y ⊢ ()x があり、副条件はどれも b の文字についてのもの
                let covered = b.iter().all(|y| sides.iter().any(|s| is_lt(s, alpha, y)));
                let relevant = sides.iter().all(|s| b.iter().any(|y| is_lt(s, alpha, y)));
                if covered && relevant { Ok(()) } else { fail(tr("R3 の副条件（b の文字はすべて x より大きい）が足りない", "missing side conditions of R3 (every letter of b is greater than x)")) }
            }
            _ => fail(tr("規則と前提の個数が合わない", "wrong number of premises for the rule")),
        }
    }
}

/// 証明を検査し、結論を返す。
pub fn check(p: &BwProof) -> Result<&BwSeq, String> {
    proof::check::<Bwc>(p)
}

/// 文字を正規形にした worm。
fn nf_worm(a: &Bracket) -> Worm<NfBracket> {
    Worm::new(a.letters().iter().map(NfBracket::new).collect())
}

fn to_bracket(w: &Worm<NfBracket>) -> Bracket {
    Bracket::new(w.letters().iter().map(|x| x.bracket().clone()).collect())
}

fn to_seq(s: &WSeq<NfBracket>) -> BwSeq {
    BwSeq::new(to_bracket(&s.lhs), to_bracket(&s.rhs))
}

/// a ⊢ b が成り立つか（WC の構文的判定。文字の比較は順序数を使わない括弧語の比較）。
pub fn decide(a: &Bracket, b: &Bracket) -> bool {
    wc::decide(&nf_worm(a), &nf_worm(b))
}

/// 導出の大きさなどの情報。
#[derive(Clone, Debug, Default, Serialize)]
pub struct BwcStats {
    /// 副条件（文字どうしの比較）として導出した括弧語のシーケントの数（重複なし）
    pub side_conditions: usize,
    /// 副条件の入れ子の最大の深さ
    pub max_side_depth: usize,
}

struct Deriver {
    b: Builder<BwSeq, BwRule>,
    side: HashSet<BwSeq>,
    depth: usize,
    max_depth: usize,
}

impl Deriver {
    fn new() -> Self {
        Deriver { b: Builder::new(), side: HashSet::new(), depth: 0, max_depth: 0 }
    }

    fn concl(&self, id: usize) -> &BwSeq {
        self.b.conclusion(id)
    }

    /// p: a ⊢ b と q: b ⊢ c から a ⊢ c（片方が恒等式なら省く）。
    fn cut(&mut self, p: usize, q: usize) -> usize {
        let (pc, qc) = (self.concl(p).clone(), self.concl(q).clone());
        debug_assert_eq!(pc.rhs, qc.lhs);
        if pc.lhs == pc.rhs {
            return q;
        }
        if qc.lhs == qc.rhs {
            return p;
        }
        self.b.add(BwRule::Cut, vec![p, q], BwSeq::new(pc.lhs, qc.rhs))
    }

    /// 副条件のシーケント a ⊢ b を（入れ子を 1 段深くして）導出する。
    fn side(&mut self, a: &Bracket, b: &Bracket) -> Result<usize, String> {
        self.depth += 1;
        self.max_depth = self.max_depth.max(self.depth);
        let r = self.prove(a, b);
        self.depth -= 1;
        self.side.insert(BwSeq::new(a.clone(), b.clone()));
        r
    }

    /// y ◁ x の証拠 x ⊢ ()y。
    fn side_lt(&mut self, x: &Bracket, y: &Bracket) -> Result<usize, String> {
        self.side(x, &y.prepend(Bracket::top()))
    }

    fn prove(&mut self, a: &Bracket, b: &Bracket) -> Result<usize, String> {
        let goal = BwSeq::new(a.clone(), b.clone());
        if let Some(id) = self.b.lookup(&goal) {
            return Ok(id);
        }
        // 1. 文字を正規形にした worm で WC の証明を作る（構文的、順序数なし）
        let (wa, wb) = (nf_worm(a), nf_worm(b));
        let p = wc::prove(&wa, &wb).map_err(|_| format!("BWC ⊬ {goal}"))?;
        // 2. WC の各ステップを BWC の規則に置き換え、文字の比較を副条件として導出する
        let mut id = self.translate(&p)?;
        // 3. 正規形でない文字があれば、元の括弧語との書き換えを前後に付ける
        let (na, nb) = (to_bracket(&wa), to_bracket(&wb));
        if na != *a {
            let br = self.rewrite(a, &na)?;
            id = self.cut(br, id);
        }
        if nb != *b {
            let br = self.rewrite(&nb, b)?;
            id = self.cut(id, br);
        }
        Ok(id)
    }

    fn translate(&mut self, p: &WcProof<NfBracket>) -> Result<usize, String> {
        let mut map: Vec<usize> = Vec::with_capacity(p.nodes.len());
        for node in &p.nodes {
            let c = to_seq(&node.conclusion);
            let prem: Vec<usize> = node.premises.iter().map(|&i| map[i]).collect();
            let id = match node.rule {
                WcRule::A1 => self.b.add(BwRule::A1, prem, c),
                WcRule::A2 => self.b.add(BwRule::A2, prem, c),
                WcRule::Cut => self.b.add(BwRule::Cut, prem, c),
                WcRule::Nec => self.b.add(BwRule::Nec, prem, c),
                // (x)c ⊢ (y)c（x > y）：副条件 x ⊢ ()y
                WcRule::A3 => {
                    let (x, y) = (c.lhs.letters()[0].clone(), c.rhs.letters()[0].clone());
                    let s = self.side_lt(&x, &y)?;
                    self.b.add(BwRule::A3, vec![s], c)
                }
                // a ⊢ b, a ⊢ (x)c ⇒ a ⊢ b(x)c：b の異なる文字 y ごとに副条件 y ⊢ ()x
                WcRule::R3 => {
                    let q = &p.nodes[node.premises[1]].conclusion;
                    let alpha = q.rhs.letters()[0].bracket().clone();
                    let b = &p.nodes[node.premises[0]].conclusion.rhs;
                    let mut seen = HashSet::new();
                    let mut prem = prem;
                    for y in b.letters() {
                        if seen.insert(y.clone()) {
                            prem.push(self.side_lt(y.bracket(), &alpha)?);
                        }
                    }
                    self.b.add(BwRule::R3, prem, c)
                }
            };
            map.push(id);
        }
        Ok(map[p.root])
    }

    /// 同じ長さで、対応する文字が同じ順序数を表す 2 つの括弧語の間の導出 from ⊢ to。
    /// 右から 1 文字ずつ：Nec で (x)c ⊢ (x)c'、文字が違えば A3（副条件 x ⊢ y）で (x)c' ⊢ (y)c'。
    fn rewrite(&mut self, from: &Bracket, to: &Bracket) -> Result<usize, String> {
        let (f, t) = (from.letters(), to.letters());
        if f.len() != t.len() {
            return Err(format!("{}: {from} ⊢ {to}", tr("書き換えできない形（バグです）", "cannot rewrite (a bug)")));
        }
        let mut id = self.b.add(BwRule::A1, vec![], BwSeq::new(Bracket::top(), Bracket::top()));
        for i in (0..f.len()).rev() {
            let (x, y) = (&f[i], &t[i]);
            let tf = Bracket::new(f[i + 1..].to_vec());
            let tt = Bracket::new(t[i + 1..].to_vec());
            let nec = self.b.add(BwRule::Nec, vec![id], BwSeq::new(tf.prepend(x.clone()), tt.prepend(x.clone())));
            id = if x == y {
                nec
            } else {
                let s = self.side(x, y)?;
                let a3 = self.b.add(BwRule::A3, vec![s], BwSeq::new(tt.prepend(x.clone()), tt.prepend(y.clone())));
                self.cut(nec, a3)
            };
        }
        Ok(id)
    }
}

/// BWC で a ⊢ b の導出を作る。成り立たなければ `Err`。
pub fn prove(a: &Bracket, b: &Bracket) -> Result<(BwProof, BwcStats), String> {
    let mut d = Deriver::new();
    let root = d.prove(a, b)?;
    let stats = BwcStats { side_conditions: d.side.len(), max_side_depth: d.max_depth };
    Ok((d.b.finish(root), stats))
}

/// b ◁ a（a ⊢ ()b）の BWC の導出。
pub fn prove_lt(b: &Bracket, a: &Bracket) -> Result<(BwProof, BwcStats), String> {
    let s = BwSeq::lt(b, a);
    prove(&s.lhs, &s.rhs)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn br(s: &str) -> Bracket {
        s.parse().unwrap()
    }

    fn proves(a: &str, b: &str) -> (BwProof, BwcStats) {
        let (p, st) = prove(&br(a), &br(b)).unwrap_or_else(|e| panic!("{e}"));
        let c = check(&p).unwrap_or_else(|e| panic!("{a} ⊢ {b}: {e}"));
        assert_eq!(c, &BwSeq::new(br(a), br(b)));
        (p, st)
    }

    #[test]
    fn basic() {
        // ε_0 > ω：((())) ⊢ ()(())
        let (_, st) = proves("((()))", "()(())");
        assert!(st.side_conditions > 0);
        // ω の 2 通りの書き方（正規形でない (())() も ω）
        proves("((())())", "((()))");
        proves("((()))", "((())())");
        // 成り立たないもの
        assert!(prove(&br("()"), &br("(())")).is_err());
        assert!(!decide(&br("()"), &br("(())")));
        // ⊤ はどこからでも
        proves("()", "");
        proves("", "");
    }

    #[test]
    fn checker_rejects() {
        let (p, _) = proves("((()))", "()(())");
        // 副条件の結論を壊すと検査に落ちる
        for i in 0..p.nodes.len() {
            if p.nodes[i].rule == BwRule::A3 {
                let mut q = p.clone();
                let s = q.nodes[i].premises[0];
                q.nodes[s].conclusion.rhs = Bracket::top();
                assert!(check(&q).is_err());
                return;
            }
        }
    }

    #[test]
    fn parse() {
        let s: BwSeq = "((())) |- ()(())".parse().unwrap();
        assert_eq!(s.to_string(), "((())) ⊢ ()(())");
        let t: BwSeq = "() ⊢ ⊤".parse().unwrap();
        assert!(t.rhs.is_top());
    }
}
