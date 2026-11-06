//! Bracket Calculus (BC)：モダリティそのものが括弧語でできた、自己完結した証明体系。
//!
//! 出典：D. Fernández-Duque & E. Hermo Reyes, "Deducibility and Independence in
//! Beklemishev's Autonomous Provability Calculus" (arXiv:2008.13445), §6。
//!
//! RC_Γ0 では、モダリティ ⟨α⟩ の番号 α は「あらかじめ与えられた順序数」だった。
//! BC では番号の代わりに括弧語 a を使い、(a)φ と書く。モダリティどうしの大小も
//! 順序数で決めるのではなく、**BC 自身の導出**で決める。だから順序数の理論を
//! 一切前提にせずに Γ0 までの順序数表記を作れる、というのが BC の要点。
//!
//! # 言語（Def. 26）
//! ```text
//!   φ, ψ ::= ⊤ | p | φ ∧ ψ | (a)φ        （a は括弧語）
//! ```
//! 括弧語 a = (a_1)(a_2)…(a_k) は、そのまま式 (a_1)(a_2)…(a_k)⊤ とも読む。
//!
//! # 公理と規則（Def. 27）
//! ```text
//! Id   φ ⊢ φ           ⊤    φ ⊢ ⊤          ∧E1  φ ∧ ψ ⊢ φ       ∧E2  φ ∧ ψ ⊢ ψ
//! ∧I   φ ⊢ ψ, φ ⊢ χ ⇒ φ ⊢ ψ ∧ χ
//! Cut  φ ⊢ ψ, ψ ⊢ χ ⇒ φ ⊢ χ
//! R3a  φ ⊢ ψ, b ≤ a ⇒ (a)φ ⊢ (b)ψ
//! R3b  φ ⊢ ψ, b ≤ a ⇒ (a)(b)φ ⊢ (b)ψ
//! R4   b ◁ a       ⇒ (a)φ ∧ (b)ψ ⊢ (a)(φ ∧ (b)ψ)
//! ```
//! ここで
//! - b ◁ a は「シーケント a ⊢ ()b が導出できる」こと
//! - b ≤ a は「a ⊢ ()b か a ⊢ b が導出できる」こと
//!
//! （論文では規則 3 を 1 つの規則として結論を 2 つ書いている。ここでは R3a と R3b に分けた。）
//! つまり R3・R4 の副条件は、それ自体が括弧語どうしの BC の導出。このライブラリの
//! 証明 DAG では、副条件の導出を**ふつうの前提として**持たせる。R3a・R3b の前提は
//! [φ ⊢ ψ の導出, 副条件の導出]、R4 の前提は [副条件の導出] の形になる。こうすると
//! 検査器は 1 ステップずつ形を照らし合わせるだけでよく、順序数を一切使わない。
//!
//! # BC と RC_Γ0 の関係（Thm 38）
//! τ を (a)φ ↦ ⟨o*(a)⟩φ^τ という翻訳とすると、BC ⊢ φ ⊢ ψ ⟺ RC_Γ0 ⊢ φ^τ ⊢ ψ^τ。
//!
//! # このモジュールでの作り方
//! - 判定 [`decide`]：モダリティを正規形の括弧語 [`NfBracket`] に直して RC の判定器にかける。
//!   括弧語の大小は順序数を使わない比較で決めるので、ここでも順序数は出てこない。
//!   照合用に、τ で Veblen 表記の順序数に翻訳して判定する [`decide_tau`] も用意する。
//! - 導出 [`derive`]：RC の導出（[`crate::rcproof`]）を作り、各ステップを BC の規則に
//!   置き換える。Nec は R3a（副条件 a ⊢ a）、4 は R3b、Mono は R3a（副条件 a ⊢ ()b）、
//!   J は R4（副条件 a ⊢ ()b）になる。副条件 a ⊢ ()b は同じ方法で再帰的に導出する。
//!   副条件に出てくるモダリティは a, b の文字と ⊤ だけで、入れ子が必ず浅くなるので止まる。
//!   正規形でないモダリティ (a) は、副条件 a ⊢ nf(a) を使って正規形 (nf(a)) と行き来する。

use crate::bracket::{Bracket, NfBracket};
use crate::proof::{self, Builder, Calculus, Proof};
use crate::rc;
use crate::rcproof::{self, RSeq, RcRule};
use crate::spf::Spf;
use crate::veblen::Veblen;
use serde::Serialize;
use std::collections::HashSet;
use std::fmt;
use std::str::FromStr;

// ----------------------------------------------------------------------
// 式
// ----------------------------------------------------------------------

/// BC の式。モダリティは括弧語。
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Formula {
    Top,
    Var(String),
    And(Box<Formula>, Box<Formula>),
    Dia(Bracket, Box<Formula>),
}

impl Formula {
    pub fn var(name: &str) -> Formula {
        Formula::Var(name.to_string())
    }

    pub fn and(a: Formula, b: Formula) -> Formula {
        Formula::And(Box::new(a), Box::new(b))
    }

    pub fn dia(a: Bracket, phi: Formula) -> Formula {
        Formula::Dia(a, Box::new(phi))
    }

    /// 括弧語 a = (a_1)…(a_k) を式 (a_1)…(a_k)⊤ として読む。
    pub fn worm(a: &Bracket) -> Formula {
        a.letters().iter().rev().fold(Formula::Top, |acc, x| Formula::dia(x.clone(), acc))
    }

    /// worm の形の式なら括弧語に戻す（∧ や変数を含めば `None`）。
    pub fn as_worm(&self) -> Option<Bracket> {
        let mut letters = Vec::new();
        let mut cur = self;
        loop {
            match cur {
                Formula::Top => return Some(Bracket::new(letters)),
                Formula::Dia(a, x) => {
                    letters.push(a.clone());
                    cur = x;
                }
                _ => return None,
            }
        }
    }

    /// 式の大きさ（記号の個数。モダリティの中身は数えない）。
    pub fn size(&self) -> usize {
        match self {
            Formula::Top | Formula::Var(_) => 1,
            Formula::And(a, b) => 1 + a.size() + b.size(),
            Formula::Dia(_, a) => 1 + a.size(),
        }
    }

    /// モダリティの括弧の入れ子の深さの最大値（論文の Nt に当たる量）。
    pub fn nesting(&self) -> usize {
        match self {
            Formula::Top | Formula::Var(_) => 0,
            Formula::And(a, b) => a.nesting().max(b.nesting()),
            Formula::Dia(m, a) => (m.depth() + 1).max(a.nesting()),
        }
    }

    /// すべてのモダリティを正規形にした式（順序数を使わない）。
    pub fn normalize(&self) -> Formula {
        match self {
            Formula::Top | Formula::Var(_) => self.clone(),
            Formula::And(a, b) => Formula::and(a.normalize(), b.normalize()),
            Formula::Dia(m, a) => Formula::dia(m.normal_form_syntactic(), a.normalize()),
        }
    }

    /// RC の式に直す：(a)φ ↦ ⟨nf(a)⟩φ。文字は正規形の括弧語で、順序数は使わない。
    pub fn to_rc(&self) -> Spf<NfBracket> {
        match self {
            Formula::Top => Spf::Top,
            Formula::Var(p) => Spf::Var(p.clone()),
            Formula::And(a, b) => Spf::and(a.to_rc(), b.to_rc()),
            Formula::Dia(m, a) => Spf::dia(NfBracket::new(m), a.to_rc()),
        }
    }

    /// [`Self::to_rc`] の逆向き。
    pub fn from_rc(a: &Spf<NfBracket>) -> Formula {
        match a {
            Spf::Top => Formula::Top,
            Spf::Var(p) => Formula::Var(p.clone()),
            Spf::And(x, y) => Formula::and(Formula::from_rc(x), Formula::from_rc(y)),
            Spf::Dia(m, x) => Formula::dia(m.bracket().clone(), Formula::from_rc(x)),
        }
    }

    /// 論文の翻訳 τ（Def. 28）：(a)φ ↦ ⟨o*(a)⟩φ^τ。**順序数を使う**（照合用）。
    pub fn tau(&self) -> Spf<Veblen> {
        match self {
            Formula::Top => Spf::Top,
            Formula::Var(p) => Spf::Var(p.clone()),
            Formula::And(a, b) => Spf::and(a.tau(), b.tau()),
            Formula::Dia(m, a) => Spf::dia(m.ordinal(), a.tau()),
        }
    }
}

// ----------------------------------------------------------------------
// 表示とパース
// ----------------------------------------------------------------------

/// モダリティ (a) の表示。a = ⊤ なら ()。
fn modality(a: &Bracket) -> String {
    if a.is_top() { "()".to_string() } else { format!("({a})") }
}

impl fmt::Display for Formula {
    /// 論文の書き方：(a)φ。φ = ⊤ なら省略、φ が ∧ なら (a)(φ ∧ ψ) と括弧でくくる。
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::Top => write!(f, "⊤"),
            Formula::Var(p) => write!(f, "{p}"),
            Formula::And(a, b) => match **b {
                // 右側の ∧ は括弧でくくる（パースすると左結合になるので）
                Formula::And(..) => write!(f, "{a} ∧ ({b})"),
                _ => write!(f, "{a} ∧ {b}"),
            },
            Formula::Dia(m, a) => {
                write!(f, "{}", modality(m))?;
                match **a {
                    Formula::Top => Ok(()),
                    Formula::And(..) => write!(f, "({a})"),
                    _ => write!(f, "{a}"),
                }
            }
        }
    }
}

impl Serialize for Formula {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.collect_str(self)
    }
}

/// パースの失敗。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub input: String,
    pub pos: usize,
    pub msg: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}（{} 文字目付近）: {}", self.msg, self.pos, self.input)
    }
}

impl std::error::Error for ParseError {}

// 文法：
//   formula := unary ( ('∧' | '&') unary )*
//   unary   := '(' 括弧語 ')' rest      … モダリティ（rest が無ければ ⊤）
//            | '(' formula ')'          … ただのグループ（括弧語として読めないとき）
//            | ('<' | '⟨') 括弧語 ('>' | '⟩') unary
//            | '⊤' | 'T' | 'top' | 変数名
//
// "(" の後ろが括弧だけでできていれば、まずモダリティとして読む。たとえば
// "((()))" は「モダリティ (()) を ⊤ に付けた式」であり、グループ "( (()) )" ではない。
// "(a)(p ∧ q)" の 2 つ目の括弧は中に p があるので、括弧語ではなくグループとして読む。

struct Parser<'a> {
    input: &'a str,
    chars: Vec<char>,
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Parser { input, chars: input.chars().collect(), pos: 0 }
    }

    fn error<T>(&self, msg: &str) -> Result<T, ParseError> {
        Err(ParseError { input: self.input.to_string(), pos: self.pos, msg: msg.to_string() })
    }

    fn skip_ws(&mut self) {
        while self.pos < self.chars.len() && self.chars[self.pos].is_whitespace() {
            self.pos += 1;
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.skip_ws();
        self.chars.get(self.pos).copied()
    }

    fn eat(&mut self, c: char) -> bool {
        if self.peek() == Some(c) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    /// 括弧語 (a_1)(a_2)… を読む（読めなければ `None`、位置は呼び出し側で戻す）。
    fn word(&mut self) -> Option<Bracket> {
        let mut letters = Vec::new();
        while self.peek() == Some('(') {
            self.pos += 1;
            let inner = self.word()?;
            if !self.eat(')') {
                return None;
            }
            letters.push(inner);
        }
        Some(Bracket::new(letters))
    }

    /// '(' の位置で「括弧語 + ')'」が読めればそれを返す。読めなければ位置を戻す。
    fn try_modality(&mut self) -> Option<Bracket> {
        let start = self.pos;
        self.pos += 1; // '('
        if let Some(a) = self.word()
            && self.eat(')')
        {
            return Some(a);
        }
        self.pos = start;
        None
    }

    fn formula(&mut self) -> Result<Formula, ParseError> {
        let mut acc = self.unary()?;
        while self.eat('∧') || self.eat('&') {
            let rhs = self.unary()?;
            acc = Formula::and(acc, rhs);
        }
        Ok(acc)
    }

    /// モダリティの後ろ：式が続かなければ ⊤。
    fn rest(&mut self) -> Result<Formula, ParseError> {
        match self.peek() {
            None | Some('∧' | '&' | ')') => Ok(Formula::Top),
            _ => self.unary(),
        }
    }

    fn unary(&mut self) -> Result<Formula, ParseError> {
        match self.peek() {
            Some('(') => {
                if let Some(a) = self.try_modality() {
                    return Ok(Formula::dia(a, self.rest()?));
                }
                self.pos += 1;
                let a = self.formula()?;
                if !self.eat(')') {
                    return self.error("')' が必要です");
                }
                Ok(a)
            }
            Some(open @ ('<' | '⟨')) => {
                self.pos += 1;
                let close = if open == '<' { '>' } else { '⟩' };
                let start = self.pos;
                let Some(a) = self.word() else {
                    self.pos = start;
                    return self.error("括弧語が読めません");
                };
                // ⟨⊤⟩ や ⟨()()⊤⟩ のような末尾の ⊤ は許す
                let _ = self.eat('⊤') || self.eat('T');
                if !self.eat(close) {
                    return self.error(&format!("'{close}' が必要です"));
                }
                Ok(Formula::dia(a, self.unary()?))
            }
            Some('⊤') => {
                self.pos += 1;
                Ok(Formula::Top)
            }
            Some(c) if c.is_ascii_alphabetic() => {
                let start = self.pos;
                while self.pos < self.chars.len()
                    && (self.chars[self.pos].is_ascii_alphanumeric() || self.chars[self.pos] == '_')
                {
                    self.pos += 1;
                }
                let name: String = self.chars[start..self.pos].iter().collect();
                match name.as_str() {
                    "T" | "top" => Ok(Formula::Top),
                    _ if c.is_ascii_lowercase() => Ok(Formula::Var(name)),
                    _ => {
                        self.pos = start;
                        self.error("変数名は英小文字で始めてください")
                    }
                }
            }
            Some(_) => self.error("式が読めません"),
            None => self.error("式が途中で終わっています"),
        }
    }

    fn finish(&mut self) -> Result<(), ParseError> {
        if self.peek().is_some() { self.error("余分な文字があります") } else { Ok(()) }
    }
}

/// `"((()))p ∧ (())q"`、`"(())(p & ()q)"`、`"<(())>p"` などを読む。
impl FromStr for Formula {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut p = Parser::new(s);
        let a = p.formula()?;
        p.finish()?;
        Ok(a)
    }
}

// ----------------------------------------------------------------------
// 判断・規則・検査器
// ----------------------------------------------------------------------

/// BC のシーケント φ ⊢ ψ。
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize)]
pub struct BSeq {
    pub lhs: Formula,
    pub rhs: Formula,
}

impl BSeq {
    pub fn new(lhs: Formula, rhs: Formula) -> BSeq {
        BSeq { lhs, rhs }
    }

    /// 括弧語どうしのシーケント a ⊢ b。
    pub fn worms(a: &Bracket, b: &Bracket) -> BSeq {
        BSeq::new(Formula::worm(a), Formula::worm(b))
    }

    /// 「b ◁ a」を表すシーケント a ⊢ ()b。
    pub fn lt(b: &Bracket, a: &Bracket) -> BSeq {
        BSeq::new(Formula::worm(a), Formula::dia(Bracket::top(), Formula::worm(b)))
    }

    fn from_rc(s: &RSeq<NfBracket>) -> BSeq {
        BSeq::new(Formula::from_rc(&s.lhs), Formula::from_rc(&s.rhs))
    }

    /// τ で RC_Γ0 のシーケントに翻訳する（順序数を使う、照合用）。
    pub fn tau(&self) -> RSeq<Veblen> {
        RSeq { lhs: self.lhs.tau(), rhs: self.rhs.tau() }
    }
}

impl fmt::Display for BSeq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ⊢ {}", self.lhs, self.rhs)
    }
}

/// `"φ |- ψ"` または `"φ ⊢ ψ"` を読む。
impl FromStr for BSeq {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (l, r) = s.split_once("⊢").or_else(|| s.split_once("|-")).ok_or_else(|| ParseError {
            input: s.to_string(),
            pos: 0,
            msg: "'⊢' または '|-' が必要です".to_string(),
        })?;
        Ok(BSeq::new(l.parse()?, r.parse()?))
    }
}

/// BC の規則。
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize)]
pub enum BcRule {
    Id,
    Top,
    AndE1,
    AndE2,
    AndI,
    Cut,
    R3a,
    R3b,
    R4,
}

impl fmt::Display for BcRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            BcRule::Id => "Id",
            BcRule::Top => "⊤",
            BcRule::AndE1 => "∧E1",
            BcRule::AndE2 => "∧E2",
            BcRule::AndI => "∧I",
            BcRule::Cut => "Cut",
            BcRule::R3a => "R3a",
            BcRule::R3b => "R3b",
            BcRule::R4 => "R4",
        };
        write!(f, "{s}")
    }
}

/// BC という証明体系（検査の規則だけを定める）。
pub struct Bc;

pub type BcProof = Proof<BSeq, BcRule>;

/// s が「b ◁ a」の証拠 a ⊢ ()b か。
fn lt_witness(s: &BSeq, a: &Bracket, b: &Bracket) -> bool {
    *s == BSeq::lt(b, a)
}

/// s が「b ≤ a」の証拠（a ⊢ ()b か a ⊢ b）か。
fn le_witness(s: &BSeq, a: &Bracket, b: &Bracket) -> bool {
    lt_witness(s, a, b) || *s == BSeq::worms(a, b)
}

impl Calculus for Bc {
    type Judgment = BSeq;
    type Rule = BcRule;

    fn check_step(rule: &BcRule, prem: &[&BSeq], c: &BSeq) -> Result<(), String> {
        use Formula::{And, Dia, Top};
        let ok = match (rule, prem) {
            (BcRule::Id, []) => c.lhs == c.rhs,
            (BcRule::Top, []) => c.rhs == Top,
            (BcRule::AndE1, []) => matches!(&c.lhs, And(a, _) if **a == c.rhs),
            (BcRule::AndE2, []) => matches!(&c.lhs, And(_, b) if **b == c.rhs),
            (BcRule::AndI, [p, q]) => {
                p.lhs == c.lhs && q.lhs == c.lhs && c.rhs == Formula::and(p.rhs.clone(), q.rhs.clone())
            }
            (BcRule::Cut, [p, q]) => p.lhs == c.lhs && p.rhs == q.lhs && q.rhs == c.rhs,
            // (a)φ ⊢ (b)ψ
            (BcRule::R3a, [p, s]) => match (&c.lhs, &c.rhs) {
                (Dia(a, phi), Dia(b, psi)) => p.lhs == **phi && p.rhs == **psi && le_witness(s, a, b),
                _ => false,
            },
            // (a)(b)φ ⊢ (b)ψ
            (BcRule::R3b, [p, s]) => match (&c.lhs, &c.rhs) {
                (Dia(a, inner), Dia(b, psi)) => {
                    matches!(&**inner, Dia(b2, phi) if b2 == b && p.lhs == **phi && p.rhs == **psi)
                        && le_witness(s, a, b)
                }
                _ => false,
            },
            // (a)φ ∧ (b)ψ ⊢ (a)(φ ∧ (b)ψ)
            (BcRule::R4, [s]) => match (&c.lhs, &c.rhs) {
                (And(l, r), Dia(a2, inner)) => match (&**l, &**r, &**inner) {
                    (Dia(a, phi), Dia(b, psi), And(phi2, rb)) => {
                        a == a2
                            && phi == phi2
                            && matches!(&**rb, Dia(b2, psi2) if b2 == b && psi2 == psi)
                            && lt_witness(s, a, b)
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

/// 導出を検査し、結論を返す。検査に順序数は一切使わない。
pub fn check(p: &BcProof) -> Result<&BSeq, String> {
    proof::check::<Bc>(p)
}

// ----------------------------------------------------------------------
// 判定
// ----------------------------------------------------------------------

/// BC ⊢ φ ⊢ ψ か。モダリティを正規形の括弧語にして RC の判定器にかける
/// （括弧語の大小は順序数を使わない比較で決まる）。
pub fn decide(lhs: &Formula, rhs: &Formula) -> bool {
    rc::entails(&lhs.to_rc(), &rhs.to_rc())
}

/// 照合用：τ で RC_Γ0 に翻訳して判定する（Thm 38）。順序数を使う。
pub fn decide_tau(lhs: &Formula, rhs: &Formula) -> bool {
    rc::entails(&lhs.tau(), &rhs.tau())
}

// ----------------------------------------------------------------------
// 導出の構成
// ----------------------------------------------------------------------

/// 導出の大きさなどの情報。
#[derive(Clone, Debug, Default, Serialize)]
pub struct BcStats {
    /// 副条件（b ◁ a や b ≤ a）として導出した括弧語のシーケントの数（重複なし）
    pub side_conditions: usize,
    /// 副条件の入れ子の最大の深さ（副条件の導出の中の副条件、…）
    pub max_side_depth: usize,
}

/// BC の導出を組み立てる道具。
struct Deriver {
    b: Builder<BSeq, BcRule>,
    side: HashSet<BSeq>,
    depth: usize,
    max_depth: usize,
}

impl Deriver {
    fn new() -> Self {
        Deriver { b: Builder::new(), side: HashSet::new(), depth: 0, max_depth: 0 }
    }

    fn concl(&self, id: usize) -> &BSeq {
        self.b.conclusion(id)
    }

    fn id(&mut self, phi: &Formula) -> usize {
        self.b.add(BcRule::Id, vec![], BSeq::new(phi.clone(), phi.clone()))
    }

    /// p: φ ⊢ ψ と q: ψ ⊢ χ から φ ⊢ χ（片方が Id なら省く）。
    fn cut(&mut self, p: usize, q: usize) -> usize {
        let (pc, qc) = (self.concl(p).clone(), self.concl(q).clone());
        debug_assert_eq!(pc.rhs, qc.lhs);
        if pc.lhs == pc.rhs {
            return q;
        }
        if qc.lhs == qc.rhs {
            return p;
        }
        self.b.add(BcRule::Cut, vec![p, q], BSeq::new(pc.lhs, qc.rhs))
    }

    /// 副条件のシーケントを（入れ子を 1 段深くして）導出する。
    fn side(&mut self, goal: BSeq) -> Result<usize, String> {
        self.depth += 1;
        self.max_depth = self.max_depth.max(self.depth);
        let r = self.prove(&goal.lhs, &goal.rhs);
        self.depth -= 1;
        self.side.insert(goal);
        r
    }

    /// b ◁ a の証拠 a ⊢ ()b。
    fn side_lt(&mut self, a: &Bracket, b: &Bracket) -> Result<usize, String> {
        self.side(BSeq::lt(b, a))
    }

    /// b ≤ a の証拠：a = b なら Id で a ⊢ a、そうでなければ a ⊢ b を導出する。
    fn side_le(&mut self, a: &Bracket, b: &Bracket) -> Result<usize, String> {
        if a == b { Ok(self.id(&Formula::worm(a))) } else { self.side(BSeq::worms(a, b)) }
    }

    /// φ ⊢ ψ の BC の導出。
    fn prove(&mut self, lhs: &Formula, rhs: &Formula) -> Result<usize, String> {
        let goal = BSeq::new(lhs.clone(), rhs.clone());
        if let Some(id) = self.b.lookup(&goal) {
            return Ok(id);
        }
        // 1. モダリティを正規形にして RC で導出する
        let (ln, rn) = (lhs.normalize(), rhs.normalize());
        let (p, _) = rcproof::derive(&ln.to_rc(), &rn.to_rc()).map_err(|_| format!("BC ⊬ {goal}"))?;
        // 2. RC の各ステップを BC の規則に置き換える
        let mut id = self.translate(&p)?;
        // 3. 正規形でないモダリティがあれば、元の式との橋渡しを前後に付ける
        if ln != *lhs {
            let br = self.bridge(lhs, &ln)?;
            id = self.cut(br, id);
        }
        if rn != *rhs {
            let br = self.bridge(&rn, rhs)?;
            id = self.cut(id, br);
        }
        Ok(id)
    }

    /// RC の導出（文字は正規形の括弧語）を BC の導出に置き換える。
    fn translate(&mut self, p: &rcproof::RcProof<NfBracket>) -> Result<usize, String> {
        use Formula::{And, Dia};
        let mut map: Vec<usize> = Vec::with_capacity(p.nodes.len());
        for node in &p.nodes {
            let c = BSeq::from_rc(&node.conclusion);
            let prem: Vec<usize> = node.premises.iter().map(|&i| map[i]).collect();
            let id = match node.rule {
                RcRule::Id => self.b.add(BcRule::Id, prem, c),
                RcRule::Top => self.b.add(BcRule::Top, prem, c),
                RcRule::AndE1 => self.b.add(BcRule::AndE1, prem, c),
                RcRule::AndE2 => self.b.add(BcRule::AndE2, prem, c),
                RcRule::AndI => self.b.add(BcRule::AndI, prem, c),
                RcRule::Cut => self.b.add(BcRule::Cut, prem, c),
                // Nec：(a)φ ⊢ (a)ψ は R3a（副条件 a ⊢ a）
                RcRule::Nec => {
                    let Dia(a, _) = &c.lhs else { unreachable!("Nec の形") };
                    let s = self.side_le(&a.clone(), &a.clone())?;
                    self.b.add(BcRule::R3a, vec![prem[0], s], c)
                }
                // 4：(a)(a)φ ⊢ (a)φ は R3b（前提 φ ⊢ φ、副条件 a ⊢ a）
                RcRule::Four => {
                    let Dia(a, inner) = &c.lhs else { unreachable!("4 の形") };
                    let Dia(_, phi) = &**inner else { unreachable!("4 の形") };
                    let (a, phi) = (a.clone(), (**phi).clone());
                    let refl = self.id(&phi);
                    let s = self.side_le(&a, &a)?;
                    self.b.add(BcRule::R3b, vec![refl, s], c)
                }
                // Mono：(a)φ ⊢ (b)φ（b ◁ a）は R3a（前提 φ ⊢ φ、副条件 a ⊢ ()b）
                RcRule::Mono => {
                    let (Dia(a, phi), Dia(b, _)) = (&c.lhs, &c.rhs) else { unreachable!("Mono の形") };
                    let (a, b, phi) = (a.clone(), b.clone(), (**phi).clone());
                    let refl = self.id(&phi);
                    let s = self.side_lt(&a, &b)?;
                    self.b.add(BcRule::R3a, vec![refl, s], c)
                }
                // J：(a)φ ∧ (b)ψ ⊢ (a)(φ ∧ (b)ψ)（b ◁ a）は R4（副条件 a ⊢ ()b）
                RcRule::J => {
                    let And(l, r) = &c.lhs else { unreachable!("J の形") };
                    let (Dia(a, _), Dia(b, _)) = (&**l, &**r) else { unreachable!("J の形") };
                    let (a, b) = (a.clone(), b.clone());
                    let s = self.side_lt(&a, &b)?;
                    self.b.add(BcRule::R4, vec![s], c)
                }
            };
            map.push(id);
        }
        Ok(map[p.root])
    }

    /// モダリティだけが違う（対応するモダリティが同じ順序数を表す）2 つの式の間の
    /// 導出 from ⊢ to。モダリティの付け替えは R3a（副条件 a ⊢ a'）で行う。
    fn bridge(&mut self, from: &Formula, to: &Formula) -> Result<usize, String> {
        use Formula::{And, Dia};
        if from == to {
            return Ok(self.id(from));
        }
        let goal = BSeq::new(from.clone(), to.clone());
        match (from, to) {
            (And(x, y), And(x2, y2)) => {
                let e1 = self.b.add(BcRule::AndE1, vec![], BSeq::new(from.clone(), (**x).clone()));
                let bx = self.bridge(x, x2)?;
                let l = self.cut(e1, bx);
                let e2 = self.b.add(BcRule::AndE2, vec![], BSeq::new(from.clone(), (**y).clone()));
                let by = self.bridge(y, y2)?;
                let r = self.cut(e2, by);
                Ok(self.b.add(BcRule::AndI, vec![l, r], goal))
            }
            (Dia(a, x), Dia(a2, x2)) => {
                let inner = self.bridge(x, x2)?;
                let s = self.side_le(a, a2)?;
                Ok(self.b.add(BcRule::R3a, vec![inner, s], goal))
            }
            _ => Err(format!("橋渡しできない形（バグです）: {goal}")),
        }
    }
}

/// BC で φ ⊢ ψ の導出を作る。成り立たなければ `Err`。
pub fn derive(lhs: &Formula, rhs: &Formula) -> Result<(BcProof, BcStats), String> {
    let mut d = Deriver::new();
    let root = d.prove(lhs, rhs)?;
    let stats = BcStats { side_conditions: d.side.len(), max_side_depth: d.max_depth };
    Ok((d.b.finish(root), stats))
}

/// b ◁ a（a ⊢ ()b）の BC の導出。成り立たなければ `Err`。
pub fn derive_lt(b: &Bracket, a: &Bracket) -> Result<(BcProof, BcStats), String> {
    let s = BSeq::lt(b, a);
    derive(&s.lhs, &s.rhs)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(s: &str) -> Formula {
        s.parse().unwrap_or_else(|e| panic!("{e}"))
    }

    #[test]
    fn parse_and_display() {
        // 括弧語はそのまま式として読む
        assert_eq!(f("((()))"), Formula::worm(&"((()))".parse().unwrap()));
        assert_eq!(f("(())p ∧ ()q").to_string(), "(())p ∧ ()q");
        // 2 つ目の括弧は中に p があるのでグループ
        let x = f("(())(p ∧ ()q)");
        assert!(matches!(&x, Formula::Dia(_, inner) if matches!(**inner, Formula::And(..))));
        assert_eq!(x.to_string(), "(())(p ∧ ()q)");
        // ⟨a⟩ の中身はモダリティの括弧語そのもの：⟨(())⟩p = ((()))p
        assert_eq!(f("<(())>p"), f("((()))p"));
        assert_eq!(f("<()>p"), f("(())p"));
        assert_eq!(f("⟨⊤⟩p"), f("()p"));
        for s in ["⊤", "p", "()", "((()))(())p", "(()) ∧ (()())", "p ∧ (q ∧ r)", "(())((()) ∧ p)"] {
            assert_eq!(f(s).to_string().parse::<Formula>().unwrap(), f(s), "{s}");
        }
        assert!("(()".parse::<Formula>().is_err());
        assert!("p ∧".parse::<Formula>().is_err());
    }

    #[test]
    fn translations() {
        // (())p = ⟨ω⟩p、正規形でないモダリティ (())() も ω
        assert_eq!(f("((()))p").tau().to_string(), "⟨ω⟩p");
        assert_eq!(f("((())())p").tau().to_string(), "⟨ω⟩p");
        assert_eq!(f("((())())p").normalize(), f("((()))p"));
        assert_eq!(Formula::from_rc(&f("((()))p ∧ ()q").to_rc()), f("((()))p ∧ ()q"));
    }

    fn proves(s: &str) -> (BcProof, BcStats) {
        let g: BSeq = s.parse().unwrap();
        assert!(decide(&g.lhs, &g.rhs), "{s}");
        let (p, st) = derive(&g.lhs, &g.rhs).unwrap_or_else(|e| panic!("{e}"));
        let c = check(&p).unwrap_or_else(|e| panic!("{s}: {e}\n{p}"));
        assert_eq!(c, &g);
        (p, st)
    }

    #[test]
    fn examples() {
        proves("p ⊢ p");
        proves("(())(())p ⊢ (())p"); // 4
        proves("(())p ⊢ ()p"); // Mono：() ◁ (())
        proves("((()))p ∧ (())q ⊢ ((()))(p ∧ (())q)"); // J：⟨ω⟩p ∧ ⟨1⟩q（1 ◁ ω）
        proves("((()))p ⊢ ()(())p"); // ⟨ω⟩p ⊢ ⟨0⟩⟨1⟩p
        proves("((())())p ⊢ ((()))p"); // 正規形でないモダリティ（どちらも ω）
        proves("((()))p ⊢ ((())())p");
        // ε_0 > ω^ω：括弧語として ((())) ⊢ ()(()())
        let (_, st) = proves("((())) ⊢ ()(()())");
        assert!(st.side_conditions > 0);
    }

    #[test]
    fn non_theorems() {
        for s in ["p ⊢ ()p", "()p ⊢ (())p", "()p ∧ ()q ⊢ ()(p ∧ q)", "(()()) ⊢ ()((()))"] {
            let g: BSeq = s.parse().unwrap();
            assert!(!decide(&g.lhs, &g.rhs), "{s}");
            assert!(derive(&g.lhs, &g.rhs).is_err(), "{s}");
        }
    }

    #[test]
    fn checker_rejects_bad_steps() {
        let s = |x: &str| x.parse::<BSeq>().unwrap();
        // 副条件の向きが逆（() ⊢ ()(()) は「(()) ◁ ()」の証拠ではない）
        let bad = Proof {
            nodes: vec![
                proof::Node { rule: BcRule::Id, premises: vec![], conclusion: s("p ⊢ p") },
                proof::Node { rule: BcRule::Id, premises: vec![], conclusion: s("() ⊢ ()") },
                proof::Node { rule: BcRule::R3a, premises: vec![0, 1], conclusion: s("()p ⊢ (())p") },
            ],
            root: 2,
        };
        assert!(check(&bad).is_err());
    }
}
