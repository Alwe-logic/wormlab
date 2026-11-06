//! Pakhomov–Lazar の Reflection Calculus for Bar Induction（RC_BI）と、その拡張 RC_BIω。
//!
//! 出典：F. Pakhomov & V. Lazar, "A Reflection Calculus for Bar Induction and the
//! Linearity of Consistency Strength Ordering" (arXiv:2610.20115)。
//!
//! # 言語（§2.1, §2.2）
//! ```text
//!   A ::= ⊤ | p | A ∧ B | ⟨1⟩_α A | ⟨2⟩_β A | ↓A | ∇A
//! ```
//! - ⟨1⟩_α（1 ≤ α < ω、RC_BIω では α = ω も）：Π¹_α 反射（ACA₀ + Π¹_α-RFN）
//! - ⟨2⟩_β（2 ≤ β < ω）：Π¹_β の ω モデル反射
//! - ↓：ω モデル射影（その理論の ω モデルすべてで成り立つ文）
//! - ∇：その理論の真な Π¹₁ 定理
//!
//! # 判定（§3, Thm 3.19）
//! 変数を含まない式 A, B について、A ⊢ B ⟺ 有限モデル M_A の根で B が真。
//! M_A の作り方は [`Model::of`] を参照。RC の標準木の閉包（[`crate::rc`]）と同じ発想だが、
//! フレーム条件の一部が「点の存在」を要求するので、閉包の前に点を足しておく。

use crate::bitset::BitSet;
use std::collections::BTreeSet;
use std::fmt;
use std::str::FromStr;

// ----------------------------------------------------------------------
// 添字（rank）
// ----------------------------------------------------------------------

/// モダリティの添字。有限の自然数か ω。
///
/// 【Rust メモ】enum に `#[derive(PartialOrd, Ord)]` を付けると、まず「何番目の
/// 変種か」で比べ、同じ変種なら中身で比べる順序になる。`Fin` を先に書いたので、
/// どの `Fin(n)` も `Omega` より小さい。
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Rank {
    Fin(u32),
    Omega,
}

impl Rank {
    pub fn fin(self) -> Option<u32> {
        match self {
            Rank::Fin(n) => Some(n),
            Rank::Omega => None,
        }
    }
}

const SUBSCRIPTS: [char; 10] = ['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉'];

impl fmt::Display for Rank {
    /// 有限なら下付き数字（₂）、ω なら _ω。
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rank::Fin(n) => {
                let s: String = n.to_string().chars().map(|c| SUBSCRIPTS[c as usize - '0' as usize]).collect();
                write!(f, "{s}")
            }
            Rank::Omega => write!(f, "_ω"),
        }
    }
}

// ----------------------------------------------------------------------
// 式
// ----------------------------------------------------------------------

/// RC_BIω の式。
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Formula {
    Top,
    Var(String),
    And(Box<Formula>, Box<Formula>),
    /// ⟨i⟩_α A。i = 1 なら α ≥ 1（ω も可）、i = 2 なら 2 ≤ α < ω。
    Dia(u8, Rank, Box<Formula>),
    /// ↓A
    Down(Box<Formula>),
    /// ∇A
    Nabla(Box<Formula>),
}

/// ⟨i⟩_α が言語にあるモダリティか。
pub fn valid_modality(i: u8, alpha: Rank) -> bool {
    match (i, alpha) {
        (1, Rank::Fin(n)) => n >= 1,
        (1, Rank::Omega) => true,
        (2, Rank::Fin(n)) => n >= 2,
        _ => false,
    }
}

impl Formula {
    pub fn var(name: &str) -> Formula {
        Formula::Var(name.to_string())
    }

    pub fn and(a: Formula, b: Formula) -> Formula {
        Formula::And(Box::new(a), Box::new(b))
    }

    /// ⟨i⟩_α A（言語にないモダリティなら panic）。
    pub fn dia(i: u8, alpha: Rank, a: Formula) -> Formula {
        assert!(valid_modality(i, alpha), "⟨{i}⟩{alpha} は RC_BIω のモダリティではありません");
        Formula::Dia(i, alpha, Box::new(a))
    }

    /// ⟨1⟩_n A
    pub fn one(n: u32, a: Formula) -> Formula {
        Formula::dia(1, Rank::Fin(n), a)
    }

    /// ⟨1⟩_ω A
    pub fn one_omega(a: Formula) -> Formula {
        Formula::dia(1, Rank::Omega, a)
    }

    /// ⟨2⟩_n A
    pub fn two(n: u32, a: Formula) -> Formula {
        Formula::dia(2, Rank::Fin(n), a)
    }

    pub fn down(a: Formula) -> Formula {
        Formula::Down(Box::new(a))
    }

    pub fn nabla(a: Formula) -> Formula {
        Formula::Nabla(Box::new(a))
    }

    /// 複数の式の連言（空なら ⊤）。
    pub fn conj(items: impl IntoIterator<Item = Formula>) -> Formula {
        items.into_iter().reduce(Formula::and).unwrap_or(Formula::Top)
    }

    /// 式の大きさ（記号の個数）。
    pub fn size(&self) -> usize {
        match self {
            Formula::Top | Formula::Var(_) => 1,
            Formula::And(a, b) => 1 + a.size() + b.size(),
            Formula::Dia(_, _, a) | Formula::Down(a) | Formula::Nabla(a) => 1 + a.size(),
        }
    }

    /// 変数を含まないか。
    pub fn is_closed(&self) -> bool {
        match self {
            Formula::Top => true,
            Formula::Var(_) => false,
            Formula::And(a, b) => a.is_closed() && b.is_closed(),
            Formula::Dia(_, _, a) | Formula::Down(a) | Formula::Nabla(a) => a.is_closed(),
        }
    }

    /// W_BI の元か：変数・∇・⟨1⟩_ω を含まない（論文の順序 <¹₁ が考える式）。
    pub fn in_wbi(&self) -> bool {
        match self {
            Formula::Top => true,
            Formula::Var(_) | Formula::Nabla(_) => false,
            Formula::And(a, b) => a.in_wbi() && b.in_wbi(),
            Formula::Dia(_, Rank::Omega, _) => false,
            Formula::Dia(_, _, a) | Formula::Down(a) => a.in_wbi(),
        }
    }

    /// 現れる有限の添字の最大値（なければ 0）。
    pub fn max_rank(&self) -> u32 {
        match self {
            Formula::Top | Formula::Var(_) => 0,
            Formula::And(a, b) => a.max_rank().max(b.max_rank()),
            Formula::Dia(_, r, a) => r.fin().unwrap_or(0).max(a.max_rank()),
            Formula::Down(a) | Formula::Nabla(a) => a.max_rank(),
        }
    }

    /// top conjuncts（Def 4.5）：∧ をほどいた各成分。
    pub fn top_conjuncts(&self) -> Vec<&Formula> {
        match self {
            Formula::And(a, b) => {
                let mut v = a.top_conjuncts();
                v.extend(b.top_conjuncts());
                v
            }
            _ => vec![self],
        }
    }
}

// ----------------------------------------------------------------------
// 表示とパース
// ----------------------------------------------------------------------

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // 単項演算子の後ろ：∧ なら括弧でくくる
        fn operand(f: &mut fmt::Formatter<'_>, a: &Formula) -> fmt::Result {
            match a {
                Formula::And(..) => write!(f, "({a})"),
                _ => write!(f, "{a}"),
            }
        }
        match self {
            Formula::Top => write!(f, "⊤"),
            Formula::Var(p) => write!(f, "{p}"),
            Formula::And(a, b) => match **b {
                Formula::And(..) => write!(f, "{a} ∧ ({b})"),
                _ => write!(f, "{a} ∧ {b}"),
            },
            Formula::Dia(i, r, a) => {
                write!(f, "⟨{i}⟩{r}")?;
                operand(f, a)
            }
            Formula::Down(a) => {
                write!(f, "↓")?;
                operand(f, a)
            }
            Formula::Nabla(a) => {
                write!(f, "∇")?;
                operand(f, a)
            }
        }
    }
}

impl serde::Serialize for Formula {
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
//   unary   := ('<' | '⟨') ('1' | '2') ('>' | '⟩') rank? unary     … 添字を省くと ⟨1⟩₁, ⟨2⟩₂
//            | ('↓' | 'D') unary | ('∇' | 'N') unary
//            | '⊤' | 'T' | 'top' | 変数名 | '(' formula ')'
//   rank    := 下付き数字（₂）| '_' 数字 | '_' ('ω' | 'w' | 'omega')

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

    fn formula(&mut self) -> Result<Formula, ParseError> {
        let mut acc = self.unary()?;
        while self.eat('∧') || self.eat('&') {
            let rhs = self.unary()?;
            acc = Formula::and(acc, rhs);
        }
        Ok(acc)
    }

    /// モダリティの直後の添字（なければ `None`）。空白は挟まない。
    fn rank(&mut self) -> Result<Option<Rank>, ParseError> {
        let at = |p: &Self, i: usize| p.chars.get(p.pos + i).copied();
        // 下付き数字
        let mut digits = String::new();
        while let Some(c) = at(self, 0) {
            match SUBSCRIPTS.iter().position(|&s| s == c) {
                Some(d) => {
                    digits.push(char::from(b'0' + d as u8));
                    self.pos += 1;
                }
                None => break,
            }
        }
        if !digits.is_empty() {
            return digits.parse().map(|n| Some(Rank::Fin(n))).or_else(|_| self.error("添字が大きすぎます"));
        }
        if at(self, 0) != Some('_') {
            return Ok(None);
        }
        self.pos += 1;
        let start = self.pos;
        while let Some(c) = at(self, 0) {
            if c.is_ascii_alphanumeric() || c == 'ω' {
                self.pos += 1;
            } else {
                break;
            }
        }
        let s: String = self.chars[start..self.pos].iter().collect();
        match s.as_str() {
            "ω" | "w" | "omega" => Ok(Some(Rank::Omega)),
            _ => match s.parse() {
                Ok(n) => Ok(Some(Rank::Fin(n))),
                Err(_) => {
                    self.pos = start;
                    self.error("添字が読めません（数字か ω）")
                }
            },
        }
    }

    fn unary(&mut self) -> Result<Formula, ParseError> {
        match self.peek() {
            Some(open @ ('<' | '⟨')) => {
                self.pos += 1;
                let close = if open == '<' { '>' } else { '⟩' };
                let i = match self.peek() {
                    Some('1') => 1u8,
                    Some('2') => 2u8,
                    _ => return self.error("⟨1⟩ か ⟨2⟩ が必要です"),
                };
                self.pos += 1;
                if !self.eat(close) {
                    return self.error(&format!("'{close}' が必要です"));
                }
                let alpha = self.rank()?.unwrap_or(Rank::Fin(i as u32));
                if !valid_modality(i, alpha) {
                    return self.error(&format!("⟨{i}⟩{alpha} はモダリティではありません（⟨1⟩ は添字 1 以上か ω、⟨2⟩ は 2 以上の有限）"));
                }
                Ok(Formula::dia(i, alpha, self.unary()?))
            }
            Some('↓' | 'D') => {
                self.pos += 1;
                Ok(Formula::down(self.unary()?))
            }
            Some('∇' | 'N') => {
                self.pos += 1;
                Ok(Formula::nabla(self.unary()?))
            }
            Some('⊤') => {
                self.pos += 1;
                Ok(Formula::Top)
            }
            Some('(') => {
                self.pos += 1;
                let a = self.formula()?;
                if !self.eat(')') {
                    return self.error("')' が必要です");
                }
                Ok(a)
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

/// `"<2>_2 <2>_3 T & D T"`、`"⟨2⟩₂⟨2⟩₃⊤ ∧ ↓⊤"`、`"<1>_w N p"` などを読む。
impl FromStr for Formula {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut p = Parser::new(s);
        let a = p.formula()?;
        p.finish()?;
        Ok(a)
    }
}

/// シーケント A ⊢ B。
#[derive(Clone, PartialEq, Eq, Hash, Debug, serde::Serialize)]
pub struct Sequent {
    pub lhs: Formula,
    pub rhs: Formula,
}

impl fmt::Display for Sequent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ⊢ {}", self.lhs, self.rhs)
    }
}

/// `"A |- B"` または `"A ⊢ B"` を読む。
impl FromStr for Sequent {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (l, r) = s.split_once("⊢").or_else(|| s.split_once("|-")).ok_or_else(|| ParseError {
            input: s.to_string(),
            pos: 0,
            msg: "'⊢' または '|-' が必要です".to_string(),
        })?;
        Ok(Sequent { lhs: l.parse()?, rhs: r.parse()? })
    }
}

// ----------------------------------------------------------------------
// 有限モデル M_A（§3, Def 3.9）
// ----------------------------------------------------------------------

/// 点の種類（Def 3.9）。
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PointKind {
    /// 式の構文木の点（tree point）
    Tree,
    /// ↓B ごとに 1 つ足す零点（zero point）
    Zero,
    /// ↓B ごとに、M_B で根から R¹₁ で行ける点の数だけ足す中間点（intermediate point）
    Intermediate,
    /// R² の行き先の点 b ごとに 1 つ足すコピー点 b↓（中身は b の番号）
    Copy(usize),
}

/// 前モデルの辺の種類。
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Edge {
    One(Rank),
    Two(u32),
    Down,
    Nabla,
}

impl Edge {
    /// 辺の rank（Def 3.7）：R↓・R∇ は 1、R^i_α は α。
    fn rank(self) -> Rank {
        match self {
            Edge::One(r) => r,
            Edge::Two(k) => Rank::Fin(k),
            Edge::Down | Edge::Nabla => Rank::Fin(1),
        }
    }
}

/// 前モデル M⁰_A を組み立てる道具。点は作った順に番号を振る。
struct Pre {
    kinds: Vec<PointKind>,
    edges: Vec<(usize, Edge, usize)>,
    n_fin: u32,
}

impl Pre {
    fn point(&mut self, k: PointKind) -> usize {
        self.kinds.push(k);
        self.kinds.len() - 1
    }

    /// 式 a の構造を、点 `root`（a の根）から下に付け足す。
    /// 連言は同じ根に両方を付け足すので、自然に「根の同一視」になる。
    fn build(&mut self, a: &Formula, root: usize) {
        match a {
            Formula::Top | Formula::Var(_) => {}
            Formula::And(b, c) => {
                self.build(b, root);
                self.build(c, root);
            }
            Formula::Dia(i, r, b) => {
                let x = self.point(PointKind::Tree);
                if *i == 1 {
                    self.edges.push((root, Edge::One(*r), x));
                } else {
                    let k = r.fin().expect("⟨2⟩ の添字は有限");
                    self.edges.push((root, Edge::Two(k), x));
                    // ⟨2⟩_α B の根には R¹_ω のループを付ける
                    self.edges.push((x, Edge::One(Rank::Omega), x));
                }
                self.build(b, x);
            }
            Formula::Nabla(b) => {
                let x = self.point(PointKind::Tree);
                self.edges.push((root, Edge::Nabla, x));
                self.build(b, x);
            }
            Formula::Down(b) => {
                let rb = self.point(PointKind::Tree);
                self.edges.push((root, Edge::Down, rb));
                self.build(b, rb);
                // M_B（閉包まで）を、B の点だけ（番号 rb..end）で作る
                let (start, end) = (rb, self.kinds.len());
                let sub = Pre {
                    kinds: self.kinds[start..end].to_vec(),
                    edges: self
                        .edges
                        .iter()
                        .filter(|(x, _, _)| (start..end).contains(x))
                        .map(|&(x, e, y)| (x - start, e, y - start))
                        .collect(),
                    n_fin: self.n_fin,
                };
                let mb = Model::from_pre(sub);
                // M_B で根から R¹₁ で行ける、前モデルの点 b_i
                let succ: Vec<usize> =
                    mb.r1[0][0].iter().filter(|&y| y < end - start).map(|y| y + start).collect();
                let z = self.point(PointKind::Zero);
                self.edges.push((root, Edge::One(Rank::Omega), z));
                for bi in succ {
                    let e = self.point(PointKind::Intermediate);
                    self.edges.push((root, Edge::One(Rank::Omega), e));
                    self.edges.push((e, Edge::Down, bi));
                }
            }
        }
    }
}

/// 閉包を取った有限モデル。点 0 が根。
///
/// 添字は 1..=N（N = `n_fin`）と ω だけを持つ。N は扱う式に現れる有限の添字の最大値
/// （少なくとも 2）にする。それより大きい有限の添字の関係は R¹_ω と一致する
/// （Lemma 4.9 の証明と同じ理由）ので、持たなくてよい。
#[derive(Clone, Debug)]
pub struct Model {
    n_fin: u32,
    kinds: Vec<PointKind>,
    /// 前モデルの点の数（これ以降の点はコピー点）
    n_pre: usize,
    /// anchor（Def 3.9 (2)）。前モデルの点だけ
    anchors: Vec<usize>,
    /// r1[s][x]：x の R¹_α 後続。s = α − 1（α = 1..=N）、s = N が ω
    r1: Vec<Vec<BitSet>>,
    /// r2[s][x]：x の R²_α 後続。s = α − 2（α = 2..=N）
    r2: Vec<Vec<BitSet>>,
    down: Vec<BitSet>,
    nabla: Vec<BitSet>,
}

impl Model {
    /// 変数のない式 A の有限モデル M_A（Def 3.9）。
    ///
    /// 1. 前モデル M⁰_A：A の構文木に、⟨2⟩ の行き先の R¹_ω ループと、↓ ごとの零点・中間点を足す。
    /// 2. R² の行き先の点 b ごとにコピー点 b↓ を足し、b↓ R¹_ω b、b⊤ R∇ b↓、b↓ R↓ b⊤
    ///    （b⊤ は b の anchor：rank ≥ 2 の辺を逆向きにたどった行き止まり）。
    /// 3. 規則 (a)〜(l) で閉包を取る。
    ///
    /// `n_fin` は持つ有限の添字の上限（A に現れる最大の添字より小さければ引き上げる）。
    pub fn of(a: &Formula, n_fin: u32) -> Model {
        let n_fin = n_fin.max(a.max_rank()).max(2);
        let mut pre = Pre { kinds: vec![PointKind::Tree], edges: Vec::new(), n_fin };
        pre.build(a, 0);
        Model::from_pre(pre)
    }

    /// 前モデルからコピー点を足して閉包を取る。
    fn from_pre(pre: Pre) -> Model {
        let Pre { mut kinds, mut edges, n_fin } = pre;
        let n_pre = kinds.len();

        // rank ≥ 2 の辺（ループを除く）で入ってくる親。各点に高々 1 本（論文の (P3)）
        let mut parent2: Vec<Option<usize>> = vec![None; n_pre];
        let mut is_r2 = vec![false; n_pre];
        for &(x, e, y) in &edges {
            if x != y && e.rank() >= Rank::Fin(2) {
                debug_assert!(parent2[y].is_none(), "(P3) に反する：点 {y} に rank ≥ 2 の辺が 2 本");
                parent2[y] = Some(x);
            }
            if let Edge::Two(_) = e {
                is_r2[y] = true;
            }
        }
        let anchors: Vec<usize> = (0..n_pre)
            .map(|b| {
                let mut a = b;
                while let Some(p) = parent2[a] {
                    a = p;
                }
                a
            })
            .collect();
        for b in 0..n_pre {
            if is_r2[b] {
                let c = kinds.len();
                kinds.push(PointKind::Copy(b));
                edges.push((c, Edge::One(Rank::Omega), b));
                edges.push((anchors[b], Edge::Nabla, c));
                edges.push((c, Edge::Down, anchors[b]));
            }
        }

        let n = kinds.len();
        let nf = n_fin as usize;
        let mut m = Model {
            n_fin,
            kinds,
            n_pre,
            anchors,
            r1: vec![vec![BitSet::new(n); n]; nf + 1],
            r2: vec![vec![BitSet::new(n); n]; nf - 1],
            down: vec![BitSet::new(n); n],
            nabla: vec![BitSet::new(n); n],
        };
        for (x, e, y) in edges {
            match e {
                Edge::One(r) => {
                    let s = m.slot1(r);
                    m.r1[s][x].insert(y);
                }
                Edge::Two(k) => {
                    m.r2[k as usize - 2][x].insert(y);
                }
                Edge::Down => {
                    m.down[x].insert(y);
                }
                Edge::Nabla => {
                    m.nabla[x].insert(y);
                }
            }
        }
        m.close();
        m
    }

    /// R¹_α の添字 α の格納位置。N より大きい有限の添字は ω と同じ扱い。
    fn slot1(&self, r: Rank) -> usize {
        match r {
            Rank::Fin(k) if k <= self.n_fin => k as usize - 1,
            _ => self.n_fin as usize,
        }
    }

    /// 規則 (a)〜(l) について、変化がなくなるまで閉包を取る。
    fn close(&mut self) {
        let n = self.kinds.len();
        let nf = self.n_fin as usize;
        let omega = nf; // r1 の ω の位置
        loop {
            let mut changed = false;

            // (a) R^i_α ⊆ R^i_β（β < α）と (b) R²_α ⊆ R¹_α：上の添字から順に下へ流す
            for s in (0..nf.saturating_sub(2)).rev() {
                for x in 0..n {
                    let upper = self.r2[s + 1][x].clone();
                    changed |= self.r2[s][x].union_with(&upper);
                }
            }
            for k in 2..=nf {
                for x in 0..n {
                    let row = self.r2[k - 2][x].clone();
                    changed |= self.r1[k - 1][x].union_with(&row);
                }
            }
            for s in (0..omega).rev() {
                for x in 0..n {
                    let upper = self.r1[s + 1][x].clone();
                    changed |= self.r1[s][x].union_with(&upper);
                }
            }
            // (c) R∇ は反射的、(d) R¹_α ⊆ R∇（R¹₁ がすべての R^i_α を含む）、(e) R↓ ⊆ R∇
            for x in 0..n {
                changed |= self.nabla[x].insert(x);
                let r11 = self.r1[0][x].clone();
                changed |= self.nabla[x].union_with(&r11);
                let d = self.down[x].clone();
                changed |= self.nabla[x].union_with(&d);
            }
            // (f) x R^i_α y R^j_α z ⇒ x R^j_α z（i は R¹_α ⊇ R²_α で代表させる）
            for s in 0..=omega {
                for x in 0..n {
                    let mids: Vec<usize> = self.r1[s][x].iter().collect();
                    for y in mids {
                        let row1 = self.r1[s][y].clone();
                        changed |= self.r1[s][x].union_with(&row1);
                        // j = 2 は 2 ≤ α ≤ N のとき
                        if (1..nf).contains(&s) {
                            let row2 = self.r2[s - 1][y].clone();
                            changed |= self.r2[s - 1][x].union_with(&row2);
                        }
                    }
                }
            }
            // (g) R∇ は推移的、(h) x R∇ y R¹_α z ⇒ x R¹₁ z、(i) x R¹_α y R∇ z ⇒ x R¹₁ z、
            // (j) x R↓ y R∇ z ⇒ x R↓ z
            for x in 0..n {
                let mids: Vec<usize> = self.nabla[x].iter().collect();
                for y in mids {
                    let rn = self.nabla[y].clone();
                    changed |= self.nabla[x].union_with(&rn);
                    let r11 = self.r1[0][y].clone();
                    changed |= self.r1[0][x].union_with(&r11);
                }
                let mids: Vec<usize> = self.r1[0][x].iter().collect();
                for y in mids {
                    let rn = self.nabla[y].clone();
                    changed |= self.r1[0][x].union_with(&rn);
                }
                let mids: Vec<usize> = self.down[x].iter().collect();
                for y in mids {
                    let rn = self.nabla[y].clone();
                    changed |= self.down[x].union_with(&rn);
                }
            }
            // (k) x R^i_α y かつ x R^j_β z（α > β、または α = β = ω）⇒ y R^j_β z。
            // α > β となる R^i_α 全体は R¹_{β+1} で代表させる（β = N なら ω）
            for s in 0..=omega {
                let above = if s == omega { omega } else { s + 1 };
                for x in 0..n {
                    let ys: Vec<usize> = self.r1[above][x].iter().collect();
                    let row1 = self.r1[s][x].clone();
                    let row2 = if (1..nf).contains(&s) { Some(self.r2[s - 1][x].clone()) } else { None };
                    for y in ys {
                        changed |= self.r1[s][y].union_with(&row1);
                        if let Some(r2) = &row2 {
                            changed |= self.r2[s - 1][y].union_with(r2);
                        }
                    }
                }
            }
            // (l) x R²_α y かつ x R^i_β z ⇒ y R↓ z（R²₂、R¹₁ がそれぞれ全体を含む）
            for x in 0..n {
                let ys: Vec<usize> = self.r2[0][x].iter().collect();
                let r11 = self.r1[0][x].clone();
                for y in ys {
                    changed |= self.down[y].union_with(&r11);
                }
            }

            if !changed {
                break;
            }
        }
    }

    // ------------------------------------------------------------------
    // 参照
    // ------------------------------------------------------------------

    pub fn num_points(&self) -> usize {
        self.kinds.len()
    }

    pub fn kind(&self, x: usize) -> PointKind {
        self.kinds[x]
    }

    pub fn n_fin(&self) -> u32 {
        self.n_fin
    }

    /// 前モデルの点 x の anchor。
    pub fn anchor(&self, x: usize) -> Option<usize> {
        (x < self.n_pre).then(|| self.anchors[x])
    }

    /// x の R^i_α 後続（持っていない添字なら `None`）。
    pub fn succ(&self, i: u8, alpha: Rank, x: usize) -> Option<&BitSet> {
        match (i, alpha) {
            (1, Rank::Omega) => Some(&self.r1[self.n_fin as usize][x]),
            (1, Rank::Fin(k)) if (1..=self.n_fin).contains(&k) => Some(&self.r1[k as usize - 1][x]),
            (2, Rank::Fin(k)) if (2..=self.n_fin).contains(&k) => Some(&self.r2[k as usize - 2][x]),
            _ => None,
        }
    }

    pub fn succ_down(&self, x: usize) -> &BitSet {
        &self.down[x]
    }

    pub fn succ_nabla(&self, x: usize) -> &BitSet {
        &self.nabla[x]
    }

    /// 持っているすべての関係（名前と行の組）。表示とフレーム条件の検査に使う。
    fn relations(&self) -> Vec<(String, &Vec<BitSet>)> {
        let mut out = Vec::new();
        for k in 1..=self.n_fin {
            out.push((format!("R¹{}", Rank::Fin(k)), &self.r1[k as usize - 1]));
        }
        out.push(("R¹_ω".to_string(), &self.r1[self.n_fin as usize]));
        for k in 2..=self.n_fin {
            out.push((format!("R²{}", Rank::Fin(k)), &self.r2[k as usize - 2]));
        }
        out.push(("R↓".to_string(), &self.down));
        out.push(("R∇".to_string(), &self.nabla));
        out
    }

    // ------------------------------------------------------------------
    // 充足
    // ------------------------------------------------------------------

    /// 式 b が真になる点の集合（変数はどこでも偽）。
    /// 持っていない有限の添字（N より大きい）は ω と同じ関係として扱う。
    pub fn truth_set(&self, b: &Formula) -> BitSet {
        let n = self.num_points();
        let diamond = |rows: &Vec<BitSet>, inner: &BitSet| {
            let mut out = BitSet::new(n);
            for (x, row) in rows.iter().enumerate() {
                if row.intersects(inner) {
                    out.insert(x);
                }
            }
            out
        };
        match b {
            Formula::Top => BitSet::full(n),
            Formula::Var(_) => BitSet::new(n),
            Formula::And(x, y) => {
                let mut s = self.truth_set(x);
                s.intersect_with(&self.truth_set(y));
                s
            }
            Formula::Dia(i, r, x) => {
                let inner = self.truth_set(x);
                let rows = match (i, r) {
                    (2, Rank::Fin(k)) if *k <= self.n_fin => &self.r2[*k as usize - 2],
                    (2, _) => return BitSet::new(n), // R²_k（k > N）は空
                    _ => &self.r1[self.slot1(*r)],
                };
                diamond(rows, &inner)
            }
            Formula::Down(x) => diamond(&self.down, &self.truth_set(x)),
            Formula::Nabla(x) => diamond(&self.nabla, &self.truth_set(x)),
        }
    }

    pub fn holds(&self, x: usize, b: &Formula) -> bool {
        self.truth_set(b).contains(x)
    }

    // ------------------------------------------------------------------
    // フレーム条件の検査（Def 2.12）
    // ------------------------------------------------------------------

    /// フレーム条件 I〜IV を全部調べ、破れているものを返す（空なら RC_BIω モデル）。
    /// 添字は持っているもの（1..=N と ω）について調べる。
    pub fn frame_violations(&self) -> Vec<String> {
        let n = self.num_points();
        let nf = self.n_fin;
        let mut v = Vec::new();
        // (i, α) の一覧（大きい順に並べる必要はない）
        let mut mods: Vec<(u8, Rank)> = (1..=nf).map(|k| (1, Rank::Fin(k))).collect();
        mods.push((1, Rank::Omega));
        mods.extend((2..=nf).map(|k| (2, Rank::Fin(k))));
        let rel = |i: u8, r: Rank| -> &Vec<BitSet> {
            match i {
                1 => &self.r1[self.slot1(r)],
                _ => &self.r2[r.fin().unwrap() as usize - 2],
            }
        };
        let subset = |a: &Vec<BitSet>, b: &Vec<BitSet>| (0..n).all(|x| a[x].iter().all(|y| b[x].contains(y)));
        // 合成 a;b ⊆ c
        let comp_in = |a: &Vec<BitSet>, b: &Vec<BitSet>, c: &Vec<BitSet>| {
            (0..n).all(|x| a[x].iter().all(|y| b[y].iter().all(|z| c[x].contains(z))))
        };
        let r11 = &self.r1[0];
        for &(i, a) in &mods {
            for &(j, b) in &mods {
                if i == j && b < a && !subset(rel(i, a), rel(i, b)) {
                    v.push(format!("I.1: R^{i}{a} ⊄ R^{i}{b}"));
                }
                // II.1
                if a == b && !comp_in(rel(i, a), rel(j, a), rel(j, a)) {
                    v.push(format!("II.1: R^{i}{a};R^{j}{a} ⊄ R^{j}{a}"));
                }
                // III.1
                if b < a || (a == Rank::Omega && b == Rank::Omega) {
                    for x in 0..n {
                        for y in rel(i, a)[x].iter() {
                            if !rel(j, b)[x].iter().all(|z| rel(j, b)[y].contains(z)) {
                                v.push(format!("III.1: {x}R^{i}{a}{y}, {x}R^{j}{b}z ⇒ {y}R^{j}{b}z が破れる"));
                            }
                        }
                    }
                }
            }
            if i == 2 && !subset(rel(2, a), rel(1, a)) {
                v.push(format!("I.2: R²{a} ⊄ R¹{a}"));
            }
            if i == 1 {
                if !subset(rel(1, a), &self.nabla) {
                    v.push(format!("I.4: R¹{a} ⊄ R∇"));
                }
                if !comp_in(&self.nabla, rel(1, a), r11) {
                    v.push(format!("II.3: R∇;R¹{a} ⊄ R¹₁"));
                }
                if !comp_in(rel(1, a), &self.nabla, r11) {
                    v.push(format!("II.4: R¹{a};R∇ ⊄ R¹₁"));
                }
            }
            // III.2
            if i == 2 {
                for &(j, b) in &mods {
                    if !comp_in_pair(n, rel(2, a), rel(j, b), &self.down) {
                        v.push(format!("III.2: R²{a} と R^{j}{b} から R↓ が出ない"));
                    }
                }
            }
        }
        if !(0..n).all(|x| self.nabla[x].contains(x)) {
            v.push("I.3: R∇ が反射的でない".to_string());
        }
        if !subset(&self.down, &self.nabla) {
            v.push("I.5: R↓ ⊄ R∇".to_string());
        }
        if !comp_in(&self.nabla, &self.nabla, &self.nabla) {
            v.push("II.2: R∇ が推移的でない".to_string());
        }
        if !comp_in(&self.down, &self.nabla, &self.down) {
            v.push("II.5: R↓;R∇ ⊄ R↓".to_string());
        }
        let r1w = &self.r1[nf as usize];
        // IV.1：R↓ の後続があれば R¹_ω の後続もある
        for (x, (d, w)) in self.down.iter().zip(r1w).enumerate() {
            if !d.is_empty() && w.is_empty() {
                v.push(format!("IV.1: 点 {x}"));
            }
        }
        // IV.2：x R↓ y R¹_α z ⇒ ∃d (x R¹_ω d ∧ d R↓ z)。R¹₁ が全 R¹_α を含む
        for (x, (dx, wx)) in self.down.iter().zip(r1w).enumerate() {
            for y in dx.iter() {
                for z in r11[y].iter() {
                    if !wx.iter().any(|d| self.down[d].contains(z)) {
                        v.push(format!("IV.2: {x}R↓{y}R¹{z}"));
                    }
                }
            }
        }
        // IV.3：x R²_α y ⇒ ∃c（x R∇ c、c R↓ x、y の後続はすべて c の後続）
        let rels = self.relations();
        for x in 0..n {
            for y in self.r2[0][x].iter() {
                let ok = (0..n).any(|c| {
                    self.nabla[x].contains(c)
                        && self.down[c].contains(x)
                        && rels.iter().all(|(_, r)| r[y].iter().all(|d| r[c].contains(d)))
                });
                if !ok {
                    v.push(format!("IV.3: {x}R²{y}"));
                }
            }
        }
        v
    }
}

/// x a y かつ x b z ⇒ y c z。
fn comp_in_pair(n: usize, a: &[BitSet], b: &[BitSet], c: &[BitSet]) -> bool {
    (0..n).all(|x| a[x].iter().all(|y| b[x].iter().all(|z| c[y].contains(z))))
}

impl fmt::Display for Model {
    /// 点の種類と、各関係の辺を表示する（R∇ の自己ループは省く）。
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "点（0 が根）:")?;
        for (x, k) in self.kinds.iter().enumerate() {
            let s = match k {
                PointKind::Tree => "構文木".to_string(),
                PointKind::Zero => "零点".to_string(),
                PointKind::Intermediate => "中間点".to_string(),
                PointKind::Copy(b) => format!("{b} のコピー点"),
            };
            let anchor = match self.anchor(x) {
                Some(a) if a != x => format!("（anchor {a}）"),
                _ => String::new(),
            };
            writeln!(f, "  {x}: {s}{anchor}")?;
        }
        writeln!(f, "関係:")?;
        for (name, rows) in self.relations() {
            let is_nabla = name == "R∇";
            let edges: Vec<String> = rows
                .iter()
                .enumerate()
                .flat_map(|(x, row)| {
                    row.iter().filter(move |&y| !(is_nabla && x == y)).map(move |y| format!("{x}→{y}"))
                })
                .collect();
            writeln!(f, "  {name}: {}", edges.join(" "))?;
        }
        Ok(())
    }
}

// ----------------------------------------------------------------------
// 判定
// ----------------------------------------------------------------------

/// 判定の結果。`model` は左辺の M_A で、偽なら反例（根で右辺が偽）。
#[derive(Clone, Debug)]
pub struct Decision {
    pub sequent: Sequent,
    pub holds: bool,
    pub model: Model,
}

/// 変数のない A, B について RC_BIω ⊢ A ⊢ B を判定する（Thm 3.19）。
/// A, B が ⟨1⟩_ω を含まなければ、RC_BI での判定と同じ（Prop 2.6）。
pub fn decide(lhs: &Formula, rhs: &Formula) -> Result<Decision, String> {
    if !lhs.is_closed() || !rhs.is_closed() {
        return Err("判定できるのは変数を含まない式だけです（論文の Thm 3.19）".to_string());
    }
    let model = Model::of(lhs, lhs.max_rank().max(rhs.max_rank()));
    let holds = model.holds(0, rhs);
    Ok(Decision { sequent: Sequent { lhs: lhs.clone(), rhs: rhs.clone() }, holds, model })
}

/// RC_BIω ⊢ A ⊢ B か（変数のない式のみ。変数があれば panic）。
pub fn entails(lhs: &Formula, rhs: &Formula) -> bool {
    decide(lhs, rhs).expect("変数のない式").holds
}

/// A ⊣⊢ B か。
pub fn equivalent(a: &Formula, b: &Formula) -> bool {
    entails(a, b) && entails(b, a)
}

/// 現れる添字の一覧（表示用）。
pub fn ranks(a: &Formula) -> BTreeSet<(u8, Rank)> {
    fn go(a: &Formula, out: &mut BTreeSet<(u8, Rank)>) {
        match a {
            Formula::Top | Formula::Var(_) => {}
            Formula::And(x, y) => {
                go(x, out);
                go(y, out);
            }
            Formula::Dia(i, r, x) => {
                out.insert((*i, *r));
                go(x, out);
            }
            Formula::Down(x) | Formula::Nabla(x) => go(x, out),
        }
    }
    let mut out = BTreeSet::new();
    go(a, &mut out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(s: &str) -> Formula {
        s.parse().unwrap_or_else(|e| panic!("{e}"))
    }

    fn proves(s: &str) -> bool {
        let q: Sequent = s.parse().unwrap();
        entails(&q.lhs, &q.rhs)
    }

    #[test]
    fn parse_and_display() {
        assert_eq!(f("<2>_2 <2>_3 T & D T").to_string(), "⟨2⟩₂⟨2⟩₃⊤ ∧ ↓⊤");
        assert_eq!(f("⟨2⟩₂⟨2⟩₃⊤ ∧ ↓⊤"), f("<2>_2 <2>_3 T & D T"));
        assert_eq!(f("<1>_w N p").to_string(), "⟨1⟩_ω∇p");
        assert_eq!(f("<1>T"), Formula::one(1, Formula::Top)); // 添字を省くと ⟨1⟩₁
        assert_eq!(f("<2>T"), Formula::two(2, Formula::Top)); // ⟨2⟩₂
        for s in ["⊤", "↓(⟨1⟩₁⊤ ∧ ⟨2⟩₃⊤)", "p ∧ (q ∧ r)", "⟨1⟩₁₂⊤", "∇↓⟨1⟩_ω⊤"] {
            assert_eq!(f(s).to_string().parse::<Formula>().unwrap(), f(s), "{s}");
        }
        assert!("<2>_1 T".parse::<Formula>().is_err()); // ⟨2⟩₁ はない
        assert!("<2>_w T".parse::<Formula>().is_err()); // ⟨2⟩_ω もない
        assert!("<3>T".parse::<Formula>().is_err());
        assert!(!f("<1>_w T").in_wbi() && f("<2>_2 D T").in_wbi());
    }

    #[test]
    fn small_models_are_models() {
        for s in ["⊤", "↓⊤", "⟨2⟩₂⊤", "↓⟨1⟩₁⊤", "⟨2⟩₂⟨2⟩₃⊤ ∧ ↓⊤", "↓↓⊤", "⟨2⟩₂↓⟨2⟩₂⊤", "∇⟨2⟩₃⟨1⟩_ω⊤"] {
            let m = Model::of(&f(s), 3);
            assert_eq!(m.frame_violations(), Vec::<String>::new(), "{s}\n{m}");
            assert!(m.holds(0, &f(s)), "{s}");
        }
    }

    #[test]
    fn axiom_examples() {
        assert!(proves("↓⊤ ⊢ ⟨1⟩_ω⊤")); // 13
        assert!(proves("↓⟨1⟩₁⊤ ⊢ ⟨1⟩_ω↓⊤")); // 14
        assert!(proves("⟨1⟩₁⊤ ∧ ⟨2⟩₂⊤ ⊢ ∇(↓⟨1⟩₁⊤ ∧ ⊤)")); // 15
        assert!(proves("⟨2⟩₃⊤ ∧ ⟨1⟩₁⊤ ⊢ ⟨2⟩₃↓⊤")); // 11
        assert!(proves("⟨2⟩₂⊤ ⊢ ⟨1⟩₁↓⊤")); // ACA₀⁺ は ACA の Π¹₁ 反射を示す
        assert!(!proves("⟨1⟩₁⊤ ⊢ ⟨1⟩₂⊤"));
        assert!(!proves("↓⊤ ⊢ ⟨2⟩₂⊤"));
        assert!(!proves("⊤ ⊢ ⟨1⟩₁⊤"));
    }

    #[test]
    fn known_order_from_section6() {
        // o の値：0 < 1 < ω < ε₀ < φ₂(0) < φ_ω(0) < Γ₀ < Γ_{ε₀}
        let chain = ["⊤", "⟨1⟩₁⊤", "⟨1⟩₂⊤", "↓⊤", "⟨2⟩₂⊤", "⟨2⟩₃⊤", "⟨2⟩₂⟨2⟩₃⊤", "⟨2⟩₂⟨2⟩₃⊤ ∧ ↓⊤"];
        for (i, a) in chain.iter().enumerate() {
            for (j, b) in chain.iter().enumerate() {
                // a <¹₁ b ⟺ b ⊢ ⟨1⟩₁a
                let lt = entails(&f(b), &Formula::one(1, f(a)));
                assert_eq!(lt, i < j, "{a} <¹₁ {b} の判定");
            }
        }
    }
}
