//! 順序数の式の標準形：足し算・掛け算・べき乗、Veblen 関数 φ、ε、超指数関数 e^α、崩壊関数 ψ
//! （と ω・Ω・自然数）でできた式を読み、内側から 1 段ずつ標準形（[`Veblen`]）にする。
//! 各段で使った定義・規則を記録する（Web の「式の標準形」のカード、CLI の `wormlab expr`）。
//!
//! # 使う定義（[`definitions`] が出典つきの一覧を返す）
//! - 足し算・掛け算・べき乗：ふつうの順序数の演算（右の引数についての再帰と、極限での上限）。
//!   計算は [`crate::arith`]（Cantor 標準形の上で）。
//! - Veblen 関数（2 変数）：φ(0, β) = ω^β、α > 0 なら φ(α, ·) は「すべての γ < α で
//!   φ(γ, ·) の不動点になる数」を小さい順に並べる関数。ε_β = φ(1, β)。
//! - 超指数関数：e(ξ) = −1 + ω^ξ の hyperation e^α（Fernández-Duque & Joosten, arXiv:1205.2036）。
//!   e^0 = id、e^1 = e、e^{α+β} = e^α ∘ e^β を満たすものの中で最小のもの。
//!   計算は α の Cantor 標準形で e^α = (e^{ω^{α₁}})^{c₁} ∘ … ∘ (e^{ω^{αₙ}})^{cₙ}、
//!   γ ≥ 1 なら e^{ω^γ}(0) = 0、e^{ω^γ}(1 + β) = φ(γ, β)（[`crate::transfinite::e_sub`]）。
//! - 崩壊関数 ψ：Worms and spiders（arXiv:1605.08867）Def 6.19。C(ξ) は {0, 1, Ω} を含み、
//!   + と φ と ψ↾ξ で閉じた最小の集合、ψ(ξ) は C(ξ) に入らない最小の数（[`Veblen::psi`]）。
//!
//! # 式の書き方
//! ```text
//!   expr  := term ('+' term)*
//!   term  := power (('·' | '*' | '×') power)*
//!   power := atom ('^' power)?                      （べきは右結合：ω^ω^ω = ω^(ω^ω)）
//!   atom  := 自然数 | 'ω' | 'w' | 'Ω' | 'O'
//!          | ('φ' | 'phi') '(' expr ',' expr ')'
//!          | ('ε' | 'e') '_' power                   （ε_α = φ(1, α)）
//!          | 'e' '^' power '(' expr ')'              （e^α(β)。'e' '(' expr ')' は e^1）
//!          | ('ψ' | 'psi') '(' expr ')'
//!          | '(' expr ')' | '{' expr '}'
//! ```
//! [`Veblen`] の表示（`ω^(ω + 1)·2 + 3`、`ε_(Ω + 1)`、`ψ(Ω·2)` など）はそのまま読める。

use crate::arith::{self, ArithError, Op};
use crate::i18n::{is_en, tr};
use crate::latex::ToLatex;
use crate::transfinite;
use crate::veblen::Veblen;
use std::fmt;

/// 式の文字数の上限（Web で固まらないように）。
pub const MAX_INPUT: usize = 1_000;
/// 超指数関数で e^{ω^γ} を適用する回数の上限（e^1000000(1) のような式で固まらないように）。
pub const MAX_HYPER_STEPS: u64 = 10_000;
/// 1 つの段の補足（超指数関数の適用など）に書く行数の上限。
const MAX_DETAILS: usize = 40;

/// 順序数の式。計算の途中では、計算済みの部分を [`Expr::Val`] に置き換えていく。
///
/// 【Rust メモ】`Box<Expr>` は「ヒープに置いた Expr」。enum が自分自身を中に持つ（再帰する）ときは、
/// 大きさが決まるように Box で包む
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Nat(u64),
    /// ω
    Omega,
    /// Ω
    BigOmega,
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Pow(Box<Expr>, Box<Expr>),
    /// φ(α, β)
    Phi(Box<Expr>, Box<Expr>),
    /// ε_α
    Eps(Box<Expr>),
    /// e^α(β)
    Hyp(Box<Expr>, Box<Expr>),
    /// ψ(α)
    Psi(Box<Expr>),
    /// 計算済み（標準形）
    Val(Veblen),
}

fn bx(e: Expr) -> Box<Expr> {
    Box::new(e)
}

impl Expr {
    /// 1 か（書いた 1 でも、計算した値の 1 でも）。e^1 を e と書くのに使う。
    fn is_one(&self) -> bool {
        match self {
            Expr::Nat(n) => *n == 1,
            Expr::Val(v) => v.as_nat() == Some(1),
            _ => false,
        }
    }

    /// 子の数。
    fn arity(&self) -> usize {
        match self {
            Expr::Nat(_) | Expr::Omega | Expr::BigOmega | Expr::Val(_) => 0,
            Expr::Eps(_) | Expr::Psi(_) => 1,
            _ => 2,
        }
    }

    /// i 番目の子（書き換えられる形で）。
    fn child_mut(&mut self, i: usize) -> &mut Expr {
        match self {
            Expr::Add(a, b) | Expr::Mul(a, b) | Expr::Pow(a, b) | Expr::Phi(a, b) | Expr::Hyp(a, b) => {
                if i == 0 { a } else { b }
            }
            Expr::Eps(a) | Expr::Psi(a) => a,
            _ => unreachable!("葉に子はない"),
        }
    }

    /// 根からの道 path の先の部分式。
    fn at(&mut self, path: &[usize]) -> &mut Expr {
        let mut cur = self;
        for &i in path {
            cur = cur.child_mut(i);
        }
        cur
    }
}

// ----------------------------------------------------------------------
// 表示（ふつうの文字と LaTeX）
// ----------------------------------------------------------------------

// 結合の強さ：和 < 積 < べき < それ以上分けられないもの
const SUM: u8 = 0;
const PROD: u8 = 1;
const POW: u8 = 2;
const ATOM: u8 = 3;

/// 標準形の数を式の中に置くときの結合の強さ（Veblen の表示に合わせる）。
fn val_prec(v: &Veblen) -> u8 {
    if v.is_finite() {
        return ATOM;
    }
    let terms: Vec<(Veblen, u64)> = v.principal_terms().collect();
    if terms.len() > 1 {
        return SUM;
    }
    let (p, c) = &terms[0];
    if *c > 1 {
        return PROD;
    }
    // ω^x と ε_x は、後ろに ^ が続くと指数・添字の一部に読まれるので、べきと同じ強さにする
    match p.phi_parts() {
        Some((a, b)) if a.is_zero() && b != Veblen::one() => POW,
        Some((a, _)) if a == Veblen::one() => POW,
        _ => ATOM,
    }
}

/// ε_ や e^ の後ろにかっこなしで書ける短いもの（自然数・ω・Ω）か。
fn is_short(e: &Expr) -> bool {
    match e {
        Expr::Nat(_) | Expr::Omega | Expr::BigOmega => true,
        Expr::Val(v) => v.is_finite() || *v == Veblen::omega() || *v == Veblen::big_omega(),
        _ => false,
    }
}

impl Expr {
    fn prec(&self) -> u8 {
        match self {
            Expr::Add(..) => SUM,
            Expr::Mul(..) => PROD,
            // ε_α の α はべきまで読む（ε_ω^2 = ε_(ω^2)）ので、ε_α の後ろに ^ を書くにはかっこが要る
            Expr::Pow(..) | Expr::Eps(_) => POW,
            Expr::Val(v) => val_prec(v),
            _ => ATOM,
        }
    }

    fn wrap(&self, min: u8) -> String {
        if self.prec() < min { format!("({self})") } else { self.to_string() }
    }

    fn wrap_tex(&self, min: u8) -> String {
        if self.prec() < min { format!("\\left({}\\right)", self.to_latex()) } else { self.to_latex() }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Nat(n) => write!(f, "{n}"),
            Expr::Omega => write!(f, "ω"),
            Expr::BigOmega => write!(f, "Ω"),
            Expr::Add(a, b) => write!(f, "{} + {}", a.wrap(SUM), b.wrap(SUM)),
            Expr::Mul(a, b) => write!(f, "{}·{}", a.wrap(PROD), b.wrap(PROD)),
            Expr::Pow(a, b) => write!(f, "{}^{}", a.wrap(ATOM), b.wrap(POW)),
            Expr::Phi(a, b) => write!(f, "φ({a}, {b})"),
            Expr::Eps(a) if is_short(a) => write!(f, "ε_{a}"),
            Expr::Eps(a) => write!(f, "ε_({a})"),
            // e^1 は e と書く（読むときも 'e' '(' は e^1）
            Expr::Hyp(a, b) if a.is_one() => write!(f, "e({b})"),
            Expr::Hyp(a, b) if is_short(a) => write!(f, "e^{a}({b})"),
            Expr::Hyp(a, b) => write!(f, "e^({a})({b})"),
            Expr::Psi(a) => write!(f, "ψ({a})"),
            Expr::Val(v) => write!(f, "{v}"),
        }
    }
}

impl ToLatex for Expr {
    fn to_latex(&self) -> String {
        match self {
            Expr::Nat(n) => n.to_string(),
            Expr::Omega => "\\omega".to_string(),
            Expr::BigOmega => "\\Omega".to_string(),
            Expr::Add(a, b) => format!("{} + {}", a.wrap_tex(SUM), b.wrap_tex(SUM)),
            Expr::Mul(a, b) => format!("{} \\cdot {}", a.wrap_tex(PROD), b.wrap_tex(PROD)),
            Expr::Pow(a, b) => format!("{}^{{{}}}", a.wrap_tex(ATOM), b.to_latex()),
            Expr::Phi(a, b) => format!("\\varphi({}, {})", a.to_latex(), b.to_latex()),
            Expr::Eps(a) => format!("\\varepsilon_{{{}}}", a.to_latex()),
            Expr::Hyp(a, b) if a.is_one() => format!("e({})", b.to_latex()),
            Expr::Hyp(a, b) => format!("e^{{{}}}({})", a.to_latex(), b.to_latex()),
            Expr::Psi(a) => format!("\\psi({})", a.to_latex()),
            Expr::Val(v) => v.to_latex(),
        }
    }
}

// ----------------------------------------------------------------------
// パーサ
// ----------------------------------------------------------------------

/// 式として読めなかった。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseExprError(pub String);

impl fmt::Display for ParseExprError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", tr("式として読めません", "cannot read as an expression"), self.0)
    }
}

impl std::error::Error for ParseExprError {}

struct Parser {
    s: Vec<char>,
    i: usize,
}

type PResult<T> = Result<T, ParseExprError>;

impl Parser {
    fn ws(&mut self) {
        while self.s.get(self.i).is_some_and(|c| c.is_whitespace()) {
            self.i += 1;
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.ws();
        self.s.get(self.i).copied()
    }

    /// 空白を飛ばさずに、今の位置の次の文字。
    fn next_raw(&self, k: usize) -> Option<char> {
        self.s.get(self.i + k).copied()
    }

    fn eat(&mut self, c: char) -> bool {
        if self.peek() == Some(c) {
            self.i += 1;
            true
        } else {
            false
        }
    }

    fn eat_str(&mut self, t: &str) -> bool {
        self.ws();
        let t: Vec<char> = t.chars().collect();
        if self.s[self.i..].starts_with(&t) {
            self.i += t.len();
            true
        } else {
            false
        }
    }

    fn err<T>(&self, what: &str) -> PResult<T> {
        let rest: String = self.s[self.i.min(self.s.len())..].iter().collect();
        Err(ParseExprError(match (rest.is_empty(), is_en()) {
            (true, true) => format!("{what} expected at the end"),
            (true, false) => format!("式の終わりに {what} が必要です"),
            (false, true) => format!("{what} expected near “{rest}”"),
            (false, false) => format!("「{rest}」の付近で {what} が必要です"),
        }))
    }

    fn expect(&mut self, c: char) -> PResult<()> {
        if self.eat(c) { Ok(()) } else { self.err(&format!("'{c}'")) }
    }

    fn nat(&mut self) -> PResult<Option<u64>> {
        self.ws();
        let start = self.i;
        while self.s.get(self.i).is_some_and(|c| c.is_ascii_digit()) {
            self.i += 1;
        }
        if start == self.i {
            return Ok(None);
        }
        let t: String = self.s[start..self.i].iter().collect();
        t.parse().map(Some).map_err(|_| ParseExprError(tr("自然数が大きすぎます（2^64 未満）", "a natural number is too large (below 2^64)").to_string()))
    }

    fn expr(&mut self) -> PResult<Expr> {
        let mut a = self.term()?;
        while self.eat('+') {
            a = Expr::Add(bx(a), bx(self.term()?));
        }
        Ok(a)
    }

    fn term(&mut self) -> PResult<Expr> {
        let mut a = self.power()?;
        while self.eat('·') || self.eat('*') || self.eat('×') {
            a = Expr::Mul(bx(a), bx(self.power()?));
        }
        Ok(a)
    }

    fn power(&mut self) -> PResult<Expr> {
        let base = self.atom()?;
        if self.eat('^') {
            return Ok(Expr::Pow(bx(base), bx(self.power()?)));
        }
        Ok(base)
    }

    fn atom(&mut self) -> PResult<Expr> {
        if let Some(n) = self.nat()? {
            return Ok(Expr::Nat(n));
        }
        if self.eat_str("phi") || self.eat('φ') || self.eat('ϕ') {
            self.expect('(')?;
            let a = self.expr()?;
            self.expect(',')?;
            let b = self.expr()?;
            self.expect(')')?;
            return Ok(Expr::Phi(bx(a), bx(b)));
        }
        if self.eat_str("psi") || self.eat('ψ') {
            self.expect('(')?;
            let a = self.expr()?;
            self.expect(')')?;
            return Ok(Expr::Psi(bx(a)));
        }
        if self.eat('Ω') || self.eat('O') {
            return Ok(Expr::BigOmega);
        }
        if self.eat('ω') || self.eat('w') {
            return Ok(Expr::Omega);
        }
        if self.eat('ε') {
            self.expect('_')?;
            return Ok(Expr::Eps(bx(self.power()?)));
        }
        // 'e' の後ろは '_'（ε）か '^'（超指数関数）か '('（e^1）
        if self.peek() == Some('e') && matches!(self.next_raw(1), Some('_' | '^' | '(')) {
            self.i += 1;
            if self.eat('_') {
                return Ok(Expr::Eps(bx(self.power()?)));
            }
            let alpha = if self.eat('^') { self.power()? } else { Expr::Nat(1) };
            self.expect('(')?;
            let beta = self.expr()?;
            self.expect(')')?;
            return Ok(Expr::Hyp(bx(alpha), bx(beta)));
        }
        if self.eat('(') {
            let x = self.expr()?;
            self.expect(')')?;
            return Ok(x);
        }
        if self.eat('{') {
            let x = self.expr()?;
            self.expect('}')?;
            return Ok(x);
        }
        self.err(tr("数・ω・Ω・φ(…)・ε_…・e^…(…)・ψ(…)・かっこ", "a number, ω, Ω, φ(…), ε_…, e^…(…), ψ(…) or a parenthesis"))
    }
}

impl std::str::FromStr for Expr {
    type Err = ParseExprError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.chars().count() > MAX_INPUT {
            return Err(ParseExprError(if is_en() {
                format!("the expression is too long (at most {MAX_INPUT} characters)")
            } else {
                format!("式が長すぎます（{MAX_INPUT} 文字まで）")
            }));
        }
        let mut p = Parser { s: s.chars().collect(), i: 0 };
        let e = p.expr()?;
        if p.peek().is_some() {
            return p.err(tr("式の終わり", "the end of the expression"));
        }
        Ok(e)
    }
}

// ----------------------------------------------------------------------
// 計算
// ----------------------------------------------------------------------

/// 計算できなかった理由。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprError {
    Arith(ArithError),
    /// 超指数関数の適用の回数が多すぎる
    TooManyApplications(u64),
}

impl fmt::Display for ExprError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExprError::Arith(e) => write!(f, "{e}"),
            ExprError::TooManyApplications(n) => {
                if is_en() {
                    write!(f, "the hyperexponential would apply e^(ω^γ) {n} times (at most {MAX_HYPER_STEPS})")
                } else {
                    write!(f, "超指数関数で e^(ω^γ) を {n} 回適用することになります（{MAX_HYPER_STEPS} 回まで）")
                }
            }
        }
    }
}

impl std::error::Error for ExprError {}

impl From<ArithError> for ExprError {
    fn from(e: ArithError) -> Self {
        ExprError::Arith(e)
    }
}

/// 計算の 1 段：部分式 node を標準形 value にした。
#[derive(Clone, Debug)]
pub struct Step {
    /// 計算した部分式（子はすでに標準形）
    pub node: String,
    pub node_latex: String,
    /// その標準形
    pub value: Veblen,
    /// 使った定義・規則（1 行）
    pub rule: String,
    /// 補足（掛け算・べき乗の途中、超指数関数の適用、ψ の崩し）
    pub details: Vec<String>,
    /// この段のあとの式全体
    pub whole: String,
    pub whole_latex: String,
}

/// 式の計算の結果。
#[derive(Clone, Debug)]
pub struct Eval {
    /// 読んだ式（書き方を整えたもの）
    pub input: String,
    pub input_latex: String,
    pub value: Veblen,
    pub steps: Vec<Step>,
}

impl Eval {
    /// 式全体の書き換えを `align*` で（式が変わった段だけ）。
    pub fn latex(&self) -> String {
        let mut lines: Vec<String> = Vec::new();
        let mut last = self.input_latex.clone();
        for st in &self.steps {
            if st.whole_latex != last {
                lines.push(st.whole_latex.clone());
                last = st.whole_latex.clone();
            }
        }
        if lines.is_empty() {
            lines.push(self.value.to_latex());
        }
        let mut out = String::from("\\begin{align*}\n");
        for (i, l) in lines.iter().enumerate() {
            let lhs = if i == 0 { self.input_latex.as_str() } else { "" };
            let end = if i + 1 < lines.len() { " \\\\" } else { "" };
            out.push_str(&format!("{lhs} &= {l}{end}\n"));
        }
        out.push_str("\\end{align*}");
        out
    }
}

/// 式を読んで計算する。
pub fn eval_str(s: &str) -> Result<Eval, String> {
    let e: Expr = s.parse().map_err(|e: ParseExprError| e.to_string())?;
    evaluate(&e).map_err(|e| e.to_string())
}

/// 順序数の入力を読む。まずふつうの書き方（[`Veblen`] のパーサ。`ω^(ω + 1)·2 + 3`・`φ(2, 0)`・`ψ(ε_(Ω + 1))` など）で読み、
/// 読めなければ式として計算して標準形にする。だから `Ω^Ω`・`ψ(Ω^Ω)`・`ε_0·ω`・`(ω + 1)^2`・`e^ω(1)` のように、
/// ふつうの書き方にない演算（順序数どうしの掛け算・べき乗、超指数関数）も書ける。
/// どちらでも読めなければ、式としてのエラーを返す（式の文法はふつうの書き方を含むので、こちらの方が詳しい）。
/// 計算の大きさの上限（[`arith::MAX_SIZE`]）は式の計算と同じ。
pub fn parse_ordinal(s: &str) -> Result<Veblen, String> {
    if let Ok(v) = s.parse::<Veblen>() {
        return Ok(v);
    }
    eval_str(s).map(|e| e.value)
}

/// 式を内側から 1 段ずつ標準形にする。
pub fn evaluate(e: &Expr) -> Result<Eval, ExprError> {
    let mut root = e.clone();
    let mut steps = Vec::new();
    let mut path = Vec::new();
    let value = eval_at(&mut root, &mut path, &mut steps)?;
    Ok(Eval { input: e.to_string(), input_latex: e.to_latex(), value, steps })
}

fn val(e: &Expr) -> &Veblen {
    match e {
        Expr::Val(v) => v,
        _ => unreachable!("子は計算済み"),
    }
}

fn check(v: Veblen) -> Result<Veblen, ExprError> {
    if v.size() > arith::MAX_SIZE { Err(ArithError::TooLarge.into()) } else { Ok(v) }
}

/// 道 path の先の部分式を計算し、[`Expr::Val`] に置き換える（子から先に）。
fn eval_at(root: &mut Expr, path: &mut Vec<usize>, steps: &mut Vec<Step>) -> Result<Veblen, ExprError> {
    for i in 0..root.at(path).arity() {
        path.push(i);
        eval_at(root, path, steps)?;
        path.pop();
    }
    let node = root.at(path).clone();
    let leaf = match &node {
        Expr::Nat(n) => Some(Veblen::nat(*n)),
        Expr::Omega => Some(Veblen::omega()),
        Expr::BigOmega => Some(Veblen::big_omega()),
        Expr::Val(v) => Some(v.clone()),
        _ => None,
    };
    if let Some(v) = leaf {
        *root.at(path) = Expr::Val(v.clone());
        return Ok(v);
    }
    let (value, rule, details) = apply(&node)?;
    let value = check(value)?;
    *root.at(path) = Expr::Val(value.clone());
    steps.push(Step {
        node: node.to_string(),
        node_latex: node.to_latex(),
        value: value.clone(),
        rule,
        details,
        whole: root.to_string(),
        whole_latex: root.to_latex(),
    });
    Ok(value)
}

/// 子がすべて標準形の部分式を 1 段計算する：(値, 規則, 補足)。
fn apply(node: &Expr) -> Result<(Veblen, String, Vec<String>), ExprError> {
    Ok(match node {
        Expr::Add(a, b) => {
            let (a, b) = (val(a), val(b));
            let v = arith::add(a, b)?;
            (v.clone(), add_rule(a, b, &v), Vec::new())
        }
        Expr::Mul(a, b) | Expr::Pow(a, b) => {
            let op = if matches!(node, Expr::Mul(..)) { Op::Mul } else { Op::Pow };
            let c = arith::calc(op, val(a), val(b))?;
            let rule = match op {
                Op::Mul => tr(
                    "掛け算（α·0 = 0、α·(β + 1) = α·β + α、β が極限なら上限）",
                    "multiplication (α·0 = 0, α·(β + 1) = α·β + α, the supremum at limits β)",
                ),
                _ => tr(
                    "べき乗（α^0 = 1、α^(β + 1) = α^β·α、β が極限なら上限。0^β = 0（β ≥ 1）、1^β = 1）",
                    "exponentiation (α^0 = 1, α^(β + 1) = α^β·α, the supremum at limits β; 0^β = 0 for β ≥ 1, 1^β = 1)",
                ),
            };
            let details = c.steps.iter().map(|s| format!("= {}{}{}{}", s.plain, tr("（", " ("), s.note, tr("）", ")"))).collect();
            (c.result, rule.to_string(), details)
        }
        Expr::Phi(a, b) => {
            let (a, b) = (val(a), val(b));
            let v = Veblen::phi(a.clone(), b.clone());
            (v.clone(), phi_rule(a, b, &v), Vec::new())
        }
        Expr::Eps(a) => {
            let a = val(a);
            let v = Veblen::epsilon(a.clone());
            let rule = format!("{} {}", tr("ε_α = φ(1, α)。", "ε_α = φ(1, α)."), phi_rule(&Veblen::one(), a, &v));
            (v, rule, Vec::new())
        }
        Expr::Hyp(a, b) => {
            let (v, details) = hyper(val(a), val(b))?;
            let rule = tr(
                "超指数関数：α = ω^{α₁}·c₁ + … + ω^{αₙ}·cₙ（Cantor 標準形）なら e^α = (e^{ω^{α₁}})^{c₁} ∘ … ∘ (e^{ω^{αₙ}})^{cₙ}。右（小さい項）から順に適用する（e^{μ+ν} = e^μ ∘ e^ν）",
                "hyperexponential: for α = ω^{α₁}·c₁ + … + ω^{αₙ}·cₙ (Cantor normal form), e^α = (e^{ω^{α₁}})^{c₁} ∘ … ∘ (e^{ω^{αₙ}})^{cₙ}, applied from the right (smallest term first), since e^{μ+ν} = e^μ ∘ e^ν",
            );
            (v, rule.to_string(), details)
        }
        Expr::Psi(x) => {
            let x = val(x);
            let v = Veblen::psi(x.clone());
            (v.clone(), psi_rule(x, &v), Vec::new())
        }
        _ => unreachable!("葉は eval_at で扱う"),
    })
}

fn add_rule(a: &Veblen, b: &Veblen, v: &Veblen) -> String {
    if b.is_zero() {
        tr("α + 0 = α", "α + 0 = α").to_string()
    } else if !a.is_zero() && v == b {
        tr(
            "α の項はすべて β の先頭の主項より小さいので吸収される（α + β = β。例：1 + ω = ω）",
            "every term of α is below the leading principal term of β, so α is absorbed (α + β = β; e.g. 1 + ω = ω)",
        )
        .to_string()
    } else {
        tr(
            "足し算：β の先頭の主項より小さい α の項は消え、同じ主項なら係数を足す",
            "addition: the terms of α below the leading principal term of β vanish, and equal principal terms add their coefficients",
        )
        .to_string()
    }
}

fn phi_rule(a: &Veblen, b: &Veblen, v: &Veblen) -> String {
    if !b.is_zero() && v == b {
        if a.is_zero() {
            tr(
                "ω^β = β：β は ε 数（φ(γ, δ)、γ ≥ 1）か強臨界数（Ω・ψ(…)）なので、φ(0, ·) の不動点",
                "ω^β = β: β is an ε-number (φ(γ, δ) with γ ≥ 1) or strongly critical (Ω, ψ(…)), so a fixed point of φ(0, ·)",
            )
            .to_string()
        } else {
            tr(
                "β は φ(α, ·) の不動点（β = φ(γ, δ) で γ > α、または β が α より大きい強臨界数 Ω・ψ(…)）なので φ(α, β) = β",
                "β is a fixed point of φ(α, ·) (β = φ(γ, δ) with γ > α, or β a strongly critical Ω, ψ(…) above α), so φ(α, β) = β",
            )
            .to_string()
        }
    } else if b.is_zero() && !a.is_zero() && v == a {
        tr("φ(s, 0) = s（s = α は強臨界数：Ω・ψ(…) は φ(s, 0) の形をしている）", "φ(s, 0) = s (s = α is strongly critical: Ω and ψ(…) have the form φ(s, 0))")
            .to_string()
    } else if a.is_zero() {
        tr("φ(0, β) = ω^β（Veblen 関数の定義）", "φ(0, β) = ω^β (definition of the Veblen function)").to_string()
    } else {
        tr(
            "φ(α, β)（α > 0）は、すべての γ < α について φ(γ, ·) の不動点になる数の β 番目（0 番目から）。β < φ(α, β) なので標準形の主項",
            "φ(α, β) (α > 0) is the β-th (from 0) common fixed point of all φ(γ, ·), γ < α. Since β < φ(α, β), it is a principal term in normal form",
        )
        .to_string()
    }
}

fn psi_rule(x: &Veblen, v: &Veblen) -> String {
    let k = x.max_k();
    if x.in_c(x) {
        match k {
            None => tr(
                "ξ は ψ を含まないので K(ξ) = ∅。よって ξ ∈ C(ξ) で、ψ(ξ) は標準形",
                "ξ contains no ψ, so K(ξ) = ∅. Hence ξ ∈ C(ξ) and ψ(ξ) is in normal form",
            )
            .to_string(),
            Some(k) => {
                if is_en() {
                    format!("the largest element of K(ξ) is {k} < ξ, so ξ ∈ C(ξ) and ψ(ξ) is in normal form")
                } else {
                    format!("K(ξ) の最大は {k} < ξ なので ξ ∈ C(ξ)。ψ(ξ) は標準形")
                }
            }
        }
    } else {
        let k = k.expect("ξ ∉ C(ξ) なら K(ξ) は空でない");
        let z = v.as_psi().expect("ψ の値は ψ(z) の形");
        if is_en() {
            format!(
                "the largest element of K(ξ) is {k} ≥ ξ, so ξ ∉ C(ξ). The least z ≥ ξ with z ∈ C(z) is {z}; C(·) is constant on [ξ, z], so ψ(ξ) = ψ(z)"
            )
        } else {
            format!("K(ξ) の最大は {k} ≥ ξ なので ξ ∉ C(ξ)。ξ 以上で z ∈ C(z) となる最小の z は {z} で、C(·) は [ξ, z] で変わらないので ψ(ξ) = ψ(z)")
        }
    }
}

/// e^{ω^γ} の書き方（γ = 0 なら e、γ = 1 なら e^ω）。
fn hyp_name(g: &Veblen) -> String {
    if g.is_zero() {
        return "e".to_string();
    }
    let t = Veblen::omega_pow(g.clone()).to_string();
    if t == "ω" { "e^ω".to_string() } else { format!("e^({t})") }
}

/// e^α(β) を、e^{ω^γ} を 1 回ずつ適用して計算する（補足に各回を書く）。
fn hyper(alpha: &Veblen, beta: &Veblen) -> Result<(Veblen, Vec<String>), ExprError> {
    let cnf = alpha.cnf();
    let total = cnf.iter().fold(0u64, |s, (_, c)| s.saturating_add(*c));
    if total > MAX_HYPER_STEPS {
        return Err(ExprError::TooManyApplications(total));
    }
    let mut x = beta.clone();
    let mut details = Vec::new();
    let mut count = 0u64;
    for (g, c) in cnf.iter().rev() {
        for _ in 0..*c {
            let y = check(transfinite::e_sub(g, &x))?;
            if details.len() < MAX_DETAILS {
                let why = if x.is_zero() {
                    tr("e^{ω^γ}(0) = 0", "e^{ω^γ}(0) = 0")
                } else if g.is_zero() {
                    tr("e(ξ) = −1 + ω^ξ", "e(ξ) = −1 + ω^ξ")
                } else {
                    tr("e^{ω^γ}(1 + β) = φ(γ, β)", "e^{ω^γ}(1 + β) = φ(γ, β)")
                };
                details.push(format!("{}({x}) = {y}{}{why}{}", hyp_name(g), tr("（", " ("), tr("）", ")")));
            }
            count += 1;
            x = y;
        }
    }
    if count as usize > MAX_DETAILS {
        let rest = count - MAX_DETAILS as u64;
        details.push(if is_en() { format!("… ({rest} more)") } else { format!("…（あと {rest} 回）") });
    }
    if count == 0 {
        details.push(tr("e^0 は恒等写像", "e^0 is the identity").to_string());
    }
    Ok((x, details))
}

// ----------------------------------------------------------------------
// 定義の一覧
// ----------------------------------------------------------------------

/// 使う定義 1 つ（画面の一覧と CLI の `defs` に）。
#[derive(Clone, Debug, serde::Serialize)]
pub struct Definition {
    pub key: &'static str,
    /// 例 `φ(α, β)`
    pub symbol: String,
    pub name: String,
    pub lines: Vec<String>,
    pub source: String,
}

fn def(key: &'static str, symbol: &str, name: (&str, &str), lines: &[(&str, &str)], source: (&str, &str)) -> Definition {
    Definition {
        key,
        symbol: symbol.to_string(),
        name: tr(name.0, name.1).to_string(),
        lines: lines.iter().map(|(j, e)| tr(j, e).to_string()).collect(),
        source: tr(source.0, source.1).to_string(),
    }
}

/// 式の計算で使う定義の一覧（今の言語で）。
pub fn definitions() -> Vec<Definition> {
    vec![
        def(
            "add",
            "α + β",
            ("足し算", "Addition"),
            &[
                ("α + 0 = α、α + (β + 1) = (α + β) + 1、β が極限なら α + β = sup_{γ<β} (α + γ)", "α + 0 = α, α + (β + 1) = (α + β) + 1, and α + β = sup_{γ<β} (α + γ) for limit β"),
                (
                    "標準形では：β の先頭の主項を P とすると、α の主項のうち P より小さいものは消え（1 + ω = ω）、P と同じものは係数を足す",
                    "On normal forms: with P the leading principal term of β, the principal terms of α below P vanish (1 + ω = ω) and those equal to P add their coefficients",
                ),
            ],
            ("ふつうの順序数の足し算（例：Pohlers, Proof Theory, Springer 2009）", "Standard ordinal addition (e.g. Pohlers, Proof Theory, Springer 2009)"),
        ),
        def(
            "mul",
            "α·β",
            ("掛け算", "Multiplication"),
            &[
                ("α·0 = 0、α·(β + 1) = α·β + α、β が極限なら α·β = sup_{γ<β} α·γ", "α·0 = 0, α·(β + 1) = α·β + α, and α·β = sup_{γ<β} α·γ for limit β"),
                (
                    "標準形では：右の分配法則で β を項に分け、α·ω^f = ω^{e₁ + f}（f ≥ 1、e₁ は α の先頭の指数）、α·n は先頭の係数だけ n 倍（(ω + 1)·2 = ω·2 + 1）",
                    "On normal forms: split β into terms by right distributivity; α·ω^f = ω^{e₁ + f} (f ≥ 1, e₁ the leading exponent of α), and α·n multiplies only the leading coefficient by n ((ω + 1)·2 = ω·2 + 1)",
                ),
            ],
            ("ふつうの順序数の掛け算（演算のカードと同じ計算）", "Standard ordinal multiplication (the same computation as the arithmetic card)"),
        ),
        def(
            "pow",
            "α^β",
            ("べき乗", "Exponentiation"),
            &[
                (
                    "α^0 = 1、α^(β + 1) = α^β·α、β が極限なら α^β = sup_{γ<β} α^γ（α ≥ 2）。0^β = 0（β ≥ 1）、1^β = 1",
                    "α^0 = 1, α^(β + 1) = α^β·α, and α^β = sup_{γ<β} α^γ for limit β (α ≥ 2); 0^β = 0 for β ≥ 1 and 1^β = 1",
                ),
                (
                    "標準形では：β = λ + m（λ は 0 か極限、m は有限）と分けて α^β = α^λ·α^m。2 ≤ n < ω なら n^(ω·γ) = ω^γ、α が無限なら α^λ = ω^{e₁·λ}",
                    "On normal forms: write β = λ + m (λ zero or a limit, m finite), so α^β = α^λ·α^m; n^(ω·γ) = ω^γ for 2 ≤ n < ω, and α^λ = ω^{e₁·λ} for infinite α",
                ),
            ],
            ("ふつうの順序数のべき乗（演算のカードと同じ計算）", "Standard ordinal exponentiation (the same computation as the arithmetic card)"),
        ),
        def(
            "phi",
            "φ(α, β)",
            ("Veblen 関数（2 変数）", "Veblen function (binary)"),
            &[
                ("φ(0, β) = ω^β", "φ(0, β) = ω^β"),
                (
                    "α > 0 なら、φ(α, ·) は {ξ : すべての γ < α について φ(γ, ξ) = ξ} を小さい順に並べる関数で、φ(α, β) はその β 番目（0 番目から数える）",
                    "for α > 0, φ(α, ·) enumerates {ξ : φ(γ, ξ) = ξ for all γ < α} in increasing order, and φ(α, β) is its β-th element (counting from 0)",
                ),
                (
                    "例：φ(1, β) = ε_β、φ(2, 0) = ζ₀、φ(ω, 0)。Γ₀ は φ(α, 0) = α となる最小の α（ここでは ψ(0)）",
                    "e.g. φ(1, β) = ε_β, φ(2, 0) = ζ₀, φ(ω, 0); Γ₀ is the least α with φ(α, 0) = α (here ψ(0))",
                ),
                (
                    "比較：φ(α₁, β₁) < φ(α₂, β₂) ⟺ 次のどれか。α₁ < α₂ かつ β₁ < φ(α₂, β₂)／α₁ = α₂ かつ β₁ < β₂／α₁ > α₂ かつ φ(α₁, β₁) < β₂",
                    "comparison: φ(α₁, β₁) < φ(α₂, β₂) iff α₁ < α₂ and β₁ < φ(α₂, β₂), or α₁ = α₂ and β₁ < β₂, or α₁ > α₂ and φ(α₁, β₁) < β₂",
                ),
            ],
            (
                "O. Veblen, Continuous increasing functions of finite and transfinite ordinals, Trans. AMS 9 (1908)。2 変数の形（Schütte・Pohlers の教科書と同じ）",
                "O. Veblen, Continuous increasing functions of finite and transfinite ordinals, Trans. AMS 9 (1908); the binary form, as in the textbooks of Schütte and Pohlers",
            ),
        ),
        def(
            "eps",
            "ε_α",
            ("ε 数", "Epsilon numbers"),
            &[("ε_α = φ(1, α)：ω^ξ = ξ となる ξ の α 番目（ε₀ が最小）", "ε_α = φ(1, α): the α-th ξ with ω^ξ = ξ (ε₀ is the least)")],
            ("Veblen 関数の特別な場合", "A special case of the Veblen function"),
        ),
        def(
            "hyp",
            "e^α(β)",
            ("超指数関数（hyperexponential）", "Hyperexponential"),
            &[
                ("e(ξ) = −1 + ω^ξ（ξ ≥ 1 なら ω^ξ、e(0) = 0）", "e(ξ) = −1 + ω^ξ (that is ω^ξ for ξ ≥ 1, and e(0) = 0)"),
                (
                    "e^α は e の hyperation：e^0 = 恒等写像、e^1 = e、e^{α+β} = e^α ∘ e^β を満たすもの（弱い hyperation）の中で各点で最小のもの",
                    "e^α is the hyperation of e: the pointwise least family with e^0 = id, e^1 = e and e^{α+β} = e^α ∘ e^β (a weak hyperation)",
                ),
                (
                    "計算：α = ω^{α₁}·c₁ + … + ω^{αₙ}·cₙ（Cantor 標準形）なら e^α = (e^{ω^{α₁}})^{c₁} ∘ … ∘ (e^{ω^{αₙ}})^{cₙ}（右から適用）",
                    "computation: for α = ω^{α₁}·c₁ + … + ω^{αₙ}·cₙ (Cantor normal form), e^α = (e^{ω^{α₁}})^{c₁} ∘ … ∘ (e^{ω^{αₙ}})^{cₙ}, applied from the right",
                ),
                (
                    "e^{ω^γ} は e の γ 番目の Veblen 関数（f^{ω^γ} = f_γ）で、e の不動点は 0 と ε 数。よって γ ≥ 1 なら e^{ω^γ}(0) = 0、e^{ω^γ}(1 + β) = φ(γ, β)",
                    "e^{ω^γ} is the γ-th Veblen function of e (f^{ω^γ} = f_γ), whose fixed points are 0 and the ε-numbers; so for γ ≥ 1, e^{ω^γ}(0) = 0 and e^{ω^γ}(1 + β) = φ(γ, β)",
                ),
                (
                    "例：e^ω(1) = ε₀、e^(ω^2)(1) = φ(2, 0)、e^(ω + 1)(1) = ε_ω。worm の順序数では o(μ↑A) = e^μ(o(A))",
                    "e.g. e^ω(1) = ε₀, e^(ω^2)(1) = φ(2, 0), e^(ω + 1)(1) = ε_ω; for worms, o(μ↑A) = e^μ(o(A))",
                ),
            ],
            (
                "D. Fernández-Duque & J. J. Joosten, Hyperations, Veblen progressions and transfinite iteration of ordinal functions（arXiv:1205.2036）。worm との関係は Well-orders in the transfinite Japaridze algebra I・II（arXiv:1212.3468、1204.4743）",
                "D. Fernández-Duque & J. J. Joosten, Hyperations, Veblen progressions and transfinite iteration of ordinal functions (arXiv:1205.2036); for worms, Well-orders in the transfinite Japaridze algebra I and II (arXiv:1212.3468, 1204.4743)",
            ),
        ),
        def(
            "Omega",
            "Ω",
            ("Ω", "Ω"),
            &[
                ("最初の非可算順序数。ここでは記号として扱い、大小・+・φ・ψ の引数に使える", "The first uncountable ordinal, used here as a symbol: it can be compared, added, and used inside φ and ψ"),
                ("強臨界数：α < Ω なら φ(α, Ω) = Ω、そして φ(Ω, 0) = Ω", "strongly critical: φ(α, Ω) = Ω for α < Ω, and φ(Ω, 0) = Ω"),
            ],
            ("Worms and spiders §6", "Worms and spiders §6"),
        ),
        def(
            "psi",
            "ψ(ξ)",
            ("崩壊関数 ψ", "Collapsing function ψ"),
            &[
                (
                    "C(ξ) は {0, 1, Ω} を含み、+ と φ（＝超指数関数）と ψ↾ξ（ζ < ξ での ψ(ζ)）で閉じた最小の集合",
                    "C(ξ) is the least set containing {0, 1, Ω} and closed under +, φ (equivalently the hyperexponentials) and ψ↾ξ (ψ(ζ) for ζ < ξ)",
                ),
                ("ψ(ξ) = C(ξ) に入らない最小の順序数（いつも可算）", "ψ(ξ) = the least ordinal not in C(ξ) (always countable)"),
                (
                    "例：ψ(0) = Γ₀、ψ(1) = Γ₁、ψ(Ω) は α ↦ Γ_α の最初の不動点、ψ(ε_{Ω+1}) = Bachmann–Howard 順序数",
                    "e.g. ψ(0) = Γ₀, ψ(1) = Γ₁, ψ(Ω) is the first fixed point of α ↦ Γ_α, and ψ(ε_{Ω+1}) is the Bachmann–Howard ordinal",
                ),
                (
                    "標準形の ψ(ξ) は ξ ∈ C(ξ) のものだけ。ξ ∈ C(ξ) ⟺ K(ξ) < ξ（K(ξ) は ξ の中で、ほかの ψ の内側にない ψ の引数）。ξ ∉ C(ξ) なら、ξ 以上で z ∈ C(z) となる最小の z について ψ(ξ) = ψ(z)",
                    "ψ(ξ) is in normal form only when ξ ∈ C(ξ); ξ ∈ C(ξ) iff K(ξ) < ξ (K(ξ) collects the arguments of the ψ's in ξ not inside another ψ). If ξ ∉ C(ξ), then ψ(ξ) = ψ(z) for the least z ≥ ξ with z ∈ C(z)",
                ),
                (
                    "注意：Buchholz・Rathjen・Madore などの ψ とは別の関数（例えば Madore 型の ψ では ψ(0) = ε₀）",
                    "Note: this is not the ψ of Buchholz, Rathjen or Madore (for instance, Madore's ψ has ψ(0) = ε₀)",
                ),
            ],
            ("D. Fernández-Duque, Worms and spiders（arXiv:1605.08867）Def 6.19", "D. Fernández-Duque, Worms and spiders (arXiv:1605.08867), Def 6.19"),
        ),
        def(
            "normal",
            "NF",
            ("標準形", "Normal form"),
            &[
                (
                    "主項：φ(α, β)（α, β は標準形で β < φ(α, β)）、Ω、ψ(ξ)（ξ は標準形で ξ ∈ C(ξ)）",
                    "principal terms: φ(α, β) (α, β in normal form with β < φ(α, β)), Ω, and ψ(ξ) (ξ in normal form with ξ ∈ C(ξ))",
                ),
                (
                    "標準形：主項の和 P₁·c₁ + … + Pₙ·cₙ（P₁ > … > Pₙ、cᵢ は 1 以上の自然数）。0 は空の和",
                    "normal form: a sum P₁·c₁ + … + Pₙ·cₙ of principal terms (P₁ > … > Pₙ, cᵢ ≥ 1 natural numbers); 0 is the empty sum",
                ),
                ("書き方：φ(0, 0)·n は n、φ(0, β) は ω^β、φ(1, β) は ε_β", "notation: φ(0, 0)·n is written n, φ(0, β) is ω^β, and φ(1, β) is ε_β"),
                (
                    "主項の比較：φ の比較に加え、強臨界数 s（Ω・ψ(ξ)）は φ(s, 0) とみなす。表せるのは Γ_{Ω+1} 未満（可算な数は ψ(Γ_{Ω+1}) 未満）",
                    "comparison of principal terms: as for φ, reading a strongly critical s (Ω, ψ(ξ)) as φ(s, 0); the notation reaches below Γ_{Ω+1} (countable ordinals below ψ(Γ_{Ω+1}))",
                ),
            ],
            (
                "wormlab の veblen.rs（Γ₀ 未満は Veblen の標準形、Ω・ψ は Worms and spiders §6）",
                "wormlab's veblen.rs (Veblen normal form below Γ₀; Ω and ψ from Worms and spiders §6)",
            ),
        ),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ev(s: &str) -> Eval {
        eval_str(s).unwrap_or_else(|e| panic!("{s}: {e}"))
    }

    #[test]
    fn parse_and_show() {
        let e: Expr = "e^(ω+1)(φ(1, 0)) + ψ(Ω·2)^ω".parse().unwrap();
        assert_eq!(e.to_string(), "e^(ω + 1)(φ(1, 0)) + ψ(Ω·2)^ω");
        let e: Expr = "ω^ω^ω".parse().unwrap();
        assert!(matches!(e, Expr::Pow(_, ref b) if matches!(**b, Expr::Pow(..))));
        assert_eq!("e(ω)".parse::<Expr>().unwrap(), Expr::Hyp(bx(Expr::Nat(1)), bx(Expr::Omega)));
        assert!("φ(1,".parse::<Expr>().is_err());
        assert!("e^ω".parse::<Expr>().is_err());
    }

    #[test]
    fn steps_rewrite_inside_out() {
        let r = ev("φ(1, φ(2, 0)) + 1");
        assert_eq!(r.value.to_string(), "φ(2, 0) + 1");
        assert_eq!(r.steps.len(), 3);
        assert!(r.steps[1].rule.contains("不動点"));
        assert_eq!(r.steps.last().unwrap().whole, "φ(2, 0) + 1");
    }
}
