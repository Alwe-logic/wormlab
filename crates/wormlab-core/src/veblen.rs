//! Γ0 未満の順序数を Veblen 関数 φ で表す。
//!
//! 2 変数の Veblen 関数：
//! - φ(0, β) = ω^β
//! - φ(α, ·)（α > 0）は「すべての γ < α について φ(γ, ·) の不動点」を小さい順に並べる関数
//!   例：φ(1, β) = ε_β（ω^ε = ε となる ε の β 番目）、φ(2, 0) = ζ_0 = ε_{ζ_0}
//!
//! Γ0 未満のどの順序数も、主項 φ(α, β) の和
//!
//! ```text
//!   φ(α_1, β_1)·c_1 + φ(α_2, β_2)·c_2 + …   （主項は真に減少、c_i ≥ 1）
//! ```
//!
//! として一意に書ける。ただし各主項で β < φ(α, β)（不動点にならない）とする。
//! 不動点になるのは「β 自身が単独の主項 φ(γ, δ) で γ > α」の場合だけで、
//! そのときは φ(α, β) = β として潰す（[`Veblen::phi`]）。
//!
//! ε0 未満の範囲では、すべての主項が φ(0, β) = ω^β になり、
//! これまでの [`Ordinal`]（Cantor 標準形）とちょうど一致する。

use crate::ordinal::Ordinal;
use std::cmp::Ordering;
use std::fmt;
use std::ops::Add;
use std::str::FromStr;

/// 主項 φ(a, b)。外から直接作らせず、必ず [`Veblen::phi`] を通す（正規形を保つため）。
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Phi {
    a: Veblen,
    b: Veblen,
}

/// Γ0 未満の順序数（正規形）。
///
/// 【Rust メモ】`Phi` が `Veblen` を含み、`Veblen` が `Vec<(Phi, u64)>` を含む
/// 「相互再帰」の型。`Vec` は中身をヒープに置くので、型の大きさは有限で済む。
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default, PartialOrd, Ord)]
pub struct Veblen {
    terms: Vec<(Phi, u64)>,
}

// ----------------------------------------------------------------------
// 比較
// ----------------------------------------------------------------------

/// 主項どうしの比較。正規形 x = φ(a1, b1), y = φ(a2, b2) について
/// - a1 = a2 なら b1 と b2 の比較
/// - a1 < a2 なら b1 と y の比較（φ(a1, ·) は y を不動点に持つので）
/// - a1 > a2 なら x と b2 の比較（φ(a2, ·) は x を不動点に持つので）
///
/// 【Rust メモ】`derive` ではなく `impl Ord` を手で書くと、比較の意味を
/// 自分で決められる。`Veblen` の方は `derive(Ord)` のままで、
/// 「項の列の辞書式順序」になる（中の `Phi` の比較にはこの実装が使われる）。
impl Ord for Phi {
    fn cmp(&self, other: &Phi) -> Ordering {
        match self.a.cmp(&other.a) {
            Ordering::Equal => self.b.cmp(&other.b),
            Ordering::Less => cmp_with_phi(&self.b, other),
            Ordering::Greater => cmp_with_phi(&other.b, self).reverse(),
        }
    }
}

impl PartialOrd for Phi {
    fn partial_cmp(&self, other: &Phi) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// 順序数 v と、単独の主項 p（= φ(p.a, p.b)·1）の比較。
fn cmp_with_phi(v: &Veblen, p: &Phi) -> Ordering {
    match v.terms.first() {
        None => Ordering::Less, // 0 < p
        Some((q, c)) => match q.cmp(p) {
            Ordering::Equal if *c > 1 || v.terms.len() > 1 => Ordering::Greater,
            o => o,
        },
    }
}

// ----------------------------------------------------------------------
// 構成
// ----------------------------------------------------------------------

impl Veblen {
    pub fn zero() -> Self {
        Veblen { terms: Vec::new() }
    }

    pub fn nat(n: u64) -> Self {
        Self::phi_mul(Self::zero(), Self::zero(), n)
    }

    pub fn one() -> Self {
        Self::nat(1)
    }

    /// ω
    pub fn omega() -> Self {
        Self::omega_pow(Self::one())
    }

    /// φ(a, b)。不動点になる場合（b が φ(c, d) で c > a）は b を返す。
    pub fn phi(a: Veblen, b: Veblen) -> Veblen {
        Self::phi_mul(a, b, 1)
    }

    /// φ(a, b)·c
    fn phi_mul(a: Veblen, b: Veblen, c: u64) -> Veblen {
        if c == 0 {
            return Self::zero();
        }
        // 【Rust メモ】`if let … && 条件` で「パターンに合い、かつ条件も満たす」を一度に書ける
        if let [(q, 1)] = b.terms.as_slice()
            && q.a > a
        {
            // b = φ(q.a, q.b) は φ(a, ·) の不動点
            return Veblen { terms: vec![(q.clone(), c)] };
        }
        Veblen { terms: vec![(Phi { a, b }, c)] }
    }

    /// ω^x = φ(0, x)
    pub fn omega_pow(x: Veblen) -> Veblen {
        Self::phi(Self::zero(), x)
    }

    /// ε_x = φ(1, x)
    pub fn epsilon(x: Veblen) -> Veblen {
        Self::phi(Self::one(), x)
    }

    /// x·n（x を n 回足す）
    pub fn mul_nat(&self, n: u64) -> Veblen {
        if n == 0 || self.is_zero() {
            return Self::zero();
        }
        // x·n = x + x + … + x では、2 個目以降の x の先頭より小さい項がすべて
        // 吸収されるので、結局「先頭の項の係数だけが n 倍」になる。
        // 例：(ω + 1)·2 = ω + 1 + ω + 1 = ω·2 + 1
        let mut terms = self.terms.clone();
        terms[0].1 *= n;
        Veblen { terms }
    }

    // ------------------------------------------------------------------
    // 問い合わせ
    // ------------------------------------------------------------------

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// 有限なら `Some(n)`。
    pub fn as_nat(&self) -> Option<u64> {
        match self.terms.as_slice() {
            [] => Some(0),
            [(p, c)] if p.a.is_zero() && p.b.is_zero() => Some(*c),
            _ => None,
        }
    }

    pub fn is_finite(&self) -> bool {
        self.as_nat().is_some()
    }

    /// 後続順序数か（最後の項が 1 = φ(0, 0)）。
    pub fn is_successor(&self) -> bool {
        matches!(self.terms.last(), Some((p, _)) if p.a.is_zero() && p.b.is_zero())
    }

    pub fn is_limit(&self) -> bool {
        !self.is_zero() && !self.is_successor()
    }

    /// 加法的に分解できない（単独の主項・係数 1）か。
    pub fn is_principal(&self) -> bool {
        matches!(self.terms.as_slice(), [(_, 1)])
    }

    /// 単独の主項 φ(a, b) なら (a, b)。
    pub fn as_phi(&self) -> Option<(&Veblen, &Veblen)> {
        match self.terms.as_slice() {
            [(p, 1)] => Some((&p.a, &p.b)),
            _ => None,
        }
    }

    /// 主項と係数の列。
    pub fn terms(&self) -> impl Iterator<Item = (&Veblen, &Veblen, u64)> {
        self.terms.iter().map(|(p, c)| (&p.a, &p.b, *c))
    }

    /// Cantor 標準形 ω^{e_1}·c_1 + … の指数の列（係数つき）。
    /// φ(0, b) の指数は b、φ(a, b)（a > 0）は ω^x = x となる数なので指数は自分自身。
    pub fn cnf(&self) -> Vec<(Veblen, u64)> {
        self.terms.iter().map(|(p, c)| (cnf_exponent(p), *c)).collect()
    }

    /// ℓ(α)：CNF の最後の指数（α = β + ω^{ℓα}）。ℓ(0) = 0。
    pub fn last_exponent(&self) -> Veblen {
        self.terms.last().map(|(p, _)| cnf_exponent(p)).unwrap_or_default()
    }

    /// 1 + α
    pub fn one_plus(&self) -> Veblen {
        Self::one() + self.clone()
    }

    /// −1 + α（1 + γ = α となる γ）。α = 0 なら `None`。
    pub fn minus_one_plus(&self) -> Option<Veblen> {
        Self::one().sub_left(self)
    }

    /// 左からの引き算：μ + δ = α となる δ（= −μ + α）。μ > α なら `None`。
    ///
    /// 共通の先頭部分を取り除き、最初に食い違った所からの α の残りが δ になる
    /// （μ の残りの項は小さいので δ に吸収される）。
    pub fn sub_left(&self, alpha: &Veblen) -> Option<Veblen> {
        let (mu, al) = (&self.terms, &alpha.terms);
        let mut i = 0;
        loop {
            match (mu.get(i), al.get(i)) {
                (None, _) => return Some(Veblen { terms: al[i..].to_vec() }),
                (Some(_), None) => return None,
                (Some((pm, cm)), Some((pa, ca))) => match pm.cmp(pa) {
                    Ordering::Greater => return None,
                    Ordering::Less => return Some(Veblen { terms: al[i..].to_vec() }),
                    Ordering::Equal => {
                        if cm == ca {
                            i += 1;
                            continue;
                        }
                        if cm > ca {
                            return None;
                        }
                        // cm < ca：μ の残りは (pa, ca − cm) に吸収される
                        let mut terms = vec![(pa.clone(), ca - cm)];
                        terms.extend_from_slice(&al[i + 1..]);
                        return Some(Veblen { terms });
                    }
                },
            }
        }
    }

    // ------------------------------------------------------------------
    // 基本列
    // ------------------------------------------------------------------

    /// α = β + φ(a, b)·c（最後の項）と分けて (β, a, b, c) を返す。α = 0 なら `None`。
    pub fn split_last(&self) -> Option<(Veblen, Veblen, Veblen, u64)> {
        let mut terms = self.terms.clone();
        let (p, c) = terms.pop()?;
        Some((Veblen { terms }, p.a, p.b, c))
    }

    /// 後続順序数 β + 1 なら β。そうでなければ `None`。
    pub fn pred(&self) -> Option<Veblen> {
        if !self.is_successor() {
            return None;
        }
        let mut terms = self.terms.clone();
        let last = terms.last_mut().expect("後続順序数は空でない");
        if last.1 > 1 {
            last.1 -= 1;
        } else {
            terms.pop();
        }
        Some(Veblen { terms })
    }

    /// 基本列 α[n]（標準的な定義）。α = 0 なら `None`、後続順序数なら直前の数。
    ///
    /// 極限順序数 α = β + φ(a, b) では α[n] = β + φ(a, b)[n] とし、主項は
    /// ```text
    /// ω^{b+1}[n]        = ω^b · n
    /// ω^λ[n]            = ω^{λ[n]}                         （λ は極限）
    /// φ(a, λ)[n]        = φ(a, λ[n])                       （a ≥ 1、λ は極限）
    /// φ(a+1, 0)[n]      = φ(a, ·)^n (0)                    （n 回合成）
    /// φ(a+1, b+1)[n]    = φ(a, ·)^n (φ(a+1, b) + 1)
    /// φ(λ, 0)[n]        = φ(λ[n], 0)                       （λ は極限）
    /// φ(λ, b+1)[n]      = φ(λ[n], φ(λ, b) + 1)
    /// ```
    /// 例：ω[n] = n、ε_0[n] = ω^ω^…（n 段）、φ(2, 0)[n] = ε_ε_…（n 段）。
    /// どの n でも α[n] < α で、n について増加し、上限が α になる。
    pub fn fundamental(&self, n: u64) -> Option<Veblen> {
        if self.is_zero() {
            return None;
        }
        if self.is_successor() {
            return self.pred();
        }
        let mut terms = self.terms.clone();
        let (p, c) = terms.pop().expect("空でない");
        if c > 1 {
            terms.push((p.clone(), c - 1));
        }
        Some(Veblen { terms } + fundamental_phi(&p, n))
    }

    /// ε0 未満なら Cantor 標準形の [`Ordinal`] に変換する。
    pub fn to_cnf(&self) -> Option<Ordinal> {
        let mut out = Ordinal::zero();
        for (p, c) in &self.terms {
            if !p.a.is_zero() {
                return None;
            }
            out = out + Ordinal::omega_pow_mul(p.b.to_cnf()?, *c);
        }
        Some(out)
    }
}

/// 極限の主項 φ(a, b)（1 = φ(0, 0) 以外）の基本列。
fn fundamental_phi(p: &Phi, n: u64) -> Veblen {
    let (a, b) = (&p.a, &p.b);
    if a.is_zero() {
        // ω^b（b ≥ 1）
        return match b.pred() {
            Some(bp) => Veblen::omega_pow(bp).mul_nat(n),
            None => Veblen::omega_pow(b.fundamental(n).expect("b は極限")),
        };
    }
    if b.is_limit() {
        return Veblen::phi(a.clone(), b.fundamental(n).expect("b は極限"));
    }
    // b は 0 か後続：φ(a, b) は「φ(a, b−1) の次の不動点」
    let start = match b.pred() {
        None => Veblen::zero(),
        Some(bp) => Veblen::phi(a.clone(), bp) + Veblen::one(),
    };
    match a.pred() {
        Some(ap) => (0..n).fold(start, |x, _| Veblen::phi(ap.clone(), x)),
        None => {
            // a は極限
            let an = a.fundamental(n).expect("a は極限");
            Veblen::phi(an, start)
        }
    }
}

fn cnf_exponent(p: &Phi) -> Veblen {
    if p.a.is_zero() {
        p.b.clone()
    } else {
        Veblen { terms: vec![(p.clone(), 1)] }
    }
}

impl From<&Ordinal> for Veblen {
    /// Cantor 標準形（ε0 未満）からの変換。
    fn from(x: &Ordinal) -> Veblen {
        let terms = x
            .terms()
            .iter()
            .map(|(e, c)| (Phi { a: Veblen::zero(), b: Veblen::from(e) }, *c))
            .collect();
        Veblen { terms }
    }
}

/// 順序数の加法（CNF と同じく、右辺の先頭より小さい項は吸収される）。
impl Add for Veblen {
    type Output = Veblen;

    fn add(self, rhs: Veblen) -> Veblen {
        let Some((lead, lead_c)) = rhs.terms.first() else {
            return self;
        };
        let mut terms = Vec::new();
        let mut merged = *lead_c;
        for (p, c) in self.terms {
            match p.cmp(lead) {
                Ordering::Greater => terms.push((p, c)),
                Ordering::Equal => merged += c,
                Ordering::Less => break,
            }
        }
        terms.push((lead.clone(), merged));
        terms.extend(rhs.terms.into_iter().skip(1));
        Veblen { terms }
    }
}

// ----------------------------------------------------------------------
// 表示
// ----------------------------------------------------------------------

impl fmt::Display for Veblen {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            return write!(f, "0");
        }
        let parts: Vec<String> = self
            .terms
            .iter()
            .map(|(p, c)| {
                if p.a.is_zero() && p.b.is_zero() {
                    return c.to_string(); // 有限部分
                }
                let base = phi_to_string(p);
                if *c == 1 { base } else { format!("{base}·{c}") }
            })
            .collect();
        write!(f, "{}", parts.join(" + "))
    }
}

fn phi_to_string(p: &Phi) -> String {
    if p.a.is_zero() {
        match p.b.as_nat() {
            Some(1) => "ω".to_string(),
            _ if p.b.is_finite() || p.b.is_principal() => format!("ω^{}", p.b),
            _ => format!("ω^({})", p.b),
        }
    } else if p.a.as_nat() == Some(1) {
        if p.b.is_finite() || p.b == Veblen::omega() {
            format!("ε_{}", p.b)
        } else {
            format!("ε_({})", p.b)
        }
    } else {
        format!("φ({}, {})", p.a, p.b)
    }
}

// ----------------------------------------------------------------------
// パーサ
// ----------------------------------------------------------------------
//
//   expr   := term ('+' term)*
//   term   := factor (('·' | '*') 自然数)?
//   factor := 自然数 | ('ω' | 'w') ('^' factor)? | ('ε' | 'e') '_' factor
//           | ('φ' | 'phi') '(' expr ',' expr ')' | '(' expr ')'

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseOrdinalError(pub String);

impl fmt::Display for ParseOrdinalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "順序数として読めません: {}", self.0)
    }
}

impl std::error::Error for ParseOrdinalError {}

struct P {
    s: Vec<char>,
    i: usize,
}

impl P {
    fn ws(&mut self) {
        while self.s.get(self.i).is_some_and(|c| c.is_whitespace()) {
            self.i += 1;
        }
    }
    fn peek(&mut self) -> Option<char> {
        self.ws();
        self.s.get(self.i).copied()
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
    fn err<T>(&self) -> Result<T, ParseOrdinalError> {
        let rest: String = self.s[self.i.min(self.s.len())..].iter().collect();
        Err(ParseOrdinalError(format!("「{rest}」の付近")))
    }
    fn nat(&mut self) -> Option<u64> {
        self.ws();
        let start = self.i;
        while self.s.get(self.i).is_some_and(|c| c.is_ascii_digit()) {
            self.i += 1;
        }
        let t: String = self.s[start..self.i].iter().collect();
        t.parse().ok()
    }
    fn expr(&mut self) -> Result<Veblen, ParseOrdinalError> {
        let mut acc = self.term()?;
        while self.eat('+') {
            acc = acc + self.term()?;
        }
        Ok(acc)
    }
    fn term(&mut self) -> Result<Veblen, ParseOrdinalError> {
        let x = self.factor()?;
        if self.eat('·') || self.eat('*') {
            match self.nat() {
                Some(n) => Ok(x.mul_nat(n)),
                None => self.err(),
            }
        } else {
            Ok(x)
        }
    }
    fn factor(&mut self) -> Result<Veblen, ParseOrdinalError> {
        if let Some(n) = self.nat() {
            return Ok(Veblen::nat(n));
        }
        if self.eat_str("phi") || self.eat('φ') {
            if !self.eat('(') {
                return self.err();
            }
            let a = self.expr()?;
            if !self.eat(',') {
                return self.err();
            }
            let b = self.expr()?;
            if !self.eat(')') {
                return self.err();
            }
            return Ok(Veblen::phi(a, b));
        }
        if self.eat('ω') || self.eat('w') {
            if self.eat('^') {
                return Ok(Veblen::omega_pow(self.factor()?));
            }
            return Ok(Veblen::omega());
        }
        if self.eat('ε') || self.eat('e') {
            if !self.eat('_') {
                return self.err();
            }
            return Ok(Veblen::epsilon(self.factor()?));
        }
        if self.eat('(') {
            let x = self.expr()?;
            if !self.eat(')') {
                return self.err();
            }
            return Ok(x);
        }
        self.err()
    }
}

/// `"ω^(ω + 1)·2 + 3"`, `"ε_0"`, `"e_(w+1)"`, `"φ(2, 0)"`, `"phi(w, 1)"` などを読む。
/// 読んだ式は計算して正規形にする（例：`"ω^ε_0"` は `ε_0` になる）。
impl FromStr for Veblen {
    type Err = ParseOrdinalError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut p = P { s: s.chars().collect(), i: 0 };
        let x = p.expr()?;
        if p.peek().is_some() {
            return p.err();
        }
        Ok(x)
    }
}

/// JSON などでは文字列として書き出す。
impl serde::Serialize for Veblen {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.collect_str(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(s: &str) -> Veblen {
        s.parse().unwrap_or_else(|e| panic!("{s}: {e}"))
    }

    #[test]
    fn fixed_points_collapse() {
        assert_eq!(v("ω^ε_0"), v("ε_0"));
        assert_eq!(v("φ(0, ε_0)"), v("ε_0"));
        assert_eq!(v("ε_(φ(2, 0))"), v("φ(2, 0)"));
        assert_eq!(v("φ(1, φ(ω, 3))"), v("φ(ω, 3)"));
        // 不動点にならない例
        assert_ne!(v("ω^(ε_0 + 1)"), v("ε_0 + 1"));
        assert_ne!(v("ε_(ε_0)"), v("ε_0"));
    }

    #[test]
    fn known_order() {
        let chain = [
            "0", "1", "2", "ω", "ω + 1", "ω·2", "ω^2", "ω^ω", "ω^ω^ω", "ε_0", "ε_0 + 1",
            "ε_0·2", "ω^(ε_0 + 1)", "ω^(ω^(ε_0 + 1))", "ε_1", "ε_ω", "ε_(ε_0)", "ε_(ε_(ε_0))",
            "φ(2, 0)", "φ(2, 0) + 1", "ε_(φ(2, 0) + 1)", "φ(2, 1)", "φ(3, 0)", "φ(ω, 0)",
            "φ(ω, 1)", "φ(ω + 1, 0)", "φ(ε_0, 0)", "φ(φ(2, 0), 0)", "φ(φ(φ(2, 0), 0), 0)",
        ];
        for w in chain.windows(2) {
            assert!(v(w[0]) < v(w[1]), "{} < {} のはず", w[0], w[1]);
        }
    }

    #[test]
    fn display_roundtrip() {
        for s in [
            "0", "7", "ω", "ω·2 + 3", "ω^(ω + 1) + ω^ω + ω + 3", "ε_0", "ε_1 + ε_0·2 + ω",
            "ε_(ω + 1)", "φ(2, 0)", "φ(ω, ε_0 + 1)", "ω^(φ(2, 0) + 1)",
        ] {
            assert_eq!(v(s).to_string(), s);
            assert_eq!(v(&v(s).to_string()), v(s));
        }
    }

    #[test]
    fn arithmetic() {
        assert_eq!(v("1 + ω"), v("ω"));
        assert_eq!(v("ω + ε_0"), v("ε_0"));
        assert_eq!(v("ε_0 + ε_0"), v("ε_0·2"));
        assert_eq!(v("ω").sub_left(&v("ω·2 + 1")), Some(v("ω + 1")));
        assert_eq!(v("ω + 5").sub_left(&v("ε_0")), Some(v("ε_0")));
        assert_eq!(v("ε_0").sub_left(&v("ω")), None);
        assert_eq!(v("ε_0 + ω^2").last_exponent(), v("2"));
        assert_eq!(v("ω + ε_1").last_exponent(), v("ε_1"));
        assert_eq!(v("ω·3 + 2").mul_nat(2), v("ω·6 + 2"));
        assert_eq!(v("ε_0·2 + ω^ε_1"), v("ε_1")); // ω^ε_1 = ε_1 が前を吸収する
    }

    #[test]
    fn cnf_conversion() {
        let x = v("ω^(ω^ω + 1)·2 + ω + 3");
        let c = x.to_cnf().unwrap();
        assert_eq!(c.to_string(), "ω^(ω^ω + 1)·2 + ω + 3");
        assert_eq!(Veblen::from(&c), x);
        assert_eq!(v("ε_0").to_cnf(), None);
    }
}
