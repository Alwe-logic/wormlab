//! 強正値式（strictly positive formula）。Reflection Calculus (RC) の言語。
//!
//! ```text
//!   A, B ::= ⊤ | p | A ∧ B | ⟨n⟩A
//! ```
//!
//! 否定も含意も ∨ もない。worm はちょうど「∧ を含まない閉じた強正値式」。

use crate::worm::Worm;
use std::collections::BTreeSet;
use std::fmt;
use std::str::FromStr;

/// 強正値式。
///
/// 【Rust メモ】再帰的な enum は、自分自身を直接は含めない（サイズが
/// 決まらないため）。`Box<Spf>` は「ヒープ上の Spf へのポインタ」で、
/// これを挟むと再帰型が作れる。
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Spf {
    Top,
    Var(String),
    And(Box<Spf>, Box<Spf>),
    Dia(u32, Box<Spf>),
}

impl Spf {
    pub fn var(name: &str) -> Spf {
        Spf::Var(name.to_string())
    }

    pub fn and(a: Spf, b: Spf) -> Spf {
        Spf::And(Box::new(a), Box::new(b))
    }

    pub fn dia(n: u32, a: Spf) -> Spf {
        Spf::Dia(n, Box::new(a))
    }

    /// 複数の式の連言（空なら ⊤）。
    pub fn conj(items: impl IntoIterator<Item = Spf>) -> Spf {
        items.into_iter().reduce(Spf::and).unwrap_or(Spf::Top)
    }

    /// 式に現れるモダリティの番号の集合。
    pub fn modalities(&self) -> BTreeSet<u32> {
        let mut out = BTreeSet::new();
        self.collect_modalities(&mut out);
        out
    }

    fn collect_modalities(&self, out: &mut BTreeSet<u32>) {
        match self {
            Spf::Top | Spf::Var(_) => {}
            Spf::And(a, b) => {
                a.collect_modalities(out);
                b.collect_modalities(out);
            }
            Spf::Dia(n, a) => {
                out.insert(*n);
                a.collect_modalities(out);
            }
        }
    }

    /// 式の大きさ（記号の個数）。
    pub fn size(&self) -> usize {
        match self {
            Spf::Top | Spf::Var(_) => 1,
            Spf::And(a, b) => 1 + a.size() + b.size(),
            Spf::Dia(_, a) => 1 + a.size(),
        }
    }

    /// worm なら worm に戻す（∧ や変数を含めば `None`）。
    pub fn as_worm(&self) -> Option<Worm> {
        let mut letters = Vec::new();
        let mut cur = self;
        loop {
            match cur {
                Spf::Top => return Some(Worm::new(letters)),
                Spf::Dia(n, a) => {
                    letters.push(*n);
                    cur = a;
                }
                _ => return None,
            }
        }
    }
}

impl From<&Worm> for Spf {
    /// worm n_1 … n_k を ⟨n_1⟩…⟨n_k⟩⊤ に変換する。
    fn from(w: &Worm) -> Spf {
        w.letters()
            .iter()
            .rev()
            .fold(Spf::Top, |acc, &n| Spf::dia(n, acc))
    }
}

// ----------------------------------------------------------------------
// 表示
// ----------------------------------------------------------------------

impl fmt::Display for Spf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Spf::Top => write!(f, "⊤"),
            Spf::Var(p) => write!(f, "{p}"),
            Spf::And(a, b) => write!(f, "{a} ∧ {b}"),
            Spf::Dia(n, a) => match **a {
                Spf::And(..) => write!(f, "⟨{n}⟩({a})"),
                _ => write!(f, "⟨{n}⟩{a}"),
            },
        }
    }
}

// ----------------------------------------------------------------------
// パーサ（再帰下降）
// ----------------------------------------------------------------------
//
//   formula := unary ( ('∧' | '&') unary )*
//   unary   := ('<' n '>' | '⟨' n '⟩') unary
//            | '⊤' | 'T' | 'top' | 変数名 | '(' formula ')'
//
// 変数名は英小文字で始まり、英数字と _ が続くもの（"top" は除く）。

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

    fn formula(&mut self) -> Result<Spf, ParseError> {
        let mut acc = self.unary()?;
        while self.eat('∧') || self.eat('&') {
            let rhs = self.unary()?;
            acc = Spf::and(acc, rhs);
        }
        Ok(acc)
    }

    fn number(&mut self) -> Result<u32, ParseError> {
        self.skip_ws();
        let start = self.pos;
        while self.pos < self.chars.len() && self.chars[self.pos].is_ascii_digit() {
            self.pos += 1;
        }
        if start == self.pos {
            return self.error("モダリティの番号が必要です");
        }
        let s: String = self.chars[start..self.pos].iter().collect();
        s.parse().or_else(|_| self.error("番号が大きすぎます"))
    }

    fn unary(&mut self) -> Result<Spf, ParseError> {
        match self.peek() {
            Some(open @ ('<' | '⟨')) => {
                self.pos += 1;
                let n = self.number()?;
                let close = if open == '<' { '>' } else { '⟩' };
                if !self.eat(close) {
                    return self.error(&format!("'{close}' が必要です"));
                }
                Ok(Spf::dia(n, self.unary()?))
            }
            Some('⊤') => {
                self.pos += 1;
                Ok(Spf::Top)
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
                    "T" | "top" => Ok(Spf::Top),
                    _ if c.is_ascii_lowercase() => Ok(Spf::Var(name)),
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

impl FromStr for Spf {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut p = Parser::new(s);
        let a = p.formula()?;
        p.finish()?;
        Ok(a)
    }
}

/// シーケント A ⊢ B。
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Sequent {
    pub lhs: Spf,
    pub rhs: Spf,
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
        let (l, r) = s
            .split_once("⊢")
            .or_else(|| s.split_once("|-"))
            .ok_or_else(|| ParseError {
                input: s.to_string(),
                pos: 0,
                msg: "'⊢' または '|-' が必要です".to_string(),
            })?;
        Ok(Sequent { lhs: l.parse()?, rhs: r.parse()? })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_and_display() {
        let a: Spf = "<1>(p & <0>q) ∧ ⟨2⟩T".parse().unwrap();
        assert_eq!(a.to_string(), "⟨1⟩(p ∧ ⟨0⟩q) ∧ ⟨2⟩⊤");
        assert_eq!(a.to_string().parse::<Spf>().unwrap(), a);
        assert_eq!(a.modalities().into_iter().collect::<Vec<_>>(), vec![0, 1, 2]);
    }

    #[test]
    fn parse_errors() {
        assert!("<1 p".parse::<Spf>().is_err());
        assert!("p ∧".parse::<Spf>().is_err());
        assert!("P".parse::<Spf>().is_err());
        assert!("p q".parse::<Spf>().is_err());
    }

    #[test]
    fn worm_roundtrip() {
        let w: Worm = "1 0 2".parse().unwrap();
        let a = Spf::from(&w);
        assert_eq!(a.to_string(), "⟨1⟩⟨0⟩⟨2⟩⊤");
        assert_eq!(a.as_worm(), Some(w));
        assert_eq!("p".parse::<Spf>().unwrap().as_worm(), None);
    }

    #[test]
    fn sequent() {
        let s: Sequent = "<2>p |- <0><1>p".parse().unwrap();
        assert_eq!(s.to_string(), "⟨2⟩p ⊢ ⟨0⟩⟨1⟩p");
    }
}
