//! 強正値式（strictly positive formula）。Reflection Calculus (RC) の言語。
//!
//! ```text
//!   A, B ::= ⊤ | p | A ∧ B | ⟨n⟩A
//! ```
//!
//! 否定も含意も ∨ もない。worm はちょうど「∧ を含まない閉じた強正値式」。

use crate::letter::Letter;
use crate::worm::Worm;
use std::collections::BTreeSet;
use std::fmt;
use std::rc::Rc;
use std::str::FromStr;

/// 強正値式。モダリティの番号の型 `L` の既定は自然数 `u32`。
///
/// 【Rust メモ】再帰的な enum は、自分自身を直接は含めない（サイズが
/// 決まらないため）。`Rc<Spf>` は「ヒープ上の Spf を指す、参照カウントつきの
/// ポインタ」で、これを挟むと再帰型が作れる。`Box` と違って `clone` は
/// ポインタを複製するだけ（O(1)）なので、同じ部分式を多くの場所で共有できる。
/// RC の導出では、大きな左辺をシーケントごとに持つのでこれが効く。
/// 中身は書き換えないので、共有しても値としての意味は変わらない。
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Spf<L = u32> {
    Top,
    Var(String),
    And(Rc<Spf<L>>, Rc<Spf<L>>),
    Dia(L, Rc<Spf<L>>),
}

impl<L: Letter> Spf<L> {
    pub fn var(name: &str) -> Spf<L> {
        Spf::Var(name.to_string())
    }

    pub fn and(a: Spf<L>, b: Spf<L>) -> Spf<L> {
        Spf::And(Rc::new(a), Rc::new(b))
    }

    pub fn dia(n: L, a: Spf<L>) -> Spf<L> {
        Spf::Dia(n, Rc::new(a))
    }

    /// 複数の式の連言（空なら ⊤）。
    pub fn conj(items: impl IntoIterator<Item = Spf<L>>) -> Spf<L> {
        items.into_iter().reduce(Spf::and).unwrap_or(Spf::Top)
    }

    /// 式に現れるモダリティの番号の集合。
    pub fn modalities(&self) -> BTreeSet<L> {
        let mut out = BTreeSet::new();
        self.collect_modalities(&mut out);
        out
    }

    fn collect_modalities(&self, out: &mut BTreeSet<L>) {
        match self {
            Spf::Top | Spf::Var(_) => {}
            Spf::And(a, b) => {
                a.collect_modalities(out);
                b.collect_modalities(out);
            }
            Spf::Dia(n, a) => {
                out.insert(n.clone());
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
    pub fn as_worm(&self) -> Option<Worm<L>> {
        let mut letters = Vec::new();
        let mut cur = self;
        loop {
            match cur {
                Spf::Top => return Some(Worm::new(letters)),
                Spf::Dia(n, a) => {
                    letters.push(n.clone());
                    cur = a;
                }
                _ => return None,
            }
        }
    }
}

impl<L: Letter> From<&Worm<L>> for Spf<L> {
    /// worm n_1 … n_k を ⟨n_1⟩…⟨n_k⟩⊤ に変換する。
    fn from(w: &Worm<L>) -> Spf<L> {
        w.letters()
            .iter()
            .rev()
            .fold(Spf::Top, |acc, n| Spf::dia(n.clone(), acc))
    }
}

// ----------------------------------------------------------------------
// 表示
// ----------------------------------------------------------------------

impl<L: Letter> fmt::Display for Spf<L> {
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

struct Parser<'a, L> {
    input: &'a str,
    chars: Vec<char>,
    pos: usize,
    _letter: std::marker::PhantomData<L>,
}

impl<'a, L: Letter> Parser<'a, L> {
    fn new(input: &'a str) -> Self {
        Parser { input, chars: input.chars().collect(), pos: 0, _letter: std::marker::PhantomData }
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

    fn formula(&mut self) -> Result<Spf<L>, ParseError> {
        let mut acc = self.unary()?;
        while self.eat('∧') || self.eat('&') {
            let rhs = self.unary()?;
            acc = Spf::and(acc, rhs);
        }
        Ok(acc)
    }

    /// 閉じ括弧 `close` までをモダリティの番号として読む（自然数でも順序数でもよい）。
    fn modality(&mut self, close: char) -> Result<L, ParseError> {
        let start = self.pos;
        while self.pos < self.chars.len() && self.chars[self.pos] != close {
            self.pos += 1;
        }
        if self.pos >= self.chars.len() {
            self.pos = start;
            return self.error(&format!("'{close}' が必要です"));
        }
        let s: String = self.chars[start..self.pos].iter().collect();
        self.pos += 1; // 閉じ括弧
        match L::parse_letter(&s) {
            Some(n) => Ok(n),
            None => {
                self.pos = start;
                self.error("モダリティの番号が読めません")
            }
        }
    }

    fn unary(&mut self) -> Result<Spf<L>, ParseError> {
        match self.peek() {
            Some(open @ ('<' | '⟨')) => {
                self.pos += 1;
                let close = if open == '<' { '>' } else { '⟩' };
                let n = self.modality(close)?;
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

/// `"<1>(p & <0>q)"` や、順序数のモダリティ `"<ω+1>p ∧ <ε_0>q"` を読む。
impl<L: Letter> FromStr for Spf<L> {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut p = Parser::<L>::new(s);
        let a = p.formula()?;
        p.finish()?;
        Ok(a)
    }
}

/// シーケント A ⊢ B。
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Sequent<L = u32> {
    pub lhs: Spf<L>,
    pub rhs: Spf<L>,
}

impl<L: Letter> fmt::Display for Sequent<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ⊢ {}", self.lhs, self.rhs)
    }
}

/// JSON などでは文字列として書き出す。
impl<L: Letter> serde::Serialize for Spf<L> {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.collect_str(self)
    }
}

/// `"A |- B"` または `"A ⊢ B"` を読む。
impl<L: Letter> FromStr for Sequent<L> {
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
    fn ordinal_modalities() {
        use crate::veblen::Veblen;
        let a: Spf<Veblen> = "<ω+1>p ∧ ⟨ε_0⟩<0>q".parse().unwrap();
        assert_eq!(a.to_string(), "⟨ω + 1⟩p ∧ ⟨ε_0⟩⟨0⟩q");
        assert_eq!(a.to_string().parse::<Spf<Veblen>>().unwrap(), a);
    }

    #[test]
    fn sequent() {
        let s: Sequent = "<2>p |- <0><1>p".parse().unwrap();
        assert_eq!(s.to_string(), "⟨2⟩p ⊢ ⟨0⟩⟨1⟩p");
    }
}
