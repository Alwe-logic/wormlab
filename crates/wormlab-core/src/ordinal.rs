//! ε0 未満の順序数を Cantor 標準形 (CNF) で表す。
//!
//! α = ω^{β_1}·c_1 + ω^{β_2}·c_2 + … + ω^{β_k}·c_k
//! （β_1 > β_2 > … > β_k，c_i ≥ 1）
//!
//! 指数 β_i もまた同じ形の順序数なので、型は再帰的になる。

use std::cmp::Ordering;
use std::fmt;
use std::ops::Add;

/// ε0 未満の順序数。
///
/// `terms` は (指数, 係数) の列で、指数は真に降順・係数は 1 以上という
/// 不変条件を常に保つ（外から直接いじれないよう非公開にしている）。
///
/// 【Rust メモ】`#[derive(...)]` は、よく使う trait の実装をコンパイラに
/// 自動生成させる仕組み。ここで `PartialOrd, Ord` を derive すると
/// 「フィールドを辞書式に比較する」実装になる。`Vec<(Ordinal, u64)>` の
/// 辞書式順序は、CNF の比較（まず最高次の指数、次に係数、…、
/// 先に項が尽きた方が小さい）とちょうど一致するので、比較は自前で
/// 書かずに済む。
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Ordinal {
    terms: Vec<(Ordinal, u64)>,
}

impl Ordinal {
    /// 0
    pub fn zero() -> Self {
        Ordinal { terms: Vec::new() }
    }

    /// 自然数 n
    pub fn nat(n: u64) -> Self {
        if n == 0 {
            Self::zero()
        } else {
            Ordinal { terms: vec![(Self::zero(), n)] }
        }
    }

    /// ω
    pub fn omega() -> Self {
        Self::omega_pow(Self::nat(1))
    }

    /// ω^α
    pub fn omega_pow(alpha: Ordinal) -> Self {
        Ordinal { terms: vec![(alpha, 1)] }
    }

    /// ω^α · c （c = 0 なら 0）
    pub fn omega_pow_mul(alpha: Ordinal, c: u64) -> Self {
        if c == 0 {
            Self::zero()
        } else {
            Ordinal { terms: vec![(alpha, c)] }
        }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// 有限順序数なら `Some(n)`、そうでなければ `None`。
    ///
    /// 【Rust メモ】`Option<T>` は「値があるかもしれないし、ないかもしれない」
    /// を表す型。null の代わりに使い、`match` で必ず両方の場合を扱わされる。
    pub fn as_nat(&self) -> Option<u64> {
        match self.terms.as_slice() {
            [] => Some(0),
            [(e, c)] if e.is_zero() => Some(*c),
            _ => None,
        }
    }

    pub fn is_finite(&self) -> bool {
        self.as_nat().is_some()
    }

    /// 後続順序数（最後の項が ω^0 の項）か。
    pub fn is_successor(&self) -> bool {
        matches!(self.terms.last(), Some((e, _)) if e.is_zero())
    }

    /// 極限順序数（0 でも後続でもない）か。
    pub fn is_limit(&self) -> bool {
        !self.is_zero() && !self.is_successor()
    }

    /// CNF の項を (指数, 係数) として順に返す。
    pub fn terms(&self) -> &[(Ordinal, u64)] {
        &self.terms
    }

    /// 1 + α（α が有限なら α+1、無限なら α そのもの）
    pub fn one_plus(&self) -> Ordinal {
        Ordinal::nat(1) + self.clone()
    }

    /// −1 + α：1 + γ = α を満たす γ。α = 0 のときは `None`。
    pub fn minus_one_plus(&self) -> Option<Ordinal> {
        match self.as_nat() {
            Some(0) => None,
            Some(n) => Some(Ordinal::nat(n - 1)),
            None => Some(self.clone()),
        }
    }

    /// α + 1
    pub fn succ(&self) -> Ordinal {
        self.clone() + Ordinal::nat(1)
    }

    /// ω^α の列 β_1 ≥ β_2 ≥ … に展開する（係数 c の項は c 回繰り返す）。
    /// α = ω^{β_1} + ω^{β_2} + … という「係数なし」の表示。
    pub fn exponents_with_multiplicity(&self) -> Vec<Ordinal> {
        let mut out = Vec::new();
        for (e, c) in &self.terms {
            for _ in 0..*c {
                out.push(e.clone());
            }
        }
        out
    }
}

/// 順序数の加法（非可換：1 + ω = ω ≠ ω + 1）。
///
/// α + β は、β の最高次の指数 e より小さい α の項を吸収して捨て、
/// 指数がちょうど e の項があれば係数を足し合わせる。
///
/// 【Rust メモ】`impl Add for Ordinal` を書くと `a + b` という演算子が
/// 使えるようになる（演算子オーバーロード）。
impl Add for Ordinal {
    type Output = Ordinal;

    fn add(self, rhs: Ordinal) -> Ordinal {
        let Some((lead_exp, lead_coef)) = rhs.terms.first() else {
            return self; // β = 0
        };
        let mut terms: Vec<(Ordinal, u64)> = Vec::new();
        let mut merged_coef = *lead_coef;
        for (e, c) in self.terms {
            match e.cmp(lead_exp) {
                Ordering::Greater => terms.push((e, c)),
                Ordering::Equal => merged_coef += c,
                Ordering::Less => break, // 以降はすべて吸収される
            }
        }
        terms.push((lead_exp.clone(), merged_coef));
        terms.extend(rhs.terms.into_iter().skip(1));
        Ordinal { terms }
    }
}

impl fmt::Display for Ordinal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            return write!(f, "0");
        }
        let parts: Vec<String> = self
            .terms
            .iter()
            .map(|(e, c)| {
                let base = match e.as_nat() {
                    Some(0) => return c.to_string(),
                    Some(1) => "ω".to_string(),
                    _ if e.is_atomic() => format!("ω^{e}"),
                    _ => format!("ω^({e})"),
                };
                if *c == 1 { base } else { format!("{base}·{c}") }
            })
            .collect();
        write!(f, "{}", parts.join(" + "))
    }
}

impl Ordinal {
    /// 表示のとき括弧なしで指数に置けるか（自然数 or 単独の ω^β）。
    fn is_atomic(&self) -> bool {
        self.is_finite() || (self.terms.len() == 1 && self.terms[0].1 == 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn w() -> Ordinal {
        Ordinal::omega()
    }

    #[test]
    fn addition_absorbs_smaller_terms() {
        // 1 + ω = ω
        assert_eq!(Ordinal::nat(1) + w(), w());
        // ω + 1 ≠ ω
        assert_ne!(w() + Ordinal::nat(1), w());
        // ω + ω = ω·2
        assert_eq!(w() + w(), Ordinal::omega_pow_mul(Ordinal::nat(1), 2));
        // ω^2 + ω + ω^2 = ω^2·2
        let w2 = Ordinal::omega_pow(Ordinal::nat(2));
        assert_eq!(
            w2.clone() + w() + w2.clone(),
            Ordinal::omega_pow_mul(Ordinal::nat(2), 2)
        );
    }

    #[test]
    fn comparison() {
        let w2 = Ordinal::omega_pow(Ordinal::nat(2));
        let ww = Ordinal::omega_pow(w());
        assert!(Ordinal::nat(1000) < w());
        assert!(w() + Ordinal::nat(5) < w() + w());
        assert!(w2 < ww);
        assert!(w2.clone() + w2.clone() + w() < w2.clone() + w2 + w() + Ordinal::nat(1));
    }

    #[test]
    fn display() {
        let ww = Ordinal::omega_pow(w());
        let x = Ordinal::omega_pow(w() + Ordinal::nat(1)) + ww + w() + Ordinal::nat(3);
        assert_eq!(x.to_string(), "ω^(ω + 1) + ω^ω + ω + 3");
        assert_eq!((w() + w()).to_string(), "ω·2");
        assert_eq!(Ordinal::zero().to_string(), "0");
    }
}
