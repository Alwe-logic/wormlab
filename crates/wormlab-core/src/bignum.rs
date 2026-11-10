//! 多倍長の自然数（桁数に上限のない 0 以上の整数）。
//!
//! battle の長さや Hardy 関数の値は、すぐに u128（約 3.4×10^38）を超える。ここでは
//! 必要な演算（足し算・小さい数の引き算と掛け算・2^k 倍・比較・10 進表示）だけを持つ
//! 自然数の型を自分で書く（外部の crate に頼らない）。
//!
//! 内部では 2^64 進法の「桁」（limb）を下の桁から順に並べる。例えば
//! 2^64 + 5 は `[5, 1]`。いちばん上の桁は 0 にしない（0 自身は空の列）。

use std::cmp::Ordering;
use std::fmt;

/// 0 以上の整数（多倍長）。
///
/// 【Rust メモ】`Vec<u64>` を 1 つだけ持つ構造体。`derive(Default)` で
/// `BigNat::default()` が空の列 = 0 になる。
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct BigNat {
    limbs: Vec<u64>,
}

/// 10 進表示で 1 回に取り出す桁数（10^19 < 2^64）。
const DEC_CHUNK: u64 = 10_000_000_000_000_000_000;
const DEC_CHUNK_DIGITS: usize = 19;

impl BigNat {
    pub fn zero() -> BigNat {
        BigNat::default()
    }

    /// 上の桁の 0 を取り除く（正規化）。
    fn trim(mut self) -> BigNat {
        while self.limbs.last() == Some(&0) {
            self.limbs.pop();
        }
        self
    }

    pub fn is_zero(&self) -> bool {
        self.limbs.is_empty()
    }

    /// 2 進表示の桁数（0 なら 0）。
    pub fn bits(&self) -> u64 {
        match self.limbs.last() {
            None => 0,
            Some(top) => 64 * (self.limbs.len() as u64 - 1) + (64 - top.leading_zeros() as u64),
        }
    }

    pub fn to_u64(&self) -> Option<u64> {
        match self.limbs.as_slice() {
            [] => Some(0),
            [x] => Some(*x),
            _ => None,
        }
    }

    pub fn to_u128(&self) -> Option<u128> {
        match self.limbs.as_slice() {
            [] => Some(0),
            [x] => Some(*x as u128),
            [lo, hi] => Some(((*hi as u128) << 64) | *lo as u128),
            _ => None,
        }
    }

    /// 2^k
    pub fn pow2(k: u64) -> BigNat {
        BigNat::from(1u64).shl(k)
    }

    /// self + other
    pub fn add(&self, other: &BigNat) -> BigNat {
        let (long, short) = if self.limbs.len() >= other.limbs.len() { (self, other) } else { (other, self) };
        let mut out = Vec::with_capacity(long.limbs.len() + 1);
        let mut carry = false;
        for (i, &a) in long.limbs.iter().enumerate() {
            let b = short.limbs.get(i).copied().unwrap_or(0);
            // 【Rust メモ】`overflowing_add` は「あふれたか」も返す足し算
            let (s1, c1) = a.overflowing_add(b);
            let (s2, c2) = s1.overflowing_add(carry as u64);
            out.push(s2);
            carry = c1 || c2;
        }
        if carry {
            out.push(1);
        }
        BigNat { limbs: out }
    }

    pub fn add_small(&self, k: u64) -> BigNat {
        self.add(&BigNat::from(k))
    }

    /// self − other（other > self なら `None`）
    pub fn sub(&self, other: &BigNat) -> Option<BigNat> {
        if *self < *other {
            return None;
        }
        let mut out = Vec::with_capacity(self.limbs.len());
        let mut borrow = false;
        for (i, &a) in self.limbs.iter().enumerate() {
            let b = other.limbs.get(i).copied().unwrap_or(0);
            let (d1, b1) = a.overflowing_sub(b);
            let (d2, b2) = d1.overflowing_sub(borrow as u64);
            out.push(d2);
            borrow = b1 || b2;
        }
        Some(BigNat { limbs: out }.trim())
    }

    pub fn sub_small(&self, k: u64) -> Option<BigNat> {
        self.sub(&BigNat::from(k))
    }

    /// self − other、ただし負になるなら 0
    pub fn saturating_sub(&self, other: &BigNat) -> BigNat {
        self.sub(other).unwrap_or_default()
    }

    /// self × k（k は u64）
    pub fn mul_small(&self, k: u64) -> BigNat {
        if k == 0 || self.is_zero() {
            return BigNat::zero();
        }
        let mut out = Vec::with_capacity(self.limbs.len() + 1);
        let mut carry: u128 = 0;
        for &a in &self.limbs {
            // 【Rust メモ】u64 × u64 は最大 128 ビットなので u128 で計算する
            let p = a as u128 * k as u128 + carry;
            out.push(p as u64);
            carry = p >> 64;
        }
        if carry > 0 {
            out.push(carry as u64);
        }
        BigNat { limbs: out }
    }

    /// self × 2^k（左シフト）
    pub fn shl(&self, k: u64) -> BigNat {
        if self.is_zero() {
            return BigNat::zero();
        }
        let (whole, part) = ((k / 64) as usize, (k % 64) as u32);
        let mut out = vec![0u64; whole];
        if part == 0 {
            out.extend_from_slice(&self.limbs);
        } else {
            let mut carry = 0u64;
            for &a in &self.limbs {
                out.push((a << part) | carry);
                carry = a >> (64 - part);
            }
            if carry > 0 {
                out.push(carry);
            }
        }
        BigNat { limbs: out }
    }

    /// self ÷ d の商と余り（d は u64、0 でない）
    fn divmod_small(&self, d: u64) -> (BigNat, u64) {
        let mut q = vec![0u64; self.limbs.len()];
        let mut r: u128 = 0;
        for i in (0..self.limbs.len()).rev() {
            let cur = (r << 64) | self.limbs[i] as u128;
            q[i] = (cur / d as u128) as u64;
            r = cur % d as u128;
        }
        (BigNat { limbs: q }.trim(), r as u64)
    }

    /// 10 進表示（全桁）。桁数 d に対して O(d²) かかるので、百万桁を超えると数秒以上かかる。
    pub fn to_decimal(&self) -> String {
        if self.is_zero() {
            return "0".to_string();
        }
        let mut chunks = Vec::new();
        let mut cur = self.clone();
        while !cur.is_zero() {
            let (q, r) = cur.divmod_small(DEC_CHUNK);
            chunks.push(r);
            cur = q;
        }
        let mut s = chunks.last().expect("0 でない").to_string();
        for c in chunks.iter().rev().skip(1) {
            s.push_str(&format!("{c:0width$}", width = DEC_CHUNK_DIGITS));
        }
        s
    }

    /// 下 k 桁（k ≤ 19）：self mod 10^k。
    pub fn low_digits(&self, k: u32) -> u64 {
        let m = 10u128.pow(k.min(19));
        let mut r: u128 = 0;
        for &a in self.limbs.iter().rev() {
            r = ((r << 64) | a as u128) % m;
        }
        r as u64
    }

    /// log10(self) の近似（self > 0）。上の 64 ビットと桁数から計算するので、
    /// 何百万ビットあっても小数部は 10^-9 程度まで正しい。
    pub fn log10(&self) -> f64 {
        let b = self.bits();
        if b <= 64 {
            return (self.to_u64().unwrap_or(0) as f64).log10();
        }
        let shift = b - 64;
        let (whole, part) = ((shift / 64) as usize, (shift % 64) as u32);
        let lo = self.limbs[whole] as u128;
        let hi = self.limbs.get(whole + 1).copied().unwrap_or(0) as u128;
        let top = (((hi << 64) | lo) >> part) as u64;
        (top as f64).log10() + shift as f64 * std::f64::consts::LOG10_2
    }

    /// 10 進の桁数。小さければ正確に、大きければ log10 から（境目に近いときは正確に数える）。
    pub fn decimal_digits(&self) -> u64 {
        if self.bits() <= 4096 {
            return self.to_decimal().len() as u64;
        }
        let l = self.log10();
        let frac = l - l.floor();
        if frac > 1e-6 && frac < 1.0 - 1e-6 {
            return l.floor() as u64 + 1;
        }
        self.to_decimal().len() as u64
    }

    /// 短い表示：60 桁以下なら全桁、それより大きければ
    /// 「1.0957732×10^40（41 桁、末尾 …4567890123）」の形。
    pub fn summary(&self) -> String {
        if self.bits() <= 199 {
            return self.to_decimal();
        }
        let digits = self.decimal_digits();
        if crate::i18n::is_en() {
            return format!(
                "{} ({} digits, ending …{:010})",
                self.scientific(8),
                group_thousands(digits),
                self.low_digits(10)
            );
        }
        format!(
            "{}（{} 桁、末尾 …{:010}）",
            self.scientific(8),
            group_thousands(digits),
            self.low_digits(10)
        )
    }

    /// 「1.0957732×10^40」（有効数字 sig 桁）。self > 0。
    pub fn scientific(&self, sig: usize) -> String {
        let (mant, exp) = self.mantissa_exponent(sig);
        format!("{mant}×10^{exp}")
    }

    /// LaTeX：60 桁以下なら全桁、それより大きければ `\approx 1.0957732 \times 10^{40}`。
    pub fn to_latex_summary(&self) -> String {
        if self.bits() <= 199 {
            return self.to_decimal();
        }
        let (mant, exp) = self.mantissa_exponent(8);
        format!("\\approx {mant} \\times 10^{{{exp}}}")
    }

    /// 仮数（"1.0957732" の形の文字列）と指数。
    fn mantissa_exponent(&self, sig: usize) -> (String, u64) {
        let digits = self.decimal_digits();
        let exp = digits - 1;
        let l = self.log10();
        // 桁数は正確に数えてあるので、仮数は 10^(l − exp) を [1, 10) に収める
        let mut m = 10f64.powf(l - exp as f64);
        if m < 1.0 {
            m = 1.0;
        }
        let mut s = format!("{:.*}", sig.saturating_sub(1), m);
        if s.starts_with("10") {
            // 丸めで 10.000… になったら 9.999… にとどめる（指数は桁数で決まっているので変えない）
            s = format!("9.{}", "9".repeat(sig.saturating_sub(1)));
        }
        (s, exp)
    }
}

/// 1234567 → "1,234,567"
fn group_thousands(n: u64) -> String {
    let s = n.to_string();
    // 【Rust メモ】`rchunks(3)` は後ろから 3 つずつ区切ったかたまりを返す
    let mut groups: Vec<&str> = s.as_bytes().rchunks(3).map(|c| std::str::from_utf8(c).expect("数字")).collect();
    groups.reverse();
    groups.join(",")
}

impl From<u64> for BigNat {
    fn from(x: u64) -> BigNat {
        BigNat { limbs: vec![x] }.trim()
    }
}

impl From<u128> for BigNat {
    fn from(x: u128) -> BigNat {
        BigNat { limbs: vec![x as u64, (x >> 64) as u64] }.trim()
    }
}

/// 大小：桁の数が多い方が大きく、同じなら上の桁から比べる。
impl Ord for BigNat {
    fn cmp(&self, other: &BigNat) -> Ordering {
        self.limbs.len().cmp(&other.limbs.len()).then_with(|| self.limbs.iter().rev().cmp(other.limbs.iter().rev()))
    }
}

impl PartialOrd for BigNat {
    fn partial_cmp(&self, other: &BigNat) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// 全桁の 10 進表示。
impl fmt::Display for BigNat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_decimal())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn b(x: u128) -> BigNat {
        BigNat::from(x)
    }

    #[test]
    fn small_arithmetic_matches_u128() {
        let xs = [0u128, 1, 7, u64::MAX as u128, u64::MAX as u128 + 1, 1 << 100, (1 << 127) - 3, 123_456_789_012_345_678_901];
        for &x in &xs {
            for &y in &xs {
                if let Some(s) = x.checked_add(y) {
                    assert_eq!(b(x).add(&b(y)), b(s));
                }
                assert_eq!(b(x).sub(&b(y)), x.checked_sub(y).map(b));
                assert_eq!(b(x).cmp(&b(y)), x.cmp(&y));
            }
            for k in [0u64, 1, 3, 1000, u64::MAX] {
                if let Some(p) = x.checked_mul(k as u128) {
                    assert_eq!(b(x).mul_small(k), b(p));
                }
            }
            for k in [0u64, 1, 5, 63, 64, 65] {
                if x.leading_zeros() as u64 > k {
                    assert_eq!(b(x).shl(k), b(x << k));
                }
            }
            assert_eq!(b(x).to_decimal(), x.to_string());
            assert_eq!(b(x).bits(), 128 - x.leading_zeros() as u64);
            assert_eq!(b(x).to_u128(), Some(x));
        }
    }

    #[test]
    fn big_values() {
        // 2^200 = 1606938044258990275541962092341162602522202993782792835301376
        let x = BigNat::pow2(200);
        assert_eq!(x.to_decimal(), "1606938044258990275541962092341162602522202993782792835301376");
        assert_eq!(x.decimal_digits(), 61);
        assert_eq!(x.low_digits(10), 2835301376);
        assert_eq!(x.summary(), "1.6069380×10^60（61 桁、末尾 …2835301376）");
        // 10^60 − 1 は 60 桁、10^60 は 61 桁（境目の桁数）
        let mut t = BigNat::from(1u64);
        for _ in 0..60 {
            t = t.mul_small(10);
        }
        assert_eq!(t.decimal_digits(), 61);
        assert_eq!(t.sub_small(1).unwrap().decimal_digits(), 60);
        // 大きな数の桁数と先頭：2^100000 は 30103 桁、先頭 9.9900209…
        let y = BigNat::pow2(100_000);
        assert_eq!(y.decimal_digits(), 30_103);
        assert!(y.scientific(6).starts_with("9.99002"), "{}", y.scientific(6));
    }
}
