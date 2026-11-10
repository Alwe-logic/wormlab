//! Veblen 関数 φ と、Ω・ψ による順序数の正規形。
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
//!
//! # Γ0 を超える：Ω と ψ（Worms and spiders, arXiv:1605.08867, Def 6.19）
//!
//! 主項として Ω（最初の非可算順序数）と ψ(ξ) も使える。C(ξ) は {0, 1, Ω} を含み、
//! 超指数関数（＝ 加法と φ）と ψ↾ξ で閉じた最小の集合、ψ(ξ) は C(ξ) に入らない最小の数。
//! ψ(0) = Γ0、ψ(1) = Γ1、…、ψ(Ω) は α ↦ Γ_α の最初の不動点、
//! ψ(ε_{Ω+1}) が Bachmann–Howard 順序数。表せるのは ψ(Γ_{Ω+1}) 未満。
//!
//! Ω と ψ(ξ) は**強臨界数**（φ(α, ·) の不動点がすべての α < 自分 について成り立つ数）で、
//! φ(α, s) = s（α < s）、φ(s, 0) = s となる。比較では s を「φ(s, 0)」とみなす。
//!
//! 正規形の ψ(ξ) は ξ ∈ C(ξ) のものだけ。正規形の項 t について
//! t ∈ C(ξ) ⟺ K(t) < ξ（K(t) は t の中で他の ψ の内側にない ψ の引数の集合）
//! なので、C の判定は形だけでできる。ξ ∉ C(ξ) のときの ψ(ξ) は、
//! ξ 以上で C(z) ∋ z となる最小の z について ψ(z) に等しい（[`Veblen::psi`]）。

use crate::i18n::tr;
use crate::latex::ToLatex;
use crate::ordinal::Ordinal;
use std::cmp::Ordering;
use std::fmt;
use std::ops::Add;
use std::str::FromStr;

/// 主項（加法的に分解できない数）。外から直接作らせず、必ず [`Veblen::phi`]・
/// [`Veblen::big_omega`]・[`Veblen::psi`] を通す（正規形を保つため）。
///
/// 【Rust メモ】`enum` の各「変種」は別々の形のデータを持てる。`V(a, b)` は 2 つの
/// 順序数を持ち、`Omega` は何も持たず、`Psi(x)` は 1 つ持つ。
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Prin {
    /// φ(a, b)（b < φ(a, b)）
    V(Veblen, Veblen),
    /// Ω
    Omega,
    /// ψ(x)（x ∈ C(x)）
    Psi(Veblen),
}

impl Prin {
    /// 強臨界数（Ω か ψ(x)）か。
    fn is_critical(&self) -> bool {
        !matches!(self, Prin::V(..))
    }

    fn to_veblen(&self) -> Veblen {
        Veblen { terms: vec![(self.clone(), 1)] }
    }
}

/// 順序数（正規形）。
///
/// 【Rust メモ】`Prin` が `Veblen` を含み、`Veblen` が `Vec<(Prin, u64)>` を含む
/// 「相互再帰」の型。`Vec` は中身をヒープに置くので、型の大きさは有限で済む。
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default, PartialOrd, Ord)]
pub struct Veblen {
    terms: Vec<(Prin, u64)>,
}

// ----------------------------------------------------------------------
// 比較
// ----------------------------------------------------------------------

/// 主項どうしの比較。正規形 x = φ(a1, b1), y = φ(a2, b2) について
/// - a1 = a2 なら b1 と b2 の比較
/// - a1 < a2 なら b1 と y の比較（φ(a1, ·) は y を不動点に持つので）
/// - a1 > a2 なら x と b2 の比較（φ(a2, ·) は x を不動点に持つので）
///
/// 強臨界数 s は φ(s, 0) とみなして同じ規則を使う。強臨界数どうしは
/// ψ(x) < Ω、ψ(x) と ψ(y) は x と y の比較（どちらも正規形なので）。
///
/// 【Rust メモ】`derive` ではなく `impl Ord` を手で書くと、比較の意味を
/// 自分で決められる。`Veblen` の方は `derive(Ord)` のままで、
/// 「項の列の辞書式順序」になる（中の `Prin` の比較にはこの実装が使われる）。
impl Ord for Prin {
    fn cmp(&self, other: &Prin) -> Ordering {
        use Prin::*;
        match (self, other) {
            (V(a1, b1), V(a2, b2)) => match a1.cmp(a2) {
                Ordering::Equal => b1.cmp(b2),
                Ordering::Less => cmp_with_prin(b1, other),
                Ordering::Greater => cmp_with_prin(b2, self).reverse(),
            },
            (V(a, b), s) => cmp_phi_critical(a, b, s),
            (s, V(a, b)) => cmp_phi_critical(a, b, s).reverse(),
            (Omega, Omega) => Ordering::Equal,
            (Psi(_), Omega) => Ordering::Less,
            (Omega, Psi(_)) => Ordering::Greater,
            (Psi(x), Psi(y)) => x.cmp(y),
        }
    }
}

impl PartialOrd for Prin {
    fn partial_cmp(&self, other: &Prin) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// φ(a, b) と強臨界数 s（= φ(s, 0)）の比較。
fn cmp_phi_critical(a: &Veblen, b: &Veblen, s: &Prin) -> Ordering {
    match cmp_with_prin(a, s) {
        // a < s：s は φ(a, ·) の不動点なので、b と s の比較（正規形では b ≠ s）
        Ordering::Less => cmp_with_prin(b, s),
        // a = s：φ(s, b) と φ(s, 0) の比較
        Ordering::Equal if b.is_zero() => Ordering::Equal,
        _ => Ordering::Greater,
    }
}

/// 順序数 v と、単独の主項 p（係数 1）の比較。
fn cmp_with_prin(v: &Veblen, p: &Prin) -> Ordering {
    match v.terms.first() {
        None => Ordering::Less, // 0 < p
        Some((q, c)) => match q.cmp(p) {
            Ordering::Equal if *c > 1 || v.terms.len() > 1 => Ordering::Greater,
            o => o,
        },
    }
}

/// 主項 q の「一つ目の引数」（強臨界数なら q 自身）が a より大きいか。
/// そのとき q は φ(a, ·) の不動点。
fn level_above(q: &Prin, a: &Veblen) -> bool {
    match q {
        Prin::V(qa, _) => qa > a,
        s => cmp_with_prin(a, s) == Ordering::Less,
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

    /// Ω（最初の非可算順序数）
    pub fn big_omega() -> Self {
        Prin::Omega.to_veblen()
    }

    /// φ(a, b)。不動点になる場合（b が φ(c, d) で c > a、または b が a より大きい
    /// 強臨界数）は b を返し、φ(s, 0)（s は強臨界数）は s を返す。
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
            && level_above(q, &a)
        {
            // b は φ(a, ·) の不動点
            return Veblen { terms: vec![(q.clone(), c)] };
        }
        if b.is_zero()
            && let [(s, 1)] = a.terms.as_slice()
            && s.is_critical()
        {
            // φ(s, 0) = s
            return Veblen { terms: vec![(s.clone(), c)] };
        }
        Veblen { terms: vec![(Prin::V(a, b), c)] }
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

    /// x·n（[`Veblen::mul_nat`]）。係数が u64 に収まらなければ `None`。
    pub fn checked_mul_nat(&self, n: u64) -> Option<Veblen> {
        if n == 0 || self.is_zero() {
            return Some(Self::zero());
        }
        let mut terms = self.terms.clone();
        terms[0].1 = terms[0].1.checked_mul(n)?;
        Some(Veblen { terms })
    }

    /// x + y（`+` と同じ）。まとめた係数が u64 に収まらなければ `None`。
    ///
    /// 【Rust メモ】`checked_add` は、あふれたら `None` を返す足し算。`?` で `None` をそのまま返せる
    pub fn checked_add(&self, rhs: &Veblen) -> Option<Veblen> {
        let Some((lead, lead_c)) = rhs.terms.first() else {
            return Some(self.clone());
        };
        let mut terms = Vec::new();
        let mut merged = *lead_c;
        for (p, c) in &self.terms {
            match p.cmp(lead) {
                Ordering::Greater => terms.push((p.clone(), *c)),
                Ordering::Equal => merged = merged.checked_add(*c)?,
                Ordering::Less => break,
            }
        }
        terms.push((lead.clone(), merged));
        terms.extend(rhs.terms.iter().skip(1).cloned());
        Some(Veblen { terms })
    }

    /// α = β + n（β は 0 か極限、n は有限）と分けて (β, n) を返す。
    pub fn split_nat(&self) -> (Veblen, u64) {
        let mut terms = self.terms.clone();
        match terms.last() {
            Some((Prin::V(a, b), c)) if a.is_zero() && b.is_zero() => {
                let n = *c;
                terms.pop();
                (Veblen { terms }, n)
            }
            _ => (self.clone(), 0),
        }
    }

    /// 書き方の大きさ：主項（φ・Ω・ψ）の数を、引数の中まで数えたもの。
    pub fn size(&self) -> usize {
        self.terms
            .iter()
            .map(|(p, _)| match p {
                Prin::V(a, b) => 1 + a.size() + b.size(),
                Prin::Omega => 1,
                Prin::Psi(x) => 1 + x.size(),
            })
            .sum()
    }

    /// ψ(x)（Worms and spiders, Def 6.19）。x ∈ C(x)（K(x) < x）ならそのまま正規形の ψ(x)。
    /// そうでなければ、x 以上で z ∈ C(z) となる最小の z を探して ψ(z) を返す
    /// （C(·) は区間 [x, z] で変わらないので ψ(x) = ψ(z)）。
    ///
    /// z の探し方：κ = max K(x) ≥ x なら、κ 自身は正規形なので z ≤ κ。そこで
    /// x を「C(κ) に入る x 以上の最小の数」に切り上げる（[`ceil_c`]）。z もそこに入るので
    /// 切り上げても z を飛び越えない。切り上げた数の K は κ 未満になるので、
    /// max K が真に減っていき、いつか止まる。
    pub fn psi(x: Veblen) -> Veblen {
        let mut x = x;
        loop {
            match x.max_k() {
                Some(k) if k >= x => x = ceil_c(&x, &k),
                _ => return Prin::Psi(x).to_veblen(),
            }
        }
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
            [(Prin::V(a, b), c)] if a.is_zero() && b.is_zero() => Some(*c),
            _ => None,
        }
    }

    pub fn is_finite(&self) -> bool {
        self.as_nat().is_some()
    }

    /// 後続順序数か（最後の項が 1 = φ(0, 0)）。
    pub fn is_successor(&self) -> bool {
        matches!(self.terms.last(), Some((Prin::V(a, b), _)) if a.is_zero() && b.is_zero())
    }

    pub fn is_limit(&self) -> bool {
        !self.is_zero() && !self.is_successor()
    }

    /// 加法的に分解できない（単独の主項・係数 1）か。
    pub fn is_principal(&self) -> bool {
        matches!(self.terms.as_slice(), [(_, 1)])
    }

    /// 単独の主項 φ(a, b) なら (a, b)。Ω・ψ(x) では `None`（[`Veblen::phi_parts`] を参照）。
    pub fn as_phi(&self) -> Option<(&Veblen, &Veblen)> {
        match self.terms.as_slice() {
            [(Prin::V(a, b), 1)] => Some((a, b)),
            _ => None,
        }
    }

    /// 単独の主項を φ(a, b) の形で：強臨界数 s は (s, 0)。
    pub fn phi_parts(&self) -> Option<(Veblen, Veblen)> {
        match self.terms.as_slice() {
            [(Prin::V(a, b), 1)] => Some((a.clone(), b.clone())),
            [(s, 1)] => Some((s.to_veblen(), Veblen::zero())),
            _ => None,
        }
    }

    /// Ω も ψ も含まない（Γ0 未満）か。
    pub fn is_predicative(&self) -> bool {
        self.terms.iter().all(|(p, _)| match p {
            Prin::V(a, b) => a.is_predicative() && b.is_predicative(),
            _ => false,
        })
    }

    /// 可算（Ω 未満）か。
    pub fn is_countable(&self) -> bool {
        self < &Veblen::big_omega()
    }

    /// 単独の主項が ψ(x) なら x。
    pub fn as_psi(&self) -> Option<&Veblen> {
        match self.terms.as_slice() {
            [(Prin::Psi(x), 1)] => Some(x),
            _ => None,
        }
    }

    /// K(t) の最大値：他の ψ の内側にない ψ の引数のうち最大のもの。なければ `None`。
    pub fn max_k(&self) -> Option<Veblen> {
        let mut best: Option<Veblen> = None;
        let mut offer = |k: Option<Veblen>| {
            if let Some(k) = k
                && best.as_ref().is_none_or(|b| k > *b)
            {
                best = Some(k);
            }
        };
        for (p, _) in &self.terms {
            match p {
                Prin::V(a, b) => {
                    offer(a.max_k());
                    offer(b.max_k());
                }
                Prin::Omega => {}
                Prin::Psi(x) => offer(Some(x.clone())),
            }
        }
        best
    }

    /// t ∈ C(ξ)（正規形の t について K(t) < ξ）。
    pub fn in_c(&self, xi: &Veblen) -> bool {
        self.max_k().is_none_or(|k| k < *xi)
    }

    /// 主項と係数の列（主項はそれだけの順序数として）。
    pub fn principal_terms(&self) -> impl Iterator<Item = (Veblen, u64)> + '_ {
        self.terms.iter().map(|(p, c)| (p.to_veblen(), *c))
    }

    /// 主項 φ(a, b) と係数の列 (a, b, c)。強臨界数 s は (s, 0)。
    pub fn terms(&self) -> impl Iterator<Item = (Veblen, Veblen, u64)> + '_ {
        self.terms.iter().map(|(p, c)| {
            let (a, b) = p.to_veblen().phi_parts().expect("単独の主項");
            (a, b, *c)
        })
    }

    /// Cantor 標準形 ω^{e_1}·c_1 + … の指数の列（係数つき）。
    /// φ(0, b) の指数は b、φ(a, b)（a > 0）・Ω・ψ(x) は ω^x = x となる数なので指数は自分自身。
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
    /// 最後の項が強臨界数 s なら (β, s, 0, c)。
    pub fn split_last(&self) -> Option<(Veblen, Veblen, Veblen, u64)> {
        let mut terms = self.terms.clone();
        let (p, c) = terms.pop()?;
        let (a, b) = p.to_veblen().phi_parts().expect("単独の主項");
        Some((Veblen { terms }, a, b, c))
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
    /// Ω・ψ を含む数では（まだ）定義していないので `None`。
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
        if self.is_zero() || !self.is_predicative() {
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
        let Prin::V(a, b) = &p else { unreachable!("述語的な数の主項は φ") };
        Some(Veblen { terms } + fundamental_phi(a, b, n))
    }

    /// ε0 未満なら Cantor 標準形の [`Ordinal`] に変換する。
    pub fn to_cnf(&self) -> Option<Ordinal> {
        let mut out = Ordinal::zero();
        for (p, c) in &self.terms {
            match p {
                Prin::V(a, b) if a.is_zero() => out = out + Ordinal::omega_pow_mul(b.to_cnf()?, *c),
                _ => return None,
            }
        }
        Some(out)
    }
}

/// x 以上で C(κ) に入る最小の数（K(z) < κ となる最小の z ≥ x）。
///
/// x = P_1·c_1 + P_2·c_2 + …（主項は減少）で、最初に C(κ) に入らない主項 P_i を
/// 「C(κ) に入る P_i より大きい最小の主項」に置き換え、後ろを捨てる（[`next_prin`]）。
fn ceil_c(x: &Veblen, k: &Veblen) -> Veblen {
    let mut prefix = Veblen::zero();
    for (p, c) in &x.terms {
        if p.to_veblen().in_c(k) {
            prefix.terms.push((p.clone(), *c));
        } else {
            return prefix + next_prin(p, k);
        }
    }
    x.clone()
}

/// C(κ) に入らない主項 P より大きく、C(κ) に入る最小の主項。
/// - P が可算：C(κ) の可算な部分は ψ(κ) 未満の数全体で P はその外なので、答えは Ω。
/// - P = φ(a, b)、a ∈ C(κ)：φ(a, ceil(b))。
/// - P = φ(a, b)、a ∉ C(κ)：a' = ceil(a) として φ(a', ceil(e))（e は φ(a', e) > b となる最小の数）。
///
/// （証明：答え Q の正規形を φ(c, d) とすると、c < a なら d > P で d の先頭の主項が
/// もっと小さい答えになるので c ≥ a。c = a なら d ≥ ceil(b)。c > a なら Q は φ(a, ·)
/// （または φ(a', ·)）の不動点で、Q = φ(a, Q) と書き直せる。）
fn next_prin(p: &Prin, k: &Veblen) -> Veblen {
    let pv = p.to_veblen();
    if pv.is_countable() {
        return Veblen::big_omega();
    }
    match p {
        Prin::V(a, b) => {
            if a.in_c(k) {
                Veblen::phi(a.clone(), ceil_c(b, k))
            } else {
                let a2 = ceil_c(a, k);
                let e = least_arg_above(&a2, b);
                Veblen::phi(a2, ceil_c(&e, k))
            }
        }
        _ => unreachable!("Ω は C(κ) に入り、ψ(x) は可算"),
    }
}

/// φ(a, e) > b となる最小の e。
fn least_arg_above(a: &Veblen, b: &Veblen) -> Veblen {
    if *b < Veblen::phi(a.clone(), Veblen::zero()) {
        return Veblen::zero();
    }
    // φ(a, e) は主項なので、φ(a, e) > b ⟺ φ(a, e) > B（B は b の先頭の主項）
    let lead = &b.terms[0].0;
    match lead {
        Prin::V(c, d) => match a.cmp(c) {
            // B は φ(a, ·) の不動点：φ(a, e) > B ⟺ e > B
            Ordering::Less => lead.to_veblen() + Veblen::one(),
            Ordering::Equal => d.clone() + Veblen::one(),
            // φ(a, e) > φ(c, d) ⟺ φ(a, e) > d
            Ordering::Greater => least_arg_above(a, d),
        },
        s => match cmp_with_prin(a, s) {
            Ordering::Less => s.to_veblen() + Veblen::one(),
            Ordering::Equal => Veblen::one(),
            Ordering::Greater => Veblen::zero(),
        },
    }
}

/// 極限の主項 φ(a, b)（1 = φ(0, 0) 以外、述語的）の基本列。
fn fundamental_phi(a: &Veblen, b: &Veblen, n: u64) -> Veblen {
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

fn cnf_exponent(p: &Prin) -> Veblen {
    match p {
        Prin::V(a, b) if a.is_zero() => b.clone(),
        _ => p.to_veblen(),
    }
}

impl From<&Ordinal> for Veblen {
    /// Cantor 標準形（ε0 未満）からの変換。
    fn from(x: &Ordinal) -> Veblen {
        let terms = x.terms().iter().map(|(e, c)| (Prin::V(Veblen::zero(), Veblen::from(e)), *c)).collect();
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
                if let Prin::V(a, b) = p
                    && a.is_zero()
                    && b.is_zero()
                {
                    return c.to_string(); // 有限部分
                }
                let base = prin_to_string(p);
                if *c == 1 { base } else { format!("{base}·{c}") }
            })
            .collect();
        write!(f, "{}", parts.join(" + "))
    }
}

impl ToLatex for Veblen {
    /// `\omega^{\omega}\cdot 2 + 3`、`\varepsilon_{0}`、`\varphi(2, 0)` のように書く。
    /// 指数・添字は { } でくくるので、表示のような括弧は要らない。
    fn to_latex(&self) -> String {
        if self.is_zero() {
            return "0".to_string();
        }
        let parts: Vec<String> = self
            .terms
            .iter()
            .map(|(p, c)| {
                let base = match p {
                    Prin::Omega => "\\Omega".to_string(),
                    Prin::Psi(x) => format!("\\psi({})", x.to_latex()),
                    Prin::V(a, b) if a.is_zero() && b.is_zero() => return c.to_string(),
                    Prin::V(a, b) if a.is_zero() => {
                        if b.as_nat() == Some(1) { "\\omega".to_string() } else { format!("\\omega^{{{}}}", b.to_latex()) }
                    }
                    Prin::V(a, b) if a.as_nat() == Some(1) => format!("\\varepsilon_{{{}}}", b.to_latex()),
                    Prin::V(a, b) => format!("\\varphi({}, {})", a.to_latex(), b.to_latex()),
                };
                if *c == 1 { base } else { format!("{base} \\cdot {c}") }
            })
            .collect();
        parts.join(" + ")
    }
}

fn prin_to_string(p: &Prin) -> String {
    let (a, b) = match p {
        Prin::Omega => return "Ω".to_string(),
        Prin::Psi(x) => return format!("ψ({x})"),
        Prin::V(a, b) => (a, b),
    };
    if a.is_zero() {
        match b.as_nat() {
            Some(1) => "ω".to_string(),
            _ if b.is_finite() || b.is_principal() => format!("ω^{b}"),
            _ => format!("ω^({b})"),
        }
    } else if a.as_nat() == Some(1) {
        if b.is_finite() || *b == Veblen::omega() || *b == Veblen::big_omega() {
            format!("ε_{b}")
        } else {
            format!("ε_({b})")
        }
    } else {
        format!("φ({a}, {b})")
    }
}

// ----------------------------------------------------------------------
// パーサ
// ----------------------------------------------------------------------
//
//   expr   := term ('+' term)*
//   term   := factor (('·' | '*') 自然数)?
//   factor := 自然数 | ('ω' | 'w') ('^' factor)? | ('ε' | 'e') '_' factor
//           | ('φ' | 'phi') '(' expr ',' expr ')' | ('Ω' | 'O') | ('ψ' | 'psi') '(' expr ')'
//           | '(' expr ')'

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseOrdinalError(pub String);

impl fmt::Display for ParseOrdinalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", tr("順序数として読めません", "cannot read as an ordinal"), self.0)
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
        Err(ParseOrdinalError(if crate::i18n::is_en() { format!("near “{rest}”") } else { format!("「{rest}」の付近") }))
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
        if self.eat('Ω') || self.eat('O') {
            return Ok(Veblen::big_omega());
        }
        if self.eat_str("psi") || self.eat('ψ') {
            if !self.eat('(') {
                return self.err();
            }
            let x = self.expr()?;
            if !self.eat(')') {
                return self.err();
            }
            return Ok(Veblen::psi(x));
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

/// `"ω^(ω + 1)·2 + 3"`, `"ε_0"`, `"e_(w+1)"`, `"φ(2, 0)"`, `"phi(w, 1)"`、
/// `"ψ(ε_(Ω + 1))"`, `"psi(O·2)"` などを読む。
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
    fn psi_known_values() {
        // ψ(0) = Γ0 はどの述語的な数より大きい
        assert!(v("ψ(0)") > v("φ(φ(φ(2, 0), 0), 0)"));
        assert!(v("ψ(0)") > v("φ(ω^ω + 1, ε_(φ(3, 0)))"));
        // 強臨界数：φ(a, s) = s（a < s）、φ(s, 0) = s、ω^s = s
        assert_eq!(v("φ(1, ψ(0))"), v("ψ(0)"));
        assert_eq!(v("ω^ψ(0)"), v("ψ(0)"));
        assert_eq!(v("φ(ψ(0), 0)"), v("ψ(0)"));
        assert_eq!(v("φ(ω, Ω)"), v("Ω"));
        assert_eq!(v("φ(ψ(Ω), Ω)"), v("Ω"));
        assert_eq!(v("φ(Ω, 0)"), v("Ω"));
        // Γ0 < φ(Γ0, 1) < Γ1 = ψ(1) < … < ψ(ω) < ψ(Γ0) < ψ(Ω)
        let chain = [
            "φ(ψ(0), 0) + 1", "φ(1, ψ(0) + 1)", "φ(ψ(0), 1)", "φ(ψ(0) + 1, 0)", "ψ(1)", "ψ(2)", "ψ(ω)",
            "ψ(ψ(0))", "ψ(ψ(ψ(0)))", "ψ(Ω)", "ψ(Ω) + 1", "ψ(Ω + 1)", "ψ(Ω + ψ(Ω))", "ψ(Ω·2)",
            "ψ(ω^(Ω + 1))", "ψ(ε_(Ω + 1))", "ψ(φ(Ω, 1))", "ψ(φ(Ω, ω))", "Ω", "Ω + ψ(Ω)", "Ω·2",
            "ε_(Ω + 1)", "φ(Ω, 1)", "φ(Ω, Ω)", "φ(Ω + 1, 0)", "φ(φ(Ω, 1), 0)",
        ];
        assert!(v("ψ(0)") < v(chain[0]));
        for w in chain.windows(2) {
            assert!(v(w[0]) < v(w[1]), "{} < {} のはず", w[0], w[1]);
        }
    }

    #[test]
    fn psi_collapse() {
        // ξ ∉ C(ξ) なら、ξ 以上で C(z) ∋ z となる最小の z について ψ(ξ) = ψ(z)
        assert_eq!(v("ψ(ψ(Ω))"), v("ψ(Ω)"));
        assert_eq!(v("ψ(ψ(Ω) + 1)"), v("ψ(Ω)"));
        assert_eq!(v("ψ(ψ(Ω)·2)"), v("ψ(Ω)"));
        assert_eq!(v("ψ(Ω + ψ(Ω·2))"), v("ψ(Ω·2)"));
        // ψ(Ω·2 + 1) は ψ(Ω·2) より大きいが、Ω + ψ(Ω·2 + 1) からは ψ(Ω·2) までしか届かない
        assert_eq!(v("ψ(Ω + ψ(Ω·2 + 1))"), v("ψ(Ω·2)"));
        assert_eq!(v("ψ(ψ(ε_(Ω + 1)))"), v("ψ(Ω)"));
        // 正規形の例（K(ξ) < ξ）
        assert_eq!(v("ψ(Ω + ψ(Ω))").as_psi(), Some(&v("Ω + ψ(Ω)")));
        assert_eq!(v("ψ(ψ(0))").as_psi(), Some(&v("ψ(0)")));
        // 表示と読み直し
        for s in ["ψ(0)", "Ω", "ψ(Ω + ψ(Ω))·2 + ω", "φ(Ω, ψ(Ω) + 1)", "ε_(Ω + 1)", "ω^(Ω + 1)", "ψ(φ(Ω, ω))"] {
            assert_eq!(v(s).to_string(), s);
        }
        assert!(v("ψ(Ω)").is_countable() && !v("Ω").is_countable() && !v("ψ(0)").is_predicative());
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
