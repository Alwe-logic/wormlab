//! 文字が順序数（Γ0 未満）の worm の順序数 o(A)・逆写像・Π 順序数。
//!
//! 出典：D. Fernández-Duque & J. J. Joosten, "Well-orders in the transfinite
//! Japaridze algebra"
//! - I（arXiv:1212.3468）：Thm 5.8 の計算規則 o(A 0 B) = o(B) + 1 + o(A)、
//!   o(ξ↑A) = σ^ξ(o(A))
//! - II（arXiv:1204.4743）：Thm 4.9、Lemma 4.10（超指数関数 e^ξ と Veblen 関数の関係）
//!
//! # 計算規則
//! ```text
//! o(⊤) = 0
//! μ = min A > 0 のとき        o(A) = e^μ( o(μ↓A) )        （μ↓ は各文字に −μ + α）
//! μ = 0 で A = H 0 B のとき   o(A) = o(B) + 1 + o(H)      （H は最初の 0 の手前）
//! ```
//! 超指数関数 e^μ は、μ の Cantor 標準形 ω^{α_1}·c_1 + … + ω^{α_n}·c_n に対して
//! e^μ = e_{α_1}^{c_1} ∘ … ∘ e_{α_n}^{c_n}（右から順に適用）で、
//! ```text
//! e_0(β) = −1 + ω^β
//! e_α(0) = 0,  e_α(β) = φ(α, −1 + β)   （α ≥ 1, β ≥ 1）
//! ```
//! 文字がすべて有限なら e^μ = e_0 の μ 回合成になり、これまでの公式と一致する。
//!
//! 例：o(⟨ω⟩⊤) = ε_0、o(⟨ω⟩⟨ω⟩⊤) = ε_1、o(⟨ω + 1⟩⊤) = ε_ω、
//!     o(⟨ω^2⟩⊤) = φ(2, 0)、o(⟨ε_0⟩⊤) = φ(ε_0, 0)。

use crate::veblen::Veblen;
use crate::worm::Worm;
use std::cmp::Ordering;

/// e_α(β)：超指数関数の「基本の部品」。
pub fn e_sub(alpha: &Veblen, beta: &Veblen) -> Veblen {
    if beta.is_zero() {
        return Veblen::zero();
    }
    if alpha.is_zero() {
        // β ≥ 1 なので ω^β ≥ ω は無限、−1 + ω^β = ω^β
        return Veblen::omega_pow(beta.clone());
    }
    let b = beta.minus_one_plus().expect("β ≥ 1");
    Veblen::phi(alpha.clone(), b)
}

/// e^μ(β)：超指数関数（e^{α+β} = e^α ∘ e^β を満たす）。
pub fn hyperexp(mu: &Veblen, beta: &Veblen) -> Veblen {
    let mut x = beta.clone();
    // 右（小さい項）から順に適用する
    for (alpha, c) in mu.cnf().iter().rev() {
        for _ in 0..*c {
            x = e_sub(alpha, &x);
        }
    }
    x
}

/// ξ↑A：各文字の左に ξ を足す（ξ + α）。
pub fn shift_up(xi: &Veblen, a: &[Veblen]) -> Vec<Veblen> {
    a.iter().map(|x| xi.clone() + x.clone()).collect()
}

/// ξ↓A：各文字から左に ξ を引く（−ξ + α）。ξ より小さい文字があれば `None`。
pub fn shift_down(xi: &Veblen, a: &[Veblen]) -> Option<Vec<Veblen>> {
    a.iter().map(|x| xi.sub_left(x)).collect()
}

fn o_rec(a: &[Veblen]) -> Veblen {
    let Some(mu) = a.iter().min() else {
        return Veblen::zero(); // o(⊤) = 0
    };
    if !mu.is_zero() {
        // A = μ↑(μ↓A)
        let lowered = shift_down(mu, a).expect("μ は最小値");
        return hyperexp(mu, &o_rec(&lowered));
    }
    // A = H 0 B（H は最初の 0 の手前）なら o(A) = o(B) + 1 + o(H)。
    // 0 で一度に分けて A = H_1 0 H_2 0 … 0 H_k とし、右の成分から畳む
    // （B に対して最小値を探し直すと、0 が多いとき O(n²) になる）。
    let mut parts = a.split(|x| x.is_zero()).rev();
    let mut sum = o_rec(parts.next().expect("split は 1 つ以上の成分を返す"));
    for h in parts {
        sum = sum + Veblen::one() + o_rec(h);
    }
    sum
}

/// 逆写像の本体。o(inv(α)) = α となる worm を返す。
fn inv(alpha: &Veblen) -> Vec<Veblen> {
    if alpha.is_zero() {
        return Vec::new();
    }
    // 1 + α = ω^{β_1} + … + ω^{β_k}（重複を許して展開）
    let gamma = alpha.one_plus();
    let mut betas: Vec<Veblen> = Vec::new();
    for (e, c) in gamma.cnf() {
        for _ in 0..c {
            betas.push(e.clone());
        }
    }
    let one = Veblen::one();
    if betas.len() >= 2 {
        // A = (1↑inv(β_k)) 0 inv(−1 + ω^{β_1} + … + ω^{β_{k−1}})
        let last = betas.pop().unwrap();
        let rest = betas.into_iter().fold(Veblen::zero(), |s, b| s + Veblen::omega_pow(b));
        let mut out = shift_up(&one, &inv(&last));
        out.push(Veblen::zero());
        out.extend(inv(&rest.minus_one_plus().expect("1 以上")));
        return out;
    }
    let beta = betas.pop().unwrap();
    if beta < gamma {
        // α = −1 + ω^β（β < ω^β）なので A = 1↑inv(β)
        shift_up(&one, &inv(&beta))
    } else {
        // ω^β = β：α は主項 φ(a, b)（a ≥ 1）。e_a(1 + b) = φ(a, b) なので A = ω^a↑inv(1 + b)
        let (a, b) = alpha.as_phi().expect("ε 型の数は単独の主項");
        let shift = Veblen::omega_pow(a.clone());
        shift_up(&shift, &inv(&b.one_plus()))
    }
}

impl Worm<Veblen> {
    /// o(A) < Γ0。モジュール冒頭の規則で計算する。
    pub fn ordinal(&self) -> Veblen {
        o_rec(self.letters())
    }

    /// α < Γ0 を表す worm（o の逆写像）。
    ///
    /// 【Rust メモ】自然数版の `Worm::from_ordinal` と同じ名前にすると、
    /// `Worm::from_ordinal(…)` と書いたときにどちらか決められなくなる
    /// （引数の型からは選んでくれない）ので、別の名前にしている。
    pub fn from_veblen(alpha: &Veblen) -> Worm<Veblen> {
        Worm::new(inv(alpha))
    }

    /// 同じ順序数を持つ標準形の worm。
    pub fn normal_form(&self) -> Worm<Veblen> {
        Worm::from_veblen(&self.ordinal())
    }

    /// <_0 に関する比較（≡ を同一視した全順序）。
    pub fn cmp0(&self, other: &Worm<Veblen>) -> Ordering {
        self.ordinal().cmp(&other.ordinal())
    }

    /// GLP ⊢ A ↔ B か。
    pub fn equiv(&self, other: &Worm<Veblen>) -> bool {
        self.ordinal() == other.ordinal()
    }

    /// Ω_ξ(A) = o(ξ↓h_ξ(A))：ξ-順序型（Π 順序数）。h_ξ は文字が ξ 以上の最長の先頭部分。
    pub fn pi_ordinal(&self, xi: &Veblen) -> Veblen {
        let head = self.head(xi.clone());
        o_rec(&shift_down(xi, head.letters()).expect("h_ξ の文字は ξ 以上"))
    }

    /// 自然数の worm から作る（各文字 n を順序数 n に）。
    pub fn from_nat(a: &Worm) -> Worm<Veblen> {
        a.map(|&n| Veblen::nat(n as u64))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(s: &str) -> Veblen {
        s.parse().unwrap()
    }

    fn o(s: &str) -> String {
        s.parse::<Worm<Veblen>>().unwrap().ordinal().to_string()
    }

    #[test]
    fn known_values() {
        assert_eq!(o("⊤"), "0");
        assert_eq!(o("<2>"), "ω^ω");
        assert_eq!(o("<ω>"), "ε_0");
        assert_eq!(o("<ω><ω>"), "ε_1");
        assert_eq!(o("<ω><0>"), "ε_0");
        assert_eq!(o("<0><ω>"), "ε_0 + 1");
        assert_eq!(o("<ω + 1>"), "ε_ω");
        assert_eq!(o("<ω·2>"), "ε_(ε_0)");
        assert_eq!(o("<ω^2>"), "φ(2, 0)");
        assert_eq!(o("<ω^ω>"), "φ(ω, 0)");
        assert_eq!(o("<ε_0>"), "φ(ε_0, 0)");
    }

    #[test]
    fn hyperexp_composition() {
        // e^{α+β} = e^α ∘ e^β
        let (a, b, x) = (v("ω + 2"), v("ω^2 + 1"), v("ε_0 + 3"));
        assert_eq!(hyperexp(&(a.clone() + b.clone()), &x), hyperexp(&a, &hyperexp(&b, &x)));
        // 有限なら e^n = e_0 の n 回合成
        assert_eq!(hyperexp(&v("2"), &v("1")), v("ω^ω"));
    }

    #[test]
    fn inverse_examples() {
        for s in ["0", "5", "ω", "ω·2 + 1", "ε_0", "ε_0 + ω", "ε_1", "ε_ω", "φ(2, 0)", "φ(ω, 3) + ε_0", "φ(ε_0, 0)"] {
            let a = v(s);
            let w = Worm::from_veblen(&a);
            assert_eq!(w.ordinal(), a, "{s} ↦ {w}");
        }
    }
}
