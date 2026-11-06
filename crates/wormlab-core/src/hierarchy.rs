//! 基本列を使って定義される急増加関数と、battle の長さ。
//!
//! # Hardy 階層
//! ```text
//! H_0(n)     = n
//! H_{α+1}(n) = H_α(n + 1)
//! H_λ(n)     = H_{λ[n]}(n)          （λ は極限、λ[n] は標準の基本列）
//! ```
//! 例：H_k(n) = n + k、H_ω(n) = 2n、H_{ω·2}(n) = 4n、H_{ω^2}(n) = 2^n·n。
//!
//! # 急増加関数（fast-growing hierarchy）
//! f_0(n) = n + 1、f_{α+1}(n) = f_α^n(n)（n 回合成）、f_λ(n) = f_{λ[n]}(n)。
//! ε0 未満では f_α = H_{ω^α} が成り立つので、ここでは H 経由で計算する
//! （テストでは直接の定義と突き合わせる）。
//!
//! 値はすぐに天文学的な大きさになるので、計算はすべて
//! 「上限を超えたら打ち切り」（`None`）にしている。
//!
//! # battle の長さ
//! - 順序数の battle：α → α{k}（後続なら直前、極限なら α[k]）を k = 1, 2, … で繰り返す。
//!   終わったときの k は、基本列を λ[k] + 1 にずらした Hardy 関数 H'_α(1) に等しい。
//! - worm の battle：worm（括弧語）の基本列 a{k} を繰り返す（Beklemishev の worm battle）。
//!   こちらは worm の形に依存し、順序数の標準基本列とは少しずれる（例：ω²{2} = ω·2 + 1）。

use crate::bracket::Bracket;
use crate::veblen::Veblen;
use crate::worm::Worm;

/// 計算の打ち切り条件。
#[derive(Clone, Copy, Debug)]
pub struct Budget {
    /// 基本列を取る回数の上限
    pub max_steps: u64,
}

impl Default for Budget {
    fn default() -> Self {
        Budget { max_steps: 10_000_000 }
    }
}

/// Hardy 関数 H_α(n)。上限を超えたら `None`。
pub fn hardy(alpha: &Veblen, n: u128, budget: Budget) -> Option<u128> {
    let (mut a, mut n) = (alpha.clone(), n);
    let mut steps = 0u64;
    // 【Rust メモ】`while let パターン = 式` は「パターンに合う間は繰り返す」。
    while let Some((beta, x, y, c)) = a.split_last() {
        if x.is_zero() && y.is_zero() {
            // 末尾の有限部分 c はまとめて：H_{β+c}(n) = H_β(n + c)
            n = n.checked_add(c as u128)?;
            a = beta;
        } else if x.is_zero() && y.as_nat() == Some(1) {
            // 末尾が ω·c なら H_{β+ω·c}(n) = H_β(n·2^c)
            let factor = 1u128.checked_shl(u32::try_from(c).ok()?)?;
            n = n.checked_mul(factor)?;
            a = beta;
        } else {
            steps += 1;
            if steps > budget.max_steps {
                return None;
            }
            a = a.fundamental(u64::try_from(n).ok()?).expect("極限");
        }
    }
    Some(n)
}

/// 急増加関数 f_α(n) = H_{ω^α}(n)（α < ε0 で直接の定義と一致）。
pub fn fast_growing(alpha: &Veblen, n: u128, budget: Budget) -> Option<u128> {
    hardy(&Veblen::omega_pow(alpha.clone()), n, budget)
}

/// 順序数の battle：k = start, start+1, … として α ← α{k} を 0 になるまで繰り返した回数。
pub fn ordinal_battle_length(alpha: &Veblen, start: u64, budget: Budget) -> Option<u64> {
    let (mut a, mut k, mut steps) = (alpha.clone(), start, 0u64);
    while !a.is_zero() {
        // 有限部分 m だけが残ったら、あと m 回で終わる
        if let Some(m) = a.as_nat() {
            return steps.checked_add(m);
        }
        steps += 1;
        if steps > budget.max_steps {
            return None;
        }
        a = a.fundamental(k).expect("0 でない");
        k += 1;
    }
    Some(steps)
}

/// worm（括弧語）の battle の長さ：⊤ になるまでの回数。
pub fn worm_battle_length(a: &Bracket, budget: Budget) -> Option<u64> {
    let mut steps = 0u64;
    for _ in a.battle().skip(1) {
        steps += 1;
        if steps > budget.max_steps {
            return None;
        }
    }
    Some(steps)
}

/// 文字が有限の worm の battle の長さ（括弧語版より速い）。
pub fn worm_battle_length_finite(a: &Worm, budget: Budget) -> Option<u64> {
    let mut steps = 0u64;
    for _ in a.battle().skip(1) {
        steps += 1;
        if steps > budget.max_steps {
            return None;
        }
    }
    Some(steps)
}

/// α から始めた worm battle の長さ（α の正規形の worm から出発）。
/// ε0 未満なら文字が有限の worm で、それ以上なら括弧語で数える。
pub fn worm_battle_length_of(alpha: &Veblen, budget: Budget) -> Option<u64> {
    match alpha.to_cnf() {
        Some(c) => worm_battle_length_finite(&Worm::from_ordinal(&c), budget),
        None => worm_battle_length(&Bracket::from_ordinal(alpha), budget),
    }
}

/// α の正規形の括弧語から 1 ステップ進めたときの順序数（worm が作る「基本列」）。
pub fn worm_fundamental(alpha: &Veblen, n: usize) -> Option<Veblen> {
    Bracket::from_ordinal(alpha).fundamental(n).map(|b| b.ordinal())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(s: &str) -> Veblen {
        s.parse().unwrap()
    }

    fn h(s: &str, n: u128) -> Option<u128> {
        hardy(&v(s), n, Budget::default())
    }

    #[test]
    fn hardy_values() {
        assert_eq!(h("0", 5), Some(5));
        assert_eq!(h("7", 5), Some(12));
        assert_eq!(h("ω", 5), Some(10));
        assert_eq!(h("ω + 3", 5), Some(16));
        assert_eq!(h("ω·2", 5), Some(20));
        assert_eq!(h("ω^2", 3), Some(24));
        assert_eq!(h("ω^2", 10), Some(10 * 1024));
        assert_eq!(h("ω^2 + ω", 3), Some(6 * 64));
        assert_eq!(h("ω^ω", 2), Some(8)); // ω^ω[2] = ω^2
        assert_eq!(h("ε_0", 3), None); // 値が大きすぎて打ち切り
    }

    #[test]
    fn fast_growing_values() {
        let f = |s: &str, n: u128| fast_growing(&v(s), n, Budget::default());
        assert_eq!(f("0", 5), Some(6));
        assert_eq!(f("1", 5), Some(10));
        assert_eq!(f("2", 3), Some(24));
        assert_eq!(f("ω", 2), Some(8));
    }

    #[test]
    fn battle_lengths() {
        let b = Budget::default();
        assert_eq!(ordinal_battle_length(&v("3"), 1, b), Some(3));
        // ω → 1 → 0
        assert_eq!(ordinal_battle_length(&v("ω"), 1, b), Some(2));
        // worm の battle：(()) = ω → ()() → () → ⊤
        assert_eq!(worm_battle_length(&"(())".parse().unwrap(), b), Some(3));
    }
}
