//! RC_BI の式の順序 <¹₁ と基本列（Pakhomov–Lazar, arXiv:2610.20115, §4）。
//!
//! # 順序（Def 4.1）
//! W_BI（変数・∇・⟨1⟩_ω を含まない式）の上で
//! - A <¹₁ B :⟺ B ⊢ ⟨1⟩₁A（B の理論は A の理論の Π¹₁ 反映を示す）
//! - A ≡¹₁ B :⟺ ∇A ⊣⊢ ∇B（同じ Π¹₁ 定理をもつ）
//!
//! Thm 4.11：≤¹₁ は W_BI 上の線形で整礎な前順序。だから W_BI/≡¹₁ は整列順序で、
//! 各式 A は順序数 o(A)（自分より下の同値類の個数）を表す。o(A) の理論の
//! 証明論的順序数は ε_{o(A)}（Cor 6.6）。
//!
//! # 形と基本列（Def 4.5, 4.6）
//! ∧ をほどいた成分（top conjuncts、⊤ は除く）を見て
//! - 零：成分がない（A ≡ ⊤、o(A) = 0）
//! - 後続形：成分がすべて ⟨1⟩₁B の形。A = ⟨1⟩₁B₁ ∧ … ∧ ⟨1⟩₁B_k の直前は B_i のうち最大のもの
//! - 極限形：↓B か ⟨i⟩_α B（α ≥ 2）の成分がある。近似 (A)_n（n ≥ 1）が A への基本列になる
//!   （Lemma 4.7：(A)_n <¹₁ A。Lemma 4.10 と線形性から、A より下のどの式も
//!   ある (A)_n 以下になる）
//!
//! 近似の定義は [`approx`] を参照。

use crate::i18n::tr;
use crate::rcbi::{Formula, Rank, entails};
use std::cmp::Ordering;

// ----------------------------------------------------------------------
// 順序
// ----------------------------------------------------------------------

/// A <¹₁ B（B ⊢ ⟨1⟩₁A）。
pub fn lt(a: &Formula, b: &Formula) -> bool {
    entails(b, &Formula::one(1, a.clone()))
}

/// A ≡¹₁ B（∇A ⊣⊢ ∇B）。∇A ⊢ ∇B は A ⊢ ∇B と同じ（公理 3・7 と Mod₃）。
pub fn equiv(a: &Formula, b: &Formula) -> bool {
    entails(a, &Formula::nabla(b.clone())) && entails(b, &Formula::nabla(a.clone()))
}

/// <¹₁ での比較。どれにも当てはまらなければ `None`（Thm 4.11 により W_BI では起こらない）。
pub fn compare(a: &Formula, b: &Formula) -> Option<Ordering> {
    if lt(a, b) {
        Some(Ordering::Less)
    } else if lt(b, a) {
        Some(Ordering::Greater)
    } else if equiv(a, b) {
        Some(Ordering::Equal)
    } else {
        None
    }
}

// ----------------------------------------------------------------------
// 形
// ----------------------------------------------------------------------

/// 式の形（Def 4.5）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Form {
    /// ⊤ と同値（o = 0）
    Zero,
    /// 後続形。中身は直前の式（o(A) = o(直前) + 1）
    Successor(Formula),
    /// 極限形。近似 (A)_n が基本列
    Limit,
}

/// ⊤ 以外の top conjuncts。
fn conjuncts(a: &Formula) -> Vec<&Formula> {
    a.top_conjuncts().into_iter().filter(|c| **c != Formula::Top).collect()
}

/// 極限形か：成分に ↓B か ⟨i⟩_α B（α ≥ 2）がある。
pub fn is_limit(a: &Formula) -> bool {
    conjuncts(a).iter().any(|c| match c {
        Formula::Down(_) => true,
        Formula::Dia(_, r, _) => *r >= Rank::Fin(2),
        _ => false,
    })
}

/// 式の形を求める。後続形なら直前の式も求める（B_i の最大を <¹₁ で選ぶ）。
pub fn form(a: &Formula) -> Result<Form, String> {
    if !a.in_wbi() {
        return Err(format!("{a} {}", tr("は W_BI の式ではありません（変数・∇・⟨1⟩_ω を含まない式だけ）", "is not a W_BI formula (only formulas without variables, ∇ or ⟨1⟩_ω)")));
    }
    if is_limit(a) {
        return Ok(Form::Limit);
    }
    // 残りは成分がすべて ⟨1⟩₁B の形
    let mut best: Option<&Formula> = None;
    for c in conjuncts(a) {
        let Formula::Dia(1, Rank::Fin(1), b) = c else {
            return Err(format!("{}: {c}", tr("想定外の成分（バグです）", "unexpected component (a bug)")));
        };
        best = Some(match best {
            None => b,
            Some(cur) => match compare(cur, b) {
                Some(Ordering::Less) => b,
                Some(_) => cur,
                None => {
                    return Err(if crate::i18n::is_en() {
                        format!("{cur} and {b} are incomparable (contradicts Thm 4.11)")
                    } else {
                        format!("{cur} と {b} が比較できません（Thm 4.11 に反する）")
                    });
                }
            },
        });
    }
    Ok(match best {
        None => Form::Zero,
        Some(b) => Form::Successor(b.clone()),
    })
}

// ----------------------------------------------------------------------
// 近似 (A)_n（Def 4.6）
// ----------------------------------------------------------------------

/// ⊤ を省いた連言（⊤ ∧ A は A と同値なので、式が無駄に大きくならないようにする）。
fn conj(items: Vec<Formula>) -> Formula {
    Formula::conj(items.into_iter().filter(|x| *x != Formula::Top))
}

fn and(a: Formula, b: Formula) -> Formula {
    conj(vec![a, b])
}

/// 極限形の式 A の近似 (A)_n（n ≥ 1）。極限形でなければ `None`。
///
/// - A = ⟨i⟩_α A′（α ≥ 2）：(A)₁ = A′、(A)_{n+1} = ⟨i⟩_{α−1}(A′ ∧ (A)_n)（α > i）
///   または ⟨1⟩₁(A′ ∧ ↓(A)_n)（α = i = 2）
/// - A = ↓C：C が極限形なら ⟨1⟩_n↓(C)_n。そうでなければ C = ⟨1⟩₁E₁ ∧ … ∧ ⟨1⟩₁E_k として
///   ⟨1⟩_n↓E₁ ∧ … ∧ ⟨1⟩_n↓E_k（k = 0 なら ⟨1⟩_n⊤）
/// - 成分が 2 つ以上：↓ の成分があれば、それらを近似して ◇ の成分はそのまま。
///   なければ最大の添字 α₁ の成分 C₁ … C_m と残り C⁰ に分け、巡回シフト A⟲ を使って
///   (A)₁ = C⁰、(A)_{n+1} = ⟨i₁⟩_{α₁−1}(C₁′ ∧ (A⟲)_n)（α₁ > i₁）または ⟨1⟩₁(C₁′ ∧ ↓(A⟲)_n)
///
/// どの場合も (A)_{n+1}（n ≥ 1）は ◇ 1 つの式になる（論文の Lemma 4.7 の証明で使う性質）。
///
/// 結果の式は、⊤ との連言を省いて簡単にしてある（同値な式）。
pub fn approx(a: &Formula, n: u32) -> Option<Formula> {
    assert!(n >= 1, "近似の番号は 1 から");
    let cs = conjuncts(a);
    if !is_limit(a) {
        return None;
    }
    if cs.len() == 1 {
        return Some(match cs[0] {
            Formula::Dia(i, Rank::Fin(alpha), a1) => single(*i, *alpha, a1, n),
            Formula::Down(c) => down_approx(c, n),
            _ => unreachable!("極限形の単独の成分"),
        });
    }
    let downs: Vec<&Formula> = cs.iter().copied().filter(|c| matches!(c, Formula::Down(_))).collect();
    let mut dias: Vec<(u8, u32, &Formula)> = cs
        .iter()
        .filter_map(|c| match c {
            Formula::Dia(i, Rank::Fin(k), x) => Some((*i, *k, &**x)),
            _ => None,
        })
        .collect();
    if !downs.is_empty() {
        let mut items: Vec<Formula> = downs
            .iter()
            .map(|d| match d {
                Formula::Down(c) => down_approx(c, n),
                _ => unreachable!(),
            })
            .collect();
        items.extend(dias.iter().map(|&(i, k, x)| Formula::dia(i, Rank::Fin(k), x.clone())));
        return Some(conj(items));
    }
    // ◇ の成分だけ：添字の大きい順に（同じ添字は元の順のまま）
    // 【Rust メモ】Reverse で包むと大きい順に並ぶ。sort_by_key は安定ソートなので同じ添字は元の順のまま
    dias.sort_by_key(|d| std::cmp::Reverse(d.1));
    let alpha = dias[0].1;
    let m = dias.iter().take_while(|d| d.1 == alpha).count();
    let top: Vec<(u8, &Formula)> = dias[..m].iter().map(|&(i, _, x)| (i, x)).collect();
    let rest: Vec<Formula> = dias[m..].iter().map(|&(i, k, x)| Formula::dia(i, Rank::Fin(k), x.clone())).collect();
    Some(conj_approx(&top, alpha, &rest, n))
}

/// A = ⟨i⟩_α A′ の近似。
fn single(i: u8, alpha: u32, a1: &Formula, n: u32) -> Formula {
    if n == 1 {
        return a1.clone();
    }
    let prev = single(i, alpha, a1, n - 1);
    if alpha > i as u32 {
        Formula::dia(i, Rank::Fin(alpha - 1), and(a1.clone(), prev))
    } else {
        Formula::one(1, and(a1.clone(), Formula::down(prev)))
    }
}

/// 最大の添字 α の成分 top = [(i₁, C₁′), …, (i_m, C_m′)] と残り rest からなる式の近似。
fn conj_approx(top: &[(u8, &Formula)], alpha: u32, rest: &[Formula], n: u32) -> Formula {
    if n == 1 {
        return conj(rest.to_vec());
    }
    let (i1, c1) = top[0];
    // 巡回シフト A⟲：C₁ を C_m の後ろへ
    let mut shifted = top[1..].to_vec();
    shifted.push(top[0]);
    let prev = conj_approx(&shifted, alpha, rest, n - 1);
    if alpha > i1 as u32 {
        Formula::dia(i1, Rank::Fin(alpha - 1), and(c1.clone(), prev))
    } else {
        Formula::one(1, and(c1.clone(), Formula::down(prev)))
    }
}

/// A = ↓C の近似。
fn down_approx(c: &Formula, n: u32) -> Formula {
    if is_limit(c) {
        return Formula::one(n, Formula::down(approx(c, n).expect("極限形")));
    }
    let es: Vec<Formula> = conjuncts(c)
        .into_iter()
        .map(|x| match x {
            Formula::Dia(1, Rank::Fin(1), e) => Formula::one(n, Formula::down((**e).clone())),
            _ => unreachable!("極限形でない式の成分は ⟨1⟩₁E"),
        })
        .collect();
    if es.is_empty() { Formula::one(n, Formula::Top) } else { conj(es) }
}

// ----------------------------------------------------------------------
// battle
// ----------------------------------------------------------------------

/// battle の 1 ステップ A{k}（k ≥ 0）：後続形なら直前、極限形なら (A)_{k+1}、零なら `None`。
///
/// 近似の番号を 1 ずらすのは、(A)_n が標準の基本列の α[n−1] に当たるから
/// （例：(⟨1⟩₂⊤)_n = ⟨1⟩₁^{n−1}⊤ は ω[n−1] = n − 1）。こうすると A{k} は α[k] に当たる。
pub fn step(a: &Formula, k: u32) -> Result<Option<Formula>, String> {
    Ok(match form(a)? {
        Form::Zero => None,
        Form::Successor(b) => Some(b),
        Form::Limit => approx(a, k + 1),
    })
}

/// A⦃0⦄ = A、A⦃k⦄ = A⦃k−1⦄{k} を返すイテレータ（⊤ と同値になったら終わる）。
/// worm の battle と同じく、k = 1, 2, 3, … と番号を増やしながら基本列をとる。
pub fn battle(a: &Formula) -> Battle {
    Battle { current: Some(a.clone()), k: 0 }
}

pub struct Battle {
    current: Option<Formula>,
    k: u32,
}

impl Iterator for Battle {
    type Item = Formula;

    fn next(&mut self) -> Option<Formula> {
        let cur = self.current.take()?;
        self.k += 1;
        self.current = step(&cur, self.k).expect("W_BI の式");
        Some(cur)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(s: &str) -> Formula {
        s.parse().unwrap_or_else(|e| panic!("{e}"))
    }

    #[test]
    fn forms() {
        assert_eq!(form(&f("T")).unwrap(), Form::Zero);
        assert_eq!(form(&f("<1>T & T")).unwrap(), Form::Successor(f("T")));
        // 直前は大きいほう
        assert_eq!(form(&f("<1>T & <1><1>T")).unwrap(), Form::Successor(f("<1>T")));
        assert_eq!(form(&f("<1>(D T) & <1><1><1>T")).unwrap(), Form::Successor(f("D T")));
        assert_eq!(form(&f("<1>_2 T")).unwrap(), Form::Limit);
        assert_eq!(form(&f("D T & <1>T")).unwrap(), Form::Limit);
        assert!(form(&f("N T")).is_err());
    }

    #[test]
    fn approximations() {
        // ⟨1⟩₂⊤ = ω：(A)_n = ⟨1⟩₁^{n−1}⊤
        assert_eq!(approx(&f("<1>_2 T"), 1), Some(f("T")));
        assert_eq!(approx(&f("<1>_2 T"), 3), Some(f("<1><1>T")));
        // ↓⊤ = ε₀：(↓⊤)_n = ⟨1⟩_n⊤
        assert_eq!(approx(&f("D T"), 4), Some(f("<1>_4 T")));
        // ⟨2⟩₂⊤：(A)₂ = ⟨1⟩₁(⊤ ∧ ↓⊤) = ⟨1⟩₁↓⊤、(A)₃ = ⟨1⟩₁↓⟨1⟩₁↓⊤
        assert_eq!(approx(&f("<2>_2 T"), 2), Some(f("<1> D T")));
        assert_eq!(approx(&f("<2>_2 T"), 3), Some(f("<1> D <1> D T")));
        // 巡回シフト：⟨1⟩₂p ∧ ⟨1⟩₂q の形（ここでは p = ⟨1⟩₁⊤, q = ↓⊤）
        let a = f("<1>_2 <1>T & <1>_2 D T");
        assert_eq!(approx(&a, 1), Some(f("T")));
        assert_eq!(approx(&a, 2), Some(f("<1>(<1>T)")));
        assert_eq!(approx(&a, 3), Some(f("<1>(<1>T & <1>(D T))")));
        assert_eq!(approx(&f("<1>T"), 1), None);
    }

    #[test]
    fn order_examples() {
        assert_eq!(compare(&f("D T"), &f("<2>_2 T")), Some(Ordering::Less));
        assert_eq!(compare(&f("<1>T & T"), &f("<1>T")), Some(Ordering::Equal));
        // 同値でない式どうしの ≡¹₁（Π¹₁ 定理が同じ）：↓⊤ ∧ ⟨1⟩₁⊤ と ↓⊤
        assert_eq!(compare(&f("D T & <1>T"), &f("D T")), Some(Ordering::Equal));
        // 近似は元の式より下（Lemma 4.7）
        for n in 1..5 {
            let x = approx(&f("<2>_2<2>_3 T"), n).unwrap();
            assert!(lt(&x, &f("<2>_2<2>_3 T")), "{x}");
        }
    }

    #[test]
    fn small_battle_terminates() {
        // ⟨1⟩₂⟨1⟩₁⊤（= ω + 1）：直前 ⟨1⟩₂⊤ …
        let steps: Vec<String> = battle(&f("<1>_2 T & <1><1>_2 T")).map(|x| x.to_string()).collect();
        assert_eq!(steps.first().unwrap(), "⟨1⟩₂⊤ ∧ ⟨1⟩₁⟨1⟩₂⊤");
        assert_eq!(steps.last().unwrap(), "⊤");
    }
}
