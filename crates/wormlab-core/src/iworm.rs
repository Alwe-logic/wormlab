//! Impredicative autonomous worm（Worms and spiders, arXiv:1605.08867, §6.4–6.5）。
//!
//! 括弧語に、文字としての Ω を加えたもの（Def 6.33）：
//!
//! ```text
//!   W_Ω ::= ⊤ | (w)v | Ωv        （w, v ∈ W_Ω）
//! ```
//!
//! 翻訳 ·^π（Def 6.34）で、文字が順序数の worm に移す：
//! ⊤^π = ⊤、((w)v)^π = ⟨π(w^π)⟩v^π、(Ωv)^π = ⟨Ω⟩v^π。
//!
//! 射影 π（Def 6.24）は、文字が可算な worm では o(u) そのもの、Ω を含む worm では
//! 「U(u) に入らない最小の数」で、Lemma 6.31 により o(u) ∈ [Ω, e_{Ω+1}1] なら
//! π(u) = ψ(−Ω + o(u))。ここで e_{Ω+1}1 = e^Ω(ω) = φ(Ω, ω)。
//! W_Ω の worm の値 p(w) = π(w^π) は ψ(e_{Ω+1}1) 未満のすべての数をとる（Thm 6.36）。
//!
//! 例：p(Ω) = π(⟨Ω⟩⊤) = ψ(0) = Γ0、p(ΩΩ) = ψ(φ(Ω, 1) − Ω) = ψ(φ(Ω, 1))、
//! p((Ω)) = o(⟨Γ0⟩⊤) = Γ0（Lemma 6.27：o(⟨πw⟩⊤) = πw）。

use crate::i18n::tr;
use crate::latex::ToLatex;
use crate::veblen::Veblen;
use crate::worm::Worm;
use std::fmt;
use std::str::FromStr;

/// W_Ω の文字：Ω か、括弧でくくった worm。
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ILetter {
    Omega,
    Br(IWorm),
}

/// W_Ω の worm（左端が外側）。
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct IWorm(Vec<ILetter>);

/// e_{Ω+1}1 = φ(Ω, ω)：Lemma 6.31 が使える範囲の上端（W_Ω の worm の o はこれ未満）。
pub fn top() -> Veblen {
    Veblen::phi(Veblen::big_omega(), Veblen::omega())
}

/// 射影 π(u)（Def 6.24）。文字がすべて可算なら o(u)、そうでなく o(u) ≤ e_{Ω+1}1 なら
/// ψ(−Ω + o(u))（Lemma 6.31）。o(u) がそれより大きいときは `None`（この範囲の外は扱わない）。
pub fn projection(u: &Worm<Veblen>) -> Option<Veblen> {
    let o = u.ordinal();
    if u.letters().iter().all(Veblen::is_countable) {
        return Some(o);
    }
    if o > top() {
        return None;
    }
    let x = Veblen::big_omega().sub_left(&o).expect("Ω を文字に持つ worm の o は Ω 以上");
    Some(Veblen::psi(x))
}

impl IWorm {
    pub fn top() -> IWorm {
        IWorm(Vec::new())
    }

    pub fn new(letters: Vec<ILetter>) -> IWorm {
        IWorm(letters)
    }

    pub fn letters(&self) -> &[ILetter] {
        &self.0
    }

    /// 翻訳 w^π：文字 Ω は Ω に、(u) は p(u) に。
    pub fn to_worm(&self) -> Worm<Veblen> {
        Worm::new(
            self.0
                .iter()
                .map(|l| match l {
                    ILetter::Omega => Veblen::big_omega(),
                    ILetter::Br(u) => u.value(),
                })
                .collect(),
        )
    }

    /// o(w^π)（Ω を含めば非可算）。
    pub fn ordinal(&self) -> Veblen {
        self.to_worm().ordinal()
    }

    /// p(w) = π(w^π)（可算）。
    pub fn value(&self) -> Veblen {
        projection(&self.to_worm()).expect("W_Ω の worm の o は e_{Ω+1}1 未満")
    }

    /// o(w^π) = α となる W_Ω の worm（α < e_{Ω+1}1）。α を表す標準形の worm を作り、
    /// 文字 Ω はそのまま、可算な文字 λ は p(u) = λ となる (u) にする。
    pub fn from_ordinal(alpha: &Veblen) -> Option<IWorm> {
        if *alpha >= top() {
            return None;
        }
        let w = Worm::from_veblen(alpha);
        let mut out = Vec::new();
        for l in w.letters() {
            if *l == Veblen::big_omega() {
                out.push(ILetter::Omega);
            } else if l.is_countable() {
                out.push(ILetter::Br(IWorm::from_value(l)?));
            } else {
                return None; // e_{Ω+1}1 未満なら起きない
            }
        }
        Some(IWorm(out))
    }

    /// p(w) = ξ となる W_Ω の worm（ξ < ψ(e_{Ω+1}1)、Thm 6.36 の構成）。
    /// ξ が強臨界数 ψ(z) なら o(w^π) = Ω + z となる worm（π(w^π) = ψ(z)）、
    /// そうでなければ o(w^π) = ξ となる worm（文字はすべて可算で π = o）。
    pub fn from_value(xi: &Veblen) -> Option<IWorm> {
        if !xi.is_countable() {
            return None;
        }
        match xi.as_psi() {
            Some(z) => IWorm::from_ordinal(&(Veblen::big_omega() + z.clone())),
            None => IWorm::from_ordinal(xi),
        }
    }

    /// 同じ値を持つ標準の worm。
    pub fn normal_form(&self) -> IWorm {
        IWorm::from_value(&self.value()).expect("値は ψ(e_{Ω+1}1) 未満")
    }

    /// 括弧の入れ子の深さ（Ω と ⊤ は 0）。
    pub fn depth(&self) -> usize {
        self.0
            .iter()
            .map(|l| match l {
                ILetter::Omega => 0,
                ILetter::Br(u) => 1 + u.depth(),
            })
            .max()
            .unwrap_or(0)
    }

    /// 記号（括弧の対と Ω）の数。
    pub fn size(&self) -> usize {
        self.0
            .iter()
            .map(|l| match l {
                ILetter::Omega => 1,
                ILetter::Br(u) => 1 + u.size(),
            })
            .sum()
    }
}

impl fmt::Display for IWorm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            return write!(f, "⊤");
        }
        fn go(w: &IWorm, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            for l in &w.0 {
                match l {
                    ILetter::Omega => write!(f, "Ω")?,
                    ILetter::Br(u) => {
                        write!(f, "(")?;
                        go(u, f)?;
                        write!(f, ")")?;
                    }
                }
            }
            Ok(())
        }
        go(self, f)
    }
}

impl ToLatex for IWorm {
    fn to_latex(&self) -> String {
        if self.0.is_empty() {
            return "\\top".to_string();
        }
        fn go(w: &IWorm, out: &mut String) {
            for l in &w.0 {
                match l {
                    ILetter::Omega => out.push_str("\\Omega "),
                    ILetter::Br(u) => {
                        out.push('(');
                        go(u, out);
                        out.push(')');
                    }
                }
            }
        }
        let mut s = String::new();
        go(self, &mut s);
        s.trim_end().to_string()
    }
}

/// `"()(Ω)Ω"`、`"⊤"`（または `"T"`）を読む。Ω は `O` とも書ける。空白は無視する。
impl FromStr for IWorm {
    type Err = String;

    fn from_str(s: &str) -> Result<IWorm, String> {
        let t: String = s.chars().filter(|c| !c.is_whitespace()).collect();
        if t == "⊤" || t == "T" || t.is_empty() {
            return Ok(IWorm::top());
        }
        // 【Rust メモ】括弧の入れ子は「開いている worm のスタック」で読む
        let mut stack: Vec<Vec<ILetter>> = vec![Vec::new()];
        for c in t.chars() {
            match c {
                '(' => stack.push(Vec::new()),
                ')' => {
                    let inner = stack.pop().ok_or(tr("閉じ括弧が多すぎます", "too many closing brackets"))?;
                    let top = stack.last_mut().ok_or_else(|| format!("{}: {s}", tr("閉じ括弧が多すぎます", "too many closing brackets")))?;
                    top.push(ILetter::Br(IWorm(inner)));
                }
                'Ω' | 'O' => stack.last_mut().expect("空でない").push(ILetter::Omega),
                _ => {
                    return Err(if crate::i18n::is_en() {
                        format!("unexpected character “{c}” in an impredicative worm: {s}")
                    } else {
                        format!("impredicative worm として読めない文字「{c}」: {s}")
                    });
                }
            }
        }
        if stack.len() != 1 {
            return Err(format!("{}: {s}", tr("括弧が閉じていません", "unclosed bracket")));
        }
        Ok(IWorm(stack.pop().expect("1 つ")))
    }
}

impl serde::Serialize for IWorm {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.collect_str(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(s: &str) -> Veblen {
        s.parse().unwrap()
    }

    fn w(s: &str) -> IWorm {
        s.parse().unwrap()
    }

    #[test]
    fn known_values() {
        assert_eq!(w("⊤").value(), v("0"));
        assert_eq!(w("()").value(), v("1"));
        assert_eq!(w("(())").value(), v("ω"));
        assert_eq!(w("((()))").value(), v("ε_0"));
        // Ω を含むと ψ に射影される
        assert_eq!(w("Ω").value(), v("ψ(0)"));
        assert_eq!(w("ΩΩ").value(), v("ψ(φ(Ω, 1))"));
        assert_eq!(w("()Ω").value(), v("ψ(1)"));
        assert_eq!(w("Ω()").value(), v("ψ(0)")); // ⟨Ω⟩⟨1⟩⊤ ≡ ⟨Ω⟩⊤
        // (()) は文字 ⟨1⟩、((())) は ⟨ω⟩：⟨1⟩⟨Ω⟩ の o は ω^{Ω+1}、⟨ω⟩⟨Ω⟩ の o は ε_{Ω+1}
        assert_eq!(w("(())Ω").value(), v("ψ(ω^(Ω + 1))"));
        // Bachmann–Howard 順序数 ψ(ε_{Ω+1})
        assert_eq!(w("((()))Ω").value(), v("ψ(ε_(Ω + 1))"));
        // Lemma 6.27：(w) と w は、w が Ω を含むとき同じ値
        assert_eq!(w("(Ω)").value(), w("Ω").value());
        assert_eq!(w("(ΩΩ)").value(), w("ΩΩ").value());
    }

    #[test]
    fn projection_top() {
        // Cor 6.32：π(⟨Ω + 1⟩⊤) = ψ(e_{Ω+1}1)
        let u: Worm<Veblen> = "<Ω + 1>".parse().unwrap();
        assert_eq!(projection(&u), Some(Veblen::psi(top())));
        let big: Worm<Veblen> = "<Ω + 2>".parse().unwrap();
        assert_eq!(projection(&big), None);
    }

    #[test]
    fn inverse_examples() {
        for s in ["0", "5", "ω", "ε_0", "φ(2, 0)", "ψ(0)", "ψ(0) + 1", "ψ(1)", "ψ(ψ(0))", "ψ(Ω)", "ψ(Ω + 1)",
            "ψ(Ω·2)", "ψ(ε_(Ω + 1))", "ψ(φ(Ω, 1))", "ψ(φ(Ω, 5) + ψ(Ω))", "φ(ψ(Ω), ψ(0))"] {
            let x = v(s);
            let iw = IWorm::from_value(&x).unwrap_or_else(|| panic!("{s}"));
            assert_eq!(iw.value(), x, "{s} ↦ {iw}");
            assert_eq!(iw.to_string().parse::<IWorm>().unwrap(), iw);
        }
        // 上限 ψ(e_{Ω+1}1) は表せない
        assert_eq!(IWorm::from_value(&Veblen::psi(top())), None);
    }
}
