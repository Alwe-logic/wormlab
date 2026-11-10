//! 順序数の標準形の書き方を選ぶ（順序数電卓のタブの「標準形」の選択）。
//!
//! どれも同じ順序数の書き方の違いで、計算そのものは [`Veblen`] の正規形で行う。
//! - [`Notation::Veblen`]：Veblen 形（略記つき）。φ(0, β) は ω^β、φ(1, β) は ε_β と書く（今までの表示）
//! - [`Notation::Phi`]：Veblen 形（φ だけ）。ω^β・ε_β の略記を使わない
//! - [`Notation::Hyper`]：超指数関数と ψ。0・1・+・e^α(β) で書き、強臨界数 Ω・ψ(ξ) だけを原子にする
//!   （Worms and spiders Prop 5.14 の超指数標準形を各部分に繰り返す。ψ の中も同じ形）
//! - [`Notation::Worm`]：Beklemishev 標準形の worm（文字は順序数）
//! - [`Notation::Bracket`]：括弧語の正規形（Γ₀ 未満）
//! - [`Notation::IWorm`]：impredicative worm（Ω を文字に持つ括弧語、可算な数）
//!
//! # 超指数標準形（Worms and spiders, arXiv:1605.08867, Prop 5.14・5.15）
//! ξ > 0 は、β が 1 か加法的に分解できる数であるような ξ = e^α(β) の形に、ただ一通りに書ける
//! （α は「分解できない度合い」。ξ が分解できる数なら α = 0）。計算は Prop 5.15
//! （e^1(1 + β) = φ(0, 1 + β)、e^{ω^{1+α}}(1 + β) = φ(1 + α, β)）と e^{α+β} = e^α ∘ e^β から：
//! ```text
//! 度合い(ξ)：ξ = 1 か分解できる数  → (0, ξ)
//!            ξ が強臨界数 s         → (s, 1)      （s = e^s(1)。書くときは原子のまま）
//!            ξ = ω^b（b ≥ 1）        → (1 + α', β')、(α', β') = 度合い(b)
//!            ξ = φ(a, b)（a ≥ 1）    → (ω^a + α', β')、(α', β') = 度合い(1 + b)
//! ```
//! 強臨界数でない主項 ξ では α < ξ なので、α と β を同じ方法で書けば止まる。

use crate::bracket::Bracket;
use crate::i18n::{is_en, tr};
use crate::iworm::IWorm;
use crate::latex::ToLatex;
use crate::repeats::{self, Piece};
use crate::veblen::Veblen;
use crate::worm::Worm;
use std::collections::HashMap;

/// 標準形の書き方。
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Notation {
    Veblen,
    Phi,
    Hyper,
    Worm,
    Bracket,
    IWorm,
}

impl Notation {
    pub const ALL: [Notation; 6] =
        [Notation::Veblen, Notation::Phi, Notation::Hyper, Notation::Worm, Notation::Bracket, Notation::IWorm];

    /// "veblen"・"phi"・"hyper"・"worm"・"bracket"・"iworm"。
    pub fn key(self) -> &'static str {
        match self {
            Notation::Veblen => "veblen",
            Notation::Phi => "phi",
            Notation::Hyper => "hyper",
            Notation::Worm => "worm",
            Notation::Bracket => "bracket",
            Notation::IWorm => "iworm",
        }
    }

    pub fn parse(s: &str) -> Option<Notation> {
        Notation::ALL.into_iter().find(|n| n.key() == s.trim())
    }
}

/// worm・括弧語に書き出す文字の数の上限（これを超えたら Veblen 形のまま）。
pub const MAX_LETTERS: u128 = 4_000;
/// 繰り返しでまとめて書き始める長さ（worm の文字の数・括弧語の記号の数）。
const COMPACT_FROM: usize = 40;

/// 書き方を変えた結果。
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct Rendered {
    pub text: String,
    pub latex: String,
    /// 選んだ書き方で書けなかったときの理由（そのときは Veblen 形）
    pub note: Option<String>,
}

fn veblen_form(v: &Veblen, note: Option<String>) -> Rendered {
    Rendered { text: v.to_string(), latex: v.to_latex(), note }
}

/// v を書き方 n で書く。
pub fn render(v: &Veblen, n: Notation) -> Rendered {
    match n {
        Notation::Veblen => veblen_form(v, None),
        Notation::Phi => Rendered { text: phi_text(v), latex: phi_latex(v), note: None },
        Notation::Hyper => Rendered { text: hyper_text(v), latex: hyper_latex(v), note: None },
        Notation::Worm => match worm_len(v, &mut HashMap::new()) {
            len if len > MAX_LETTERS => veblen_form(v, Some(too_long(len))),
            _ => {
                let w = Worm::from_veblen(v);
                Rendered { text: worm_text(&w), latex: worm_latex(&w), note: None }
            }
        },
        Notation::Bracket => {
            if !v.is_predicative() {
                return veblen_form(v, Some(tr("Γ₀ 以上は括弧語で書けません", "ordinals ≥ Γ₀ have no bracket word").to_string()));
            }
            match bracket_pairs(v, &mut HashMap::new()) {
                p if p > MAX_LETTERS => veblen_form(v, Some(too_long(p))),
                _ => {
                    let b = Bracket::from_ordinal(v);
                    if b.pairs() > COMPACT_FROM {
                        let c = repeats::bracket(&b);
                        Rendered { text: c.text, latex: c.latex, note: None }
                    } else {
                        Rendered { text: b.to_string(), latex: b.to_latex(), note: None }
                    }
                }
            }
        }
        Notation::IWorm => {
            if !v.is_countable() {
                return veblen_form(v, Some(tr("Ω 以上（非可算）は impredicative worm で書けません", "uncountable ordinals have no impredicative worm").to_string()));
            }
            if iworm_size(v, &mut HashMap::new()) > MAX_LETTERS {
                return veblen_form(v, Some(tr("長すぎて書き出せません", "too long to write out").to_string()));
            }
            match IWorm::from_value(v) {
                Some(w) => Rendered { text: w.to_string(), latex: w.to_latex(), note: None },
                None => veblen_form(
                    v,
                    Some(tr("ψ(e^{Ω+1}1) 以上は impredicative worm で書けません", "ordinals ≥ ψ(e^{Ω+1}1) have no impredicative worm").to_string()),
                ),
            }
        }
    }
}

fn too_long(n: u128) -> String {
    let n = if n >= MAX_LETTERS * 1000 { format!("{}+", MAX_LETTERS * 1000) } else { n.to_string() };
    if is_en() { format!("too long to write out ({n} letters)") } else { format!("長すぎて書き出せません（{n} 文字）") }
}

// ----------------------------------------------------------------------
// Veblen 形（φ だけ）
// ----------------------------------------------------------------------

/// 和の書き方：主項（係数つき）を書く関数 `prin` を受け取り、自然数の部分は数字で書く。
fn sum_text(v: &Veblen, sep: &str, mul: &dyn Fn(&str, u64) -> String, prin: &dyn Fn(&Veblen) -> String) -> String {
    if v.is_zero() {
        return "0".to_string();
    }
    let parts: Vec<String> = v
        .principal_terms()
        .map(|(p, c)| if p == Veblen::one() { c.to_string() } else if c == 1 { prin(&p) } else { mul(&prin(&p), c) })
        .collect();
    parts.join(sep)
}

fn phi_text(v: &Veblen) -> String {
    sum_text(v, " + ", &|s, c| format!("{s}·{c}"), &|p| match p.as_phi() {
        Some((a, b)) => format!("φ({}, {})", phi_text(a), phi_text(b)),
        None => match p.as_psi() {
            Some(x) => format!("ψ({})", phi_text(x)),
            None => "Ω".to_string(),
        },
    })
}

fn phi_latex(v: &Veblen) -> String {
    sum_text(v, " + ", &|s, c| format!("{s} \\cdot {c}"), &|p| match p.as_phi() {
        Some((a, b)) => format!("\\varphi({}, {})", phi_latex(a), phi_latex(b)),
        None => match p.as_psi() {
            Some(x) => format!("\\psi({})", phi_latex(x)),
            None => "\\Omega".to_string(),
        },
    })
}

// ----------------------------------------------------------------------
// 超指数関数と ψ
// ----------------------------------------------------------------------

/// 強臨界数（Ω・ψ(ξ)）か。
fn strongly_critical(v: &Veblen) -> bool {
    v.is_principal() && v.as_phi().is_none()
}

/// 超指数標準形 ξ = e^α(β)（β は 1 か加法的に分解できる数）の (α, β)。ξ ≥ 1。
pub fn hyper_degree(x: &Veblen) -> (Veblen, Veblen) {
    if *x == Veblen::one() || !x.is_principal() {
        return (Veblen::zero(), x.clone());
    }
    if strongly_critical(x) {
        return (x.clone(), Veblen::one());
    }
    let (a, b) = x.as_phi().expect("強臨界数でない主項");
    if a.is_zero() {
        // ξ = ω^b = e(b)（b ≥ 1）
        let (d, beta) = hyper_degree(b);
        (Veblen::one() + d, beta)
    } else {
        // ξ = φ(a, b) = e^{ω^a}(1 + b)
        let (d, beta) = hyper_degree(&(Veblen::one() + b.clone()));
        (Veblen::omega_pow(a.clone()) + d, beta)
    }
}

/// e^α(β) の α を、かっこなしで書ける（自然数・Ω・ψ(…)）か。
fn hyper_simple(a: &Veblen) -> bool {
    a.is_finite() || strongly_critical(a)
}

fn hyper_text(v: &Veblen) -> String {
    sum_text(v, " + ", &|s, c| format!("{s}·{c}"), &|p| {
        if *p == Veblen::big_omega() {
            return "Ω".to_string();
        }
        if let Some(x) = p.as_psi() {
            return format!("ψ({})", hyper_text(x));
        }
        let (a, b) = hyper_degree(p);
        let beta = hyper_text(&b);
        if a == Veblen::one() {
            format!("e({beta})")
        } else if hyper_simple(&a) {
            format!("e^{}({beta})", hyper_text(&a))
        } else {
            format!("e^({})({beta})", hyper_text(&a))
        }
    })
}

fn hyper_latex(v: &Veblen) -> String {
    sum_text(v, " + ", &|s, c| format!("{s} \\cdot {c}"), &|p| {
        if *p == Veblen::big_omega() {
            return "\\Omega".to_string();
        }
        if let Some(x) = p.as_psi() {
            return format!("\\psi({})", hyper_latex(x));
        }
        let (a, b) = hyper_degree(p);
        if a == Veblen::one() { format!("e({})", hyper_latex(&b)) } else { format!("e^{{{}}}({})", hyper_latex(&a), hyper_latex(&b)) }
    })
}

// ----------------------------------------------------------------------
// worm・括弧語・impredicative worm（大きさを先に数える）
// ----------------------------------------------------------------------

/// α を表す標準形の worm の長さ（作らずに数える。transfinite の逆写像と同じ場合分け）。
pub fn worm_len(alpha: &Veblen, memo: &mut HashMap<Veblen, u128>) -> u128 {
    if alpha.is_zero() {
        return 0;
    }
    if let Some(&n) = memo.get(alpha) {
        return n;
    }
    // 1 + α = ω^{β_1} + … + ω^{β_k}（重複を許す）。A は β_k, …, β_2 の部分（各 1↑inv(β_i) と区切りの 0）
    // と、最後に残る −1 + ω^{β_1} の部分からなる
    // （k = 1 で ω^{β_1} = β_1 のときは β_1 = α 自身なので、β_1 の長さは数えない）
    let gamma = alpha.one_plus();
    let cnf = gamma.cnf();
    let k = cnf.iter().fold(0u128, |s, (_, c)| s.saturating_add(u128::from(*c)));
    let (b1, _) = &cnf[0];
    let mut total: u128 = 0;
    if k >= 2 {
        // k ≥ 2 なら各 β_i < α
        for (e, c) in &cnf {
            total = total.saturating_add(u128::from(*c).saturating_mul(worm_len(e, memo).saturating_add(1)));
        }
        total = total.saturating_sub(worm_len(b1, memo) + 1);
    }
    let single = if *b1 < Veblen::omega_pow(b1.clone()) {
        worm_len(b1, memo)
    } else {
        // −1 + ω^{β_1} = β_1 = φ(a, b)：A = ω^a↑inv(1 + b)
        let (_, b) = b1.phi_parts().expect("主項");
        worm_len(&b.one_plus(), memo)
    };
    let n = total.saturating_add(single);
    memo.insert(alpha.clone(), n);
    n
}

/// α を表す正規形の括弧語の括弧の対の数（作らずに数える）。
fn bracket_pairs(alpha: &Veblen, memo: &mut HashMap<Veblen, u128>) -> u128 {
    if worm_len(alpha, &mut HashMap::new()) > MAX_LETTERS {
        return u128::MAX;
    }
    if let Some(&n) = memo.get(alpha) {
        return n;
    }
    let w = Worm::from_veblen(alpha);
    let mut n: u128 = 0;
    for l in w.letters() {
        n = n.saturating_add(1).saturating_add(bracket_pairs(l, memo));
        if n > MAX_LETTERS {
            break;
        }
    }
    memo.insert(alpha.clone(), n);
    n
}

/// impredicative worm の大きさ（文字の数を、文字の中まで）。
fn iworm_size(xi: &Veblen, memo: &mut HashMap<Veblen, u128>) -> u128 {
    let alpha = match xi.as_psi() {
        Some(z) => Veblen::big_omega() + z.clone(),
        None => xi.clone(),
    };
    if worm_len(&alpha, &mut HashMap::new()) > MAX_LETTERS {
        return u128::MAX;
    }
    if let Some(&n) = memo.get(&alpha) {
        return n;
    }
    let w = Worm::from_veblen(&alpha);
    let mut n: u128 = 0;
    for l in w.letters() {
        let inner = if *l == Veblen::big_omega() || !l.is_countable() { 0 } else { iworm_size(l, memo) };
        n = n.saturating_add(1).saturating_add(inner);
        if n > MAX_LETTERS {
            break;
        }
    }
    memo.insert(alpha, n);
    n
}

/// 文字が順序数の worm の書き方（長ければ同じ部分の繰り返しを (…)^k にまとめる）。
fn worm_text(w: &Worm<Veblen>) -> String {
    let ls = w.letters();
    if ls.is_empty() {
        return "⊤".to_string();
    }
    let one = |x: &Veblen| format!("⟨{x}⟩");
    if ls.len() <= COMPACT_FROM {
        return ls.iter().map(one).collect();
    }
    fn go(p: &[Piece], ls: &[Veblen], one: &dyn Fn(&Veblen) -> String) -> String {
        p.iter()
            .map(|x| match x {
                Piece::One(i) => one(&ls[*i]),
                Piece::Rep(inner, k) => {
                    let body = go(inner, ls, one);
                    if matches!(inner.as_slice(), [Piece::One(_)]) { format!("{body}^{k}") } else { format!("({body})^{k}") }
                }
            })
            .collect()
    }
    go(&repeats::compress(ls), ls, &one)
}

fn worm_latex(w: &Worm<Veblen>) -> String {
    let ls = w.letters();
    if ls.len() <= COMPACT_FROM {
        return w.to_latex();
    }
    fn go(p: &[Piece], ls: &[Veblen]) -> String {
        p.iter()
            .map(|x| match x {
                Piece::One(i) => format!("\\langle {}\\rangle", ls[*i].to_latex()),
                Piece::Rep(inner, k) => {
                    let body = go(inner, ls);
                    if matches!(inner.as_slice(), [Piece::One(_)]) { format!("{body}^{{{k}}}") } else { format!("\\left({body}\\right)^{{{k}}}") }
                }
            })
            .collect()
    }
    format!("{}\\top", go(&repeats::compress(ls), ls))
}

// ----------------------------------------------------------------------
// 一覧（画面の選択肢と説明）
// ----------------------------------------------------------------------

/// 書き方 1 つの説明。
#[derive(Clone, Debug, serde::Serialize)]
pub struct NotationInfo {
    pub key: &'static str,
    pub name: String,
    pub lines: Vec<String>,
    pub source: String,
    /// 例：ε_0 + ω をこの書き方で
    pub example: String,
}

/// すべての書き方（今の言語で）。
pub fn notations() -> Vec<NotationInfo> {
    let ex: Veblen = "φ(2, 0) + ε_0·2 + ω^ω + 3".parse().expect("例");
    let info = |n: Notation, name: (&str, &str), lines: &[(&str, &str)], source: (&str, &str)| NotationInfo {
        key: n.key(),
        name: tr(name.0, name.1).to_string(),
        lines: lines.iter().map(|(j, e)| tr(j, e).to_string()).collect(),
        source: tr(source.0, source.1).to_string(),
        example: render(&ex, n).text,
    };
    vec![
        info(
            Notation::Veblen,
            ("Veblen 形（略記つき）", "Veblen form (abbreviated)"),
            &[
                (
                    "主項 φ(α, β)（β < φ(α, β)）・Ω・ψ(ξ)（ξ ∈ C(ξ)）の非増加な和。同じ主項の和は ·n",
                    "a non-increasing sum of principal terms φ(α, β) (β < φ(α, β)), Ω and ψ(ξ) (ξ ∈ C(ξ)); repeated terms as ·n",
                ),
                ("φ(0, 0)·n は n、φ(0, β) は ω^β、φ(1, β) は ε_β と書く", "φ(0, 0)·n is written n, φ(0, β) as ω^β, and φ(1, β) as ε_β"),
            ],
            ("2 変数の Veblen 関数（Veblen 1908）と Worms and spiders §6 の Ω・ψ", "the binary Veblen function (Veblen 1908) with Ω and ψ from Worms and spiders §6"),
        ),
        info(
            Notation::Phi,
            ("Veblen 形（φ だけ）", "Veblen form (φ only)"),
            &[(
                "同じ標準形を、ω^β・ε_β の略記を使わずに φ(0, β)・φ(1, β) と書く（自然数と係数 ·n は略記のまま。ω = φ(0, 1)）",
                "the same normal form, writing φ(0, β) and φ(1, β) instead of ω^β and ε_β (natural numbers and coefficients ·n stay abbreviated; ω = φ(0, 1))",
            )],
            ("Veblen 1908", "Veblen 1908"),
        ),
        info(
            Notation::Hyper,
            ("超指数関数と ψ", "Hyperexponentials and ψ"),
            &[
                (
                    "0・1・+・e^α(β) で書く。ξ > 0 は、β が 1 か加法的に分解できる数であるような ξ = e^α(β) の形にただ一通りに書ける（α は分解できない度合い）。α と β も同じ形に書く",
                    "written with 0, 1, + and e^α(β): every ξ > 0 is uniquely ξ = e^α(β) with β equal to 1 or additively decomposable (α is the degree of indecomposability); α and β are written the same way",
                ),
                (
                    "強臨界数（Ω と ψ(ξ)、Γ₀ 以上）は ξ = e^ξ(1) となって小さく分けられないので、原子として書く（ψ の中も同じ形）。これは C(ξ) を {0, 1, Ω} から +・超指数関数・ψ↾ξ で作る作り方そのもの",
                    "strongly critical ordinals (Ω and ψ(ξ), from Γ₀ on) satisfy ξ = e^ξ(1) and cannot be split further, so they are atoms (with the same form inside ψ); this mirrors how C(ξ) is built from {0, 1, Ω} by +, hyperexponentials and ψ↾ξ",
                ),
                (
                    "e(β) = e^1(β)、e(1) = ω、e^(e(1))(1) = e^ω(1) = ε₀。自然数 n と、同じ項の n 回の和 ·n は略記",
                    "e(β) = e^1(β), e(1) = ω, e^(e(1))(1) = e^ω(1) = ε₀; natural numbers n and n-fold sums ·n are abbreviations",
                ),
            ],
            (
                "Worms and spiders（arXiv:1605.08867）Prop 5.14（Aguilera & Fernández-Duque）・Prop 5.15、§6 の C(ξ)",
                "Worms and spiders (arXiv:1605.08867), Prop 5.14 (Aguilera & Fernández-Duque) and Prop 5.15; C(ξ) from §6",
            ),
        ),
        info(
            Notation::Worm,
            ("worm（Beklemishev 標準形）", "Worm (Beklemishev normal form)"),
            &[
                (
                    "o(A) = α となる標準形の worm。文字は順序数（Veblen 形）で、⟨α₁⟩⟨α₂⟩…⊤ の ⊤ は省く。長い worm は同じ部分の繰り返しを (…)^k にまとめる",
                    "the normal-form worm A with o(A) = α; letters are ordinals (in Veblen form), written ⟨α₁⟩⟨α₂⟩… with the final ⊤ left out; long worms group repeated parts as (…)^k",
                ),
                (
                    "1 + α = ω^{β₁} + … + ω^{β_k}（重複を許す）として、k ≥ 2 なら A = (1↑inv(β_k)) 0 inv(−1 + ω^{β₁} + … + ω^{β_{k−1}})、など",
                    "with 1 + α = ω^{β₁} + … + ω^{β_k} (repetitions allowed): for k ≥ 2, A = (1↑inv(β_k)) 0 inv(−1 + ω^{β₁} + … + ω^{β_{k−1}}), and so on",
                ),
            ],
            (
                "Fernández-Duque & Joosten, Well-orders in the transfinite Japaridze algebra I・II（arXiv:1212.3468、1204.4743）。wormlab の transfinite.rs",
                "Fernández-Duque & Joosten, Well-orders in the transfinite Japaridze algebra I and II (arXiv:1212.3468, 1204.4743); wormlab's transfinite.rs",
            ),
        ),
        info(
            Notation::Bracket,
            ("括弧語（正規形）", "Bracket word (normal form)"),
            &[(
                "Γ₀ 未満。文字そのものも括弧語で書いた worm（() = 1、(()) = ω、((())) = ε₀）。各文字が正規形で、翻訳した worm が Beklemishev 標準形のもの。長い語は [ … ]^k にまとめる",
                "below Γ₀: a worm whose letters are themselves bracket words (() = 1, (()) = ω, ((())) = ε₀), with every letter in normal form and the translated worm in Beklemishev normal form; long words group repeats as [ … ]^k",
            )],
            ("Fernández-Duque & Hermo Reyes（arXiv:2008.13445）Def 31・Thm 32", "Fernández-Duque & Hermo Reyes (arXiv:2008.13445), Def 31 and Thm 32"),
        ),
        info(
            Notation::IWorm,
            ("impredicative worm", "Impredicative worm"),
            &[(
                "Ω を文字に持つ括弧語。値 p(w) が α になる標準の worm（可算で ψ(e^{Ω+1}1) 未満の数）",
                "a bracket word that may use Ω as a letter: the standard worm w with value p(w) = α (for countable α below ψ(e^{Ω+1}1))",
            )],
            ("Worms and spiders（arXiv:1605.08867）Def 6.33・Thm 6.36", "Worms and spiders (arXiv:1605.08867), Def 6.33 and Thm 6.36"),
        ),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(s: &str) -> Veblen {
        s.parse().unwrap()
    }

    #[test]
    fn hyper_examples() {
        for (x, want) in [
            ("1", "1"),
            ("3", "3"),
            ("ω", "e(1)"),
            ("ω^2", "e(2)"),
            ("ω^ω", "e^2(1)"),
            ("ε_0", "e^(e(1))(1)"),
            ("ε_1", "e^(e(1))(2)"),
            ("ε_ω", "e^(e(1) + 1)(1)"),
            ("φ(2, 0)", "e^(e(2))(1)"),
            ("ω^(ε_0 + 1)", "e(e^(e(1))(1) + 1)"),
            ("ψ(0)", "ψ(0)"),
            ("φ(ψ(0), 1)", "e^ψ(0)(2)"),
            ("φ(Ω, Ω)", "e^(Ω·2)(1)"),
            ("ω·2 + 1", "e(1)·2 + 1"),
        ] {
            assert_eq!(render(&v(x), Notation::Hyper).text, want, "{x}");
        }
    }

    #[test]
    fn phi_and_fallbacks() {
        assert_eq!(render(&v("ε_0·2 + ω^ω"), Notation::Phi).text, "φ(1, 0)·2 + φ(0, φ(0, 1))");
        let r = render(&v("ψ(0)"), Notation::Bracket);
        assert!(r.note.is_some() && r.text == "ψ(0)");
        let r = render(&v("ω·1000000000"), Notation::Worm);
        assert!(r.note.is_some());
        assert_eq!(render(&v("0"), Notation::Worm).text, "⊤");
        assert_eq!(render(&v("ε_0"), Notation::Bracket).text, "((()))");
        assert_eq!(render(&v("ψ(Ω·2)"), Notation::IWorm).text, "Ω()Ω()Ω");
    }

    #[test]
    fn worm_length_is_counted_exactly() {
        for s in ["0", "1", "5", "ω", "ω·3 + 2", "ω^ω + ω^2·2", "ε_0 + 1", "φ(2, ω) + ε_1", "ψ(0)", "Ω + 3"] {
            let x = v(s);
            assert_eq!(worm_len(&x, &mut HashMap::new()), Worm::from_veblen(&x).letters().len() as u128, "{s}");
        }
    }
}
