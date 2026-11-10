//! 順序数の演算：足し算 α + β・掛け算 α·β・べき乗 α^β（[`Veblen`] の正規形、Ω・ψ を含む数も）。
//!
//! どれも Cantor 標準形 α = ω^{e_1}·c_1 + … + ω^{e_k}·c_k（e_1 > … > e_k）の上で計算する
//! （[`Veblen::cnf`]。ε 数・Ω・ψ(x) のように ω^x = x となる主項は、指数が自分自身）。
//!
//! - 足し算：α の項のうち β の先頭の項より小さいものは吸収される（1 + ω = ω）。
//! - 掛け算：右の分配法則 α·(β + γ) = α·β + α·γ で β を項に分け、
//!   α·ω^f = ω^{e_1 + f}（f ≥ 1、e_1 は α の先頭の指数）、α·n は先頭の係数だけが n 倍。
//! - べき乗：β = λ + m（λ は 0 か ω の倍数、m は有限）と分けて α^β = α^λ·α^m。
//!   α が有限の n ≥ 2 なら、λ = ω·γ として n^λ = (n^ω)^γ = ω^γ。
//!   α が無限なら α^λ = ω^{e_1·λ}。α^m は掛け算を繰り返す（2 乗を使って log m 回）。
//!
//! 計算の過程（[`Calc::steps`]）も、それぞれの規則の説明つきで返す（Web と LaTeX 用）。
//!
//! 結果が大きくなりすぎるとき（主項の数が [`MAX_SIZE`] を超える）と、係数が u64 に
//! 収まらないときはエラーにする。例：(ω + 1)^1000 は 1001 項で計算できるが、
//! (ω + 1)^(10^9) は大きすぎる。

use crate::i18n::{is_en, tr};
use crate::latex::ToLatex;
use crate::veblen::Veblen;
use std::fmt;

/// 結果・途中の数の大きさの上限（[`Veblen::size`]：主項の数を引数の中まで数えたもの）。
pub const MAX_SIZE: usize = 5_000;

/// 演算の種類。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Add,
    Mul,
    Pow,
}

impl Op {
    /// "+"・"*"（"·"・"x"）・"^"（"**"）を読む。
    pub fn parse(s: &str) -> Option<Op> {
        match s.trim() {
            "+" | "add" => Some(Op::Add),
            "*" | "·" | "x" | "mul" => Some(Op::Mul),
            "^" | "**" | "pow" => Some(Op::Pow),
            _ => None,
        }
    }
}

/// 計算できなかった理由。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArithError {
    /// 係数（自然数）が u64 に収まらない
    Overflow,
    /// 結果（か途中の数）が大きすぎる
    TooLarge,
}

impl fmt::Display for ArithError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArithError::Overflow => write!(
                f,
                "{}",
                tr("係数が大きすぎます（2^64 未満の自然数だけ扱えます）", "a coefficient is too large (only natural numbers below 2^64 are supported)")
            ),
            ArithError::TooLarge => write!(
                f,
                "{}",
                if is_en() {
                    format!("the result is too large to write out (more than {MAX_SIZE} terms)")
                } else {
                    format!("結果が大きすぎて書き出せません（項が {MAX_SIZE} 個を超えます）")
                }
            ),
        }
    }
}

impl std::error::Error for ArithError {}

// 【Rust メモ】`type` は型の別名。`Result<Veblen>` と書けば `Result<Veblen, ArithError>` のこと
type Result<T> = std::result::Result<T, ArithError>;

fn check(v: Veblen) -> Result<Veblen> {
    if v.size() > MAX_SIZE { Err(ArithError::TooLarge) } else { Ok(v) }
}

fn add_ok(a: &Veblen, b: &Veblen) -> Result<Veblen> {
    a.checked_add(b).ok_or(ArithError::Overflow)
}

fn times(a: &Veblen, n: u64) -> Result<Veblen> {
    a.checked_mul_nat(n).ok_or(ArithError::Overflow)
}

/// α + β
pub fn add(a: &Veblen, b: &Veblen) -> Result<Veblen> {
    check(add_ok(a, b)?)
}

/// α の先頭の指数 e_1（α = ω^{e_1}·c_1 + …）。α = 0 なら `None`。
fn lead_exponent(a: &Veblen) -> Option<Veblen> {
    a.cnf().into_iter().next().map(|(e, _)| e)
}

/// α·β
pub fn mul(a: &Veblen, b: &Veblen) -> Result<Veblen> {
    let Some(e1) = lead_exponent(a) else { return Ok(Veblen::zero()) };
    let mut out = Veblen::zero();
    for (f, d) in b.cnf() {
        // α·(ω^f·d) = (α·ω^f)·d。f ≥ 1 なら α·ω^f = ω^{e_1 + f}、f = 0 なら α·d
        let part = if f.is_zero() { times(a, d)? } else { times(&Veblen::omega_pow(add(&e1, &f)?), d)? };
        out = add_ok(&out, &part)?;
    }
    check(out)
}

/// λ = ω·γ となる γ（λ は 0 か ω の倍数）：ω^f·d ↦ ω^{−1+f}·d。
fn div_omega(lim: &Veblen) -> Result<Veblen> {
    let mut out = Veblen::zero();
    for (f, d) in lim.cnf() {
        let f1 = f.minus_one_plus().expect("極限の部分の指数は 1 以上");
        out = add_ok(&out, &times(&Veblen::omega_pow(f1), d)?)?;
    }
    check(out)
}

/// α^m（m は有限）：2 乗を繰り返して log m 回の掛け算で。
fn pow_nat(a: &Veblen, m: u64) -> Result<Veblen> {
    let mut result = Veblen::one();
    let mut base = a.clone();
    let mut k = m;
    while k > 0 {
        if k & 1 == 1 {
            // α^i と α^j は掛ける順を入れ替えてもよい（どちらも α^{i+j}）
            result = mul(&result, &base)?;
        }
        k >>= 1;
        if k > 0 {
            base = mul(&base, &base)?;
        }
    }
    Ok(result)
}

/// α^β
pub fn pow(a: &Veblen, b: &Veblen) -> Result<Veblen> {
    if b.is_zero() {
        return Ok(Veblen::one());
    }
    if a.is_zero() || *a == Veblen::one() {
        return Ok(a.clone());
    }
    let (lim, m) = b.split_nat();
    if let Some(n) = a.as_nat() {
        // n ≥ 2：n^{ω·γ + m} = ω^γ·n^m
        let nm = u32::try_from(m).ok().and_then(|m| n.checked_pow(m)).ok_or(ArithError::Overflow)?;
        return mul(&Veblen::omega_pow(div_omega(&lim)?), &Veblen::nat(nm));
    }
    let e1 = lead_exponent(a).expect("0 でない");
    let x = mul(&e1, &lim)?;
    mul(&Veblen::omega_pow(x), &pow_nat(a, m)?)
}

/// 演算をする。
pub fn apply(op: Op, a: &Veblen, b: &Veblen) -> Result<Veblen> {
    match op {
        Op::Add => add(a, b),
        Op::Mul => mul(a, b),
        Op::Pow => pow(a, b),
    }
}

// ----------------------------------------------------------------------
// 計算の過程
// ----------------------------------------------------------------------

/// 計算の過程の 1 行：「= 式」とその理由。
#[derive(Clone, Debug)]
pub struct Step {
    /// 式（ふつうの文字で。例 `ω^(ε_0 + 1)·2`）
    pub plain: String,
    /// 式（LaTeX）
    pub tex: String,
    /// この行で使った規則
    pub note: String,
}

/// 計算の結果と過程。
#[derive(Clone, Debug)]
pub struct Calc {
    pub op: Op,
    /// 左辺（例 `(ω + 1)·ω`）
    pub lhs: String,
    pub lhs_tex: String,
    /// 左辺 = steps[0] = steps[1] = …（最後の行が結果）
    pub steps: Vec<Step>,
    pub result: Veblen,
}

impl Calc {
    /// 計算の過程を `align*` で（amsmath）。
    pub fn latex(&self) -> String {
        let mut out = String::from("\\begin{align*}\n");
        for (i, st) in self.steps.iter().enumerate() {
            let lhs = if i == 0 { self.lhs_tex.as_str() } else { "" };
            let end = if i + 1 < self.steps.len() { " \\\\" } else { "" };
            out.push_str(&format!("{lhs} &= {}{end}\n", st.tex));
        }
        out.push_str("\\end{align*}");
        out
    }
}

/// 途中の式（表示用）。`prec` は結合の強さ：0 = 和、1 = 積やべき（ω^x）、2 = それ以上分けられない。
#[derive(Clone, Debug)]
struct Ex {
    plain: String,
    tex: String,
    prec: u8,
}

fn ord(v: &Veblen) -> Ex {
    let cnf = v.cnf();
    let prec = match cnf.as_slice() {
        [] => 2,
        [(_, c)] if *c > 1 && !v.is_finite() => 1,
        // ω^x（x ≠ 1）はべきなので、べきの底になるときは括弧が要る
        [_] => match v.as_phi() {
            Some((a, b)) if a.is_zero() && !b.is_zero() && *b != Veblen::one() => 1,
            _ => 2,
        },
        _ => 0,
    };
    Ex { plain: v.to_string(), tex: v.to_latex(), prec }
}

fn nat(n: u64) -> Ex {
    Ex { plain: n.to_string(), tex: n.to_string(), prec: 2 }
}

fn omega() -> Ex {
    Ex { plain: "ω".into(), tex: "\\omega".into(), prec: 2 }
}

/// 結合の強さが `min` より弱ければ括弧でくくる。
fn wrap(e: &Ex, min: u8) -> Ex {
    if e.prec >= min {
        e.clone()
    } else {
        Ex { plain: format!("({})", e.plain), tex: format!("\\left({}\\right)", e.tex), prec: 2 }
    }
}

fn sum(parts: &[Ex]) -> Ex {
    if let [one] = parts {
        return one.clone();
    }
    Ex {
        plain: parts.iter().map(|p| p.plain.as_str()).collect::<Vec<_>>().join(" + "),
        tex: parts.iter().map(|p| p.tex.as_str()).collect::<Vec<_>>().join(" + "),
        prec: 0,
    }
}

fn prod(a: &Ex, b: &Ex) -> Ex {
    let (a, b) = (wrap(a, 1), wrap(b, 1));
    Ex { plain: format!("{}·{}", a.plain, b.plain), tex: format!("{} \\cdot {}", a.tex, b.tex), prec: 1 }
}

fn power(base: &Ex, exp: &Ex) -> Ex {
    let base = wrap(base, 2);
    let plain = if exp.prec == 2 { format!("{}^{}", base.plain, exp.plain) } else { format!("{}^({})", base.plain, exp.plain) };
    Ex { plain, tex: format!("{}^{{{}}}", base.tex, exp.tex), prec: 1 }
}

/// ω^f·d の項（f = 0 なら d）を表示用に。
fn term(f: &Veblen, d: u64) -> Ex {
    ord(&Veblen::omega_pow(f.clone()).mul_nat(d))
}

fn step(e: &Ex, note: String) -> Step {
    Step { plain: e.plain.clone(), tex: e.tex.clone(), note }
}

fn result_step(v: &Veblen, note: String) -> Step {
    step(&ord(v), note)
}

/// 最後の行が結果と違う形なら、「標準形にする」行を足す。
fn finish(steps: &mut Vec<Step>, result: &Veblen, note: String) {
    let r = ord(result);
    if steps.last().is_none_or(|s| s.plain != r.plain) {
        steps.push(step(&r, note));
    }
}

/// 演算をして、計算の過程も返す。
pub fn calc(op: Op, a: &Veblen, b: &Veblen) -> Result<Calc> {
    let result = apply(op, a, b)?;
    let (ea, eb) = (ord(a), ord(b));
    let lhs = match op {
        // β が和なら括弧でくくる（(α + β) + γ = α + (β + γ) なので値は同じだが、読みやすく）
        Op::Add => sum(&[ea.clone(), wrap(&eb, 1)]),
        Op::Mul => prod(&ea, &eb),
        Op::Pow => power(&ea, &eb),
    };
    let steps = match op {
        Op::Add => add_steps(a, b, &result),
        Op::Mul => mul_steps(a, b, &result)?,
        Op::Pow => pow_steps(a, b, &result)?,
    };
    Ok(Calc { op, lhs: lhs.plain, lhs_tex: lhs.tex, steps, result })
}

fn add_steps(a: &Veblen, b: &Veblen, result: &Veblen) -> Vec<Step> {
    if a.is_zero() || b.is_zero() {
        return vec![result_step(result, tr("0 を足しても変わらない", "adding 0 changes nothing").into())];
    }
    let bt: Vec<(Veblen, u64)> = b.principal_terms().collect();
    let lead = bt[0].0.clone();
    let mut kept = Vec::new();
    let mut same = None;
    let mut absorbed = Vec::new();
    for (p, c) in a.principal_terms() {
        match p.cmp(&lead) {
            std::cmp::Ordering::Greater => kept.push(ord(&p.mul_nat(c))),
            std::cmp::Ordering::Equal => same = Some(ord(&p.mul_nat(c))),
            std::cmp::Ordering::Less => absorbed.push(ord(&p.mul_nat(c))),
        }
    }
    let merge_note = || -> String {
        if is_en() {
            format!("collect the equal terms {lead}")
        } else {
            format!("同じ項 {lead} をまとめる")
        }
    };
    let mut steps = Vec::new();
    if !absorbed.is_empty() {
        let gone = sum(&absorbed).plain;
        let note = if is_en() {
            format!("terms of α smaller than the leading term {lead} of β are absorbed ({gone}), as in 1 + ω = ω")
        } else {
            format!("α の項のうち β の先頭の項 {lead} より小さいもの（{gone}）は吸収される（1 + ω = ω と同じ）")
        };
        if same.is_some() {
            let mut shown = kept.clone();
            shown.extend(same.clone());
            shown.extend(bt.iter().map(|(p, c)| ord(&p.mul_nat(*c))));
            steps.push(step(&sum(&shown), note));
            finish(&mut steps, result, merge_note());
        } else {
            steps.push(result_step(result, note));
        }
    } else if same.is_some() {
        steps.push(result_step(result, merge_note()));
    } else {
        steps.push(result_step(result, tr("吸収される項はなく、項を並べるだけ", "no term is absorbed; the terms are just written in a row").into()));
    }
    steps
}

fn mul_steps(a: &Veblen, b: &Veblen, result: &Veblen) -> Result<Vec<Step>> {
    if a.is_zero() || b.is_zero() {
        return Ok(vec![result_step(result, tr("0 を掛けると 0", "anything times 0 is 0").into())]);
    }
    let ea = ord(a);
    let bc = b.cnf();
    let e1 = lead_exponent(a).expect("0 でない");
    let mut steps = Vec::new();
    if bc.len() > 1 {
        let parts: Vec<Ex> = bc.iter().map(|(f, d)| prod(&ea, &term(f, *d))).collect();
        steps.push(step(
            &sum(&parts),
            tr("右の分配法則 α·(β + γ) = α·β + α·γ で、β を項ごとに分ける", "split β into its terms by right distributivity α·(β + γ) = α·β + α·γ").into(),
        ));
    }
    let mut parts = Vec::new();
    let (mut has_inf, mut has_fin) = (false, false);
    for (f, d) in &bc {
        if f.is_zero() {
            has_fin = true;
            parts.push(ord(&times(a, *d)?));
        } else {
            has_inf = true;
            let exp = if e1.is_zero() { ord(f) } else { sum(&[ord(&e1), ord(f)]) };
            let p = power(&omega(), &exp);
            parts.push(if *d > 1 { prod(&p, &nat(*d)) } else { p });
        }
    }
    let mut notes = Vec::new();
    if has_inf {
        notes.push(if e1.is_zero() {
            tr("有限の n では n·ω^f = ω^f（f ≥ 1）", "for a finite n, n·ω^f = ω^f (f ≥ 1)").to_string()
        } else if is_en() {
            format!("with ω^{e1} the leading term of α, α·ω^f = ω^({e1} + f) for f ≥ 1 (the other terms of α are absorbed)")
        } else {
            format!("α の先頭の項を ω^{e1} とすると、f ≥ 1 なら α·ω^f = ω^({e1} + f)（α の残りの項は吸収される）")
        });
    }
    if has_fin {
        notes.push(
            tr("有限の m を掛けると、先頭の項の係数だけが m 倍になる（(ω + 1)·2 = ω·2 + 1）", "multiplying by a finite m multiplies only the leading coefficient by m ((ω + 1)·2 = ω·2 + 1)")
                .to_string(),
        );
    }
    steps.push(step(&sum(&parts), notes.join(tr("。", "; "))));
    finish(&mut steps, result, tr("指数を計算して標準形にする", "evaluate the exponents to get the normal form").into());
    Ok(steps)
}

fn pow_steps(a: &Veblen, b: &Veblen, result: &Veblen) -> Result<Vec<Step>> {
    if b.is_zero() {
        return Ok(vec![result_step(result, tr("α^0 = 1", "α^0 = 1").into())]);
    }
    if a.is_zero() {
        return Ok(vec![result_step(result, tr("0^β = 0（β ≥ 1）", "0^β = 0 (β ≥ 1)").into())]);
    }
    if *a == Veblen::one() {
        return Ok(vec![result_step(result, tr("1^β = 1", "1^β = 1").into())]);
    }
    let ea = ord(a);
    let (lim, m) = b.split_nat();
    let mut steps = Vec::new();
    // 説明の中の「α^λ」（λ が和なら括弧つき）
    let alpha = Ex { plain: "α".into(), tex: "\\alpha".into(), prec: 2 };
    let a_lim = power(&alpha, &ord(&lim)).plain;
    // 「ω^λ」の λ の部分（和なら括弧つき）
    let lim_p = power(&omega(), &ord(&lim)).plain.trim_start_matches("ω^").to_string();
    // α^m の表示（m = 0 なら付けない）
    let am_ex = |m: u64| if m == 1 { ea.clone() } else { power(&ea, &nat(m)) };
    let with_am = |x: &Ex, am: Option<&Ex>| match am {
        Some(am) => prod(x, am),
        None => x.clone(),
    };
    if !lim.is_zero() && m > 0 {
        let note = if is_en() {
            format!("α^(β + m) = α^β·α^m with β = {lim} (a multiple of ω) and m = {m}")
        } else {
            format!("α^(β + m) = α^β·α^m（β = {lim} は ω の倍数、m = {m}）")
        };
        steps.push(step(&prod(&power(&ea, &ord(&lim)), &am_ex(m)), note));
    }
    if let Some(n) = a.as_nat() {
        // n ≥ 2
        if !lim.is_zero() {
            let gamma = div_omega(&lim)?;
            let nm = (m > 0).then(|| power(&nat(n), &nat(m)));
            let note = if is_en() {
                format!("{lim} = ω·γ with γ = {gamma}, so {n}^(ω·γ) = ({n}^ω)^γ = ω^γ (since {n}^ω = ω)")
            } else {
                format!("{lim} = ω·γ（γ = {gamma}）と書けるので {n}^(ω·γ) = ({n}^ω)^γ = ω^γ（{n}^ω = ω だから）")
            };
            steps.push(step(&with_am(&power(&omega(), &ord(&gamma)), nm.as_ref()), note));
        }
        finish(&mut steps, result, tr("計算して標準形にする", "evaluate to get the normal form").into());
        return Ok(steps);
    }
    let e1 = lead_exponent(a).expect("0 でない");
    let am_val = if m > 1 { Some(pow_nat(a, m)?) } else { None };
    let am_shown = (m > 0).then(|| am_ex(m));
    let mut x_ex = None;
    if !lim.is_zero() {
        let note = match (e1 == Veblen::one(), is_en()) {
            (true, true) => format!("the leading term of α is ω and {lim} is a multiple of ω, so {a_lim} = ω^{lim_p}"),
            (true, false) => format!("α の先頭の項が ω で {lim} は ω の倍数なので、{a_lim} = ω^{lim_p}"),
            (false, true) => format!("the leading term of α is ω^{e1} and {lim} is a multiple of ω, so {a_lim} = ω^({e1}·{lim})"),
            (false, false) => format!("α の先頭の項が ω^{e1} で {lim} は ω の倍数なので、{a_lim} = ω^({e1}·{lim})"),
        };
        // e_1 = 1（α の先頭が ω）なら 1·λ = λ なので、掛け算の形は書かない
        let exp = if e1 == Veblen::one() { ord(&lim) } else { prod(&ord(&e1), &ord(&lim)) };
        steps.push(step(&with_am(&power(&omega(), &exp), am_shown.as_ref()), note));
        let x = mul(&e1, &lim)?;
        let xe = power(&omega(), &ord(&x));
        if steps.last().is_some_and(|s| s.plain != with_am(&xe, am_shown.as_ref()).plain) {
            let note = if is_en() { format!("multiply the exponents: {e1}·{lim} = {x}") } else { format!("指数の掛け算 {e1}·{lim} = {x}") };
            steps.push(step(&with_am(&xe, am_shown.as_ref()), note));
        }
        x_ex = Some(xe);
    }
    if let Some(am) = &am_val {
        let shown = ord(am);
        let note = if is_en() {
            format!("α^{m} = α·α·…·α ({m} factors) = {am}")
        } else {
            format!("α^{m} = α·α·…·α（{m} 個）= {am}")
        };
        steps.push(step(&x_ex.as_ref().map_or(shown.clone(), |x| prod(x, &shown)), note));
    }
    finish(&mut steps, result, tr("掛け算をして標準形にする", "multiply out to get the normal form").into());
    Ok(steps)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(s: &str) -> Veblen {
        s.parse().unwrap()
    }

    #[test]
    fn known_values() {
        let cases = [
            ("1", "+", "ω", "ω"),
            ("ω", "+", "1", "ω + 1"),
            ("ω^2 + ω", "+", "ω^2", "ω^2·2"),
            ("ω + 1", "*", "2", "ω·2 + 1"),
            ("2", "*", "ω", "ω"),
            ("ω + 1", "*", "ω", "ω^2"),
            ("ω + 1", "*", "ω + 1", "ω^2 + ω + 1"),
            ("ω^ω", "*", "ω^ω", "ω^(ω·2)"),
            ("ε_0", "*", "ε_0", "ω^(ε_0·2)"),
            ("ε_0", "*", "ω", "ω^(ε_0 + 1)"),
            ("2", "^", "ω", "ω"),
            ("2", "^", "ω + 1", "ω·2"),
            ("2", "^", "ω·2 + 3", "ω^2·8"),
            ("3", "^", "ω^ω", "ω^ω^ω"),
            ("ω", "^", "ω", "ω^ω"),
            ("ω + 1", "^", "2", "ω^2 + ω + 1"),
            ("ω + 1", "^", "ω", "ω^ω"),
            ("ω·2", "^", "2", "ω^2·2"),
            ("ω", "^", "ε_0", "ε_0"),
            ("ε_0", "^", "ω", "ω^ω^(ε_0 + 1)"), // ε_0·ω = ω^(ε_0 + 1)
            ("ε_0", "^", "ε_0", "ω^ω^(ε_0·2)"),
            ("Ω", "*", "Ω", "ω^(Ω·2)"),
            ("Ω + 1", "*", "ω", "ω^(Ω + 1)"),
            ("ψ(0)", "^", "2", "ω^(ψ(0)·2)"),
            ("2", "^", "Ω", "Ω"),
            ("ω", "^", "Ω + 1", "ω^(Ω + 1)"),
        ];
        for (a, op, b, want) in cases {
            let got = apply(Op::parse(op).unwrap(), &v(a), &v(b)).unwrap();
            assert_eq!(got, v(want), "{a} {op} {b} = {got}（期待 {want}）");
        }
    }

    #[test]
    fn errors() {
        assert_eq!(mul(&v("ω·5000000000"), &v("5000000000")), Err(ArithError::Overflow));
        assert_eq!(pow(&v("2"), &v("64")), Err(ArithError::Overflow));
        assert_eq!(pow(&v("ω + 1"), &v("1000000000")), Err(ArithError::TooLarge));
        assert_eq!(pow(&v("ω + 1"), &v("1000")).map(|x| x.cnf().len()), Ok(1001));
    }

    #[test]
    fn steps_end_with_result() {
        for (a, op, b) in [("ω + 1", "*", "ω·2 + 3"), ("ε_0 + ω", "^", "ω + 2"), ("3", "^", "ω^2 + ω + 4"), ("ω^2 + ω + 1", "+", "ω^2·3")] {
            let c = calc(Op::parse(op).unwrap(), &v(a), &v(b)).unwrap();
            assert_eq!(c.steps.last().unwrap().plain, c.result.to_string(), "{a} {op} {b}");
            assert!(c.latex().starts_with("\\begin{align*}"));
        }
    }
}
