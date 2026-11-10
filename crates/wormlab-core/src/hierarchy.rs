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

use crate::bignum::BigNat;
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

/// Hardy 関数を計算するときの仕事量（基本列をとる順序数の大きさの合計）の上限。
/// 回数の上限（[`Budget`]）だけだと、φ(2, 0) のように基本列の項がどんどん大きくなる数で、
/// 打ち切るまでに何十秒もかかっていた（CLI の `hardy "φ(2,0)" 3`）。
pub const HARDY_MAX_WORK: u64 = 2_000_000;

/// Hardy 関数 H_α(n)。上限を超えたら `None`。
pub fn hardy(alpha: &Veblen, n: u128, budget: Budget) -> Option<u128> {
    let (mut a, mut n) = (alpha.clone(), n);
    let (mut steps, mut work) = (0u64, 0u64);
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
            work += a.size() as u64;
            if steps > budget.max_steps || work > HARDY_MAX_WORK {
                return None;
            }
            // Ω・ψ を含む数の基本列はまだ定義していないので、そこで打ち切る
            a = a.fundamental(u64::try_from(n).ok()?)?;
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
        a = a.fundamental(k)?;
        k += 1;
    }
    Some(steps)
}

/// worm（括弧語）の battle の長さ：⊤ になるまでの回数。
///
/// [`Bracket::battle_length_capped`]（逆順の Vec で、1 ステップの手間は変わった文字の数）で数える。
/// ε₀ 以上では語の長さが伸び続けるので、文字の数が [`MAX_BATTLE_LETTERS`] を超えても打ち切る（`None`）。
pub fn worm_battle_length(a: &Bracket, budget: Budget) -> Option<u64> {
    worm_battle_steps(a, budget).ok()
}

/// battle で数えられた所までのステップ数：⊤ に着いたら `Ok`、打ち切ったら `Err`（そこまでのステップ数は下界）。
pub fn worm_battle_steps(a: &Bracket, budget: Budget) -> Result<u64, u64> {
    a.battle_length_capped(budget.max_steps, MAX_BATTLE_LETTERS)
}

/// battle を実際に動かすときの語の大きさ（括弧の対の数）の上限（[`worm_battle_length_any`] で使う）。
pub const MAX_BATTLE_PAIRS: usize = 1_000_000;
/// battle を実際に動かすときの仕事量（各ステップの語の大きさの合計）の上限。数秒で止まる程度。
pub const MAX_BATTLE_WORK: u64 = 100_000_000;
/// 速い battle（逆順の Vec）で持つ文字の数の上限（メモリを使い切らないため。u32 の worm で 40 MB）。
pub const MAX_BATTLE_LETTERS: usize = 10_000_000;

/// 文字が有限の worm の battle の長さ（括弧語版より速い）。[`Worm::battle_length_capped`] で数える。
pub fn worm_battle_length_finite(a: &Worm, budget: Budget) -> Option<u64> {
    a.battle_length_capped(budget.max_steps, MAX_BATTLE_LETTERS).ok()
}

/// α から始めた worm battle の長さ（α の正規形の worm から出発）。
/// ε0 未満なら文字が有限の worm で、それ以上なら括弧語で数える。
pub fn worm_battle_length_of(alpha: &Veblen, budget: Budget) -> Option<u64> {
    match alpha.to_cnf() {
        Some(c) => worm_battle_length_finite(&Worm::from_ordinal(&c), budget),
        None if alpha.is_predicative() => worm_battle_length(&Bracket::from_ordinal(alpha), budget),
        None => None,
    }
}

/// α の正規形の括弧語から 1 ステップ進めたときの順序数（worm が作る「基本列」）。
pub fn worm_fundamental(alpha: &Veblen, n: usize) -> Option<Veblen> {
    if !alpha.is_predicative() {
        return None;
    }
    Bracket::from_ordinal(alpha).fundamental(n).map(|b| b.ordinal())
}

/// worm が作る基本列の**閉じた形**（ε₀ 未満、bc.md §3）：α{m} = D(α, m+1)。
///
/// D は標準の基本列 α[n] の「いちばん内側で +1 する」版：
/// - α = R + ω^{β+1} なら D(α, n) = R + ω^β·n + 1（ただし α = ω のときは n）
/// - α = R + ω^λ（λ は極限）なら D(α, n) = R + ω^{D(λ, n)}
///
/// （標準は (R + ω^{β+1})[n] = R + ω^β·n、(R + ω^λ)[n] = R + ω^{λ[n]}。）
/// worm の battle の 1 ステップは、順序数の言葉ではこの D で書ける。極限でない α や
/// ε₀ 以上の α では `None`。
pub fn worm_fs_closed(alpha: &Veblen, m: usize) -> Option<Veblen> {
    if !alpha.is_limit() || alpha.to_cnf().is_none() {
        return None;
    }
    Some(d_step(alpha, m as u64 + 1))
}

fn d_step(alpha: &Veblen, n: u64) -> Veblen {
    let mut cnf = alpha.cnf();
    let (e, c) = cnf.pop().expect("極限なので 0 でない");
    // R = 前の項 + ω^e·(c − 1)
    let mut r = Veblen::zero();
    for (ei, ci) in &cnf {
        r = r + Veblen::omega_pow(ei.clone()).mul_nat(*ci);
    }
    if c > 1 {
        r = r + Veblen::omega_pow(e.clone()).mul_nat(c - 1);
    }
    match e.pred() {
        // 最後の指数が後続 β+1：R + ω^β·n + 1（有限になるのは α = ω のときだけで、そのときは n）
        Some(beta) => {
            let x = r + Veblen::omega_pow(beta).mul_nat(n);
            if x.is_finite() { x } else { x + Veblen::nat(1) }
        }
        // 最後の指数が極限 λ：R + ω^{D(λ, n)}
        None => r + Veblen::omega_pow(d_step(&e, n)),
    }
}

/// battle の長さ：ちょうどの値か、下からの評価（「少なくともこれだけ」）。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Length {
    Exact(u128),
    /// 計算を打ち切った時点までに、すでにこれだけのステップを数えた（本当の長さはこれ以上）
    AtLeast(u128),
}

/// ε₀ 未満の α を表す worm の battle が、すでに `done` ステップ進んだところ
/// （次は {done+1} を使う）から ⊤ に着くまでの残りのステップ数。worm を作らずに、
/// 閉じた形 α{m} = D(α, m+1)（[`worm_fs_closed`]）で順序数だけを追う。
///
/// 末尾の有限部分 k は k ステップをまとめて進め、R + ω·c の形は 1 つの ω ごとに
/// 「進んだステップ数 j ↦ 2j + 4」をまとめて計算する（D(R + ω, j+2) = R + (j+3) のあと
/// j+3 回の引き算。R = 0 なら D(ω, j+2) = j+2 なので j ↦ 2j + 3）。
/// D の適用が `budget` 回を超えるか u128 を超えたら、そこまでに数えたステップ数を
/// [`Length::AtLeast`] で返す（数えたステップは実際に起きるので、正しい下界になる）。
/// ε₀ 以上なら `None`。
pub fn worm_battle_length_bound(alpha: &Veblen, done: u128, budget: Budget) -> Option<Length> {
    alpha.to_cnf()?;
    let mut a = alpha.clone();
    let mut j = done;
    let mut steps = 0u64;
    let at_least = |j: u128| Some(Length::AtLeast(j - done));
    loop {
        if a.is_zero() {
            return Some(Length::Exact(j - done));
        }
        // 末尾の有限部分：k 回の引き算
        let (head, k) = split_finite(&a);
        if k > 0 {
            match j.checked_add(k as u128) {
                Some(x) => j = x,
                None => return Some(Length::AtLeast(u128::MAX - done)),
            }
            a = head;
            continue;
        }
        // R + ω·c：ω を 1 つ外すごとに j ↦ 2j + 4（最後の 1 つで残りが 0 なら 2j + 3）
        let cnf = a.cnf();
        let (e, c) = cnf.last().expect("0 でない").clone();
        if e == Veblen::nat(1) {
            let mut r = Veblen::zero();
            for (ei, ci) in &cnf[..cnf.len() - 1] {
                r = r + Veblen::omega_pow(ei.clone()).mul_nat(*ci);
            }
            for i in 0..c {
                let last = i + 1 == c && r.is_zero();
                match j.checked_mul(2).and_then(|x| x.checked_add(if last { 3 } else { 4 })) {
                    Some(x) => j = x,
                    // この ω を外し終えるまでに少なくとも j + 1 + (j + 2) ステップ > u128
                    None => return Some(Length::AtLeast(u128::MAX - done)),
                }
            }
            a = r;
            continue;
        }
        steps += 1;
        if steps > budget.max_steps {
            return at_least(j);
        }
        // 次のステップは {j+1}：α ↦ D(α, j+2)
        let Some(n) = j.checked_add(2).and_then(|x| u64::try_from(x).ok()) else {
            return at_least(j);
        };
        a = d_step(&a, n);
        j += 1;
    }
}

/// [`worm_battle_length_bound`] のちょうどの値だけ（打ち切ったら `None`）。
pub fn worm_battle_remaining(alpha: &Veblen, done: u128, budget: Budget) -> Option<u128> {
    match worm_battle_length_bound(alpha, done, budget)? {
        Length::Exact(n) => Some(n),
        Length::AtLeast(_) => None,
    }
}

/// α = β + k（β は 0 か極限、k は有限）に分ける。
fn split_finite(a: &Veblen) -> (Veblen, u64) {
    let mut cnf = a.cnf();
    match cnf.last() {
        Some((e, k)) if e.is_zero() => {
            let k = *k;
            cnf.pop();
            let mut r = Veblen::zero();
            for (ei, ci) in &cnf {
                r = r + Veblen::omega_pow(ei.clone()).mul_nat(*ci);
            }
            (r, k)
        }
        _ => (a.clone(), 0),
    }
}

// ----------------------------------------------------------------------
// 多倍長で計算する版（u128 を超える値）
// ----------------------------------------------------------------------

/// 多倍長の計算の打ち切り条件。
#[derive(Clone, Copy, Debug)]
pub struct BigBudget {
    /// 基本列（D や α[n]）を取る回数の上限
    pub max_steps: u64,
    /// 途中の値の大きさの上限（2 進の桁数）。既定は 2^22 ビット（約 126 万桁）
    pub max_bits: u64,
}

impl Default for BigBudget {
    fn default() -> Self {
        BigBudget { max_steps: 10_000_000, max_bits: 1 << 22 }
    }
}

/// 多倍長で計算した値：ちょうどの値か、下からの評価。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BigValue {
    /// ちょうどの値
    Exact(BigNat),
    /// 2^k を超える（大きすぎて途中で止めたが、ここまでは確か）
    Above2Pow(BigNat),
    /// 計算の量の上限（回数・語の長さ・仕事量）で止めた。本当の値はこれ以上
    AtLeast(BigNat),
}

impl BigValue {
    pub fn exact(&self) -> Option<&BigNat> {
        match self {
            BigValue::Exact(n) => Some(n),
            _ => None,
        }
    }

    /// 「304371277216207601659」「1.0957732×10^40（41 桁、…）」「2^(4194306) を超える」など。
    pub fn describe(&self) -> String {
        match self {
            BigValue::Exact(n) => n.summary(),
            BigValue::Above2Pow(k) => {
                if crate::i18n::is_en() {
                    format!("greater than 2^{}", paren(&k.summary()))
                } else {
                    format!("2^{} を超える", paren(&k.summary()))
                }
            }
            BigValue::AtLeast(n) => {
                if crate::i18n::is_en() {
                    format!("at least {} (stopped at the computation limit)", n.summary())
                } else {
                    format!("{} 以上（計算の量の上限で打ち切り）", n.summary())
                }
            }
        }
    }

    /// LaTeX：`= 304\ldots`、`> 2^{4194306}`、`\geq …` の形（関係の記号から）。
    pub fn to_latex_relation(&self) -> String {
        match self {
            BigValue::Exact(n) => format!("= {}", n.to_latex_summary()),
            BigValue::Above2Pow(k) => format!("> 2^{{{}}}", k.to_latex_summary().replace("\\approx ", "")),
            BigValue::AtLeast(n) => format!("\\geq {}", n.to_latex_summary().replace("\\approx ", "")),
        }
    }
}

/// 数字だけなら括弧なし、「1.2×10^5（…）」のような表示なら括弧でくくる。
fn paren(s: &str) -> String {
    if s.chars().all(|c| c.is_ascii_digit()) { s.to_string() } else { format!("({s})") }
}

/// 途中で止めたときの理由。
enum Stop {
    /// 最後に着く添字は 2^k 以上
    Above(BigNat),
    /// 回数の上限。最後に着く添字はこの値以上
    Steps(BigNat),
}

struct GCtx {
    steps: u64,
    /// 再帰の深さ（[`MAX_DEPTH`] を超えたら、確かな下界 2^{x+2} で止める）
    depth: u32,
    budget: BigBudget,
}

/// g_principal の再帰の深さの上限（スタックを使い切らないため）。
const MAX_DEPTH: u32 = 1000;

impl GCtx {
    fn step(&mut self, x: &BigNat) -> Result<(), Stop> {
        self.steps += 1;
        if self.steps > self.budget.max_steps { Err(Stop::Steps(x.clone())) } else { Ok(()) }
    }
}

/// G_α(x)：添字 x（すでに x ステップ進んだ）から α の worm battle で α を食べ終えたときの添字。
/// D は最後の項だけを書き換えるので、G は CNF の項ごとの合成になる：
/// G_{γ_1 + … + γ_k} = G_{γ_1} ∘ … ∘ G_{γ_k}（右の項から）。
/// （ただし全体がちょうど ω になったときの D(ω, n) = n は、ここでは n + 1 として数える。
///   battle は必ず一度だけ ω を通るので、残りのステップ数は G_α(j) − j − 1。）
fn g_ordinal(alpha: &Veblen, x: BigNat, ctx: &mut GCtx) -> Result<BigNat, Stop> {
    let mut x = x;
    for (e, c) in alpha.cnf().iter().rev() {
        x = g_power(e, *c, x, ctx)?;
    }
    Ok(x)
}

/// G_{ω^e} を c 回：
/// - e = 0：x + c
/// - e = 1：2^c(x + 4) − 4（1 回ごとに x ↦ 2x + 4）
/// - e ≥ 2：1 回ずつ [`g_principal`]
fn g_power(e: &Veblen, c: u64, x: BigNat, ctx: &mut GCtx) -> Result<BigNat, Stop> {
    if e.is_zero() {
        return Ok(x.add_small(c));
    }
    if *e == Veblen::one() {
        let y = x.add_small(4);
        if y.bits() + c > ctx.budget.max_bits {
            // 2^c(x + 4) − 4 ≥ 2^(c + bits(x + 4) − 2)
            return Err(Stop::Above(BigNat::from(c).add_small(y.bits() - 2)));
        }
        return Ok(y.shl(c).sub_small(4).expect("4 以上"));
    }
    let mut x = x;
    for _ in 0..c {
        ctx.step(&x)?;
        x = g_principal(e, x, ctx)?;
    }
    Ok(x)
}

/// G_{ω^e}(x)、e ≥ 2：
/// - e = 2：2^{x+2}(x + 6) − 4（D(ω², x+2) = ω·(x+2) + 1 のあと x + 2 個の ω）
/// - e = β + 1：G_{ω^β} を x + 2 回、x + 2 から（D(ω^{β+1}, x+2) = ω^β·(x+2) + 1）
/// - e が極限：G_{ω^{D(e, x+2)}}(x + 1)
///
/// どの場合も G_{ω^e}(x) ≥ G_{ω²}(x) ≥ 2^{x+2} なので、x が大きすぎたら 2^{x+2} 以上として止める。
fn g_principal(e: &Veblen, x: BigNat, ctx: &mut GCtx) -> Result<BigNat, Stop> {
    let small = x.to_u64().filter(|&v| v.saturating_add(2) <= ctx.budget.max_bits);
    let Some(xs) = small else {
        return Err(Stop::Above(x.add_small(2)));
    };
    let n = xs + 2;
    if *e == Veblen::nat(2) {
        return Ok(BigNat::from(xs + 6).shl(n).sub_small(4).expect("4 以上"));
    }
    if ctx.depth >= MAX_DEPTH {
        // e ≥ 3、x ≥ 1 なら G_{ω^e}(x) ≥ G_{ω³}(x) = G_{ω²}^{x+2}(x+2) ≥ G_{ω²}(G_{ω²}(x+2)) ≥ 2^{G_{ω²}(x+2)+2}
        // （e = β+1 は 1 回目の反復だけを見て β に下げ、極限 e は D(e, x+2) ≥ x+2 ≥ 3 に下げる帰納法）
        if xs >= 1 && xs + 4 <= ctx.budget.max_bits {
            let y = BigNat::from(xs + 8).shl(xs + 4).sub_small(4).expect("4 以上");
            return Err(Stop::Above(y.add_small(2)));
        }
        return Err(Stop::Above(x.add_small(2)));
    }
    ctx.depth += 1;
    let out = match e.pred() {
        Some(beta) => g_power(&beta, n, BigNat::from(n), ctx),
        None => ctx.step(&x).and_then(|()| g_power(&d_step(e, n), 1, x.add_small(1), ctx)),
    };
    ctx.depth -= 1;
    out
}

/// [`worm_battle_length_bound`] の多倍長版：ε₀ 未満の α を表す worm の battle が、すでに
/// `done` ステップ進んだところから ⊤ に着くまでの残りのステップ数。ε₀ 以上なら `None`。
///
/// 値が `budget.max_bits` ビットを超えそうになったら、そこまでで分かる下界 2^k を返す
/// （[`BigValue::Above2Pow`]）。例：ω³ は 2^126·130 − 5 ≈ 1.1059177×10^40 ステップ（ちょうど）、
/// ω³ + 1 は 2^(2^286·290 − 3) を超える。
pub fn worm_battle_length_big(alpha: &Veblen, done: &BigNat, budget: BigBudget) -> Option<BigValue> {
    alpha.to_cnf()?;
    if let Some(k) = alpha.as_nat() {
        return Some(BigValue::Exact(BigNat::from(k)));
    }
    let mut ctx = GCtx { steps: 0, depth: 0, budget };
    let start = done.add_small(1);
    Some(match g_ordinal(alpha, done.clone(), &mut ctx) {
        Ok(fin) => BigValue::Exact(fin.sub(&start).expect("最後の添字は done + 1 以上")),
        Err(Stop::Above(k)) => {
            // 残り = 最後の添字 − done − 1 ≥ 2^k − (done + 1) ≥ 2^(k−1)（2^(k−1) ≥ done + 1 なら）
            if k > BigNat::from(start.bits()) {
                BigValue::Above2Pow(k.sub_small(1).expect("1 以上"))
            } else {
                let k = k.to_u64().expect("小さい");
                BigValue::AtLeast(BigNat::pow2(k).saturating_sub(&start))
            }
        }
        Err(Stop::Steps(x)) => BigValue::AtLeast(x.saturating_sub(&start)),
    })
}

impl BigValue {
    /// 先に s ステップ進んでいた分を足す。
    fn plus(self, s: u64) -> BigValue {
        match self {
            BigValue::Exact(n) => BigValue::Exact(n.add_small(s)),
            BigValue::AtLeast(n) => BigValue::AtLeast(n.add_small(s)),
            above => above,
        }
    }
}

/// α（Γ0 未満）を表す worm の battle の長さ（多倍長）。
/// - ε₀ 未満：閉じた形（[`worm_battle_length_big`]）
/// - ε₀ 以上：括弧語の battle を、順序数が ε₀ 未満に落ちるまで実際に動かし、そこから閉じた形に
///   切り替える（例：ε₀ は 1 ステップで ε₀{1} = ω^{ω^2}… の有限の worm になる）。
///   切り替えるのは語が正規形のとき（a* が有限の文字の標準形の worm、つまり o の自然な worm の
///   とき）だけにして、閉じた形の定理の前提を満たすようにする。
///
/// 動かす部分は語の長さと仕事量で打ち切る（そのときは数えたステップ数を下界として返す）。
/// Ω・ψ を含む数では `None`。
pub fn worm_battle_length_any(alpha: &Veblen, budget: BigBudget) -> Option<BigValue> {
    if alpha.to_cnf().is_some() {
        return worm_battle_length_big(alpha, &BigNat::zero(), budget);
    }
    if !alpha.is_predicative() {
        return None;
    }
    let (mut steps, mut work) = (0u64, 0u64);
    for w in Bracket::from_ordinal(alpha).battle().skip(1) {
        steps += 1;
        let size = w.pairs();
        work += size as u64;
        if size > MAX_BATTLE_PAIRS || work > MAX_BATTLE_WORK || steps > budget.max_steps {
            return Some(BigValue::AtLeast(BigNat::from(steps - 1)));
        }
        // o* < ε₀ ⟺ 文字がすべて有限 ⟺ 入れ子が 2 段以下（文字 ()…() は自然数）。順序数の計算は重いので先に見る
        if w.depth() > 2 {
            continue;
        }
        let o = w.ordinal();
        if o.to_cnf().is_some() && w.is_normal_syntactic() {
            let rest = worm_battle_length_big(&o, &BigNat::from(steps), budget)?;
            return Some(rest.plus(steps));
        }
    }
    Some(BigValue::Exact(BigNat::from(steps)))
}

/// [`hardy`] の多倍長版。末尾の有限部分 k、ω·c、ω²·c はまとめて計算する
/// （H_{β+k}(n) = H_β(n + k)、H_{β+ω·c}(n) = H_β(n·2^c)、H_{ω²}(n) = n·2^n）。
/// それ以外の極限では α[n] を取るので、n が u64 に収まらなくなったらそこで止める
/// （H_β(m) ≥ m なので、そのときの n が下界）。Ω・ψ を含む数では `None`。
pub fn hardy_big(alpha: &Veblen, n: &BigNat, budget: BigBudget) -> Option<BigValue> {
    if !alpha.is_predicative() {
        return None;
    }
    let (mut a, mut n) = (alpha.clone(), n.clone());
    let (mut steps, mut work) = (0u64, 0u64);
    while let Some((beta, x, y, c)) = a.split_last() {
        if x.is_zero() && y.is_zero() {
            n = n.add_small(c);
            a = beta;
        } else if x.is_zero() && y.as_nat() == Some(1) {
            // n·2^c ≥ 2^(c + bits(n) − 1)
            if n.bits() + c > budget.max_bits {
                return Some(BigValue::Above2Pow(BigNat::from(c).add_small(n.bits() - 1)));
            }
            n = n.shl(c);
            a = beta;
        } else if x.is_zero() && y.as_nat() == Some(2) {
            for _ in 0..c {
                // n·2^n ≥ 2^n
                let Some(k) = n.to_u64().filter(|&k| k.saturating_add(n.bits()) <= budget.max_bits) else {
                    return Some(BigValue::Above2Pow(n));
                };
                n = n.shl(k);
            }
            a = beta;
        } else {
            steps += 1;
            work += a.size() as u64;
            if steps > budget.max_steps || work > HARDY_MAX_WORK {
                return Some(BigValue::AtLeast(n));
            }
            let Some(k) = n.to_u64() else {
                return Some(BigValue::AtLeast(n));
            };
            a = a.fundamental(k)?;
        }
    }
    Some(BigValue::Exact(n))
}

/// 画面に並べる Hardy 関数の値 H_α(1..5)（ε₀ 未満だけ。多倍長で 2^16 ビットまで）。
/// ちょうどの値でなくなったら（下界・打ち切り）、そこから先の n は計算しない。
pub fn hardy_samples(alpha: &Veblen) -> Vec<(u128, Option<BigValue>)> {
    let mut out = Vec::new();
    if alpha.to_cnf().is_none() {
        return out;
    }
    let budget = BigBudget { max_steps: 20_000, max_bits: 1 << 16 };
    for n in 1..=5u128 {
        let v = hardy_big(alpha, &BigNat::from(n), budget);
        let stop = !matches!(v, Some(BigValue::Exact(_)));
        out.push((n, v));
        if stop {
            break;
        }
    }
    out
}

/// 急増加関数 f_α(n) = H_{ω^α}(n) の多倍長版。
pub fn fast_growing_big(alpha: &Veblen, n: &BigNat, budget: BigBudget) -> Option<BigValue> {
    hardy_big(&Veblen::omega_pow(alpha.clone()), n, budget)
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

    /// 閉じた形で数えた battle の長さが、worm を実際に動かした長さと一致する
    #[test]
    fn battle_length_by_closed_form() {
        for a in ["3", "ω", "ω + 2", "ω·2", "ω·3", "ω^2", "ω^2 + 1", "ω^2 + ω", "ω^2 + ω + 1", "ω^2 + ω·2"] {
            let x = v(a);
            let sim = worm_battle_length_of(&x, Budget::default());
            let closed = worm_battle_remaining(&x, 0, Budget::default()).map(|n| n as u64);
            assert_eq!(sim, closed, "α = {a}");
        }
        // ω^2 + ω·2 は 294,907 回（hierarchy.md の表）
        assert_eq!(worm_battle_remaining(&v("ω^2 + ω·2"), 0, Budget::default()), Some(294_907));
    }

    fn big(s: &str) -> BigValue {
        worm_battle_length_big(&v(s), &BigNat::zero(), BigBudget::default()).unwrap()
    }

    /// 多倍長版は u128 版と（u128 に収まる範囲で）一致し、その先もちょうどの値を出す
    #[test]
    fn battle_length_big() {
        for a in ["0", "5", "ω", "ω + 2", "ω·3", "ω^2", "ω^2 + ω·3", "ω^2 + ω·4", "ω^2·2", "ω^ω", "ω^ω + ω^3·2 + 7"] {
            let small = worm_battle_length_bound(&v(a), 0, Budget::default()).unwrap();
            match (small, big(a)) {
                (Length::Exact(n), BigValue::Exact(m)) => assert_eq!(BigNat::from(n), m, "α = {a}"),
                (Length::AtLeast(_), BigValue::Exact(m)) => assert!(m.bits() > 127, "α = {a}"),
                (Length::AtLeast(_), BigValue::Above2Pow(_)) => {}
                (s, b) => panic!("α = {a}: {s:?} と {b:?}"),
            }
        }
        // ω³：2^126·130 − 5（約 1.1×10^40）
        let w3 = BigNat::pow2(126).mul_small(130).sub_small(5).unwrap();
        assert_eq!(big("ω^3"), BigValue::Exact(w3));
        // ω² + ω·k：2^(j+2)(j+6) − 5、j = 2^(k+2) − 4（k = 5〜8 は u128 を超える）
        for k in 5..=8u64 {
            let j = (1u64 << (k + 2)) - 4;
            let want = BigNat::pow2(j + 2).mul_small(j + 6).sub_small(5).unwrap();
            assert_eq!(big(&format!("ω^2 + ω·{k}")), BigValue::Exact(want), "k = {k}");
        }
        // ω³ + 1：添字 1 から G_{ω²} を 3 回。3 回目の引数 2^286·290 − 4 で上限を超える
        let x = BigNat::pow2(286).mul_small(290).sub_small(4).unwrap();
        assert_eq!(big("ω^3 + 1"), BigValue::Above2Pow(x.add_small(1)));
        // done から始めた残りは done について増える
        let from = |j: u64| worm_battle_length_big(&v("ω^2 + ω"), &BigNat::from(j), BigBudget::default()).unwrap();
        assert!(from(3).exact().unwrap() < from(4).exact().unwrap());
    }

    /// ε₀ 以上：括弧語の battle を ε₀ 未満に落ちるまで動かしてから閉じた形
    #[test]
    fn battle_length_any() {
        let any = |s: &str| worm_battle_length_any(&v(s), BigBudget::default()).unwrap();
        // ε₀ 未満は閉じた形と同じ
        for a in ["7", "ω^2 + ω·4", "ω^3", "ω^3 + 1"] {
            assert_eq!(any(a), big(a), "α = {a}");
        }
        // ε₀：1 ステップで ε₀{1}（有限の worm）になり、そこから閉じた形 = 1 + rem(ε₀{1}, 1)
        let e1 = worm_fundamental(&v("ε_0"), 1).unwrap();
        assert!(e1.to_cnf().is_some());
        let rest = worm_battle_length_big(&e1, &BigNat::from(1u64), BigBudget::default()).unwrap();
        assert_eq!(any("ε_0"), rest.plus(1));
        // Thm 52 の a'_2 = ()((()))（o* = ε₀ + 1）：G(2) は 2^(10^400) を超える
        match any("ε_0 + 1") {
            BigValue::Above2Pow(k) => assert!(k.decimal_digits() > 400, "{}", k.summary()),
            other => panic!("{other:?}"),
        }
        // Ω・ψ を含む数は扱わない
        assert_eq!(worm_battle_length_any(&v("ψ(0)"), BigBudget::default()), None);
    }

    #[test]
    fn hardy_big_values() {
        let hb = |s: &str, n: u64| hardy_big(&v(s), &BigNat::from(n), BigBudget::default()).unwrap();
        // u128 版と一致
        for (s, n) in [("ω^2", 10), ("ω^2 + ω", 3), ("ω^ω", 2), ("ω^3", 2), ("ε_0", 2)] {
            assert_eq!(hb(s, n).exact().and_then(BigNat::to_u128), h(s, n as u128), "H_{s}({n})");
        }
        // H_{ω²}(200) = 200·2^200（u128 を超える）
        assert_eq!(hb("ω^2", 200), BigValue::Exact(BigNat::pow2(200).mul_small(200)));
        // H_{ω³}(3) = H_{ω²}^3(3)：3 → 24 → 402653184 → 402653184·2^402653184（上限を超える）
        assert_eq!(hb("ω^3", 3), BigValue::Above2Pow(BigNat::from(402_653_184u64)));
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
