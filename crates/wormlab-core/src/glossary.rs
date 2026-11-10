//! 定義集：wormlab で使うゲーム・基本列・順序数上の関数・表記と順序数の対応・体系の意味論の定義を、
//! 出典つきで一か所に集めたもの（Web の「規則と定義」タブの定義の側・CLI の `defs`）。
//!
//! - 各定義は、文字の式（日本語・英語）・LaTeX・出典・関連する定義・試せるタブを持つ。
//! - 「計算した例」は、定義の場合分けごとに 1 つずつ（[`Example`]：どの場合か・その例）。
//!   例の値は、その場で wormlab-core の実装を呼んで作る。だから例は実装と必ず一致する
//!   （定義の文と実装がずれていれば、例の値で気づける）。
//! - 特殊な場合（Cantor 標準形の基本列・文字が自然数の worm の基本列など）は別の定義にして、
//!   [`Entry::general`]・[`Entry::special`] で一般の場合とつなぐ。
//! - 足し算・φ・ψ など、式の標準形（[`crate::expr`]）が使う定義は [`crate::expr::definitions`] の文を
//!   そのまま使い、ここで LaTeX と例を足す。
//! - LaTeX は数式だけ（`align*`。言葉は短い英語の `\text{…}`）にして、言語によらず pdflatex でも
//!   MathJax でも読めるようにする。

use crate::bc;
use crate::bignum::BigNat;
use crate::bracket::{Bracket, depth_bound};
use crate::expr;
use crate::headbody;
use crate::hierarchy::{self, BigBudget, Budget};
use crate::i18n::{is_en, tr};
use crate::iworm::{self, IWorm};
use crate::notation::{self, Notation};
use crate::rc;
use crate::rcbi;
use crate::rcbi_order::{self, Form};
use crate::spf::Sequent;
use crate::veblen::Veblen;
use crate::worm::Worm;
use serde::Serialize;
use std::cmp::Ordering;

/// 定義の分類。
#[derive(Clone, Debug, Serialize)]
pub struct Category {
    pub id: &'static str,
    pub name: String,
    /// 分類の説明（1 文）
    pub lead: String,
    pub entries: Vec<Entry>,
}

/// 定義の場合分け 1 つと、その例。
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Example {
    /// どの場合か（規則の式か短い文。例 `ω^{b+1}[n] = ω^b·n`）
    pub case: String,
    /// その場合に当てはまる代表の例（wormlab で計算した値。例 `ω^2[3] = ω·3`）
    pub text: String,
    /// 同じ場合のほかの例（Web では「もっと見る」で開く）
    pub more: Vec<String>,
}

/// 1 つの定義。
#[derive(Clone, Debug, Serialize)]
pub struct Entry {
    /// 鍵（Web のリンク・CLI の `defs <鍵>` で使う。英小文字とハイフン）
    pub key: &'static str,
    /// 記号（例 `φ(α, β)`）
    pub symbol: String,
    pub name: String,
    /// 定義の文（文字の式）
    pub lines: Vec<String>,
    /// 同じ定義の LaTeX（数式だけ）
    pub latex: String,
    /// 場合分けごとの例（wormlab-core の実装を呼んで作る）
    pub examples: Vec<Example>,
    pub source: String,
    /// 関連する定義の鍵
    pub related: Vec<&'static str>,
    /// この定義を特別な場合として含む、一般の定義の鍵（例：Cantor 標準形の基本列 → 標準の基本列）
    pub general: Vec<&'static str>,
    /// この定義の特殊な場合の鍵（[`all`] が `general` を逆にたどって埋める）
    pub special: Vec<&'static str>,
    /// 試せるタブ（battle・ordinal・proof・rules・model）
    pub tab: Option<&'static str>,
    /// 研究中（論文の草稿の段階）の定義か
    pub research: bool,
}

/// 定義の材料（言語を選ぶ前）。
struct Raw {
    key: &'static str,
    symbol: &'static str,
    name: (&'static str, &'static str),
    lines: &'static [(&'static str, &'static str)],
    latex: &'static str,
    source: (&'static str, &'static str),
    related: &'static [&'static str],
    /// 一般の場合の鍵（[`Entry::general`]）
    general: &'static [&'static str],
    tab: Option<&'static str>,
    research: bool,
}

impl Raw {
    fn build(&self) -> Entry {
        Entry {
            key: self.key,
            symbol: self.symbol.to_string(),
            name: tr(self.name.0, self.name.1).to_string(),
            lines: self.lines.iter().map(|(j, e)| tr(j, e).to_string()).collect(),
            latex: self.latex.trim().to_string(),
            examples: examples(self.key),
            source: tr(self.source.0, self.source.1).to_string(),
            related: self.related.to_vec(),
            general: self.general.to_vec(),
            special: Vec::new(),
            tab: self.tab,
            research: self.research,
        }
    }
}

/// 式の標準形の定義（[`expr::definitions`]）に、LaTeX・関連・例を足したもの。
fn from_expr(key: &'static str, latex: &'static str, related: &'static [&'static str], general: &'static [&'static str]) -> Entry {
    let d = expr::definitions().into_iter().find(|d| d.key == key).expect("expr の定義の鍵");
    Entry {
        key: d.key,
        symbol: d.symbol,
        name: d.name,
        lines: d.lines,
        latex: latex.trim().to_string(),
        examples: examples(key),
        source: d.source,
        related: related.to_vec(),
        general: general.to_vec(),
        special: Vec::new(),
        tab: Some("ordinal"),
        research: false,
    }
}

/// すべての定義（今の言語で、分類ごと）。各定義の `special` は、ほかの定義の `general` を逆にたどって埋める。
pub fn all() -> Vec<Category> {
    let mut cats = categories();
    // 【Rust メモ】move クロージャ：内側のクロージャが e.key を借りずに値として持つ（外側の e が先に消えるため）
    let pairs: Vec<(&'static str, &'static str)> =
        cats.iter().flat_map(|c| c.entries.iter().flat_map(|e| e.general.iter().map(move |g| (*g, e.key)))).collect();
    for e in cats.iter_mut().flat_map(|c| c.entries.iter_mut()) {
        e.special = pairs.iter().filter(|(g, _)| *g == e.key).map(|(_, k)| *k).collect();
    }
    cats
}

fn categories() -> Vec<Category> {
    vec![
        Category {
            id: "games",
            name: tr("ゲームと長さ", "Games and their lengths").to_string(),
            lead: tr(
                "worm・括弧語・順序数・RC_BI の式を 1 段ずつ下げていくゲーム（battle）と、その長さ。",
                "The games (battles) that lower a worm, a bracket word, an ordinal or an RC_BI formula one step at a time, and their lengths.",
            )
            .to_string(),
            entries: GAMES.iter().map(Raw::build).collect(),
        },
        Category {
            id: "fundamental",
            name: tr("基本列", "Fundamental sequences").to_string(),
            lead: tr(
                "順序数・worm・括弧語・RC_BI の式を 1 段下げる列。Cantor 標準形・文字が自然数の worm の特殊な場合を、Veblen 表記・括弧語の一般の場合の手前に置き、「一般の場合」「特殊な場合」のリンクでつなぐ。battle はこの列を繰り返すゲーム。",
                "Sequences that lower an ordinal, a worm, a bracket word or an RC_BI formula by one step. The special cases (Cantor normal form, worms with natural-number letters) come before the general ones (Veblen notation, bracket words), linked as “general case” and “special cases”. A battle repeats these sequences.",
            )
            .to_string(),
            entries: FUNDAMENTAL.iter().map(Raw::build).collect(),
        },
        Category {
            id: "functions",
            name: tr("順序数上の関数", "Functions on ordinals").to_string(),
            lead: tr(
                "演算・Veblen 関数・超指数関数・崩壊関数と標準形、基本列で決まる Hardy 階層と急増加関数。",
                "Arithmetic, the Veblen function, hyperexponentials, the collapsing function and normal forms, and the Hardy and fast-growing hierarchies determined by fundamental sequences.",
            )
            .to_string(),
            entries: functions(),
        },
        Category {
            id: "notations",
            name: tr("表記と順序数の対応", "Notations and their ordinals").to_string(),
            lead: tr(
                "worm・括弧語・impredicative worm・RC_BI の式がどの順序数を表すか、と逆向きの写像・標準形。",
                "Which ordinal a worm, a bracket word, an impredicative worm or an RC_BI formula denotes, together with the inverse maps and normal forms.",
            )
            .to_string(),
            entries: NOTATIONS.iter().map(Raw::build).collect(),
        },
        Category {
            id: "semantics",
            name: tr("体系の意味論", "Semantics of the calculi").to_string(),
            lead: tr(
                "RC・BC・RC_BI の Kripke フレームと、判定に使う有限モデル。推論規則は、同じタブの「推論規則」の側にあります。",
                "Kripke frames for RC, BC and RC_BI, and the finite models used to decide them. The inference rules are under “Inference rules” on the same tab.",
            )
            .to_string(),
            entries: SEMANTICS.iter().map(Raw::build).collect(),
        },
    ]
}

/// 鍵で 1 つの定義を探す。
pub fn get(key: &str) -> Option<Entry> {
    all().into_iter().flat_map(|c| c.entries).find(|e| e.key == key)
}

// ----------------------------------------------------------------------
// ゲームと長さ
// ----------------------------------------------------------------------

const GAMES: &[Raw] = &[
    Raw {
        key: "worm-battle",
        symbol: "A⦃k⦄",
        name: ("worm battle", "Worm battle"),
        lines: &[
            (
                "worm A = n₁ n₂ … n_k は式 ⟨n₁⟩⟨n₂⟩…⟨n_k⟩⊤（文字は自然数、左端が外側、空の worm は ⊤）",
                "a worm A = n₁ n₂ … n_k is the formula ⟨n₁⟩⟨n₂⟩…⟨n_k⟩⊤ (natural-number letters, the leftmost is outermost, the empty worm is ⊤)",
            ),
            (
                "battle：A⦃0⦄ = A、A⦃k⦄ = A⦃k−1⦄{k}。k 回目の 1 ステップは、worm の基本列 A{n} を n = k で使う。⊤ に着いたら終わり",
                "the battle: A⦃0⦄ = A and A⦃k⦄ = A⦃k−1⦄{k}; step k applies the worm fundamental sequence A{n} with n = k, stopping at ⊤",
            ),
            (
                "どの n でも o(A{n}) < o(A) なので、battle はいつか必ず ⊤ に着く（worm principle）。この事実は PA では証明できない",
                "o(A{n}) < o(A) for every n, so every battle reaches ⊤ (the worm principle); this fact is not provable in PA",
            ),
        ],
        latex: r"
\begin{align*}
A\{\!\{0\}\!\} &= A, \qquad A\{\!\{k\}\!\} = A\{\!\{k-1\}\!\}\{k\} \quad (A\{n\} \text{ the fundamental sequence of worms})
\end{align*}",
        source: (
            "L. D. Beklemishev, The worm principle, Logic Colloquium '02, Lecture Notes in Logic 27（2006）。順序数との対応は Provability algebras and proof-theoretic ordinals I, APAL 128（2004）",
            "L. D. Beklemishev, The worm principle, Logic Colloquium '02, Lecture Notes in Logic 27 (2006); for the ordinals, Provability algebras and proof-theoretic ordinals I, APAL 128 (2004)",
        ),
        related: &["nat-worm-fs", "worm", "worm-o", "battle-length", "worm-fs"],
        general: &["bracket-battle"],
        tab: Some("battle"),
        research: false,
    },
    Raw {
        key: "bracket-battle",
        symbol: "a⦃k⦄",
        name: ("括弧語の battle", "Bracket-word battle"),
        lines: &[
            (
                "battle：a⦃0⦄ = a、a⦃k⦄ = a⦃k−1⦄{k}。k 回目の 1 ステップは、括弧語の基本列 a{n} を n = k で使う。⊤ に着いたら終わり",
                "the battle: a⦃0⦄ = a and a⦃k⦄ = a⦃k−1⦄{k}; step k applies the bracket-word fundamental sequence a{n} with n = k, stopping at ⊤",
            ),
            (
                "文字がすべて ()^m の形（有限）なら worm battle と同じ",
                "when every letter has the form ()^m (finite), it is the worm battle",
            ),
            (
                "いつか必ず ⊤ に着く（Thm 42）が、この事実は ATR₀ では証明できない（Thm 52）",
                "every battle reaches ⊤ (Thm 42), but this is not provable in ATR₀ (Thm 52)",
            ),
        ],
        latex: r"
\begin{align*}
a\{\!\{0\}\!\} &= a, \qquad a\{\!\{k\}\!\} = a\{\!\{k-1\}\!\}\{k\} \quad (a\{n\} \text{ the fundamental sequence of bracket words})
\end{align*}",
        source: (
            "D. Fernández-Duque & E. Hermo Reyes, Deducibility and Independence in Beklemishev's Autonomous Provability Calculus（arXiv:2008.13445）Def 19・§8・Thm 42・Thm 52",
            "D. Fernández-Duque & E. Hermo Reyes, Deducibility and Independence in Beklemishev's Autonomous Provability Calculus (arXiv:2008.13445), Def 19, §8, Thm 42 and Thm 52",
        ),
        related: &["bracket-fs", "bracket", "thm52", "battle-length"],
        general: &[],
        tab: Some("battle"),
        research: false,
    },
    Raw {
        key: "ordinal-battle",
        symbol: "α ← α[k]",
        name: ("標準 battle（順序数の battle）", "Standard battle (ordinal battle)"),
        lines: &[
            (
                "順序数 α から始めて、k = 1, 2, 3, … の順に α を α[k] で置き換える（後続順序数なら α[k] は直前の数）。0 に着いたら終わり",
                "starting from an ordinal α, replace α by α[k] for k = 1, 2, 3, … (for a successor, α[k] is its predecessor), stopping at 0",
            ),
            (
                "α[k] は標準の基本列。基本列は真に減るので、必ず有限回で 0 に着く",
                "α[k] is the standard fundamental sequence; it always decreases, so 0 is reached after finitely many steps",
            ),
            (
                "Web の探検では始めの k（1〜20）を選べる。長さは worm battle とは別物で、ふつうはずっと短い",
                "on the web page the starting k (1 to 20) can be chosen; the length differs from the worm battle and is usually much shorter",
            ),
        ],
        latex: r"
\begin{align*}
\alpha_0 &= \alpha, \qquad \alpha_k = \alpha_{k-1}[k] \quad (k \ge 1,\ \alpha_{k-1} > 0)\\
\beta[k] &= \beta - 1 \quad (\beta \text{ successor})
\end{align*}",
        source: (
            "wormlab の hierarchy.rs（標準の基本列は Veblen 関数についての標準的な選び方。Hardy 階層の定義と同じ列）",
            "wormlab's hierarchy.rs (the fundamental sequences are the standard choice for the Veblen function, the same ones that define the Hardy hierarchy)",
        ),
        related: &["fs", "hardy", "battle-length"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "rcbi-battle",
        symbol: "A⦃k⦄ (RC_BI)",
        name: ("RC_BI の式の battle", "Battle of RC_BI formulas"),
        lines: &[
            (
                "1 ステップ A{k}：A が後続形なら直前の式、極限形なら近似 (A)_{k+1}。⊤ と同値（零）なら終わり",
                "one step A{k}: the predecessor if A is of successor form, the approximation (A)_{k+1} if it is of limit form; stop when A is equivalent to ⊤ (zero)",
            ),
            ("battle：A⦃0⦄ = A、A⦃k⦄ = A⦃k−1⦄{k}", "the battle: A⦃0⦄ = A and A⦃k⦄ = A⦃k−1⦄{k}"),
            (
                "番号を 1 ずらすのは (A)_n が標準の基本列の α[n − 1] に当たるから（例：(⟨1⟩₂⊤)_n = ⟨1⟩₁^{n−1}⊤ は ω[n − 1] = n − 1）。こうすると A{k} は α[k] に当たる",
                "the index is shifted by one because (A)_n corresponds to α[n − 1] of the standard sequence (e.g. (⟨1⟩₂⊤)_n = ⟨1⟩₁^{n−1}⊤ is ω[n − 1] = n − 1); then A{k} corresponds to α[k]",
            ),
            (
                "<¹₁ は整礎（Thm 4.11）なので必ず ⊤ に着く",
                "since <¹₁ is well-founded (Thm 4.11), every battle reaches ⊤",
            ),
        ],
        latex: r"
\begin{align*}
A\{k\} &= \begin{cases} B & (A \text{ of successor form with predecessor } B)\\ (A)_{k+1} & (A \text{ of limit form})\end{cases}\\
A\{\!\{0\}\!\} &= A, \qquad A\{\!\{k\}\!\} = A\{\!\{k-1\}\!\}\{k\}
\end{align*}",
        source: (
            "F. Pakhomov & V. Lazar, A Reflection Calculus for Bar Induction and the Linearity of Consistency Strength Ordering（arXiv:2610.20115）§4 の基本列による。番号の付け方は wormlab の選び方",
            "Based on the fundamental sequences of F. Pakhomov & V. Lazar, A Reflection Calculus for Bar Induction and the Linearity of Consistency Strength Ordering (arXiv:2610.20115), §4; the indexing is wormlab's choice",
        ),
        related: &["rcbi-fs", "rcbi-order", "worm-battle"],
        general: &[],
        tab: Some("battle"),
        research: false,
    },
    Raw {
        key: "battle-length",
        symbol: "ℓ(A)",
        name: ("battle の長さ", "Length of a battle"),
        lines: &[
            (
                "battle の長さは、⊤（順序数なら 0）に着くまでのステップ数：ℓ(A) = min{k : A⦃k⦄ = ⊤}。順序数 α の worm battle の長さは、α の正規形の括弧語 b_α（ε₀ 未満なら標準形の worm と同じ）から始めた長さ",
                "the length of a battle is the number of steps to reach ⊤ (0 for ordinals): ℓ(A) = min{k : A⦃k⦄ = ⊤}; the worm-battle length of an ordinal α is that of its normal-form bracket word b_α (the normal-form worm below ε₀)",
            ),
            (
                "計算の仕方：短いものは実際に動かす。ε₀ 未満の worm は、閉じた形 α{m} = D(α, m + 1) で順序数だけを追い、多倍長の整数で数える",
                "how it is computed: short battles are run; below ε₀ only the ordinals are followed, using the closed form α{m} = D(α, m + 1), and counted with big integers",
            ),
            (
                "答えの形：ちょうどの値、「2^k を超える」（途中の値が上限を超えたときの下界）、「N 以上」（数えるのを打ち切ったときの下界）",
                "forms of the answer: an exact value, “more than 2^k” (a lower bound when an intermediate value exceeds the limit), or “at least N” (a lower bound when counting was stopped)",
            ),
        ],
        latex: r"
\begin{align*}
\ell(A) &= \min\{k : A\{\!\{k\}\!\} = \top\}, \qquad \ell_{\mathrm{worm}}(\alpha) = \ell(b_\alpha)
\end{align*}",
        source: (
            "wormlab の hierarchy.rs（閉じた形は bc.md §3、多倍長は bignum.rs）",
            "wormlab's hierarchy.rs (closed form: bc.md §3; big integers: bignum.rs)",
        ),
        related: &["worm-battle", "ordinal-battle", "worm-fs", "thm52"],
        general: &[],
        tab: Some("battle"),
        research: false,
    },
    Raw {
        key: "thm52",
        symbol: "G(m)",
        name: ("Thm 52 の関数 G", "The function G of Thm 52"),
        lines: &[
            (
                "括弧語の列 a₀ = ⊤、a₁ = ()、a_{n+2} = (((a_n)))、a′_m = ()a_m",
                "the bracket words a₀ = ⊤, a₁ = (), a_{n+2} = (((a_n))) and a′_m = ()a_m",
            ),
            (
                "G(m) = a′_m から始めた括弧語の battle の長さ",
                "G(m) is the length of the bracket-word battle starting from a′_m",
            ),
            (
                "m ↦ G(m) は、ATR₀ で全域性を証明できるどんな関数よりも速く増える（Thm 52）。G(2) は 2^(4.23×10^455) を超える（CLI の thm52 2 で計算）",
                "m ↦ G(m) eventually dominates every function that ATR₀ proves total (Thm 52); G(2) exceeds 2^(4.23×10^455) (computed by the CLI command thm52 2)",
            ),
        ],
        latex: r"
\begin{align*}
a_0 &= \top, \quad a_1 = (), \quad a_{n+2} = (((a_n))), \quad a'_m = ()\,a_m\\
G(m) &= \ell(a'_m)
\end{align*}",
        source: (
            "D. Fernández-Duque & E. Hermo Reyes（arXiv:2008.13445）Thm 52",
            "D. Fernández-Duque & E. Hermo Reyes (arXiv:2008.13445), Thm 52",
        ),
        related: &["bracket-battle", "battle-length"],
        general: &[],
        tab: Some("battle"),
        research: false,
    },
];

// ----------------------------------------------------------------------
// 順序数上の関数
// ----------------------------------------------------------------------

fn functions() -> Vec<Entry> {
    let mut v = vec![
        from_expr(
            "add",
            r"
\begin{align*}
\alpha + 0 &= \alpha, \qquad \alpha + (\beta + 1) = (\alpha + \beta) + 1,\\
\alpha + \lambda &= \sup_{\gamma < \lambda} (\alpha + \gamma) \quad (\lambda \text{ limit})
\end{align*}",
            &["mul", "normal"],
            &[],
        ),
        from_expr(
            "mul",
            r"
\begin{align*}
\alpha \cdot 0 &= 0, \qquad \alpha \cdot (\beta + 1) = \alpha \cdot \beta + \alpha,\\
\alpha \cdot \lambda &= \sup_{\gamma < \lambda} \alpha \cdot \gamma \quad (\lambda \text{ limit})
\end{align*}",
            &["add", "pow"],
            &[],
        ),
        from_expr(
            "pow",
            r"
\begin{align*}
\alpha^0 &= 1, \qquad \alpha^{\beta + 1} = \alpha^\beta \cdot \alpha,\\
\alpha^\lambda &= \sup_{\gamma < \lambda} \alpha^\gamma \quad (\lambda \text{ limit},\ \alpha \ge 2)
\end{align*}",
            &["mul", "phi"],
            &[],
        ),
        from_expr(
            "phi",
            r"
\begin{align*}
\varphi(0, \beta) &= \omega^\beta\\
\varphi(\alpha, \cdot) &= \text{the enumeration of } \{\xi : \varphi(\gamma, \xi) = \xi \text{ for all } \gamma < \alpha\} \quad (\alpha > 0)\\
\varphi(\alpha_1, \beta_1) < \varphi(\alpha_2, \beta_2) &\iff
\begin{cases}
\alpha_1 < \alpha_2 \text{ and } \beta_1 < \varphi(\alpha_2, \beta_2)\\
\alpha_1 = \alpha_2 \text{ and } \beta_1 < \beta_2\\
\alpha_1 > \alpha_2 \text{ and } \varphi(\alpha_1, \beta_1) < \beta_2
\end{cases}
\end{align*}",
            &["eps", "hyp", "normal", "fs"],
            &[],
        ),
        from_expr(
            "eps",
            r"
\begin{align*}
\varepsilon_\alpha &= \varphi(1, \alpha)
\end{align*}",
            &["phi"],
            &["phi"],
        ),
        from_expr(
            "hyp",
            r"
\begin{align*}
e(\xi) &= -1 + \omega^\xi\\
e^0 &= \mathrm{id}, \quad e^1 = e, \quad e^{\alpha + \beta} = e^\alpha \circ e^\beta \quad (\text{the pointwise least such family})\\
e^{\omega^\gamma}(0) &= 0, \quad e^{\omega^\gamma}(1 + \beta) = \varphi(\gamma, \beta) \quad (\gamma \ge 1)
\end{align*}",
            &["phi", "hyper-nf", "worm-o-transfinite"],
            &[],
        ),
        from_expr(
            "Omega",
            r"
\begin{align*}
\varphi(\alpha, \Omega) &= \Omega \quad (\alpha < \Omega), \qquad \varphi(\Omega, 0) = \Omega
\end{align*}",
            &["psi", "normal"],
            &[],
        ),
        from_expr(
            "psi",
            r"
\begin{align*}
C(\xi) &= \text{the least set containing } 0, 1, \Omega \text{ and closed under } +,\ \varphi,\ \psi \restriction \xi\\
\psi(\xi) &= \min\{\eta : \eta \notin C(\xi)\}
\end{align*}",
            &["Omega", "normal", "iworm"],
            &[],
        ),
        from_expr(
            "normal",
            r"
\begin{align*}
\alpha &= P_1 \cdot c_1 + \cdots + P_n \cdot c_n \quad (P_1 > \cdots > P_n,\ c_i \ge 1)\\
P &\in \{\varphi(\alpha, \beta) : \beta < \varphi(\alpha, \beta)\} \cup \{\Omega\} \cup \{\psi(\xi) : \xi \in C(\xi)\}
\end{align*}",
            &["phi", "psi", "hyper-nf"],
            &[],
        ),
    ];
    v.extend(FUNCTIONS.iter().map(Raw::build));
    v
}

const FUNCTIONS: &[Raw] = &[
    Raw {
        key: "cnf",
        symbol: "CNF",
        name: ("Cantor 標準形", "Cantor normal form"),
        lines: &[
            (
                "0 より大きいどの順序数 α も、α = ω^{α₁}·c₁ + … + ω^{α_k}·c_k（α₁ > … > α_k、c_i は 1 以上の自然数）の形にただ一通りに書ける。0 は空の和、自然数 n は ω^0·n",
                "every ordinal α > 0 can be written uniquely as α = ω^{α₁}·c₁ + … + ω^{α_k}·c_k (α₁ > … > α_k, c_i ≥ 1 natural numbers); 0 is the empty sum and a natural number n is ω^0·n",
            ),
            (
                "比較は辞書式：左の項から順に見て、最初に違う所で指数が大きい方（指数が同じなら係数が大きい方）が大きい",
                "comparison is lexicographic: reading terms from the left, at the first difference the larger exponent (or, for equal exponents, the larger coefficient) wins",
            ),
            (
                "α < ε₀ なら指数 α_i は α より小さいので、指数も同じ形で書き切れる。ε₀ は ω^ξ = ξ となる最初の数で、ここで指数が小さくならなくなる",
                "for α < ε₀ the exponents α_i are smaller than α, so they too can be written in this form; ε₀, the least ξ with ω^ξ = ξ, is where exponents stop getting smaller",
            ),
            (
                "Veblen 表記の標準形（NF）は、主項を ω^β = φ(0, β) から φ(α, β)・Ω・ψ(ξ) に広げたもの",
                "the Veblen normal form (NF) extends the principal terms from ω^β = φ(0, β) to φ(α, β), Ω and ψ(ξ)",
            ),
        ],
        latex: r"
\begin{align*}
\alpha &= \omega^{\alpha_1} \cdot c_1 + \cdots + \omega^{\alpha_k} \cdot c_k \quad (\alpha_1 > \cdots > \alpha_k,\ c_i \ge 1)\\
\alpha &< \varepsilon_0 \Rightarrow \alpha_1 < \alpha, \qquad \varepsilon_0 = \min\{\xi : \omega^\xi = \xi\}
\end{align*}",
        source: (
            "G. Cantor, Beiträge zur Begründung der transfiniten Mengenlehre II, Math. Ann. 49（1897）。教科書は例えば W. Pohlers, Proof Theory（Springer 2009）",
            "G. Cantor, Beiträge zur Begründung der transfiniten Mengenlehre II, Math. Ann. 49 (1897); see e.g. W. Pohlers, Proof Theory (Springer 2009)",
        ),
        related: &["add", "mul", "pow", "cnf-fs", "worm-o"],
        general: &["normal"],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "hyper-nf",
        symbol: "ξ = e^α(β)",
        name: ("超指数関数による標準形", "Hyperexponential normal form"),
        lines: &[
            (
                "0 より大きい順序数 ξ は、β が 1 か加法的に分解できる数（2 つの小さい数の和）であるような ξ = e^α(β) の形に、ただ一通りに書ける（Prop 5.14）。α を ξ の分解できない度合いと読む",
                "every ordinal ξ > 0 can be written uniquely as ξ = e^α(β) with β equal to 1 or additively decomposable (a sum of two smaller ordinals) (Prop 5.14); α measures how indecomposable ξ is",
            ),
            (
                "α と β も同じ形に書き、0・1・+・e^α(β) だけで書き切る。Prop 5.15：e(1 + β) = ω^{1+β}、e^{ω^{1+α}}(1 + β) = φ(1 + α, β)",
                "α and β are written the same way, so everything is expressed with 0, 1, + and e^α(β); Prop 5.15: e(1 + β) = ω^{1+β} and e^{ω^{1+α}}(1 + β) = φ(1 + α, β)",
            ),
            (
                "強臨界数（Ω と ψ(ξ)）は s = e^s(1) となって小さく分けられないので、原子として書く（ψ の中も同じ形）",
                "strongly critical ordinals (Ω and ψ(ξ)) satisfy s = e^s(1) and cannot be split further, so they are atoms (with the same form inside ψ)",
            ),
            (
                "順序数電卓のタブの「表示する標準形」で「超指数＋ψ」を選ぶと、この形で表示する",
                "choosing “hyperexp + ψ” under “Normal form to display” on the ordinal tab shows ordinals in this form",
            ),
        ],
        latex: r"
\begin{align*}
\xi &= e^\alpha(\beta), \quad \beta = 1 \text{ or } \beta \text{ additively decomposable}\quad(\xi > 0, \text{ unique})\\
e(1 + \beta) &= \omega^{1+\beta}, \qquad e^{\omega^{1+\alpha}}(1 + \beta) = \varphi(1 + \alpha, \beta)
\end{align*}",
        source: (
            "D. Fernández-Duque, Worms and spiders（arXiv:1605.08867）Prop 5.14（Aguilera & Fernández-Duque による）・Prop 5.15",
            "D. Fernández-Duque, Worms and spiders (arXiv:1605.08867), Prop 5.14 (due to Aguilera & Fernández-Duque) and Prop 5.15",
        ),
        related: &["hyp", "normal", "psi"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "hardy",
        symbol: "H_α(n)",
        name: ("Hardy 階層", "Hardy hierarchy"),
        lines: &[
            (
                "H₀(n) = n、H_{α+1}(n) = H_α(n + 1)、H_λ(n) = H_{λ[n]}(n)（λ は極限、λ[n] は標準の基本列）",
                "H₀(n) = n, H_{α+1}(n) = H_α(n + 1), and H_λ(n) = H_{λ[n]}(n) for a limit λ (λ[n] the standard fundamental sequence)",
            ),
            (
                "値はすぐに大きくなるので、wormlab は多倍長の整数で計算し、上限を超えたら下界を返す",
                "values grow very fast, so wormlab computes with big integers and returns a lower bound when a limit is exceeded",
            ),
        ],
        latex: r"
\begin{align*}
H_0(n) &= n, \qquad H_{\alpha+1}(n) = H_\alpha(n+1), \qquad H_\lambda(n) = H_{\lambda[n]}(n)
\end{align*}",
        source: (
            "G. H. Hardy（1904）に由来する標準的な定義（例：Buchholz & Wainer, Provably computable functions and the fast growing hierarchy, 1987）",
            "The standard definition going back to G. H. Hardy (1904) (e.g. Buchholz & Wainer, Provably computable functions and the fast growing hierarchy, 1987)",
        ),
        related: &["fs", "fgh", "ordinal-battle"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "fgh",
        symbol: "f_α(n)",
        name: ("急増加関数", "Fast-growing hierarchy"),
        lines: &[
            (
                "f₀(n) = n + 1、f_{α+1}(n) = f_αⁿ(n)（n 回合成）、f_λ(n) = f_{λ[n]}(n)",
                "f₀(n) = n + 1, f_{α+1}(n) = f_αⁿ(n) (n-fold composition), and f_λ(n) = f_{λ[n]}(n)",
            ),
            (
                "ε₀ 未満では f_α = H_{ω^α}。wormlab はこの関係で H から計算する（テストで直接の定義と突き合わせている）",
                "below ε₀, f_α = H_{ω^α}; wormlab computes f through H (the tests compare it with the direct definition)",
            ),
        ],
        latex: r"
\begin{align*}
f_0(n) &= n + 1, \qquad f_{\alpha+1}(n) = f_\alpha^{\,n}(n), \qquad f_\lambda(n) = f_{\lambda[n]}(n)\\
f_\alpha &= H_{\omega^\alpha} \quad (\alpha < \varepsilon_0)
\end{align*}",
        source: (
            "Löb & Wainer（1970）の急増加階層。例：Buchholz & Wainer（1987）",
            "The fast-growing hierarchy of Löb & Wainer (1970); see e.g. Buchholz & Wainer (1987)",
        ),
        related: &["hardy", "fs"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
];

// ----------------------------------------------------------------------
// 基本列（特殊な場合 → 一般の場合の順）
// ----------------------------------------------------------------------

const FUNDAMENTAL: &[Raw] = &[
    Raw {
        key: "cnf-fs",
        symbol: "α[n] (α < ε₀)",
        name: ("Cantor 標準形の基本列", "Fundamental sequences on Cantor normal forms"),
        lines: &[
            (
                "ε₀ 未満の順序数を Cantor 標準形で書いたときの基本列。最後の項だけを下げる",
                "the fundamental sequences of ordinals below ε₀ written in Cantor normal form; only the last term is lowered",
            ),
            (
                "0 には基本列がない。後続順序数では (β + 1)[n] = β",
                "0 has no fundamental sequence; for a successor, (β + 1)[n] = β",
            ),
            (
                "最後の項が ω^{γ+1} なら (β + ω^{γ+1})[n] = β + ω^γ·n。最後の項が ω^λ（λ は極限）なら (β + ω^λ)[n] = β + ω^{λ[n]}。係数のある項 ω^γ·c は ω^γ を c 個並べたものとみる",
                "if the last term is ω^{γ+1}, (β + ω^{γ+1})[n] = β + ω^γ·n; if it is ω^λ with λ a limit, (β + ω^λ)[n] = β + ω^{λ[n]}; a term ω^γ·c counts as c copies of ω^γ",
            ),
            (
                "上限の ε₀ では ε₀[0] = 0、ε₀[n + 1] = ω^{ε₀[n]}（ω の塔）",
                "at the limit ε₀: ε₀[0] = 0 and ε₀[n + 1] = ω^{ε₀[n]} (towers of ω)",
            ),
            (
                "一般の場合（Veblen 表記の標準の基本列）で、主項が ω^β = φ(0, β) だけのときの形。Hardy 階層・急増加関数の定義に使う",
                "this is the general case (standard fundamental sequences for Veblen notation) when every principal term is ω^β = φ(0, β); it defines the Hardy and fast-growing hierarchies",
            ),
        ],
        latex: r"
\begin{align*}
(\beta + 1)[n] &= \beta, \qquad (\beta + \omega^{\gamma+1})[n] = \beta + \omega^\gamma \cdot n\\
(\beta + \omega^\lambda)[n] &= \beta + \omega^{\lambda[n]} \quad (\lambda \text{ limit})\\
\varepsilon_0[0] &= 0, \qquad \varepsilon_0[n+1] = \omega^{\varepsilon_0[n]}
\end{align*}",
        source: (
            "Hardy 階層・急増加関数でふつうに使う選び方（例：Buchholz & Wainer, Provably computable functions and the fast growing hierarchy, 1987。文献によって ·n と ·(n + 1) の違いがある）。wormlab では veblen.rs の一般の基本列で計算する",
            "The usual choice for the Hardy and fast-growing hierarchies (e.g. Buchholz & Wainer, Provably computable functions and the fast growing hierarchy, 1987; some authors use ·(n + 1) instead of ·n); wormlab computes it with the general sequences of veblen.rs",
        ),
        related: &["cnf", "hardy", "ordinal-battle", "nat-worm-fs"],
        general: &["fs"],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "fs",
        symbol: "α[n]",
        name: ("標準の基本列", "Standard fundamental sequences"),
        lines: &[
            (
                "0 には基本列がない。後続順序数 α + 1 では (α + 1)[n] = α",
                "0 has no fundamental sequence; for a successor, (α + 1)[n] = α",
            ),
            (
                "極限順序数 α = β + P（P は最後の主項）では α[n] = β + P[n]。主項は",
                "for a limit α = β + P (P the last principal term), α[n] = β + P[n], where for principal terms",
            ),
            (
                "ω^{b+1}[n] = ω^b·n、ω^λ[n] = ω^{λ[n]}（λ は極限）",
                "ω^{b+1}[n] = ω^b·n and ω^λ[n] = ω^{λ[n]} (λ a limit)",
            ),
            (
                "a ≥ 1 では φ(a, λ)[n] = φ(a, λ[n])（λ は極限）、φ(a + 1, 0)[n] = φ(a, ·)ⁿ(0)、φ(a + 1, b + 1)[n] = φ(a, ·)ⁿ(φ(a + 1, b) + 1)（n 回合成）",
                "for a ≥ 1: φ(a, λ)[n] = φ(a, λ[n]) (λ a limit), φ(a + 1, 0)[n] = φ(a, ·)ⁿ(0) and φ(a + 1, b + 1)[n] = φ(a, ·)ⁿ(φ(a + 1, b) + 1) (n-fold composition)",
            ),
            (
                "φ(λ, 0)[n] = φ(λ[n], 0)、φ(λ, b + 1)[n] = φ(λ[n], φ(λ, b) + 1)（λ は極限）",
                "φ(λ, 0)[n] = φ(λ[n], 0) and φ(λ, b + 1)[n] = φ(λ[n], φ(λ, b) + 1) (λ a limit)",
            ),
            (
                "どの n でも α[n] < α で、極限なら n について増加し、上限は α。Ω・ψ を含む数（Γ₀ 以上）にはまだ定義していない",
                "α[n] < α for every n, and for a limit it increases in n with supremum α; numbers with Ω or ψ (from Γ₀ on) have no fundamental sequence here yet",
            ),
        ],
        latex: r"
\begin{align*}
(\alpha + 1)[n] &= \alpha, \qquad (\beta + P)[n] = \beta + P[n]\\
\omega^{b+1}[n] &= \omega^b \cdot n, \qquad \omega^\lambda[n] = \omega^{\lambda[n]}\\
\varphi(a, \lambda)[n] &= \varphi(a, \lambda[n]) \quad (a \ge 1)\\
\varphi(a+1, 0)[n] &= \varphi(a, \cdot)^n(0), \qquad \varphi(a+1, b+1)[n] = \varphi(a, \cdot)^n(\varphi(a+1, b) + 1)\\
\varphi(\lambda, 0)[n] &= \varphi(\lambda[n], 0), \qquad \varphi(\lambda, b+1)[n] = \varphi(\lambda[n], \varphi(\lambda, b) + 1)
\end{align*}",
        source: (
            "wormlab の veblen.rs（Veblen 関数についての標準的な選び方。hierarchy.md）",
            "wormlab's veblen.rs (the standard choice for the Veblen function; hierarchy.md)",
        ),
        related: &["worm-fs", "hardy", "fgh", "ordinal-battle"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "nat-worm-fs",
        symbol: "A{n}",
        name: ("worm の基本列（文字が自然数）", "Fundamental sequence of a worm (natural-number letters)"),
        lines: &[
            (
                "worm A = n₁ n₂ … n_k は式 ⟨n₁⟩⟨n₂⟩…⟨n_k⟩⊤（文字は自然数、左端が外側、空の worm は ⊤）。⊤ には基本列がない",
                "a worm A = n₁ n₂ … n_k is the formula ⟨n₁⟩⟨n₂⟩…⟨n_k⟩⊤ (natural-number letters, the leftmost is outermost, the empty worm is ⊤); ⊤ has no fundamental sequence",
            ),
            ("A = 0B なら A{n} = B", "if A = 0B, then A{n} = B"),
            (
                "先頭の文字 h が 1 以上なら、h 未満の文字が最初に現れる位置で A = VU と分ける（V の文字はすべて h 以上。h 未満の文字がなければ U = ⊤）。V の先頭の文字を h − 1 にした V′ を n + 1 回並べて A{n} = V′V′…V′U",
                "if the first letter h is at least 1, split A = VU at the first letter below h (all letters of V are ≥ h; U = ⊤ if there is none), let V′ be V with its first letter replaced by h − 1, and put A{n} = V′V′…V′U with n + 1 copies of V′",
            ),
            (
                "o(A{n}) < o(A)。A が標準形なら o(A{n}) = D(o(A), n + 1)（worm が作る列 α{n} の閉じた形）",
                "o(A{n}) < o(A); if A is in normal form, o(A{n}) = D(o(A), n + 1) (the closed form of the sequence α{n} given by worms)",
            ),
            (
                "括弧語の基本列で、文字 m を ()^m（() を m 個）と読んだ場合と同じ。Beklemishev の定義を、wormlab の「左端が外側」の書き方に合わせて左右を反転したもの",
                "this is the bracket-word sequence with each letter m read as ()^m (m copies of ()); it is Beklemishev's definition mirrored to wormlab's convention that the leftmost letter is outermost",
            ),
        ],
        latex: r"
\begin{align*}
(0B)\{n\} &= B\\
(VU)\{n\} &= \underbrace{V'\cdots V'}_{n+1}\,U
  \quad (V = hV_0,\ h \ge 1,\ V \ge h,\ U = \top \text{ or } U = gU_0,\ g < h,\ V' = (h-1)V_0)\\
o(A\{n\}) &< o(A), \qquad o(A\{n\}) = D(o(A), n+1) \quad (A \text{ in normal form})
\end{align*}",
        source: (
            "L. D. Beklemishev, The worm principle, Logic Colloquium '02, Lecture Notes in Logic 27（2006）。閉じた形 D は wormlab の hierarchy.rs（bc.md §3）",
            "L. D. Beklemishev, The worm principle, Logic Colloquium '02, Lecture Notes in Logic 27 (2006); the closed form D is from wormlab's hierarchy.rs (bc.md §3)",
        ),
        related: &["worm-battle", "worm-o", "worm-fs", "cnf-fs"],
        general: &["bracket-fs"],
        tab: Some("battle"),
        research: false,
    },
    Raw {
        key: "bracket-fs",
        symbol: "a{n}",
        name: ("括弧語の基本列", "Fundamental sequence of a bracket word"),
        lines: &[
            (
                "括弧語は ⊤ と、括弧語 a, b から作る (a)b。最後の ⊤ は省いて (a₁)(a₂)…(a_k) と書き、各 a_i を文字と呼ぶ（() = (⊤)⊤）。文字どうしは o* で比べる",
                "bracket words are ⊤ and (a)b for bracket words a, b; the final ⊤ is dropped, so we write (a₁)(a₂)…(a_k) and call each a_i a letter (() = (⊤)⊤); letters are compared by o*",
            ),
            (
                "⊤ には基本列がない。a₁ = ⊤ なら a{n} = (a₂)…(a_k)",
                "⊤ has no fundamental sequence; if a₁ = ⊤, then a{n} = (a₂)…(a_k)",
            ),
            (
                "a₁ ≠ ⊤ なら、a₁ より小さい文字が最初に現れる位置を ℓ（なければ k + 1）として、b = (a₁{n})(a₂)…(a_{ℓ−1})、c = (a_ℓ)…(a_k) とおき a{n} = b^{n+1}c。a₁{n} は文字 a₁ を括弧語とみた基本列（入れ子が 1 段浅い再帰）",
                "if a₁ ≠ ⊤, let ℓ be the position of the first letter smaller than a₁, or k + 1 if there is none, put b = (a₁{n})(a₂)…(a_{ℓ−1}) and c = (a_ℓ)…(a_k), and let a{n} = b^{n+1}c; here a₁{n} is the sequence of the letter a₁ itself (a recursion one level shallower)",
            ),
            (
                "o*(a{n}) < o*(a)（Prop 41）。文字がすべて ()^m の形なら、worm の基本列 A{n} と同じ",
                "o*(a{n}) < o*(a) (Prop 41); when every letter has the form ()^m, this is the worm sequence A{n}",
            ),
        ],
        latex: r"
\begin{align*}
\bigl((\top)(a_2)\cdots(a_k)\bigr)\{n\} &= (a_2)\cdots(a_k)\\
a\{n\} &= b^{\,n+1}c, \quad b = (a_1\{n\})(a_2)\cdots(a_{\ell-1}),\ c = (a_\ell)\cdots(a_k),\\
&\qquad \ell = \min(\{i > 1 : o^*(a_i) < o^*(a_1)\} \cup \{k+1\})\\
o^*(a\{n\}) &< o^*(a)
\end{align*}",
        source: (
            "D. Fernández-Duque & E. Hermo Reyes, Deducibility and Independence in Beklemishev's Autonomous Provability Calculus（arXiv:2008.13445）§8・Prop 41",
            "D. Fernández-Duque & E. Hermo Reyes, Deducibility and Independence in Beklemishev's Autonomous Provability Calculus (arXiv:2008.13445), §8 and Prop 41",
        ),
        related: &["bracket", "bracket-battle", "worm-fs"],
        general: &[],
        tab: Some("battle"),
        research: false,
    },
    Raw {
        key: "worm-fs",
        symbol: "α{n}",
        name: ("worm が作る列", "The sequence given by worms"),
        lines: &[
            (
                "α{n} = o*(a{n})：α の正規形の括弧語 a に、括弧語の基本列を 1 回使ったものの順序数。ε₀ 未満では、標準形の worm A の基本列の順序数 o(A{n}) と同じ",
                "α{n} = o*(a{n}): the ordinal of the normal-form bracket word a of α after one application of the bracket-word fundamental sequence; below ε₀ it is o(A{n}) for the normal-form worm A of α",
            ),
            (
                "標準の基本列とは少しずれる（例：ω²{1} = ω·2 + 1、ω²[1] = ω）",
                "it differs slightly from the standard sequence (e.g. ω²{1} = ω·2 + 1 while ω²[1] = ω)",
            ),
            (
                "ε₀ 未満では閉じた形 α{m} = D(α, m + 1)。D は α[n] の「いちばん内側で +1 する」版：α = R + ω^{β+1} なら D(α, n) = R + ω^β·n + 1（α = ω なら n）、α = R + ω^λ（λ は極限）なら D(α, n) = R + ω^{D(λ, n)}",
                "below ε₀ there is a closed form α{m} = D(α, m + 1), where D is α[n] with “+1 at the innermost place”: D(R + ω^{β+1}, n) = R + ω^β·n + 1 (but D(ω, n) = n) and D(R + ω^λ, n) = R + ω^{D(λ, n)} for a limit λ",
            ),
        ],
        latex: r"
\begin{align*}
\alpha\{n\} &= o^*(a\{n\}) \quad (a \text{ the normal-form bracket word of } \alpha)\\
\alpha\{m\} &= D(\alpha, m+1) \quad (\alpha < \varepsilon_0)\\
D(R + \omega^{\beta+1}, n) &= R + \omega^\beta \cdot n + 1, \qquad D(\omega, n) = n\\
D(R + \omega^\lambda, n) &= R + \omega^{D(\lambda, n)} \quad (\lambda \text{ limit})
\end{align*}",
        source: (
            "wormlab の hierarchy.rs（worm_fundamental・worm_fs_closed、bc.md §3）",
            "wormlab's hierarchy.rs (worm_fundamental, worm_fs_closed; bc.md §3)",
        ),
        related: &["fs", "bracket-fs", "nat-worm-fs", "battle-length"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "rcbi-fs",
        symbol: "(A)_n",
        name: ("RC_BI の式の形と近似", "Forms and approximations of RC_BI formulas"),
        lines: &[
            (
                "∧ をほどいた成分（⊤ を除く）を見て：成分がなければ零（A ≡ ⊤）。成分がすべて ⟨1⟩₁B の形なら後続形で、A = ⟨1⟩₁B₁ ∧ … ∧ ⟨1⟩₁B_k の直前は B_i のうち最大のもの。↓B か ⟨i⟩_α B（α ≥ 2）の成分があれば極限形",
                "look at the conjuncts (other than ⊤): with none, A is zero (A ≡ ⊤); if all have the form ⟨1⟩₁B, A is of successor form and the predecessor of ⟨1⟩₁B₁ ∧ … ∧ ⟨1⟩₁B_k is the largest B_i; if some conjunct is ↓B or ⟨i⟩_α B (α ≥ 2), A is of limit form",
            ),
            (
                "A = ⟨i⟩_α A′（α ≥ 2）：(A)₁ = A′、(A)_{n+1} = ⟨i⟩_{α−1}(A′ ∧ (A)_n)（α > i）または ⟨1⟩₁(A′ ∧ ↓(A)_n)（α = i = 2）",
                "A = ⟨i⟩_α A′ (α ≥ 2): (A)₁ = A′ and (A)_{n+1} = ⟨i⟩_{α−1}(A′ ∧ (A)_n) (α > i) or ⟨1⟩₁(A′ ∧ ↓(A)_n) (α = i = 2)",
            ),
            (
                "A = ↓C：C が極限形なら ⟨1⟩_n↓(C)_n。そうでなければ C = ⟨1⟩₁E₁ ∧ … ∧ ⟨1⟩₁E_k として ⟨1⟩_n↓E₁ ∧ … ∧ ⟨1⟩_n↓E_k（k = 0 なら ⟨1⟩_n⊤）",
                "A = ↓C: ⟨1⟩_n↓(C)_n if C is of limit form; otherwise, with C = ⟨1⟩₁E₁ ∧ … ∧ ⟨1⟩₁E_k, it is ⟨1⟩_n↓E₁ ∧ … ∧ ⟨1⟩_n↓E_k (⟨1⟩_n⊤ if k = 0)",
            ),
            (
                "成分が 2 つ以上：↓ の成分があればそれらを近似し、◇ の成分はそのまま。なければ最大の添字 α₁ の成分 C₁, …, C_m と残り C⁰ に分け、巡回シフト A⟲ を使って (A)₁ = C⁰、(A)_{n+1} = ⟨i₁⟩_{α₁−1}(C₁′ ∧ (A⟲)_n)（α₁ > i₁）または ⟨1⟩₁(C₁′ ∧ ↓(A⟲)_n)",
                "two or more conjuncts: approximate the ↓ conjuncts if there are any, keeping the ◇ conjuncts; otherwise split into the conjuncts C₁, …, C_m with the largest index α₁ and the rest C⁰, and with the cyclic shift A⟲ put (A)₁ = C⁰ and (A)_{n+1} = ⟨i₁⟩_{α₁−1}(C₁′ ∧ (A⟲)_n) (α₁ > i₁) or ⟨1⟩₁(C₁′ ∧ ↓(A⟲)_n)",
            ),
            (
                "(A)_n <¹₁ A（Lemma 4.7）で、A より下のどの式もある (A)_n 以下（Lemma 4.10 と線形性）",
                "(A)_n <¹₁ A (Lemma 4.7), and every formula below A is below some (A)_n (Lemma 4.10 and linearity)",
            ),
        ],
        latex: r"
\begin{align*}
(\langle i \rangle_\alpha A')_1 &= A', \qquad
(\langle i \rangle_\alpha A')_{n+1} = \begin{cases} \langle i \rangle_{\alpha-1}(A' \wedge (A)_n) & (\alpha > i)\\ \langle 1 \rangle_1(A' \wedge {\downarrow}(A)_n) & (\alpha = i = 2)\end{cases}\\
({\downarrow}C)_n &= \langle 1 \rangle_n {\downarrow}(C)_n \quad (C \text{ of limit form})\\
({\downarrow}(\langle 1 \rangle_1 E_1 \wedge \cdots \wedge \langle 1 \rangle_1 E_k))_n &= \langle 1 \rangle_n {\downarrow}E_1 \wedge \cdots \wedge \langle 1 \rangle_n {\downarrow}E_k
\end{align*}",
        source: (
            "F. Pakhomov & V. Lazar（arXiv:2610.20115）Def 4.5・Def 4.6・Lemma 4.7・Lemma 4.10",
            "F. Pakhomov & V. Lazar (arXiv:2610.20115), Def 4.5, Def 4.6, Lemma 4.7 and Lemma 4.10",
        ),
        related: &["rcbi-order", "rcbi-battle"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
];

// ----------------------------------------------------------------------
// 表記と順序数の対応
// ----------------------------------------------------------------------

const NOTATIONS: &[Raw] = &[
    Raw {
        key: "worm",
        symbol: "A <_n B",
        name: ("worm と順序 <_n", "Worms and the orders <_n"),
        lines: &[
            (
                "worm は ⊤ と ⟨α⟩A（A は worm）の形の式。文字 α は自然数か順序数",
                "worms are ⊤ and the formulas ⟨α⟩A with A a worm; the letters α are natural numbers or ordinals",
            ),
            (
                "A <_n B :⟺ GLP ⊢ B → ⟨n⟩A（RC では B ⊢ ⟨n⟩A）。A ≡ B :⟺ どちらの向きにも導ける",
                "A <_n B :⟺ GLP ⊢ B → ⟨n⟩A (in RC: B ⊢ ⟨n⟩A); A ≡ B :⟺ each proves the other",
            ),
            (
                "<₀ は worm の同値類の上の整列順序で、文字が自然数なら順序型は ε₀。順序数 o(A) はこの順序での A の位置",
                "<₀ well-orders the equivalence classes of worms, with order type ε₀ for natural-number letters; o(A) is the position of A in this order",
            ),
            (
                "wormlab は <₀ を 3 通りに独立に計算する：o(A) の比較、RC の判定、head/body の再帰（Worms and spiders Thm 3.17）",
                "wormlab computes <₀ in three independent ways: comparing o(A), the RC decision procedure, and the head/body recursion (Worms and spiders, Thm 3.17)",
            ),
        ],
        latex: r"
\begin{align*}
A <_n B &\iff \mathrm{GLP} \vdash B \to \langle n \rangle A \iff \mathrm{RC} \vdash B \vdash \langle n \rangle A\\
A \equiv B &\iff A \vdash B \text{ and } B \vdash A
\end{align*}",
        source: (
            "L. D. Beklemishev, Provability algebras and proof-theoretic ordinals I, APAL 128（2004）。head/body は D. Fernández-Duque, Worms and spiders（arXiv:1605.08867）Thm 3.17",
            "L. D. Beklemishev, Provability algebras and proof-theoretic ordinals I, APAL 128 (2004); head/body: D. Fernández-Duque, Worms and spiders (arXiv:1605.08867), Thm 3.17",
        ),
        related: &["worm-o", "bnf", "rc-frame", "worm-battle"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "worm-o",
        symbol: "o(A)",
        name: ("worm の順序数（文字が自然数）", "Ordinal of a worm (natural-number letters)"),
        lines: &[
            (
                "A を文字 0 で区切って A = A₁ 0 A₂ 0 … 0 A_k（各 A_i は 0 を含まない、空でもよい）とし、A↓ を全文字から 1 を引いた worm とすると 1 + o(A) = ω^{o(A_k↓)} + … + ω^{o(A₁↓)}",
                "write A = A₁ 0 A₂ 0 … 0 A_k (no A_i contains 0; they may be empty) and let A↓ subtract 1 from every letter; then 1 + o(A) = ω^{o(A_k↓)} + … + ω^{o(A₁↓)}",
            ),
            ("o(⊤) = 0。和は内側（右）の成分から順に足す", "o(⊤) = 0; the sum is taken from the innermost (rightmost) component"),
            (
                "o は (worm/≡, <₀) から ε₀ への順序同型。特に A ≡ B ⟺ o(A) = o(B)",
                "o is an order isomorphism from (worms/≡, <₀) onto ε₀; in particular A ≡ B iff o(A) = o(B)",
            ),
        ],
        latex: r"
\begin{align*}
o(\top) &= 0\\
1 + o(A_1\, 0\, A_2\, 0 \cdots 0\, A_k) &= \omega^{o(A_k{\downarrow})} + \cdots + \omega^{o(A_1{\downarrow})}
\end{align*}",
        source: (
            "L. D. Beklemishev, Provability algebras and proof-theoretic ordinals I, APAL 128（2004）",
            "L. D. Beklemishev, Provability algebras and proof-theoretic ordinals I, APAL 128 (2004)",
        ),
        related: &["worm", "worm-o-transfinite", "worm-inverse", "pi-ordinal"],
        general: &["worm-o-transfinite"],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "worm-o-transfinite",
        symbol: "o(⟨α⟩A)",
        name: ("worm の順序数（文字が順序数）", "Ordinal of a worm (ordinal letters)"),
        lines: &[
            ("o(⊤) = 0", "o(⊤) = 0"),
            (
                "μ = min A > 0 なら o(A) = e^μ(o(μ↓A))（μ↓ は各文字 α を −μ + α に）",
                "if μ = min A > 0, then o(A) = e^μ(o(μ↓A)) (μ↓ replaces each letter α by −μ + α)",
            ),
            (
                "A = H 0 B（H は最初の 0 の手前）なら o(A) = o(B) + 1 + o(H)",
                "if A = H 0 B (H before the first 0), then o(A) = o(B) + 1 + o(H)",
            ),
            (
                "e^μ は超指数関数。文字がすべて自然数なら、文字が自然数の o と一致する",
                "e^μ is the hyperexponential; for natural-number letters this agrees with the formula for finite worms",
            ),
        ],
        latex: r"
\begin{align*}
o(\top) &= 0\\
o(A) &= e^\mu\bigl(o(\mu{\downarrow}A)\bigr) \quad (\mu = \min A > 0)\\
o(H\,0\,B) &= o(B) + 1 + o(H) \quad (H \text{ has no } 0)
\end{align*}",
        source: (
            "D. Fernández-Duque & J. J. Joosten, Well-orders in the transfinite Japaridze algebra I（arXiv:1212.3468）Thm 5.8、II（arXiv:1204.4743）Thm 4.9・Lemma 4.10",
            "D. Fernández-Duque & J. J. Joosten, Well-orders in the transfinite Japaridze algebra I (arXiv:1212.3468), Thm 5.8, and II (arXiv:1204.4743), Thm 4.9 and Lemma 4.10",
        ),
        related: &["worm-o", "hyp", "worm-inverse", "bracket"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "worm-inverse",
        symbol: "inv(α)",
        name: ("逆写像（標準形の worm）", "Inverse map (normal-form worm)"),
        lines: &[
            (
                "1 + α = ω^{β₁} + … + ω^{β_k}（β₁ ≥ … ≥ β_k、重複を許す）と展開する",
                "expand 1 + α = ω^{β₁} + … + ω^{β_k} (β₁ ≥ … ≥ β_k, with repetitions)",
            ),
            (
                "k ≥ 2 なら inv(α) = (1↑inv(β_k)) 0 inv(−1 + ω^{β₁} + … + ω^{β_{k−1}})（ξ↑A は各文字の左に ξ を足す）",
                "if k ≥ 2, inv(α) = (1↑inv(β_k)) 0 inv(−1 + ω^{β₁} + … + ω^{β_{k−1}}) (ξ↑A adds ξ on the left of every letter)",
            ),
            (
                "k = 1 で β < ω^β なら inv(α) = 1↑inv(β)。ω^β = β = φ(a, b)（a ≥ 1）なら inv(α) = ω^a↑inv(1 + b)。強臨界数 s なら ⟨s⟩⊤",
                "if k = 1 and β < ω^β, inv(α) = 1↑inv(β); if ω^β = β = φ(a, b) (a ≥ 1), inv(α) = ω^a↑inv(1 + b); for a strongly critical s it is ⟨s⟩⊤",
            ),
            (
                "o(inv(α)) = α で、inv(α) は Beklemishev 標準形。これを α の標準形の worm と呼ぶ",
                "o(inv(α)) = α, and inv(α) is in Beklemishev normal form; it is called the normal-form worm of α",
            ),
        ],
        latex: r"
\begin{align*}
1 + \alpha &= \omega^{\beta_1} + \cdots + \omega^{\beta_k} \quad (\beta_1 \ge \cdots \ge \beta_k)\\
\mathrm{inv}(\alpha) &= (1{\uparrow}\mathrm{inv}(\beta_k))\ 0\ \mathrm{inv}(-1 + \omega^{\beta_1} + \cdots + \omega^{\beta_{k-1}}) \quad (k \ge 2)\\
\mathrm{inv}(\alpha) &= 1{\uparrow}\mathrm{inv}(\beta) \quad (k = 1,\ \beta < \omega^\beta)\\
\mathrm{inv}(\varphi(a, b)) &= \omega^a{\uparrow}\mathrm{inv}(1 + b) \quad (a \ge 1)
\end{align*}",
        source: (
            "wormlab の transfinite.rs（Fernández-Duque & Joosten の計算規則を逆にたどる構成。出力が標準形であることはテストで確認）",
            "wormlab's transfinite.rs (a construction inverting the rules of Fernández-Duque & Joosten; the tests check that the output is in normal form)",
        ),
        related: &["worm-o", "worm-o-transfinite", "bnf", "bracket"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "bnf",
        symbol: "BNF",
        name: ("Beklemishev 標準形", "Beklemishev normal form"),
        lines: &[
            (
                "α = min A のすべての出現で A = A_k α … α A₀ と区切る（各 A_i の文字は α より大きい）",
                "split A = A_k α … α A₀ at every occurrence of α = min A (each A_i has letters above α)",
            ),
            (
                "A が標準形 :⟺ 各 A_i が標準形で、A_{i+1} ⊴ A_i（左の成分ほど小さいか等しい。⊴ は ≤₀）",
                "A is in normal form :⟺ every A_i is in normal form and A_{i+1} ⊴ A_i (components weakly increase to the right; ⊴ is ≤₀)",
            ),
            (
                "どの worm も、ただ 1 つの標準形の worm と同値（Thm 11）",
                "every worm is equivalent to exactly one worm in normal form (Thm 11)",
            ),
        ],
        latex: r"
\begin{align*}
A &= A_k\,\alpha\,A_{k-1}\,\alpha \cdots \alpha\,A_0 \quad (\alpha = \min A)\\
A \in \mathrm{BNF} &\iff A_i \in \mathrm{BNF} \text{ and } A_{i+1} \trianglelefteq A_i \text{ for all } i
\end{align*}",
        source: (
            "D. Fernández-Duque & E. Hermo Reyes（arXiv:2008.13445）Def 10・Thm 11",
            "D. Fernández-Duque & E. Hermo Reyes (arXiv:2008.13445), Def 10 and Thm 11",
        ),
        related: &["worm-inverse", "worm", "bracket-nf"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "pi-ordinal",
        symbol: "Ω_ξ(A)",
        name: ("Π 順序数（ξ-順序型）", "Π ordinals (ξ-order types)"),
        lines: &[
            (
                "h_ξ(A) を、文字がすべて ξ 以上の A の最長の先頭部分とし、Ω_ξ(A) = o(ξ↓h_ξ(A))",
                "let h_ξ(A) be the longest initial segment of A whose letters are all ≥ ξ, and Ω_ξ(A) = o(ξ↓h_ξ(A))",
            ),
            (
                "Ω₀ = o、Ω_{n+1}(A) = ℓ(Ω_n(A))（ℓ は Cantor 標準形の最後の指数）",
                "Ω₀ = o and Ω_{n+1}(A) = ℓ(Ω_n(A)) (ℓ is the last exponent of the Cantor normal form)",
            ),
            (
                "A を理論とみたとき、列 (Ω₀(A), Ω₁(A), …) が Π_{n+1} 順序数の列に当たる",
                "reading A as a theory, the sequence (Ω₀(A), Ω₁(A), …) gives its Π_{n+1} ordinals",
            ),
        ],
        latex: r"
\begin{align*}
\Omega_\xi(A) &= o(\xi{\downarrow}h_\xi(A)), \qquad \Omega_0 = o, \qquad \Omega_{n+1}(A) = \ell(\Omega_n(A))
\end{align*}",
        source: (
            "D. Fernández-Duque & J. J. Joosten, Well-orders in the transfinite Japaridze algebra I（Cor 4.16）・II（Lemma 6.2・Thm 6.5）",
            "D. Fernández-Duque & J. J. Joosten, Well-orders in the transfinite Japaridze algebra I (Cor 4.16) and II (Lemma 6.2, Thm 6.5)",
        ),
        related: &["worm-o", "worm-o-transfinite"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "bracket",
        symbol: "o*(a)",
        name: ("括弧語と順序数 o*", "Bracket words and o*"),
        lines: &[
            (
                "翻訳 a*：⊤* = ⊤、((a)b)* = ⟨o(a*)⟩b*。各文字 a_i を、それ自身が表す順序数に置き換えた worm",
                "translation a*: ⊤* = ⊤ and ((a)b)* = ⟨o(a*)⟩b*, the worm obtained by replacing each letter a_i by the ordinal it denotes",
            ),
            ("o*(a) = o(a*)", "o*(a) = o(a*)"),
            (
                "入れ子の深さ N(a)（⊤ は 0、() は 1）について h(N(a)) ≤ o*(a) < h(N(a) + 1)。h(0) = 0、h(n + 1) = e^{h(n)}(1) で、上限が Γ₀（Prop 23）",
                "for the nesting depth N(a) (⊤ has 0, () has 1), h(N(a)) ≤ o*(a) < h(N(a) + 1), where h(0) = 0 and h(n + 1) = e^{h(n)}(1) with supremum Γ₀ (Prop 23)",
            ),
        ],
        latex: r"
\begin{align*}
\top^* &= \top, \qquad ((a)b)^* = \langle o(a^*) \rangle b^*, \qquad o^*(a) = o(a^*)\\
h(0) &= 0, \quad h(n+1) = e^{h(n)}(1), \qquad h(N(a)) \le o^*(a) < h(N(a)+1)
\end{align*}",
        source: (
            "D. Fernández-Duque & E. Hermo Reyes（arXiv:2008.13445）Def 19・Prop 23",
            "D. Fernández-Duque & E. Hermo Reyes (arXiv:2008.13445), Def 19 and Prop 23",
        ),
        related: &["bracket-battle", "bracket-nf", "worm-o-transfinite", "bc-tau"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "bracket-nf",
        symbol: "nf(a)",
        name: ("括弧語の正規形と順序数なしの比較", "Normal form of bracket words, compared without ordinals"),
        lines: &[
            (
                "a が正規形 :⟺ 各文字が正規形で、a* が Beklemishev 標準形（Def 31）。Γ₀ 未満の各順序数に、正規形の括弧語がちょうど 1 つある（Thm 32）",
                "a is in normal form :⟺ every letter is in normal form and a* is in Beklemishev normal form (Def 31); each ordinal below Γ₀ has exactly one normal-form bracket word (Thm 32)",
            ),
            (
                "順序数を使わない比較：a, b を文字の列とみて head/body の再帰（Thm 3.17）にかけ、文字どうしの大小は同じ比較で再帰的に決める（入れ子が 1 段浅くなるので止まる）",
                "comparison without ordinals: run the head/body recursion (Thm 3.17) on a and b as strings of letters, deciding comparisons of letters by the same procedure recursively (it stops because letters are one level shallower)",
            ),
            (
                "順序数を使わない正規形：文字を正規化し、最小の文字で区切った各成分を正規化し、左側にもっと大きい成分がある成分を隣の区切りごと消す",
                "normal form without ordinals: normalize the letters, split at the least letter and normalize each component, then delete each component that has a larger component to its left, together with its separator",
            ),
        ],
        latex: r"
\begin{align*}
a \in \mathrm{NF} &\iff a_i \in \mathrm{NF} \text{ for all letters } a_i \text{ and } a^* \in \mathrm{BNF}
\end{align*}",
        source: (
            "D. Fernández-Duque & E. Hermo Reyes（arXiv:2008.13445）Def 31・Thm 32。順序数なしの比較と正規形は wormlab の bracket.rs（BracketOrder）",
            "D. Fernández-Duque & E. Hermo Reyes (arXiv:2008.13445), Def 31 and Thm 32; the comparison and normal form without ordinals are wormlab's bracket.rs (BracketOrder)",
        ),
        related: &["bracket", "bnf", "bc-tau"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "iworm",
        symbol: "p(w)",
        name: ("impredicative worm と値 p", "Impredicative worms and their value p"),
        lines: &[
            (
                "W_Ω ::= ⊤ | (w)v | Ωv：括弧語に、文字としての Ω を足したもの",
                "W_Ω ::= ⊤ | (w)v | Ωv: bracket words with Ω allowed as a letter",
            ),
            (
                "翻訳 ·^π：⊤^π = ⊤、((w)v)^π = ⟨π(w^π)⟩v^π、(Ωv)^π = ⟨Ω⟩v^π",
                "translation ·^π: ⊤^π = ⊤, ((w)v)^π = ⟨π(w^π)⟩v^π and (Ωv)^π = ⟨Ω⟩v^π",
            ),
            (
                "射影 π(u)：文字がすべて可算なら o(u)。Ω を含み o(u) ≤ e_{Ω+1}1 = φ(Ω, ω) なら π(u) = ψ(−Ω + o(u))（Lemma 6.31）",
                "projection π(u): o(u) if all letters are countable; if u contains Ω and o(u) ≤ e_{Ω+1}1 = φ(Ω, ω), then π(u) = ψ(−Ω + o(u)) (Lemma 6.31)",
            ),
            (
                "値 p(w) = π(w^π)。p は ψ(e_{Ω+1}1) 未満のすべての数をとる（Thm 6.36）",
                "the value p(w) = π(w^π); p takes every value below ψ(e_{Ω+1}1) (Thm 6.36)",
            ),
        ],
        latex: r"
\begin{align*}
\top^\pi &= \top, \qquad ((w)v)^\pi = \langle \pi(w^\pi) \rangle v^\pi, \qquad (\Omega v)^\pi = \langle \Omega \rangle v^\pi\\
\pi(u) &= \begin{cases} o(u) & (\text{all letters countable})\\ \psi(-\Omega + o(u)) & (\Omega \le o(u) \le e_{\Omega+1}1 = \varphi(\Omega, \omega))\end{cases}\\
p(w) &= \pi(w^\pi)
\end{align*}",
        source: (
            "D. Fernández-Duque, Worms and spiders（arXiv:1605.08867）Def 6.24・6.33・6.34、Lemma 6.31、Thm 6.36",
            "D. Fernández-Duque, Worms and spiders (arXiv:1605.08867), Defs 6.24, 6.33 and 6.34, Lemma 6.31 and Thm 6.36",
        ),
        related: &["psi", "bracket", "worm-o-transfinite"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "rcbi-order",
        symbol: "A <¹₁ B",
        name: ("RC_BI の式の順序と順序数", "Order and ordinals of RC_BI formulas"),
        lines: &[
            (
                "W_BI は変数・∇・⟨1⟩_ω を含まない RC_BI の式の全体",
                "W_BI is the set of RC_BI formulas without variables, ∇ and ⟨1⟩_ω",
            ),
            (
                "A <¹₁ B :⟺ B ⊢ ⟨1⟩₁A（B の理論は A の理論の Π¹₁ 反射を示す）。A ≡¹₁ B :⟺ ∇A ⊣⊢ ∇B（同じ Π¹₁ 定理をもつ）",
                "A <¹₁ B :⟺ B ⊢ ⟨1⟩₁A (the theory of B proves Π¹₁ reflection for that of A); A ≡¹₁ B :⟺ ∇A ⊣⊢ ∇B (they have the same Π¹₁ theorems)",
            ),
            (
                "≤¹₁ は W_BI 上の線形で整礎な前順序（Thm 4.11）。o(A) は A より下の同値類の順序型で、Bachmann–Howard 順序数までの値をとる",
                "≤¹₁ is a linear well-founded preorder on W_BI (Thm 4.11); o(A) is the order type of the classes below A, and these reach up to the Bachmann–Howard ordinal",
            ),
            (
                "A が表す理論の Π¹₁ 証明論的順序数は ε_{o(A)}（Cor 6.6）",
                "the Π¹₁ proof-theoretic ordinal of the theory denoted by A is ε_{o(A)} (Cor 6.6)",
            ),
        ],
        latex: r"
\begin{align*}
A <^1_1 B &\iff B \vdash \langle 1 \rangle_1 A, \qquad A \equiv^1_1 B \iff \nabla A \dashv\vdash \nabla B\\
|A^*|_{\Pi^1_1} &= \varepsilon_{o(A)}
\end{align*}",
        source: (
            "F. Pakhomov & V. Lazar（arXiv:2610.20115）Def 4.1・Thm 4.11・Cor 6.6",
            "F. Pakhomov & V. Lazar (arXiv:2610.20115), Def 4.1, Thm 4.11 and Cor 6.6",
        ),
        related: &["rcbi-fs", "rcbi-battle", "rcbi-frame"],
        general: &[],
        tab: Some("ordinal"),
        research: false,
    },
    Raw {
        key: "bc-tau",
        symbol: "φ^τ",
        name: ("BC の順序 ◁ と翻訳 τ", "The order ◁ of BC and the translation τ"),
        lines: &[
            (
                "BC の式：φ ::= ⊤ | p | φ ∧ ψ | (a)φ（a は括弧語）。括弧語 a はそのまま式 (a₁)…(a_k)⊤ とも読む",
                "BC formulas: φ ::= ⊤ | p | φ ∧ ψ | (a)φ (a a bracket word); a bracket word a is also read as the formula (a₁)…(a_k)⊤",
            ),
            (
                "b ◁ a :⟺ BC ⊢ a ⊢ ()b。b ≤ a :⟺ BC ⊢ a ⊢ ()b か BC ⊢ a ⊢ b。大小は順序数ではなく BC 自身の導出で決まる",
                "b ◁ a :⟺ BC ⊢ a ⊢ ()b, and b ≤ a :⟺ BC ⊢ a ⊢ ()b or BC ⊢ a ⊢ b; the order is fixed by derivations in BC itself, not by ordinals",
            ),
            (
                "翻訳 τ：(a)φ ↦ ⟨o*(a)⟩φ^τ（ほかは同じ形のまま）。BC ⊢ φ ⊢ ψ ⟺ RC_Γ₀ ⊢ φ^τ ⊢ ψ^τ（Thm 38）",
                "the translation τ: (a)φ ↦ ⟨o*(a)⟩φ^τ (the rest unchanged); BC ⊢ φ ⊢ ψ iff RC_Γ₀ ⊢ φ^τ ⊢ ψ^τ (Thm 38)",
            ),
            (
                "正規形の括弧語は ≤ について型 Γ₀ の整列順序（Thm 39、証明は順序数経由）",
                "the normal-form bracket words are well-ordered by ≤ with order type Γ₀ (Thm 39, proved through ordinals)",
            ),
        ],
        latex: r"
\begin{align*}
b \lhd a &\iff \mathrm{BC} \vdash a \vdash ()b, \qquad b \le a \iff \mathrm{BC} \vdash a \vdash ()b \text{ or } \mathrm{BC} \vdash a \vdash b\\
((a)\varphi)^\tau &= \langle o^*(a) \rangle \varphi^\tau, \qquad \mathrm{BC} \vdash \varphi \vdash \psi \iff \mathrm{RC}_{\Gamma_0} \vdash \varphi^\tau \vdash \psi^\tau
\end{align*}",
        source: (
            "D. Fernández-Duque & E. Hermo Reyes（arXiv:2008.13445）Def 26・Def 27・Def 28・Thm 38・Thm 39",
            "D. Fernández-Duque & E. Hermo Reyes (arXiv:2008.13445), Defs 26, 27 and 28, Thm 38 and Thm 39",
        ),
        related: &["bracket", "bracket-nf", "bc-frame", "rc-frame"],
        general: &[],
        tab: Some("proof"),
        research: false,
    },
];

// ----------------------------------------------------------------------
// 体系の意味論
// ----------------------------------------------------------------------

const SEMANTICS: &[Raw] = &[
    Raw {
        key: "rc-frame",
        symbol: "(W, R_α)",
        name: ("RC のフレームと真理", "Frames and truth for RC"),
        lines: &[
            (
                "様相の集合 Λ（線形順序）について、RC_Λ フレームは (W, (R_α)_{α∈Λ})。条件は推移性（x R_α y R_α z ⇒ x R_α z）、単調性（β < α なら R_α ⊆ R_β）、J（α > β で x R_α y かつ x R_β z ⇒ y R_β z）",
                "for a linearly ordered set Λ of modalities, an RC_Λ frame is (W, (R_α)_{α∈Λ}) with transitivity (x R_α y R_α z ⇒ x R_α z), monotonicity (R_α ⊆ R_β for β < α) and J (for α > β, x R_α y and x R_β z ⇒ y R_β z)",
            ),
            (
                "真理：x ⊨ ⟨α⟩φ :⟺ ある y で x R_α y かつ y ⊨ φ。⊤・変数・∧ はふつうどおり。A ⊢ B が妥当 :⟺ どの点でも A が真なら B も真",
                "truth: x ⊨ ⟨α⟩φ :⟺ x R_α y and y ⊨ φ for some y; ⊤, variables and ∧ as usual; A ⊢ B is valid :⟺ B holds wherever A holds",
            ),
            (
                "RC は有限フレームについて健全かつ完全。非反射性や整礎性は要らない（それらは算術的完全性のためのもの）",
                "RC is sound and complete for finite frames; irreflexivity and well-foundedness are not needed (they matter only for arithmetical completeness)",
            ),
        ],
        latex: r"
\begin{align*}
&x R_\alpha y R_\alpha z \Rightarrow x R_\alpha z, \qquad R_\alpha \subseteq R_\beta \ (\beta < \alpha)\\
&x R_\alpha y \wedge x R_\beta z \Rightarrow y R_\beta z \quad (\alpha > \beta)\\
&x \models \langle \alpha \rangle \varphi \iff \exists y\,(x R_\alpha y \wedge y \models \varphi)
\end{align*}",
        source: (
            "E. V. Dashkov, On the positive fragment of the polymodal provability logic GLP, Math. Notes 91（2012）。L. D. Beklemishev, Positive provability logic for uniform reflection principles, APAL 165（2014, arXiv:1304.4396）§4（Cor 4.8、Remark 4.10：様相が線形順序でも同じ）",
            "E. V. Dashkov, On the positive fragment of the polymodal provability logic GLP, Math. Notes 91 (2012); L. D. Beklemishev, Positive provability logic for uniform reflection principles, APAL 165 (2014, arXiv:1304.4396), §4 (Cor 4.8; Remark 4.10: the same for linearly ordered modalities)",
        ),
        related: &["rc-closure", "worm", "bc-frame"],
        general: &[],
        tab: Some("model"),
        research: false,
    },
    Raw {
        key: "rc-closure",
        symbol: "T[A]",
        name: ("RC の閉包モデル", "Closure model for RC"),
        lines: &[
            (
                "標準木 T[A]：式 A の構文木をそのままモデルにしたもの（p・⊤ は 1 点、B ∧ C は根を貼り合わせ、⟨α⟩B は新しい根から T[B] の根へ R_α の辺）",
                "the canonical tree T[A] is the syntax tree of A read as a model (p and ⊤ are one point, B ∧ C glues the roots, ⟨α⟩B adds a new root with an R_α edge to the root of T[B])",
            ),
            (
                "S = A, B に現れる様相として、T[A] を推移性・単調性・J で閉じた最小のフレームにする",
                "with S the modalities occurring in A and B, close T[A] under transitivity, monotonicity and J over S",
            ),
            (
                "A ⊢ B ⟺ 閉包したモデルの根で B が真。偽ならそのモデルが反例。点の数の多項式時間で判定できる",
                "A ⊢ B iff B is true at the root of the closed model; if not, that model is a counterexample; this decides RC in polynomial time",
            ),
        ],
        latex: r"
\begin{align*}
\mathrm{RC} \vdash A \vdash B &\iff \overline{T[A]}^{\,S}, \mathrm{root} \models B \qquad (S = \text{modalities of } A, B)
\end{align*}",
        source: (
            "L. D. Beklemishev（arXiv:1304.4396）Def 5.1・Thm 3(ii)（閉包法は Dashkov による）",
            "L. D. Beklemishev (arXiv:1304.4396), Def 5.1 and Thm 3(ii) (the closure method is due to Dashkov)",
        ),
        related: &["rc-frame", "rcbi-model"],
        general: &[],
        tab: Some("model"),
        research: false,
    },
    Raw {
        key: "bc-frame",
        symbol: "(W, R_a)",
        name: ("BC のフレーム", "Frames for BC"),
        lines: &[
            (
                "括弧語の順序 ◁ を入れ子の深さについての再帰で作る：深さ < d の語の順序 Λ_{<d} が決まっていれば、深さ ≤ d の語 a, b を Λ_{<d} の上の worm と読み、b ◁ a :⟺ RC_{Λ<d} ⊢ a ⊢ ⟨[⊤]⟩b",
                "the order ◁ of bracket words is built by recursion on nesting depth: once the order Λ_{<d} of words of depth < d is known, words a, b of depth ≤ d are read as worms over Λ_{<d}, and b ◁ a :⟺ RC_{Λ<d} ⊢ a ⊢ ⟨[⊤]⟩b",
            ),
            (
                "BC フレーム (W, (R_a)_{a∈B})：(F1) R_a は推移的、(F2) b ≤ a なら R_a ⊆ R_b、(F3) b ◁ a で x R_a y かつ x R_b z ⇒ y R_b z",
                "a BC frame (W, (R_a)_{a∈B}): (F1) R_a is transitive, (F2) R_a ⊆ R_b when b ≤ a, (F3) for b ◁ a, x R_a y and x R_b z ⇒ y R_b z",
            ),
            (
                "主張（草稿）：BC ⊢ φ ⊢ ψ ⟺ すべての BC フレームで妥当 ⟺ 有限の閉包モデルの根で ψ が真。どの段にも順序数は出てこない",
                "claim (draft): BC ⊢ φ ⊢ ψ iff it is valid in all BC frames iff ψ is true at the root of a finite closure model; no ordinals appear anywhere",
            ),
        ],
        latex: r"
\begin{align*}
&(F1)\ x R_a y R_a z \Rightarrow x R_a z \qquad (F2)\ b \le a \Rightarrow R_a \subseteq R_b\\
&(F3)\ b \lhd a,\ x R_a y \wedge x R_b z \Rightarrow y R_b z
\end{align*}",
        source: (
            "wormlab の研究ノートと論文の草稿（An autonomous Kripke semantics for the Bracket Calculus、未公開）。問いは Fernández-Duque & Hermo Reyes（arXiv:2008.13445）§10",
            "wormlab's research notes and draft paper (An autonomous Kripke semantics for the Bracket Calculus, unpublished); the question is from Fernández-Duque & Hermo Reyes (arXiv:2008.13445), §10",
        ),
        related: &["bc-tau", "bc-psi", "rc-frame"],
        general: &[],
        tab: Some("proof"),
        research: true,
    },
    Raw {
        key: "bc-psi",
        symbol: "Ψ(T)",
        name: ("BC の自律的な意味論（不動点 Ψ）", "Autonomous semantics for BC (the fixed point Ψ)"),
        lines: &[
            (
                "比較のシーケント：括弧語 a, b について a ⊢ b と a ⊢ ()b。T はその集合",
                "comparison sequents are a ⊢ b and a ⊢ ()b for bracket words a, b; T is a set of them",
            ),
            (
                "T フレーム (W, (R_a)_{a∈B})：(a ⊢ b) か (a ⊢ ()b) が T に入れば R_a ⊆ R_b、かつ x R_a y R_b z ⇒ x R_b z。(a ⊢ ()b) が T に入れば x R_a y かつ x R_b z ⇒ y R_b z",
                "a T-frame (W, (R_a)_{a∈B}): if (a ⊢ b) or (a ⊢ ()b) is in T, then R_a ⊆ R_b and x R_a y R_b z ⇒ x R_b z; if (a ⊢ ()b) is in T, then x R_a y and x R_b z ⇒ y R_b z",
            ),
            (
                "Ψ(T) = すべての T フレームで妥当な比較のシーケントの集合。Ψ は単調",
                "Ψ(T) is the set of comparison sequents valid in all T-frames; Ψ is monotone",
            ),
            (
                "主張（草稿）：Ψ の不動点はただ 1 つで、それは BC で導出できる比較の全体。深さ d の語どうしの比較は Ψ^d(∅) で出そろう。◁ も RC も順序数も定義に出てこない",
                "claim (draft): Ψ has exactly one fixed point, namely the set of comparisons derivable in BC, and comparisons of words of depth d appear in Ψ^d(∅); neither ◁ nor RC nor ordinals occur in the definition",
            ),
        ],
        latex: r"
\begin{align*}
&(a \vdash b) \in T \text{ or } (a \vdash ()b) \in T \Rightarrow R_a \subseteq R_b \text{ and } (x R_a y R_b z \Rightarrow x R_b z)\\
&(a \vdash ()b) \in T \Rightarrow (x R_a y \wedge x R_b z \Rightarrow y R_b z)\\
&\Psi(T) = \{\sigma \text{ comparison sequent} : \sigma \text{ valid in all } T\text{-frames}\}
\end{align*}",
        source: (
            "wormlab の研究ノートと論文の草稿（未公開）。計算機での裏づけは wormlab の bcfix（作業中）",
            "wormlab's research notes and draft paper (unpublished); computer checks in wormlab's bcfix (in progress)",
        ),
        related: &["bc-frame", "bc-tau"],
        general: &[],
        tab: None,
        research: true,
    },
    Raw {
        key: "rcbi-frame",
        symbol: "(S, R)",
        name: ("RC_BIω のモデル", "Models of RC_BIω"),
        lines: &[
            (
                "関係は R¹_α（1 ≤ α < ω と α = ω）、R²_α（2 ≤ α < ω）、R↓、R∇。真理は x ⊨ ⟨i⟩_α A :⟺ ある y で x Rⁱ_α y かつ y ⊨ A（↓・∇ も同じ形）",
                "the relations are R¹_α (1 ≤ α < ω and α = ω), R²_α (2 ≤ α < ω), R↓ and R∇; x ⊨ ⟨i⟩_α A :⟺ x Rⁱ_α y and y ⊨ A for some y (likewise for ↓ and ∇)",
            ),
            (
                "I 単調性：Rⁱ_α ⊆ Rⁱ_β（β < α）、R²_α ⊆ R¹_α、R∇ は反射的、R¹_α ⊆ R∇、R↓ ⊆ R∇",
                "I monotonicity: Rⁱ_α ⊆ Rⁱ_β (β < α), R²_α ⊆ R¹_α, R∇ reflexive, R¹_α ⊆ R∇, R↓ ⊆ R∇",
            ),
            (
                "II 推移性：a Rⁱ_α b Rʲ_α c ⇒ a Rʲ_α c、R∇ は推移的、a R∇ b R¹_α c ⇒ a R¹₁ c、a R¹_α b R∇ c ⇒ a R¹₁ c、a R↓ b R∇ c ⇒ a R↓ c",
                "II transitivity: a Rⁱ_α b Rʲ_α c ⇒ a Rʲ_α c, R∇ transitive, a R∇ b R¹_α c ⇒ a R¹₁ c, a R¹_α b R∇ c ⇒ a R¹₁ c, a R↓ b R∇ c ⇒ a R↓ c",
            ),
            (
                "III 連言：a Rⁱ_α b かつ a Rʲ_β c ⇒ b Rʲ_β c（β < α か α = β = ω）、a R²_α b かつ a Rⁱ_β c ⇒ b R↓ c",
                "III conjunction: a Rⁱ_α b and a Rʲ_β c ⇒ b Rʲ_β c (β < α or α = β = ω); a R²_α b and a Rⁱ_β c ⇒ b R↓ c",
            ),
            (
                "IV 構成：a R↓ b ⇒ ある c で a R¹_ω c。a R↓ b R¹_α c ⇒ ある d で a R¹_ω d R↓ c。a R²_α b ⇒ ある c で a R∇ c、c R↓ a、b のどの後続も c の後続（同じ関係で）、変数の値は b ≤ c",
                "IV construction: a R↓ b ⇒ a R¹_ω c for some c; a R↓ b R¹_α c ⇒ a R¹_ω d R↓ c for some d; a R²_α b ⇒ there is c with a R∇ c, c R↓ a, every successor of b also a successor of c (for the same relation), and V(b, p) ≤ V(c, p)",
            ),
            (
                "RC_BIω はこのモデルについて健全かつ完全（Thm 2.14）",
                "RC_BIω is sound and complete for these models (Thm 2.14)",
            ),
        ],
        latex: r"
\begin{align*}
&x \models \langle i \rangle_\alpha A \iff \exists y\,(x R^i_\alpha y \wedge y \models A), \quad x \models {\downarrow}A \iff \exists y\,(x R_{\downarrow} y \wedge y \models A)\\
&\text{I: } R^i_\alpha \subseteq R^i_\beta\ (\beta < \alpha),\ R^2_\alpha \subseteq R^1_\alpha,\ R_\nabla \text{ reflexive},\ R^1_\alpha \subseteq R_\nabla,\ R_\downarrow \subseteq R_\nabla\\
&\text{II: } R^i_\alpha ; R^j_\alpha \subseteq R^j_\alpha,\ R_\nabla ; R_\nabla \subseteq R_\nabla,\ R_\nabla ; R^1_\alpha \subseteq R^1_1,\ R^1_\alpha ; R_\nabla \subseteq R^1_1,\ R_\downarrow ; R_\nabla \subseteq R_\downarrow\\
&\text{III: } a R^i_\alpha b \wedge a R^j_\beta c \Rightarrow b R^j_\beta c\ (\beta < \alpha \text{ or } \alpha = \beta = \omega),\quad a R^2_\alpha b \wedge a R^i_\beta c \Rightarrow b R_\downarrow c\\
&\text{IV: } a R_\downarrow b \Rightarrow \exists c\, a R^1_\omega c,\quad a R_\downarrow b R^1_\alpha c \Rightarrow \exists d\,(a R^1_\omega d R_\downarrow c),\\
&\qquad a R^2_\alpha b \Rightarrow \exists c\,(a R_\nabla c \wedge c R_\downarrow a \wedge \forall d\,\forall R\,(b R d \Rightarrow c R d) \wedge V(b) \le V(c))
\end{align*}",
        source: (
            "F. Pakhomov & V. Lazar（arXiv:2610.20115）Def 2.12・Def 2.13・Thm 2.14",
            "F. Pakhomov & V. Lazar (arXiv:2610.20115), Def 2.12, Def 2.13 and Thm 2.14",
        ),
        related: &["rcbi-model", "rcbi-order", "rc-frame"],
        general: &[],
        tab: Some("model"),
        research: false,
    },
    Raw {
        key: "rcbi-model",
        symbol: "M_A",
        name: ("RC_BI の有限モデル M_A", "The finite model M_A of RC_BI"),
        lines: &[
            (
                "前モデル：変数のない式 A の構文木に、⟨2⟩ の行き先の R¹_ω ループと、↓ ごとの零点・中間点を足す",
                "pre-model: the syntax tree of a variable-free formula A, with R¹_ω loops at the targets of ⟨2⟩ and a zero point and intermediate points for each ↓",
            ),
            (
                "R² の行き先の点 b ごとにコピー点 b↓ を足し（b↓ R¹_ω b、b⊤ R∇ b↓、b↓ R↓ b⊤。b⊤ は b の anchor）、規則 (a)〜(l) で閉じる",
                "for each target b of R² add a copy point b↓ (b↓ R¹_ω b, b⊤ R∇ b↓, b↓ R↓ b⊤, where b⊤ is the anchor of b), then close under the rules (a)–(l)",
            ),
            (
                "A ⊢ B ⟺ M_A の根で B が真（Thm 3.19、変数のない式）。M_A はフレーム条件 I〜IV を満たす（wormlab はこれを検査する）",
                "A ⊢ B iff B is true at the root of M_A (Thm 3.19, variable-free formulas); M_A satisfies the frame conditions I–IV (wormlab checks this)",
            ),
            (
                "wormlab は ↓B の中間点を、双模倣で同じ行き先ごとに 1 つにまとめる（点の数が ↓ の入れ子について指数から多項式になる）",
                "wormlab merges the intermediate points of ↓B with bisimilar targets (the number of points becomes polynomial instead of exponential in the nesting of ↓)",
            ),
        ],
        latex: r"
\begin{align*}
\mathrm{RC}_{\mathrm{BI}\omega} \vdash A \vdash B &\iff M_A, \mathrm{root} \models B \quad (A, B \text{ variable-free})
\end{align*}",
        source: (
            "F. Pakhomov & V. Lazar（arXiv:2610.20115）Def 3.9・Thm 3.19。点の共有は wormlab の rcbi.rs（algorithms.md §6）",
            "F. Pakhomov & V. Lazar (arXiv:2610.20115), Def 3.9 and Thm 3.19; the sharing of points is wormlab's rcbi.rs (algorithms.md §6)",
        ),
        related: &["rcbi-frame", "rc-closure", "rcbi-order"],
        general: &[],
        tab: Some("model"),
        research: false,
    },
];

// ----------------------------------------------------------------------
// 計算した例（定義の場合分けごとに 1 つ。実装を呼んで作る）
// ----------------------------------------------------------------------

/// 例の文の区切り（日本語は全角、英語は半角）。
fn colon() -> &'static str {
    tr("：", ": ")
}

fn comma() -> &'static str {
    tr("、", ", ")
}

/// 長い文字は先頭だけにする。
fn clip(s: String) -> String {
    const MAX: usize = 120;
    if s.chars().count() <= MAX { s } else { format!("{}…", s.chars().take(MAX).collect::<String>()) }
}

/// 日本語と英語で語順の違う文。
fn t2(ja: String, en: String) -> String {
    if is_en() { en } else { ja }
}

/// 場合と、その例の列（1 つ目が代表、残りは「もっと見る」。同じものは 1 度だけ）。
fn example(case: String, items: Vec<String>) -> Result<Example, String> {
    let mut it = items.into_iter().map(clip);
    let text = it.next().ok_or_else(|| format!("{case} の例がない"))?;
    let mut more: Vec<String> = Vec::new();
    for x in it {
        if x != text && !more.contains(&x) {
            more.push(x);
        }
    }
    Ok(Example { case, text, more })
}

/// 場合（日本語と英語）と、その例の列。
fn ex(case: (&str, &str), items: Vec<String>) -> Result<Example, String> {
    example(tr(case.0, case.1).to_string(), items)
}

/// 言語によらない式で書いた場合と、その例の列。
fn exf(case: &str, items: Vec<String>) -> Result<Example, String> {
    example(case.to_string(), items)
}

/// 入力の列を同じ作り方で例の列にする。
fn each<T>(xs: &[T], f: impl Fn(&T) -> Result<String, String>) -> Result<Vec<String>, String> {
    xs.iter().map(f).collect()
}

/// 式の列を計算して「式 = 値」の列にする。
fn evs(xs: &[&str]) -> Result<Vec<String>, String> {
    each(xs, |s| ev(s))
}

/// 標準の基本列の例の列。
fn fss(xs: &[(&str, u64)]) -> Result<Vec<String>, String> {
    each(xs, |(s, n)| fs_ex(s, *n))
}

/// 式どうしの比較の例の列。
fn cmps(xs: &[(&str, &str)]) -> Result<Vec<String>, String> {
    each(xs, |(a, b)| cmp_ex(a, b))
}

fn ord(s: &str) -> Result<Veblen, String> {
    s.parse::<Veblen>().map_err(|e| e.to_string())
}

fn worm(s: &str) -> Result<Worm, String> {
    s.parse::<Worm>().map_err(|e| e.to_string())
}

fn bracket(s: &str) -> Result<Bracket, String> {
    s.parse::<Bracket>().map_err(|e| e.to_string())
}

fn rcbi_formula(s: &str) -> Result<rcbi::Formula, String> {
    s.parse::<rcbi::Formula>().map_err(|e| e.to_string())
}

/// 式を標準形にして「式 = 値」。
fn ev(s: &str) -> Result<String, String> {
    let e = expr::eval_str(s)?;
    Ok(format!("{} = {}", e.input, e.value))
}

/// 2 つの式を計算して比べた「a < b」（書いた式のまま）。
fn cmp_ex(a: &str, b: &str) -> Result<String, String> {
    let (x, y) = (expr::eval_str(a)?.value, expr::eval_str(b)?.value);
    Ok(format!("{a} {} {b}", rel(x.cmp(&y))))
}

fn rel(o: Ordering) -> &'static str {
    match o {
        Ordering::Less => "<",
        Ordering::Equal => "=",
        Ordering::Greater => ">",
    }
}

/// 和や積の数に [n] や {n} を付けるときは、かっこで囲む（かっこの外に + か · があるとき）。
fn grouped(s: &str) -> String {
    let mut depth = 0i32;
    let top_level_op = s.chars().any(|c| {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            _ => {}
        }
        depth == 0 && (c == '+' || c == '·')
    });
    if top_level_op { format!("({s})") } else { s.to_string() }
}

/// 添字：1 文字ならそのまま、2 文字以上なら {…} で囲む（H_ω、H_{ω^2}）。
fn sub(s: &str) -> String {
    if s.chars().count() == 1 { s.to_string() } else { format!("{{{s}}}") }
}

/// 標準の基本列の例「α[n] = 値」。
fn fs_ex(s: &str, n: u64) -> Result<String, String> {
    let v = ord(s)?.fundamental(n).ok_or_else(|| format!("{s}[{n}]"))?;
    Ok(format!("{}[{n}] = {v}", grouped(s)))
}

/// 判定の結果の言葉。
fn verdict(holds: bool) -> &'static str {
    if holds { tr("導出できる", "derivable") } else { tr("導出できない", "not derivable") }
}

/// RC のシーケントを判定した「A ⊢ B：導出できる」。
fn rc_ex(s: &str) -> Result<(String, rc::Decision), String> {
    let seq = s.parse::<Sequent<u32>>().map_err(|e| e.to_string())?;
    let d = rc::decide(&seq.lhs, &seq.rhs);
    Ok((format!("{} ⊢ {}{}{}", seq.lhs, seq.rhs, colon(), verdict(d.holds)), d))
}

/// RC_BI のシーケントを判定した「A ⊢ B：導出できる」。
fn rcbi_ex(s: &str) -> Result<String, String> {
    let seq = s.parse::<rcbi::Sequent>().map_err(|e| e.to_string())?;
    let d = rcbi::decide(&seq.lhs, &seq.rhs)?;
    Ok(format!("{} ⊢ {}{}{}", seq.lhs, seq.rhs, colon(), verdict(d.holds)))
}

/// 鍵ごとの例（定義の場合分けごとに、代表の例 1 つと、同じ場合のほかの例）。計算できなければ空
/// （テストで、例のある鍵は空でないことを確かめる）。
pub fn examples(key: &str) -> Vec<Example> {
    examples_of(key).unwrap_or_default()
}

/// worm battle の最初の数ステップ「2 0 2 → 1 1 0 2 → …」。
fn worm_steps(s: &str, k: usize) -> Result<String, String> {
    Ok(worm(s)?.battle().take(k).map(|w| w.to_string()).collect::<Vec<_>>().join(" → "))
}

/// 括弧語の battle の最初の数ステップ。
fn bracket_steps(s: &str, k: usize) -> Result<String, String> {
    Ok(bracket(s)?.battle().take(k).map(|w| w.to_string()).collect::<Vec<_>>().join(" → "))
}

/// 「A は N ステップで ⊤」（数えきれないものは入れない）。
fn reaches_top(name: String, len: Option<u64>) -> Option<String> {
    len.map(|n| t2(format!("{name} は {n} ステップで ⊤"), format!("{name} reaches ⊤ after {n} steps")))
}

/// 順序数の標準 battle の道すじ「ω^2 → [1] ω → [2] 2 → …」（長ければ先頭だけ）。
fn ordinal_path(s: &str, start: u64) -> Result<String, String> {
    let mut x = ord(s)?;
    let (mut out, mut k) = (vec![x.to_string()], start);
    while let Some(y) = x.fundamental(k) {
        out.push(format!("[{k}] {y}"));
        x = y;
        k += 1;
        if out.len() > 8 {
            out.push("…".into());
            break;
        }
    }
    Ok(out.join(" → "))
}

/// RC_BI の式の battle で見つけた 1 ステップ（なければ None）。
struct RcbiSteps {
    /// 極限形の式からの最初の 1 ステップ
    limit: Option<String>,
    /// 後続形の式からの最初の 1 ステップ
    succ: Option<String>,
    /// ⊤ に着く最後の 1 ステップ
    last: Option<String>,
}

/// RC_BI の式の battle で、極限形・後続形の最初の 1 ステップと、最後の 1 ステップ。
fn rcbi_battle_steps(s: &str) -> Result<RcbiSteps, String> {
    let a = rcbi_formula(s)?;
    // 長い battle では式がどんどん大きくなるので、短いうち（12 ステップ・300 文字まで）だけ見る
    let mut steps: Vec<rcbi::Formula> = Vec::new();
    for f in rcbi_order::battle(&a).take(12) {
        let long = f.to_string().chars().count() > 300;
        steps.push(f);
        if long {
            break;
        }
    }
    let (mut limit, mut succ) = (None, None);
    for (k, w) in steps.windows(2).enumerate() {
        let line = format!("A⦃{k}⦄ = {} → A⦃{}⦄ = {}", w[0], k + 1, w[1]);
        match rcbi_order::form(&w[0])? {
            Form::Limit if limit.is_none() => limit = Some(line),
            Form::Successor(_) if succ.is_none() => succ = Some(line),
            _ => {}
        }
    }
    let n = steps.len();
    let last = (n >= 2 && rcbi_order::form(&steps[n - 1])? == Form::Zero)
        .then(|| format!("A⦃{}⦄ = {} → A⦃{}⦄ = {}", n - 2, steps[n - 2], n - 1, steps[n - 1]));
    Ok(RcbiSteps { limit, succ, last })
}

/// 文字が自然数の worm の基本列「(A){n} = …」。
fn worm_fs(s: &str, n: usize) -> Result<String, String> {
    let a = worm(s)?;
    Ok(format!("({a}){{{n}}} = {}", a.battle_step(n).ok_or("A{n}")?))
}

/// 括弧語の基本列「a = …：a{n} = …」。
fn bracket_fs(s: &str, n: usize) -> Result<String, String> {
    let a = bracket(s)?;
    Ok(format!("a = {a}{}a{{{n}}} = {}", colon(), a.fundamental(n).ok_or("a{n}")?))
}

/// worm が作る列 α{n}（括弧語を動かした値）。
fn worm_seq(a: &Veblen, n: usize) -> Result<Veblen, String> {
    hierarchy::worm_fundamental(a, n).ok_or_else(|| format!("{a}{{{n}}}"))
}

/// α{n} = D(α, n + 1) = 値（閉じた形と、括弧語を動かした値が同じことを確かめてから）。
fn worm_seq_closed(s: &str, n: usize) -> Result<String, String> {
    let a = ord(s)?;
    let (w, d) = (worm_seq(&a, n)?, hierarchy::worm_fs_closed(&a, n).ok_or("D")?);
    if w != d {
        return Err(format!("D({a}, {}) = {d} ≠ {w}", n + 1));
    }
    Ok(format!("{}{{{n}}} = D({s}, {}) = {w}", grouped(s), n + 1))
}

/// RC_BI の式の形「A：後続形、直前は B」など。
fn rcbi_form(s: &str) -> Result<String, String> {
    let a = rcbi_formula(s)?;
    Ok(match rcbi_order::form(&a)? {
        Form::Zero => format!("{a}{}{}", colon(), tr("零", "zero")),
        Form::Successor(p) => format!("{a}{}{} {p}", colon(), tr("後続形、直前は", "successor form, predecessor")),
        Form::Limit => format!("{a}{}{}", colon(), tr("極限形", "limit form")),
    })
}

/// RC_BI の式の近似「(A)_n = …」。
fn rcbi_approx(s: &str, n: u32) -> Result<String, String> {
    let a = rcbi_formula(s)?;
    Ok(format!("({a})_{n} = {}", rcbi_order::approx(&a, n).ok_or("approx")?))
}

/// RC_BI の式の順序の記号。
fn rcbi_rel(o: Option<Ordering>) -> &'static str {
    match o {
        Some(Ordering::Less) => "<¹₁",
        Some(Ordering::Equal) => "≡¹₁",
        Some(Ordering::Greater) => ">¹₁",
        None => "?",
    }
}

/// RC_BI の式の鎖「⊤ <¹₁ ⟨1⟩₁⊤ <¹₁ …」。
fn rcbi_chain(xs: &[&str]) -> Result<String, String> {
    let fs: Vec<rcbi::Formula> = xs.iter().map(|s| rcbi_formula(s)).collect::<Result<_, _>>()?;
    let mut s = fs[0].to_string();
    for w in fs.windows(2) {
        s.push_str(&format!(" {} {}", rcbi_rel(rcbi_order::compare(&w[0], &w[1])), w[1]));
    }
    Ok(s)
}

/// worm の <_n「A <₁ B」か「A ≮₁ B」。
fn worm_lt(a: &str, b: &str, n: u32) -> Result<(bool, String), String> {
    let (x, y) = (worm(a)?, worm(b)?);
    let sub = ["₀", "₁", "₂", "₃"][n as usize];
    let lt = x.lt_n(&y, n);
    Ok((lt, format!("{x} {}{sub} {y}", if lt { "<" } else { "≮" })))
}

/// 2 つの worm の o の比較「o(A) = … < … = o(B)」。
fn worm_o_cmp(a: &str, b: &str) -> Result<String, String> {
    let (x, y) = (worm(a)?, worm(b)?);
    let (ox, oy) = (x.ordinal(), y.ordinal());
    Ok(format!("o({x}) = {ox} {} {oy} = o({y})", rel(Veblen::from(&ox).cmp(&Veblen::from(&oy)))))
}

/// RC の閉包モデル：標準木の点と辺の数、閉じたあとの辺の数（関係ごとの組の数の和）。
fn rc_closure_sizes(lhs: &str) -> Result<(String, usize, usize, usize), String> {
    let (_, d) = rc_ex(&format!("{lhs} |- {lhs}"))?;
    let m = &d.model;
    let n = m.num_points();
    let all: usize = m
        .signature()
        .iter()
        .map(|r| (0..n).flat_map(|x| (0..n).map(move |y| (x, y))).filter(|&(x, y)| m.related(r, x, y)).count())
        .sum();
    Ok((d.sequent.lhs.to_string(), n, m.tree_edges().len(), all))
}

fn examples_of(key: &str) -> Result<Vec<Example>, String> {
    Ok(match key {
        // ---- ゲームと長さ
        "worm-battle" => vec![
            exf("A⦃k⦄ = A⦃k−1⦄{k}", each(&["2 0 2", "1 1", "2", "1 2 1", "0 3"], |s| worm_steps(s, 4))?)?,
            ex(
                ("いつか必ず ⊤ に着く", "it always reaches ⊤"),
                ["2", "1", "1 1", "1 0 1", "0 1 1", "2 0 2"]
                    .iter()
                    .map(|s| worm(s).map(|w| reaches_top(w.to_string(), w.battle_length_capped(100_000, 10_000).ok())))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten()
                    .collect(),
            )?,
        ],
        "bracket-battle" => {
            let corr = |s: &str| -> Result<String, String> {
                let w = worm(s)?;
                let b = Bracket::from_nat_worm(&w);
                let (b1, w1) = (b.fundamental(1).ok_or("a{1}")?, w.battle_step(1).ok_or("A{1}")?);
                if Bracket::from_nat_worm(&w1) != b1 {
                    return Err(format!("{b1} ≠ {w1}"));
                }
                Ok(format!("{b} → {b1}  ↔  {w} → {w1}"))
            };
            vec![
                exf("a⦃k⦄ = a⦃k−1⦄{k}", each(&["((()))", "(()())", "(())()()", "(()(()))"], |s| bracket_steps(s, 3))?)?,
                ex(("文字が ()^m なら worm battle", "letters ()^m: the worm battle"), each(&["2 0 2", "1 1", "1 2 1", "3"], |s| corr(s))?)?,
                ex(
                    ("いつか必ず ⊤ に着く（Thm 42）", "it always reaches ⊤ (Thm 42)"),
                    ["(())()", "()()()", "(())", "(()())", "(())(())"]
                        .iter()
                        .map(|s| bracket(s).map(|b| reaches_top(b.to_string(), b.battle_length_capped(100_000, 10_000).ok())))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect(),
                )?,
            ]
        }
        "ordinal-battle" => {
            let lens = |s: &str, ks: &[u64]| -> Result<String, String> {
                let a = ord(s)?;
                let parts: Vec<String> = ks
                    .iter()
                    .map(|&k| {
                        let l = hierarchy::ordinal_battle_length(&a, k, Budget::default()).ok_or("length")?;
                        Ok(t2(format!("k = {k} からは {l} ステップ"), format!("{l} steps from k = {k}")))
                    })
                    .collect::<Result<_, String>>()?;
                Ok(format!("{a}{}{}", colon(), parts.join(comma())))
            };
            vec![
                ex(
                    ("α ← α[k]（後続なら直前の数）", "α ← α[k] (the predecessor for a successor)"),
                    each(&["ω^2", "ω·2 + 1", "ω^ω", "ε_0"], |s| ordinal_path(s, 1))?,
                )?,
                ex(("始めの k を変える", "another starting k"), vec![lens("ω^2", &[1, 3])?, lens("ω·2", &[1, 2, 3])?, lens("ω^ω", &[1, 2])?])?,
            ]
        }
        "rcbi-battle" => {
            let runs: Vec<RcbiSteps> =
                ["<1>_2 <1>_2 T", "<1>_3 T", "D T", "<2>_2 T"].iter().map(|s| rcbi_battle_steps(s)).collect::<Result<_, _>>()?;
            vec![
                ex(("極限形なら (A)_{k+1}", "limit form: (A)_{k+1}"), runs.iter().filter_map(|r| r.limit.clone()).collect())?,
                ex(("後続形なら直前の式", "successor form: the predecessor"), runs.iter().filter_map(|r| r.succ.clone()).collect())?,
                ex(("⊤ と同値になったら終わり", "stop at a formula equivalent to ⊤"), runs.iter().filter_map(|r| r.last.clone()).collect())?,
            ]
        }
        "battle-length" => {
            let both = |s: &str| -> Result<String, String> {
                let a = ord(s)?;
                let w = Worm::from_ordinal(&a.to_cnf().ok_or("ε₀ 未満")?);
                let l = hierarchy::worm_battle_length_of(&a, Budget::default()).ok_or("worm")?;
                let lo = hierarchy::ordinal_battle_length(&a, 1, Budget::default()).ok_or("ordinal")?;
                Ok(t2(
                    format!("{a}（標準形の worm は {w}）：worm battle {l}、標準 battle {lo}"),
                    format!("{a} (normal-form worm {w}): worm battle {l}, standard battle {lo}"),
                ))
            };
            let bound = |s: &str| -> Result<Option<String>, String> {
                let v = hierarchy::worm_battle_length_any(&ord(s)?, BigBudget::default()).ok_or("bound")?;
                Ok((!matches!(v, hierarchy::BigValue::Exact(_))).then(|| format!("{s}{}{}", colon(), v.describe())))
            };
            vec![
                exf(
                    "ℓ(A) = min{k : A⦃k⦄ = ⊤}",
                    each(&["1 1", "1", "1 0 1", "2"], |s| {
                        let w = worm(s)?;
                        Ok(format!("ℓ({w}) = {}", w.battle_length(1_000_000).ok_or("battle")?))
                    })?,
                )?,
                ex(("順序数は標準形の worm から", "an ordinal starts from its normal-form worm"), each(&["ω^2", "ω", "ω·2", "ω^ω"], |s| both(s))?)?,
                ex(
                    ("大きすぎれば下界", "a lower bound when too large"),
                    ["ε_0", "ω^ω^ω"].iter().map(|s| bound(s)).collect::<Result<Vec<_>, _>>()?.into_iter().flatten().collect(),
                )?,
            ]
        }
        "thm52" => {
            let g = |m: usize| Bracket::thm52(m).battle_length(1_000).ok_or("G");
            vec![
                exf("a_{n+2} = (((a_n)))", (2..5).map(|n| format!("a_{n} = {}", Bracket::thm52_a(n))).collect())?,
                exf("a′_m = ()a_m", [2, 0, 1, 3].iter().map(|&m| format!("a′_{m} = {}", Bracket::thm52(m))).collect())?,
                exf("G(m) = ℓ(a′_m)", vec![format!("G(0) = {}{}G(1) = {}", g(0)?, comma(), g(1)?)])?,
            ]
        }

        // ---- 基本列
        "cnf-fs" => vec![
            exf("(β + 1)[n] = β", fss(&[("ω^2 + 1", 3), ("ω + 5", 2), ("ω^ω + 1", 4), ("7", 3)])?)?,
            exf(
                "(β + ω^{γ+1})[n] = β + ω^γ·n",
                fss(&[("ω^ω + ω^2", 3), ("ω", 5), ("ω^2", 2), ("ω^3 + ω", 4), ("ω^(ω + 1)", 2)])?,
            )?,
            ex(("係数のある項 ω^γ·c", "a term ω^γ·c"), fss(&[("ω^2·2", 3), ("ω·3", 4), ("ω^ω·2", 2), ("ω^3·2 + ω·5", 2)])?)?,
            exf(
                "(β + ω^λ)[n] = β + ω^{λ[n]}",
                fss(&[("ω^(ω^2)", 3), ("ω^ω", 3), ("ω^(ω·2)", 2), ("ω^(ω^ω)", 2), ("ω^(ω + 1) + ω^ω", 3)])?,
            )?,
            exf("ε₀[n + 1] = ω^{ε₀[n]}", fss(&[("ε_0", 3), ("ε_0", 0), ("ε_0", 1), ("ε_0", 2), ("ε_0", 4)])?)?,
        ],
        "fs" => vec![
            exf("(α + 1)[n] = α", fss(&[("ω + 1", 3), ("ε_0 + 1", 2), ("φ(2, 0) + 2", 5)])?)?,
            exf("(β + P)[n] = β + P[n]", fss(&[("ε_0 + ω", 3), ("ε_0·2", 2), ("φ(2, 0) + ε_0", 2), ("ω^(ε_0 + 1) + ω", 4)])?)?,
            exf("ω^{b+1}[n] = ω^b·n", fss(&[("ω^2", 3), ("ω^(ε_0 + 1)", 2), ("ω^(ω + 1)", 3)])?)?,
            exf("ω^λ[n] = ω^{λ[n]}", fss(&[("ω^ω", 3), ("ω^(ω^2)", 2), ("ω^(ε_0·2)", 2)])?)?,
            exf("φ(a, λ)[n] = φ(a, λ[n])", fss(&[("ε_ω", 3), ("ε_(ε_0)", 2), ("φ(2, ω)", 2), ("φ(ω, ω)", 3)])?)?,
            exf("φ(a + 1, 0)[n] = φ(a, ·)ⁿ(0)", fss(&[("φ(2, 0)", 2), ("ε_0", 3), ("φ(3, 0)", 2), ("φ(ω + 1, 0)", 2)])?)?,
            exf("φ(a + 1, b + 1)[n] = φ(a, ·)ⁿ(φ(a + 1, b) + 1)", fss(&[("ε_1", 2), ("ε_2", 1), ("φ(2, 1)", 2)])?)?,
            exf("φ(λ, 0)[n] = φ(λ[n], 0)", fss(&[("φ(ω, 0)", 3), ("φ(ε_0, 0)", 2), ("φ(ω^2, 0)", 2)])?)?,
            exf("φ(λ, b + 1)[n] = φ(λ[n], φ(λ, b) + 1)", fss(&[("φ(ω, 1)", 2), ("φ(ε_0, 1)", 1), ("φ(ω, 2)", 1)])?)?,
        ],
        "nat-worm-fs" => {
            let less = |s: &str, n: usize| -> Result<String, String> {
                let a = worm(s)?;
                let b = a.battle_step(n).ok_or("A{n}")?;
                Ok(format!("o({b}) = {} < {} = o({a})", b.ordinal(), a.ordinal()))
            };
            // 標準形の worm だけ：閉じた形 D と実際の基本列の順序数が同じことを確かめる
            let closed = |s: &str, n: usize| -> Result<Option<String>, String> {
                let a = worm(s)?;
                if !headbody::is_bnf(&a) {
                    return Ok(None);
                }
                let b = a.battle_step(n).ok_or("A{n}")?;
                let (oa, ob) = (Veblen::from(&a.ordinal()), Veblen::from(&b.ordinal()));
                // 閉じた形は極限順序数だけ（後続順序数なら A{n} は先頭の 0 を消すだけ）
                let Some(d) = hierarchy::worm_fs_closed(&oa, n) else {
                    return Ok(None);
                };
                if d != ob {
                    return Err(format!("D({oa}, {}) = {d} ≠ {ob}", n + 1));
                }
                Ok(Some(format!("o(({a}){{{n}}}) = o({b}) = {ob} = D({oa}, {})", n + 1)))
            };
            vec![
                exf("(0B){n} = B", each(&[("0 2 1", 3), ("0", 5), ("0 0 1", 2), ("0 1 0 1", 1)], |(s, n)| worm_fs(s, *n))?)?,
                ex(
                    ("(VU){n} = V′…V′U（U ≠ ⊤）", "(VU){n} = V′…V′U (U ≠ ⊤)"),
                    each(&[("2 0 2", 1), ("1 0 1", 2), ("2 1 0 3", 1), ("3 2 1", 1)], |(s, n)| worm_fs(s, *n))?,
                )?,
                ex(
                    ("h 未満の文字がない（U = ⊤）", "no letter below h (U = ⊤)"),
                    each(&[("1 2", 2), ("1", 3), ("2", 2), ("1 1", 1), ("2 3 2", 1)], |(s, n)| worm_fs(s, *n))?,
                )?,
                exf("o(A{n}) < o(A)", each(&[("2 0 2", 1), ("1 1", 2), ("2", 3), ("1 0 1", 2)], |(s, n)| less(s, *n))?)?,
                ex(
                    ("A が標準形なら o(A{n}) = D(o(A), n + 1)", "A in normal form: o(A{n}) = D(o(A), n + 1)"),
                    [("1 1", 2), ("2", 1), ("1 2", 1), ("0 1 1", 2)]
                        .iter()
                        .map(|(s, n)| closed(s, *n))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect(),
                )?,
            ]
        }
        "bracket-fs" => {
            let less = |s: &str, n: usize| -> Result<String, String> {
                let a = bracket(s)?;
                let b = a.fundamental(n).ok_or("a{n}")?;
                Ok(format!("o*({b}) = {} < {} = o*({a})", b.ordinal(), a.ordinal()))
            };
            vec![
                ex(
                    ("a₁ = ⊤ なら最初の文字を消す", "a₁ = ⊤: drop the first letter"),
                    each(&[("()(())", 2), ("()", 3), ("()()(())", 1), ("()((()))", 2)], |(s, n)| bracket_fs(s, *n))?,
                )?,
                ex(
                    ("a₁ より小さい文字がある（c ≠ ⊤）", "a letter below a₁ (c ≠ ⊤)"),
                    each(&[("((()))()", 1), ("(())()(())", 1), ("(()())(())", 1), ("((()))(())", 2)], |(s, n)| bracket_fs(s, *n))?,
                )?,
                ex(
                    ("a₁ より小さい文字がない（c = ⊤）", "no letter below a₁ (c = ⊤)"),
                    each(&[("((()))", 1), ("(())", 2), ("(()())", 1), ("(())(())", 1)], |(s, n)| bracket_fs(s, *n))?,
                )?,
                exf("o*(a{n}) < o*(a)", each(&[("((()))", 1), ("(()())", 2), ("((()))()", 1)], |(s, n)| less(s, *n))?)?,
            ]
        }
        "worm-fs" => {
            let differs = |s: &str, n: usize| -> Result<String, String> {
                let a = ord(s)?;
                Ok(format!("{s}{{{n}}} = {}{}{s}[{n}] = {}", worm_seq(&a, n)?, comma(), a.fundamental(n as u64).ok_or("fs")?))
            };
            vec![
                exf(
                    "α{n} = o*(a{n})",
                    each(&[("ε_0", 1), ("ε_0", 2), ("φ(2, 0)", 1), ("ε_1", 1)], |(s, n)| Ok(format!("{s}{{{n}}} = {}", worm_seq(&ord(s)?, *n)?)))?,
                )?,
                ex(("標準の基本列とは少しずれる", "slightly different from α[n]"), each(&[("ω^2", 1), ("ω", 1), ("ω^ω", 2)], |(s, n)| differs(s, *n))?)?,
                exf("D(R + ω^{β+1}, n) = R + ω^β·n + 1", each(&[("ω^2", 2), ("ω·2", 1), ("ω^3", 2), ("ω^ω + ω", 2)], |(s, n)| worm_seq_closed(s, *n))?)?,
                exf("D(ω, n) = n", each(&[("ω", 2), ("ω", 0), ("ω", 4)], |(s, n)| worm_seq_closed(s, *n))?)?,
                exf("D(R + ω^λ, n) = R + ω^{D(λ, n)}", each(&[("ω^ω", 2), ("ω^(ω·2)", 1), ("ω^ω^ω", 1), ("ω^ω·2", 1)], |(s, n)| worm_seq_closed(s, *n))?)?,
            ]
        }
        "rcbi-fs" => vec![
            ex(("成分がない：零", "no conjuncts: zero"), each(&["T & T", "T"], |s| rcbi_form(s))?)?,
            ex(
                ("成分がすべて ⟨1⟩₁B：後続形", "all conjuncts ⟨1⟩₁B: successor form"),
                each(&["<1>_1 <1>_1 T & <1>_1 T", "<1>_1 T", "<1>_1 D T", "<1>_1 <1>_2 T"], |s| rcbi_form(s))?,
            )?,
            ex(
                ("↓B か ⟨i⟩_α B（α ≥ 2）がある：極限形", "some ↓B or ⟨i⟩_α B (α ≥ 2): limit form"),
                each(&["D T", "<1>_2 T", "<2>_2 T", "<1>_1 T & D T"], |s| rcbi_form(s))?,
            )?,
            exf(
                "(⟨i⟩_α A′)_{n+1} = ⟨i⟩_{α−1}(A′ ∧ (A)_n)",
                each(&[("<1>_2 T", 3), ("<1>_3 T", 2), ("<1>_2 <1>_1 T", 2), ("<2>_3 T", 2)], |(s, n)| rcbi_approx(s, *n))?,
            )?,
            exf("(⟨2⟩₂A′)_{n+1} = ⟨1⟩₁(A′ ∧ ↓(A)_n)", each(&[("<2>_2 T", 2), ("<2>_2 T", 3), ("<2>_2 <1>_1 T", 2)], |(s, n)| rcbi_approx(s, *n))?)?,
            ex(("(↓C)_n（C が極限形でない）", "(↓C)_n (C not of limit form)"), each(&[("D T", 2), ("D T", 3), ("D <1>_1 T", 2)], |(s, n)| rcbi_approx(s, *n))?)?,
            ex(
                ("(↓C)_n = ⟨1⟩_n↓(C)_n（C が極限形）", "(↓C)_n = ⟨1⟩_n↓(C)_n (C of limit form)"),
                each(&[("D <1>_2 T", 2), ("D D T", 2), ("D <2>_2 T", 2)], |(s, n)| rcbi_approx(s, *n))?,
            )?,
            ex(
                ("成分が 2 つ以上で ↓ がある：↓ の成分を近似", "two or more conjuncts with ↓: approximate the ↓ ones"),
                each(&[("D T & <1>_2 T", 2), ("D T & D <1>_1 T", 2)], |(s, n)| rcbi_approx(s, *n))?,
            )?,
            ex(
                ("成分が 2 つ以上で ↓ がない：巡回シフト", "two or more conjuncts without ↓: cyclic shift"),
                each(&[("<1>_2 T & <1>_1 <1>_1 T", 2), ("<1>_2 T & <1>_3 T", 2), ("<2>_2 T & <1>_2 T", 2)], |(s, n)| rcbi_approx(s, *n))?,
            )?,
        ],

        // ---- 順序数上の関数
        "add" => vec![
            exf("α + 0 = α", evs(&["ω^2 + 0", "ε_0 + 0", "3 + 0"])?)?,
            exf("α + (β + 1) = (α + β) + 1", evs(&["ω + 1 + 1", "ε_0 + 2", "ω·2 + 3"])?)?,
            ex(("β が極限なら sup_{γ<β} (α + γ)", "limit β: sup_{γ<β} (α + γ)"), evs(&["1 + ω", "5 + ω^2", "ω + ε_0"])?)?,
            ex(("小さい主項は消える", "smaller principal terms vanish"), evs(&["ω^2 + ω·3 + ω^3", "ω + ω^2", "ε_0 + ε_1", "ω^ω·5 + ψ(0)"])?)?,
            ex(("同じ主項は係数を足す", "equal principal terms add coefficients"), evs(&["ω^2·2 + ω + ω^2", "ω + ω", "ε_0·2 + ε_0", "ω^3 + 1 + ω^3"])?)?,
        ],
        "mul" => vec![
            exf("α·0 = 0", evs(&["ω·0", "ε_0·0"])?)?,
            exf("α·(β + 1) = α·β + α", evs(&["(ω + 1)·2", "(ω^2 + ω)·3", "(ε_0 + 1)·2"])?)?,
            ex(("β が極限なら sup_{γ<β} α·γ", "limit β: sup_{γ<β} α·γ"), evs(&["2·ω", "100·ω", "3·ω^2"])?)?,
            exf("α·ω^f = ω^{e₁ + f}", evs(&["(ω^2 + 1)·ω", "ω·ω", "(ω + 3)·ω^2", "ε_0·ω"])?)?,
            ex(("右の分配法則", "right distributivity"), evs(&["(ω + 1)·(ω + 1)", "(ω + 2)·(ω·2 + 3)", "ω^2·(ω + 1)"])?)?,
        ],
        "pow" => vec![
            exf("α^0 = 1", evs(&["ω^0", "(ε_0)^0", "5^0"])?)?,
            exf("α^(β + 1) = α^β·α", evs(&["(ω + 1)^2", "(ω·2)^2", "2^3", "(ω^2 + 1)^3"])?)?,
            ex(("β が極限なら sup_{γ<β} α^γ", "limit β: sup_{γ<β} α^γ"), evs(&["2^ω", "3^ω", "10^ω"])?)?,
            exf("1^β = 1", evs(&["1^ω", "1^ε_0"])?)?,
            ex(("0^β = 0（β ≥ 1）", "0^β = 0 (β ≥ 1)"), evs(&["0^ω", "0^3"])?)?,
            exf("n^(ω·γ) = ω^γ", evs(&["2^(ω·3)", "3^(ω^2)", "2^(ω^ω)", "5^(ω·2)"])?)?,
            exf("α^λ = ω^{e₁·λ}", evs(&["(ω + 1)^ω", "(ω^ω + 1)^ω", "(ω^2 + ω)^ω", "(ε_0)^ω"])?)?,
            exf("α^(λ + m) = α^λ·α^m", evs(&["2^(ω + 1)", "(ω + 1)^(ω + 1)", "3^(ω·2 + 2)"])?)?,
        ],
        "phi" => vec![
            exf("φ(0, β) = ω^β", evs(&["φ(0, 3)", "φ(0, ω)", "φ(0, ε_0 + 1)"])?)?,
            ex(("α > 0：共通の不動点を並べる", "α > 0: common fixed points"), evs(&["φ(1, φ(2, 0))", "φ(0, ε_0)", "φ(1, φ(ω, 0))", "φ(2, φ(3, 0))"])?)?,
            ex(
                ("α₁ < α₂ かつ β₁ < φ(α₂, β₂)", "α₁ < α₂ and β₁ < φ(α₂, β₂)"),
                cmps(&[("φ(1, ω)", "φ(2, 0)"), ("φ(0, ε_0 + 1)", "φ(1, 1)"), ("φ(1, φ(2, 0) + 1)", "φ(2, 1)")])?,
            )?,
            ex(("α₁ = α₂ かつ β₁ < β₂", "α₁ = α₂ and β₁ < β₂"), cmps(&[("φ(1, 2)", "φ(1, 3)"), ("φ(2, ω)", "φ(2, ε_0)"), ("φ(ω, 0)", "φ(ω, 1)")])?)?,
            ex(
                ("α₁ > α₂ かつ φ(α₁, β₁) < β₂", "α₁ > α₂ and φ(α₁, β₁) < β₂"),
                cmps(&[("φ(1, 0)", "φ(0, ε_0 + 1)"), ("φ(2, 0)", "φ(1, φ(2, 0) + 1)"), ("φ(ω, 0)", "φ(2, φ(ω, 0) + 1)")])?,
            )?,
        ],
        "eps" => vec![
            exf("ε_α = φ(1, α)", evs(&["φ(1, 2)", "φ(1, ω)", "φ(1, ε_0)"])?)?,
            ex(("ω^ξ = ξ の解", "a solution of ω^ξ = ξ"), evs(&["ω^ε_0", "ω^ε_1", "ω^φ(2, 0)", "ω^ε_(ε_0)"])?)?,
        ],
        "hyp" => vec![
            exf("e(0) = −1 + ω^0 = 0", evs(&["e(0)"])?)?,
            ex(("ξ ≥ 1 なら e(ξ) = ω^ξ", "e(ξ) = ω^ξ for ξ ≥ 1"), evs(&["e(ω)", "e(1)", "e(ε_0)", "e(ω + 1)"])?)?,
            exf("e^{α+β} = e^α ∘ e^β", evs(&["e^2(1)", "e^3(1)", "e^2(ω)", "e^(ω + 2)(1)"])?)?,
            exf("e^{ω^γ}(0) = 0", evs(&["e^ω(0)", "e^(ω^2)(0)", "e^(ε_0)(0)"])?)?,
            exf("e^{ω^γ}(1 + β) = φ(γ, β)", evs(&["e^ω(1)", "e^ω(2)", "e^ω(ω)", "e^(ω^2)(1)", "e^(ω^ω)(1)"])?)?,
            ex(
                ("e^α は Cantor 標準形の項ごとに右から", "e^α term by term, from the right"),
                evs(&["e^(ω + 1)(1)", "e^(ω·2)(1)", "e^(ω^2 + ω)(1)", "e^(ω + 2)(ω)"])?,
            )?,
        ],
        "Omega" => vec![
            ex(("α < Ω なら φ(α, Ω) = Ω", "φ(α, Ω) = Ω for α < Ω"), evs(&["φ(2, Ω)", "φ(0, Ω)", "φ(ε_0, Ω)", "φ(ψ(0), Ω)"])?)?,
            exf("φ(Ω, 0) = Ω", evs(&["φ(Ω, 0)"])?)?,
            ex(
                ("記号として大小・+ に使える", "a symbol for comparisons and sums"),
                vec![ev("ω + Ω")?, cmp_ex("φ(ε_0, 0)", "Ω")?, cmp_ex("Ω + ω", "Ω·2")?, ev("Ω^2")?],
            )?,
        ],
        "psi" => vec![
            ex(
                ("ψ(0) = Γ₀ は φ(·, 0) の不動点", "ψ(0) = Γ₀ is a fixed point of φ(·, 0)"),
                evs(&["φ(ψ(0), 0)", "φ(0, ψ(0))", "ε_(ψ(0))", "φ(ψ(1), 0)"])?,
            )?,
            ex(("ψ(ξ) はいつも可算", "ψ(ξ) is always countable"), cmps(&[("ψ(Ω·2)", "Ω"), ("ψ(ε_(Ω + 1))", "Ω"), ("ψ(Ω^Ω)", "Ω")])?)?,
            ex(
                ("ξ ∉ C(ξ) なら ψ(z) に崩す", "ξ ∉ C(ξ): collapse to ψ(z)"),
                // 崩れて書き方が変わるものだけ
                ["ψ(Ω + ψ(Ω·2 + 1))", "ψ(ψ(Ω))", "ψ(ψ(Ω·2))", "ψ(Ω + ψ(Ω + 1))", "ψ(ψ(ε_(Ω + 1)))"]
                    .iter()
                    .map(|s| {
                        let e = expr::eval_str(s)?;
                        let (input, value) = (e.input.to_string(), e.value.to_string());
                        Ok((input != value).then(|| format!("{input} = {value}")))
                    })
                    .collect::<Result<Vec<_>, String>>()?
                    .into_iter()
                    .flatten()
                    .collect(),
            )?,
        ],
        "normal" => vec![
            ex(
                ("β < φ(α, β) でなければ β が主項", "if not β < φ(α, β), β is the principal term"),
                evs(&["φ(0, φ(1, 0))", "φ(1, φ(2, 0))", "φ(0, φ(ω, 1))"])?,
            )?,
            ex(("主項の和 P₁·c₁ + …", "a sum of principal terms P₁·c₁ + …"), evs(&["φ(0, φ(1, 0)) + 2 + ω", "ε_0 + ω + ε_0", "ψ(0) + ε_0·2 + 1"])?)?,
            ex(("書き方 n・ω^β・ε_β", "writing n, ω^β, ε_β"), evs(&["φ(1, 2) + φ(0, 2) + φ(0, 0)·3", "φ(0, φ(0, 1))", "φ(1, φ(1, 0))"])?)?,
            ex(
                ("強臨界数 s は φ(s, 0) とみて比べる", "a strongly critical s compares as φ(s, 0)"),
                cmps(&[("φ(ε_0, 0)", "ψ(0)"), ("φ(ψ(0), 1)", "ψ(1)"), ("Ω", "φ(ψ(0), 0)")])?,
            )?,
        ],
        "cnf" => {
            let terms = |s: &str| -> Result<String, String> {
                let a = ord(s)?;
                let ts: Vec<String> = a.cnf().iter().map(|(e, c)| format!("({e}, {c})")).collect();
                Ok(t2(format!("{a}：指数と係数は {}", ts.join("、")), format!("{a}: exponents and coefficients {}", ts.join(", "))))
            };
            let lex = |a: &str, b: &str| -> Result<String, String> { Ok(format!("{a} {} {b}", rel(ord(a)?.cmp(&ord(b)?)))) };
            let fixed = |s: &str| -> Result<String, String> {
                let a = ord(s)?;
                match a.cnf().as_slice() {
                    [(e, 1)] if *e == a => Ok(format!("{a} = ω^{}", grouped(&e.to_string()))),
                    _ => Err(format!("{a} は ω^ξ = ξ の解ではない")),
                }
            };
            vec![
                ex(
                    ("α = ω^{α₁}·c₁ + … + ω^{α_k}·c_k", "α = ω^{α₁}·c₁ + … + ω^{α_k}·c_k"),
                    each(&["ω^ω·2 + ω^3 + 4", "ω^2 + ω·3 + 1", "7", "ω^(ω + 1)·3 + ω^ω"], |s| terms(s))?,
                )?,
                ex(
                    ("比較は辞書式", "lexicographic comparison"),
                    each(&[("ω^2 + 1", "ω·5 + 7"), ("ω^3 + ω", "ω^3 + 5"), ("ω^ω·2", "ω^ω + ω^5"), ("ω^2·3 + 1", "ω^2·3 + ω")], |(a, b)| lex(a, b))?,
                )?,
                ex(("ε₀ で指数が小さくならなくなる", "at ε₀ the exponent stops decreasing"), each(&["ε_0", "ε_1", "φ(2, 0)"], |s| fixed(s))?)?,
            ]
        }
        "hyper-nf" => {
            let h = |s: &str| -> Result<String, String> { Ok(format!("{s} = {}", notation::render(&ord(s)?, Notation::Hyper).text)) };
            vec![
                exf("ξ = e^α(1)", each(&["φ(2, 0)", "ε_0", "ω", "φ(ω, 0)"], |s| h(s))?)?,
                ex(("ξ = e^α(β)、β は分解できる", "ξ = e^α(β), β decomposable"), each(&["ε_(ω + 1)", "ω^(ω + 1)", "ε_1"], |s| h(s))?)?,
                exf("ω^{1+β} = e(1 + β)", each(&["ω^ω", "ω^2", "ω^(ε_0 + 1)"], |s| h(s))?)?,
                ex(("強臨界数は原子", "strongly critical numbers are atoms"), each(&["ψ(ε_(Ω + 1))", "ε_(ψ(0) + 1)", "ω^(ψ(Ω) + 1)"], |s| h(s))?)?,
            ]
        }
        "hardy" => {
            let h = |(s, n): &(&str, u128)| -> Result<String, String> {
                Ok(format!("H_{}({n}) = {}", sub(s), hierarchy::hardy(&ord(s)?, *n, Budget::default()).ok_or("hardy")?))
            };
            let big = |s: &str| -> Result<Option<String>, String> {
                let v = hierarchy::hardy_big(&ord(s)?, &BigNat::from(3u128), BigBudget { max_steps: 20_000, max_bits: 1 << 16 }).ok_or("hardy_big")?;
                Ok((!matches!(v, hierarchy::BigValue::Exact(_))).then(|| format!("H_{}(3){}{}", sub(s), colon(), v.describe())))
            };
            vec![
                exf("H_0(n) = n", each(&[("0", 3), ("0", 7)], h)?)?,
                exf("H_{α+1}(n) = H_α(n + 1)", each(&[("5", 3), ("1", 0), ("ω + 1", 3)], h)?)?,
                exf("H_λ(n) = H_{λ[n]}(n)", each(&[("ω", 3), ("ω·2", 3), ("ω^2", 3), ("ω^2 + ω", 2)], h)?)?,
                ex(
                    ("大きな値は下界で答える", "large values as lower bounds"),
                    ["ε_0", "ω^ω"].iter().map(|s| big(s)).collect::<Result<Vec<_>, _>>()?.into_iter().flatten().collect(),
                )?,
            ]
        }
        "fgh" => {
            let f = |(s, n): &(&str, u128)| -> Result<String, String> {
                Ok(format!("f_{}({n}) = {}", sub(s), hierarchy::fast_growing(&ord(s)?, *n, Budget::default()).ok_or("fgh")?))
            };
            let fh = |(s, n): &(&str, u128)| -> Result<String, String> {
                let w = Veblen::omega_pow(ord(s)?);
                let v = hierarchy::hardy(&w, *n, Budget::default()).ok_or("hardy")?;
                Ok(format!("{} = H_{}({n}) = {v}", f(&(s, *n))?.split(" = ").next().unwrap_or_default(), sub(&w.to_string())))
            };
            vec![
                exf("f_0(n) = n + 1", each(&[("0", 3), ("0", 10)], f)?)?,
                exf("f_{α+1}(n) = f_αⁿ(n)", each(&[("1", 3), ("2", 3), ("1", 5)], f)?)?,
                exf("f_λ(n) = f_{λ[n]}(n)", each(&[("ω", 2), ("ω", 1), ("ω + 1", 1)], f)?)?,
                exf("f_α = H_{ω^α}", each(&[("2", 3), ("1", 4), ("0", 5)], fh)?)?,
            ]
        }

        // ---- 表記と順序数の対応
        "worm" => {
            let only_lt = |pairs: &[(&str, &str)], n: u32| -> Result<Vec<String>, String> {
                Ok(pairs.iter().map(|(a, b)| worm_lt(a, b, n)).collect::<Result<Vec<_>, _>>()?.into_iter().filter(|(lt, _)| *lt).map(|(_, s)| s).collect())
            };
            // <₀ だが <₁ でない組
            let stronger = |a: &str, b: &str| -> Result<Option<String>, String> {
                let ((l0, s0), (l1, s1)) = (worm_lt(a, b, 0)?, worm_lt(a, b, 1)?);
                Ok((l0 && !l1).then(|| format!("{s0}{}{s1}", comma())))
            };
            let equiv = |a: &str, b: &str| -> Result<Option<String>, String> {
                let (x, y) = (worm(a)?, worm(b)?);
                Ok(x.equiv(&y).then(|| format!("{x} ≡ {y}")))
            };
            vec![
                exf("A <₀ B :⟺ B ⊢ ⟨0⟩A", only_lt(&[("1 1", "2"), ("0 0 0", "1"), ("1 0 1", "1 1"), ("2 0 1", "2 1")], 0)?)?,
                exf("A <₁ B :⟺ B ⊢ ⟨1⟩A", only_lt(&[("1 0 1", "1 1"), ("0 0 0", "1"), ("1 1", "2")], 1)?)?,
                ex(
                    ("<₁ は <₀ より強い", "<₁ is stronger than <₀"),
                    [("1 1", "1 0 1 1"), ("2", "2 0 1 0 2"), ("1", "0 1 0 1")]
                        .iter()
                        .map(|(a, b)| stronger(a, b))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect(),
                )?,
                exf(
                    "A ≡ B",
                    [("1 0", "1"), ("2 0 1", "2"), ("1 2 0 1", "1 2"), ("0 1 0", "0 1")]
                        .iter()
                        .map(|(a, b)| equiv(a, b))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect(),
                )?,
                ex(("o は順序を保つ", "o preserves the order"), each(&[("1 1", "2"), ("1 0 1", "1 1"), ("2 0 2", "3")], |(a, b)| worm_o_cmp(a, b))?)?,
            ]
        }
        "worm-o" => {
            let o = |s: &str| -> Result<String, String> {
                let a = worm(s)?;
                Ok(format!("o({a}) = {}", a.ordinal()))
            };
            let same = |a: &str, b: &str| -> Result<Option<String>, String> {
                let (x, y) = (worm(a)?, worm(b)?);
                Ok((x.ordinal() == y.ordinal()).then(|| format!("o({x}) = {} = o({y})", x.ordinal())))
            };
            vec![
                exf("o(⊤) = 0", vec![format!("o(⊤) = {}", Worm::<u32>::top().ordinal())])?,
                exf(
                    "1 + o(A) = ω^{o(A_k↓)} + … + ω^{o(A₁↓)}",
                    each(&["1 0 2", "0", "1", "0 1", "1 1", "2", "1 0 1", "2 1"], |s| o(s))?,
                )?,
                exf(
                    "A ≡ B ⟺ o(A) = o(B)",
                    [("1 0", "1"), ("2 0 1", "2"), ("1 2 0 1", "1 2")].iter().map(|(a, b)| same(a, b)).collect::<Result<Vec<_>, _>>()?.into_iter().flatten().collect(),
                )?,
            ]
        }
        "worm-o-transfinite" => {
            let o = |s: &str| -> Result<String, String> {
                let a = s.parse::<Worm<Veblen>>().map_err(|e| e.to_string())?;
                Ok(format!("o({a}) = {}", a.ordinal()))
            };
            vec![
                exf("o(A) = e^μ(o(μ↓A))", each(&["⟨ω^2⟩", "⟨ω⟩", "⟨ω⟩⟨ω⟩", "⟨ω + 1⟩", "⟨ε_0⟩", "⟨ω·2⟩"], |s| o(s))?)?,
                exf("o(H 0 B) = o(B) + 1 + o(H)", each(&["⟨ω⟩⟨0⟩⟨ω⟩", "⟨ω⟩⟨0⟩", "⟨1⟩⟨0⟩⟨ω⟩"], |s| o(s))?)?,
                ex(("文字が自然数なら同じ値", "natural-number letters: the same value"), each(&["⟨1⟩⟨1⟩", "⟨2⟩⟨0⟩⟨2⟩", "⟨1⟩⟨0⟩⟨1⟩"], |s| o(s))?)?,
            ]
        }
        "worm-inverse" => {
            let inv = |s: &str| -> Result<String, String> { Ok(format!("inv({s}) = {}", Worm::<Veblen>::from_veblen(&ord(s)?))) };
            vec![
                ex(("k ≥ 2：最後の項を切り離す", "k ≥ 2: split off the last term"), each(&["ω·2", "ω^ω + 1", "ε_0 + 1", "ω^2 + ω"], |s| inv(s))?)?,
                ex(("k = 1、β < ω^β：1↑inv(β)", "k = 1, β < ω^β: 1↑inv(β)"), each(&["ω^ω", "ω", "ω^2", "ω^(ε_0 + 1)"], |s| inv(s))?)?,
                ex(("ω^β = β = φ(a, b)：ω^a↑inv(1 + b)", "ω^β = β = φ(a, b): ω^a↑inv(1 + b)"), each(&["φ(2, 0)", "ε_0", "ε_1", "φ(ω, 0)"], |s| inv(s))?)?,
                ex(("強臨界数 s：⟨s⟩⊤", "strongly critical s: ⟨s⟩⊤"), each(&["ψ(0)", "ψ(1)", "Ω"], |s| inv(s))?)?,
            ]
        }
        "bnf" => {
            let cands: Vec<Worm> = ["1 1 0 2", "1 0 1", "0 1 1", "2 0 1", "1 0", "2 1 1", "1 0 2 0 1", "2 2 0 1", "3 0 1 2"]
                .iter()
                .map(|s| worm(s))
                .collect::<Result<_, _>>()?;
            let label = |w: &Worm, normal: bool| format!("{w}{}{}", colon(), if normal { tr("標準形", "normal form") } else { tr("標準形でない", "not normal form") });
            let (yes, no): (Vec<&Worm>, Vec<&Worm>) = cands.iter().partition(|w| headbody::is_bnf(w));
            vec![
                ex(("どの成分も A_{i+1} ⊴ A_i", "A_{i+1} ⊴ A_i for every component"), yes.iter().map(|w| label(w, true)).collect())?,
                ex(("A_{i+1} ⊴ A_i でない所がある", "some A_{i+1} ⊴ A_i fails"), no.iter().map(|w| label(w, false)).collect())?,
                ex(("同値な標準形がただ 1 つ（Thm 11）", "a unique equivalent normal form (Thm 11)"), no.iter().map(|w| format!("{w} ≡ {}", w.normal_form())).collect())?,
            ]
        }
        "pi-ordinal" => {
            let ws: Vec<Worm> = ["2 1 0 1", "3 1 2 0 1", "2 2 1"].iter().map(|s| worm(s)).collect::<Result<_, _>>()?;
            let mut first = Vec::new();
            let mut zero = Vec::new();
            let mut next = Vec::new();
            for a in &ws {
                let os = a.pi_ordinals(3);
                let hd = a.head(1).down(1).ok_or("down")?;
                if Veblen::from(&hd.ordinal()) != Veblen::from(&os[1]) {
                    return Err(format!("Ω_1({a})"));
                }
                first.push(format!("Ω_1({a}) = o({hd}) = {}", os[1]));
                zero.push(format!("Ω_0({a}) = o({a}) = {}", os[0]));
                next.push(format!("Ω_2({a}) = ℓ({}) = {}", os[1], os[2]));
            }
            vec![exf("Ω_ξ(A) = o(ξ↓h_ξ(A))", first)?, exf("Ω₀ = o", zero)?, exf("Ω_{n+1}(A) = ℓ(Ω_n(A))", next)?]
        }
        "bracket" => {
            let star = |s: &str| -> Result<String, String> {
                let a = bracket(s)?;
                Ok(format!("a = {a}{}a* = {}", colon(), a.to_worm()))
            };
            let o = |s: &str| -> Result<String, String> {
                let a = bracket(s)?;
                Ok(format!("a = {a}{}a* = {}{}o*(a) = {}", colon(), a.to_worm(), comma(), a.ordinal()))
            };
            let depth = |s: &str| -> Result<String, String> {
                let a = bracket(s)?;
                let n = a.depth();
                Ok(format!("a = {a}{}N(a) = {n}{}{} ≤ {} < {}", colon(), comma(), depth_bound(n), a.ordinal(), depth_bound(n + 1)))
            };
            vec![
                exf("((a)b)* = ⟨o(a*)⟩b*", each(&["(()())()(())", "(())", "((()))(())", "(()(()))"], |s| star(s))?)?,
                exf("o*(a) = o(a*)", each(&["((()))", "()()", "(())()", "(((())))"], |s| o(s))?)?,
                exf("h(N(a)) ≤ o*(a) < h(N(a) + 1)", each(&["((()))", "(())", "(()(()))", "(((())))"], |s| depth(s))?)?,
            ]
        }
        "bracket-nf" => {
            let cands: Vec<Bracket> = ["(())()", "((()))(())", "(()())()()", "()(())", "(())(())"].iter().map(|s| bracket(s)).collect::<Result<_, _>>()?;
            let not_normal: Vec<String> = cands
                .iter()
                .filter(|a| !a.is_normal_syntactic())
                .map(|a| format!("{a}{}a* = {}{}{} {}", colon(), a.to_worm(), comma(), tr("正規形は", "its normal form is"), a.normal_form_syntactic()))
                .collect();
            vec![
                ex(("a* が BNF でなければ正規形でない", "not normal if a* is not in BNF"), not_normal)?,
                ex(
                    ("各順序数にただ 1 つ（Thm 32）", "exactly one for each ordinal (Thm 32)"),
                    each(&["ω·2", "ω", "ε_0", "ω^2 + 1", "ε_0·2"], |s| Ok(format!("{s} ↦ {}", Bracket::from_ordinal(&ord(s)?))))?,
                )?,
                ex(
                    ("順序数なしの比較", "comparison without ordinals"),
                    each(&[("()()()", "(())"), ("(())()", "(())"), ("((()))", "(()(()))"), ("(()())", "(())(())")], |(a, b)| {
                        let (x, y) = (bracket(a)?, bracket(b)?);
                        Ok(format!("{x} {} {y}", rel(x.cmp_syntactic(&y))))
                    })?,
                )?,
                ex(
                    ("順序数なしの正規形（文字の中も）", "normal form without ordinals (inside letters too)"),
                    each(&["((())())", "(())()", "(()())()", "((()())())"], |s| {
                        let a = bracket(s)?;
                        Ok(format!("{a} → {}", a.normal_form_syntactic()))
                    })?,
                )?,
            ]
        }
        "iworm" => {
            let iw = |s: &str| s.parse::<IWorm>().map_err(|e| e.to_string());
            let pi = |s: &str| -> Result<String, String> {
                let u = iw(s)?.to_worm();
                Ok(format!("π({u}) = {}", iworm::projection(&u).ok_or("π")?))
            };
            vec![
                exf(
                    "((w)v)^π = ⟨π(w^π)⟩v^π",
                    each(&["(Ω)", "()Ω", "((()))Ω", "Ω(Ω)"], |s| Ok(format!("w = {}{}w^π = {}", iw(s)?, colon(), iw(s)?.to_worm())))?,
                )?,
                ex(("文字が可算なら π(u) = o(u)", "countable letters: π(u) = o(u)"), each(&["(Ω)", "(())", "((()))", "(Ω)(Ω)"], |s| pi(s))?)?,
                ex(("Ω を含めば π(u) = ψ(−Ω + o(u))", "with Ω: π(u) = ψ(−Ω + o(u))"), each(&["ΩΩ", "Ω", "()Ω", "((()))Ω"], |s| pi(s))?)?,
                exf("p(w) = π(w^π)", each(&["((()))Ω", "Ω", "ΩΩ", "(Ω)Ω"], |s| Ok(format!("p({}) = {}", iw(s)?, iw(s)?.value())))?)?,
                ex(
                    ("p はすべての値をとる（Thm 6.36）", "p takes every value (Thm 6.36)"),
                    ["ψ(1)", "ψ(0)", "ψ(Ω)", "ψ(ε_(Ω + 1))"]
                        .iter()
                        .map(|s| Ok(IWorm::from_value(&ord(s)?).map(|w| format!("{s} = p({w})"))))
                        .collect::<Result<Vec<_>, String>>()?
                        .into_iter()
                        .flatten()
                        .collect(),
                )?,
            ]
        }
        "rcbi-order" => {
            let c = |a: &str, b: &str| -> Result<(Option<Ordering>, String), String> {
                let (x, y) = (rcbi_formula(a)?, rcbi_formula(b)?);
                let o = rcbi_order::compare(&x, &y);
                Ok((o, format!("{x} {} {y}", rcbi_rel(o))))
            };
            let only = |pairs: &[(&str, &str)], want: Ordering| -> Result<Vec<String>, String> {
                Ok(pairs.iter().map(|(a, b)| c(a, b)).collect::<Result<Vec<_>, _>>()?.into_iter().filter(|(o, _)| *o == Some(want)).map(|(_, s)| s).collect())
            };
            vec![
                exf(
                    "A <¹₁ B :⟺ B ⊢ ⟨1⟩₁A",
                    only(&[("<1>_2 T", "D T"), ("T", "<1>_1 T"), ("D T", "<2>_2 T"), ("<1>_1 <1>_1 T", "<1>_2 T")], Ordering::Less)?,
                )?,
                exf(
                    "A ≡¹₁ B :⟺ ∇A ⊣⊢ ∇B",
                    only(&[("<1>_1 T & <1>_1 T", "<1>_1 T"), ("<1>_2 T & <1>_2 T", "<1>_2 T"), ("D T & T", "D T")], Ordering::Equal)?,
                )?,
                ex(
                    ("線形で整礎（Thm 4.11）", "linear and well-founded (Thm 4.11)"),
                    vec![
                        rcbi_chain(&["T", "<1>_1 T", "<1>_2 T", "D T", "<2>_2 T", "<2>_3 T"])?,
                        rcbi_chain(&["T", "<1>_1 T", "<1>_1 <1>_1 T", "<1>_2 T", "<1>_3 T", "D T"])?,
                    ],
                )?,
            ]
        }
        "bc-tau" => {
            let f = |s: &str| s.parse::<bc::Formula>().map_err(|e| e.to_string());
            let lt = |b: &str, a: &str| -> Result<String, String> {
                let (fa, fb) = (f(a)?, f(&format!("(){b}"))?);
                let d = bc::decide(&fa, &fb);
                Ok(format!("{b} {} {a}{}{fa} ⊢ {fb} {}", if d { "◁" } else { "⋪" }, colon(), verdict(d)))
            };
            let thm = |l: &str, r: &str| -> Result<String, String> {
                let (x, y) = (f(l)?, f(r)?);
                Ok(format!("{x} ⊢ {y}{}BC {}{}RC_Γ₀ {}", colon(), verdict(bc::decide(&x, &y)), comma(), verdict(bc::decide_tau(&x, &y))))
            };
            vec![
                exf("b ◁ a :⟺ BC ⊢ a ⊢ ()b", each(&[("()", "(())"), ("(())", "((()))"), ("(())", "(()())"), ("(())", "(())")], |(b, a)| lt(b, a))?)?,
                exf("((a)φ)^τ = ⟨o*(a)⟩φ^τ", each(&["((()))p", "(())p & ((()))(()())q", "(()())(())p"], |s| Ok(format!("{} ↦ {}", f(s)?, f(s)?.tau())))?)?,
                exf(
                    "BC ⊢ φ ⊢ ψ ⟺ RC_Γ₀ ⊢ φ^τ ⊢ ψ^τ",
                    each(&[("((()))p", "(())p"), ("(())p", "((()))p"), ("((()))p & (())q", "((()))(p & (())q)")], |(l, r)| thm(l, r))?,
                )?,
            ]
        }

        // ---- 体系の意味論
        "rc-frame" => {
            let d = |s: &&str| rc_ex(s).map(|(t, _)| t);
            vec![
                ex(("推移性", "transitivity"), each(&["<1><1>p |- <1>p", "<0><0>p |- <0>p", "<2><2>q |- <2>q"], d)?)?,
                ex(("単調性", "monotonicity"), each(&["<1>p |- <0>p", "<2>p |- <1>p", "<3>p |- <0>p"], d)?)?,
                exf("J", each(&["<1>p & <0>q |- <1>(p & <0>q)", "<2>p & <1>q |- <2>(p & <1>q)", "<2>p & <0>q |- <2>(p & <0>q)"], d)?)?,
                ex(("妥当でなければ反例のフレーム", "not valid: a counter-frame"), each(&["<0>p |- <1>p", "<1>p |- <1><1>p", "<1>p & <1>q |- <1>(p & q)"], d)?)?,
            ]
        }
        "rc-closure" => {
            let sizes: Vec<(String, usize, usize, usize)> =
                ["<1>p & <0>q", "<1><1>p", "<1>(<0>p & <1>q)", "<2>p & <1>q & <0>r"].iter().map(|s| rc_closure_sizes(s)).collect::<Result<_, _>>()?;
            let d = |s: &&str| rc_ex(s).map(|(t, _)| t);
            vec![
                ex(
                    ("標準木 T[A]", "the canonical tree T[A]"),
                    sizes.iter().map(|(a, n, t, _)| t2(format!("A = {a}：{n} 点、辺 {t} 本"), format!("A = {a}: {n} points, {t} edges"))).collect(),
                )?,
                ex(
                    ("推移性・単調性・J で閉じる", "close under transitivity, monotonicity and J"),
                    sizes.iter().map(|(a, _, t, all)| t2(format!("A = {a}：辺 {t} 本 → {all} 本"), format!("A = {a}: {t} edges → {all}"))).collect(),
                )?,
                ex(("根で B が真なら A ⊢ B", "B true at the root: A ⊢ B"), each(&["<1>p & <0>q |- <1>(p & <0>q)", "<2>p |- <0><1>p", "<1><1>p |- <1>p"], d)?)?,
                ex(("根で偽ならそのモデルが反例", "false at the root: the model is a counterexample"), each(&["<0>p |- <1>p", "<1>p & <1>q |- <1>(p & q)"], d)?)?,
            ]
        }
        "rcbi-frame" => {
            let d = |s: &&str| rcbi_ex(s);
            let viol = |s: &&str| -> Result<String, String> {
                let a = rcbi_formula(s)?;
                let v = rcbi::Model::of(&a, a.max_rank()).frame_violations().len();
                Ok(t2(format!("A = {a}：違反 {v}"), format!("A = {a}: {v} violations")))
            };
            vec![
                ex(("I 単調性：Rⁱ_α ⊆ Rⁱ_β（β < α）", "I monotonicity: Rⁱ_α ⊆ Rⁱ_β (β < α)"), each(&["<1>_2 T |- <1>_1 T", "<2>_3 T |- <2>_2 T", "<2>_2 T |- <1>_2 T"], d)?)?,
                ex(
                    ("II 推移性：a Rⁱ_α b Rʲ_α c ⇒ a Rʲ_α c", "II transitivity: a Rⁱ_α b Rʲ_α c ⇒ a Rʲ_α c"),
                    each(&["<2>_2 <1>_2 T |- <1>_2 T", "<1>_2 <1>_2 T |- <1>_2 T"], d)?,
                )?,
                ex(
                    ("III 連言：a Rⁱ_α b、a Rʲ_β c ⇒ b Rʲ_β c（β < α）", "III conjunction: a Rⁱ_α b, a Rʲ_β c ⇒ b Rʲ_β c (β < α)"),
                    each(&["<1>_2 T & <1>_1 D T |- <1>_2 <1>_1 D T", "<2>_3 T & <1>_2 T |- <2>_3 <1>_2 T"], d)?,
                )?,
                ex(("IV 構成：a R↓ b ⇒ a R¹_ω c", "IV construction: a R↓ b ⇒ a R¹_ω c"), each(&["D T |- <1>_w T", "D <1>_1 T |- <1>_w T"], d)?)?,
                ex(("M_A は I〜IV を満たす", "M_A satisfies I–IV"), each(&["<2>_2 T", "D T", "<1>_2 T", "D D T"], viol)?)?,
            ]
        }
        "rcbi-model" => {
            let size = |s: &str| -> Result<(String, usize, usize), String> {
                let a = rcbi_formula(s)?;
                let k = a.max_rank();
                Ok((a.to_string(), rcbi::Model::of(&a, k).num_points(), rcbi::Model::of_unshared(&a, k).num_points()))
            };
            let points = |s: &&str| -> Result<String, String> {
                let (a, n, _) = size(s)?;
                Ok(t2(format!("A = {a}：M_A は {n} 点"), format!("A = {a}: M_A has {n} points")))
            };
            let shared = |s: &&str| -> Result<String, String> {
                let (a, n, u) = size(s)?;
                Ok(t2(format!("A = {a}：{n} 点（まとめなければ {u} 点）"), format!("A = {a}: {n} points ({u} without merging)")))
            };
            let d = |s: &&str| rcbi_ex(s);
            vec![
                ex(("前モデルとコピー点を閉じる", "close the pre-model with copy points"), each(&["D D T", "<2>_2 T", "D T", "<1>_2 <2>_2 T"], points)?)?,
                ex(("根で B が真なら A ⊢ B", "B true at the root: A ⊢ B"), each(&["<2>_2 T |- <1>_1 D T", "D T |- <1>_w T", "<2>_2 T |- <1>_2 T"], d)?)?,
                ex(("根で B が偽なら A ⊬ B", "B false at the root: A ⊬ B"), each(&["<1>_2 T |- D T", "D T |- <2>_2 T", "<1>_1 T |- <1>_2 T"], d)?)?,
                ex(
                    ("中間点をまとめる（wormlab）", "merging intermediate points (wormlab)"),
                    each(&["D D (<1>_2 T & <1>_2 T)", "D (D T & D <1>_1 T)", "D D D D T"], shared)?,
                )?,
            ]
        }
        _ => Vec::new(),
    })
}

/// 例のある鍵（テストで、すべて例が出ることを確かめる）。
pub const KEYS_WITH_EXAMPLES: &[&str] = &[
    "worm-battle",
    "bracket-battle",
    "ordinal-battle",
    "rcbi-battle",
    "battle-length",
    "thm52",
    "cnf-fs",
    "fs",
    "nat-worm-fs",
    "bracket-fs",
    "worm-fs",
    "rcbi-fs",
    "add",
    "mul",
    "pow",
    "phi",
    "eps",
    "hyp",
    "Omega",
    "psi",
    "normal",
    "cnf",
    "hyper-nf",
    "hardy",
    "fgh",
    "worm",
    "worm-o",
    "worm-o-transfinite",
    "worm-inverse",
    "bnf",
    "pi-ordinal",
    "bracket",
    "bracket-nf",
    "iworm",
    "rcbi-order",
    "bc-tau",
    "rc-frame",
    "rc-closure",
    "rcbi-frame",
    "rcbi-model",
];
