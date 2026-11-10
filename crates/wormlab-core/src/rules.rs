//! 各体系の公理と規則の一覧（Web の「規則」タブ、CLI の `wormlab rules`、証明図の規則名の説明に使う）。
//!
//! 規則の名前は、証明 DAG に出てくる名前（[`crate::rcproof::RcRule`] などの表示）と同じにする。
//! テスト（tests/rules.rs）で、各体系の規則の enum の名前と一覧の名前が一致することを確かめる。
//!
//! 出典：
//! - RC：Beklemishev, "Positive provability logic for uniform reflection principles"（APAL 165, 2014,
//!   arXiv:1304.4396）、Dashkov（Math. Notes 91, 2012）。順序数の様相は Fernández-Duque & Hermo Reyes
//!   （arXiv:2008.13445）Def 2 の RC_Λ
//! - WC：de Almeida Borges & Joosten, "The Worm Calculus"（arXiv:1803.10543）Def 3.1
//! - BC：Fernández-Duque & Hermo Reyes（arXiv:2008.13445）Def 27
//! - BWC：wormlab で定義した体系（WC の規則を括弧語に移したもの。論文にはない）
//! - RC_BI / RC_BIω：Pakhomov & Lazar（arXiv:2610.20115）Def 2.1・2.5

use crate::i18n::tr;
use serde::Serialize;

/// 1 つの公理か規則。公理は前提がない規則として持つ。
#[derive(Clone, Debug, Serialize)]
pub struct Rule {
    /// 名前（証明 DAG に出てくる名前と同じ）
    pub name: &'static str,
    /// ふつうの前提
    pub premises: Vec<String>,
    /// 副条件の前提（同じ体系の導出で示す、括弧語どうしの比較）
    pub side: Vec<String>,
    pub conclusion: String,
    /// メタの条件（例：α > β）
    pub condition: Option<String>,
    /// 補足
    pub note: Option<String>,
}

impl Rule {
    /// 1 行の書き方。例：`φ ⊢ ψ ⇒ ⟨α⟩φ ⊢ ⟨α⟩ψ`、`⟨α⟩φ ⊢ ⟨β⟩φ（α > β）`。
    pub fn text(&self) -> String {
        let mut prem: Vec<String> = self.premises.clone();
        for s in &self.side {
            prem.push(format!("[{} {s}]", tr("副条件", "side condition:")));
        }
        let mut t = if prem.is_empty() {
            self.conclusion.clone()
        } else {
            format!("{} ⇒ {}", prem.join(", "), self.conclusion)
        };
        if let Some(c) = &self.condition {
            t.push_str(&format!("{}{c}{}", tr("（", " ("), tr("）", ")")));
        }
        t
    }

    /// 副条件の前提を足す。
    ///
    /// 【Rust メモ】`mut self` で受けて `self` を返すと、`axiom(…).cond(…).note(…)` のように
    /// 続けて書ける（builder と呼ばれる書き方）
    fn side(mut self, s: &[&str]) -> Rule {
        self.side = s.iter().map(|x| x.to_string()).collect();
        self
    }

    fn cond(mut self, c: &str) -> Rule {
        self.condition = Some(c.to_string());
        self
    }

    fn note(mut self, n: &str) -> Rule {
        self.note = Some(n.to_string());
        self
    }
}

/// 前提のない規則（公理）。
fn axiom(name: &'static str, conclusion: &str) -> Rule {
    rule(name, &[], conclusion)
}

fn rule(name: &'static str, premises: &[&str], conclusion: &str) -> Rule {
    Rule {
        name,
        premises: premises.iter().map(|x| x.to_string()).collect(),
        side: Vec::new(),
        conclusion: conclusion.to_string(),
        condition: None,
        note: None,
    }
}

/// 規則のまとまり（公理、推論規則、…）。
#[derive(Clone, Debug, Serialize)]
pub struct Group {
    pub title: String,
    pub rules: Vec<Rule>,
}

fn group(title: &str, rules: Vec<Rule>) -> Group {
    Group { title: title.to_string(), rules }
}

/// 1 つの体系。
#[derive(Clone, Debug, Serialize)]
pub struct System {
    /// 証明タブの体系の名前と同じ（"rc"・"wc"・"bc"・"bwc"・"rcbi"）
    pub id: &'static str,
    pub name: String,
    pub source: String,
    /// 式・判断の書き方
    pub language: Vec<String>,
    pub groups: Vec<Group>,
    pub notes: Vec<String>,
    /// wormlab がこの体系の導出を作って検査するか（RC_BI は判定とモデルだけ）
    pub derivations: bool,
}

impl System {
    /// 名前から規則を探す。
    pub fn rule(&self, name: &str) -> Option<&Rule> {
        self.groups.iter().flat_map(|g| &g.rules).find(|r| r.name == name)
    }

    /// 端末に出す書き方。
    pub fn text(&self) -> String {
        let mut s = format!("{}\n  {}: {}\n", self.name, tr("出典", "Source"), self.source);
        for l in &self.language {
            s.push_str(&format!("  {l}\n"));
        }
        for g in &self.groups {
            s.push_str(&format!("\n  {}\n", g.title));
            let w = g.rules.iter().map(|r| r.name.chars().count()).max().unwrap_or(0);
            for r in &g.rules {
                // 【Rust メモ】`{:<w$}` は「幅 w で左寄せ」（w は変数）。名前の後ろをそろえる
                s.push_str(&format!("    {:<w$}  {}\n", r.name, r.text()));
                if let Some(n) = &r.note {
                    s.push_str(&format!("    {:<w$}  ※ {n}\n", ""));
                }
            }
        }
        if !self.notes.is_empty() {
            s.push('\n');
            for n in &self.notes {
                s.push_str(&format!("  ・{n}\n"));
            }
        }
        s
    }
}

/// すべての体系（証明タブと同じ順）。
pub fn all() -> Vec<System> {
    vec![rc(), wc(), bc(), bwc(), rcbi()]
}

/// id（"rc" など）から体系を探す。
pub fn get(id: &str) -> Option<System> {
    all().into_iter().find(|s| s.id == id)
}

fn rc() -> System {
    let ab = tr("α > β", "α > β");
    System {
        id: "rc",
        name: tr("RC（Reflection Calculus）", "RC (Reflection Calculus)").into(),
        source: tr(
            "Beklemishev, Positive provability logic for uniform reflection principles（APAL 165, 2014）、Dashkov（Math. Notes 91, 2012）。様相が順序数のもの（RC_Λ）は Fernández-Duque & Hermo Reyes（arXiv:2008.13445）Def 2",
            "Beklemishev, Positive provability logic for uniform reflection principles (APAL 165, 2014); Dashkov (Math. Notes 91, 2012). With ordinal modalities (RC_Λ): Fernández-Duque & Hermo Reyes (arXiv:2008.13445), Def 2",
        )
        .into(),
        language: vec![
            tr("式（強正値式）：φ ::= ⊤ | p | φ ∧ ψ | ⟨α⟩φ（α は自然数か順序数）", "Formulas (strictly positive): φ ::= ⊤ | p | φ ∧ ψ | ⟨α⟩φ (α a natural number or an ordinal)").into(),
            tr("判断：シーケント φ ⊢ ψ", "Judgements: sequents φ ⊢ ψ").into(),
        ],
        groups: vec![
            group(
                tr("公理", "Axioms"),
                vec![
                    axiom("Id", "φ ⊢ φ"),
                    axiom("⊤", "φ ⊢ ⊤"),
                    axiom("∧E1", "φ ∧ ψ ⊢ φ"),
                    axiom("∧E2", "φ ∧ ψ ⊢ ψ"),
                    axiom("4", "⟨α⟩⟨α⟩φ ⊢ ⟨α⟩φ"),
                    axiom("Mono", "⟨α⟩φ ⊢ ⟨β⟩φ").cond(ab),
                    axiom("J", "⟨α⟩φ ∧ ⟨β⟩ψ ⊢ ⟨α⟩(φ ∧ ⟨β⟩ψ)").cond(ab),
                ],
            ),
            group(
                tr("推論規則", "Rules"),
                vec![
                    rule("∧I", &["φ ⊢ ψ", "φ ⊢ χ"], "φ ⊢ ψ ∧ χ"),
                    rule("Cut", &["φ ⊢ ψ", "ψ ⊢ χ"], "φ ⊢ χ"),
                    rule("Nec", &["φ ⊢ ψ"], "⟨α⟩φ ⊢ ⟨α⟩ψ"),
                ],
            ),
        ],
        notes: vec![
            tr(
                "シーケント φ ⊢ ψ は、φ の有限モデル（標準木の閉包）の根で ψ を検査して判定できる（多項式時間）。成り立たなければ、そのモデルが反例になる。",
                "A sequent φ ⊢ ψ is decided by checking ψ at the root of a finite model of φ (the closure of its canonical tree), in polynomial time. If it fails, that model is a countermodel.",
            )
            .into(),
            tr(
                "worm（⊤ と ⟨α⟩ だけの式）どうしでは、RC は WC の上で保存的（WC の論文の Thm 6.2）。",
                "Between worms (formulas built from ⊤ and ⟨α⟩ only), RC is conservative over WC (Thm 6.2 of the WC paper).",
            )
            .into(),
        ],
        derivations: true,
    }
}

fn wc() -> System {
    System {
        id: "wc",
        name: tr("WC（Worm Calculus）", "WC (Worm Calculus)").into(),
        source: tr(
            "de Almeida Borges & Joosten, The Worm Calculus（arXiv:1803.10543）Def 3.1",
            "de Almeida Borges & Joosten, The Worm Calculus (arXiv:1803.10543), Def 3.1",
        )
        .into(),
        language: vec![
            tr("worm：A ::= ⊤ | αA（文字 α は自然数か順序数。⊤ は省略して書く）", "Worms: A ::= ⊤ | αA (letters α are natural numbers or ordinals; ⊤ is left out)").into(),
            tr("判断：worm どうしのシーケント A ⊢ B（変数も ∧ もない）", "Judgements: sequents A ⊢ B between worms (no variables, no ∧)").into(),
        ],
        groups: vec![
            group(
                tr("公理", "Axioms"),
                vec![
                    axiom("A1", "A ⊢ ⊤"),
                    axiom("A2", "ααA ⊢ αA"),
                    axiom("A3", "αA ⊢ βA").cond(tr("α > β", "α > β")),
                ],
            ),
            group(
                tr("推論規則", "Rules"),
                vec![
                    rule("Cut", &["A ⊢ B", "B ⊢ C"], "A ⊢ C").note(tr("論文の R1", "R1 in the paper")),
                    rule("Nec", &["A ⊢ B"], "αA ⊢ αB").note(tr("論文の R2", "R2 in the paper")),
                    rule("R3", &["A ⊢ B", "A ⊢ αC"], "A ⊢ BαC")
                        .cond(tr("B の文字はすべて α より大きい", "every letter of B is greater than α")),
                ],
            ),
        ],
        notes: vec![
            tr(
                "worm どうしのシーケントについて、RC と同じものが導出できる（RC は WC の上で保存的、論文の Thm 6.2）。",
                "Between worms, WC derives the same sequents as RC (RC is conservative over WC, Thm 6.2 of the paper).",
            )
            .into(),
            tr(
                "wormlab の判定は worm の head/body 分解による構文的なもの（モデルも順序数も使わない）。",
                "wormlab decides WC syntactically, by the head/body decomposition of worms (no models, no ordinals).",
            )
            .into(),
        ],
        derivations: true,
    }
}

fn bc() -> System {
    let le = tr("a ⊢ ()b か a ⊢ b", "a ⊢ ()b or a ⊢ b");
    System {
        id: "bc",
        name: tr("BC（Bracket Calculus）", "BC (Bracket Calculus)").into(),
        source: tr(
            "Fernández-Duque & Hermo Reyes, Deducibility and Independence in Beklemishev's Autonomous Provability Calculus（arXiv:2008.13445）Def 27",
            "Fernández-Duque & Hermo Reyes, Deducibility and Independence in Beklemishev's Autonomous Provability Calculus (arXiv:2008.13445), Def 27",
        )
        .into(),
        language: vec![
            tr("括弧語：a ::= ⊤ | (a)b（() = 1、(()) = ω、((())) = ε₀。⊤ は省略して書く）", "Bracket words: a ::= ⊤ | (a)b (() = 1, (()) = ω, ((())) = ε₀; ⊤ is left out)").into(),
            tr("式：φ ::= ⊤ | p | φ ∧ ψ | (a)φ（様相も括弧語）。判断はシーケント φ ⊢ ψ", "Formulas: φ ::= ⊤ | p | φ ∧ ψ | (a)φ (modalities are bracket words too). Judgements: sequents φ ⊢ ψ").into(),
            tr("b ◁ a は a ⊢ ()b が導出できること、b ≤ a は a ⊢ ()b か a ⊢ b が導出できること", "b ◁ a means that a ⊢ ()b is derivable; b ≤ a means that a ⊢ ()b or a ⊢ b is derivable").into(),
        ],
        groups: vec![
            group(
                tr("公理", "Axioms"),
                vec![axiom("Id", "φ ⊢ φ"), axiom("⊤", "φ ⊢ ⊤"), axiom("∧E1", "φ ∧ ψ ⊢ φ"), axiom("∧E2", "φ ∧ ψ ⊢ ψ")],
            ),
            group(
                tr("推論規則", "Rules"),
                vec![
                    rule("∧I", &["φ ⊢ ψ", "φ ⊢ χ"], "φ ⊢ ψ ∧ χ"),
                    rule("Cut", &["φ ⊢ ψ", "ψ ⊢ χ"], "φ ⊢ χ"),
                    rule("R3a", &["φ ⊢ ψ"], "(a)φ ⊢ (b)ψ").side(&[le]).cond(tr("b ≤ a", "b ≤ a")),
                    rule("R3b", &["φ ⊢ ψ"], "(a)(b)φ ⊢ (b)ψ").side(&[le]).cond(tr("b ≤ a", "b ≤ a")),
                    axiom("R4", "(a)φ ∧ (b)ψ ⊢ (a)(φ ∧ (b)ψ)").side(&["a ⊢ ()b"]).cond(tr("b ◁ a", "b ◁ a")),
                ],
            ),
        ],
        notes: vec![
            tr(
                "論文の規則 3 は結論が 2 つ（(a)φ ⊢ (b)ψ と (a)(b)φ ⊢ (b)ψ）あるので、wormlab では R3a・R3b に分けた。R4 は論文の規則 4。",
                "Rule 3 of the paper has two conclusions ((a)φ ⊢ (b)ψ and (a)(b)φ ⊢ (b)ψ), so wormlab splits it into R3a and R3b. R4 is rule 4 of the paper.",
            )
            .into(),
            tr(
                "副条件（括弧語どうしの比較）も BC の導出なので、順序数を使わずに検査できる。",
                "Side conditions (comparisons of bracket words) are BC derivations too, so derivations are checked without ordinals.",
            )
            .into(),
            tr(
                "様相を順序数に翻訳する τ で、BC ⊢ φ ⊢ ψ ⟺ RC_Γ₀ ⊢ φ^τ ⊢ ψ^τ（論文の Thm 38）。",
                "With the translation τ of modalities into ordinals, BC ⊢ φ ⊢ ψ ⟺ RC_Γ₀ ⊢ φ^τ ⊢ ψ^τ (Thm 38 of the paper).",
            )
            .into(),
        ],
        derivations: true,
    }
}

fn bwc() -> System {
    System {
        id: "bwc",
        name: tr("BWC（括弧語だけの体系、WC の BC 版）", "BWC (bracket words only; the BC version of WC)").into(),
        source: tr(
            "wormlab で定義した体系（論文にはない）。WC（arXiv:1803.10543）の規則を、BC（arXiv:2008.13445）の括弧語に移したもの",
            "A system defined in wormlab (not from a paper): the rules of WC (arXiv:1803.10543) moved to the bracket words of BC (arXiv:2008.13445)",
        )
        .into(),
        language: vec![
            tr("判断：括弧語どうしのシーケント a ⊢ b（変数も ∧ もない）。括弧語 (a₁)…(a_k) は worm (a₁)…(a_k)⊤ と読む", "Judgements: sequents a ⊢ b between bracket words (no variables, no ∧). A bracket word (a₁)…(a_k) is read as the worm (a₁)…(a_k)⊤").into(),
            tr("文字の比較 y ◁ x は、この体系の判断 x ⊢ ()y そのもの", "The comparison y ◁ x of letters is the judgement x ⊢ ()y of this very system").into(),
        ],
        groups: vec![
            group(tr("公理", "Axioms"), vec![axiom("A1", "a ⊢ ⊤"), axiom("A2", "(x)(x)c ⊢ (x)c")]),
            group(
                tr("推論規則", "Rules"),
                vec![
                    axiom("A3", "(x)c ⊢ (y)c")
                        .side(&[tr("x ⊢ ()y か x ⊢ y", "x ⊢ ()y or x ⊢ y")])
                        .cond(tr("y ≤ x", "y ≤ x"))
                        .note(tr(
                            "WC の A3（α > β）を、正規形でない括弧語のために「等しいか小さい」まで広げた",
                            "WC's A3 (α > β), widened to “equal or smaller” for bracket words not in normal form",
                        )),
                    rule("Cut", &["a ⊢ b", "b ⊢ c"], "a ⊢ c"),
                    rule("Nec", &["a ⊢ b"], "(x)a ⊢ (x)b"),
                    rule("R3", &["a ⊢ b", "a ⊢ (x)c"], "a ⊢ b(x)c")
                        .side(&["y ⊢ ()x"])
                        .cond(tr("b の各文字 y について x ◁ y", "x ◁ y for every letter y of b"))
                        .note(tr("副条件 y ⊢ ()x は、b の異なる文字 y ごとに 1 つ", "one side condition y ⊢ ()x for each distinct letter y of b")),
                ],
            ),
        ],
        notes: vec![
            tr(
                "健全性：文字を順序数に移す τ で、各規則は WC の規則（か恒等式）に移る。",
                "Soundness: under τ (letters to ordinals), each rule becomes a rule of WC (or an identity).",
            )
            .into(),
            tr(
                "括弧語どうしのシーケントについて、BC と同じものが導出できる（BC は BWC の上で保存的）。wormlab の証明器が導出を実際に作る。",
                "Between bracket words, BWC derives the same sequents as BC (BC is conservative over BWC); wormlab's prover actually builds the derivations.",
            )
            .into(),
        ],
        derivations: true,
    }
}

fn rcbi() -> System {
    System {
        id: "rcbi",
        name: tr("RC_BIω（Reflection Calculus for Bar Induction）", "RC_BIω (Reflection Calculus for Bar Induction)").into(),
        source: tr(
            "Pakhomov & Lazar, A Reflection Calculus for Bar Induction and the Linearity of Consistency Strength Ordering（arXiv:2610.20115）Def 2.1・2.5",
            "Pakhomov & Lazar, A Reflection Calculus for Bar Induction and the Linearity of Consistency Strength Ordering (arXiv:2610.20115), Defs 2.1 and 2.5",
        )
        .into(),
        language: vec![
            tr(
                "式：A ::= ⊤ | p | A ∧ B | ⟨1⟩_α A（1 ≤ α ≤ ω）| ⟨2⟩_β A（2 ≤ β < ω）| ↓A | ∇A",
                "Formulas: A ::= ⊤ | p | A ∧ B | ⟨1⟩_α A (1 ≤ α ≤ ω) | ⟨2⟩_β A (2 ≤ β < ω) | ↓A | ∇A",
            )
            .into(),
            tr(
                "⟨1⟩_n：Π¹_n 反射、⟨2⟩_n：Π¹_n の ω モデル反射、↓：ω モデルへの射影、∇：真な Π¹₁ 定理（すべて ACA₀ の上）。⟨i⟩_α の i は 1 か 2",
                "⟨1⟩_n: Π¹_n reflection; ⟨2⟩_n: Π¹_n ω-model reflection; ↓: projection to ω-models; ∇: true Π¹₁ theorems (all over ACA₀). In ⟨i⟩_α, i is 1 or 2",
            )
            .into(),
        ],
        groups: vec![
            group(
                tr("推論規則", "Rules"),
                vec![
                    rule("L∧1", &["A ⊢ C"], "A ∧ B ⊢ C"),
                    rule("L∧2", &["B ⊢ C"], "A ∧ B ⊢ C"),
                    rule("R∧", &["A ⊢ B", "A ⊢ C"], "A ⊢ B ∧ C"),
                    rule("Mod1", &["A ⊢ B"], "⟨i⟩_α A ⊢ ⟨i⟩_α B"),
                    rule("Mod2", &["A ⊢ B"], "↓A ⊢ ↓B"),
                    rule("Mod3", &["A ⊢ B"], "∇A ⊢ ∇B"),
                    rule("Cut", &["A ⊢ B", "B ⊢ C"], "A ⊢ C"),
                ],
            ),
            group(tr("自明な公理", "Trivial axioms"), vec![axiom("Id", "A ⊢ A"), axiom("⊤", "A ⊢ ⊤")]),
            group(
                tr("単調性の公理", "Monotonicity axioms"),
                vec![
                    axiom("1", "⟨i⟩_α A ⊢ ⟨i⟩_β A").cond(tr("β < α", "β < α")),
                    axiom("2", "⟨2⟩_α A ⊢ ⟨1⟩_α A"),
                    axiom("3", "A ⊢ ∇A"),
                    axiom("4", "⟨1⟩₁A ⊢ ∇A"),
                    axiom("5", "↓A ⊢ ∇A"),
                ],
            ),
            group(
                tr("推移性の公理", "Transitivity axioms"),
                vec![
                    axiom("6", "⟨i⟩_α⟨j⟩_α A ⊢ ⟨j⟩_α A"),
                    axiom("7", "∇∇A ⊢ ∇A"),
                    axiom("8", "∇⟨1⟩₁A ⊢ ⟨1⟩₁A"),
                    axiom("9", "⟨1⟩₁∇A ⊢ ⟨1⟩₁A"),
                    axiom("10", "↓∇A ⊢ ↓A"),
                ],
            ),
            group(
                tr("連言の公理", "Conjunction axioms"),
                vec![
                    axiom("11", "⟨2⟩_α A ∧ ⟨1⟩₁B ⊢ ⟨2⟩_α(A ∧ ↓B)"),
                    axiom("12", "⟨i⟩_α A ∧ ⟨j⟩_β B ⊢ ⟨i⟩_α(A ∧ ⟨j⟩_β B)")
                        .cond(tr("β < α か α = β = ω", "β < α, or α = β = ω")),
                ],
            ),
            group(
                tr("構成的な公理", "Constructive axioms"),
                vec![
                    axiom("13", "↓⊤ ⊢ ⟨1⟩_ω⊤"),
                    axiom("14", "↓⟨1⟩₁A ⊢ ⟨1⟩_ω↓A"),
                    axiom("15", "A ∧ ⟨2⟩₂B ⊢ ∇(↓A ∧ B)"),
                ],
            ),
        ],
        notes: vec![
            tr(
                "ここに書いたのは RC_BIω（Def 2.5）。⟨1⟩_ω のない RC_BI（Def 2.1）では、公理 12 の条件が β < α だけになり、公理 13・14 の ⟨1⟩_ω が ⟨1⟩_α（α < ω）になる。⟨1⟩_ω を含まない式については 2 つは同じものを導出する（Prop 2.6）。",
                "Shown here is RC_BIω (Def 2.5). In RC_BI (Def 2.1, without ⟨1⟩_ω), axiom 12 only has the condition β < α, and ⟨1⟩_ω in axioms 13 and 14 becomes ⟨1⟩_α (α < ω). On formulas without ⟨1⟩_ω the two derive the same sequents (Prop 2.6).",
            )
            .into(),
            tr(
                "wormlab は導出を作らない。変数のないシーケント A ⊢ B を、有限モデル M_A の根で B を検査して判定する（Thm 3.19）。",
                "wormlab does not build derivations here. It decides variable-free sequents A ⊢ B by checking B at the root of the finite model M_A (Thm 3.19).",
            )
            .into(),
            tr(
                "公理と規則の番号・名前は論文のもの（Id と ⊤ は wormlab での呼び方）。",
                "Axiom numbers and rule names are the paper's (Id and ⊤ are wormlab's names).",
            )
            .into(),
        ],
        derivations: false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_are_unique_per_system() {
        for s in all() {
            let mut names: Vec<&str> = s.groups.iter().flat_map(|g| g.rules.iter().map(|r| r.name)).collect();
            let n = names.len();
            names.sort();
            names.dedup();
            assert_eq!(names.len(), n, "{}: duplicate rule name", s.id);
        }
    }

    #[test]
    fn text_forms() {
        let rc = get("rc").unwrap();
        assert_eq!(rc.rule("Nec").unwrap().text(), "φ ⊢ ψ ⇒ ⟨α⟩φ ⊢ ⟨α⟩ψ");
        assert_eq!(rc.rule("Mono").unwrap().text(), "⟨α⟩φ ⊢ ⟨β⟩φ（α > β）");
        let bc = get("bc").unwrap();
        assert_eq!(bc.rule("R4").unwrap().text(), "[副条件 a ⊢ ()b] ⇒ (a)φ ∧ (b)ψ ⊢ (a)(φ ∧ (b)ψ)（b ◁ a）");
        assert!(get("nothing").is_none());
    }
}
