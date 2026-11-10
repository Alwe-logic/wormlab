//! LaTeX への書き出し。
//!
//! - 式・順序数・worm・括弧語・シーケントは [`ToLatex`] で数式の断片（`$…$` の中身）にする。
//! - 証明は 2 通り：bussproofs の証明木（[`proof_tree`]）と、行番号つきの一覧（[`proof_lines`]）。
//! - battle は表（[`battle_table`]）、順序数の書き換えは `align*`（[`ordinal_summary`]）。
//! - Kripke モデルは TikZ（[`crate::modelview::ModelView::tikz`]）。
//! - [`document`] で包むと、そのまま pdflatex にかけられる文書になる。
//!
//! 使うのは標準のコマンドだけ（`\langle`・`\top`・`\vdash`・`\varepsilon`・`\varphi` など）。
//! 必要なパッケージは amsmath・amssymb・bussproofs・tikz（[`PREAMBLE`]）。
//!
//! 【Rust メモ】`trait ToLatex` を各モジュールの型に実装している（`impl ToLatex for Veblen` は
//! veblen.rs の中、など）。型の中身（非公開のフィールド）に触れるのは、その型を定義した
//! モジュールの中だけなので、実装もそこに置く。

use crate::proof::Proof;
use crate::veblen::Veblen;
use crate::worm::Worm;
use crate::Bracket;

/// LaTeX の数式として書ける型。
pub trait ToLatex {
    /// 数式モードの中に置く LaTeX（`$` や `\[` は付けない）。
    fn to_latex(&self) -> String;
}

impl ToLatex for u32 {
    fn to_latex(&self) -> String {
        self.to_string()
    }
}

/// 文書にするときのプリアンブル（[`document`] が使う）。
pub const PREAMBLE: &str = "\\documentclass{article}
\\usepackage[a4paper,margin=20mm]{geometry}
\\usepackage{amsmath,amssymb}
\\usepackage{bussproofs}
\\usepackage{tikz}
\\allowdisplaybreaks
";

/// 断片を、そのまま pdflatex にかけられる文書にする。
pub fn document(body: &str) -> String {
    format!("{PREAMBLE}\\begin{{document}}\n\n{}\n\n\\end{{document}}\n", body.trim_end())
}

/// 数式の断片を別行立ての数式 `\[ … \]` にする。
pub fn display(math: &str) -> String {
    format!("\\[\n{math}\n\\]")
}

/// 変数名。`p` → `p`、`p1` → `p_{1}`、`foo` → `\mathit{foo}`、`a_b` → `a_{b}`。
pub fn var(name: &str) -> String {
    if let Some((head, sub)) = name.split_once('_').filter(|(h, s)| !h.is_empty() && !s.is_empty()) {
        return format!("{}_{{{}}}", var(head), var(sub));
    }
    let letters: String = name.chars().take_while(|c| c.is_ascii_alphabetic()).collect();
    let digits = &name[letters.len()..];
    let base = match letters.chars().count() {
        0 => return escape(name),
        1 => letters,
        _ => format!("\\mathit{{{letters}}}"),
    };
    if digits.is_empty() {
        base
    } else if digits.chars().all(|c| c.is_ascii_digit()) {
        format!("{base}_{{{digits}}}")
    } else {
        format!("\\mathit{{{}}}", escape(name))
    }
}

/// LaTeX で特別な意味を持つ文字を逃がす（`\mathit{}` や `\text{}` の中に置く文字列用）。
pub fn escape(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '_' | '&' | '%' | '$' | '#' | '{' | '}' => {
                out.push('\\');
                out.push(c);
            }
            '\\' => out.push_str("\\textbackslash{}"),
            _ => out.push(c),
        }
    }
    out
}

/// 規則の名前。`Cut` → `\mathrm{Cut}`、`∧E1` → `{\land}\mathrm{E}_{1}`、`⊤` → `\top`、`4` → `4`。
pub fn rule_name(name: &str) -> String {
    match name {
        "⊤" => return "\\top".to_string(),
        "4" => return "4".to_string(),
        _ => {}
    }
    if let Some(rest) = name.strip_prefix('∧') {
        // ∧E1 → ∧E_1、∧I → ∧I
        let (word, num): (String, String) = (
            rest.chars().filter(|c| !c.is_ascii_digit()).collect(),
            rest.chars().filter(|c| c.is_ascii_digit()).collect(),
        );
        let sub = if num.is_empty() { String::new() } else { format!("_{{{num}}}") };
        return format!("{{\\land}}\\mathrm{{{word}}}{sub}");
    }
    format!("\\mathrm{{{}}}", escape(name))
}

/// 順序数の関係を数式にする。`rel` は "<"・"="・">"。
pub fn relation(a: &str, rel: &str, b: &str) -> String {
    format!("{a} {rel} {b}")
}

// ----------------------------------------------------------------------
// 証明
// ----------------------------------------------------------------------

/// 証明木を描くときの既定の上限（木に展開したノード数）。これより大きい証明は
/// 同じ部分が何度も展開されて読めなくなるので、行番号つきの一覧だけにする。
pub const TREE_LIMIT: u128 = 120;

/// 証明を bussproofs の証明木にする（`\begin{prooftree} … \end{prooftree}`）。
///
/// DAG で共有している部分証明は、木では使われるたびに書き直す。木に展開した
/// ノード数が `max_nodes` を超えるとき、または前提が 6 個以上の規則があるときは `None`。
/// 公理（前提のない規則）は、空の前提から規則の名前つきの線を引いて書く。
pub fn proof_tree<J: ToLatex, R: ToLatex>(p: &Proof<J, R>, max_nodes: u128) -> Option<String> {
    if p.tree_size() > max_nodes || p.nodes.iter().any(|n| n.premises.len() > 5) {
        return None;
    }
    // 各ノードの結論と規則は 1 回だけ LaTeX にする（木では同じノードが何度も出る）
    let concl: Vec<String> = p.nodes.iter().map(|n| n.conclusion.to_latex()).collect();
    let rules: Vec<String> = p.nodes.iter().map(|n| n.rule.to_latex()).collect();

    // 【Rust メモ】入れ子の関数 fn は外側の変数を使えないので、必要なものは引数で渡す。
    fn go<J, R>(p: &Proof<J, R>, id: usize, depth: usize, concl: &[String], rules: &[String], out: &mut String) {
        let node = &p.nodes[id];
        let pad = "  ".repeat(depth);
        if node.premises.is_empty() {
            out.push_str(&format!("{pad}\\AxiomC{{}}\n"));
        }
        for &q in &node.premises {
            go(p, q, depth + 1, concl, rules, out);
        }
        let k = node.premises.len().max(1);
        let cmd = ["UnaryInfC", "BinaryInfC", "TrinaryInfC", "QuaternaryInfC", "QuinaryInfC"][k - 1];
        out.push_str(&format!("{pad}\\RightLabel{{\\scriptsize ${}$}}\n", rules[id]));
        out.push_str(&format!("{pad}\\{cmd}{{${}$}}\n", concl[id]));
    }

    let mut out = String::from("\\begin{prooftree}\n");
    go(p, p.root, 0, &concl, &rules, &mut out);
    out.push_str("\\end{prooftree}");
    Some(out)
}

/// 証明を行番号つきの一覧にする（`\[ \begin{array} … \end{array} \]`）。
///
/// 1 行 1 ノードで「番号. 結論　規則 (前提の番号)」。番号は 1 から。共有している
/// 部分証明は 1 回だけ書くので、どんな大きさの証明でも DAG のノード数の行で収まる。
pub fn proof_lines<J: ToLatex, R: ToLatex>(p: &Proof<J, R>) -> String {
    let mut out = String::from("\\begin{array}{rll}\n");
    for (i, node) in p.nodes.iter().enumerate() {
        let refs = if node.premises.is_empty() {
            String::new()
        } else {
            let ns: Vec<String> = node.premises.iter().map(|q| (q + 1).to_string()).collect();
            format!("\\ ({})", ns.join(",\\,"))
        };
        out.push_str(&format!(
            "{}. & {} & \\quad {}{} \\\\\n",
            i + 1,
            node.conclusion.to_latex(),
            node.rule.to_latex(),
            refs
        ));
    }
    out.push_str("\\end{array}");
    display(&out)
}

// ----------------------------------------------------------------------
// battle と順序数
// ----------------------------------------------------------------------

/// battle の 1 行：その時点の式と、（分かっていれば）それが表す順序数。
pub struct BattleRow {
    pub formula: String,
    pub ordinal: Option<String>,
}

/// battle の列を表にする（`\[ \begin{array} … \end{array} \]`）。
///
/// `name` は式の名前（"A" なら列見出しは A_k）、`ord` は順序数の列見出し
/// （例 "o(A_k)"。`None` なら順序数の列を作らない）。`more` なら最後に ⋮ を付ける。
pub fn battle_table(rows: &[BattleRow], name: &str, ord: Option<&str>, more: bool) -> String {
    let cols = if ord.is_some() { "rll" } else { "rl" };
    let mut out = format!("\\begin{{array}}{{{cols}}}\nk & {name}_{{k}}");
    if let Some(o) = ord {
        out.push_str(&format!(" & {o}"));
    }
    out.push_str(" \\\\ \\hline\n");
    for (k, r) in rows.iter().enumerate() {
        out.push_str(&format!("{k} & {}", r.formula));
        if ord.is_some() {
            out.push_str(&format!(" & {}", r.ordinal.as_deref().unwrap_or("")));
        }
        out.push_str(" \\\\\n");
    }
    if more {
        out.push_str(if ord.is_some() { "\\vdots & \\vdots & \\vdots \\\\\n" } else { "\\vdots & \\vdots \\\\\n" });
    }
    out.push_str("\\end{array}");
    display(&out)
}

/// 順序数 α の書き換えを `align*` にまとめる。
///
/// - `input`：入力の式（worm なら `o(…)` で包んだもの）。α の標準形と違うときだけ最初に書く
/// - α の標準形（Veblen 表記）、標準形の worm、正規形の括弧語
/// - 標準の基本列 α[0..fs)（極限のとき）と、worm が作る列 α{0..fs}（worm battle の 1 ステップ）
/// - `hardy`：Hardy 関数の値 (n, H_α(n))（多倍長。60 桁を超えたら ≈ a×10^k、下界なら > 2^k など。
///   `None` は計算できなかったもの）
pub fn ordinal_summary(
    input: Option<&str>,
    a: &Veblen,
    fs: u64,
    hardy: &[(u128, Option<crate::hierarchy::BigValue>)],
) -> String {
    let mut lines: Vec<(String, String)> = Vec::new();
    let al = a.to_latex();
    let mut first = true;
    let mut push = |rhs: String, lines: &mut Vec<(String, String)>| {
        // 入力と同じ書き方（入力が標準形の worm だったときなど）は 2 回書かない
        if lines.iter().any(|(_, r)| *r == rhs) {
            return;
        }
        let lhs = if first { "\\alpha".to_string() } else { String::new() };
        first = false;
        lines.push((lhs, rhs));
    };
    if let Some(i) = input.filter(|i| *i != al) {
        push(i.to_string(), &mut lines);
    }
    push(al.clone(), &mut lines);
    // 文字が自然数で書けるなら自然数の worm、そうでなければ文字が順序数の worm
    let worm = match a.to_cnf() {
        Some(c) => Worm::from_ordinal(&c).to_latex(),
        None => Worm::from_veblen(a).to_latex(),
    };
    push(format!("o({worm})"), &mut lines);
    // 括弧語は Γ0 未満だけ（Ω・ψ を含む数は括弧語で表せない）。
    // Γ0 以上の可算な数は impredicative worm の値 p(w) で書く
    if a.is_predicative() {
        push(format!("o^{{*}}({})", Bracket::from_ordinal(a).to_latex()), &mut lines);
    } else if let Some(w) = crate::iworm::IWorm::from_value(a) {
        push(format!("p({})", w.to_latex()), &mut lines);
    }
    if a.is_limit() {
        for n in 0..fs {
            if let Some(y) = a.fundamental(n) {
                lines.push((format!("\\alpha[{n}]"), y.to_latex()));
            }
        }
    }
    // worm が作る列 α{n}：標準形の worm から battle を 1 ステップ（n を使って）進めたものの順序数
    if !a.is_zero() {
        for n in 0..fs {
            if let Some(y) = crate::hierarchy::worm_fundamental(a, n as usize) {
                lines.push((format!("\\alpha\\{{{n}\\}}"), y.to_latex()));
            }
        }
    }
    let mut lines: Vec<(String, String)> = lines.into_iter().map(|(l, r)| (l, format!("= {r}"))).collect();
    if !hardy.is_empty() {
        // 「関係＋右辺」の組（= 24、> 2^{…}、\geq …）。最初の関係の前で揃える
        let rels: Vec<String> = hardy
            .iter()
            .map(|(_, v)| match v {
                Some(v) => v.to_latex_relation(),
                None => "= \\text{(too large)}".to_string(),
            })
            .collect();
        let mut rhs = rels[0].clone();
        for ((n, _), r) in hardy.iter().zip(&rels).skip(1) {
            rhs.push_str(&format!(",\\quad H_{{\\alpha}}({n}) {r}"));
        }
        lines.push((format!("H_{{\\alpha}}({})", hardy[0].0), rhs));
    }
    align(&lines)
}

/// 左辺と「関係＋右辺」の組を `align*` で縦に揃える（関係の前で揃える）。
/// 例：`[("\\alpha", "= \\omega"), ("", "< \\varepsilon_{0}")]`。
pub fn align(lines: &[(String, String)]) -> String {
    let body: Vec<String> = lines.iter().map(|(l, r)| format!("{l} &{r}")).collect();
    format!("\\begin{{align*}}\n{}\n\\end{{align*}}", body.join(" \\\\\n"))
}

/// [`ordinal_summary`] に、ε₀ 未満なら Hardy 関数 H_α(1..5) を付けて呼ぶ（Web と CLI で共通、
/// [`crate::hierarchy::hardy_samples`]）。
pub fn ordinal_block(input: Option<&str>, a: &Veblen, fs: u64) -> String {
    ordinal_summary(input, a, fs, &crate::hierarchy::hardy_samples(a))
}

/// シーケントの成否：`A \vdash B` か `A \nvdash B`（`\nvdash` は amssymb）。
pub fn verdict(lhs: &str, rhs: &str, holds: bool) -> String {
    format!("{lhs} {} {rhs}", if holds { "\\vdash" } else { "\\nvdash" })
}

/// RC_BI の式 A の形（零・後続・極限）と基本列 (A)_1..k を `align*` に。
pub fn rcbi_form(x: &crate::rcbi::Formula, k: u32) -> Result<String, String> {
    use crate::rcbi_order::{self, Form};
    let mut lines = vec![("A".to_string(), format!("= {}", x.to_latex()))];
    match rcbi_order::form(x)? {
        Form::Zero => lines.push((String::new(), "\\equiv^{1}_{1} \\top".to_string())),
        Form::Successor(p) => lines.push(("\\operatorname{pred}(A)".to_string(), format!("= {}", p.to_latex()))),
        Form::Limit => {
            for n in 1..=k {
                let y = rcbi_order::approx(x, n).ok_or(crate::i18n::tr("極限形なのに近似が作れません（バグです）", "no approximation for a limit form (a bug)"))?;
                lines.push((format!("(A)_{{{n}}}"), format!("= {}", y.to_latex())));
            }
        }
    }
    Ok(align(&lines))
}

/// RC_BI の順序での比較を数式に：`A <^{1}_{1} B`、`A \equiv^{1}_{1} B`。
pub fn rcbi_relation(a: &str, o: std::cmp::Ordering, b: &str) -> String {
    let rel = match o {
        std::cmp::Ordering::Less => "<^{1}_{1}",
        std::cmp::Ordering::Equal => "\\equiv^{1}_{1}",
        std::cmp::Ordering::Greater => ">^{1}_{1}",
    };
    format!("{a} {rel} {b}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names() {
        assert_eq!(var("p"), "p");
        assert_eq!(var("p12"), "p_{12}");
        assert_eq!(var("foo"), "\\mathit{foo}");
        assert_eq!(var("a_b"), "a_{b}");
        assert_eq!(rule_name("Cut"), "\\mathrm{Cut}");
        assert_eq!(rule_name("∧E1"), "{\\land}\\mathrm{E}_{1}");
        assert_eq!(rule_name("∧I"), "{\\land}\\mathrm{I}");
        assert_eq!(rule_name("⊤"), "\\top");
        assert_eq!(rule_name("R3a"), "\\mathrm{R3a}");
    }

    #[test]
    fn summary() {
        let a: Veblen = "ε_0".parse().unwrap();
        let s = ordinal_summary(None, &a, 3, &[]);
        assert!(s.contains("\\alpha &= \\varepsilon_{0}"), "{s}");
        assert!(s.contains("o^{*}(((())))"), "{s}");
        assert!(s.contains("\\alpha[2] &="), "{s}");
    }
}
