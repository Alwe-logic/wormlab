//! LaTeX への書き出しの性質ベースのテスト。
//!
//! - 書き出した LaTeX を元の書き方に戻して読み直すと、元の式・順序数に戻る（往復）
//! - 括弧 { } と \begin・\end の対応がとれている
//! - 証明木の推論の数は木に展開したノード数、行番号つきの一覧の行数は DAG のノード数
//!
//! （実際に pdflatex にかけた確認は、CLI の出力で別に行っている。design.md を参照）

use proptest::prelude::*;
use wormlab_core::latex::{self, ToLatex};
use wormlab_core::rcbi::Formula;
use wormlab_core::rcproof::derive;
use wormlab_core::{Bracket, Spf, Veblen, Worm, bc, rcbi};

/// { } の対応と、\begin{…} と \end{…} の数がそろっているか。
fn balanced(s: &str) -> bool {
    let mut depth = 0i64;
    let mut prev = ' ';
    for c in s.chars() {
        // \{ と \} は文字としての括弧なので数えない
        if prev != '\\' {
            match c {
                '{' => depth += 1,
                '}' => depth -= 1,
                _ => {}
            }
            if depth < 0 {
                return false;
            }
        }
        prev = if prev == '\\' && c == '\\' { ' ' } else { c };
    }
    depth == 0 && s.matches("\\begin{").count() == s.matches("\\end{").count()
}

/// LaTeX を、パーサが読める元の書き方に戻す（往復の確認用）。
fn unlatex(s: &str) -> String {
    s.replace("\\langle ", "<")
        .replace("\\rangle", ">")
        .replace("\\land", "&")
        .replace("\\top", "T")
        .replace("\\vdash", "|-")
        .replace("{\\downarrow}", "D")
        .replace("\\nabla", "N")
        .replace("\\varepsilon_", "ε_")
        .replace("\\varphi", "φ")
        .replace("\\omega", "ω")
        .replace("\\cdot", "·")
        .replace('{', "(")
        .replace('}', ")")
}

fn veblen() -> impl Strategy<Value = Veblen> {
    let leaf = (0u64..4).prop_map(Veblen::nat);
    leaf.prop_recursive(4, 32, 3, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| a + b),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Veblen::phi(a, b)),
            inner.clone().prop_map(Veblen::omega_pow),
            (inner, 1u64..4).prop_map(|(a, n)| a.mul_nat(n)),
        ]
    })
}

fn spf() -> impl Strategy<Value = Spf> {
    let leaf = prop_oneof![Just(Spf::Top), Just(Spf::var("p")), Just(Spf::var("q"))];
    leaf.prop_recursive(4, 16, 2, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Spf::and(a, b)),
            (0u32..3, inner).prop_map(|(n, a)| Spf::dia(n, a)),
        ]
    })
}

fn rcbi_formula() -> impl Strategy<Value = Formula> {
    let leaf = Just(Formula::Top);
    leaf.prop_recursive(4, 10, 2, |inner| {
        prop_oneof![
            2 => (inner.clone(), inner.clone()).prop_map(|(a, b)| Formula::and(a, b)),
            3 => (1u32..4, inner.clone()).prop_map(|(k, a)| Formula::one(k, a)),
            1 => inner.clone().prop_map(Formula::one_omega),
            2 => (2u32..4, inner.clone()).prop_map(|(k, a)| Formula::two(k, a)),
            2 => inner.clone().prop_map(Formula::down),
            1 => inner.prop_map(Formula::nabla),
        ]
    })
}

fn bracket() -> impl Strategy<Value = Bracket> {
    let leaf = Just(Bracket::top());
    leaf.prop_recursive(4, 24, 3, |inner| prop::collection::vec(inner, 0..4).prop_map(Bracket::new))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    #[test]
    fn veblen_round_trip(a in veblen()) {
        let t = a.to_latex();
        prop_assert!(balanced(&t), "{}", t);
        let back: Veblen = unlatex(&t).parse().map_err(|e| TestCaseError::fail(format!("{t}: {e}")))?;
        prop_assert_eq!(back, a);
    }

    #[test]
    fn worm_round_trip(w in prop::collection::vec(0u32..5, 0..8).prop_map(Worm::new)) {
        let t = w.to_latex();
        prop_assert!(balanced(&t));
        let back: Worm = unlatex(&t).parse().map_err(|e| TestCaseError::fail(format!("{t}: {e}")))?;
        prop_assert_eq!(back, w);
    }

    #[test]
    fn ordinal_worm_round_trip(a in veblen()) {
        // 標準形の worm（文字が順序数）を書き出して読み直す
        let w = Worm::from_veblen(&a);
        let t = w.to_latex();
        prop_assert!(balanced(&t), "{}", t);
        let back: Worm<Veblen> = unlatex(&t).parse().map_err(|e| TestCaseError::fail(format!("{t}: {e}")))?;
        prop_assert_eq!(back, w);
    }

    #[test]
    fn bracket_round_trip(b in bracket()) {
        let t = b.to_latex();
        let back: Bracket = unlatex(&t).replace('T', "").parse().map_err(|e| TestCaseError::fail(format!("{t}: {e}")))?;
        prop_assert_eq!(back, b);
    }

    #[test]
    fn spf_round_trip(a in spf()) {
        let t = a.to_latex();
        prop_assert!(balanced(&t));
        let back: Spf = unlatex(&t).parse().map_err(|e| TestCaseError::fail(format!("{t}: {e}")))?;
        prop_assert_eq!(back, a);
    }

    #[test]
    fn rcbi_round_trip(a in rcbi_formula()) {
        let t = a.to_latex();
        prop_assert!(balanced(&t), "{}", t);
        // 添字 _{2}・_{ω} はパーサの書き方 _2・_w に
        let mut u = t.replace("_{\\omega}", "_w");
        for k in 1..10 {
            u = u.replace(&format!("_{{{k}}}"), &format!("_{k}"));
        }
        let back: Formula = unlatex(&u).parse().map_err(|e| TestCaseError::fail(format!("{t}: {e}")))?;
        prop_assert_eq!(back, a);
    }

    /// RC の証明：木の推論の数 = 木のノード数、一覧の行数 = DAG のノード数
    #[test]
    fn rc_proof_latex(a in spf(), b in spf()) {
        if let Ok((p, _)) = derive(&a, &b) {
            let lines = latex::proof_lines(&p);
            prop_assert!(balanced(&lines));
            prop_assert_eq!(lines.matches(" \\\\\n").count(), p.dag_size());
            if let Some(tree) = latex::proof_tree(&p, 400) {
                prop_assert!(balanced(&tree));
                prop_assert_eq!(tree.matches("InfC{").count() as u128, p.tree_size());
                let leaves = p.nodes.iter().filter(|n| n.premises.is_empty()).count();
                let axioms = tree.matches("\\AxiomC{}").count();
                prop_assert!(axioms >= leaves);
            } else {
                prop_assert!(p.tree_size() > 400);
            }
        }
    }

    /// BC の証明と、ふつうでない括弧語のモダリティ
    #[test]
    fn bc_proof_latex(b in bracket(), a in bracket()) {
        let goal = bc::BSeq::lt(&b, &a);
        if let Ok((p, _)) = bc::derive(&goal.lhs, &goal.rhs) {
            prop_assert!(balanced(&latex::proof_lines(&p)));
            if let Some(tree) = latex::proof_tree(&p, latex::TREE_LIMIT) {
                prop_assert!(balanced(&tree));
            }
        }
    }

    /// 順序数のまとめと、モデルの TikZ
    #[test]
    fn summaries_and_tikz(a in veblen(), f in rcbi_formula()) {
        prop_assert!(balanced(&latex::ordinal_block(None, &a, 4)));
        let m = rcbi::Model::of(&f, f.max_rank());
        let v = wormlab_core::modelview::ModelView::from_rcbi(&m, None);
        let all: Vec<String> = v.relations.iter().map(|r| r.name.clone()).collect();
        let t = v.tikz(&all, true);
        prop_assert!(balanced(&t));
        prop_assert_eq!(t.matches("\\node[pt").count(), m.num_points());
    }
}

#[test]
fn document_wraps() {
    let d = latex::document("\\[ x \\]");
    assert!(d.starts_with("\\documentclass"));
    assert!(d.contains("\\usepackage{bussproofs}"));
    assert!(d.trim_end().ends_with("\\end{document}"));
}
