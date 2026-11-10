//! 定義集（glossary）のテスト：鍵と関連のつながり、LaTeX の形、例が実装から作れること、
//! 英語の出力に日本語が混ざらないこと、式の標準形の定義（expr::definitions）を全部含むこと。

use std::collections::HashSet;
use wormlab_core::expr;
use wormlab_core::glossary::{self, Entry, KEYS_WITH_EXAMPLES};
use wormlab_core::i18n::{Lang, set_lang};

fn entries() -> Vec<Entry> {
    glossary::all().into_iter().flat_map(|c| c.entries).collect()
}

/// 日本語の文字（ひらがな・カタカナ・漢字・全角の記号）を含むか。
fn has_japanese(s: &str) -> bool {
    s.chars().any(|c| matches!(c, '\u{3040}'..='\u{30ff}' | '\u{4e00}'..='\u{9fff}' | '\u{3000}'..='\u{303f}' | '\u{ff01}'..='\u{ff60}'))
}

#[test]
fn keys_are_unique_and_related_keys_exist() {
    let all = entries();
    let keys: Vec<&str> = all.iter().map(|e| e.key).collect();
    let set: HashSet<&str> = keys.iter().copied().collect();
    assert_eq!(set.len(), keys.len(), "鍵が重なっている: {keys:?}");
    // 目次は記号で並べるので、記号も重ならないようにする
    let symbols: HashSet<&str> = all.iter().map(|e| e.symbol.as_str()).collect();
    assert_eq!(symbols.len(), all.len(), "記号が重なっている");
    for e in &all {
        assert!(e.key.chars().all(|c| c.is_ascii_alphanumeric() || c == '-'), "鍵は英数字とハイフン: {}", e.key);
        for r in &e.related {
            assert!(set.contains(r), "{} の関連 {r} がない", e.key);
            assert_ne!(*r, e.key, "{} が自分を関連に挙げている", e.key);
        }
        if let Some(t) = e.tab {
            assert!(["battle", "ordinal", "proof", "rules", "model"].contains(&t), "{} のタブ {t}", e.key);
        }
    }
    assert_eq!(glossary::all().len(), 4);
    assert!(glossary::get("worm-battle").is_some());
    assert!(glossary::get("no-such-key").is_none());
}

#[test]
fn includes_every_expression_definition() {
    for d in expr::definitions() {
        let e = glossary::get(d.key).unwrap_or_else(|| panic!("expr の定義 {} がない", d.key));
        assert_eq!(e.lines, d.lines, "{} の文が expr と違う", d.key);
    }
}

#[test]
fn entries_are_complete_and_latex_is_balanced() {
    for e in entries() {
        assert!(!e.name.is_empty() && !e.symbol.is_empty() && !e.source.is_empty(), "{}", e.key);
        assert!(!e.lines.is_empty(), "{} に定義の文がない", e.key);
        let t = &e.latex;
        assert!(t.starts_with("\\begin{align*}") && t.ends_with("\\end{align*}"), "{} の LaTeX は align*: {t}", e.key);
        // { } の対応（\{ \} は文字としての括弧なので数えない）
        let plain = t.replace("\\{", "").replace("\\}", "");
        let mut depth = 0i32;
        for c in plain.chars() {
            match c {
                '{' => depth += 1,
                '}' => depth -= 1,
                _ => {}
            }
            assert!(depth >= 0, "{} の LaTeX で }} が多い", e.key);
        }
        assert_eq!(depth, 0, "{} の LaTeX の {{ }} が合わない", e.key);
        assert_eq!(t.matches("\\begin{").count(), t.matches("\\end{").count(), "{} の \\begin と \\end", e.key);
        // LaTeX は言語によらない（pdflatex でそのまま通るように日本語を入れない）
        assert!(!has_japanese(t), "{} の LaTeX に日本語がある", e.key);
    }
}

#[test]
fn examples_come_from_the_implementation() {
    let all = entries();
    for e in &all {
        let expected = KEYS_WITH_EXAMPLES.contains(&e.key);
        assert_eq!(!e.examples.is_empty(), expected, "{} の例: {:?}", e.key, e.examples);
        if !expected {
            assert!(e.research, "例のない定義は研究中のものだけ: {}", e.key);
        }
    }
    for k in KEYS_WITH_EXAMPLES {
        assert!(all.iter().any(|e| e.key == *k), "例の鍵 {k} の定義がない");
    }
}

#[test]
fn english_output_has_no_japanese() {
    set_lang(Lang::En);
    for c in glossary::all() {
        assert!(!has_japanese(&c.name) && !has_japanese(&c.lead), "{}", c.id);
        for e in c.entries {
            let texts = [vec![e.name.clone(), e.symbol.clone(), e.source.clone()], e.lines.clone(), e.examples.clone()].concat();
            for s in texts {
                assert!(!has_japanese(&s), "{}: {s}", e.key);
            }
            if KEYS_WITH_EXAMPLES.contains(&e.key) {
                assert!(!e.examples.is_empty(), "英語でも例が出る: {}", e.key);
            }
        }
    }
    set_lang(Lang::Ja);
}

#[test]
fn known_values_in_the_examples() {
    // 例は実装から作るので、代表的な値がここで固定した値と同じかを見ておく（実装が変わったら気づける）
    let ex = |k: &str| glossary::get(k).unwrap().examples.join(" | ");
    assert!(ex("worm-battle").contains("A⦃1⦄ = 1 1 0 2"), "{}", ex("worm-battle"));
    assert!(ex("ordinal-battle").contains("ω^2 → [1] ω → [2] 2 → [3] 1 → [4] 0"));
    assert!(ex("thm52").contains("G(0) = 1") && ex("thm52").contains("G(1) = 2"));
    assert!(ex("hyp").contains("e^ω(1) = ε_0"));
    assert!(ex("fs").contains("ε_0[3] = ω^ω"));
    assert!(ex("worm-fs").contains("ω^2{1} = ω·2 + 1"));
    assert!(ex("hardy").contains("H_{ω^2}(3) = 24"));
    assert!(ex("fgh").contains("f_2(3) = 24"));
    assert!(ex("worm-o").contains("o(1 0 1) = ω·2"));
    assert!(ex("worm-o-transfinite").contains("o(⟨ω^2⟩) = φ(2, 0)"));
    assert!(ex("iworm").contains("p(w) = ψ(0)"));
    assert!(ex("bc-tau").contains("⟨ω⟩p"));
    assert!(ex("rcbi-order").contains("⊤ <¹₁ ⟨1⟩₁⊤ <¹₁ ⟨1⟩₂⊤ <¹₁ ↓⊤ <¹₁ ⟨2⟩₂⊤ <¹₁ ⟨2⟩₃⊤"));
    // M_A はフレーム条件 I〜IV を満たす（違反 0）
    for x in glossary::get("rcbi-frame").unwrap().examples {
        assert!(x.ends_with(" 0"), "{x}");
    }
}
