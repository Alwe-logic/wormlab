//! 定義集（glossary）のテスト：鍵と関連・一般と特殊のつながり、LaTeX の形、例が実装から作れること
//! （場合ごとに 1 つ）、英語の出力に日本語が混ざらないこと、式の標準形の定義（expr::definitions）を全部含むこと。

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
    assert_eq!(glossary::all().len(), 5);
    assert!(glossary::get("worm-battle").is_some());
    assert!(glossary::get("no-such-key").is_none());
}

#[test]
fn general_and_special_cases_are_linked_both_ways() {
    let all = entries();
    let keys: HashSet<&str> = all.iter().map(|e| e.key).collect();
    for e in &all {
        for g in &e.general {
            assert!(keys.contains(g), "{} の一般の場合 {g} がない", e.key);
            let ge = glossary::get(g).unwrap();
            assert!(ge.special.contains(&e.key), "{g} の特殊な場合に {} がない", e.key);
        }
        for s in &e.special {
            assert!(glossary::get(s).unwrap().general.contains(&e.key), "{s} の一般の場合に {} がない", e.key);
        }
    }
    // ユーザーの希望で足した特殊な場合（Cantor 標準形・普通の worm）と、独立させた括弧語の基本列
    let fund: Vec<&str> = glossary::all().into_iter().find(|c| c.id == "fundamental").unwrap().entries.iter().map(|e| e.key).collect();
    assert_eq!(fund, ["cnf-fs", "fs", "nat-worm-fs", "bracket-fs", "worm-fs", "rcbi-fs"]);
    assert_eq!(glossary::get("cnf-fs").unwrap().general, ["fs"]);
    assert_eq!(glossary::get("nat-worm-fs").unwrap().general, ["bracket-fs"]);
    assert_eq!(glossary::get("cnf").unwrap().general, ["normal"]);
    assert_eq!(glossary::get("worm-battle").unwrap().general, ["bracket-battle"]);
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
        // 場合ごとに 1 つ：場合の言葉と例の両方があり、同じ場合を 2 度書かない
        let cases: HashSet<&str> = e.examples.iter().map(|x| x.case.as_str()).collect();
        assert_eq!(cases.len(), e.examples.len(), "{} で同じ場合が 2 度ある", e.key);
        for x in &e.examples {
            assert!(!x.case.is_empty() && !x.text.is_empty(), "{}: {x:?}", e.key);
            // 同じ場合のほかの例：空でなく、代表の例とも互いにも重ならない
            let mut seen: HashSet<&str> = HashSet::from([x.text.as_str()]);
            for m in &x.more {
                assert!(!m.is_empty() && seen.insert(m.as_str()), "{}: {} の例が重なる: {m}", e.key, x.case);
            }
        }
    }
    for k in KEYS_WITH_EXAMPLES {
        assert!(all.iter().any(|e| e.key == *k), "例の鍵 {k} の定義がない");
    }
}

#[test]
fn there_are_many_examples() {
    // ユーザーの希望「もっとたくさん例があるといい」：場合ごとの代表に加えて、ほかの例をたくさん
    let cases: Vec<_> = entries().into_iter().flat_map(|e| e.examples).collect();
    let total: usize = cases.iter().map(|x| 1 + x.more.len()).sum();
    let with_more = cases.iter().filter(|x| !x.more.is_empty()).count();
    assert!(total >= 500, "例の数 {total}");
    assert!(with_more * 10 >= cases.len() * 9, "ほかの例のある場合 {with_more} / {}", cases.len());
}

#[test]
fn english_output_has_no_japanese() {
    set_lang(Lang::En);
    for c in glossary::all() {
        assert!(!has_japanese(&c.name) && !has_japanese(&c.lead), "{}", c.id);
        for e in c.entries {
            let examples: Vec<String> = e.examples.iter().flat_map(|x| [vec![x.case.clone(), x.text.clone()], x.more.clone()].concat()).collect();
            let texts = [vec![e.name.clone(), e.symbol.clone(), e.source.clone()], e.lines.clone(), examples].concat();
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
    let ex = |k: &str| glossary::get(k).unwrap().examples.iter().map(|x| x.text.clone()).collect::<Vec<_>>().join(" | ");
    let all = |k: &str| glossary::get(k).unwrap().examples.iter().flat_map(|x| [vec![x.text.clone()], x.more.clone()].concat()).collect::<Vec<_>>().join(" | ");
    // ほかの例の代表的な値
    assert!(all("cnf-fs").contains("ε_0[4] = ω^ω^ω") && all("cnf-fs").contains("ω[5] = 5"), "{}", all("cnf-fs"));
    assert!(all("nat-worm-fs").contains("(1){3} = 0 0 0 0") && all("nat-worm-fs").contains("o((2){1}) = o(1 1) = ω^2 = D(ω^ω, 2)"), "{}", all("nat-worm-fs"));
    assert!(all("bnf").contains("2 0 1 ≡ 2") && all("pow").contains("(ε_0)^0 = 1"), "{} {}", all("bnf"), all("pow"));
    assert!(all("hyp").contains("e^ω(ω) = ε_ω") && all("worm-o").contains("o(2) = ω^ω"));
    assert!(ex("worm-battle").contains("2 0 2 → 1 1 0 2 → 0 1 0 1 0 1 0 2"), "{}", ex("worm-battle"));
    assert!(ex("ordinal-battle").contains("ω^2 → [1] ω → [2] 2 → [3] 1 → [4] 0"));
    assert!(ex("thm52").contains("G(0) = 1") && ex("thm52").contains("G(1) = 2"));
    assert!(ex("hyp").contains("e^ω(1) = ε_0") && ex("hyp").contains("e(ω) = ω^ω"), "{}", ex("hyp"));
    assert!(ex("cnf-fs").contains("ε_0[3] = ω^ω") && ex("cnf-fs").contains("(ω^2·2)[3] = ω^2 + ω·3"), "{}", ex("cnf-fs"));
    assert!(ex("fs").contains("φ(2, 0)[2] = ε_(ε_0)") && ex("fs").contains("φ(ω, 0)[3] = φ(3, 0)"), "{}", ex("fs"));
    assert!(ex("nat-worm-fs").contains("(2 0 2){1} = 1 1 0 2") && ex("nat-worm-fs").contains("ω·3 + 1 = D(ω^2, 3)"), "{}", ex("nat-worm-fs"));
    assert!(ex("bracket-fs").contains("a{1} = (()())(()())"), "{}", ex("bracket-fs"));
    assert!(ex("worm-fs").contains("ω^2{1} = ω·2 + 1"));
    assert!(ex("hardy").contains("H_ω(3) = 6"), "{}", ex("hardy"));
    assert!(ex("fgh").contains("f_2(3) = H_{ω^2}(3) = 24"), "{}", ex("fgh"));
    assert!(ex("worm-o").contains("o(1 0 2) = ω^ω + ω"));
    assert!(ex("worm-o-transfinite").contains("o(⟨ω^2⟩) = φ(2, 0)"));
    assert!(ex("iworm").contains("p(((()))Ω) = ψ(ε_(Ω + 1))"), "{}", ex("iworm"));
    assert!(ex("bc-tau").contains("⟨ω⟩p"));
    assert!(ex("cnf").contains("(ω, 2)") && ex("cnf").contains("ε_0 = ω^ε_0"), "{}", ex("cnf"));
    assert!(ex("rcbi-order").contains("⊤ <¹₁ ⟨1⟩₁⊤ <¹₁ ⟨1⟩₂⊤ <¹₁ ↓⊤ <¹₁ ⟨2⟩₂⊤ <¹₁ ⟨2⟩₃⊤"));
    // フレーム条件 I〜IV に当たる式はどれも導出でき、M_A はフレーム条件を満たす（違反 0）
    let frame = glossary::get("rcbi-frame").unwrap().examples;
    assert!(frame[..4].iter().all(|x| x.text.ends_with("導出できる")), "{frame:?}");
    assert!(frame[4].text.ends_with(" 0"), "{frame:?}");
    // RC のフレーム条件（推移性・単調性・J）に当たる式は導出でき、最後の例は導出できない
    let rc = glossary::get("rc-frame").unwrap().examples;
    assert!(rc[..3].iter().all(|x| x.text.ends_with("導出できる")) && rc[3].text.ends_with("導出できない"), "{rc:?}");
}
