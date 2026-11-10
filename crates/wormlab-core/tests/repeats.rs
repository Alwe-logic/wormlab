//! 繰り返しでまとめる書き方（repeats）のテスト。

use proptest::prelude::*;
use wormlab_core::repeats::{Piece, compress, expand, shown_len};
use wormlab_core::{Bracket, Worm, repeats};

/// u がそれより短い列の繰り返しでないか（原始的か）。u が原始的 ⟺ u をずらした（回した）列が
/// どれも u と違う。
fn primitive(u: &[u8]) -> bool {
    (1..u.len()).all(|p| u.iter().cycle().skip(p).take(u.len()).ne(u.iter()))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    // まとめた形を広げると、元の列に戻る（入れ子の中も含めて）
    #[test]
    fn expand_restores(t in prop::collection::vec(0u8..3, 0..300)) {
        let p = compress(&t);
        let back: Vec<u8> = expand(&p).into_iter().map(|i| t[i]).collect();
        prop_assert_eq!(back, t.clone());
        prop_assert!(shown_len(&p) <= t.len());
    }

    // u^k（u は原始的、k ≥ 2）は、1 つの繰り返し (u)^k にまとまる
    #[test]
    fn power_is_one_piece(u in prop::collection::vec(0u8..3, 1..8), k in 2usize..7) {
        prop_assume!(primitive(&u));
        let t: Vec<u8> = u.iter().copied().cycle().take(u.len() * k).collect();
        let p = compress(&t);
        prop_assert_eq!(p.len(), 1);
        let Piece::Rep(inner, kk) = &p[0] else { return Err(TestCaseError::fail("繰り返しでない")) };
        prop_assert_eq!(*kk, k);
        prop_assert_eq!(expand(inner).len(), u.len());
    }

    // battle の worm：まとめた形の文字の数は元以下で、まとめた形の ^k を広げると元の worm に戻る
    #[test]
    fn battle_worms(start in prop::collection::vec(0u32..3, 1..4), step in 0usize..12) {
        let w = Worm::new(start);
        let Some(cur) = w.battle().nth(step) else { return Ok(()) };
        let c = repeats::worm(&cur);
        prop_assert!(c.shown <= cur.len());
        prop_assert_eq!(unfold(&c.text), cur.to_string());
    }

    // 括弧語も：[ ] と ^k を広げると元の語に戻る
    #[test]
    fn battle_brackets(step in 0usize..8, which in 0usize..4) {
        let b: Bracket = ["((()))", "(()(()))", "((())())", "(())()(())"][which].parse().unwrap();
        let Some(cur) = b.battle().nth(step) else { return Ok(()) };
        let c = repeats::bracket(&cur);
        prop_assert_eq!(unfold(&c.text.replace('[', "{").replace(']', "}")), cur.to_string());
    }
}

/// まとめた形の文字（`(2 0)^3 1^2`、`{(())()}^2(()^3)`）を広げる。worm は ( ) で、括弧語は { } でくくる
/// （括弧語の ( ) は語そのものの記号で、1 文字の繰り返し (x)^k はその文字ごと繰り返す）。
fn unfold(s: &str) -> String {
    if s == "⊤" {
        return s.to_string(); // battle が終わった（空の worm・括弧語）
    }
    let worm = !s.contains('{') && !s.contains("()");
    let cs: Vec<char> = s.chars().collect();
    let (out, _) = unfold_from(&cs, 0, worm);
    if worm { out.split_whitespace().collect::<Vec<_>>().join(" ") } else { out }
}

/// i から読み、閉じ括弧（worm は ')'、括弧語は '}'）か終わりまでを広げる。(広げた文字, 読み終えた位置)
fn unfold_from(cs: &[char], mut i: usize, worm: bool) -> (String, usize) {
    let (open, close) = if worm { ('(', ')') } else { ('{', '}') };
    let mut out = String::new();
    // 直前の「繰り返しの単位」（^k が付くもの）
    let mut last_start = 0;
    while i < cs.len() {
        let c = cs[i];
        if c == close {
            return (out, i + 1);
        }
        if c == open {
            let (inner, j) = unfold_from(cs, i + 1, worm);
            last_start = out.len();
            out.push_str(&inner);
            if worm {
                out.push(' ');
            }
            i = j;
        } else if c == '^' {
            let mut j = i + 1;
            while j < cs.len() && cs[j].is_ascii_digit() {
                j += 1;
            }
            let k: usize = cs[i + 1..j].iter().collect::<String>().parse().unwrap();
            let unit = out[last_start..].to_string();
            for _ in 1..k {
                out.push_str(&unit);
            }
            i = j;
        } else if worm && c == ' ' {
            i += 1;
        } else if worm {
            // 自然数の文字
            let mut j = i;
            while j < cs.len() && cs[j].is_ascii_digit() {
                j += 1;
            }
            last_start = out.len();
            out.push_str(&cs[i..j].iter().collect::<String>());
            out.push(' ');
            i = j;
        } else {
            // 括弧語の文字 (…)：対応する ) まで（中も ^k を広げる）
            let (letter, j) = bracket_letter(cs, i);
            last_start = out.len();
            out.push_str(&letter);
            i = j;
        }
    }
    (out, i)
}

/// cs[i] = '(' から始まる括弧語の文字を、中の ^k も広げて読む。
fn bracket_letter(cs: &[char], i: usize) -> (String, usize) {
    // 中身は「文字の並び」なので、中身だけを取り出して括弧語として広げる
    let mut depth = 0;
    let mut j = i;
    loop {
        match cs[j] {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            _ => {}
        }
        j += 1;
    }
    let inner: Vec<char> = cs[i + 1..j].to_vec();
    let (body, _) = unfold_from(&inner, 0, false);
    (format!("({body})"), j + 1)
}
