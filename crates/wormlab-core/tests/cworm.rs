//! まとめたまま進める worm battle（cworm）のテスト：ふつうの battle（文字の列をそのまま持つ）と突き合わせる。

use proptest::prelude::*;
use wormlab_core::Worm;
use wormlab_core::cworm::{self, CWorm, Shape};

/// まとめた形を広げる
fn expand(shapes: &[Shape], out: &mut Vec<u32>) {
    for s in shapes {
        match s {
            Shape::Letter(x) => out.push(*x),
            Shape::Rep(inner, k) => {
                for _ in 0..*k {
                    expand(inner, out);
                }
            }
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    // 各ステップで、worm・長さ・順序数がふつうの battle と同じ。表示用の形を広げても同じ worm
    #[test]
    fn agrees_with_plain(letters in prop::collection::vec(0u32..4, 1..6)) {
        let w = Worm::new(letters);
        let mut c = CWorm::new(&w).unwrap();
        for (k, plain) in w.battle().enumerate().take(40) {
            if plain.len() > 5_000 {
                break;
            }
            let got = c.to_worm(10_000);
            prop_assert_eq!(got.as_ref(), Some(&plain), "{} の {} ステップ目", w, k);
            prop_assert_eq!(c.len().to_u64(), Some(plain.len() as u64));
            prop_assert_eq!(c.ordinal(), plain.ordinal());
            let v = c.view(100_000);
            prop_assert!(!v.truncated);
            let mut back = Vec::new();
            expand(&v.shapes, &mut back);
            prop_assert_eq!(back.as_slice(), plain.letters());
            // まとめた文字の数は元以下
            prop_assert!(cworm::shown(&v.shapes) <= plain.len());
            c.step(k as u64 + 1);
        }
    }

    // 表示を途中で切ったら、切った形は元の worm の先頭（広げると先頭の部分になる）
    #[test]
    fn truncated_view_is_prefix(letters in prop::collection::vec(0u32..4, 1..5), steps in 5u64..30, budget in 1usize..30) {
        let w = Worm::new(letters);
        let mut c = CWorm::new(&w).unwrap();
        for m in 1..=steps {
            c.step(m);
        }
        let Some(plain) = c.to_worm(200_000) else { return Ok(()) };
        let v = c.view(budget);
        prop_assert!(cworm::shown(&v.shapes) <= budget);
        let mut back = Vec::new();
        expand(&v.shapes, &mut back);
        // 切った所の繰り返しは、中身が途中まででも回数はそのまま：広げた長さは元を超えうるので、
        // 最初の文字の並びだけを比べる（中身の途中で切れた繰り返しの 1 回目まで）
        let first: Vec<u32> = {
            let mut out = Vec::new();
            fn once(shapes: &[Shape], out: &mut Vec<u32>) {
                for s in shapes {
                    match s {
                        Shape::Letter(x) => out.push(*x),
                        Shape::Rep(inner, _) => once(inner, out),
                    }
                }
            }
            if v.truncated { once(&v.shapes, &mut out) } else { out = back.clone() }
            out
        };
        if !v.truncated {
            prop_assert_eq!(back.as_slice(), plain.letters());
        } else {
            prop_assert!(!first.is_empty());
            prop_assert_eq!(first[0], plain.letters()[0]);
        }
    }
}
