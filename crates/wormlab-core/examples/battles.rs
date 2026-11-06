//! 実験：worm（括弧語）の battle と、順序数の標準基本列による battle の比較。
//!
//! 同じ順序数 α から出発して、
//! - worm battle：α の正規形の括弧語に、括弧語の基本列 a{k} を k = 1, 2, … と適用
//! - 標準 battle：α ← α[k]（後続なら直前）を k = 1, 2, … と適用
//!
//! した回数（0 / ⊤ に着くまで）と、最初の数ステップの順序数を並べる。
//!
//!   cargo run --release -p wormlab-core --example battles

use wormlab_core::hierarchy::{Budget, hardy, ordinal_battle_length, worm_battle_length_of};
use wormlab_core::{Bracket, Veblen};

fn main() {
    let budget = Budget { max_steps: 30_000_000 };
    println!("{:<10} {:>14} {:>14} {:>14}", "α", "worm battle", "標準 battle", "H_α(1)");
    for s in ["3", "ω", "ω + 1", "ω + 2", "ω·2", "ω·2 + 1", "ω·3", "ω^2", "ω^2 + 1", "ω^2 + ω", "ω^2 + ω + 1", "ω^2 + ω·2"] {
        let a: Veblen = s.parse().unwrap();
        let fmt = |x: Option<u64>| x.map_or("（打ち切り）".to_string(), |v| v.to_string());
        let wb = worm_battle_length_of(&a, budget);
        let ob = ordinal_battle_length(&a, 1, budget);
        let h = hardy(&a, 1, budget).map(|x| x as u64);
        println!("{:<10} {:>14} {:>14} {:>14}", s, fmt(wb), fmt(ob), fmt(h));
    }

    println!();
    println!("最初の数ステップ（左：worm battle、右：標準 battle）");
    for s in ["ω^2", "ε_0"] {
        let a: Veblen = s.parse().unwrap();
        println!("α = {s}");
        let worm: Vec<String> = Bracket::from_ordinal(&a).battle().take(5).map(|b| b.ordinal().to_string()).collect();
        let mut std = vec![a.to_string()];
        let mut x = a.clone();
        for k in 1..5u64 {
            match x.fundamental(k) {
                Some(y) => {
                    std.push(y.to_string());
                    x = y;
                }
                None => break,
            }
        }
        for (i, (w, o)) in worm.iter().zip(std.iter()).enumerate() {
            println!("  {i}: {w:<36} {o}");
        }
    }
}
