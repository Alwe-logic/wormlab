//! 実験：大きめのランダムな閉じた式 A について、RC_BI の有限モデル M_A の大きさを測り、
//! M_A が本当に RC_BIω モデルか（フレーム条件 I〜IV）と、根で A が真かを確かめる。
//! フレーム条件の検査は総当たりで重いので、点が 400 個以下のモデルだけで行う。
//! 最後に、↓ の入れ子の深さごとの点の数をまとめる（入れ子 1 段ごとにおよそ倍になる）。
//!
//!   cargo run --release -p wormlab-core --example rcbi_sizes

use std::collections::BTreeMap;
use std::time::Instant;
use wormlab_core::rcbi::{Formula, Model};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// 記号の数がおよそ size のランダムな閉じた式
fn random(r: &mut Rng, size: usize) -> Formula {
    if size <= 1 {
        return Formula::Top;
    }
    match r.below(9) {
        0 | 1 => {
            let left = 1 + r.below((size - 1) as u64) as usize;
            Formula::and(random(r, left), random(r, size - left))
        }
        2 | 3 => Formula::one(1 + r.below(3) as u32, random(r, size - 1)),
        4 => Formula::one_omega(random(r, size - 1)),
        5 | 6 => Formula::two(2 + r.below(2) as u32, random(r, size - 1)),
        7 => Formula::down(random(r, size - 1)),
        _ => Formula::nabla(random(r, size - 1)),
    }
}

/// ↓ の入れ子の深さ
fn down_depth(a: &Formula) -> usize {
    match a {
        Formula::Top | Formula::Var(_) => 0,
        Formula::And(x, y) => down_depth(x).max(down_depth(y)),
        Formula::Down(x) => 1 + down_depth(x),
        Formula::Dia(_, _, x) | Formula::Nabla(x) => down_depth(x),
    }
}

fn main() {
    let mut r = Rng(2026);
    let mut by_depth: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let mut checked = 0;
    println!("size,down_depth,points,ms");
    for size in [5usize, 10, 15, 20, 25, 30] {
        let (mut total, mut max, mut ms_max) = (0usize, 0usize, 0u128);
        for _ in 0..100 {
            let a = random(&mut r, size);
            let t = Instant::now();
            let m = Model::of(&a, 3);
            let ms = t.elapsed().as_millis();
            if m.num_points() <= 400 {
                let v = m.frame_violations();
                assert!(v.is_empty(), "{a}: {v:?}");
                checked += 1;
            }
            assert!(m.holds(0, &a), "{a} が根で偽");
            println!("{size},{},{},{ms}", down_depth(&a), m.num_points());
            by_depth.entry(down_depth(&a)).or_default().push(m.num_points());
            total += m.num_points();
            max = max.max(m.num_points());
            ms_max = ms_max.max(ms);
        }
        eprintln!("記号数 {size}: M_A の点の数 平均 {:.1} / 最大 {max}、構成の最長 {ms_max} ms", total as f64 / 100.0);
    }
    eprintln!("フレーム条件を調べた {checked} 個のモデルはすべて RC_BIω モデル、全 600 個で根で A が真");
    for (d, v) in by_depth {
        let avg = v.iter().sum::<usize>() as f64 / v.len() as f64;
        eprintln!("↓ の入れ子 {d} 段：{} 個、点の数 平均 {avg:.1} / 最大 {}", v.len(), v.iter().max().unwrap());
    }
}
