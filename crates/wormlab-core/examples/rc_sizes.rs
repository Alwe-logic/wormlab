//! 実験：RC の導出器を大量のランダムなシーケントで試し、
//! (1) 閉包モデルの判定と一致するか、(2) 導出の大きさが入力の大きさにどう依存するか を見る。
//!
//!   cargo run --release -p wormlab-core --example rc_sizes

use wormlab_core::Spf;
use wormlab_core::rc::entails;
use wormlab_core::rcproof::{check, derive};

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

/// 記号の数がおよそ size のランダムな式
fn random_spf(r: &mut Rng, size: usize) -> Spf {
    if size <= 1 {
        return match r.below(3) {
            0 => Spf::Top,
            1 => Spf::var("p"),
            _ => Spf::var("q"),
        };
    }
    if r.below(2) == 0 {
        Spf::dia(r.below(3) as u32, random_spf(r, size - 1))
    } else {
        let left = 1 + r.below((size - 1) as u64) as usize;
        Spf::and(random_spf(r, left), random_spf(r, size - left))
    }
}

fn main() {
    let mut r = Rng(2026);
    let (mut agree, mut total, mut proved) = (0, 0, 0);
    println!("size,proved,dag,tree,facts_total,facts_used");
    for size in [4usize, 8, 12, 16, 20, 24] {
        let mut done = 0;
        let mut tries = 0;
        while done < 30 && tries < 200_000 {
            tries += 1;
            let a = random_spf(&mut r, size);
            // 右辺は左辺から少し崩して作る（真の例が多くなるように）
            let b = if r.below(2) == 0 { random_spf(&mut r, size / 2) } else {
                let k = r.below(3) as u32;
                Spf::dia(k, random_spf(&mut r, size / 3))
            };
            let holds = entails(&a, &b);
            let res = derive(&a, &b);
            total += 1;
            if res.is_ok() == holds { agree += 1 } else { println!("不一致: {a} ⊢ {b}") }
            if let Ok((p, st)) = res {
                check(&p).expect("検査を通るはず");
                proved += 1;
                done += 1;
                println!("{size},1,{},{},{},{}", p.dag_size(), p.tree_size(), st.facts_total, st.facts_used);
            }
        }
    }
    eprintln!("閉包との一致 {agree}/{total}、導出できた {proved}");
}
