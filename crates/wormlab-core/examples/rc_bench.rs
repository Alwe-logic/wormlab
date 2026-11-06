//! 計測：RC の 2 つの判定法（閉包モデル `rc::decide` と局所規則 `rc::entails`）と、
//! 導出器 `rcproof::derive` の時間・大きさ。
//!
//!   cargo run --release -p wormlab-core --example rc_bench            # 判定の時間
//!   cargo run --release -p wormlab-core --example rc_bench -- agree   # 2 つの判定法の突き合わせ
//!   cargo run --release -p wormlab-core --example rc_bench -- derive  # 導出の時間と大きさ
//!
//! 環境変数 SIZES（例 `SIZES=40,80`）と FAMS（例 `FAMS=worm`）で絞れる。

use std::time::Instant;
use wormlab_core::Spf;
use wormlab_core::rc::{decide, entails};
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

/// 記号の数がおよそ size、モダリティ 0〜k−1 のランダムな式
fn random_spf(r: &mut Rng, size: usize, k: u64) -> Spf {
    if size <= 1 {
        return match r.below(3) {
            0 => Spf::Top,
            1 => Spf::var("p"),
            _ => Spf::var("q"),
        };
    }
    if r.below(2) == 0 {
        Spf::dia(r.below(k) as u32, random_spf(r, size - 1, k))
    } else {
        let left = 1 + r.below((size - 1) as u64) as usize;
        Spf::and(random_spf(r, left, k), random_spf(r, size - left, k))
    }
}

/// 長さ len、文字 0〜k−1 のランダムな worm
fn worm(r: &mut Rng, len: usize, k: u64) -> Spf {
    (0..len).fold(Spf::Top, |acc, _| Spf::dia(r.below(k) as u32, acc))
}

/// 式を少し崩す（連言の片方を捨てる、⟨⟩ を外す、番号を下げる）。A ⊢ weaken(A) になりやすい。
fn weaken(r: &mut Rng, a: &Spf) -> Spf {
    match a {
        Spf::And(x, y) => match r.below(3) {
            0 => weaken(r, x),
            1 => weaken(r, y),
            _ => Spf::and(weaken(r, x), weaken(r, y)),
        },
        Spf::Dia(m, x) => {
            let m2 = if *m > 0 && r.below(3) == 0 { r.below(*m as u64) as u32 } else { *m };
            if r.below(6) == 0 { weaken(r, x) } else { Spf::dia(m2, weaken(r, x)) }
        }
        other => other.clone(),
    }
}

fn time<T>(f: impl FnOnce() -> T) -> (T, f64) {
    let t = Instant::now();
    let v = f();
    (v, t.elapsed().as_secs_f64() * 1e3)
}

fn env_list<T: std::str::FromStr + Clone>(name: &str, default: &[T]) -> Vec<T> {
    match std::env::var(name) {
        Ok(v) => v.split(',').filter_map(|x| x.parse().ok()).collect(),
        Err(_) => default.to_vec(),
    }
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "decide".into());
    let mut r = Rng(2026);
    match mode.as_str() {
        "agree" => {
            let (mut n, mut t) = (0, 0);
            for i in 0..200_000usize {
                let size = 2 + (i % 14);
                let k = 1 + (i % 4) as u64;
                let a = random_spf(&mut r, size, k);
                let b = if i % 2 == 0 { random_spf(&mut r, 1 + size / 2, k) } else { weaken(&mut r, &a) };
                let (x, y) = (decide(&a, &b).holds, entails(&a, &b));
                assert_eq!(x, y, "{a} ⊢ {b}");
                n += 1;
                t += x as usize;
            }
            println!("閉包と局所規則が {n} 件で一致（うち真 {t} 件）");
        }
        "decide" => {
            let sizes: Vec<usize> = env_list("SIZES", &[100, 200, 400, 800]);
            let fams: Vec<String> = env_list("FAMS", &["random".to_string(), "worm".into(), "worm-many".into()]);
            println!("family,size_a,size_b,modalities,closure_ms,local_ms,holds");
            for &size in &sizes {
                for fam in &fams {
                    let (a, b) = match fam.as_str() {
                        "random" => {
                            let a = random_spf(&mut r, size, 4);
                            let b = weaken(&mut r, &a);
                            (a, b)
                        }
                        "worm" => (worm(&mut r, size, 4), Spf::dia(0, worm(&mut r, size / 2, 4))),
                        // モダリティの種類が多い worm（閉包が重くなる）
                        _ => {
                            let k = (size / 4) as u64;
                            (worm(&mut r, size, k), Spf::dia(0, worm(&mut r, size / 2, k)))
                        }
                    };
                    let (h1, t1) = time(|| decide(&a, &b).holds);
                    let (h2, t2) = time(|| entails(&a, &b));
                    assert_eq!(h1, h2, "{a} ⊢ {b}");
                    println!("{fam},{},{},{},{t1:.2},{t2:.3},{h2}", a.size(), b.size(), a.modalities().len());
                }
            }
        }
        _ => {
            let sizes: Vec<usize> = env_list("SIZES", &[20, 40, 80, 160]);
            let fams: Vec<String> = env_list("FAMS", &["random".to_string(), "worm".into()]);
            println!("family,size_a,size_b,ms,dag,tree,facts_total,facts_used,max_sequent");
            for &size in &sizes {
                for fam in &fams {
                    let mut done = 0;
                    for _ in 0..1000 {
                        if done == 3 {
                            break;
                        }
                        let a = if fam == "worm" { worm(&mut r, size, 4) } else { random_spf(&mut r, size, 4) };
                        let b = weaken(&mut r, &a);
                        if !entails(&a, &b) {
                            continue;
                        }
                        let (res, ms) = time(|| derive(&a, &b));
                        let (p, st) = res.expect("真なので導出がある");
                        check(&p).expect("検査を通るはず");
                        let max_seq = p.nodes.iter().map(|nd| nd.conclusion.lhs.size() + nd.conclusion.rhs.size()).max().unwrap_or(0);
                        println!(
                            "{fam},{},{},{ms:.1},{},{},{},{},{max_seq}",
                            a.size(),
                            b.size(),
                            p.dag_size(),
                            p.tree_size(),
                            st.facts_total,
                            st.facts_used
                        );
                        done += 1;
                    }
                }
            }
        }
    }
}
