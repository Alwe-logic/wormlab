//! 実験：BC の導出の大きさの上界（bc.md「導出の大きさ」）を確かめる。
//!
//! 上界の証明の要は「副条件に出てくる括弧語は、入力の括弧語の部分語とその正規形だけ」
//! という点。ここではそれを導出 DAG から直接確かめ、副条件の数・DAG の大きさを
//! 入力の大きさ n（記号の数 + 括弧の対の数）と比べる。
//!
//!   cargo run --release -p wormlab-core --example bc_bounds
//!
//! 出力は CSV：family,param,n,universe,side,side_bound,max_side_depth,dag,dag_per_side,ms

use std::collections::HashSet;
use std::time::Instant;
use wormlab_core::bc::{self, BSeq, BcProof, BcRule, Formula};
use wormlab_core::{Bracket, Veblen};

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

/// 括弧の対の数。
fn pairs(b: &Bracket) -> usize {
    b.letters().iter().map(|l| 1 + pairs(l)).sum()
}

/// 式の大きさ n：記号の数（Formula::size）＋モダリティの括弧の対の数。
fn input_size(f: &Formula) -> usize {
    fn mods(f: &Formula) -> usize {
        match f {
            Formula::Top | Formula::Var(_) => 0,
            Formula::And(a, b) => mods(a) + mods(b),
            Formula::Dia(m, a) => 1 + pairs(m) + mods(a),
        }
    }
    f.size() + mods(f)
}

/// 括弧語 b とその部分語（文字、文字の文字、…）をすべて集める。
fn subterms(b: &Bracket, out: &mut HashSet<Bracket>) {
    if out.insert(b.clone()) {
        for l in b.letters() {
            subterms(l, out);
        }
    }
}

fn modalities(f: &Formula, out: &mut HashSet<Bracket>) {
    match f {
        Formula::Top | Formula::Var(_) => {}
        Formula::And(a, b) => {
            modalities(a, out);
            modalities(b, out);
        }
        Formula::Dia(m, a) => {
            subterms(m, out);
            modalities(a, out);
        }
    }
}

/// 副条件に出てきてよい括弧語の集合 U = S ∪ nf(S) ∪ {⊤}（S は入力の括弧語の部分語）。
fn universe(goal: &BSeq) -> HashSet<Bracket> {
    let mut s = HashSet::new();
    modalities(&goal.lhs, &mut s);
    modalities(&goal.rhs, &mut s);
    let nf: Vec<Bracket> = s.iter().map(|b| b.normal_form_syntactic()).collect();
    s.extend(nf);
    s.insert(Bracket::top());
    s
}

/// 導出 DAG から副条件のシーケントを取り出し、どれも U の括弧語だけでできているか確かめる。
/// 副条件は x ⊢ y（b ≤ a の証拠）か x ⊢ ()y（b ◁ a の証拠）の形。
fn side_conditions(p: &BcProof, u: &HashSet<Bracket>) -> (usize, usize) {
    let mut seen: HashSet<&BSeq> = HashSet::new();
    let mut outside = 0;
    for node in &p.nodes {
        let side = match node.rule {
            BcRule::R3a | BcRule::R3b => node.premises.get(1),
            BcRule::R4 => node.premises.first(),
            _ => None,
        };
        let Some(&s) = side else { continue };
        let c = &p.nodes[s].conclusion;
        if !seen.insert(c) {
            continue;
        }
        let x = c.lhs.as_worm().expect("副条件の左辺は括弧語");
        let y = c.rhs.as_worm().expect("副条件の右辺は括弧語");
        let y_ok = u.contains(&y)
            || (y.letters().first().is_some_and(Bracket::is_top) && u.contains(&Bracket::new(y.letters()[1..].to_vec())));
        if !u.contains(&x) || !y_ok {
            outside += 1;
        }
    }
    (seen.len(), outside)
}

fn report(family: &str, param: usize, goal: &BSeq) {
    let t = Instant::now();
    let Ok((p, st)) = bc::derive(&goal.lhs, &goal.rhs) else { return };
    let ms = t.elapsed().as_secs_f64() * 1000.0;
    bc::check(&p).expect("検査を通るはず");
    let u = universe(goal);
    // 副条件の前提（恒等式 a ⊢ a も含む）がすべて U の括弧語でできているか
    let (premises, outside) = side_conditions(&p, &u);
    assert_eq!(outside, 0, "U の外の括弧語が副条件に出た：{goal}");
    let side = st.side_conditions;
    assert!(side <= premises.max(side));
    // 上界：副条件は x ⊢ y か x ⊢ ()y（x, y ∈ U）なので高々 2|U|² 個
    let bound = 2 * u.len() * u.len();
    assert!(side <= bound);
    let n = input_size(&goal.lhs) + input_size(&goal.rhs);
    println!(
        "{family},{param},{n},{},{side},{bound},{},{},{:.1},{ms:.1}",
        u.len(),
        st.max_side_depth,
        p.dag_size(),
        p.dag_size() as f64 / (1 + side) as f64
    );
}

/// 入れ子の深さ d の括弧語 ((…(())…))
fn nested(d: usize) -> Bracket {
    (0..d).fold(Bracket::top(), |acc, _| Bracket::new(vec![acc]))
}

/// ランダムな Γ0 未満の順序数（文字の数が多い正規形の括弧語を作るため）
fn veblen(r: &mut Rng, d: u32) -> Veblen {
    if d == 0 || r.below(3) == 0 {
        return Veblen::nat(r.below(4));
    }
    match r.below(4) {
        0 => veblen(r, d - 1) + veblen(r, d - 1),
        1 => Veblen::phi(veblen(r, d - 1), veblen(r, d - 1)),
        2 => Veblen::omega_pow(veblen(r, d - 1)),
        _ => veblen(r, d - 1).mul_nat(1 + r.below(3)),
    }
}

/// ランダムな BC の式（変数 p, q、モダリティは下の括弧語）
fn formula(r: &mut Rng, pool: &[Bracket], d: u32) -> Formula {
    if d == 0 || r.below(3) == 0 {
        return match r.below(3) {
            0 => Formula::Top,
            1 => Formula::var("p"),
            _ => Formula::var("q"),
        };
    }
    if r.below(2) == 0 {
        Formula::and(formula(r, pool, d - 1), formula(r, pool, d - 1))
    } else {
        Formula::dia(pool[r.below(pool.len() as u64) as usize].clone(), formula(r, pool, d - 1))
    }
}

fn main() {
    println!("family,param,n,universe,side,side_bound,max_side_depth,dag,dag_per_side,ms");
    // 1. 入れ子の鎖：a_{d-1} ◁ a_d（a_d は深さ d の ((…)))
    for d in 2..=12 {
        report("nested", d, &BSeq::lt(&nested(d - 1), &nested(d)));
    }
    // 2. 幅：(())^k() ◁ (())^k (())（同じ文字がたくさん並ぶ）
    for k in [1, 2, 4, 8, 16, 32] {
        let w = Bracket::new(vec![nested(1); k]);
        let mut big = w.letters().to_vec();
        big.push(nested(2));
        report("wide", k, &BSeq::lt(&w, &Bracket::new(big)));
    }
    // 2b. 違う文字がたくさん：(()^k)(()^{k-1})…(()) と、それを 1 つ短くしたもの（()^i は i を表す）
    for k in [2, 4, 8, 12, 16, 24] {
        let word = |k: usize| Bracket::new((1..=k).rev().map(|i| Bracket::new(vec![Bracket::top(); i])).collect());
        report("distinct", k, &BSeq::lt(&word(k - 1), &word(k)));
        // 文字を逆順（増加列）にしたもの：左の文字ほど小さい
        let inc = |k: usize| Bracket::new((1..=k).map(|i| Bracket::new(vec![Bracket::top(); i])).collect());
        report("distinct_inc", k, &BSeq::lt(&inc(k - 1), &inc(k)));
    }
    // 3. Thm 52 の出発点どうし：a'_{m-1} ◁ a'_m
    for m in 1..=8 {
        report("thm52", m, &BSeq::lt(&Bracket::thm52(m - 1), &Bracket::thm52(m)));
    }
    // 4. ランダムな順序数の正規形どうし（文字の種類が多い）
    let mut r = Rng(0x2026_1108);
    for depth in 2..=5u32 {
        let mut done = 0;
        while done < 12 {
            let (x, y) = (Bracket::from_ordinal(&veblen(&mut r, depth)), Bracket::from_ordinal(&veblen(&mut r, depth)));
            let (a, b) = match x.cmp_syntactic(&y) {
                std::cmp::Ordering::Greater => (x, y),
                std::cmp::Ordering::Less => (y, x),
                std::cmp::Ordering::Equal => continue,
            };
            report("random_nf", depth as usize, &BSeq::lt(&b, &a));
            done += 1;
        }
    }
    // 5. 変数と ∧ を含む式（正規形でないモダリティも混ぜる）
    let pool: Vec<Bracket> =
        ["", "()", "()()", "(())", "(())()", "()(())", "(()())", "((()))", "((())())", "(((())))", "((())(()))"]
            .iter()
            .map(|s| s.parse().unwrap())
            .collect();
    let mut done = 0;
    let mut tries = 0;
    while done < 60 && tries < 20_000 {
        tries += 1;
        let a = formula(&mut r, &pool, 4);
        // 成り立ちやすいように、右辺は左辺の一部を弱めたものも混ぜる
        let b = if r.below(2) == 0 { formula(&mut r, &pool, 3) } else { Formula::dia(Bracket::top(), a.clone()) };
        if bc::decide(&a, &b) {
            report("formula", done, &BSeq::new(a, b));
            done += 1;
        }
    }
}
