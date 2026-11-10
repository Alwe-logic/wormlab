//! ψ 表記（Worms and spiders, Def 6.19）の性質ベースのテスト。
//!
//! - 比較が全順序（反対称・推移）で、加法・φ と整合する
//! - ψ の定義そのもの：可算な正規形 t について t ∈ C(ξ) ⟺ t < ψ(ξ)（C(ξ) ∩ Ω = ψ(ξ)）。
//!   左辺は形だけの判定（K(t) < ξ）、右辺は比較なので、崩し（ξ ∉ C(ξ) のとき）と比較の
//!   両方を突き合わせることになる
//! - 崩しの最小性：ψ(ξ) = ψ(z) となる z は ξ 以上で z ∈ C(z) となる最小の数
//! - ψ は単調、ψ(ξ) は強臨界数
//! - 文字に Ω・ψ を含む worm でも、o（超指数関数）・head/body・RC の 3 つの比較が一致し、
//!   逆写像が o の逆になる（Ω・ψ と φ の計算規則の独立な検証）

use proptest::prelude::*;
use std::cmp::Ordering;
use wormlab_core::rc::equivalent;
use wormlab_core::{Spf, Veblen, Worm, headbody};

/// Ω・ψ を含むランダムな数（入れ子 3 段まで）
fn term() -> impl Strategy<Value = Veblen> {
    let leaf = prop_oneof![
        (0u64..3).prop_map(Veblen::nat),
        Just(Veblen::omega()),
        Just(Veblen::big_omega()),
        Just(Veblen::psi(Veblen::zero())),
    ];
    leaf.prop_recursive(3, 24, 3, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| a + b),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Veblen::phi(a, b)),
            inner.clone().prop_map(Veblen::omega_pow),
            inner.clone().prop_map(Veblen::psi),
            (inner, 1u64..3).prop_map(|(a, n)| a.mul_nat(n)),
        ]
    })
}

/// 崩しが起きやすい数：非可算な u に、引数の大きい ψ を混ぜる
fn tricky() -> impl Strategy<Value = Veblen> {
    (term(), term(), term(), 0usize..10).prop_map(|(u, v, w, k)| {
        let big = Veblen::big_omega();
        let u = big.clone() + u;
        let pv = Veblen::psi(u.clone() + v.clone());
        let pw = Veblen::psi(w.clone());
        match k {
            0 => u + pv,
            1 => u + pv.mul_nat(2) + pw,
            2 => Veblen::phi(pv, u),
            3 => Veblen::omega_pow(u + pv),
            4 => Veblen::phi(u, pv + w),
            5 => Veblen::phi(Veblen::phi(u.clone(), pv), pw + big),
            // 先頭の部分に ψ を残したまま崩れる形：引数 z を項全体より大きくする
            6 => {
                let z = Veblen::phi(pw.clone() + Veblen::one(), big.clone() + Veblen::one()) + v;
                Veblen::phi(pw, big + Veblen::psi(z))
            }
            7 => {
                let head = Veblen::omega_pow(big + pw);
                let z = Veblen::omega_pow(head.clone() + Veblen::one()) + v;
                head + Veblen::psi(z)
            }
            8 => {
                let head = Veblen::phi(Veblen::phi(Veblen::one(), u.clone()), pw);
                let z = Veblen::phi(Veblen::phi(Veblen::one(), u) + Veblen::one(), Veblen::zero()) + v;
                head.clone() + Veblen::psi(z.clone()) + Veblen::psi(z + head)
            }
            _ => {
                let z = Veblen::phi(Veblen::one(), u.clone()) + v;
                Veblen::phi(pw, u + Veblen::psi(z))
            }
        }
    })
}

/// 引数の候補：ランダムな数と崩しが起きやすい数
fn arg() -> impl Strategy<Value = Veblen> {
    prop_oneof![term(), tricky()]
}

/// 文字の候補（Γ0・Ω をまたぐ）
fn iletter() -> impl Strategy<Value = Veblen> {
    let pool: Vec<Veblen> = [
        "0", "1", "ω", "ε_0", "ψ(0)", "ψ(0) + 1", "ψ(1)", "ψ(Ω)", "ψ(Ω + 1)", "ψ(ε_(Ω + 1))", "Ω", "Ω + 1",
        "Ω + ψ(0)", "Ω·2", "ε_(Ω + 1)", "φ(Ω, 1)",
    ]
    .iter()
    .map(|s| s.parse().unwrap())
    .collect();
    prop::sample::select(pool)
}

fn iworm() -> impl Strategy<Value = Worm<Veblen>> {
    prop::collection::vec(iletter(), 0..6).prop_map(Worm::new)
}

/// 可算な数（ψ と φ と加法だけで作る。Ω は ψ の中にだけ現れる）
fn countable() -> impl Strategy<Value = Veblen> {
    let leaf = prop_oneof![(0u64..3).prop_map(Veblen::nat), Just(Veblen::omega())];
    (leaf, term()).prop_flat_map(|(l, t)| {
        let psi = Veblen::psi(t);
        prop_oneof![
            Just(psi.clone()),
            Just(psi.clone() + l.clone()),
            Just(Veblen::phi(l.clone(), psi.clone() + Veblen::one())),
            Just(Veblen::phi(psi.clone(), l.clone())),
            Just(l),
        ]
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    #[test]
    fn total_order(a in arg(), b in arg(), c in arg()) {
        prop_assert_eq!(a.cmp(&b), b.cmp(&a).reverse());
        prop_assert_eq!(a.cmp(&b) == Ordering::Equal, a == b);
        if a <= b && b <= c {
            prop_assert!(a <= c);
        }
    }

    #[test]
    fn arithmetic_is_monotone(a in term(), b in term(), c in term()) {
        prop_assert!(a.clone() + b.clone() >= b);
        prop_assert!(a.clone() + b.clone() >= a);
        if b < c {
            prop_assert!(a.clone() + b.clone() < a.clone() + c.clone());
        }
        // φ は 2 つの引数以上で、2 つ目について狭義単調
        let p = Veblen::phi(a.clone(), b.clone());
        prop_assert!(p >= a && p >= b);
        if b < c {
            prop_assert!(p < Veblen::phi(a.clone(), c.clone()));
        }
        // 左引き算
        let s = a.clone() + b.clone();
        prop_assert_eq!(a.clone() + a.sub_left(&s).unwrap(), s);
    }

    /// C(ξ) ∩ Ω = ψ(ξ)：可算な t について、形の判定 K(t) < ξ と比較 t < ψ(ξ) が一致する
    #[test]
    fn psi_is_least_outside_c(x in arg(), t in countable()) {
        prop_assume!(t.is_countable());
        let p = Veblen::psi(x.clone());
        prop_assert_eq!(t.in_c(&x), t < p, "t = {}, ξ = {}, ψ(ξ) = {}", t, x, p);
    }

    /// ψ(y) < ψ(ξ) ⟺ ψ(y) ∈ C(ξ)（ψ(y) の正規形の引数が ξ 未満）
    #[test]
    fn psi_values_vs_c(x in arg(), y in arg()) {
        let (px, py) = (Veblen::psi(x.clone()), Veblen::psi(y.clone()));
        prop_assert_eq!(py.in_c(&x), py < px, "ψ(y) = {}, ξ = {}, ψ(ξ) = {}", py, x, px);
    }

    /// 崩しの最小性：ψ(ξ) = ψ(z0) で z0 ≥ ξ、z0 ∈ C(z0)、ξ ≤ z < z0 の z は z ∈ C(z) にならない
    #[test]
    fn collapse_is_minimal(x in arg(), z in arg()) {
        let p = Veblen::psi(x.clone());
        let z0 = p.as_psi().expect("ψ の値は ψ(z0) の形").clone();
        prop_assert!(z0 >= x);
        prop_assert!(z0.in_c(&z0));
        if x.in_c(&x) {
            prop_assert_eq!(&z0, &x);
        }
        if x <= z && z.in_c(&z) {
            prop_assert!(z >= z0, "ξ = {}, z0 = {}, z = {} が先に C(z) ∋ z", x, z0, z);
        }
    }

    #[test]
    fn psi_monotone_and_critical(x in arg(), y in arg(), a in countable()) {
        let (px, py) = (Veblen::psi(x.clone()), Veblen::psi(y.clone()));
        if x <= y {
            prop_assert!(px <= py);
        }
        // 正規形の引数どうしなら狭義単調
        if x < y && x.in_c(&x) && y.in_c(&y) {
            prop_assert!(px < py);
        }
        prop_assert!(px.is_countable());
        prop_assert_eq!(Veblen::phi(px.clone(), Veblen::zero()), px.clone());
        if a < px {
            prop_assert_eq!(Veblen::phi(a.clone(), px.clone()), px.clone());
            prop_assert!(Veblen::phi(a.clone(), a.clone() + Veblen::one()) < px);
        }
    }

    /// 文字に Ω・ψ を含む worm：o・head/body・RC の 3 つの比較が一致する
    #[test]
    fn worm_three_methods(a in iworm(), b in iworm()) {
        let by_o = a.cmp0(&b) == Ordering::Less;
        prop_assert_eq!(headbody::lt(Veblen::zero(), &a, &b), Some(by_o),
            "head/body: {} vs {}（o = {} vs {}）", a, b, a.ordinal(), b.ordinal());
        prop_assert_eq!(a.lt_n(&b, Veblen::zero()), by_o, "RC: {} vs {}", a, b);
        prop_assert_eq!(a.equiv(&b), equivalent(&Spf::from(&a), &Spf::from(&b)));
    }

    /// 逆写像：o(inv(α)) = α（α は Ω・ψ を含んでよい）
    #[test]
    fn worm_inverse(x in arg()) {
        let w = Worm::from_veblen(&x);
        prop_assert_eq!(w.ordinal(), x.clone(), "{} ↦ {}", x, w);
    }

    #[test]
    fn display_roundtrip(x in arg()) {
        let s = x.to_string();
        prop_assert_eq!(s.parse::<Veblen>().unwrap(), x);
    }
}

#[test]
#[ignore]
fn coverage_stats() {
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;
    let mut runner = TestRunner::deterministic();
    let (mut nonnormal, mut chain, mut inc, mut outc, mut n) = (0, 0, 0, 0, 0);
    let mut longest = String::new();
    for _ in 0..5000 {
        let x = arg().new_tree(&mut runner).unwrap().current();
        let t = countable().new_tree(&mut runner).unwrap().current();
        n += 1;
        if !x.in_c(&x) {
            nonnormal += 1;
            // ceil を何回したか：ψ(x) の引数と x が違えば少なくとも 1 回
            let z0 = Veblen::psi(x.clone()).as_psi().unwrap().clone();
            if z0 != x && z0.max_k().is_some() {
                chain += 1;
                if longest.len() < 80 { longest = format!("{x}  ↦  {z0}"); }
            }
        }
        if t.is_countable() {
            if t.in_c(&x) { inc += 1 } else { outc += 1 }
        }
    }
    println!("n = {n}, x ∉ C(x): {nonnormal}, z0 が ψ を含む: {chain}, t ∈ C(x): {inc}, t ∉ C(x): {outc}");
    println!("例: {longest}");
}

/// 小さな項を全部作り、崩しの最小性と C(ξ) ∩ Ω = ψ(ξ) を総当たりで確かめる。
/// 項は {0, 1, ω, Ω, ψ(0)} から +・φ・ψ を 2 回まで使って作る（重複は除く）。
fn small_terms() -> Vec<Veblen> {
    use std::collections::BTreeSet;
    let mut all: BTreeSet<Veblen> =
        [Veblen::zero(), Veblen::one(), Veblen::omega(), Veblen::big_omega(), Veblen::psi(Veblen::zero())].into();
    for _ in 0..2 {
        let cur: Vec<Veblen> = all.iter().cloned().collect();
        for a in &cur {
            all.insert(Veblen::psi(a.clone()));
            for b in &cur {
                all.insert(a.clone() + b.clone());
                all.insert(Veblen::phi(a.clone(), b.clone()));
            }
        }
    }
    all.into_iter().collect()
}

#[test]
fn exhaustive_small_terms() {
    let pool = small_terms();
    assert!(pool.len() > 1000, "{}", pool.len());
    let normal: Vec<&Veblen> = pool.iter().filter(|z| z.in_c(z)).collect();
    let countable: Vec<&Veblen> = pool.iter().filter(|t| t.is_countable()).collect();
    let nonnormal = pool.iter().filter(|x| !x.in_c(x)).count();
    println!("項 {} 個（C(z) ∋ z は {}、可算 {}、崩れる {}）", pool.len(), normal.len(), countable.len(), nonnormal);
    for x in &pool {
        let p = Veblen::psi(x.clone());
        let z0 = p.as_psi().unwrap();
        // ξ ≤ z < z0 で z ∈ C(z) となる z はない
        if let Some(z) = normal.iter().find(|z| **z >= x && **z < z0) {
            panic!("ξ = {x}：z0 = {z0} より小さい {z} が C(z) ∋ z");
        }
        // C(ξ) ∩ Ω = ψ(ξ)
        for t in &countable {
            assert_eq!(t.in_c(x), **t < p, "t = {t}, ξ = {x}");
        }
    }
}
