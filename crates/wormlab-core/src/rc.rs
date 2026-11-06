//! Reflection Calculus (RC) の判定器。
//!
//! # RC（Dashkov; Beklemishev）
//!
//! 強正値式のシーケント A ⊢ B を導く体系：
//! 1. A ⊢ A，A ⊢ ⊤，A ⊢ B かつ B ⊢ C なら A ⊢ C
//! 2. A ∧ B ⊢ A，A ∧ B ⊢ B，A ⊢ B かつ A ⊢ C なら A ⊢ B ∧ C
//! 3. A ⊢ B なら ⟨n⟩A ⊢ ⟨n⟩B，⟨n⟩⟨n⟩A ⊢ ⟨n⟩A
//! 4. ⟨n⟩A ⊢ ⟨m⟩A（n > m）
//! 5. ⟨n⟩A ∧ ⟨m⟩B ⊢ ⟨n⟩(A ∧ ⟨m⟩B)（n > m）
//!
//! RC は強正値式について GLP の保存的な断片になっている。
//!
//! # 判定法（Beklemishev, "Positive provability logic for uniform reflection
//! principles", Def. 5.1 と Thm. 3(ii)）
//!
//! 1. A の構文木をそのまま Kripke モデルにした「標準木」T[A] を作る：
//!    p・⊤ は 1 点、B ∧ C は根を貼り合わせ、⟨n⟩B は新しい根から
//!    T[B] の根へ R_n の辺を張る。
//! 2. T[A] を、次の条件を満たす最小のフレームに閉包する（S = A, B に
//!    現れるモダリティの集合、α, β ∈ S）：
//!    - 推移性：x R_α y R_α z ⇒ x R_α z
//!    - 単調性：R_α ⊆ R_β（β < α）
//!    - 条件 J：x R_α y かつ x R_β z ⇒ y R_β z（α > β）
//!
//!    論文の polytransitivity は単調性＋推移性から従う。
//! 3. A ⊢_RC B ⟺ 閉包したモデルの根で B が真。
//!
//! 閉包は点の数の多項式時間で計算でき、モデル検査も多項式時間なので、
//! 全体が多項式時間の判定になる。偽のときは、そのモデルが反例になる。

use crate::bitset::BitSet;
use crate::spf::{Sequent, Spf};
use crate::worm::Worm;
use std::collections::BTreeSet;
use std::fmt;

/// 閉包済みの有限 Kripke モデル。点 0 が根。
#[derive(Clone, Debug)]
pub struct Model {
    /// 各点で真な変数
    labels: Vec<BTreeSet<String>>,
    /// 署名 S（昇順）
    sig: Vec<u32>,
    /// rel[i][x] = x の R_{sig[i]}-後続の集合
    rel: Vec<Vec<BitSet>>,
    /// 標準木の辺 (親, モダリティ, 子)
    tree_edges: Vec<(usize, u32, usize)>,
}

impl Model {
    /// A の標準木を作り、署名 `sig` について RC 閉包を取る。
    pub fn canonical(a: &Spf, sig: &BTreeSet<u32>) -> Model {
        let mut labels = vec![BTreeSet::new()];
        let mut tree_edges = Vec::new();
        build_tree(a, 0, &mut labels, &mut tree_edges);

        let sig: Vec<u32> = sig.iter().copied().collect();
        let n = labels.len();
        let mut rel = vec![vec![BitSet::new(n); n]; sig.len()];
        for &(x, m, y) in &tree_edges {
            let i = sig.binary_search(&m).expect("A のモダリティは署名に含まれる");
            rel[i][x].insert(y);
        }
        let mut model = Model { labels, sig, rel, tree_edges };
        model.close();
        model
    }

    /// 推移性・単調性・条件 J について、変化がなくなるまで閉包を取る。
    fn close(&mut self) {
        let n = self.labels.len();
        let k = self.sig.len();
        loop {
            let mut changed = false;

            // 単調性：上のモダリティから順に下へ流す（R_{α_{i+1}} ⊆ R_{α_i}）
            for i in (0..k.saturating_sub(1)).rev() {
                for x in 0..n {
                    let upper = self.rel[i + 1][x].clone();
                    changed |= self.rel[i][x].union_with(&upper);
                }
            }

            // 推移性：各 R_α について Warshall 法
            for r in self.rel.iter_mut() {
                for mid in 0..n {
                    let row_mid = r[mid].clone();
                    for row in r.iter_mut() {
                        if row.contains(mid) {
                            changed |= row.union_with(&row_mid);
                        }
                    }
                }
            }

            // 条件 J：x R_α y, x R_β z (α > β) ⇒ y R_β z
            for i in 0..k {
                for j in 0..i {
                    for x in 0..n {
                        let succ_beta = self.rel[j][x].clone();
                        let succ_alpha: Vec<usize> = self.rel[i][x].iter().collect();
                        for y in succ_alpha {
                            changed |= self.rel[j][y].union_with(&succ_beta);
                        }
                    }
                }
            }

            if !changed {
                break;
            }
        }
    }

    pub fn num_points(&self) -> usize {
        self.labels.len()
    }

    pub fn signature(&self) -> &[u32] {
        &self.sig
    }

    /// x R_m y か（m が署名にない場合は false）。
    pub fn related(&self, m: u32, x: usize, y: usize) -> bool {
        match self.sig.binary_search(&m) {
            Ok(i) => self.rel[i][x].contains(y),
            Err(_) => false,
        }
    }

    /// 点 x で真な変数。
    pub fn label(&self, x: usize) -> &BTreeSet<String> {
        &self.labels[x]
    }

    /// 式 B が真になる点の集合。
    pub fn truth_set(&self, b: &Spf) -> BitSet {
        let n = self.num_points();
        match b {
            Spf::Top => BitSet::full(n),
            Spf::Var(p) => {
                let mut s = BitSet::new(n);
                for x in 0..n {
                    if self.labels[x].contains(p) {
                        s.insert(x);
                    }
                }
                s
            }
            Spf::And(c, d) => {
                let mut s = self.truth_set(c);
                s.intersect_with(&self.truth_set(d));
                s
            }
            Spf::Dia(m, c) => {
                let mut s = BitSet::new(n);
                if let Ok(i) = self.sig.binary_search(m) {
                    let inner = self.truth_set(c);
                    for x in 0..n {
                        if self.rel[i][x].intersects(&inner) {
                            s.insert(x);
                        }
                    }
                }
                s
            }
        }
    }

    /// 点 x で B が真か。
    pub fn satisfies(&self, x: usize, b: &Spf) -> bool {
        self.truth_set(b).contains(x)
    }
}

/// 標準木 T[A] を `node` を根として作る。
fn build_tree(
    a: &Spf,
    node: usize,
    labels: &mut Vec<BTreeSet<String>>,
    edges: &mut Vec<(usize, u32, usize)>,
) {
    match a {
        Spf::Top => {}
        Spf::Var(p) => {
            labels[node].insert(p.clone());
        }
        Spf::And(b, c) => {
            build_tree(b, node, labels, edges);
            build_tree(c, node, labels, edges);
        }
        Spf::Dia(m, b) => {
            let child = labels.len();
            labels.push(BTreeSet::new());
            edges.push((node, *m, child));
            build_tree(b, child, labels, edges);
        }
    }
}

impl fmt::Display for Model {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "点（0 が根）:")?;
        for (x, lab) in self.labels.iter().enumerate() {
            let vars: Vec<&str> = lab.iter().map(String::as_str).collect();
            writeln!(f, "  {x}: {{{}}}", vars.join(", "))?;
        }
        writeln!(f, "標準木の辺:")?;
        for (x, m, y) in &self.tree_edges {
            writeln!(f, "  {x} →{m} {y}")?;
        }
        writeln!(f, "閉包後の関係:")?;
        for (i, m) in self.sig.iter().enumerate() {
            let pairs: Vec<String> = (0..self.num_points())
                .flat_map(|x| self.rel[i][x].iter().map(move |y| format!("{x}→{y}")))
                .collect();
            writeln!(f, "  R_{m}: {}", pairs.join(" "))?;
        }
        Ok(())
    }
}

/// 判定結果。`model` は A の閉包モデルで、`holds == false` のときは反例。
#[derive(Clone, Debug)]
pub struct Decision {
    pub sequent: Sequent,
    pub holds: bool,
    pub model: Model,
}

/// A ⊢ B を判定する。
pub fn decide(lhs: &Spf, rhs: &Spf) -> Decision {
    let mut sig = lhs.modalities();
    sig.extend(rhs.modalities());
    let model = Model::canonical(lhs, &sig);
    let holds = model.satisfies(0, rhs);
    Decision { sequent: Sequent { lhs: lhs.clone(), rhs: rhs.clone() }, holds, model }
}

/// RC ⊢ A ⊢ B か。
pub fn entails(lhs: &Spf, rhs: &Spf) -> bool {
    decide(lhs, rhs).holds
}

/// A ≡ B（両方向に導出可能）か。
pub fn equivalent(a: &Spf, b: &Spf) -> bool {
    entails(a, b) && entails(b, a)
}

/// 一般の worm に対する A <_n B（GLP ⊢ B → ⟨n⟩A）を RC で判定する。
pub fn worm_lt(n: u32, a: &Worm, b: &Worm) -> bool {
    entails(&Spf::from(b), &Spf::dia(n, Spf::from(a)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn holds(s: &str) -> bool {
        let seq: Sequent = s.parse().unwrap();
        entails(&seq.lhs, &seq.rhs)
    }

    #[test]
    fn axioms_hold() {
        assert!(holds("p ⊢ p"));
        assert!(holds("p ⊢ ⊤"));
        assert!(holds("p ∧ q ⊢ q ∧ p"));
        assert!(holds("<0><0>p ⊢ <0>p"));
        assert!(holds("<2>p ⊢ <0>p"));
        assert!(holds("<1>p ∧ <0>q ⊢ <1>(p ∧ <0>q)"));
        assert!(holds("<2><1>p ∧ <0>q ⊢ <2>(<1>p ∧ <0>q)"));
        assert!(holds("<2>p ⊢ <0><1>p"));
    }

    #[test]
    fn non_theorems_fail() {
        assert!(!holds("p ⊢ <0>p"));
        assert!(!holds("<0>p ⊢ p"));
        assert!(!holds("<0>p ⊢ <1>p"));
        assert!(!holds("<0>p ⊢ <0><0>p"));
        assert!(!holds("<0>p ∧ <0>q ⊢ <0>(p ∧ q)"));
        assert!(!holds("<1>p ∧ <1>q ⊢ <1>(p ∧ <1>q)")); // 同じ番号には J が効かない
        assert!(!holds("<0>p ∧ <1>q ⊢ <0>(p ∧ <1>q)")); // 向きが逆
    }

    #[test]
    fn subtle_theorem() {
        // ⟨1⟩p ⊢ ⟨0⟩p なので ⟨1⟩p ⊢ ⟨1⟩p ∧ ⟨0⟩p ⊢ ⟨1⟩(p ∧ ⟨0⟩p)
        assert!(holds("<1>p ⊢ <1>(p ∧ <0>p)"));
    }

    #[test]
    fn general_worm_order() {
        let w = |s: &str| s.parse::<Worm>().unwrap();
        // h_n だけを比べる素朴な方法では誤る例
        assert!(!worm_lt(1, &w("0 2"), &w("1")));
        assert!(worm_lt(1, &w("0"), &w("1")));
        assert!(worm_lt(0, &w("1 1"), &w("2")));
    }
}
