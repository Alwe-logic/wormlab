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
//! # 判定法 1：閉包モデル（Beklemishev, "Positive provability logic for uniform
//! reflection principles", Def. 5.1 と Thm. 3(ii)）。[`decide`] が使う。
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
//! ただし関係（点の組）を閉じるので、点が N 個・モダリティが k 種なら 1 周で
//! O(k²N³) のビット演算がかかる。
//!
//! # 判定法 2：局所規則（algorithms.md §1b の補題 B）。[`entails`] が使う。
//!
//! 関係は作らず、「標準木の点 x で B の部分式 β が（閉包モデルで）真」という事実
//! (x, β) だけを、次の規則の最小不動点として求める：
//! - 変数・⊤：x のラベルにあれば真。∧：両方が真なら真。
//! - 木の辺 x →k y（k ≥ m）：y で β か ⟨m⟩β が真なら、x で ⟨m⟩β が真（Nec・単調性・4）
//! - 押し下げ：木の辺 t →k x（k > m）：t で ⟨m⟩β が真なら、x でも真（t での J）
//!
//! ⟨m⟩β を結論とする規則の前提は ⟨m⟩β と β だけなので、目標は Sub(B) だけで閉じている。
//! 規則（Horn 節）は O(N·|Sub(B)|) 個なので、作業リストで回すと O(|A|·|B|) 時間。
//! テストで閉包モデルの判定と突き合わせている。
use crate::bitset::BitSet;
use crate::letter::{Letter, Ranks};
use crate::spf::{Sequent, Spf};
use crate::worm::Worm;
use std::collections::{BTreeSet, HashMap, VecDeque};
use std::fmt;

/// 閉包済みの有限 Kripke モデル。点 0 が根。
///
/// モダリティの番号は自然数でも順序数でもよい（大小比較しか使わない）。
/// 署名 S は有限集合なので、関係は S の要素ごとに 1 本ずつ持つ。
#[derive(Clone, Debug)]
pub struct Model<L = u32> {
    /// 各点で真な変数
    labels: Vec<BTreeSet<String>>,
    /// 署名 S（昇順）
    sig: Vec<L>,
    /// rel[i][x] = x の R_{sig[i]}-後続の集合
    rel: Vec<Vec<BitSet>>,
    /// 標準木の辺 (親, モダリティ, 子)
    tree_edges: Vec<(usize, L, usize)>,
}

impl<L: Letter> Model<L> {
    /// A の標準木を作り、署名 `sig` について RC 閉包を取る。
    pub fn canonical(a: &Spf<L>, sig: &BTreeSet<L>) -> Model<L> {
        let mut labels = vec![BTreeSet::new()];
        let mut tree_edges = Vec::new();
        build_tree(a, 0, &mut labels, &mut tree_edges);

        let sig: Vec<L> = sig.iter().cloned().collect();
        let n = labels.len();
        let mut rel = vec![vec![BitSet::new(n); n]; sig.len()];
        for (x, m, y) in &tree_edges {
            let i = sig.binary_search(m).expect("A のモダリティは署名に含まれる");
            rel[i][*x].insert(*y);
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

    pub fn signature(&self) -> &[L] {
        &self.sig
    }

    /// 標準木の辺 (親, モダリティ, 子)。閉包で足した辺は含まない（描画の骨組みに使う）。
    pub fn tree_edges(&self) -> &[(usize, L, usize)] {
        &self.tree_edges
    }

    /// x R_m y か（m が署名にない場合は false）。
    pub fn related(&self, m: &L, x: usize, y: usize) -> bool {
        match self.sig.binary_search(m) {
            Ok(i) => self.rel[i][x].contains(y),
            Err(_) => false,
        }
    }

    /// 点 x で真な変数。
    pub fn label(&self, x: usize) -> &BTreeSet<String> {
        &self.labels[x]
    }

    /// 式 B が真になる点の集合。
    pub fn truth_set(&self, b: &Spf<L>) -> BitSet {
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
    pub fn satisfies(&self, x: usize, b: &Spf<L>) -> bool {
        self.truth_set(b).contains(x)
    }
}

/// 標準木 T[A] を `node` を根として作る。
fn build_tree<L: Letter>(
    a: &Spf<L>,
    node: usize,
    labels: &mut Vec<BTreeSet<String>>,
    edges: &mut Vec<(usize, L, usize)>,
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
            edges.push((node, m.clone(), child));
            build_tree(b, child, labels, edges);
        }
    }
}

impl<L: Letter> fmt::Display for Model<L> {
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
pub struct Decision<L = u32> {
    pub sequent: Sequent<L>,
    pub holds: bool,
    pub model: Model<L>,
}

/// A ⊢ B を閉包モデルで判定する（判定法 1）。反例のモデルが要るとき用。
/// 真偽だけなら [`entails`] の方がずっと速い。
pub fn decide<L: Letter>(lhs: &Spf<L>, rhs: &Spf<L>) -> Decision<L> {
    let mut sig = lhs.modalities();
    sig.extend(rhs.modalities());
    let model = Model::canonical(lhs, &sig);
    let holds = model.satisfies(0, rhs);
    debug_assert_eq!(holds, entails(lhs, rhs), "閉包と局所規則の判定が食い違う: {lhs} ⊢ {rhs}");
    Decision { sequent: Sequent { lhs: lhs.clone(), rhs: rhs.clone() }, holds, model }
}

/// RC ⊢ A ⊢ B か（判定法 2、O(|A|·|B|)）。
///
/// 文字が u32 でなければ、先に順位（u32）に直してから判定する（大小しか使わないので）。
pub fn entails<L: Letter>(lhs: &Spf<L>, rhs: &Spf<L>) -> bool {
    if Ranks::<L>::is_u32() {
        let (t, d) = (ATree::new(lhs), SubDag::new(rhs));
        return saturate(&t, &d, false).holds(0, d.root);
    }
    let r = Ranks::new(lhs.modalities().into_iter().chain(rhs.modalities()));
    entails(&ranked(lhs, &r), &ranked(rhs, &r))
}

/// 式のモダリティを順位に直す。
pub(crate) fn ranked<L: Letter>(a: &Spf<L>, r: &Ranks<L>) -> Spf<u32> {
    match a {
        Spf::Top => Spf::Top,
        Spf::Var(p) => Spf::Var(p.clone()),
        Spf::And(x, y) => Spf::and(ranked(x, r), ranked(y, r)),
        Spf::Dia(m, x) => Spf::dia(r.of(m), ranked(x, r)),
    }
}

/// A ≡ B（両方向に導出可能）か。
pub fn equivalent<L: Letter>(a: &Spf<L>, b: &Spf<L>) -> bool {
    entails(a, b) && entails(b, a)
}

/// 一般の worm に対する A <_n B（GLP ⊢ B → ⟨n⟩A）を RC で判定する。
pub fn worm_lt<L: Letter>(n: L, a: &Worm<L>, b: &Worm<L>) -> bool {
    entails(&Spf::from(b), &Spf::dia(n, Spf::from(a)))
}

// ----------------------------------------------------------------------
// 判定法 2：局所規則の最小不動点（rcproof の導出もこれを使う）
// ----------------------------------------------------------------------

/// A の構文木。点の番号は [`Model::canonical`] と同じ（根 0、⟨k⟩ を見つけた順）。
pub(crate) struct ATree<L> {
    /// 各点で真な変数
    pub(crate) vars: Vec<Vec<String>>,
    /// 子への辺 (ラベル, 子)
    pub(crate) kids: Vec<Vec<(L, usize)>>,
    /// 親への辺 (親, ラベル)
    pub(crate) parent: Vec<Option<(usize, L)>>,
}

impl<L: Letter> ATree<L> {
    pub(crate) fn new(a: &Spf<L>) -> ATree<L> {
        let mut t = ATree { vars: vec![vec![]], kids: vec![vec![]], parent: vec![None] };
        t.build(a, 0);
        t
    }

    fn build(&mut self, a: &Spf<L>, x: usize) {
        match a {
            Spf::Top => {}
            Spf::Var(p) => self.vars[x].push(p.clone()),
            Spf::And(l, r) => {
                self.build(l, x);
                self.build(r, x);
            }
            Spf::Dia(k, b) => {
                let y = self.vars.len();
                self.vars.push(vec![]);
                self.kids.push(vec![]);
                self.parent.push(Some((x, k.clone())));
                self.kids[x].push((k.clone(), y));
                self.build(b, y);
            }
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.vars.len()
    }
}

/// B の部分式の形（子は部分式の番号）。
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum SubNode<L> {
    Top,
    Var(String),
    And(usize, usize),
    Dia(L, usize),
}

/// B の部分式の DAG。同じ部分式は 1 つにまとめ、子を親より先に並べる。
pub(crate) struct SubDag<L> {
    pub(crate) node: Vec<SubNode<L>>,
    /// 各部分式そのもの
    pub(crate) form: Vec<Spf<L>>,
    /// B 自身の番号
    pub(crate) root: usize,
}

impl<L: Letter> SubDag<L> {
    pub(crate) fn new(b: &Spf<L>) -> SubDag<L> {
        let mut d = SubDag { node: vec![], form: vec![], root: 0 };
        let mut index = HashMap::new();
        d.root = d.intern(b, &mut index);
        d
    }

    fn intern(&mut self, b: &Spf<L>, index: &mut HashMap<SubNode<L>, usize>) -> usize {
        let n = match b {
            Spf::Top => SubNode::Top,
            Spf::Var(p) => SubNode::Var(p.clone()),
            Spf::And(x, y) => SubNode::And(self.intern(x, index), self.intern(y, index)),
            Spf::Dia(m, x) => SubNode::Dia(m.clone(), self.intern(x, index)),
        };
        *index.entry(n).or_insert_with_key(|n| {
            self.node.push(n.clone());
            self.form.push(b.clone());
            self.node.len() - 1
        })
    }

    pub(crate) fn len(&self) -> usize {
        self.node.len()
    }
}

/// 事実 (x, i)「点 x で部分式 i が真」をどの規則で得たか。
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Why {
    /// 変数・⊤
    Base,
    /// ∧ の両方が真
    And,
    /// 木の辺 x → child。`via_dia` なら child で ⟨m⟩β、そうでなければ child で β から。
    Edge { child: usize, via_dia: bool },
    /// 木の辺 parent → x での押し下げ
    Push { parent: usize },
}

/// 局所規則の最小不動点。
pub(crate) struct Facts {
    s: usize,
    on: Vec<bool>,
    /// `record` のときだけ：各事実の理由（x·s + i で引く）と、得た順
    pub(crate) why: Vec<Option<Why>>,
    pub(crate) order: Vec<(usize, usize)>,
}

impl Facts {
    pub(crate) fn holds(&self, x: usize, i: usize) -> bool {
        self.on[x * self.s + i]
    }

    pub(crate) fn why(&self, x: usize, i: usize) -> Why {
        self.why[x * self.s + i].expect("record して得た事実")
    }
}

/// 局所規則の最小不動点を作業リスト（先着順）で求める。O(|A|·|B|)。
/// `record` なら各事実の理由と得た順も残す（得た順では、前提は必ず結論より前）。
pub(crate) fn saturate<L: Letter>(t: &ATree<L>, d: &SubDag<L>, record: bool) -> Facts {
    let (n, s) = (t.len(), d.len());
    // 部分式 i が真になったときに見直す相手
    let mut and_users: Vec<Vec<(usize, usize)>> = vec![vec![]; s]; // (i ∧ j の番号, j)
    let mut dia_users: Vec<Vec<usize>> = vec![vec![]; s]; // ⟨m⟩i の番号
    let mut by_var: HashMap<&str, usize> = HashMap::new();
    let mut top = None;
    for (u, node) in d.node.iter().enumerate() {
        match node {
            SubNode::Top => top = Some(u),
            SubNode::Var(p) => {
                by_var.insert(p.as_str(), u);
            }
            SubNode::And(i, j) => {
                and_users[*i].push((u, *j));
                if i != j {
                    and_users[*j].push((u, *i));
                }
            }
            SubNode::Dia(_, i) => dia_users[*i].push(u),
        }
    }
    let modality = |u: usize| match &d.node[u] {
        SubNode::Dia(m, _) => Some(m),
        _ => None,
    };

    let mut f = Facts { s, on: vec![false; n * s], why: vec![], order: vec![] };
    if record {
        f.why = vec![None; n * s];
    }
    let mut work = VecDeque::new();
    let add = |f: &mut Facts, work: &mut VecDeque<(usize, usize)>, x: usize, u: usize, w: Why| {
        if !f.on[x * s + u] {
            f.on[x * s + u] = true;
            work.push_back((x, u));
            if record {
                f.why[x * s + u] = Some(w);
                f.order.push((x, u));
            }
        }
    };
    for x in 0..n {
        if let Some(u) = top {
            add(&mut f, &mut work, x, u, Why::Base);
        }
        for p in &t.vars[x] {
            if let Some(&u) = by_var.get(p.as_str()) {
                add(&mut f, &mut work, x, u, Why::Base);
            }
        }
    }
    while let Some((x, i)) = work.pop_front() {
        for &(u, j) in &and_users[i] {
            if f.on[x * s + j] {
                add(&mut f, &mut work, x, u, Why::And);
            }
        }
        if let Some((p, k)) = &t.parent[x] {
            // 木の辺 p →k x：x で β ⇒ p で ⟨m⟩β（k ≥ m）
            for &u in &dia_users[i] {
                if modality(u).is_some_and(|m| k >= m) {
                    add(&mut f, &mut work, *p, u, Why::Edge { child: x, via_dia: false });
                }
            }
            // x で ⟨m⟩β ⇒ p で ⟨m⟩β（k ≥ m）
            if modality(i).is_some_and(|m| k >= m) {
                add(&mut f, &mut work, *p, i, Why::Edge { child: x, via_dia: true });
            }
        }
        // 押し下げ：x で ⟨m⟩β ⇒ 子 y で ⟨m⟩β（x →k y、k > m）
        if let Some(m) = modality(i) {
            for (k, y) in &t.kids[x] {
                if k > m {
                    add(&mut f, &mut work, *y, i, Why::Push { parent: x });
                }
            }
        }
    }
    f
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
    fn push_down_twice() {
        // 根の ⟨0⟩p を J で 2 段押し下げる
        assert!(holds("<2><1>⊤ ∧ <0>p ⊢ <2><1><0>p"));
        // ⟨2⟩⟨0⟩p ⊢ ⟨0⟩⟨0⟩p を根に作ってから押し下げる
        assert!(holds("<2><0>⊤ ∧ <0>p ⊢ <2><0><0>p"));
        // 同じ番号には J が効かない
        assert!(!holds("<1><1>⊤ ∧ <1>p ⊢ <1><1><1>p"));
    }

    #[test]
    fn closure_and_local_rules_agree() {
        for s in [
            "p ⊢ p", "<1>p ∧ <0>q ⊢ <1>(p ∧ <0>q)", "<2>p ⊢ <0><1>p", "<1>p ⊢ <1>(p ∧ <0>p)",
            "p ⊢ <0>p", "<0>p ⊢ <0><0>p", "<1>p ∧ <1>q ⊢ <1>(p ∧ <1>q)", "<0>p ∧ <1>q ⊢ <0>(p ∧ <1>q)",
            "<2><1>⊤ ∧ <0>p ⊢ <2><1><0>p", "<2>(p ∧ <1>q) ∧ <0>r ⊢ <0>(<1>(p ∧ <0>r) ∧ <0>q)",
        ] {
            let seq: Sequent = s.parse().unwrap();
            assert_eq!(decide(&seq.lhs, &seq.rhs).holds, entails(&seq.lhs, &seq.rhs), "{s}");
        }
    }

    #[test]
    fn subformulas_are_shared() {
        let b: Spf = "<0>p ∧ (<0>p ∧ q)".parse().unwrap();
        let d = SubDag::new(&b);
        // p, ⟨0⟩p, q, ⟨0⟩p ∧ q, 全体
        assert_eq!(d.len(), 5);
        assert_eq!(d.form[d.root], b);
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
