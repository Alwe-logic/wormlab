//! 証明の共通形式：証明は DAG（有向非巡回グラフ）として持つ。
//!
//! - 各ノードは「規則・前提ノードの番号・結論」からなる。
//! - 前提は必ず自分より前のノードを指す（だから配列の順に検査すれば十分）。
//! - 同じ部分証明は 1 回だけ作って何度も参照できる（DAG にする理由）。
//!
//! 体系ごとの違いは [`Calculus`] trait の `check_step`（1 ステップの検査）
//! だけに閉じ込める。検査器はこの小さな関数と [`check`] だけで、
//! 証明を「探す」側のコードがどれだけ複雑でも、検査が通れば正しい
//! （de Bruijn 基準）。
//!
//! 【Rust メモ】trait は「この型はこういう操作を持つ」という約束（インター
//! フェース）。`type Judgment;` のような「関連型」を持たせると、体系ごとに
//! 判断（シーケントなど）の型を自由に選べる。

use serde::Serialize;
use std::collections::HashMap;
use std::fmt;
use std::hash::{BuildHasherDefault, Hash, Hasher};

/// 速いハッシュ関数（rustc の FxHash と同じ作り）。証明の判断（worm の組）を
/// キーにする表で使う。標準の SipHash は安全だが遅く、証明器の時間の半分近くを
/// 占めていた。ここでは悪意ある入力を気にする必要がないので、これで十分。
#[derive(Default, Clone, Copy)]
pub struct FxHasher {
    hash: u64,
}

impl FxHasher {
    #[inline]
    fn add(&mut self, w: u64) {
        self.hash = (self.hash.rotate_left(5) ^ w).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for c in &mut chunks {
            self.add(u64::from_le_bytes(c.try_into().unwrap()));
        }
        let rest = chunks.remainder();
        if !rest.is_empty() {
            let mut buf = [0u8; 8];
            buf[..rest.len()].copy_from_slice(rest);
            self.add(u64::from_le_bytes(buf));
        }
    }
    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.add(i as u64)
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.add(i as u64)
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add(i)
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64)
    }
    fn finish(&self) -> u64 {
        self.hash
    }
}

/// [`FxHasher`] を使う `HashMap` の型引数。`HashMap<K, V, FxBuild>` のように使う。
pub type FxBuild = BuildHasherDefault<FxHasher>;

/// 証明体系。
pub trait Calculus {
    /// 判断（例：シーケント A ⊢ B）
    type Judgment: Clone + Eq + Hash + fmt::Display + Serialize;
    /// 規則の名前（例：A1, Cut, …）
    type Rule: Clone + Eq + Hash + fmt::Display + Serialize;

    /// 前提 `premises` から規則 `rule` で `conclusion` が出るかを検査する。
    fn check_step(
        rule: &Self::Rule,
        premises: &[&Self::Judgment],
        conclusion: &Self::Judgment,
    ) -> Result<(), String>;
}

/// 証明 DAG の 1 ノード。
#[derive(Clone, Debug, Serialize)]
pub struct Node<J, R> {
    pub rule: R,
    pub premises: Vec<usize>,
    pub conclusion: J,
}

/// 証明 DAG。最後のノードが最終的な結論とは限らないので、`root` で指す。
#[derive(Clone, Debug, Serialize)]
pub struct Proof<J, R> {
    pub nodes: Vec<Node<J, R>>,
    pub root: usize,
}

/// 証明 DAG を組み立てるための道具。
///
/// - `add` は同じ (規則, 前提, 結論) のノードを二重に作らない。
/// - `known` は「この判断はもう証明済み」という表で、証明器のメモ化に使う。
pub struct Builder<J, R> {
    nodes: Vec<Node<J, R>>,
    dedup: HashMap<(R, Vec<usize>, J), usize, FxBuild>,
    known: HashMap<J, usize, FxBuild>,
    /// 各ノードを根とする証明を木に展開したときの大きさ（候補の比較に使う）
    sizes: Vec<u128>,
}

impl<J: Clone + Eq + Hash, R: Clone + Eq + Hash> Default for Builder<J, R> {
    fn default() -> Self {
        Builder { nodes: Vec::new(), dedup: HashMap::default(), known: HashMap::default(), sizes: Vec::new() }
    }
}

impl<J: Clone + Eq + Hash, R: Clone + Eq + Hash> Builder<J, R> {
    pub fn new() -> Self {
        Self::default()
    }

    /// ノードを追加してその番号を返す。
    pub fn add(&mut self, rule: R, premises: Vec<usize>, conclusion: J) -> usize {
        use std::collections::hash_map::Entry;
        // 【Rust メモ】entry は「探して、無ければその場で入れる」を 1 回のハッシュで行う。
        match self.dedup.entry((rule, premises, conclusion)) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                let id = self.nodes.len();
                let (rule, premises, conclusion) = e.key().clone();
                let size = premises.iter().fold(1u128, |acc, &p| acc.saturating_add(self.sizes[p]));
                self.sizes.push(size);
                self.known.entry(conclusion.clone()).or_insert(id);
                self.nodes.push(Node { rule, premises, conclusion });
                e.insert(id);
                id
            }
        }
    }

    /// 判断 `j` がすでに証明済みならそのノード番号。
    pub fn lookup(&self, j: &J) -> Option<usize> {
        self.known.get(j).copied()
    }

    /// ノード `id` を根とする証明を木に展開したときのノード数（上限で飽和）。
    pub fn tree_size(&self, id: usize) -> u128 {
        self.sizes[id]
    }

    pub fn conclusion(&self, id: usize) -> &J {
        &self.nodes[id].conclusion
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// `root` に到達できるノードだけを残して証明として取り出す。
    pub fn finish(self, root: usize) -> Proof<J, R> {
        // 到達可能なノードに印を付ける（前提は必ず前にあるので逆順に走査）
        let mut used = vec![false; self.nodes.len()];
        used[root] = true;
        for i in (0..=root).rev() {
            if used[i] {
                for &p in &self.nodes[i].premises {
                    used[p] = true;
                }
            }
        }
        let mut renum = vec![usize::MAX; self.nodes.len()];
        let mut nodes = Vec::new();
        for (i, node) in self.nodes.into_iter().enumerate() {
            if used[i] {
                renum[i] = nodes.len();
                let premises = node.premises.iter().map(|&p| renum[p]).collect();
                nodes.push(Node { rule: node.rule, premises, conclusion: node.conclusion });
            }
        }
        Proof { root: renum[root], nodes }
    }
}

impl<J, R> Proof<J, R> {
    /// DAG のノード数（共有した部分証明は 1 回と数える）。
    pub fn dag_size(&self) -> usize {
        self.nodes.len()
    }

    /// 木として展開したときのノード数（共有しない素朴な証明の大きさ）。
    /// 巨大になりうるので上限で飽和させる。
    pub fn tree_size(&self) -> u128 {
        let mut size = vec![0u128; self.nodes.len()];
        for (i, node) in self.nodes.iter().enumerate() {
            size[i] = node
                .premises
                .iter()
                .fold(1u128, |acc, &p| acc.saturating_add(size[p]));
        }
        size[self.root]
    }

    /// 証明の高さ（最長の枝の長さ）。
    pub fn height(&self) -> usize {
        let mut h = vec![0usize; self.nodes.len()];
        for (i, node) in self.nodes.iter().enumerate() {
            h[i] = 1 + node.premises.iter().map(|&p| h[p]).max().unwrap_or(0);
        }
        h[self.root]
    }

    pub fn conclusion(&self) -> &J {
        &self.nodes[self.root].conclusion
    }
}

/// 証明を検査し、正しければ最終的な結論を返す。
pub fn check<C: Calculus>(proof: &Proof<C::Judgment, C::Rule>) -> Result<&C::Judgment, String> {
    if proof.root >= proof.nodes.len() {
        return Err("root が範囲外".to_string());
    }
    for (i, node) in proof.nodes.iter().enumerate() {
        let mut prem = Vec::with_capacity(node.premises.len());
        for &p in &node.premises {
            if p >= i {
                return Err(format!("ノード {i}: 前提 {p} が自分より後ろにある"));
            }
            prem.push(&proof.nodes[p].conclusion);
        }
        C::check_step(&node.rule, &prem, &node.conclusion)
            .map_err(|e| format!("ノード {i} ({} : {}): {e}", node.rule, node.conclusion))?;
    }
    Ok(&proof.nodes[proof.root].conclusion)
}

impl<J: fmt::Display, R: fmt::Display> fmt::Display for Proof<J, R> {
    /// 1 行 1 ノードで表示する：`  12. 1 1 ⊢ 0 1      [R3: 4, 11]`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lines: Vec<String> = self.nodes.iter().map(|n| n.conclusion.to_string()).collect();
        let width = lines.iter().map(|s| s.chars().count()).max().unwrap_or(0);
        for (i, (node, line)) in self.nodes.iter().zip(&lines).enumerate() {
            let pad = width - line.chars().count();
            let prem: Vec<String> = node.premises.iter().map(|p| p.to_string()).collect();
            let refs = if prem.is_empty() { String::new() } else { format!(": {}", prem.join(", ")) };
            writeln!(f, "{i:>5}. {line}{}   [{}{refs}]", " ".repeat(pad), node.rule)?;
        }
        Ok(())
    }
}
