//! 固定長のビット集合。Kripke モデルの「点の集合」や関係の各行に使う。
//!
//! 64 個の点を 1 つの u64 に詰めるので、和集合・共通部分が 64 点ずつ
//! まとめて計算でき、閉包計算が速くなる。

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct BitSet {
    len: usize,
    words: Vec<u64>,
}

impl BitSet {
    /// 空集合（要素は 0..len の範囲）。
    pub fn new(len: usize) -> Self {
        BitSet { len, words: vec![0; len.div_ceil(64)] }
    }

    /// 全体集合 {0, …, len-1}。
    pub fn full(len: usize) -> Self {
        let mut s = Self::new(len);
        for i in 0..len {
            s.insert(i);
        }
        s
    }

    pub fn capacity(&self) -> usize {
        self.len
    }

    pub fn contains(&self, i: usize) -> bool {
        self.words[i / 64] >> (i % 64) & 1 == 1
    }

    /// 要素を加える。新しく加わったら true。
    pub fn insert(&mut self, i: usize) -> bool {
        let before = self.words[i / 64];
        self.words[i / 64] |= 1 << (i % 64);
        before != self.words[i / 64]
    }

    /// self ∪= other。変化があれば true。
    pub fn union_with(&mut self, other: &BitSet) -> bool {
        let mut changed = false;
        for (a, b) in self.words.iter_mut().zip(&other.words) {
            let new = *a | *b;
            changed |= new != *a;
            *a = new;
        }
        changed
    }

    /// self ∩= other。
    pub fn intersect_with(&mut self, other: &BitSet) {
        for (a, b) in self.words.iter_mut().zip(&other.words) {
            *a &= *b;
        }
    }

    /// self ∩ other ≠ ∅ か。
    pub fn intersects(&self, other: &BitSet) -> bool {
        self.words.iter().zip(&other.words).any(|(a, b)| a & b != 0)
    }

    pub fn is_empty(&self) -> bool {
        self.words.iter().all(|&w| w == 0)
    }

    pub fn count(&self) -> usize {
        self.words.iter().map(|w| w.count_ones() as usize).sum()
    }

    /// 要素を小さい順に列挙する。
    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.len).filter(|&i| self.contains(i))
    }
}
