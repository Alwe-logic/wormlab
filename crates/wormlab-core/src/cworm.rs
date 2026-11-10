//! 繰り返しでまとめたまま進める worm battle（文字が自然数の worm）。
//!
//! battle の 1 ステップ（[`Worm::battle_step`]）は、先頭の文字 h が 0 ならそれを消し、そうでなければ
//! h 未満の文字が最初に現れる手前までを V とし、V の先頭を h−1 にした V' を m+1 回並べる：
//! A = V U ↦ V'^{m+1} U。worm はすぐに長くなる（worm 3 の 32 ステップ目で 3730 文字）が、
//! 中身は V' の繰り返しなので、「文字」と「ブロックの k 回の繰り返し」の並びで持てば小さく済む。
//!
//! # 1 ステップの進め方
//!
//! worm を逆順（先頭が末尾）の項目の列で持つ。項目は文字 1 つか、ブロック（項目の列）の k 回の繰り返し。
//! 1. 先頭が繰り返しなら 1 回分をほどく（B^k → B B^{k−1}）。先頭が文字になるまで続ける。
//! 2. 先頭の文字 h を取る。h = 0 ならそれで終わり。
//! 3. V を集める：次の項目が h 未満の文字なら止める。繰り返しで、ブロックの最小の文字が h 以上なら
//!    丸ごと V に入れる（ほどかない）。最小の文字が h 未満なら 1 回分をほどいて続ける。
//! 4. V' = (h−1) と集めた項目、をブロックにして、その m+1 回の繰り返しを 1 つの項目として先頭に置く。
//!
//! 長さ（文字の数）は多倍長で数える。順序数 o(A) も、worm を広げずに計算する（[`Summ`]）。

use crate::bignum::BigNat;
use crate::ordinal::Ordinal;
use crate::repeats::{self, Piece};
use crate::worm::Worm;
use std::collections::HashMap;
use std::rc::Rc;

// ----------------------------------------------------------------------
// 順序数の要約
// ----------------------------------------------------------------------

/// 文字の列の、順序数を計算するための要約。
///
/// o(A) の定義：A を文字 0 で A = C_1 0 C_2 0 … 0 C_k と分けると
/// 1 + o(A) = ω^{o(C_k↓)} + … + ω^{o(C_1↓)}（C↓ は文字を 1 ずつ下げたもの）。
/// 列をつなぐと「前の列の最後の成分」と「後の列の最初の成分」がくっつくので、
/// 最初と最後の成分だけを要約のまま持ち、間の成分はもう順序数にして足しておく：
///
/// - `Empty`：空の列
/// - `Free(s)`：0 を含まない列。s は C↓ の要約
/// - `Split(f, mid, l)`：0 を含む列。f = C_1↓ と l = C_k↓ の要約、mid = ω^{o(C_{k−1}↓)} + … + ω^{o(C_2↓)}
///
/// つなぐ操作 [`concat`] は結合法則を満たすので、B^k の要約は 2 乗の繰り返しで log k 回のつなぎで求まる。
#[derive(Clone, Debug)]
enum Summ {
    Empty,
    Free(Rc<Summ>),
    /// 真ん中の和は大きくなるので共有して持つ（要約を写すたびに順序数を写さないように）
    Split(Rc<Summ>, Rc<Ordinal>, Rc<Summ>),
}

/// 文字 x 1 つの要約：x = 0 なら Split(空, 0, 空)、x > 0 なら Free(x−1 の要約)。
fn letter_summ(x: u32) -> Summ {
    let mut s = Summ::Split(Rc::new(Summ::Empty), Rc::new(Ordinal::zero()), Rc::new(Summ::Empty));
    for _ in 0..x {
        s = Summ::Free(Rc::new(s));
    }
    s
}

/// 2 つの列をつないだ列の要約。
fn concat(a: &Summ, b: &Summ) -> Summ {
    use Summ::*;
    match (a, b) {
        (Empty, _) => b.clone(),
        (_, Empty) => a.clone(),
        (Free(x), Free(y)) => Free(Rc::new(concat(x, y))),
        (Free(x), Split(f, m, l)) => Split(Rc::new(concat(x, f)), m.clone(), l.clone()),
        (Split(f, m, l), Free(y)) => Split(f.clone(), m.clone(), Rc::new(concat(l, y))),
        // C_1 … C_k と D_1 … D_j：C_k と D_1 がくっついて 1 つの成分になる
        (Split(f1, m1, l1), Split(f2, m2, l2)) => {
            let joined = Ordinal::omega_pow(value(&concat(l1, f2)));
            Split(f1.clone(), Rc::new((**m2).clone() + joined + (**m1).clone()), l2.clone())
        }
    }
}

/// 列を k 回つないだ列の要約（2 乗を繰り返す）。
fn power(a: &Summ, k: u64) -> Summ {
    let mut result = Summ::Empty;
    let mut base = a.clone();
    let mut k = k;
    while k > 0 {
        if k & 1 == 1 {
            result = concat(&result, &base);
        }
        k >>= 1;
        if k > 0 {
            base = concat(&base, &base);
        }
    }
    result
}

/// 要約された列の順序数 o。
fn value(s: &Summ) -> Ordinal {
    let one_plus = match s {
        Summ::Empty => return Ordinal::zero(),
        Summ::Free(x) => Ordinal::omega_pow(value(x)),
        Summ::Split(f, m, l) => Ordinal::omega_pow(value(l)) + (**m).clone() + Ordinal::omega_pow(value(f)),
    };
    one_plus.minus_one_plus().expect("1 + o は 1 以上")
}

// ----------------------------------------------------------------------
// 項目とブロック
// ----------------------------------------------------------------------

/// worm の項目：文字 1 つ、ブロックの k 回の繰り返し、ブロックの i 番目から後ろ（1 回）。
///
/// 繰り返しをほどくとき、ブロックの中身を全部積むと項目の数がどんどん増える（worm 4 では
/// 200 ステップで 1 万を超えた）。そこで B^k は「B の 0 番目から後ろ」と B^{k−1} の 2 つにだけ
/// ほどき、「i 番目から後ろ」は必要になったら「i 番目の項目」と「i+1 番目から後ろ」に分ける。
#[derive(Clone, Debug)]
pub enum Item {
    Letter(u32),
    Rep(Rc<Block>, u64),
    Slice(Rc<Block>, usize),
}

/// 項目の列（繰り返しの中身）。i 番目から後ろの長さ・最小の文字・順序数の要約を覚えておく
/// （「i 番目から後ろ」の項目をほどかずに扱えるように）。
#[derive(Debug)]
pub struct Block {
    items: Vec<Item>,
    /// suf_len[i] = items[i..] の長さ（i = items.len() は 0）
    suf_len: Vec<BigNat>,
    suf_min: Vec<u32>,
    suf_summ: Vec<Summ>,
}

impl Block {
    fn new(items: Vec<Item>) -> Block {
        let n = items.len();
        let mut suf_len = vec![BigNat::zero(); n + 1];
        let mut suf_min = vec![u32::MAX; n + 1];
        let mut suf_summ = vec![Summ::Empty; n + 1];
        for i in (0..n).rev() {
            suf_len[i] = items[i].len().add(&suf_len[i + 1]);
            suf_min[i] = items[i].min().min(suf_min[i + 1]);
            suf_summ[i] = concat(&items[i].summ(), &suf_summ[i + 1]);
        }
        Block { items, suf_len, suf_min, suf_summ }
    }

    fn len(&self) -> &BigNat {
        &self.suf_len[0]
    }

    fn min(&self) -> u32 {
        self.suf_min[0]
    }

    pub fn items(&self) -> &[Item] {
        &self.items
    }
}

impl Item {
    fn len(&self) -> BigNat {
        match self {
            Item::Letter(_) => BigNat::from(1u64),
            Item::Rep(b, k) => b.len().mul_small(*k),
            Item::Slice(b, i) => b.suf_len[*i].clone(),
        }
    }

    fn min(&self) -> u32 {
        match self {
            Item::Letter(x) => *x,
            Item::Rep(b, _) => b.min(),
            Item::Slice(b, i) => b.suf_min[*i],
        }
    }

    fn summ(&self) -> Summ {
        match self {
            Item::Letter(x) => letter_summ(*x),
            Item::Rep(b, k) => power(&b.suf_summ[0], *k),
            Item::Slice(b, i) => b.suf_summ[*i].clone(),
        }
    }
}

// ----------------------------------------------------------------------
// まとめたままの worm
// ----------------------------------------------------------------------

/// 文字の大きさの上限（順序数の要約が文字の大きさだけ入れ子になるので）。
pub const MAX_LETTER: u32 = 100;

/// 繰り返しでまとめたまま持つ worm。
#[derive(Clone, Debug)]
pub struct CWorm {
    /// 項目の列（逆順：末尾が worm の先頭）
    rev: Vec<Item>,
    /// acc[i] = rev[0..=i] の部分（worm の後ろの方）の要約
    acc: Vec<Summ>,
    len: BigNat,
}

impl CWorm {
    /// worm から作る（初めから繰り返しのある所はまとめておく）。文字が [`MAX_LETTER`] を超えれば `None`。
    pub fn new(w: &Worm) -> Option<CWorm> {
        let ls = w.letters();
        if ls.iter().any(|&x| x > MAX_LETTER) {
            return None;
        }
        fn items(pieces: &[Piece], ls: &[u32]) -> Vec<Item> {
            pieces
                .iter()
                .map(|p| match p {
                    Piece::One(i) => Item::Letter(ls[*i]),
                    Piece::Rep(inner, k) => Item::Rep(Rc::new(Block::new(items(inner, ls))), *k as u64),
                })
                .collect()
        }
        let forward = items(&repeats::compress(ls), ls);
        let mut c = CWorm { rev: Vec::new(), acc: Vec::new(), len: BigNat::zero() };
        for it in forward.into_iter().rev() {
            c.len = c.len.add(&it.len());
            c.push(it);
        }
        Some(c)
    }

    fn push(&mut self, it: Item) {
        let rest = self.acc.last().cloned().unwrap_or(Summ::Empty);
        self.acc.push(concat(&it.summ(), &rest));
        self.rev.push(it);
    }

    fn pop(&mut self) -> Option<Item> {
        self.acc.pop();
        self.rev.pop()
    }

    /// 長さ（文字の数）。
    pub fn len(&self) -> &BigNat {
        &self.len
    }

    /// ⊤（空の worm）か。
    pub fn is_top(&self) -> bool {
        self.rev.is_empty()
    }

    /// 順序数 o(A)（worm を広げずに計算する）。
    pub fn ordinal(&self) -> Ordinal {
        self.acc.last().map_or(Ordinal::zero(), value)
    }

    /// 項目の数（まとめた形の大きさの目安）。
    pub fn items(&self) -> usize {
        self.rev.len()
    }

    /// 先頭の項目が文字でなければ 1 段ほどく。ほどいたら true。
    /// B^k → (B の 0 番目から後ろ) B^{k−1}、(B の i 番目から後ろ) → (B の i 番目) (B の i+1 番目から後ろ)。
    fn expand_top(&mut self) -> bool {
        match self.rev.last() {
            Some(Item::Rep(..)) => {
                let Some(Item::Rep(b, k)) = self.pop() else { unreachable!() };
                if k > 1 {
                    self.push(Item::Rep(b.clone(), k - 1));
                }
                if !b.items.is_empty() {
                    self.push(Item::Slice(b, 0));
                }
                true
            }
            Some(Item::Slice(..)) => {
                let Some(Item::Slice(b, i)) = self.pop() else { unreachable!() };
                if i + 1 < b.items.len() {
                    self.push(Item::Slice(b.clone(), i + 1));
                }
                self.push(b.items[i].clone());
                true
            }
            _ => false,
        }
    }

    /// battle の 1 ステップ（m は [`Worm::battle_step`] と同じ）。⊤ なら何もせず false。
    pub fn step(&mut self, m: u64) -> bool {
        while self.expand_top() {}
        let Some(Item::Letter(h)) = self.pop() else { return false };
        if h == 0 {
            self.len = self.len.sub_small(1).expect("先頭の文字の分はある");
            return true;
        }
        // V を集める：h 未満の文字の手前まで。最小の文字が h 以上の項目（繰り返し・後ろの部分）は丸ごと入る
        let mut v = vec![Item::Letter(h - 1)];
        loop {
            match self.rev.last() {
                None => break,
                Some(Item::Letter(x)) if *x < h => break,
                Some(it) if it.min() < h => {
                    self.expand_top();
                }
                Some(_) => v.push(self.pop().expect("ある")),
            }
        }
        let block = Rc::new(Block::new(v));
        // 長さ：|V| 文字が (m+1)·|V| 文字になる
        self.len = self.len.add(&block.len().mul_small(m));
        self.push(Item::Rep(block, m + 1));
        true
    }

    /// 長さが `max_len` 以下なら、ふつうの worm に広げる（テスト用）。
    pub fn to_worm(&self, max_len: u64) -> Option<Worm> {
        if self.len.to_u64()? > max_len {
            return None;
        }
        fn go(it: &Item, out: &mut Vec<u32>) {
            match it {
                Item::Letter(x) => out.push(*x),
                Item::Rep(b, k) => {
                    for _ in 0..*k {
                        for i in &b.items {
                            go(i, out);
                        }
                    }
                }
                Item::Slice(b, i) => {
                    for j in &b.items[*i..] {
                        go(j, out);
                    }
                }
            }
        }
        let mut out = Vec::new();
        for it in self.rev.iter().rev() {
            go(it, &mut out);
        }
        Some(Worm::new(out))
    }

    /// 表示用の形（[`Shape`]）：繰り返しをまとめ直し、書く文字が `budget` を超えたら先頭だけ（`truncated`）。
    /// ブロックは共有されているので、そのまま広げると大きくなりうる。作りながら数えて、上限で止める。
    pub fn view(&self, budget: usize) -> View {
        let forward: Vec<Item> = self.rev.iter().rev().cloned().collect();
        let mut b = Builder { left: budget, truncated: false, memo: HashMap::new() };
        let shapes = b.list(&forward);
        View { shapes, truncated: b.truncated }
    }
}

// ----------------------------------------------------------------------
// 表示用の形
// ----------------------------------------------------------------------

/// 表示用の形：文字か、中身の k 回の繰り返し。
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Shape {
    Letter(u32),
    Rep(Vec<Shape>, u64),
}

/// 表示用の形の列と、途中で切ったか。
#[derive(Clone, Debug)]
pub struct View {
    pub shapes: Vec<Shape>,
    pub truncated: bool,
}

/// 表示用の形を作る：書いた文字の数を数え、`left` が尽きたら止める。
/// 同じブロック（の i 番目から後ろ）の形は覚えておく。
struct Builder {
    left: usize,
    truncated: bool,
    memo: HashMap<(*const Block, usize), (Vec<Shape>, usize)>,
}

impl Builder {
    fn list(&mut self, items: &[Item]) -> Vec<Shape> {
        let mut out: Vec<Shape> = Vec::new();
        for it in items {
            if self.truncated {
                break;
            }
            match it {
                Item::Letter(x) => {
                    if self.left == 0 {
                        self.truncated = true;
                        break;
                    }
                    self.left -= 1;
                    out.push(Shape::Letter(*x));
                }
                Item::Rep(b, k) => {
                    let inner = self.block(b, 0);
                    out.extend(rep(inner, *k));
                }
                Item::Slice(b, i) => {
                    let part = self.block(b, *i);
                    out.extend(part);
                }
            }
            merge_tail(&mut out);
        }
        recompress(out)
    }

    /// ブロック b の i 番目から後ろの形。
    fn block(&mut self, b: &Rc<Block>, i: usize) -> Vec<Shape> {
        let key = (Rc::as_ptr(b), i);
        if let Some((s, n)) = self.memo.get(&key)
            && *n <= self.left
        {
            self.left -= *n;
            return s.clone();
        }
        let before = self.left;
        let s = self.list(&b.items[i..]);
        if !self.truncated {
            self.memo.insert(key, (s.clone(), before - self.left));
        }
        s
    }
}

/// 中身を k 回繰り返した形（k = 1 なら中身そのもの、中身が 1 つの繰り返しなら回数を掛ける）。
fn rep(inner: Vec<Shape>, k: u64) -> Vec<Shape> {
    if k == 1 || inner.is_empty() {
        return inner;
    }
    if let [Shape::Rep(x, j)] = inner.as_slice()
        && let Some(jk) = j.checked_mul(k)
    {
        return vec![Shape::Rep(x.clone(), jk)];
    }
    vec![Shape::Rep(inner, k)]
}

/// 列の末尾で、隣り合う同じ繰り返しをまとめる：X^a X^b → X^{a+b}、X X^a → X^{a+1}、X^a X → X^{a+1}。
fn merge_tail(out: &mut Vec<Shape>) {
    loop {
        let n = out.len();
        // X^a X^b
        if n >= 2
            && let (Shape::Rep(x, a), Shape::Rep(y, b)) = (&out[n - 2], &out[n - 1])
            && x == y
            && let Some(ab) = a.checked_add(*b)
        {
            let x = x.clone();
            out.truncate(n - 2);
            out.push(Shape::Rep(x, ab));
            continue;
        }
        // X X^a（X^a の直前に X の中身がそのまま並んでいる）
        if let Some(Shape::Rep(x, a)) = out.last() {
            let w = x.len();
            if n > w && out[n - 1 - w..n - 1] == x[..] {
                let (x, a) = (x.clone(), *a);
                out.truncate(n - 1 - w);
                out.push(Shape::Rep(x, a + 1));
                continue;
            }
        }
        // X^a X（末尾の w 個が、その手前の X^a の中身と同じ）
        let found = (1..n).find_map(|w| match out.get(n - w - 1) {
            Some(Shape::Rep(x, a)) if x.len() == w && out[n - w..] == x[..] => Some((x.clone(), *a)),
            _ => None,
        });
        if let Some((x, a)) = found {
            out.truncate(n - x.len() - 1);
            out.push(Shape::Rep(x, a + 1));
            continue;
        }
        break;
    }
}

/// 形の列の中に、まだまとめていない繰り返しがあればまとめる（[`repeats::compress`] を形の列に使う）。
fn recompress(shapes: Vec<Shape>) -> Vec<Shape> {
    if shapes.len() < 2 || shapes.len() > 2_000 {
        return shapes;
    }
    let pieces = repeats::compress(&shapes);
    fn build(pieces: &[Piece], shapes: &[Shape]) -> Vec<Shape> {
        let mut out = Vec::new();
        for p in pieces {
            match p {
                Piece::One(i) => out.push(shapes[*i].clone()),
                Piece::Rep(inner, k) => out.extend(rep(build(inner, shapes), *k as u64)),
            }
            merge_tail(&mut out);
        }
        out
    }
    build(&pieces, &shapes)
}

/// まとめた形を `(2 0 1)^3 1^5` のように書く（[`repeats::worm`] と同じ書き方）。
pub fn text(shapes: &[Shape]) -> String {
    shapes
        .iter()
        .map(|s| match s {
            Shape::Letter(x) => x.to_string(),
            Shape::Rep(inner, k) => match inner.as_slice() {
                [Shape::Letter(x)] => format!("{x}^{k}"),
                _ => format!("({})^{k}", text(inner)),
            },
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// まとめた形の LaTeX（最後の ⊤ なし）。
pub fn latex(shapes: &[Shape]) -> String {
    shapes
        .iter()
        .map(|s| match s {
            Shape::Letter(x) => format!("\\langle {x}\\rangle"),
            Shape::Rep(inner, k) => match inner.as_slice() {
                [Shape::Letter(x)] => format!("\\langle {x}\\rangle^{{{k}}}"),
                _ => format!("\\left({}\\right)^{{{k}}}", latex(inner)),
            },
        })
        .collect()
}

/// まとめた形で書いた文字の数。
pub fn shown(shapes: &[Shape]) -> usize {
    shapes
        .iter()
        .map(|s| match s {
            Shape::Letter(_) => 1,
            Shape::Rep(inner, _) => shown(inner),
        })
        .sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// まとめたまま進めた battle が、ふつうの battle と同じ worm・長さ・順序数になる
    #[test]
    fn agrees_with_plain_battle() {
        for start in ["3", "2 0 2", "1 2 1", "2 2", "1 1 0 2", "3 1 2", "2 1 0 2 1", "1 3 0 2", "4"] {
            let w: Worm = start.parse().unwrap();
            let mut c = CWorm::new(&w).unwrap();
            for (k, plain) in w.battle().enumerate().take(60) {
                if plain.len() > 20_000 {
                    break;
                }
                assert_eq!(c.to_worm(100_000).as_ref(), Some(&plain), "{start} の {k} ステップ目");
                assert_eq!(c.len().to_u64(), Some(plain.len() as u64));
                assert_eq!(c.ordinal(), plain.ordinal(), "{start} の {k} ステップ目の順序数");
                c.step(k as u64 + 1);
            }
        }
    }

    #[test]
    fn view_of_long_worm() {
        // worm 3 の 32 ステップ目（3730 文字）
        let mut c = CWorm::new(&"3".parse().unwrap()).unwrap();
        for m in 1..=32 {
            c.step(m);
        }
        assert_eq!(c.len().to_u64(), Some(3730));
        let v = c.view(10_000);
        assert!(!v.truncated);
        assert!(shown(&v.shapes) < 200, "{}", text(&v.shapes));
    }
}
