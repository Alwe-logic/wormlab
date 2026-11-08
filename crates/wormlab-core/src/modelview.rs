//! Kripke モデルを描くための形と、TikZ への書き出し。
//!
//! RC の閉包モデル（[`crate::rc::Model`]）も RC_BI の M_A（[`crate::rcbi::Model`]）も、
//! いったん同じ [`ModelView`]（点・関係・骨組みの辺・点の配置）に直す。Web の図（SVG）と
//! TikZ の図はどちらもこの配置を使うので、同じ形の図になる。
//!
//! 配置：根から「骨組みの辺」（閉包を取る前の辺）をたどった深さで段に分け、段の中では
//! 親の位置の平均（重心）で並べる。単位は Web の図のピクセル（TikZ では 60 px = 1 cm）。
//!
//! 【Rust メモ】`#[derive(Serialize, Deserialize)]` で JSON との相互変換ができる。
//! Web では、一度 JSON にして渡したモデルを送り返してもらい、TikZ にするのに使う。

use crate::bitset::BitSet;
use crate::latex;
use crate::letter::Letter;
use crate::spf::Spf;
use crate::{rc, rcbi};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet, VecDeque};

/// 点の半径・段の間隔（ピクセル）。
pub const RADIUS: f64 = 15.0;
pub const LAYER: f64 = 92.0;
pub const GAP: f64 = 84.0;

/// 点。
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct PointView {
    pub id: usize,
    /// 真な変数（RC）。カンマ区切り
    pub label: String,
    /// 点の種類（表示用）
    pub kind: String,
    /// 種類の短い名前："point"（RC）・"tree"・"zero"・"int"・"copy"（RC_BI）
    pub tag: String,
    /// TikZ で点の下に書く数式（`\{p, q\}`、`3{\downarrow}` など。空なら書かない）
    pub latex: String,
    pub anchor: Option<usize>,
}

/// 関係（閉包を取った後の辺の全体）。
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct RelationView {
    pub name: String,
    pub latex: String,
    pub edges: Vec<(usize, usize)>,
}

/// 点の配置（ピクセル）。
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Layout {
    pub x: Vec<f64>,
    pub y: Vec<f64>,
    pub width: f64,
    pub height: f64,
}

/// 描くためのモデル。
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ModelView {
    pub root: usize,
    pub points: Vec<PointView>,
    pub relations: Vec<RelationView>,
    /// 骨組みの辺 (始点, 関係の名前, 終点)
    pub base_edges: Vec<(usize, String, usize)>,
    /// 印を付ける点（右辺が真の点など）
    pub highlight: Vec<usize>,
    pub layout: Layout,
}

fn edges_of(rows: &[BitSet]) -> Vec<(usize, usize)> {
    rows.iter().enumerate().flat_map(|(x, row)| row.iter().map(move |y| (x, y))).collect()
}

impl ModelView {
    fn new(
        root: usize,
        points: Vec<PointView>,
        relations: Vec<RelationView>,
        base_edges: Vec<(usize, String, usize)>,
        highlight: Vec<usize>,
    ) -> ModelView {
        let layout = layout(root, points.len(), &relations, &base_edges);
        ModelView { root, points, relations, base_edges, highlight, layout }
    }

    /// RC の閉包モデル。`highlight` が真になる点に印を付ける。
    pub fn from_rc<L: Letter>(m: &rc::Model<L>, highlight: Option<&Spf<L>>) -> ModelView {
        let n = m.num_points();
        let points = (0..n)
            .map(|x| {
                let vars: Vec<&String> = m.label(x).iter().collect();
                let label = vars.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(",");
                let tex = if vars.is_empty() {
                    String::new()
                } else {
                    format!("\\{{{}\\}}", vars.iter().map(|v| latex::var(v)).collect::<Vec<_>>().join(", "))
                };
                PointView { id: x, label, kind: "点".to_string(), tag: "point".to_string(), latex: tex, anchor: None }
            })
            .collect();
        let relations = m
            .signature()
            .iter()
            .map(|l| RelationView {
                name: format!("R_{l}"),
                latex: format!("R_{{{}}}", l.to_latex()),
                edges: (0..n).flat_map(|x| (0..n).filter(move |&y| m.related(l, x, y)).map(move |y| (x, y))).collect(),
            })
            .collect();
        let base = m.tree_edges().iter().map(|(x, l, y)| (*x, format!("R_{l}"), *y)).collect();
        let hl = highlight.map(|b| m.truth_set(b).iter().collect()).unwrap_or_default();
        ModelView::new(0, points, relations, base, hl)
    }

    /// RC_BI の有限モデル M_A。
    pub fn from_rcbi(m: &rcbi::Model, highlight: Option<&rcbi::Formula>) -> ModelView {
        let n = m.num_points();
        let points = (0..n)
            .map(|x| {
                let (kind, tag, tex) = match m.kind(x) {
                    rcbi::PointKind::Tree => ("構文木".to_string(), "tree", String::new()),
                    rcbi::PointKind::Zero => ("零点".to_string(), "zero", "\\mathrm{zero}".to_string()),
                    rcbi::PointKind::Intermediate => ("中間点".to_string(), "int", "\\mathrm{int}".to_string()),
                    rcbi::PointKind::Copy(b) => (format!("{b} のコピー点"), "copy", format!("{b}{{\\downarrow}}")),
                };
                PointView { id: x, label: String::new(), kind, tag: tag.to_string(), latex: tex, anchor: m.anchor(x) }
            })
            .collect();
        let relations = m
            .relations()
            .into_iter()
            .zip(m.relation_latex_names())
            .map(|((name, rows), tex)| RelationView { name, latex: tex, edges: edges_of(rows) })
            .collect();
        let hl = highlight.map(|b| m.truth_set(b).iter().collect()).unwrap_or_default();
        ModelView::new(0, points, relations, m.base_edges(), hl)
    }

    /// TikZ の図にする（`\begin{tikzpicture} … \end{tikzpicture}`、`\usepackage{tikz}` が必要）。
    ///
    /// 骨組みの辺（`base` が真のとき、太線）と、名前が `shown` に入っている関係の辺（細線）を描く。
    /// 色は Web の図と同じ順。幅が 16 cm を超えるときは縮める（点の大きさはそのまま）。
    pub fn tikz(&self, shown: &[String], base: bool) -> String {
        const PALETTE: [&str; 8] = ["2A78D6", "EB6834", "1BAF7A", "EDA100", "E87BA4", "008300", "6250D6", "E34948"];
        const MUTED: &str = "898781";
        let n = self.points.len();
        let cm = 1.0 / 60.0;
        let fit = if self.layout.width * cm > 16.0 { 16.0 / (self.layout.width * cm) } else { 1.0 };
        let k = cm * fit;
        let px = |i: usize| self.layout.x[i] * k;
        let py = |i: usize| -self.layout.y[i] * k;
        let index_of = |name: &str| self.relations.iter().position(|r| r.name == name);

        let mut out = String::from("% wormlab: Kripke model (\\usepackage{tikz})\n");
        out.push_str(
            "\\begin{tikzpicture}[>=stealth,\n  \
             pt/.style={circle, draw=black!70, minimum size=5.5mm, inner sep=0pt, font=\\scriptsize},\n  \
             zero/.style={fill=blue!12}, int/.style={fill=black!10}, copy/.style={fill=orange!20},\n  \
             hl/.style={draw=blue!70!black, very thick},\n  \
             lab/.style={font=\\tiny, text=black!60, inner sep=1pt}]\n",
        );
        for (i, _) in self.relations.iter().enumerate() {
            let c = PALETTE.get(i).copied().unwrap_or(MUTED);
            out.push_str(&format!("\\definecolor{{wlr{i}}}{{HTML}}{{{c}}}\n"));
        }

        // 点
        let hl: HashSet<usize> = self.highlight.iter().copied().collect();
        for p in &self.points {
            let mut style = String::from("pt");
            match p.tag.as_str() {
                "zero" | "int" | "copy" => style.push_str(&format!(", {}", p.tag)),
                _ => {}
            }
            if hl.contains(&p.id) {
                style.push_str(", hl");
            }
            if !p.latex.is_empty() {
                style.push_str(&format!(", label={{[lab]below:${}$}}", p.latex));
            }
            out.push_str(&format!("\\node[{style}] (p{}) at ({:.2}, {:.2}) {{{}}};\n", p.id, px(p.id), py(p.id), p.id));
        }

        // 辺：(始点, 終点, 関係の番号, 骨組みか)
        let mut edges: Vec<(usize, usize, usize, bool)> = Vec::new();
        if base {
            for (a, name, b) in &self.base_edges {
                edges.push((*a, *b, index_of(name).unwrap_or(0), true));
            }
        }
        for (i, r) in self.relations.iter().enumerate() {
            if shown.contains(&r.name) {
                edges.extend(r.edges.iter().map(|&(a, b)| (a, b, i, false)));
            }
        }
        let pairs: HashSet<(usize, usize)> = edges.iter().map(|&(a, b, _, _)| (a, b)).collect();
        let mut count: HashMap<(usize, usize), usize> = HashMap::new();
        for &(a, b, i, thick) in &edges {
            let style = if thick { format!("->, thick, wlr{i}") } else { format!("->, wlr{i}, opacity=0.6") };
            let c = count.entry((a, b)).or_insert(0);
            let j = *c;
            *c += 1;
            if a == b {
                out.push_str(&format!(
                    "\\draw[{style}] (p{a}) to[out={}, in={}, looseness={}] (p{a});\n",
                    115 + 10 * j,
                    65 - 10 * j as i64,
                    7 + 2 * j
                ));
                continue;
            }
            // 同じ 2 点の間の 2 本目以降は曲げてずらす。逆向きの辺もあるときは少し曲げて重ならないように
            let sign = if j & 1 == 0 { 1 } else { -1 };
            let mut bend = sign * j.div_ceil(2) as i64 * 12;
            if pairs.contains(&(b, a)) {
                bend += 10;
            }
            let path = match bend {
                0 => "--".to_string(),
                d if d > 0 => format!("to[bend left={d}]"),
                d => format!("to[bend right={}]", -d),
            };
            out.push_str(&format!("\\draw[{style}] (p{a}) {path} (p{b});\n"));
        }

        // 凡例：描いた関係だけ
        let used: Vec<usize> = (0..self.relations.len()).filter(|&i| edges.iter().any(|e| e.2 == i)).collect();
        if !used.is_empty() && n > 0 {
            let x0 = (0..n).map(px).fold(f64::INFINITY, f64::min);
            let y0 = (0..n).map(py).fold(f64::INFINITY, f64::min);
            let items: Vec<String> = used
                .iter()
                .map(|&i| format!("\\textcolor{{wlr{i}}}{{\\rule[0.5ex]{{1.2em}}{{1pt}}}}\\,${}$", self.relations[i].latex))
                .collect();
            let note = match (base, edges.iter().any(|e| !e.3)) {
                (true, true) => "\\quad (thick: tree edges, thin: closure)",
                _ => "",
            };
            out.push_str(&format!(
                "\\node[anchor=north west, font=\\scriptsize] at ({:.2}, {:.2}) {{{}{note}}};\n",
                x0 - 0.3,
                y0 - 0.6,
                items.join("\\quad ")
            ));
        }
        out.push_str("\\end{tikzpicture}");
        out
    }
}

/// 点の配置。Web の図と同じ手順（web/src/lib/graph.ts もこの結果を使う）。
fn layout(root: usize, n: usize, relations: &[RelationView], base_edges: &[(usize, String, usize)]) -> Layout {
    if n == 0 {
        return Layout { x: Vec::new(), y: Vec::new(), width: 320.0, height: 90.0 };
    }
    let mut depth = vec![-1i64; n];
    let mut parents: Vec<Vec<usize>> = vec![Vec::new(); n];

    // 深さが決まっている点から幅優先でたどり、まだの点に深さと親を付ける
    fn bfs(adj: &[Vec<usize>], depth: &mut [i64], parents: &mut [Vec<usize>]) {
        let mut queue: VecDeque<usize> = (0..depth.len()).filter(|&i| depth[i] >= 0).collect();
        while let Some(x) = queue.pop_front() {
            for &y in &adj[x] {
                if depth[y] < 0 {
                    depth[y] = depth[x] + 1;
                    parents[y].push(x);
                    queue.push_back(y);
                }
            }
        }
    }

    let mut base_adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (x, _, y) in base_edges {
        if x != y {
            base_adj[*x].push(*y);
        }
    }
    depth[root] = 0;
    bfs(&base_adj, &mut depth, &mut parents);
    // 骨組みで届かない点は、すべての関係でたどる
    let mut all_adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for r in relations {
        for &(x, y) in &r.edges {
            if x != y {
                all_adj[x].push(y);
            }
        }
    }
    bfs(&all_adj, &mut depth, &mut parents);
    let max_d = depth.iter().copied().max().unwrap_or(0).max(0);
    for d in depth.iter_mut() {
        if *d < 0 {
            *d = max_d + 1;
        }
    }

    let n_layers = depth.iter().copied().max().unwrap_or(0) as usize + 1;
    let mut layers: Vec<Vec<usize>> = vec![Vec::new(); n_layers];
    for (i, &d) in depth.iter().enumerate() {
        layers[d as usize].push(i);
    }
    let widest = layers.iter().map(|l| l.len()).max().unwrap_or(0);
    let width = f64::max(320.0, (widest + 1) as f64 * GAP);
    let mut x = vec![0.0f64; n];
    for layer in &layers {
        // 親の x の平均で並べる（親のない点は番号で）
        let mut keyed: Vec<(f64, usize)> = layer
            .iter()
            .map(|&i| {
                let ps = &parents[i];
                let key = if ps.is_empty() { i as f64 } else { ps.iter().map(|&p| x[p]).sum::<f64>() / ps.len() as f64 };
                (key, i)
            })
            .collect();
        keyed.sort_by(|a, b| a.0.total_cmp(&b.0).then(a.1.cmp(&b.1)));
        let len = keyed.len() as f64;
        for (k, &(_, p)) in keyed.iter().enumerate() {
            x[p] = (k + 1) as f64 * width / (len + 1.0);
        }
    }
    let y: Vec<f64> = depth.iter().map(|&d| 40.0 + d as f64 * LAYER).collect();
    let height = 40.0 + (n_layers - 1) as f64 * LAYER + 50.0;
    Layout { x, y, width, height }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rc_view_and_tikz() {
        let a: Spf = "<2>p & <1>q".parse().unwrap();
        let m = rc::Model::canonical(&a, &a.modalities());
        let v = ModelView::from_rc(&m, None);
        assert_eq!(v.points.len(), 3);
        assert_eq!(v.layout.y[0], 40.0);
        assert!(v.layout.y[1] > v.layout.y[0]);
        let t = v.tikz(&[], true);
        assert!(t.starts_with("% wormlab"));
        assert_eq!(t.matches("\\node[pt").count(), 3);
        assert_eq!(t.matches("\\draw[").count(), 2);
        assert!(t.contains("$\\{p\\}$"), "{t}");
        // 関係も描く
        let all: Vec<String> = v.relations.iter().map(|r| r.name.clone()).collect();
        assert!(v.tikz(&all, true).matches("\\draw[").count() > 2);
    }

    #[test]
    fn rcbi_view() {
        let a: rcbi::Formula = "D <1> T".parse().unwrap();
        let m = rcbi::Model::of(&a, a.max_rank());
        let v = ModelView::from_rcbi(&m, None);
        assert_eq!(v.points.len(), 5);
        assert!(v.points.iter().any(|p| p.tag == "zero"));
        assert_eq!(v.relations.len(), m.relations().len());
        assert!(v.relations.iter().any(|r| r.latex == "R_{\\downarrow}"));
        // JSON にして戻しても同じ
        // （serde_json は core の依存にないので、ここでは配置の長さだけ確かめる）
        assert_eq!(v.layout.x.len(), 5);
    }
}
