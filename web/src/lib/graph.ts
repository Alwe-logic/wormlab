// Kripke モデル（RC の閉包モデル、RC_BI の M_A）を SVG で描く。
//
// 点の配置は Rust 側（wormlab-core の modelview）が計算して JSON の layout に入れてくる：
// 根から「骨組みの辺」（閉包を取る前の辺）をたどった深さで段に分け、段の中では親の位置の
// 平均（重心）で並べる。TikZ の図も同じ配置なので、見た目がそろう。
// 辺は関係ごとに色を固定して描く。閉包で足した辺は多くなりがちなので、関係ごとに
// チェックを入れたものだけ描く。

import { h, hideTip, s, showTip } from './dom';
import { tr } from './i18n';
import { texBlock } from './latex';
import { call } from './wasm';

export interface Point {
  id: number;
  label: string;
  kind: string;
  /** "point"・"tree"・"zero"・"int"・"copy" */
  tag: string;
  latex: string;
  anchor?: number | null;
}

export interface ModelJson {
  root: number;
  points: Point[];
  relations: { name: string; latex: string; edges: [number, number][] }[];
  base_edges: [number, string, number][];
  highlight: number[];
  layout: { x: number[]; y: number[]; width: number; height: number };
  holds?: boolean;
  title?: string;
  frame_violations?: string[] | null;
}

const R = 15; // 点の半径（Rust の modelview::RADIUS と同じ）
let figures = 0; // これまでに描いた図の数（矢印の id を図ごとに変えるため）

/** 関係の色（固定の順。9 本目以降は灰色）。 */
function color(i: number): string {
  return i < 8 ? `var(--series-${i + 1})` : 'var(--series-muted)';
}

function kindFill(tag: string): string {
  if (tag === 'zero') return 'var(--kind-zero)';
  if (tag === 'int') return 'var(--kind-int)';
  if (tag === 'copy') return 'var(--kind-copy)';
  return 'var(--kind-tree)';
}

/** 2 点を結ぶ（曲げ量 bend の）パス。端は点の円の外側から。 */
function edgePath(x1: number, y1: number, x2: number, y2: number, bend: number): string {
  if (x1 === x2 && y1 === y2) {
    // 自己ループ：点の上に小さな輪
    const k = 10 + Math.abs(bend);
    return `M ${x1 - 6} ${y1 - R + 2} C ${x1 - 26 - k} ${y1 - 46 - k}, ${x1 + 26 + k} ${y1 - 46 - k}, ${x1 + 6} ${y1 - R + 2}`;
  }
  const dx = x2 - x1;
  const dy = y2 - y1;
  const len = Math.hypot(dx, dy);
  const ux = dx / len;
  const uy = dy / len;
  const sx = x1 + ux * R;
  const sy = y1 + uy * R;
  const ex = x2 - ux * (R + 3);
  const ey = y2 - uy * (R + 3);
  const mx = (sx + ex) / 2 - uy * bend;
  const my = (sy + ey) / 2 + ux * bend;
  return `M ${sx} ${sy} Q ${mx} ${my} ${ex} ${ey}`;
}

/** モデルを描く。`container` の中身を置き換える。 */
export function renderModel(container: HTMLElement, m: ModelJson, highlightLabel = tr('B が真', 'B is true')): void {
  container.replaceChildren();
  const { x, y, width, height } = m.layout;
  const names = m.relations.map((r) => r.name);
  const colorOf = (name: string) => color(Math.max(0, names.indexOf(name)));

  // 操作：骨組みの辺と、関係ごとの閉包後の辺
  const legend = h('div', { class: 'legend' });
  const showBase = h('input', { type: 'checkbox', checked: true }) as HTMLInputElement;
  legend.append(h('label', {}, showBase, tr('骨組み（閉包の前の辺、太線）', 'skeleton (edges before closure, thick)')));
  const relChecks = m.relations.map((r, i) => {
    const c = h('input', { type: 'checkbox' }) as HTMLInputElement;
    legend.append(
      h('label', {}, c, h('span', { class: 'swatch', style: `background:${color(i)}` }), `${r.name}（${r.edges.length}）`),
    );
    return c;
  });
  container.append(
    h('div', { class: 'muted', style: 'font-size:13px' }, tr(
        '関係のチェックを入れると、閉包を取った後の辺（細線）も描きます。',
        'Check a relation to also draw its edges after closure (thin lines).',
      )),
    legend,
  );

  const svg = s('svg', { width, height, viewBox: `0 0 ${width} ${height}`, role: 'img' });
  const defs = s('defs');
  // 矢印の id は図ごとに変える（同じページに図が 2 つあると、id が重なって隠れた方の矢印を参照してしまう）
  const uid = ++figures;
  const markerFor = (i: number) => {
    const id = `arrow-${uid}-${i}`;
    if (!defs.querySelector(`#${id}`)) {
      defs.append(
        s(
          'marker',
          { id, viewBox: '0 0 10 10', refX: 8, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' },
          s('path', { d: 'M 0 1 L 9 5 L 0 9 z', fill: color(i) }),
        ),
      );
    }
    return `url(#${id})`;
  };
  svg.append(defs);
  const closureLayer = s('g');
  const baseLayer = s('g');
  const nodeLayer = s('g');
  svg.append(closureLayer, baseLayer, nodeLayer);

  const tipOn = (el: SVGElement, text: string) => {
    el.addEventListener('mousemove', (e) => showTip(text, (e as MouseEvent).clientX, (e as MouseEvent).clientY));
    el.addEventListener('mouseleave', hideTip);
  };

  const drawEdges = () => {
    closureLayer.replaceChildren();
    baseLayer.replaceChildren();
    // 同じ 2 点の間に複数の辺があるときは曲げてずらす
    const count = new Map<string, number>();
    const bendFor = (a: number, b: number) => {
      const key = `${a}-${b}`;
      const k = count.get(key) ?? 0;
      count.set(key, k + 1);
      return (k % 2 === 0 ? 1 : -1) * Math.ceil(k / 2) * 14;
    };
    if (showBase.checked) {
      for (const [a, name, b] of m.base_edges) {
        const i = Math.max(0, names.indexOf(name));
        const p = s('path', {
          d: edgePath(x[a], y[a], x[b], y[b], bendFor(a, b)),
          fill: 'none',
          stroke: colorOf(name),
          'stroke-width': 2.2,
          'marker-end': markerFor(i),
        });
        tipOn(p, `${a} ${name} ${b}${tr('（骨組み）', ' (skeleton)')}`);
        // 当たり判定を広げる透明な線
        const hit = s('path', { d: p.getAttribute('d')!, fill: 'none', stroke: 'transparent', 'stroke-width': 10 });
        tipOn(hit, `${a} ${name} ${b}${tr('（骨組み）', ' (skeleton)')}`);
        baseLayer.append(p, hit);
      }
    }
    m.relations.forEach((r, i) => {
      if (!relChecks[i].checked) return;
      for (const [a, b] of r.edges) {
        const p = s('path', {
          d: edgePath(x[a], y[a], x[b], y[b], bendFor(a, b)),
          fill: 'none',
          stroke: color(i),
          'stroke-width': 1.2,
          'stroke-opacity': 0.75,
          'marker-end': markerFor(i),
        });
        tipOn(p, `${a} ${r.name} ${b}`);
        closureLayer.append(p);
      }
    });
  };

  const hl = new Set(m.highlight);
  for (const p of m.points) {
    const g = s('g');
    const ring = hl.has(p.id);
    g.append(
      s('circle', {
        cx: x[p.id],
        cy: y[p.id],
        r: R,
        fill: kindFill(p.tag),
        stroke: ring ? 'var(--accent)' : 'var(--text-secondary)',
        'stroke-width': ring ? 3.5 : 1.2,
      }),
      s(
        'text',
        { x: x[p.id], y: y[p.id] + 4, 'text-anchor': 'middle', 'font-size': 12, fill: 'var(--text-primary)' },
        String(p.id),
      ),
    );
    const sub = [p.label, p.tag === 'tree' || p.tag === 'point' ? '' : p.kind].filter(Boolean).join(' ');
    if (sub) {
      g.append(
        s(
          'text',
          { x: x[p.id], y: y[p.id] + R + 14, 'text-anchor': 'middle', 'font-size': 11, fill: 'var(--text-secondary)' },
          sub,
        ),
      );
    }
    const info = [
      tr(`点 ${p.id}`, `point ${p.id}`),
      p.kind,
      p.label ? tr(`変数：${p.label}`, `variables: ${p.label}`) : '',
      p.anchor !== undefined && p.anchor !== null && p.anchor !== p.id ? `anchor：${p.anchor}` : '',
      ring ? highlightLabel : '',
    ].filter(Boolean);
    tipOn(g, info.join(tr('、', ', ')));
    nodeLayer.append(g);
  }

  // TikZ のコード：図と同じ配置で、いま描いている辺（骨組み・チェックした関係）を描く
  const tikz = texBlock({
    title: tr('TikZ のコード（上の図と同じ配置・同じ辺）', 'TikZ code (same layout and edges as the figure above)'),
    code: '',
    render: 'none',
    note: tr(
      'LaTeX の文書で \\usepackage{tikz} が必要です。チェックを切り替えると、描く辺もそれに合わせて変わります。',
      'Needs \\usepackage{tikz} in your LaTeX document. Toggling the checkboxes changes the edges drawn here too.',
    ),
  });
  const model = JSON.stringify(m);
  const updateTikz = async () => {
    const shown = m.relations.filter((_, i) => relChecks[i].checked).map((r) => r.name);
    try {
      const r = await call<{ tikz: string }>((api) => api.model_tikz(model, JSON.stringify(shown), showBase.checked));
      tikz.setCode(r.tikz);
    } catch (e) {
      tikz.setCode(`% ${e instanceof Error ? e.message : String(e)}`);
    }
  };
  const redraw = () => {
    drawEdges();
    updateTikz();
  };

  showBase.addEventListener('change', redraw);
  relChecks.forEach((c) => c.addEventListener('change', redraw));
  drawEdges();
  container.append(h('div', { class: 'figure' }, svg));

  // 表（色に頼らずに読める形）
  const rows = m.relations.map((r) =>
    h('tr', {}, h('th', {}, r.name), h('td', {}, r.edges.map(([a, b]) => `${a}→${b}`).join(' ') || tr('（なし）', '(none)'))),
  );
  const pointsRow = h(
    'tr',
    {},
    h('th', {}, tr('点', 'points')),
    h('td', {}, m.points.map((p) => `${p.id}:${p.kind}${p.label ? `{${p.label}}` : ''}`).join('  ')),
  );
  container.append(
    h('details', { style: 'margin-top:8px' }, h('summary', {}, tr('表で見る', 'View as a table')), h('table', { class: 'kv' }, pointsRow, ...rows)),
    tikz.el,
  );
  updateTikz();
}
