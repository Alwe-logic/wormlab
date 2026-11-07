// Kripke モデル（RC の閉包モデル、RC_BI の M_A）を SVG で描く。
//
// 点の配置：根から「骨組みの辺」（閉包を取る前の辺）をたどった深さで段に分け、
// 段の中では親の位置の平均（重心）で並べる。辺は関係ごとに色を固定して描く。
// 閉包で足した辺は多くなりがちなので、関係ごとにチェックを入れたものだけ描く。

import { h, hideTip, s, showTip } from './dom';

export interface Point {
  id: number;
  label: string;
  kind: string;
  anchor?: number | null;
}

export interface ModelJson {
  root: number;
  points: Point[];
  relations: { name: string; edges: [number, number][] }[];
  base_edges: [number, string, number][];
  highlight: number[];
  holds?: boolean;
  title?: string;
  frame_violations?: string[] | null;
}

const R = 15; // 点の半径
const LAYER = 92; // 段の間隔
const GAP = 84; // 段の中の点の間隔

/** 関係の色（固定の順。9 本目以降は灰色）。 */
function color(i: number): string {
  return i < 8 ? `var(--series-${i + 1})` : 'var(--series-muted)';
}

function kindFill(kind: string): string {
  if (kind.startsWith('零')) return 'var(--kind-zero)';
  if (kind.startsWith('中間')) return 'var(--kind-int)';
  if (kind.includes('コピー')) return 'var(--kind-copy)';
  return 'var(--kind-tree)';
}

/** 深さと段の中の順番から座標を決める。 */
function layout(m: ModelJson): { x: number[]; y: number[]; width: number; height: number } {
  const n = m.points.length;
  const depth = new Array<number>(n).fill(-1);
  const parents: number[][] = Array.from({ length: n }, () => []);
  const bfs = (adj: number[][]) => {
    const queue = depth.map((d, i) => (d >= 0 ? i : -1)).filter((i) => i >= 0);
    while (queue.length) {
      const x = queue.shift()!;
      for (const y of adj[x]) {
        if (depth[y] < 0) {
          depth[y] = depth[x] + 1;
          parents[y].push(x);
          queue.push(y);
        }
      }
    }
  };
  const baseAdj: number[][] = Array.from({ length: n }, () => []);
  for (const [x, , y] of m.base_edges) if (x !== y) baseAdj[x].push(y);
  depth[m.root] = 0;
  bfs(baseAdj);
  // 骨組みで届かない点は、すべての関係で
  const allAdj: number[][] = Array.from({ length: n }, () => []);
  for (const r of m.relations) for (const [x, y] of r.edges) if (x !== y) allAdj[x].push(y);
  bfs(allAdj);
  const maxD = Math.max(0, ...depth);
  for (let i = 0; i < n; i++) if (depth[i] < 0) depth[i] = maxD + 1;

  const layers: number[][] = [];
  for (let i = 0; i < n; i++) (layers[depth[i]] ??= []).push(i);
  const x = new Array<number>(n).fill(0);
  const widest = Math.max(...layers.map((l) => l?.length ?? 0));
  const width = Math.max(320, (widest + 1) * GAP);
  for (const layer of layers) {
    if (!layer) continue;
    // 親の x の平均で並べる（根の段はそのまま）
    const key = (i: number) =>
      parents[i].length ? parents[i].reduce((a, p) => a + x[p], 0) / parents[i].length : i;
    layer.sort((a, b) => key(a) - key(b) || a - b);
    layer.forEach((p, k) => {
      x[p] = ((k + 1) * width) / (layer.length + 1);
    });
  }
  const y = depth.map((d) => 40 + d * LAYER);
  return { x, y, width, height: 40 + (layers.length - 1) * LAYER + 50 };
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
export function renderModel(container: HTMLElement, m: ModelJson, highlightLabel = 'B が真'): void {
  container.replaceChildren();
  const { x, y, width, height } = layout(m);
  const names = m.relations.map((r) => r.name);
  const colorOf = (name: string) => color(Math.max(0, names.indexOf(name)));

  // 操作：骨組みの辺と、関係ごとの閉包後の辺
  const legend = h('div', { class: 'legend' });
  const showBase = h('input', { type: 'checkbox', checked: true }) as HTMLInputElement;
  legend.append(h('label', {}, showBase, '骨組み（閉包の前の辺、太線）'));
  const relChecks = m.relations.map((r, i) => {
    const c = h('input', { type: 'checkbox' }) as HTMLInputElement;
    legend.append(
      h('label', {}, c, h('span', { class: 'swatch', style: `background:${color(i)}` }), `${r.name}（${r.edges.length}）`),
    );
    return c;
  });
  container.append(
    h('div', { class: 'muted', style: 'font-size:13px' }, '関係のチェックを入れると、閉包を取った後の辺（細線）も描きます。'),
    legend,
  );

  const svg = s('svg', { width, height, viewBox: `0 0 ${width} ${height}`, role: 'img' });
  const defs = s('defs');
  const markerFor = (i: number) => {
    const id = `arrow-${i}`;
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
        tipOn(p, `${a} ${name} ${b}（骨組み）`);
        // 当たり判定を広げる透明な線
        const hit = s('path', { d: p.getAttribute('d')!, fill: 'none', stroke: 'transparent', 'stroke-width': 10 });
        tipOn(hit, `${a} ${name} ${b}（骨組み）`);
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
        fill: kindFill(p.kind),
        stroke: ring ? 'var(--accent)' : 'var(--text-secondary)',
        'stroke-width': ring ? 3.5 : 1.2,
      }),
      s(
        'text',
        { x: x[p.id], y: y[p.id] + 4, 'text-anchor': 'middle', 'font-size': 12, fill: 'var(--text-primary)' },
        String(p.id),
      ),
    );
    const sub = [p.label, p.kind === '構文木' || p.kind === '点' ? '' : p.kind].filter(Boolean).join(' ');
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
      `点 ${p.id}`,
      p.kind,
      p.label ? `変数：${p.label}` : '',
      p.anchor !== undefined && p.anchor !== null && p.anchor !== p.id ? `anchor：${p.anchor}` : '',
      ring ? highlightLabel : '',
    ].filter(Boolean);
    tipOn(g, info.join('、'));
    nodeLayer.append(g);
  }

  showBase.addEventListener('change', drawEdges);
  relChecks.forEach((c) => c.addEventListener('change', drawEdges));
  drawEdges();
  container.append(h('div', { class: 'figure' }, svg));

  // 表（色に頼らずに読める形）
  const rows = m.relations.map((r) =>
    h('tr', {}, h('th', {}, r.name), h('td', {}, r.edges.map(([a, b]) => `${a}→${b}`).join(' ') || '（なし）')),
  );
  const pointsRow = h(
    'tr',
    {},
    h('th', {}, '点'),
    h('td', {}, m.points.map((p) => `${p.id}:${p.kind}${p.label ? `{${p.label}}` : ''}`).join('  ')),
  );
  container.append(
    h('details', { style: 'margin-top:8px' }, h('summary', {}, '表で見る'), h('table', { class: 'kv' }, pointsRow, ...rows)),
  );
}
