// battle の表示に使う小さなグラフ：worm の棒グラフ、括弧語の入れ子のブロック、長さの推移の折れ線。

import { h, hideTip, s, showTip } from './dom';
import { lang, tr } from './i18n';

/**
 * worm を棒の列で描く（左が外側＝先頭の文字＝頭）。高さ ∝ 値。
 * 棒はブロックを積んだ形（アーケードのドット絵）にし、先頭の棒には worm の目を付ける。
 * worm が長くて棒が細いときは、ブロックに分けずにただの棒にする。
 * `labels` は棒ごとのツールチップの文字。
 */
export function bars(container: HTMLElement, values: number[], labels: string[], maxValue: number): void {
  container.replaceChildren();
  const W = Math.max(320, Math.min(1060, container.clientWidth || 1060));
  const H = 150;
  const n = values.length;
  const svg = s('svg', { width: W, height: H + 24, viewBox: `0 0 ${W} ${H + 24}`, role: 'img' });
  svg.append(s('line', { x1: 0, x2: W, y1: H, y2: H, stroke: 'var(--axis)', 'stroke-width': 1 }));
  if (n === 0) {
    svg.append(s('text', { x: 8, y: H - 8, 'font-size': 12, fill: 'var(--text-muted)' }, tr('⊤（空の worm）', '⊤ (the empty worm)')));
    container.append(svg);
    return;
  }
  // 棒の幅は 40px まで（短い worm で棒が太くなりすぎないように）
  const slot = Math.min(42, W / n);
  const gap = slot >= 6 ? 2 : 0;
  const bw = Math.max(1, slot - gap);
  const top = Math.max(1, maxValue);
  const unit = (H - 10) / (top + 1); // 値 1 あたりの高さ（ブロック 1 個）
  const blocky = bw >= 6 && unit >= 6; // ブロックに分けて描けるか
  const g = s('g', { fill: 'var(--series-1)' });
  // 光らせるのは棒が少ないときだけ（多いと重い）
  if (n <= 200) g.setAttribute('style', 'filter: drop-shadow(0 0 3px rgba(57, 255, 20, 0.55))');
  values.forEach((v, i) => {
    const x = i * slot;
    if (blocky) {
      for (let k = 0; k <= v; k++) {
        const y = H - (k + 1) * unit;
        g.append(s('rect', { x, y: y + 1, width: bw, height: unit - 2 }));
      }
    } else {
      const bh = (v + 1) * unit;
      g.append(s('rect', { x, y: H - bh, width: bw, height: bh }));
    }
  });
  svg.append(g);
  // 頭（先頭の棒）の顔
  drawFace(svg, 0, bw, values[0], unit, blocky, H);
  // ツールチップ（棒より広い当たり判定：x 座標から一番近い棒）
  const hit = s('rect', { x: 0, y: 0, width: W, height: H, fill: 'transparent' });
  hit.addEventListener('mousemove', (e) => {
    const rect = svg.getBoundingClientRect();
    const px = ((e.clientX - rect.left) / rect.width) * W;
    const i = Math.min(n - 1, Math.max(0, Math.floor(px / slot)));
    showTip(tr(`${i + 1} 文字目：${labels[i]}`, `letter ${i + 1}: ${labels[i]}`), e.clientX, e.clientY);
  });
  hit.addEventListener('mouseleave', hideTip);
  svg.append(hit);
  svg.append(
    s('text', { x: 0, y: H + 16, 'font-size': 11, fill: 'var(--text-muted)' }, tr('← 先頭（外側）', '← head (outermost)')),
    // 右の「n 文字」は、左の「← 先頭」と重ならない位置まで右に置く（英語の方が幅を取る）
    s('text', { x: Math.min(W, Math.max(n * slot, lang() === 'en' ? 200 : 120)), y: H + 16, 'font-size': 11, fill: 'var(--text-muted)', 'text-anchor': 'end' }, tr(`${n} 文字`, `${n} letters`)),
  );
  container.append(svg);
}

/** 括弧の対：文字の位置 [start, end]、深さ（いちばん外側の文字が 1）、どの外側の文字に入っているか。 */
interface Pair {
  start: number;
  end: number;
  depth: number;
  letter: number;
}

/** 括弧語の文字列から、括弧の対を全部取り出す（括弧以外の文字は無視する）。 */
function bracketPairs(t: string): Pair[] {
  const out: Pair[] = [];
  const open: number[] = [];
  let letter = -1;
  for (let i = 0; i < t.length; i++) {
    if (t[i] === '(') {
      if (open.length === 0) letter++; // いちばん外側の対が始まる＝次の文字
      open.push(i);
    } else {
      const start = open.pop();
      if (start === undefined) break; // 対応しない閉じ括弧（来ないはず）
      out.push({ start, end: i, depth: open.length + 1, letter });
    }
  }
  return out;
}

/** 括弧語の入れ子の深さ（battle の全ステップで縦の目盛りをそろえるのに使う）。 */
export function bracketDepth(text: string): number {
  let d = 0;
  let max = 0;
  for (const c of text) {
    if (c === '(') max = Math.max(max, ++d);
    else if (c === ')') d--;
  }
  return max;
}

/**
 * 括弧語を入れ子のブロックで描く：括弧の対 1 つがブロック 1 つで、その対の範囲の幅を持ち、
 * 入れ子の深さの段に置く（下の段がいちばん外側の文字 a₁, a₂, …、上ほど内側）。左が先頭。
 * 色で battle の次の 1 ステップを示す：黄 = 先頭の文字 a₁（a₁{n} に縮む。a₁ = () なら消える）、
 * 水色 = a₁ と一緒に n+1 回複製される文字 a₂…a_{ℓ−1}（ℓ は a₁ より小さい最初の文字）、緑 = 残り。
 * `labels` は外側の文字ごとの順序数、`ranks` はその大小の順位（ℓ を決めるのに使う）。
 * `maxDepth` は縦の目盛り（全ステップの最大の深さ）。
 */
export function nest(container: HTMLElement, text: string, labels: string[], ranks: number[], maxDepth: number): void {
  container.replaceChildren();
  const W = Math.max(320, Math.min(1060, container.clientWidth || 1060));
  const H = 150;
  const t = text.replace(/[^()]/g, '');
  const svg = s('svg', { width: W, height: H + 24, viewBox: `0 0 ${W} ${H + 24}`, role: 'img' });
  svg.append(s('line', { x1: 0, x2: W, y1: H, y2: H, stroke: 'var(--axis)', 'stroke-width': 1 }));
  if (!t) {
    svg.append(
      s('text', { x: 8, y: H - 8, 'font-size': 12, fill: 'var(--text-muted)' }, tr('⊤（空の括弧語）', '⊤ (the empty bracket word)')),
    );
    container.append(svg);
    return;
  }
  const n = t.length;
  const ps = bracketPairs(t);
  const k = ps.reduce((m, p) => Math.max(m, p.letter + 1), 0); // 外側の文字の数
  const depth = Math.max(1, maxDepth, bracketDepth(t));
  const unit = Math.min(14, W / n); // 括弧 1 つあたりの幅
  const rowH = Math.min(36, (H - 6) / depth); // 1 段の高さ
  const gapY = rowH >= 6 ? 2 : rowH >= 3 ? 1 : 0;
  const gapX = unit >= 3 ? 2 : unit >= 1 ? 1 : 0;

  // 次のステップで何が起きるか：a₁ = () なら消えるだけ。そうでなければ a₁ より小さい最初の文字 ℓ まで複製
  const vanish = t.startsWith('()');
  let l = 1;
  if (!vanish) {
    const p = ranks.findIndex((r, i) => i > 0 && r < ranks[0]);
    l = p < 0 ? k : p;
  }
  const role = (letter: number) => (letter === 0 ? 'head' : letter < l ? 'copy' : 'rest');
  const FILL = { head: 'var(--accent)', copy: 'var(--series-3)', rest: 'var(--series-1)' } as const;

  const g = s('g', {});
  if (ps.length <= 200) g.setAttribute('style', 'filter: drop-shadow(0 0 3px rgba(57, 255, 20, 0.45))');
  const yOf = (d: number) => H - d * rowH;
  if (unit * 2 >= 2) {
    // 対ごとに 1 つのブロック。隣の外側の文字と見分けられるよう、1 つおきに少し暗くする
    for (const p of ps) {
      const r = role(p.letter);
      g.append(
        s('rect', {
          x: p.start * unit + gapX / 2,
          y: yOf(p.depth) + gapY / 2,
          width: Math.max(0.5, (p.end - p.start + 1) * unit - gapX),
          height: rowH - gapY,
          fill: FILL[r],
          'fill-opacity': r !== 'head' && p.letter % 2 === 1 ? 0.7 : 1,
        }),
      );
    }
  } else {
    // 語が長くて対の幅が 2px 未満：同じ段・同じ色で 1px 未満の隙間しかない対はまとめて描く（数千個の細い四角を避ける）
    const runs = new Map<string, [number, number][]>();
    for (const p of ps) {
      const key = `${p.depth}:${role(p.letter)}`;
      const x0 = p.start * unit;
      const x1 = (p.end + 1) * unit;
      const list = runs.get(key) ?? [];
      const last = list[list.length - 1];
      if (last && x0 - last[1] < 1) last[1] = Math.max(last[1], x1);
      else list.push([x0, x1]);
      runs.set(key, list);
    }
    // 緑 → 水色 → 黄の順に描き、細くなった先頭の文字が隣に隠れないよう最低 3px（複製される部分は 2px）にする
    const MIN = { rest: 1, copy: 2, head: 3 } as const;
    const order = (key: string) => ['rest', 'copy', 'head'].indexOf(key.split(':')[1]);
    for (const [key, list] of [...runs].sort((a, b) => order(a[0]) - order(b[0]))) {
      const [d, r] = key.split(':') as [string, keyof typeof FILL];
      for (const [x0, x1] of list) {
        g.append(
          s('rect', { x: x0, y: yOf(Number(d)) + gapY / 2, width: Math.max(MIN[r], x1 - x0), height: rowH - gapY, fill: FILL[r] }),
        );
      }
    }
  }
  svg.append(g);

  // ツールチップ：x 座標から、その位置の外側の文字
  const letterAt = new Int32Array(n).fill(-1);
  const letterDepth = new Array<number>(k).fill(0);
  for (const p of ps) {
    if (p.depth === 1) letterAt.fill(p.letter, p.start, p.end + 1);
    letterDepth[p.letter] = Math.max(letterDepth[p.letter], p.depth);
  }
  const hit = s('rect', { x: 0, y: 0, width: W, height: H, fill: 'transparent' });
  hit.addEventListener('mousemove', (e) => {
    const rect = svg.getBoundingClientRect();
    const px = ((e.clientX - rect.left) / rect.width) * W;
    const i = letterAt[Math.min(n - 1, Math.max(0, Math.floor(px / unit)))];
    if (i < 0) return hideTip();
    const note =
      i === 0
        ? vanish
          ? tr('先頭：次のステップで消える', 'head: vanishes in the next step')
          : tr('先頭：次のステップで縮む', 'head: shrinks in the next step')
        : i < l
          ? tr('先頭と一緒に複製される', 'copied along with the head')
          : '';
    const base = tr(
      `${i + 1} 文字目：${labels[i] ?? ''}（入れ子 ${letterDepth[i]} 段）`,
      `letter ${i + 1}: ${labels[i] ?? ''} (nesting ${letterDepth[i]})`,
    );
    showTip(note ? `${base}${tr('、', ', ')}${note}` : base, e.clientX, e.clientY);
  });
  hit.addEventListener('mouseleave', hideTip);
  svg.append(hit);
  svg.append(
    s('text', { x: 0, y: H + 16, 'font-size': 11, fill: 'var(--text-muted)' }, tr('← 先頭（外側）', '← head (outermost)')),
    s(
      'text',
      { x: Math.min(W, Math.max(n * unit, lang() === 'en' ? 260 : 220)), y: H + 16, 'font-size': 11, fill: 'var(--text-muted)', 'text-anchor': 'end' },
      tr(`${k} 文字・深さ ${bracketDepth(t)}`, `${k} letters, depth ${bracketDepth(t)}`),
    ),
  );

  // 凡例（色の見本つき）
  const swatch = (color: string) => h('span', { style: `color:${color}` }, '■ ');
  const legend = h(
    'div',
    { class: 'muted', style: 'font-size:12px;margin-bottom:4px;display:flex;flex-wrap:wrap;gap:2px 14px' },
    h('span', {}, tr('括弧の対 1 つ = ブロック 1 つ（下の段が外側の文字、上ほど内側）', 'One block per bracket pair (outer letters on the bottom row, inner pairs above)')),
    h('span', {}, swatch('var(--accent)'), tr('先頭の文字 a₁（次のステップで縮む。() なら消える）', 'head letter a₁ (shrinks next step; vanishes if it is ())')),
    h('span', {}, swatch('var(--series-3)'), tr('a₁ と一緒に複製される文字', 'letters copied along with a₁')),
    h('span', {}, swatch('var(--series-1)'), tr('残りの文字', 'the remaining letters')),
  );
  container.append(legend, svg);
}


/**
 * worm の頭（先頭の棒、左端 x0・幅 bw・値 v0）に顔を描く：目、太くなれば赤い口も（ロゴの worm と同じ色）。
 * 棒が細すぎれば何もしない。
 */
function drawFace(svg: SVGSVGElement, x0: number, bw: number, v0: number, unit: number, blocky: boolean, H: number): void {
  if (bw < 10) return;
  const yTop = H - (v0 + 1) * unit + (blocky ? 1 : 0);
  const room = blocky ? unit - 2 : (v0 + 1) * unit; // 顔を描ける高さ（いちばん上のブロック）
  const e = Math.max(3, Math.round(bw / 7)); // 目の大きさ
  const ey = yTop + Math.max(2, Math.round(e * 0.8));
  const lx = x0 + Math.round(bw * 0.22);
  const rx = x0 + Math.round(bw * 0.78) - e;
  svg.append(
    s('rect', { x: lx, y: ey, width: e, height: e, fill: '#000' }),
    s('rect', { x: rx, y: ey, width: e, height: e, fill: '#000' }),
  );
  const u = Math.max(1, Math.round(e / 3)); // 口のドット 1 つ
  const my = ey + e + u;
  if (bw >= 14 && my + 2 * u + 1 <= yTop + room) {
    const mx = lx + e;
    const w = Math.max(3 * u, rx - mx);
    // にっこりした口：両端が 1 ドット上がった赤い線
    svg.append(
      s('rect', { x: mx + u, y: my + u, width: w - 2 * u, height: u + 1, fill: 'var(--worm-mouth)' }),
      s('rect', { x: mx, y: my, width: u, height: u + 1, fill: 'var(--worm-mouth)' }),
      s('rect', { x: mx + w - u, y: my, width: u, height: u + 1, fill: 'var(--worm-mouth)' }),
    );
  }
}

/** 括弧語の文字（いちばん外側の括弧の対 1 つ）：括弧語の書き方 t と、その o*。 */
export interface BLetter {
  t: string;
  o: string;
}
/** 括弧語のまとめた形：文字か、中身の k 回の繰り返し。 */
export type BNode = BLetter | { r: BNode[]; k: number };
/** 括弧語を次のステップでの役割ごとに分けてまとめた形（wasm の battle_compact の parts）。 */
export interface BracketParts {
  vanish: boolean;
  head: BLetter | null;
  copy: BNode[];
  rest: BNode[];
}

/**
 * まとめた括弧語を、入れ子のブロック（[`nest`] と同じ描き方）で描く。繰り返しの中身は 1 回分だけ描き、
 * 下に波括弧と ×k を付ける。色は [`nest`] と同じ役割（黄 = 先頭 a₁、水色 = a₁ と一緒に複製される文字、緑 = 残り）で、
 * 3 つの部分は別々にまとめてある（先頭や複製される部分が、後ろの繰り返しに混ざらないように）。
 */
export function nestTree(container: HTMLElement, parts: BracketParts, maxDepth: number, lengthLabel: string): void {
  container.replaceChildren();
  const W = Math.max(320, Math.min(1060, container.clientWidth || 1060));
  const H = 150;
  const BR = 24;
  const GAP = 8;
  type Role = 'head' | 'copy' | 'rest';
  const items: { letter: BLetter; role: Role; gap: boolean; mult: number }[] = [];
  const braces: Brace[] = [];
  let gapNext = false;
  const walk = (ns: BNode[], role: Role, mult: number): number => {
    let deepest = 0;
    for (const nd of ns) {
      if ('t' in nd) {
        items.push({ letter: nd, role, gap: gapNext, mult });
        gapNext = false;
      } else {
        if (items.length > 0) gapNext = true;
        const from = items.length;
        const level = walk(nd.r, role, mult * nd.k) + 1;
        if (items.length > from) braces.push({ from, to: items.length - 1, k: nd.k, level });
        deepest = Math.max(deepest, level);
        gapNext = true;
      }
    }
    return deepest;
  };
  let maxLevel = 0;
  if (parts.head) maxLevel = walk([parts.head], 'head', 1);
  gapNext = items.length > 0;
  maxLevel = Math.max(maxLevel, walk(parts.copy, 'copy', 1));
  gapNext = items.length > 0;
  maxLevel = Math.max(maxLevel, walk(parts.rest, 'rest', 1));
  const n = items.length;
  const bottom = H + 6 + maxLevel * BR;
  const svgH = bottom + 20;
  // 括弧 1 つあたりの幅：全体が入れば広く（14px まで）、入らなければ 3px にして横にスクロール
  const chars = items.reduce((m, it) => m + it.letter.t.length, 0);
  const gaps = items.filter((it) => it.gap).length;
  const unit = Math.max(3, Math.min(14, (W - gaps * GAP) / Math.max(1, chars)));
  const total = chars * unit + gaps * GAP;
  const SW = Math.max(W, Math.ceil(total));
  const svg = s('svg', { width: SW, height: svgH, viewBox: `0 0 ${SW} ${svgH}`, role: 'img', class: SW > W ? 'wide' : undefined });
  svg.append(s('line', { x1: 0, x2: SW, y1: H, y2: H, stroke: 'var(--axis)', 'stroke-width': 1 }));
  if (n === 0) {
    svg.append(s('text', { x: 8, y: H - 8, 'font-size': 12, fill: 'var(--text-muted)' }, tr('⊤（空の括弧語）', '⊤ (the empty bracket word)')));
    container.append(svg);
    return;
  }
  const depth = Math.max(1, maxDepth, ...items.map((it) => bracketDepth(it.letter.t)));
  const rowH = Math.min(36, (H - 6) / depth);
  const gapY = rowH >= 6 ? 2 : rowH >= 3 ? 1 : 0;
  const gapX = unit >= 3 ? 2 : 1;
  const FILL = { head: 'var(--accent)', copy: 'var(--series-3)', rest: 'var(--series-1)' } as const;
  const xs: number[] = [];
  const ws: number[] = [];
  let x = 0;
  for (const it of items) {
    if (it.gap) x += GAP;
    xs.push(x);
    ws.push(it.letter.t.length * unit);
    x += it.letter.t.length * unit;
  }
  const g = s('g', {});
  if (n <= 200) g.setAttribute('style', 'filter: drop-shadow(0 0 3px rgba(57, 255, 20, 0.45))');
  items.forEach((it, i) => {
    for (const p of bracketPairs(it.letter.t)) {
      g.append(
        s('rect', {
          x: xs[i] + p.start * unit + gapX / 2,
          y: H - p.depth * rowH + gapY / 2,
          width: Math.max(0.5, (p.end - p.start + 1) * unit - gapX),
          height: rowH - gapY,
          fill: FILL[it.role],
          // 隣の文字と見分けられるよう、1 つおきに少し暗くする
          'fill-opacity': it.role !== 'head' && i % 2 === 1 ? 0.7 : 1,
        }),
      );
    }
  });
  svg.append(g);
  drawBraces(svg, braces, (i) => xs[i], (i) => xs[i] + ws[i], H, BR, SW, svgH, (b) =>
    tr(`この括弧の中（${b.to - b.from + 1} 文字）を ${fmtCount(b.k)} 回くり返す`, `the ${b.to - b.from + 1} letters above this brace, repeated ${fmtCount(b.k)} times`),
  );

  // ツールチップ：その文字の o*、役割、広げると何回出てくるか
  const hit = s('rect', { x: 0, y: 0, width: SW, height: H, fill: 'transparent' });
  hit.addEventListener('mousemove', (e) => {
    const rect = svg.getBoundingClientRect();
    const px = ((e.clientX - rect.left) / rect.width) * SW;
    let i = 0;
    while (i + 1 < n && xs[i + 1] <= px) i++;
    const it = items[i];
    const base = tr(
      `まとめた形の ${i + 1} 番目の文字：${it.letter.o}（入れ子 ${bracketDepth(it.letter.t)} 段）`,
      `letter ${i + 1} of the compressed form: ${it.letter.o} (nesting ${bracketDepth(it.letter.t)})`,
    );
    const note =
      it.role === 'head'
        ? parts.vanish
          ? tr('、先頭：次のステップで消える', ', head: vanishes in the next step')
          : tr('、先頭：次のステップで縮む', ', head: shrinks in the next step')
        : it.role === 'copy'
          ? tr('、先頭と一緒に複製される', ', copied along with the head')
          : '';
    const times = it.mult > 1 ? tr(`（広げると ${fmtCount(it.mult)} 回出てくる）`, ` (appears ${fmtCount(it.mult)} times when expanded)`) : '';
    showTip(base + note + times, e.clientX, e.clientY);
  });
  hit.addEventListener('mouseleave', hideTip);
  svg.append(hit);
  svg.append(
    s('text', { x: 0, y: bottom + 14, 'font-size': 11, fill: 'var(--text-muted)' }, tr('← 先頭（外側）', '← head (outermost)')),
    s('text', { x: Math.min(W, container.clientWidth || W) - 4, y: bottom + 14, 'font-size': 11, fill: 'var(--text-muted)', 'text-anchor': 'end' }, lengthLabel),
  );

  // 凡例（色の見本つき）
  const swatch = (color: string) => h('span', { style: `color:${color}` }, '■ ');
  const legend = h(
    'div',
    { class: 'muted', style: 'font-size:12px;margin-bottom:4px;display:flex;flex-wrap:wrap;gap:2px 14px' },
    h('span', {}, tr('括弧の対 1 つ = ブロック 1 つ（下の段が外側の文字、上ほど内側）', 'One block per bracket pair (outer letters on the bottom row, inner pairs above)')),
    h('span', {}, swatch('var(--accent)'), tr('先頭の文字 a₁（次のステップで縮む。() なら消える）', 'head letter a₁ (shrinks next step; vanishes if it is ())')),
    h('span', {}, swatch('var(--series-3)'), tr('a₁ と一緒に複製される文字', 'letters copied along with a₁')),
    h('span', {}, swatch('var(--series-1)'), tr('残りの文字', 'the remaining letters')),
    h('span', { style: 'color:var(--accent)' }, tr('波括弧 ×k：上の文字の並びを k 回くり返す', 'brace ×k: the letters above it, repeated k times')),
  );
  container.append(legend, SW > W ? h('div', { class: 'scroll-x' }, svg) : svg);
}

/** 大きな数を読みやすく：12 桁までは 1,234,567、それより長ければ 1.23×10^40。 */
export function fmtCount(x: number | string): string {
  const t = typeof x === 'string' ? x : Number.isFinite(x) && x < 1e15 ? String(Math.round(x)) : x.toExponential(2).replace('e+', '×10^');
  if (!/^\d+$/.test(t)) return t;
  if (t.length <= 12) return Number(t).toLocaleString('en-US');
  return `${t[0]}.${t.slice(1, 3)}×10^${t.length - 1}`;
}

/** 棒（値 v、左端 x、幅 bw）を描く：ブロックを積んだ形か、ただの棒。 */
function drawBar(g: SVGGElement, x: number, bw: number, v: number, unit: number, blocky: boolean, H: number): void {
  if (blocky) {
    for (let k = 0; k <= v; k++) {
      const y = H - (k + 1) * unit;
      g.append(s('rect', { x, y: y + 1, width: bw, height: unit - 2 }));
    }
  } else {
    const bh = (v + 1) * unit;
    g.append(s('rect', { x, y: H - bh, width: bw, height: bh }));
  }
}

/** 繰り返しの波括弧：from 番目から to 番目までの項目を k 回くり返す（level は下から何段目か。内側ほど 1 に近い）。 */
interface Brace {
  from: number;
  to: number;
  k: number;
  level: number;
}

/**
 * 棒やブロックの下（y = H から）に、繰り返しの波括弧と回数 ×k を描く。項目 i の左端・右端は left(i)・right(i)。
 * 回数の文字が同じ段の隣と重なるなら書かず、括弧にカーソルを重ねたときのツールチップ（`tip`）で見せる。
 */
function drawBraces(
  svg: SVGSVGElement,
  braces: Brace[],
  left: (i: number) => number,
  right: (i: number) => number,
  H: number,
  BR: number,
  SW: number,
  svgH: number,
  tip: (b: Brace) => string,
): void {
  const bg = s('g', { fill: 'none', stroke: 'var(--accent)', 'stroke-width': 1.5 });
  const lastRight = new Map<number, number>();
  const placed = [...braces].sort((a, b) => left(a.from) - left(b.from));
  for (const b of placed) {
    const xa = left(b.from);
    const xb = right(b.to);
    const y = H + 6 + (b.level - 1) * BR;
    const d = Math.min(5, (xb - xa) / 4);
    const mid = (xa + xb) / 2;
    bg.append(
      s('path', {
        d: `M ${xa} ${y} Q ${xa} ${y + d} ${xa + d} ${y + d} L ${mid - d} ${y + d} Q ${mid} ${y + d} ${mid} ${y + 2 * d} Q ${mid} ${y + d} ${mid + d} ${y + d} L ${xb - d} ${y + d} Q ${xb} ${y + d} ${xb} ${y}`,
      }),
    );
    const label = `×${fmtCount(b.k)}`;
    const lw = 6.6 * label.length;
    const lx = Math.min(SW - lw / 2, Math.max(lw / 2, mid));
    if (lx - lw / 2 >= (lastRight.get(b.level) ?? -Infinity) + 3) {
      svg.append(s('text', { x: lx, y: y + 2 * d + 11, 'font-size': 11, fill: 'var(--accent)', 'text-anchor': 'middle' }, label));
      lastRight.set(b.level, lx + lw / 2);
    }
  }
  svg.append(bg);
  const maxLevel = braces.reduce((m, b) => Math.max(m, b.level), 0);
  const hitB = s('rect', { x: 0, y: H, width: SW, height: 6 + maxLevel * BR, fill: 'transparent' });
  hitB.addEventListener('mousemove', (e) => {
    const rect = svg.getBoundingClientRect();
    const px = ((e.clientX - rect.left) / rect.width) * SW;
    const py = ((e.clientY - rect.top) / rect.height) * svgH;
    const level = Math.floor((py - H - 6) / BR) + 1;
    const b = braces.find((b) => b.level === level && left(b.from) <= px && px <= right(b.to));
    if (!b) return hideTip();
    showTip(tip(b), e.clientX, e.clientY);
  });
  hitB.addEventListener('mouseleave', hideTip);
  svg.append(hitB);
}

/** worm のまとめた形：文字は数、繰り返しは { r: 中身, k: 回数 }（wasm の battle_worm_view の tree）。 */
export type WormNode = number | { r: WormNode[]; k: number };

/**
 * まとめた worm を棒で描く：繰り返しの中身は 1 回分だけ描き、その下に波括弧（underbrace）と回数 ×k を付ける。
 * 入れ子の繰り返しは括弧も入れ子にし、内側の括弧ほど棒の近くに置く。棒の高さ・ブロック・頭の顔は [`bars`] と同じ。
 * `lengthLabel` は右下に書く長さ、`truncated` ならまとめた形が長すぎて先頭だけ（最後に … を付ける）。
 */
export function wormTree(container: HTMLElement, nodes: WormNode[], maxValue: number, lengthLabel: string, truncated: boolean): void {
  container.replaceChildren();
  const W = Math.max(320, Math.min(1060, container.clientWidth || 1060));
  const H = 150;
  const BR = 24; // 括弧 1 段の高さ（括弧と回数）
  const GAP = 6; // 繰り返しの前後にあける間

  // 並べる：棒（値・前の間・広げたときに何回出てくるか）と括弧（どの棒からどの棒まで・回数・段）
  const items: { v: number; gap: boolean; mult: number }[] = [];
  const braces: Brace[] = [];
  let gapNext = false;
  const walk = (ns: WormNode[], mult: number): number => {
    let deepest = 0;
    for (const nd of ns) {
      if (typeof nd === 'number') {
        items.push({ v: nd, gap: gapNext, mult });
        gapNext = false;
      } else {
        if (items.length > 0) gapNext = true;
        const from = items.length;
        const level = walk(nd.r, mult * nd.k) + 1;
        if (items.length > from) braces.push({ from, to: items.length - 1, k: nd.k, level });
        deepest = Math.max(deepest, level);
        gapNext = true;
      }
    }
    return deepest;
  };
  const maxLevel = walk(nodes, 1);
  const n = items.length;
  const bottom = H + 6 + maxLevel * BR; // 括弧の下
  const svgH = bottom + 20;
  const gaps = items.filter((it) => it.gap).length;
  const room = W - gaps * GAP - (truncated ? 24 : 0);
  // 棒は 10px 以上の幅で描く（入りきらなければ横にスクロールする）
  const slot = Math.max(10, Math.min(42, room / Math.max(1, n)));
  const total = n * slot + gaps * GAP + (truncated ? 24 : 0);
  const SW = Math.max(W, Math.ceil(total));
  const svg = s('svg', { width: SW, height: svgH, viewBox: `0 0 ${SW} ${svgH}`, role: 'img', class: SW > W ? 'wide' : undefined });
  svg.append(s('line', { x1: 0, x2: SW, y1: H, y2: H, stroke: 'var(--axis)', 'stroke-width': 1 }));
  if (n === 0) {
    svg.append(s('text', { x: 8, y: H - 8, 'font-size': 12, fill: 'var(--text-muted)' }, tr('⊤（空の worm）', '⊤ (the empty worm)')));
    container.append(svg);
    return;
  }
  const gap = slot >= 6 ? 2 : 0;
  const bw = Math.max(1, slot - gap);
  const top = Math.max(1, maxValue);
  const unit = (H - 10) / (top + 1);
  const blocky = bw >= 6 && unit >= 6;
  const xs: number[] = [];
  let x = 0;
  for (const it of items) {
    if (it.gap) x += GAP;
    xs.push(x);
    x += slot;
  }
  const g = s('g', { fill: 'var(--series-1)' });
  if (n <= 200) g.setAttribute('style', 'filter: drop-shadow(0 0 3px rgba(57, 255, 20, 0.55))');
  items.forEach((it, i) => drawBar(g, xs[i], bw, it.v, unit, blocky, H));
  svg.append(g);
  drawFace(svg, 0, bw, items[0].v, unit, blocky, H);
  if (truncated) {
    svg.append(s('text', { x: x + 4, y: H - 6, 'font-size': 16, fill: 'var(--text-muted)' }, '…'));
  }

  drawBraces(svg, braces, (i) => xs[i], (i) => xs[i] + bw, H, BR, SW, svgH, (b) =>
    tr(`この括弧の中（${b.to - b.from + 1} 文字）を ${fmtCount(b.k)} 回くり返す`, `the ${b.to - b.from + 1} letters above this brace, repeated ${fmtCount(b.k)} times`),
  );

  // ツールチップ：その文字が、繰り返しを広げると何回出てくるか
  const hit = s('rect', { x: 0, y: 0, width: SW, height: H, fill: 'transparent' });
  hit.addEventListener('mousemove', (e) => {
    const rect = svg.getBoundingClientRect();
    const px = ((e.clientX - rect.left) / rect.width) * SW;
    let i = 0;
    while (i + 1 < n && xs[i + 1] <= px) i++;
    const it = items[i];
    const where = tr(`まとめた形の ${i + 1} 番目の文字：${it.v}`, `letter ${i + 1} of the compressed form: ${it.v}`);
    const times = it.mult > 1 ? tr(`（広げると ${fmtCount(it.mult)} 回出てくる）`, ` (appears ${fmtCount(it.mult)} times when expanded)`) : '';
    showTip(where + times, e.clientX, e.clientY);
  });
  hit.addEventListener('mouseleave', hideTip);
  svg.append(hit);
  svg.append(
    s('text', { x: 0, y: bottom + 14, 'font-size': 11, fill: 'var(--text-muted)' }, tr('← 先頭（外側）', '← head (outermost)')),
    // 長さは見えている幅の右端に（図が横にスクロールするときも、最初に見える所に）
    s('text', { x: Math.min(W, container.clientWidth || W) - 4, y: bottom + 14, 'font-size': 11, fill: 'var(--text-muted)', 'text-anchor': 'end' }, lengthLabel),
  );
  // 幅が足りなければ横にスクロールする
  container.append(SW > W ? h('div', { class: 'scroll-x' }, svg) : svg);
}

/** 長さの推移の折れ線（現在のステップに印）。長さが 100 万を超えたら縦軸を対数にする。 */
export function lengthChart(container: HTMLElement, lengths: number[], current: number, onPick: (i: number) => void): void {
  container.replaceChildren();
  const W = Math.max(320, Math.min(1060, container.clientWidth || 1060));
  const H = 120;
  const pad = { l: 44, r: 10, t: 10, b: 22 };
  const n = lengths.length;
  const maxL = Math.max(1, ...lengths);
  const log = maxL > 1e6;
  const f = (v: number) => (log ? Math.log10(1 + v) : v);
  const xs = (i: number) => pad.l + (n <= 1 ? 0 : (i / (n - 1)) * (W - pad.l - pad.r));
  const ys = (v: number) => pad.t + (1 - f(v) / f(maxL)) * (H - pad.t - pad.b);
  const svg = s('svg', { width: W, height: H, viewBox: `0 0 ${W} ${H}`, role: 'img' });
  // 目盛り（0 と最大）
  for (const v of [0, maxL]) {
    svg.append(
      s('line', { x1: pad.l, x2: W - pad.r, y1: ys(v), y2: ys(v), stroke: 'var(--grid)', 'stroke-width': 1 }),
      s('text', { x: pad.l - 6, y: ys(v) + 4, 'font-size': 11, fill: 'var(--text-muted)', 'text-anchor': 'end' }, fmtCount(v)),
    );
  }
  svg.append(
    s('text', { x: pad.l, y: H - 4, 'font-size': 11, fill: 'var(--text-muted)' }, tr('ステップ 0', 'step 0')),
    s('text', { x: W - pad.r, y: H - 4, 'font-size': 11, fill: 'var(--text-muted)', 'text-anchor': 'end' }, `${n - 1}`),
  );
  const d = lengths.map((v, i) => `${i ? 'L' : 'M'} ${xs(i)} ${ys(v)}`).join(' ');
  svg.append(
    s('path', {
      d,
      fill: 'none',
      stroke: 'var(--series-1)',
      'stroke-width': 2,
      style: 'filter: drop-shadow(0 0 3px rgba(57, 255, 20, 0.6))',
    }),
  );
  const cross = s('line', { y1: pad.t, y2: H - pad.b, stroke: 'var(--axis)', 'stroke-width': 1, visibility: 'hidden' });
  svg.append(cross);
  svg.append(
    s('circle', { cx: xs(current), cy: ys(lengths[current] ?? 0), r: 6, fill: 'var(--accent)', stroke: '#000', 'stroke-width': 2 }),
  );
  const hit = s('rect', { x: pad.l, y: 0, width: W - pad.l - pad.r, height: H, fill: 'transparent', style: 'cursor:pointer' });
  const pick = (e: MouseEvent) => {
    const rect = svg.getBoundingClientRect();
    const px = ((e.clientX - rect.left) / rect.width) * W;
    return Math.min(n - 1, Math.max(0, Math.round(((px - pad.l) / (W - pad.l - pad.r)) * (n - 1))));
  };
  hit.addEventListener('mousemove', (e) => {
    const i = pick(e);
    cross.setAttribute('x1', String(xs(i)));
    cross.setAttribute('x2', String(xs(i)));
    cross.setAttribute('visibility', 'visible');
    showTip(tr(`ステップ ${i}：長さ ${fmtCount(lengths[i])}`, `step ${i}: length ${fmtCount(lengths[i])}`), e.clientX, e.clientY);
  });
  hit.addEventListener('mouseleave', () => {
    cross.setAttribute('visibility', 'hidden');
    hideTip();
  });
  hit.addEventListener('click', (e) => onPick(pick(e)));
  svg.append(hit);
  container.append(h('div', { class: 'muted', style: 'font-size:12px' }, log
        ? tr('長さの推移（縦は対数。クリックでそのステップへ）', 'Length over time (log scale; click to jump to that step)')
        : tr('長さの推移（クリックでそのステップへ）', 'Length over time (click to jump to that step)')), svg);
}
