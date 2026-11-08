// battle の表示に使う小さなグラフ：worm の棒グラフと、長さの推移の折れ線。

import { h, hideTip, s, showTip } from './dom';

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
    svg.append(s('text', { x: 8, y: H - 8, 'font-size': 12, fill: 'var(--text-muted)' }, '⊤（空の worm）'));
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
  // 頭（先頭の棒）の顔：目、太くなれば赤い口も（ロゴの worm と同じ色）
  const v0 = values[0];
  if (bw >= 10) {
    const yTop = H - (v0 + 1) * unit + (blocky ? 1 : 0);
    const room = blocky ? unit - 2 : (v0 + 1) * unit; // 顔を描ける高さ（いちばん上のブロック）
    const e = Math.max(3, Math.round(bw / 7)); // 目の大きさ
    const ey = yTop + Math.max(2, Math.round(e * 0.8));
    const lx = Math.round(bw * 0.22);
    const rx = Math.round(bw * 0.78) - e;
    svg.append(
      s('rect', { x: lx, y: ey, width: e, height: e, fill: '#000' }),
      s('rect', { x: rx, y: ey, width: e, height: e, fill: '#000' }),
    );
    const u = Math.max(1, Math.round(e / 3)); // 口のドット 1 つ
    const my = ey + e + u;
    if (bw >= 14 && my + 2 * u + 1 <= yTop + room) {
      const x0 = lx + e;
      const w = Math.max(3 * u, rx - x0);
      // にっこりした口：両端が 1 ドット上がった赤い線
      svg.append(
        s('rect', { x: x0 + u, y: my + u, width: w - 2 * u, height: u + 1, fill: 'var(--worm-mouth)' }),
        s('rect', { x: x0, y: my, width: u, height: u + 1, fill: 'var(--worm-mouth)' }),
        s('rect', { x: x0 + w - u, y: my, width: u, height: u + 1, fill: 'var(--worm-mouth)' }),
      );
    }
  }
  // ツールチップ（棒より広い当たり判定：x 座標から一番近い棒）
  const hit = s('rect', { x: 0, y: 0, width: W, height: H, fill: 'transparent' });
  hit.addEventListener('mousemove', (e) => {
    const rect = svg.getBoundingClientRect();
    const px = ((e.clientX - rect.left) / rect.width) * W;
    const i = Math.min(n - 1, Math.max(0, Math.floor(px / slot)));
    showTip(`${i + 1} 文字目：${labels[i]}`, e.clientX, e.clientY);
  });
  hit.addEventListener('mouseleave', hideTip);
  svg.append(hit);
  svg.append(
    s('text', { x: 0, y: H + 16, 'font-size': 11, fill: 'var(--text-muted)' }, '← 先頭（外側）'),
    s('text', { x: Math.max(n * slot, 120), y: H + 16, 'font-size': 11, fill: 'var(--text-muted)', 'text-anchor': 'end' }, `${n} 文字`),
  );
  container.append(svg);
}

/** 長さの推移の折れ線（現在のステップに印）。 */
export function lengthChart(container: HTMLElement, lengths: number[], current: number, onPick: (i: number) => void): void {
  container.replaceChildren();
  const W = Math.max(320, Math.min(1060, container.clientWidth || 1060));
  const H = 120;
  const pad = { l: 44, r: 10, t: 10, b: 22 };
  const n = lengths.length;
  const maxL = Math.max(1, ...lengths);
  const xs = (i: number) => pad.l + (n <= 1 ? 0 : (i / (n - 1)) * (W - pad.l - pad.r));
  const ys = (v: number) => pad.t + (1 - v / maxL) * (H - pad.t - pad.b);
  const svg = s('svg', { width: W, height: H, viewBox: `0 0 ${W} ${H}`, role: 'img' });
  // 目盛り（0 と最大）
  for (const v of [0, maxL]) {
    svg.append(
      s('line', { x1: pad.l, x2: W - pad.r, y1: ys(v), y2: ys(v), stroke: 'var(--grid)', 'stroke-width': 1 }),
      s('text', { x: pad.l - 6, y: ys(v) + 4, 'font-size': 11, fill: 'var(--text-muted)', 'text-anchor': 'end' }, String(v)),
    );
  }
  svg.append(
    s('text', { x: pad.l, y: H - 4, 'font-size': 11, fill: 'var(--text-muted)' }, 'ステップ 0'),
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
    showTip(`ステップ ${i}：長さ ${lengths[i]}`, e.clientX, e.clientY);
  });
  hit.addEventListener('mouseleave', () => {
    cross.setAttribute('visibility', 'hidden');
    hideTip();
  });
  hit.addEventListener('click', (e) => onPick(pick(e)));
  svg.append(hit);
  container.append(h('div', { class: 'muted', style: 'font-size:12px' }, '長さの推移（クリックでそのステップへ）'), svg);
}
