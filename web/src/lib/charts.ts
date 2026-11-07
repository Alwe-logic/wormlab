// battle の表示に使う小さなグラフ：worm の棒グラフと、長さの推移の折れ線。

import { h, hideTip, s, showTip } from './dom';

/**
 * worm を棒の列で描く（左が外側＝先頭の文字）。高さ ∝ 値。
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
  const g = s('g');
  values.forEach((v, i) => {
    const bh = ((v + 1) / (top + 1)) * (H - 10);
    const x = i * slot;
    const r = bw >= 8 ? 4 : 0;
    // 上の角だけ丸めた棒
    const d =
      r > 0
        ? `M ${x} ${H} V ${H - bh + r} Q ${x} ${H - bh} ${x + r} ${H - bh} H ${x + bw - r} Q ${x + bw} ${H - bh} ${x + bw} ${H - bh + r} V ${H} Z`
        : `M ${x} ${H} V ${H - bh} H ${x + bw} V ${H} Z`;
    const p = s('path', { d, fill: 'var(--series-1)' });
    g.append(p);
  });
  svg.append(g);
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
  svg.append(s('path', { d, fill: 'none', stroke: 'var(--series-1)', 'stroke-width': 2 }));
  const cross = s('line', { y1: pad.t, y2: H - pad.b, stroke: 'var(--axis)', 'stroke-width': 1, visibility: 'hidden' });
  svg.append(cross);
  svg.append(
    s('circle', { cx: xs(current), cy: ys(lengths[current] ?? 0), r: 5, fill: 'var(--series-1)', stroke: 'var(--surface-1)', 'stroke-width': 2 }),
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
