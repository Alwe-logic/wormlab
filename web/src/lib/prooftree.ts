// 証明図（gentzen 式の木：前提を上に並べ、線を引き、その下に結論、線の右に規則の名前）を HTML で描く。
//
// 前は bussproofs のコードを MathJax で描いていたが、木が大きくなると規則の名前が隣の部分に
// 重なったり、右端が切れたりした（MathJax の bussproofs は名前の幅を場所として取らない）。
// ここでは各推論を 2 列の grid にして、規則の名前に専用の列を与える。名前の幅のぶん場所が
// 空くので、隣の部分証明とは重ならない。
//
//   ┌──────────────┬─────┐
//   │ 前提 前提 …  │     │
//   ├──────────────┼─────┤
//   │ ──────────── │ 名前 │
//   ├──────────────┼─────┤
//   │    結論      │     │
//   └──────────────┴─────┘
//
// 線の長さは、描いたあとに測って「いちばん左の前提の結論の左端から、いちばん右の前提の結論の
// 右端まで（結論の方が広ければ結論の幅）」にそろえ、名前を線の右端に寄せる（fitLines）。
// 線の長さと名前の移動（transform）は grid の列の幅を変えないので、測り直しは 1 回で済む。
//
// 大きな証明：DAG を木に展開すると巨大になりうるので、最初は決まった数のノードまでを
// 根から幅優先で開き、残りは「⋮」で畳んでおく。⋮ を押すと開き、結論を押すと畳む。

import { h } from './dom';
import { tr } from './i18n';
import type { ProofJson } from './proof';

/** 最初に開くノードの数（目安） */
const INITIAL_BUDGET = 160;
/** ⋮ を 1 回押したときに開くノードの数（目安） */
const EXPAND_BUDGET = 60;

/** 推論 1 つ（前提の要素、規則の名前、結論）を作る。 */
export function inference(opts: {
  premises: HTMLElement[];
  rule: string;
  /** 規則の名前にカーソルを合わせたときの説明 */
  ruleTitle?: string;
  conclusion: string | HTMLElement;
  /** 結論に付けるクラス（副条件の印など） */
  conclusionClass?: string;
  cls?: string;
}): HTMLElement {
  const concl =
    typeof opts.conclusion === 'string' ? h('div', { class: 'pf-concl' }, opts.conclusion) : opts.conclusion;
  concl.classList.add('pf-concl');
  if (opts.conclusionClass) concl.classList.add(...opts.conclusionClass.split(' '));
  return h(
    'div',
    { class: `pf${opts.cls ? ` ${opts.cls}` : ''}` },
    h('div', { class: 'pf-prem' }, ...opts.premises),
    h('div', { class: 'pf-line', 'aria-hidden': 'true' }),
    h('span', { class: 'pf-rule', title: opts.ruleTitle }, opts.rule),
    concl,
  );
}

/** 前提に置く式（推論ではないもの。規則の一覧の図式で使う）。 */
export function formula(text: string, cls?: string): HTMLElement {
  return h('span', { class: `pf-f${cls ? ` ${cls}` : ''}` }, text);
}

/** 要素の直接の子のうち、クラス c を持つもの。 */
function child(el: Element, c: string): HTMLElement | null {
  for (const x of el.children) if (x.classList.contains(c)) return x as HTMLElement;
  return null;
}

/** 前提の欄の 1 つの「結論にあたる部分」（推論ならその結論、式や ⋮ ならそれ自身）。 */
function premiseFace(x: Element): HTMLElement {
  return (x.classList.contains('pf') ? child(x, 'pf-concl') : null) ?? (x as HTMLElement);
}

/** 線の長さと規則の名前の位置を、描いた結果に合わせる（root の中のすべての推論）。 */
export function fitLines(root: HTMLElement): void {
  const pfs = [...root.querySelectorAll<HTMLElement>('.pf')];
  if (root.classList.contains('pf')) pfs.push(root);
  const parts = pfs.map((pf) => ({
    line: child(pf, 'pf-line'),
    rule: child(pf, 'pf-rule'),
    concl: child(pf, 'pf-concl'),
    prem: child(pf, 'pf-prem'),
  }));
  // 1. 前に合わせた分を戻す（書くだけ）
  for (const p of parts) {
    if (p.line) {
      p.line.style.marginLeft = '';
      p.line.style.width = '';
    }
    if (p.rule) p.rule.style.transform = '';
  }
  // 2. 測る（読むだけ。ここで 1 回だけ配置が計算される）
  const plans = parts.map((p) => {
    if (!p.line || !p.concl) return null;
    const col = p.line.getBoundingClientRect();
    const c = p.concl.getBoundingClientRect();
    let left = c.left;
    let right = c.right;
    const items = p.prem ? [...p.prem.children] : [];
    if (items.length) {
      left = Math.min(left, premiseFace(items[0]).getBoundingClientRect().left);
      right = Math.max(right, premiseFace(items[items.length - 1]).getBoundingClientRect().right);
    }
    return { p, margin: left - col.left, width: right - left, shift: right - col.right };
  });
  // 3. 書く
  for (const plan of plans) {
    if (!plan) continue;
    const { p, margin, width, shift } = plan;
    p.line!.style.marginLeft = `${margin}px`;
    p.line!.style.width = `${Math.max(width, 1)}px`;
    if (p.rule) p.rule.style.transform = `translateX(${shift}px)`;
  }
}

/** 要素が画面に出ているか（隠れたタブの中などでは大きさが 0 で、線の長さを測れない）。 */
function visible(el: HTMLElement): boolean {
  return el.getClientRects().length > 0 && el.clientWidth > 0;
}

const watched = new WeakSet<HTMLElement>();
const pending = new WeakSet<HTMLElement>();

const afterFit = new WeakMap<HTMLElement, () => void>();

/**
 * root の中の推論の線を合わせ、`after` を呼ぶ（配置を見て直す処理）。root が今は隠れている
 * （別のタブの中など）なら、画面に出たときにそうする。
 */
export function fitWhenShown(root: HTMLElement, after?: () => void): void {
  if (after) afterFit.set(root, after);
  else afterFit.delete(root);
  const fit = () => {
    afterFit.get(root)?.();
    fitLines(root);
  };
  if (visible(root)) {
    fit();
    return;
  }
  pending.add(root);
  if (watched.has(root)) return;
  watched.add(root);
  new ResizeObserver(() => {
    if (pending.has(root) && visible(root)) {
      pending.delete(root);
      fit();
    }
  }).observe(root);
}

/** 大きな数の表示（隠れているノードの数など）。 */
function count(n: number): string {
  return n < 1e15 ? n.toLocaleString() : n.toExponential(2).replace('e+', '×10^');
}

export interface DiagramOptions {
  /** k 番目の前提が副条件か */
  isSide: (rule: string, k: number) => boolean;
  /** 規則の名前の説明（カーソルを合わせたとき） */
  ruleText?: (rule: string) => string | undefined;
}

export interface Diagram {
  /** 図の枠（操作のボタンと、スクロールする図） */
  el: HTMLElement;
}

/**
 * 証明 DAG を証明図にする。同じ部分証明も、木として現れる場所ごとに描く
 * （開閉は現れる場所ごと。場所は根からの前提の番号の列 "0.2.1" で表す）。
 */
export function proofDiagram(p: ProofJson, opts: DiagramOptions): Diagram {
  // 部分証明を木に展開したときのノードの数（DAG の上で一度ずつ数える）
  const sizes = new Array<number>(p.nodes.length).fill(0);
  const sizeOf = (id: number): number => {
    if (sizes[id]) return sizes[id];
    // 前提は自分より前の番号なので、番号の順に数えれば再帰は浅い。念のため明示的に積む
    const stack = [id];
    while (stack.length) {
      const x = stack[stack.length - 1];
      const todo = p.nodes[x].premises.filter((q) => !sizes[q]);
      if (todo.length) {
        stack.push(...todo);
        continue;
      }
      stack.pop();
      sizes[x] = 1 + p.nodes[x].premises.reduce((s, q) => s + sizes[q], 0);
    }
    return sizes[id];
  };

  /** 開いている場所 */
  const open = new Set<string>();

  /** 場所 path（ノード id）から、幅優先で budget 個くらいまで開く。 */
  const expandFrom = (path: string, id: number, budget: number) => {
    let shown = 1;
    const queue: [string, number][] = [[path, id]];
    while (queue.length) {
      const [pp, x] = queue.shift()!;
      const prem = p.nodes[x].premises;
      if (!prem.length) continue;
      if (pp !== path && shown + prem.length > budget) continue;
      open.add(pp);
      shown += prem.length;
      prem.forEach((q, k) => queue.push([`${pp}.${k}`, q]));
    }
  };
  const reset = () => {
    open.clear();
    expandFrom('0', p.root, INITIAL_BUDGET);
  };
  reset();

  const view = h('div', { class: 'pf-view' });
  const tree = h('div', { class: 'pf-tree' });
  view.append(tree);
  let fontSize = 14;

  const build = (path: string, id: number, side: boolean): HTMLElement => {
    const node = p.nodes[id];
    const prem = node.premises;
    let premises: HTMLElement[] = [];
    const isOpen = open.has(path);
    if (prem.length && isOpen) {
      premises = prem.map((q, k) => build(`${path}.${k}`, q, opts.isSide(node.rule, k)));
    } else if (prem.length) {
      const hidden = sizeOf(id) - 1;
      const more = h(
        'button',
        {
          type: 'button',
          class: 'pf-more',
          title: tr(`開く（隠れているノード ${count(hidden)} 個）`, `Open (${count(hidden)} hidden nodes)`),
        },
        '⋮',
        h('span', { class: 'pf-more-n' }, count(hidden)),
      );
      more.addEventListener('click', () => {
        expandFrom(path, id, EXPAND_BUDGET);
        redraw(path);
      });
      premises = [more];
    }
    const el = inference({
      premises,
      rule: node.rule,
      ruleTitle: opts.ruleText?.(node.rule),
      conclusion: node.conclusion,
      conclusionClass: side ? 'pf-side-c' : undefined,
    });
    el.dataset.path = path;
    if (side) el.title = tr('副条件（括弧語どうしの比較）の導出', 'Derivation of a side condition (a comparison of bracket words)');
    if (prem.length && isOpen) {
      const c = child(el, 'pf-concl')!;
      c.classList.add('pf-fold');
      c.title = tr('押すと、この結論の上を畳む', 'Click to fold the derivation above this conclusion');
      c.addEventListener('click', () => {
        for (const k of [...open]) if (k === path || k.startsWith(`${path}.`)) open.delete(k);
        redraw(path);
      });
    }
    return el;
  };

  /** 線の長さをまだ合わせていない（隠れていた間に描いた） */
  let dirty = true;
  /** 根の結論までスクロールしたか（最初に画面に出たときに 1 回） */
  let placed = false;

  /** 描き直す。anchor の場所の推論が、画面の同じ位置に残るようにスクロールする。 */
  const redraw = (anchor?: string) => {
    const before = anchor ? tree.querySelector<HTMLElement>(`[data-path="${anchor}"] > .pf-concl`)?.getBoundingClientRect() : undefined;
    tree.style.fontSize = `${fontSize}px`;
    tree.replaceChildren(build('0', p.root, false));
    dirty = true;
    if (!visible(view)) return;
    fitLines(tree);
    dirty = false;
    if (anchor && before) {
      const after = tree.querySelector<HTMLElement>(`[data-path="${anchor}"] > .pf-concl`)?.getBoundingClientRect();
      if (after) {
        view.scrollLeft += after.left - before.left;
        view.scrollTop += after.top - before.top;
      }
    }
  };

  /** 根の結論が見えるように（下端、根の結論が真ん中）スクロールする。 */
  const showRoot = () => {
    const c = tree.querySelector<HTMLElement>(':scope > .pf > .pf-concl');
    view.scrollTop = view.scrollHeight;
    if (c) {
      const v = view.getBoundingClientRect();
      const r = c.getBoundingClientRect();
      view.scrollLeft += r.left + r.width / 2 - (v.left + v.width / 2);
    }
  };

  const zoom = (f: number) => {
    // 拡大・縮小の中心は、今見えている真ん中
    const cx = (view.scrollLeft + view.clientWidth / 2) / Math.max(view.scrollWidth, 1);
    const cy = (view.scrollTop + view.clientHeight / 2) / Math.max(view.scrollHeight, 1);
    fontSize = Math.min(28, Math.max(3, fontSize * f));
    redraw();
    view.scrollLeft = cx * view.scrollWidth - view.clientWidth / 2;
    view.scrollTop = cy * view.scrollHeight - view.clientHeight / 2;
  };

  const btn = (label: string, title: string, f: () => void) => {
    const b = h('button', { type: 'button', class: 'small', title }, label);
    b.addEventListener('click', f);
    return b;
  };
  const controls = h(
    'div',
    { class: 'pf-controls' },
    btn(tr('縮小', 'Smaller'), tr('文字を小さくする', 'Smaller text'), () => zoom(1 / 1.25)),
    btn(tr('拡大', 'Larger'), tr('文字を大きくする', 'Larger text'), () => zoom(1.25)),
    btn(tr('幅に合わせる', 'Fit width'), tr('図全体が枠の幅に入る大きさにする', 'Scale the diagram to fit the width'), () => {
      const w = tree.scrollWidth;
      if (w > 0) fontSize = Math.min(28, Math.max(3, (fontSize * (view.clientWidth - 16)) / w));
      redraw();
      showRoot();
    }),
    btn(tr('最初の表示', 'Reset'), tr('開いた・畳んだ所と大きさを最初に戻す', 'Reset folding and size'), () => {
      fontSize = 14;
      reset();
      redraw();
      showRoot();
    }),
    h(
      'span',
      { class: 'pf-hint' },
      tr('⋮ を押すと上が開き、結論を押すと畳みます。', 'Press ⋮ to open what is above; press a conclusion to fold it.'),
    ),
  );

  const el = h('div', { class: 'pf-diagram' }, controls, view);
  redraw();
  // 画面に出たとき（タブを切り替えた、隠れていた結果の欄が出た）に線を合わせ、最初の 1 回は
  // 根の結論までスクロールする。ResizeObserver は大きさが 0 から変わったときにも呼ばれる
  new ResizeObserver(() => {
    if (!visible(view)) return;
    if (dirty) {
      fitLines(tree);
      dirty = false;
    }
    if (!placed) {
      placed = true;
      showRoot();
    }
  }).observe(view);
  return { el };
}
