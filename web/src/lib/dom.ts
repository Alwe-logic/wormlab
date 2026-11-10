// DOM を組み立てるための小さな道具。

import { tr } from './i18n';

/** 要素を作る。属性と子（文字列か要素）を受け取る。 */
export function h<K extends keyof HTMLElementTagNameMap>(
  tag: K,
  attrs: Record<string, string | number | boolean | undefined> = {},
  ...children: (Node | string | null | undefined)[]
): HTMLElementTagNameMap[K] {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (v === undefined || v === false) continue;
    if (k === 'class') e.className = String(v);
    else e.setAttribute(k, v === true ? '' : String(v));
  }
  for (const c of children) {
    if (c === null || c === undefined) continue;
    e.append(typeof c === 'string' ? document.createTextNode(c) : c);
  }
  return e;
}

const SVG = 'http://www.w3.org/2000/svg';

/** SVG の要素を作る。 */
export function s<K extends keyof SVGElementTagNameMap>(
  tag: K,
  attrs: Record<string, string | number | undefined> = {},
  ...children: (Node | string)[]
): SVGElementTagNameMap[K] {
  const e = document.createElementNS(SVG, tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (v !== undefined) e.setAttribute(k, String(v));
  }
  for (const c of children) e.append(typeof c === 'string' ? document.createTextNode(c) : c);
  return e;
}

/** id で要素を取る（見つからなければ例外）。 */
export function byId<T extends HTMLElement = HTMLElement>(id: string): T {
  const e = document.getElementById(id);
  if (!e) throw new Error(tr(`要素 #${id} がありません`, `no element #${id}`));
  return e as T;
}

/** 「計算中…」の文。 */
export function busyText(): string {
  return tr('計算中…', 'Computing…');
}

/** 状態表示の欄にメッセージを出す。 */
export function setStatus(el: HTMLElement, msg: string, error = false): void {
  el.textContent = msg;
  el.classList.toggle('error', error);
  // 計算中は、小さな worm が伸び縮みする印を出す（CSS の .status.busy）
  el.classList.toggle('busy', msg === busyText());
}

/** ツールチップ（ページに 1 つだけ）。 */
let tip: HTMLDivElement | null = null;

export function showTip(text: string, x: number, y: number): void {
  if (!tip) {
    tip = h('div', { class: 'tooltip', role: 'status' });
    document.body.append(tip);
  }
  tip.textContent = text;
  tip.style.display = 'block';
  const pad = 14;
  const w = tip.offsetWidth;
  const left = x + pad + w > window.innerWidth ? x - pad - w : x + pad;
  tip.style.left = `${Math.max(4, left)}px`;
  tip.style.top = `${y + pad}px`;
}

export function hideTip(): void {
  if (tip) tip.style.display = 'none';
}

/** 例のボタンを並べる。押すと入力欄に入れて `run` を呼ぶ。 */
export function examples(container: HTMLElement, input: HTMLInputElement, items: string[], run: () => void): void {
  container.replaceChildren(h('span', {}, tr('例：', 'e.g.')));
  for (const x of items) {
    const b = h('button', { type: 'button' }, x);
    b.addEventListener('click', () => {
      input.value = x;
      run();
    });
    container.append(b);
  }
}

/** 基本列の探検（Explore.astro）に、この順序数から始めるよう頼むイベント。 */
export const EXPLORE_EVENT = 'wormlab:explore';

/** 順序数（Veblen 表記の文字列）を基本列の探検に送る。 */
export function exploreOrdinal(text: string): void {
  window.dispatchEvent(new CustomEvent<string>(EXPLORE_EVENT, { detail: text }));
}

/** 規則の一覧（Rules.astro）で、この体系を開くよう頼むイベント。 */
export const RULES_EVENT = 'wormlab:rules';

/** 規則のタブに移って、体系 id（rc・wc・bc・bwc・rcbi）の一覧を出す。 */
export function showRules(id: string): void {
  window.dispatchEvent(new CustomEvent<string>(RULES_EVENT, { detail: id }));
  location.hash = 'rules';
}

/** 定義のタブ（Glossary.astro）で、この定義を見せるよう頼むイベント。 */
export const DEFS_EVENT = 'wormlab:definition';

/** 定義のタブに移って、鍵 key の定義（worm-battle など）を見せる。 */
export function showDefinition(key: string): void {
  location.hash = 'defs';
  window.dispatchEvent(new CustomEvent<string>(DEFS_EVENT, { detail: key }));
}

/** 証明のタブ（Proof.astro）で、この体系を選ぶよう頼むイベント。 */
export const PROVE_EVENT = 'wormlab:prove';

/** 証明のタブに移って、体系 id を選ぶ。 */
export function proveIn(id: string): void {
  window.dispatchEvent(new CustomEvent<string>(PROVE_EVENT, { detail: id }));
  location.hash = 'proof';
}
