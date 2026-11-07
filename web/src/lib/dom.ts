// DOM を組み立てるための小さな道具。

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
  if (!e) throw new Error(`要素 #${id} がありません`);
  return e as T;
}

/** 状態表示の欄にメッセージを出す。 */
export function setStatus(el: HTMLElement, msg: string, error = false): void {
  el.textContent = msg;
  el.classList.toggle('error', error);
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
  container.append(h('span', {}, '例：'));
  for (const x of items) {
    const b = h('button', { type: 'button' }, x);
    b.addEventListener('click', () => {
      input.value = x;
      run();
    });
    container.append(b);
  }
}
