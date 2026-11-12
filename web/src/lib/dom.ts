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

/** エラーの表示を自動で消すまでの時間（ミリ秒） */
const ERROR_MS = 8000;
/** 欄ごとの「エラーを消す」予定（次のメッセージを出したら取り消す） */
const errorTimers = new WeakMap<HTMLElement, number>();

/** エラーの表示を、薄くしてから消す（CSS の .status.fading）。 */
function clearError(el: HTMLElement): void {
  if (!el.classList.contains('error') || el.classList.contains('keep')) return;
  el.classList.add('fading');
  window.setTimeout(() => {
    // 薄くしている間に別のメッセージが出ていたら、そちらを残す
    if (!el.classList.contains('fading')) return;
    el.textContent = '';
    el.classList.remove('error', 'fading');
  }, 400);
}

/**
 * 状態表示の欄にメッセージを出す。エラーは {@link ERROR_MS} たつか、同じカードの入力を書き換え始めたら消える
 * （直している最中に古いエラーが残っていると紛らわしいので）。
 * keep = true のエラーは消さない（読み込みに失敗して画面に何も出せないときなど、入力とは関係のないエラー）。
 */
export function setStatus(el: HTMLElement, msg: string, error = false, keep = false): void {
  window.clearTimeout(errorTimers.get(el));
  el.classList.remove('fading');
  el.textContent = msg;
  el.classList.toggle('error', error);
  // 計算中は、小さな worm が伸び縮みする印を出す（CSS の .status.busy）
  el.classList.toggle('busy', msg === busyText());
  el.classList.toggle('keep', error && keep);
  if (error && msg && !keep) errorTimers.set(el, window.setTimeout(() => clearError(el), ERROR_MS));
}

// 入力欄を書き換え始めたら、同じカードのエラーの表示を消す（ページ全体で 1 回だけ登録）
document.addEventListener('input', (e) => {
  const box = (e.target as Element | null)?.closest('.card, section.panel');
  box?.querySelectorAll<HTMLElement>('.status.error').forEach(clearError);
});

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
  exampleButtons(
    container,
    items.map((x) => ({
      label: x,
      run: () => {
        input.value = x;
        run();
      },
    })),
  );
}

/** はじめから見せる例のボタンの数（残りは「もっと」で開く） */
const VISIBLE_EXAMPLES = 6;

/**
 * 例のボタンを並べる。多いときは最初の {@link VISIBLE_EXAMPLES} 個だけ見せ、「もっと（k）」のボタンで残りを開く
 * （開いたあとは「閉じる」）。押したときの動きは items の run。
 */
export function exampleButtons(container: HTMLElement, items: { label: string; run: () => void }[]): void {
  container.replaceChildren(h('span', {}, tr('例：', 'e.g.')));
  const extra: HTMLElement[] = [];
  items.forEach((it, i) => {
    const b = h('button', { type: 'button' }, it.label);
    b.addEventListener('click', it.run);
    if (i >= VISIBLE_EXAMPLES) {
      b.hidden = true;
      extra.push(b);
    }
    container.append(b);
  });
  if (!extra.length) return;
  const label = (open: boolean) => (open ? tr('閉じる', 'fewer') : tr(`もっと（${extra.length}）`, `more (${extra.length})`));
  const more = h('button', { type: 'button', class: 'ex-more', 'aria-expanded': 'false' }, label(false));
  more.addEventListener('click', () => {
    const open = more.getAttribute('aria-expanded') !== 'true';
    for (const b of extra) b.hidden = !open;
    more.setAttribute('aria-expanded', String(open));
    more.textContent = label(open);
  });
  container.append(more);
}

/** 基本列の探検（Explore.astro）に、この順序数から始めるよう頼むイベント。 */
export const EXPLORE_EVENT = 'wormlab:explore';

/** 順序数（Veblen 表記の文字列）を基本列の探検に送る。 */
export function exploreOrdinal(text: string): void {
  window.dispatchEvent(new CustomEvent<string>(EXPLORE_EVENT, { detail: text }));
}

/** 規則の一覧（Rules.astro）で、この体系を開くよう頼むイベント。 */
export const RULES_EVENT = 'wormlab:rules';

/** 「規則と定義」のタブ（推論規則の側）に移って、体系 id（rc・wc・bc・bwc・rcbi）の一覧を出す。 */
export function showRules(id: string): void {
  window.dispatchEvent(new CustomEvent<string>(RULES_EVENT, { detail: id }));
  location.hash = 'rules';
}

/** 定義の画面（Glossary.astro、#defs）で、この定義を見せるよう頼むイベント。 */
export const DEFS_EVENT = 'wormlab:definition';

/** 「規則と定義」のタブ（定義の側）に移って、鍵 key の定義（worm-battle など）を見せる。 */
export function showDefinition(key: string): void {
  location.hash = 'defs';
  window.dispatchEvent(new CustomEvent<string>(DEFS_EVENT, { detail: key }));
}

/** 証明のタブ（Proof.astro）で、この体系を選ぶよう頼むイベント。 */
export const PROVE_EVENT = 'wormlab:prove';

/** 証明のタブに移って、体系 id を選ぶ。`sequent` を渡すと、そのシーケントを入れて証明する。 */
export function proveIn(id: string, sequent?: string): void {
  window.dispatchEvent(new CustomEvent<ProveRequest>(PROVE_EVENT, { detail: sequent === undefined ? id : { id, sequent } }));
  location.hash = 'proof';
}

/** 証明のタブへの頼み：体系の id だけか、体系とシーケント。 */
export type ProveRequest = string | { id: string; sequent: string };
