// 順序数の書き方（標準形）の選択：順序数電卓のタブに出る数を、選んだ標準形で見せる。
//
// - 書き方は 6 つ（Rust の notation.rs の Notation）：Veblen 形（略記つき）・Veblen 形（φ だけ）・
//   超指数関数と ψ・worm・括弧語・impredicative worm。選んだものはこのブラウザに保存する。
// - 書き換えは wasm の ordinal_render（JSON の配列で一度にまとめて）。結果は覚えておき、同じ数は呼ばない。
// - 書き換えるのは「見せる文字」だけ。ボタンで次の数へ行く・別のカードへ渡す・記録に入れるときは、
//   いつも Rust の Veblen 形の文字（canonical）を使う。
// - 選んだ書き方で書けない数（Γ₀ 以上の括弧語など）は Veblen 形のままにし、理由（note）を添える。
// - 書き方を切り替えると `wormlab:notation` イベントが飛ぶので、数を出している部品は描き直す。

import { h } from './dom';
import { lang, tr } from './i18n';
import { loaded } from './wasm';

export type NotationKey = 'veblen' | 'phi' | 'hyper' | 'worm' | 'bracket' | 'iworm';

export const NOTATIONS: NotationKey[] = ['veblen', 'phi', 'hyper', 'worm', 'bracket', 'iworm'];

const KEY = 'wormlab-notation';
const EVENT = 'wormlab:notation';

function isKey(x: unknown): x is NotationKey {
  return typeof x === 'string' && (NOTATIONS as string[]).includes(x);
}

function load(): NotationKey {
  try {
    const v = localStorage.getItem(KEY);
    if (isKey(v)) return v;
  } catch {
    // 読めなければいつもの Veblen 形
  }
  return 'veblen';
}

let current: NotationKey = load();

/** 今の書き方。 */
export function notation(): NotationKey {
  return current;
}

/** 書き方を切り替える（保存し、描き直しのイベントを飛ばす）。 */
export function setNotation(n: NotationKey): void {
  if (n === current) return;
  current = n;
  try {
    localStorage.setItem(KEY, n);
  } catch {
    // 保存できなくても、このページの中では切り替わる
  }
  window.dispatchEvent(new CustomEvent(EVENT, { detail: n }));
}

/** 書き方が切り替わったときに呼ぶ関数を登録する。 */
export function onNotation(f: (n: NotationKey) => void): void {
  window.addEventListener(EVENT, () => f(current));
}

/** 書き換えた数 */
export interface Shown {
  /** 見せる文字 */
  text: string;
  /** 選んだ書き方で書けず Veblen 形のままにした理由（書けたときは null） */
  note: string | null;
}

interface RenderJson {
  text: string;
  latex: string | null;
  note: string | null;
  /** 順序数として読めなかった（battle の途中の「…」など）ので、そのまま返した */
  raw: boolean;
}

/** 覚えておく結果（書き方・言語・数ごと）。多くなりすぎたら捨てる */
const cache = new Map<string, Shown>();
const MAX_CACHE = 20_000;
/** 一度に ordinal_render に渡す数（Rust 側の上限 MAX_RENDER_ITEMS と同じ） */
const BATCH = 500;

const cacheKey = (text: string) => `${current}|${lang()}|${text}`;

/** texts をまとめて書き換え、覚えておく（もう覚えている数と Veblen 形のときは何もしない）。 */
export function prepare(texts: Iterable<string>): void {
  if (current === 'veblen') return;
  const api = loaded();
  if (!api?.ordinal_render) return;
  const todo = [...new Set(texts)].filter((t) => t && !cache.has(cacheKey(t)));
  if (todo.length === 0) return;
  if (cache.size + todo.length > MAX_CACHE) cache.clear();
  for (let i = 0; i < todo.length; i += BATCH) {
    const part = todo.slice(i, i + BATCH);
    try {
      const v = JSON.parse(api.ordinal_render(JSON.stringify(part), current));
      if (!Array.isArray(v)) continue;
      // 【メモ】v[j] は part[j] の結果（同じ順番で返ってくる）
      part.forEach((t, j) => {
        const r = v[j] as RenderJson | undefined;
        cache.set(cacheKey(t), r && !r.raw ? { text: r.text, note: r.note } : { text: t, note: null });
      });
    } catch {
      // 書き換えられなければ、そのまま見せる
    }
  }
}

/** 1 つの数を今の書き方で（書き換えられなければそのまま）。 */
export function rendered(text: string): Shown {
  if (current === 'veblen' || !text) return { text, note: null };
  const k = cacheKey(text);
  if (!cache.has(k)) prepare([text]);
  return cache.get(k) ?? { text, note: null };
}

/** 見せる文字だけ。 */
export function show(text: string): string {
  return rendered(text).text;
}

/** 書き方の名前（選ぶボタンの文字）。 */
export function notationName(n: NotationKey = current): string {
  switch (n) {
    case 'veblen':
      return tr('Veblen 形', 'Veblen form');
    case 'phi':
      return tr('φ だけ', 'φ only');
    case 'hyper':
      return tr('超指数＋ψ', 'hyperexp + ψ');
    case 'worm':
      return 'worm';
    case 'bracket':
      return tr('括弧語', 'bracket word');
    case 'iworm':
      return 'impredicative worm';
  }
}

/**
 * 1 つの数を見せる要素：書けなかったときは理由をツールチップに、印（*）を付ける。
 * 【メモ】tag は要素の種類（span・div など）、cls はクラス名。
 */
export function shownEl(text: string, tag: 'span' | 'div' = 'span', cls = ''): HTMLElement {
  const r = rendered(text);
  const el = h(tag, { class: `${cls}${r.note ? ' nf-fallback' : ''}`.trim() || undefined, title: r.note ?? undefined }, r.text);
  return el;
}

/** texts のうち書けなかった数の理由をまとめた 1 行（どれも書けたら null）。 */
export function fallbackLine(texts: Iterable<string>): HTMLElement | null {
  if (current === 'veblen') return null;
  const notes = new Set<string>();
  for (const t of texts) {
    const n = rendered(t).note;
    // 「長すぎて書き出せません（4397 文字）」の文字数は数ごとに違うので、まとめるときは省く（数のツールチップには残る）
    if (n) notes.add(n.replace(/\s*[（(][^（）()]*\d[^（）()]*[）)]/g, ''));
  }
  if (notes.size === 0) return null;
  const name = notationName();
  // 日本語の文では、英字で終わる名前（worm など）のあとに空白を入れる
  const ja = /[A-Za-z]$/.test(name) ? `${name} ` : name;
  return h(
    'p',
    { class: 'nf-note' },
    tr(
      `＊ ${ja}で書けない数は Veblen 形のまま：${[...notes].join('／')}`,
      `* Numbers that have no ${name} form are left in Veblen form: ${[...notes].join('; ')}`,
    ),
  );
}
