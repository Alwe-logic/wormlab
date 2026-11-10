// 隠し機能：ロゴの worm ⟨2⟩⟨0⟩⟨2⟩⊤ を battle させる。
//
// 頭を押すと 1 ステップ進む（押し続けると連続で進む）。しっぽ（⊤）を押すと、⊤ まであと何ステップかを出す。
// o = ω^ω·2 なので battle は必ず終わるが、標準形の worm から数えると 2^(1.19×10^50) ステップを超える
// （Rust の logo_worm が閉じた形で数える）。進めたステップ数はこのブラウザに覚えておく。

import { h } from './dom';
import { tr } from './i18n';
import { call, wasm } from './wasm';

interface LogoJson {
  step: number;
  /** まとめた形：文字は数、繰り返しは {r: 中身, k: 回数} */
  tree: Shape[];
  truncated: boolean;
  top: boolean;
  length: string;
  ordinal: string;
  remaining: string | null;
}

type Shape = number | { r: Shape[]; k: number };

const KEY = 'wormlab-logo-step';
/** ロゴに並べる体の節の数の上限（あふれたら …） */
const MAX_SEGS = 7;
/** HUD に書く順序数の文字数の上限（全体はツールチップ） */
const MAX_HUD_ORD = 100;
/** 押し続けたときの間隔（ミリ秒）と、連続になるまでの時間 */
const REPEAT_MS = 70;
const HOLD_MS = 350;

let step = 0;
let busy = false;
let last: LogoJson | null = null;

function loadStep(): number {
  try {
    const n = Number(localStorage.getItem(KEY) ?? 0);
    return Number.isInteger(n) && n >= 0 && n <= 1_000_000 ? n : 0;
  } catch {
    return 0;
  }
}

function saveStep(): void {
  try {
    if (step) localStorage.setItem(KEY, String(step));
    else localStorage.removeItem(KEY);
  } catch {
    // 保存できなくても、このページの中では進む
  }
}

const SUP = '⁰¹²³⁴⁵⁶⁷⁸⁹';

/** 回数を上付きの数字で（中の繰り返しの回数に使う）。 */
function sup(k: number): string {
  return [...String(k)].map((d) => SUP[Number(d)]).join('');
}

/** 繰り返しの中身を 1 行の文字に（中の繰り返しは 1²⁰ や (1 0)³ の形）。 */
function shapeText(s: Shape[]): string {
  const parts = s.map((x) => {
    if (typeof x === 'number') return String(x);
    const inner = shapeText(x.r);
    return `${x.r.length === 1 && typeof x.r[0] === 'number' ? inner : `(${inner})`}${sup(x.k)}`;
  });
  return parts.join(' ');
}

/** 体の節（一番外側の項目ごとに 1 つ。繰り返しは中身と回数）。 */
function segments(tree: Shape[], truncated: boolean): HTMLElement[] {
  const segs = tree.slice(0, MAX_SEGS).map((x, i) => {
    const el =
      typeof x === 'number'
        ? h('span', { class: 'seg' }, String(x))
        : h(
            'span',
            { class: 'seg wide' },
            x.r.length === 1 && typeof x.r[0] === 'number' ? String(x.r[0]) : `(${shapeText(x.r)})`,
            h('sup', {}, String(x.k)),
          );
    // 這う動きを節ごとにずらす（ロゴの最初の形と同じ 0.3 秒ずつ）
    el.style.animationDelay = `${-0.3 * ((i % 4) + 1)}s`;
    return el;
  });
  if (tree.length > MAX_SEGS || truncated) segs.push(h('span', { class: 'seg wide' }, '…'));
  return segs;
}

function hudText(r: LogoJson): (string | HTMLElement)[] {
  const len = r.length.length > 12 ? `${r.length.slice(0, 3)}…(${r.length.length}${tr('桁', ' digits')})` : Number(r.length).toLocaleString();
  return [
    h('span', {}, `STEP ${r.step.toLocaleString()}`),
    h('span', {}, `LEN ${len}`),
    h(
      'span',
      { class: 'hud-o', title: r.ordinal.length > MAX_HUD_ORD ? r.ordinal : undefined },
      `o = ${r.ordinal.length > MAX_HUD_ORD ? `${r.ordinal.slice(0, MAX_HUD_ORD)}…` : r.ordinal}`,
    ),
  ];
}

function render(r: LogoJson, showRemaining = false): void {
  last = r;
  const body = document.getElementById('logo-body');
  const hud = document.getElementById('logo-hud');
  if (!body || !hud) return;
  body.replaceChildren(...(r.top ? [] : segments(r.tree, r.truncated)));
  if (r.step === 0 && !showRemaining) {
    hud.hidden = true;
    return;
  }
  const reset = h('button', { type: 'button', class: 'hud-reset' }, 'RESET');
  reset.addEventListener('click', () => go(0));
  const parts = hudText(r);
  if (r.top) parts.push(h('span', { class: 'hud-clear' }, 'STAGE CLEAR'));
  else if (showRemaining && r.remaining)
    parts.push(h('span', { class: 'hud-rem' }, tr(`⊤ まであと ${r.remaining}`, `Steps left to ⊤: ${r.remaining}`)));
  hud.replaceChildren(...parts, reset);
  hud.hidden = false;
}

/** ステップ n の形を出す。 */
async function go(n: number, showRemaining = false): Promise<void> {
  if (busy) return;
  busy = true;
  try {
    const r = await call<LogoJson>((api) => {
      if (!api.logo_worm) throw new TypeError('logo_worm is not a function');
      return api.logo_worm(n);
    });
    step = r.step;
    saveStep();
    render(r, showRemaining);
  } catch {
    // 古い wasm（logo_worm がない）などでは、ロゴはそのまま
  } finally {
    busy = false;
  }
}

/** ロゴの頭・しっぽに動きを付ける（ページを開いたときに 1 回）。 */
export function setupLogo(): void {
  const head = document.getElementById('logo-head');
  const tail = document.getElementById('logo-tail');
  if (!head || !tail) return;
  let hold = 0;
  let repeat = 0;
  const stop = () => {
    window.clearTimeout(hold);
    window.clearInterval(repeat);
  };
  head.addEventListener('pointerdown', (e) => {
    if (e.button !== 0) return;
    stop();
    go(step + 1);
    // 押し続けると連続で進む
    hold = window.setTimeout(() => {
      repeat = window.setInterval(() => go(step + 1), REPEAT_MS);
    }, HOLD_MS);
  });
  for (const ev of ['pointerup', 'pointerleave', 'pointercancel']) head.addEventListener(ev, stop);
  // キーボード（Enter・スペース）でも 1 ステップ
  head.addEventListener('click', (e) => {
    if ((e as PointerEvent).pointerType === '' || e.detail === 0) go(step + 1);
  });
  tail.addEventListener('click', () => go(step, true));
  // 前に進めていたら、その続きから
  const saved = loadStep();
  if (saved > 0) wasm().then(() => go(saved));
}

/** 今のロゴの形（テスト用）。 */
export function logoState(): LogoJson | null {
  return last;
}
