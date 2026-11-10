// 隠し機能：HI-ORDINAL のハイスコア表（右上のスコア欄を押すと出る）。
//
// 最初の表は、理論の Π¹₁ 証明論的順序数 |T|_{Π¹₁}（BI の ψ(ε_{Ω+1}) から RCA₀ の ω^ω まで、9 行と空き 1 行）。
// RCA₀・PA 以外は RC_BI の論文（arXiv:2610.20115）§6 の値（Cor 6.6：|A*|_{Π¹₁} = ε_{o(A)}）。
// PRA・EFA のような 1 階の弱い理論は、Π¹₁ と Π⁰₂ のどちらの順序数かで値が変わるので入れない。
// 順序数電卓・演算・battle で計算した可算な順序数が、大きければ表に入る（同じ大きさなら先の記録が上）。
// 1 位を超えると、右上の HI-ORDINAL もその数になる。Ω 以上（数えられない数）は記録にならない。
//
// 記録はこのブラウザ（localStorage）にだけ置く。読めない・書けない環境でも、このページの中では動く。

import { h } from './dom';
import { tr } from './i18n';
import { loaded } from './wasm';

interface Entry {
  /** 順序数（Rust の Veblen の書き方。比べるときはこれを使う） */
  o: string;
  /** 名前：理論の名前か、3 文字のイニシャル */
  name: string;
  /** 最初からある理論の行か */
  theory?: boolean;
  /** 別の書き方（Γ₀ など） */
  alias?: string;
  /** どこで計算したか（calc・arith・battle） */
  src?: string;
}

/** 最初の表：理論と Π¹₁ 証明論的順序数（大きい順）。 */
const DEFAULTS: Entry[] = [
  { o: 'ψ(ε_(Ω + 1))', name: 'BI', theory: true, alias: 'Bachmann–Howard' },
  { o: 'ψ(ε_0)', name: 'ATR', theory: true, alias: 'Γ_ε₀' },
  { o: 'ψ(0)', name: 'ATR₀', theory: true, alias: 'Γ₀' },
  { o: 'φ(ω, 0)', name: 'Σ¹₁-DC₀', theory: true },
  { o: 'φ(2, 0)', name: 'ACA₀⁺', theory: true },
  { o: 'ε_(ε_0)', name: 'ACA', theory: true },
  { o: 'ε_ω', name: 'ACA₀′', theory: true },
  { o: 'ε_0', name: 'PA', theory: true },
  { o: 'ω^ω', name: 'RCA₀', theory: true },
];

const KEY = 'wormlab-hiscore';
const ROWS = 10;
/** これより長い順序数は記録しない（保存する量を小さく） */
const MAX_CHARS = 200;

/** 保存してある自分の記録（理論の行は保存した版によらず、いつも DEFAULTS から作り直す）。 */
function loadMine(): Entry[] {
  try {
    const v = JSON.parse(localStorage.getItem(KEY) ?? 'null');
    if (Array.isArray(v)) return v.filter((e) => typeof e?.o === 'string' && typeof e?.name === 'string' && !e.theory);
  } catch {
    // 読めなければ記録なし
  }
  return [];
}

function save(t: Entry[]): void {
  try {
    localStorage.setItem(KEY, JSON.stringify(t));
  } catch {
    // 保存できなくても、このページの中では表は動く
  }
}

let table: Entry[] = DEFAULTS.map((e) => ({ ...e }));

/** a と b の大小（"<"・"="・">"）。比べられなければ null。 */
function compare(a: string, b: string): string | null {
  const api = loaded();
  if (!api) return null;
  try {
    const v = JSON.parse(api.ordinal_compare('ordinal', a, 'ordinal', b));
    return typeof v.relation === 'string' ? v.relation : null;
  } catch {
    return null;
  }
}

/** 見せるための書き方（ε_0 → ε₀ など、小さな置き換えだけ）。 */
export function pretty(o: string): string {
  return o.replace(/_0\b/g, '₀').replace(/_\(ε₀\)/g, '_ε₀');
}

let warnedUncountable = false;

const ORDINALS = ['1ST', '2ND', '3RD', '4TH', '5TH', '6TH', '7TH', '8TH', '9TH', '10TH'];

/** 計算した順序数を記録に入れてみる（入れば順位を知らせる）。 */
export function recordOrdinal(o: string | undefined | null, src: string): void {
  if (!o || o.length > MAX_CHARS || o.includes('…')) return;
  // 数えられない数（Ω 以上）は記録にしない
  const vsOmega = compare(o, 'Ω');
  if (vsOmega === null) return;
  if (vsOmega !== '<') {
    // 知らせるのはページを開いている間に 1 回だけ（Ω を含む式を何度も計算するとうるさいので）
    if (!warnedUncountable) {
      warnedUncountable = true;
      toast(tr('Ω 以上は数えられないので、記録になりません', 'Ω and above are uncountable: no score'), false);
    }
    return;
  }
  // 同じ大きさの自分の記録があれば入れない
  for (const e of table) if (!e.theory && compare(o, e.o) === '=') return;
  const i = insert({ o, name: 'YOU', src });
  if (i < 0) return;
  save(table);
  showTop();
  toast(i === 0 ? tr('NEW HI-ORDINAL!', 'NEW HI-ORDINAL!') : `NEW RECORD!  ${ORDINALS[i]}`, true, i);
}

/** 表の順位の所に入れる（同じ大きさなら先の行が上）。入った位置、入らなければ −1。 */
function insert(e: Entry): number {
  let i = 0;
  while (i < table.length && compare(e.o, table[i].o) !== '>') i++;
  if (i >= ROWS) return -1;
  table.splice(i, 0, e);
  table = table.slice(0, ROWS);
  return i;
}

/** 右上の HI-ORDINAL：表の 1 位。最初の表のままなら ψ(ε_{Ω+1})（HTML のまま）。 */
function showTop(): void {
  const box = document.getElementById('hiscore');
  const value = box?.querySelector<HTMLElement>('.value');
  if (!box || !value) return;
  const top = table[0];
  if (top.theory) return;
  value.textContent = pretty(top.o);
  box.classList.add('beaten');
}

let toastEl: HTMLElement | null = null;
let toastTimer = 0;

/** 画面の下に出す小さな知らせ。good なら押すと表を開く。 */
function toast(text: string, good: boolean, rank?: number): void {
  toastEl?.remove();
  const el = h('button', { type: 'button', class: `hs-toast${good ? '' : ' bad'}` }, text);
  if (good) el.addEventListener('click', () => openTable(rank));
  else el.addEventListener('click', () => el.remove());
  document.body.append(el);
  toastEl = el;
  window.clearTimeout(toastTimer);
  toastTimer = window.setTimeout(() => el.remove(), 5000);
}

let dialog: HTMLDialogElement | null = null;

/** 表を開く。focus の行（新しい記録）は名前を書けるようにしておく。 */
function openTable(focus?: number): void {
  dialog ??= document.getElementById('hiscore-dialog') as HTMLDialogElement | null;
  if (!dialog) return;
  render(focus);
  if (!dialog.open) dialog.showModal();
  if (focus !== undefined) dialog.querySelector<HTMLInputElement>(`input[data-row="${focus}"]`)?.select();
}

function render(focus?: number): void {
  if (!dialog) return;
  const srcName: Record<string, string> = {
    calc: tr('電卓', 'calculator'),
    arith: tr('演算', 'arithmetic'),
    expr: tr('式', 'expression'),
    battle: 'battle',
  };
  const rows = table.map((e, i) => {
    let name: HTMLElement;
    if (e.theory) {
      name = h('span', { class: 'hs-theory' }, e.name);
    } else {
      const input = h('input', {
        type: 'text',
        maxlength: 3,
        value: e.name,
        'data-row': String(i),
        'aria-label': tr('イニシャル（3 文字）', 'Initials (3 letters)'),
        spellcheck: 'false',
        autocomplete: 'off',
      });
      input.addEventListener('input', () => {
        input.value = input.value.toUpperCase().replace(/[^A-Z0-9.!?-]/g, '').slice(0, 3);
      });
      input.addEventListener('change', () => {
        e.name = input.value || 'YOU';
        save(table);
      });
      name = input;
    }
    return h(
      'tr',
      { class: `${e.theory ? 'cpu' : 'you'}${i === focus ? ' new' : ''}` },
      h('td', { class: 'hs-rank' }, ORDINALS[i]),
      h(
        'td',
        { class: 'hs-ord' },
        pretty(e.o),
        e.alias ? h('span', { class: 'hs-alias' }, ` = ${e.alias}`) : null,
        e.src ? h('span', { class: 'hs-alias' }, `  (${srcName[e.src] ?? e.src})`) : null,
      ),
      h('td', { class: 'hs-name' }, name),
    );
  });
  // 空いている行（アーケードの「???」）
  for (let i = table.length; i < ROWS; i++) {
    rows.push(
      h(
        'tr',
        { class: 'empty' },
        h('td', { class: 'hs-rank' }, ORDINALS[i]),
        h('td', { class: 'hs-ord' }, '???'),
        h('td', { class: 'hs-name' }, '---'),
      ),
    );
  }
  const close = h('button', { type: 'button', class: 'small' }, tr('とじる', 'Close'));
  close.addEventListener('click', () => dialog?.close());
  const clear = h('button', { type: 'button', class: 'small' }, tr('記録を消す', 'Clear my scores'));
  let armed = false;
  clear.addEventListener('click', () => {
    // 消すと戻せないので、2 回押して消す
    if (!armed) {
      armed = true;
      clear.textContent = tr('もう一度押すと消します', 'Press again to clear');
      return;
    }
    table = DEFAULTS.map((e) => ({ ...e }));
    save(table);
    location.reload();
  });
  dialog.replaceChildren(
    h('h2', { class: 'hs-title' }, 'HIGH SCORES'),
    h('table', { class: 'hs-table' }, h('tbody', {}, ...rows)),
    h(
      'p',
      { class: 'hs-note' },
      tr(
        '理論の行は Π¹₁ 証明論的順序数（RCA₀・PA 以外は RC_BI の論文 §6 の値）。PRA や EFA のような 1 階の弱い理論は、Π¹₁ と Π⁰₂ のどちらの順序数かで値が変わるので入れていません。順序数電卓・演算・式の標準形・battle で計算した可算な順序数が、大きければ表に入ります（このブラウザにだけ保存）。1 位を超えると右上の HI-ORDINAL も変わります。',
        'Theory rows show Π¹₁ proof-theoretic ordinals (all but RCA₀ and PA are the values in §6 of the RC_BI paper). Weak first-order theories such as PRA and EFA are left out, since their ordinal depends on whether it is the Π¹₁ or the Π⁰₂ one. Countable ordinals you compute in the calculator, arithmetic, expressions or battle enter the table if they are large enough (saved in this browser only). Beat the 1st place and the HI-ORDINAL changes too.',
      ),
    ),
    h('div', { class: 'hs-actions' }, close, table.some((e) => !e.theory) ? clear : null),
  );
}

/** 右上のスコア欄を押すと表が開くようにする（ページを開いたときに 1 回）。 */
export function setupHiscore(): void {
  // 保存してある自分の記録を、今の理論の表に入れ直す（理論の行を直した版でも記録が残るように）
  for (const e of loadMine()) insert({ o: e.o, name: e.name, src: e.src });
  showTop();
  document.getElementById('hiscore')?.addEventListener('click', () => openTable());
  const d = document.getElementById('hiscore-dialog') as HTMLDialogElement | null;
  // 枠の外（背景）を押したら閉じる
  d?.addEventListener('click', (e) => {
    if (e.target === d) d.close();
  });
}
