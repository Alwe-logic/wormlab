// 隠し機能：開発者ツールのコンソールに出す worm と一言、それと小さな道具 `wormlab.o(…)`。

import { tr } from './i18n';
import { loaded } from './wasm';

/** ドット絵の worm ⟨2⟩⟨0⟩⟨2⟩⊤（ロゴと同じ。左が頭） */
const WORM = [
  ' ▄███▄  ▄▄▄  ▄▄▄  ▄▄▄  ▄▄▄▄▄',
  '██▀█▀██ █2█  █0█  █2█    █  ',
  ' ▀███▀  ▀▀▀  ▀▀▀  ▀▀▀    ▀  ',
].join('\n');

/** 入力の種類を推し量る（電卓と同じ 4 種類）：自然数と空白なら worm、括弧だけなら括弧語、Ω を含む括弧語は impredicative worm。 */
function kindOf(s: string): string {
  const t = s.trim();
  if (/^[\d\s]+$/.test(t)) return 'worm';
  if (/^[()⊤T\s]+$/.test(t)) return 'bracket';
  if (/^[()ΩO\s]+$/.test(t)) return 'iworm';
  return 'ordinal';
}

function api() {
  const a = loaded();
  if (!a) throw new Error(tr('WebAssembly をまだ読み込んでいます。少し待ってから試してください', 'WebAssembly is still loading; try again in a moment'));
  return a;
}

function parse(text: string): Record<string, unknown> {
  const v = JSON.parse(text);
  if (v && typeof v === 'object' && 'error' in v) throw new Error(String(v.error));
  return v;
}

/** コンソールから使う道具。 */
const tools = {
  /** worm・括弧語・順序数の順序数。例：wormlab.o('2 0 2') → "ω^ω·2" */
  o(input: string): string {
    return String(parse(api().ordinal_info(kindOf(input), input)).ordinal);
  },
  /** 2 つの大小。例：wormlab.cmp('((()))', 'ε_0') → "=" */
  cmp(a: string, b: string): string {
    return String(parse(api().ordinal_compare(kindOf(a), a, kindOf(b), b)).relation);
  },
  help(): void {
    console.log(
      tr(
        "wormlab.o('2 0 2')        worm・括弧語・順序数の順序数\nwormlab.cmp('((()))', 'ε_0')  大小（<・=・>）",
        "wormlab.o('2 0 2')        the ordinal of a worm, bracket word or ordinal\nwormlab.cmp('((()))', 'ε_0')  compare two (<, =, >)",
      ),
    );
  },
};

/** コンソールに一言を出し、`wormlab` を使えるようにする（ページを開いたときに 1 回）。 */
export function setupConsole(): void {
  (window as unknown as { wormlab: typeof tools }).wormlab = tools;
  const big = 'color:#39ff14;font-family:monospace;font-size:12px;line-height:1.1;text-shadow:0 0 4px rgba(57,255,20,.7)';
  const small = 'color:#8fdc84;font-family:monospace;font-size:12px';
  const credit = 'color:#ffe600;font-family:monospace;font-size:11px;letter-spacing:.1em';
  console.log(
    `%c${WORM}\n\n%cEVERY WORM REACHES ⊤ — BUT PA CAN'T PROVE IT\n\n%c${tr(
      'コンソールの奥までようこそ。\nこの worm（⟨2⟩⟨0⟩⟨2⟩⊤、o = ω^ω·2）は画面の左上にもいます。頭をつついてみてください。\n右上の HI-ORDINAL は、まだ誰かに破られるのを待っています。\n\nwormlab.help() で、ここから使える小さな道具の使い方が出ます。',
      "Welcome to the back room.\nThis worm (⟨2⟩⟨0⟩⟨2⟩⊤, o = ω^ω·2) also lives in the top left of the page. Try poking its head.\nThe HI-ORDINAL in the top right is still waiting to be beaten.\n\nwormlab.help() lists the little tools you can use from here.",
    )}`,
    big,
    credit,
    small,
  );
}
