// WebAssembly（Rust の wormlab-core）を読み込んで呼ぶための小さな層。
//
// `npm run wasm` で src/pkg/ に wasm-pack の出力（JavaScript の糊と .wasm）ができる。
// Rust 側の関数は文字列を受け取って JSON の文字列を返すので、ここで JSON.parse し、
// {"error": …} なら例外にする。
//
// 言語：読み込んだときと切り替えたときに `set_lang` を呼び、Rust 側のエラーや説明の文も
// 画面と同じ言語にする。

import { lang, onLang, tr } from './i18n';

export interface Api {
  version(): string;
  /** エラーや説明の文の言語（"ja" か "en"） */
  set_lang(lang: string): void;
  ordinal_info(kind: string, input: string): string;
  ordinal_compare(kindA: string, a: string, kindB: string, b: string): string;
  /** 順序数の演算（op は "+"・"*"・"^"）と計算の過程 */
  ordinal_arith(op: string, kindA: string, a: string, kindB: string, b: string): string;
  /** 基本列の探検：α[n]・α{n}（n = from から count 個）と、k = start からの標準 battle の道すじ */
  ordinal_explore(input: string, from: number, count: number, start: number): string;
  battle(kind: string, input: string, limit: number): string;
  /** battle の 1 ステップを繰り返しでまとめた書き方（古い wasm にはないので省略可） */
  battle_compact?: (kind: string, input: string) => string;
  /** worm の battle の step ステップ目の形（まとめた形の木・文字・LaTeX・順序数。古い wasm にはない） */
  battle_worm_view?: (input: string, step: number) => string;
  prove(system: string, sequent: string): string;
  rc_model(input: string): string;
  rcbi_model(input: string): string;
  rcbi_info(input: string, k: number): string;
  rcbi_compare(a: string, b: string): string;
  model_tikz(model: string, shown: string, base: boolean): string;
  /** LaTeX の断片をプリアンブルつきの文書にする（JSON ではなく文字列） */
  latex_document(body: string): string;
  /** 各体系の公理と規則の一覧（古い wasm にはない） */
  rules?: () => string;
  /** 順序数の式（+・·・^・φ・ε・e^α・ψ）を、使った定義つきで 1 段ずつ標準形に（古い wasm にはない） */
  ordinal_expr?: (input: string) => string;
  /** 式の計算で使う定義の一覧（古い wasm にはない） */
  ordinal_definitions?: () => string;
  /** 順序数（Veblen 形の文字の JSON 配列）を、選んだ標準形の書き方で（古い wasm にはない） */
  ordinal_render?: (texts: string, notation: string) => string;
  /** 標準形の書き方の一覧（名前・説明・出典・例。古い wasm にはない） */
  ordinal_notations?: () => string;
  /** 隠し機能：ロゴの worm の battle の step ステップ目（古い wasm にはない） */
  logo_worm?: (step: number) => string;
}

let loading: Promise<Api> | null = null;
let ready: Api | null = null;

// `npm run wasm` が作る src/pkg/wormlab_wasm.js を、Vite の普通のモジュールとして読む。
// import.meta.glob を使うのは、まだビルドしていない（ファイルがない）ときにもページ自体は
// 表示して、案内を出せるようにするため。
const modules = import.meta.glob('../pkg/wormlab_wasm.js');

async function load(): Promise<Api> {
  const loader = modules['../pkg/wormlab_wasm.js'];
  if (!loader) {
    throw new Error(
      tr(
        'WebAssembly がまだありません。web/ で `npm run wasm` を実行してから、`npm run dev` を起動し直してください。',
        'The WebAssembly module is not built yet. Run `npm run wasm` in web/ and restart `npm run dev`.',
      ),
    );
  }
  const mod = (await loader()) as { default: () => Promise<unknown> } & Api;
  await mod.default();
  // 古い wasm（set_lang がない）でも動くようにする
  mod.set_lang?.(lang());
  ready = mod;
  return mod;
}

// 言語を切り替えたら Rust 側にも伝える（部品の描き直しより先に登録されるので、先に呼ばれる）
onLang((l) => ready?.set_lang?.(l));

/** 読み込み済みなら API、まだなら null（クリックの中など、待てないところで使う）。 */
export function loaded(): Api | null {
  return ready;
}

/** 読み込み済みの API（初回だけ読み込む）。 */
export function wasm(): Promise<Api> {
  loading ??= load();
  return loading;
}

/** 画面を一度描き直させてから重い計算に入るための小休止。 */
export function nextFrame(): Promise<void> {
  return new Promise((r) => requestAnimationFrame(() => setTimeout(r, 0)));
}

/**
 * Rust の関数を呼んで JSON を受け取る。`{"error": …}` なら例外を投げる。
 * Rust 側がパニックすると WebAssembly の実行時エラーになり、それ以降の計算は
 * 信用できないので、ページの再読み込みを促す。
 */
export async function call<T>(f: (api: Api) => string): Promise<T> {
  const api = await wasm();
  let text: string;
  try {
    text = f(api);
  } catch (e) {
    const detail = e instanceof Error ? e.message : String(e);
    // 新しく足した関数が、前にビルドした wasm にない
    if (e instanceof TypeError && /is not a function/.test(detail)) {
      throw new Error(
        tr(
          'この機能は新しい WebAssembly が必要です。web/ で `npm run wasm` をやり直してから、ページを再読み込みしてください。',
          'This feature needs a newer WebAssembly build. Run `npm run wasm` in web/ again, then reload the page.',
        ),
      );
    }
    throw new Error(
      tr(
        `計算中に内部エラーが起きました（${detail}）。ページを再読み込みして、入力を小さくして試してください。`,
        `An internal error occurred during the computation (${detail}). Please reload the page and try a smaller input.`,
      ),
    );
  }
  const value = JSON.parse(text);
  if (value && typeof value === 'object' && 'error' in value) {
    throw new Error(String(value.error));
  }
  return value as T;
}
