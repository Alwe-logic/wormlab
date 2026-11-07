// WebAssembly（Rust の wormlab-core）を読み込んで呼ぶための小さな層。
//
// `npm run wasm` で src/pkg/ に wasm-pack の出力（JavaScript の糊と .wasm）ができる。
// Rust 側の関数は文字列を受け取って JSON の文字列を返すので、ここで JSON.parse し、
// {"error": …} なら例外にする。

export interface Api {
  version(): string;
  ordinal_info(kind: string, input: string): string;
  ordinal_compare(kindA: string, a: string, kindB: string, b: string): string;
  battle(kind: string, input: string, limit: number): string;
  prove(system: string, sequent: string): string;
  rc_model(input: string): string;
  rcbi_model(input: string): string;
  rcbi_info(input: string, k: number): string;
  rcbi_compare(a: string, b: string): string;
}

let loading: Promise<Api> | null = null;

// `npm run wasm` が作る src/pkg/wormlab_wasm.js を、Vite の普通のモジュールとして読む。
// import.meta.glob を使うのは、まだビルドしていない（ファイルがない）ときにもページ自体は
// 表示して、案内を出せるようにするため。
const modules = import.meta.glob('../pkg/wormlab_wasm.js');

async function load(): Promise<Api> {
  const loader = modules['../pkg/wormlab_wasm.js'];
  if (!loader) {
    throw new Error('WebAssembly がまだありません。web/ で `npm run wasm` を実行してから、`npm run dev` を起動し直してください。');
  }
  const mod = (await loader()) as { default: () => Promise<unknown> } & Api;
  await mod.default();
  return mod;
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
    throw new Error(
      `計算中に内部エラーが起きました（${e instanceof Error ? e.message : String(e)}）。ページを再読み込みして、入力を小さくして試してください。`,
    );
  }
  const value = JSON.parse(text);
  if (value && typeof value === 'object' && 'error' in value) {
    throw new Error(String(value.error));
  }
  return value as T;
}
