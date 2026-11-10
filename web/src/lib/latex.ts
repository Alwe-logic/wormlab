// LaTeX の表示（MathJax）と、コードのコピー。
//
// LaTeX のコードは Rust（wormlab-core の latex モジュール）が作る。ここでは
//   - MathJax で数式として表示する（必要になったときに CDN から 1 回だけ読む）
//   - コードを見せて、クリップボードにコピーする（そのままか、プリアンブルつきの文書にして）
// だけを行う。
//
// MathJax は SVG を出す "tex-svg-full" 版を使う。SVG ならフォントのファイルを別に取りに
// 行かないので、claude.ai の公開ページのような制限のある場所でも動く。"full" には
// 証明木の bussproofs も入っている。TikZ は MathJax では描けないので、コードだけを出す。

import { h } from './dom';
import { tr } from './i18n';
import { loaded } from './wasm';

const MATHJAX_URL = 'https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-svg-full.js';

interface MathJaxApi {
  tex2svgPromise(tex: string, options: { display: boolean }): Promise<HTMLElement>;
  startup: {
    defaultReady(): void;
    promise: Promise<void>;
    document: { clear(): void; updateDocument(): void };
  };
}

let styled = false;

let loading: Promise<MathJaxApi> | null = null;

/** MathJax を読み込む（初回だけ）。 */
export function mathjax(): Promise<MathJaxApi> {
  loading ??= new Promise<MathJaxApi>((resolve, reject) => {
    const w = window as unknown as { MathJax: unknown };
    // 読み込む前に設定を置いておくと、MathJax がそれを読んで起動する
    w.MathJax = {
      tex: { packages: { '[+]': ['bussproofs', 'textmacros'] } },
      svg: { fontCache: 'local' },
      options: { enableMenu: false },
      startup: {
        typeset: false,
        ready() {
          const mj = w.MathJax as MathJaxApi;
          mj.startup.defaultReady();
          mj.startup.promise.then(() => resolve(mj), reject);
        },
      },
    };
    const script = document.createElement('script');
    script.src = MATHJAX_URL;
    script.async = true;
    script.onerror = () => {
      loading = null;
      reject(
        new Error(
          tr(
            '数式の表示に使う MathJax を読み込めませんでした（ネットワークを確認してください）。コードはコピーできます。',
            'Could not load MathJax for rendering formulas (check your network). You can still copy the code.',
          ),
        ),
      );
    };
    document.head.append(script);
  });
  return loading;
}

/** `\[ … \]` を外す（MathJax には中身だけを渡す）。prooftree・align* はそのまま。 */
function mathBody(code: string): string {
  const t = code.trim();
  if (t.startsWith('\\[') && t.endsWith('\\]')) return t.slice(2, -2).trim();
  return t;
}

/** 数式を描く。`el` の中身を置き換える。描けなかったらメッセージを出す。 */
export async function renderTex(el: HTMLElement, code: string): Promise<void> {
  try {
    const mj = await mathjax();
    const node = await mj.tex2svgPromise(mathBody(code), { display: true });
    el.replaceChildren(node);
    // tex2svg で作った数式には、MathJax の CSS（推論の線の太さ・読み上げ用の隠し要素など）が
    // まだ入っていないので、最初の 1 回だけ文書に入れてもらう
    if (!styled) {
      styled = true;
      mj.startup.document.clear();
      mj.startup.document.updateDocument();
    }
  } catch (e) {
    el.replaceChildren(h('span', { class: 'muted' }, e instanceof Error ? e.message : String(e)));
  }
}

/** これより長いコードは、ボタンを押したときだけ描く（MathJax が重くなるので）。 */
const AUTO_RENDER = 12_000;

export interface TexBlockOptions {
  title: string;
  code: string;
  /** "auto"：すぐ描く（長ければボタン）、"manual"：ボタンで描く、"none"：描かない（TikZ） */
  render?: 'auto' | 'manual' | 'none';
  /** 見出しの下の小さな説明 */
  note?: string;
  /** コードを最初から開いておくか（既定は render が "none" のときだけ開く） */
  codeOpen?: boolean;
}

export interface TexBlock {
  el: HTMLElement;
  /** コードを差し替える（表示も描き直す） */
  setCode(code: string): void;
}

/**
 * LaTeX の枠：見出し、コピーのボタン、数式の表示、コード。
 * 「文書としてコピー」はプリアンブル（\documentclass など）を付けたものをコピーする。
 */
export function texBlock(opts: TexBlockOptions): TexBlock {
  let code = opts.code;
  const mode = opts.render ?? 'auto';
  const msg = h('span', { class: 'tex-msg', 'aria-live': 'polite' });
  const pre = h('pre', { class: 'tex-code' });
  const view = h('div', { class: 'tex-view' });

  const copy = async (text: string) => {
    try {
      await navigator.clipboard.writeText(text);
      msg.textContent = tr('コピーしました', 'Copied');
    } catch {
      // クリップボードが使えない環境では、コードを選択状態にする
      details.open = true;
      pre.textContent = text;
      const range = document.createRange();
      range.selectNodeContents(pre);
      const sel = window.getSelection();
      sel?.removeAllRanges();
      sel?.addRange(range);
      msg.textContent = tr('選択しました。⌘C（Ctrl+C）でコピーしてください', 'Selected. Press ⌘C (Ctrl+C) to copy');
    }
    window.setTimeout(() => {
      msg.textContent = '';
      pre.textContent = code;
    }, 4000);
  };

  const copyCode = h('button', { type: 'button', class: 'small' }, tr('コードをコピー', 'Copy code'));
  copyCode.addEventListener('click', () => copy(code));
  const copyDoc = h('button', { type: 'button', class: 'small' }, tr('文書としてコピー', 'Copy as document'));
  copyDoc.title = tr(
    'プリアンブル（\\documentclass・\\usepackage）を付けて、そのまま pdflatex にかけられる形でコピーします',
    'Copies with a preamble (\\documentclass, \\usepackage), ready to run through pdflatex',
  );
  copyDoc.addEventListener('click', () => {
    const api = loaded();
    copy(api ? api.latex_document(code) : code);
  });

  const details = h('details', { class: 'tex-details' }, h('summary', {}, tr('LaTeX のコード', 'LaTeX code')), pre);
  const el = h(
    'div',
    { class: 'tex' },
    h(
      'div',
      { class: 'tex-head' },
      h('span', { class: 'tex-title' }, opts.title),
      h('span', { class: 'tex-actions' }, copyCode, copyDoc, msg),
    ),
    opts.note ? h('div', { class: 'tex-note' }, opts.note) : null,
  );
  if (mode !== 'none') el.append(view);
  el.append(details);
  if (opts.codeOpen ?? mode === 'none') details.open = true;

  const draw = () => {
    if (mode === 'none') return;
    if (mode === 'manual' || code.length > AUTO_RENDER) {
      const b = h('button', { type: 'button', class: 'small' }, tr('数式で表示', 'Render'));
      b.addEventListener('click', () => {
        view.replaceChildren(h('span', { class: 'muted' }, tr('描いています…', 'Rendering…')));
        renderTex(view, code);
      });
      view.replaceChildren(
        b,
        h('span', { class: 'muted', style: 'margin-left:8px;font-size:12px' }, tr(`（コード ${code.length.toLocaleString()} 文字）`, `(${code.length.toLocaleString()} characters of code)`)),
      );
    } else {
      view.replaceChildren(h('span', { class: 'muted' }, tr('描いています…', 'Rendering…')));
      renderTex(view, code);
    }
  };

  const setCode = (c: string) => {
    code = c;
    pre.textContent = c;
    draw();
  };
  setCode(code);
  return { el, setCode };
}
