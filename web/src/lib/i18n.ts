// 画面の言語（日本語・英語）。
//
// - 言語は、前に選んだもの（localStorage）か、なければブラウザの言語で決める。
// - 動的な文は `tr('日本語', 'English')` のように、両方を並べて書く。
// - 静的な文（.astro の HTML）は、日本語をそのまま書き、英語を `data-en`（文字だけ）か
//   `data-en-html`（中に要素がある）に書く。属性は `data-en-aria-label`・`data-en-title`・
//   `data-en-placeholder`。`applyStatic()` が今の言語に合わせて入れ替える。
// - 言語を切り替えると `wormlab:lang` イベントが飛ぶので、結果を表示している部品は描き直す。

export type Lang = 'ja' | 'en';

const KEY = 'wormlab-lang';
const EVENT = 'wormlab:lang';

function detect(): Lang {
  try {
    const saved = localStorage.getItem(KEY);
    if (saved === 'ja' || saved === 'en') return saved;
  } catch {
    // 保存できない環境（プライベートモードなど）では、ブラウザの言語だけで決める
  }
  const langs = navigator.languages?.length ? navigator.languages : [navigator.language];
  return langs.some((l) => l?.toLowerCase().startsWith('ja')) ? 'ja' : 'en';
}

let current: Lang = detect();

export function lang(): Lang {
  return current;
}

/** 日本語と英語の組から、今の言語のものを選ぶ。 */
export function tr(ja: string, en: string): string {
  return current === 'en' ? en : ja;
}

/** 言語を切り替える（保存し、静的な文を入れ替え、描き直しのイベントを飛ばす）。 */
export function setLang(l: Lang): void {
  current = l;
  try {
    localStorage.setItem(KEY, l);
  } catch {
    // 保存できなくても、このページの中では切り替わる
  }
  applyStatic();
  window.dispatchEvent(new CustomEvent(EVENT, { detail: l }));
}

/** 言語が切り替わったときに呼ぶ関数を登録する。 */
export function onLang(f: (l: Lang) => void): void {
  window.addEventListener(EVENT, () => f(current));
}

const ATTRS = ['aria-label', 'title', 'placeholder'] as const;

/** `data-en`・`data-en-html`・`data-en-<属性>` を持つ要素を、今の言語に合わせる。 */
export function applyStatic(root: ParentNode = document): void {
  document.documentElement.lang = current;
  // Base.astro が英語のときに隠していた画面を出す
  document.documentElement.classList.remove('i18n-pending');
  root.querySelectorAll<HTMLElement>('[data-en], [data-en-html]').forEach((el) => {
    // 最初に見たときの日本語（HTML）を覚えておく
    if (el.dataset.ja === undefined) el.dataset.ja = el.innerHTML;
    if (current === 'ja') el.innerHTML = el.dataset.ja;
    else if (el.dataset.enHtml !== undefined) el.innerHTML = el.dataset.enHtml;
    else el.textContent = el.dataset.en ?? '';
  });
  for (const a of ATTRS) {
    root.querySelectorAll<HTMLElement>(`[data-en-${a}]`).forEach((el) => {
      const jaKey = `data-ja-${a}`;
      if (!el.hasAttribute(jaKey)) el.setAttribute(jaKey, el.getAttribute(a) ?? '');
      el.setAttribute(a, current === 'ja' ? (el.getAttribute(jaKey) ?? '') : (el.getAttribute(`data-en-${a}`) ?? ''));
    });
  }
  const desc = document.querySelector('meta[name="description"]');
  if (desc) {
    desc.setAttribute(
      'content',
      tr(
        'Beklemishev の worm、反映計算（RC・WC・BC・RC_BI）、順序数をブラウザで計算する',
        "Compute Beklemishev's worms, reflection calculi (RC, WC, BC, RC_BI) and ordinals in the browser",
      ),
    );
  }
}
