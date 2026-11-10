// 各体系の公理と規則の一覧（Rust の wormlab-core/src/rules.rs が作る）。
//
// 「規則」タブで表示し、証明図では規則の名前にカーソルを合わせたときの説明に使う。
// 言語ごとに 1 回だけ読む。

import { lang } from './i18n';
import { call } from './wasm';

export interface RuleDoc {
  name: string;
  premises: string[];
  /** 副条件の前提（同じ体系の導出で示す、括弧語どうしの比較） */
  side: string[];
  conclusion: string;
  condition: string | null;
  note: string | null;
  /** 1 行の書き方（例：φ ⊢ ψ ⇒ ⟨α⟩φ ⊢ ⟨α⟩ψ） */
  text: string;
}

export interface RuleGroup {
  title: string;
  rules: RuleDoc[];
}

export interface RuleSystem {
  /** 証明タブの体系の名前と同じ（rc・wc・bc・bwc・rcbi） */
  id: string;
  name: string;
  source: string;
  language: string[];
  groups: RuleGroup[];
  notes: string[];
  /** wormlab がこの体系の導出を作るか */
  derivations: boolean;
}

let cache: { lang: string; data: Promise<RuleSystem[]> } | null = null;

/** すべての体系の一覧（今の言語で）。 */
export function loadRules(): Promise<RuleSystem[]> {
  if (!cache || cache.lang !== lang()) {
    const data = call<RuleSystem[]>((api) => {
      if (!api.rules) throw new TypeError('rules is not a function');
      return api.rules();
    });
    // 失敗したら（古い wasm など）次に呼んだときにやり直す
    data.catch(() => {
      cache = null;
    });
    cache = { lang: lang(), data };
  }
  return cache.data;
}

/** 体系 id の規則の名前から、説明（「名前：1 行の書き方」）を引く関数。読めなければ何も返さない。 */
export async function ruleTexts(id: string): Promise<(name: string) => string | undefined> {
  try {
    const sys = (await loadRules()).find((s) => s.id === id);
    const map = new Map<string, string>();
    for (const g of sys?.groups ?? []) for (const r of g.rules) map.set(r.name, `${r.name}: ${r.text}`);
    return (name) => map.get(name);
  } catch {
    return () => undefined;
  }
}
