// 証明（導出の DAG）を、開いたり閉じたりできる木として表示する。
//
// DAG では同じ部分証明が何度も使われるので、木に展開すると巨大になりうる。
// そこで、子は「開いたとき」に初めて作る。

import { h } from './dom';
import { texBlock } from './latex';

export interface ProofNode {
  rule: string;
  premises: number[];
  conclusion: string;
}

export interface ProofJson {
  root: number;
  nodes: ProofNode[];
  dag_size: number;
  tree_size: string;
  height: number;
  latex: {
    verdict: string;
    /** bussproofs の証明木（木に展開して tree_limit ノードを超えるときは null） */
    tree: string | null;
    /** 行番号つきの一覧（DAG が大きすぎるときは null） */
    lines: string | null;
    tree_limit: string;
  };
}

/** BC の規則で「副条件（括弧語どうしの比較の導出）」に当たる前提の番号。 */
function sideIndex(rule: string): number | null {
  if (rule === 'R3a' || rule === 'R3b') return 1;
  if (rule === 'R4') return 0;
  return null;
}

function line(node: ProofNode, side: boolean): HTMLElement {
  return h(
    'span',
    {},
    side ? h('span', { class: 'side' }, '副条件') : null,
    node.conclusion,
    h('span', { class: 'rule' }, node.rule),
  );
}

function nodeEl(p: ProofJson, id: number, side: boolean, open: boolean): HTMLElement {
  const node = p.nodes[id];
  if (node.premises.length === 0) {
    return h('div', { class: 'leaf' }, line(node, side));
  }
  const d = h('details', {}, h('summary', {}, line(node, side)));
  let built = false;
  const build = () => {
    if (built) return;
    built = true;
    const si = sideIndex(node.rule);
    node.premises.forEach((q, k) => d.append(nodeEl(p, q, si === k, false)));
  };
  d.addEventListener('toggle', () => {
    if (d.open) build();
  });
  if (open) {
    d.open = true;
    build();
  }
  return d;
}

/** 木の表示と、1 行 1 ノードの一覧を作る。 */
export function renderProof(container: HTMLElement, p: ProofJson): void {
  container.replaceChildren();
  const tree = h('div', { class: 'proof-tree' }, nodeEl(p, p.root, false, true));
  const width = String(p.nodes.length - 1).length;
  const lines = p.nodes
    .map((n, i) => {
      const prem = n.premises.length ? `: ${n.premises.join(', ')}` : '';
      return `${String(i).padStart(width)}. ${n.conclusion}   [${n.rule}${prem}]`;
    })
    .join('\n');
  container.append(
    h(
      'p',
      { class: 'muted', style: 'font-size:13px;margin:0 0 8px' },
      `DAG ${p.dag_size} ノード / 木に展開すると ${p.tree_size} ノード / 高さ ${p.height}。` +
        '▸ を押すと、その結論を導いた前提が開きます。',
    ),
    tree,
    h('details', { style: 'margin-top:10px' }, h('summary', {}, '全行を番号つきで見る'), h('div', { class: 'proof-lines' }, lines)),
  );

  // LaTeX：bussproofs の証明木と、行番号つきの一覧
  const tex = p.latex;
  if (tex.tree) {
    container.append(
      texBlock({
        title: '証明木（bussproofs）',
        code: tex.tree,
        note: '\\usepackage{bussproofs} が必要です。公理は空の前提から規則の名前つきの線を引いて書いています。',
      }).el,
    );
  } else {
    container.append(
      h(
        'p',
        { class: 'tex-note', style: 'margin-top:12px' },
        `証明木（bussproofs）は、木に展開すると ${p.tree_size} ノードで大きすぎる（上限 ${tex.tree_limit}）ので省略しました。下の行番号つきの一覧を使ってください。`,
      ),
    );
  }
  if (tex.lines) {
    container.append(
      texBlock({
        title: '行番号つきの一覧',
        code: tex.lines,
        render: p.dag_size > 80 ? 'manual' : 'auto',
        note: '共有している部分証明は 1 回だけ書きます。番号は 1 から（上の一覧の番号 + 1）。',
      }).el,
    );
  }
}
