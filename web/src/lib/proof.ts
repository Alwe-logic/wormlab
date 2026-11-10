// 証明（導出の DAG）の表示：証明図（lib/prooftree.ts）と、開いたり閉じたりできる入れ子の一覧。
//
// DAG では同じ部分証明が何度も使われるので、木に展開すると巨大になりうる。
// そこで、入れ子の一覧の子は「開いたとき」に初めて作る（証明図は ⋮ で畳んでおく）。

import { h } from './dom';
import { tr } from './i18n';
import { texBlock } from './latex';
import { proofDiagram } from './prooftree';

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

/**
 * k 番目の前提が「副条件（括弧語どうしの比較の導出）」か。
 * BC：R3a・R3b の 2 番目、R4 の 1 番目。BWC：A3 の前提、R3 の 3 番目以降。
 * （WC の A3 は前提なし、R3 は前提 2 つなので、WC では当てはまらない）
 */
export function isSide(rule: string, k: number): boolean {
  if (rule === 'R3a' || rule === 'R3b') return k === 1;
  if (rule === 'R4' || rule === 'A3') return k === 0;
  if (rule === 'R3') return k >= 2;
  return false;
}

/** 規則の名前の説明（「名前：1 行の書き方」）。 */
type RuleText = (rule: string) => string | undefined;

function line(node: ProofNode, side: boolean, ruleText?: RuleText): HTMLElement {
  return h(
    'span',
    {},
    side ? h('span', { class: 'side' }, tr('副条件', 'side condition')) : null,
    node.conclusion,
    h('span', { class: 'rule', title: ruleText?.(node.rule) }, node.rule),
  );
}

function nodeEl(p: ProofJson, id: number, side: boolean, open: boolean, ruleText?: RuleText): HTMLElement {
  const node = p.nodes[id];
  if (node.premises.length === 0) {
    return h('div', { class: 'leaf' }, line(node, side, ruleText));
  }
  const d = h('details', {}, h('summary', {}, line(node, side, ruleText)));
  let built = false;
  const build = () => {
    if (built) return;
    built = true;
    node.premises.forEach((q, k) => d.append(nodeEl(p, q, isSide(node.rule, k), false, ruleText)));
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

/** 表示のしかた（証明図か入れ子の一覧か）。切り替えたものを次の証明でも使う。 */
let mode: 'diagram' | 'outline' = 'diagram';

/**
 * 証明図・入れ子の一覧・1 行 1 ノードの一覧・LaTeX を作る。
 * `ruleText` は規則の名前にカーソルを合わせたときの説明、`sides` は副条件のある体系（BC・BWC）か。
 */
export function renderProof(container: HTMLElement, p: ProofJson, opts: { ruleText?: RuleText; sides?: boolean } = {}): void {
  container.replaceChildren();
  const diagram = proofDiagram(p, { isSide, ruleText: opts.ruleText });
  const tree = h('div', { class: 'proof-tree' }, nodeEl(p, p.root, false, true, opts.ruleText));
  // 証明図と入れ子の一覧の切り替え
  const views: [typeof mode, string, HTMLElement][] = [
    ['diagram', tr('証明図', 'Proof diagram'), diagram.el],
    ['outline', tr('入れ子の一覧', 'Nested list'), tree],
  ];
  const buttons = views.map(([m, label]) => {
    const b = h('button', { type: 'button', class: 'small', 'aria-pressed': String(m === mode) }, label);
    b.addEventListener('click', () => {
      mode = m;
      show();
    });
    return b;
  });
  const show = () => {
    views.forEach(([m, , el], i) => {
      el.hidden = m !== mode;
      buttons[i].setAttribute('aria-pressed', String(m === mode));
    });
  };
  show();
  const switcher = h('div', { class: 'view-switch', role: 'group', 'aria-label': tr('表示', 'View') }, ...buttons);
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
      tr(
        `DAG ${p.dag_size} ノード / 木に展開すると ${p.tree_size} ノード / 高さ ${p.height}。規則の名前にカーソルを合わせると、その規則の形が出ます。`,
        `DAG: ${p.dag_size} nodes / ${p.tree_size} nodes as a tree / height ${p.height}. Hover over a rule name to see the rule.`,
      ),
      opts.sides
        ? tr(
            '桃色の結論は副条件（括弧語どうしの比較）の導出です。',
            ' Pink conclusions are derivations of side conditions (comparisons of bracket words).',
          )
        : '',
    ),
    switcher,
    diagram.el,
    tree,
    h('details', { style: 'margin-top:10px' }, h('summary', {}, tr('全行を番号つきで見る', 'All lines, numbered')), h('div', { class: 'proof-lines' }, lines)),
  );

  // LaTeX：bussproofs の証明木と、行番号つきの一覧
  const tex = p.latex;
  if (tex.tree) {
    container.append(
      texBlock({
        title: tr('証明木（bussproofs）', 'Proof tree (bussproofs)'),
        code: tex.tree,
        // 画面の証明図は上で描いているので、ここはコードだけ（MathJax の bussproofs は、大きな木で
        // 規則の名前を隣の部分に重ねてしまう）
        render: 'none',
        codeOpen: false,
        note: tr(
          '\\usepackage{bussproofs} が必要です。公理は空の前提から規則の名前つきの線を引いて書いています。画面の証明図と同じ木です。',
          'Needs \\usepackage{bussproofs}. Axioms are drawn as a labelled line with no premises. It is the same tree as the diagram above.',
        ),
      }).el,
    );
  } else {
    container.append(
      h(
        'p',
        { class: 'tex-note', style: 'margin-top:12px' },
        tr(
          `証明木（bussproofs）は、木に展開すると ${p.tree_size} ノードで大きすぎる（上限 ${tex.tree_limit}）ので省略しました。下の行番号つきの一覧を使ってください。`,
          `The proof tree (bussproofs) is omitted: as a tree it has ${p.tree_size} nodes, over the limit of ${tex.tree_limit}. Use the numbered list below.`,
        ),
      ),
    );
  }
  if (tex.lines) {
    container.append(
      texBlock({
        title: tr('行番号つきの一覧', 'Numbered list'),
        code: tex.lines,
        render: p.dag_size > 80 ? 'manual' : 'auto',
        note: tr(
          '共有している部分証明は 1 回だけ書きます。番号は 1 から（上の一覧の番号 + 1）。',
          'Shared subproofs are written once. Numbering starts at 1 (the list above + 1).',
        ),
      }).el,
    );
  }
}
