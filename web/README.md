# wormlab-web

wormlab の計算をブラウザで見るためのサイトです。Rust の `wormlab-core` を WebAssembly にして、
[Astro](https://astro.build/) で作ったページから呼び出します。計算はすべてブラウザの中で行います。

画面は 1 ページで、タブが 6 つあります。

| タブ | 中身 |
|---|---|
| battle | worm・括弧語・RC_BI の式の battle を 1 ステップずつ再生（worm は棒グラフ、括弧語は入れ子のブロック、長さの推移の折れ線つき）。長くなったステップは、同じ部分が続く所を (ab)^k でまとめて表示（worm・括弧語の図は、繰り返しの中身を 1 回分だけ描いて波括弧と ×k）。worm の battle はまとめたまま進めるので、長さの上限なく 2000 ステップまで |
| 順序数電卓 | 表示する標準形の選択（Veblen 形・φ だけ・超指数関数と ψ・worm・括弧語・impredicative worm。タブの中の数をその書き方で出す）。順序数・worm・括弧語の相互変換、標準形、基本列、Hardy 関数。基本列をたどる探検（α[n]・α{n} を押して降りる、標準 battle の道すじ）、演算 α+β・α·β・α^β（計算の過程つき）、式の標準形（+・·・^・Veblen 関数 φ・ε・超指数関数 e^α・崩壊関数 ψ を組み合わせた式を、使った定義つきで内側から 1 段ずつ。定義の一覧と出典つき）、大小の比較。RC_BI の式の比較と基本列 |
| 証明 | RC・WC・BC・BWC で判定し、導出を証明図（⋮ で開く・結論を押して畳む、拡大・縮小・幅に合わせる）か入れ子の一覧で表示（成り立たなければ反例モデル）。規則の名前にカーソルを合わせると規則の形が出る。RC_BI は判定とモデル |
| 規則 | 各体系（RC・WC・BC・BWC・RC_BIω）の公理と推論規則を、証明図と同じ形で一覧（出典・式の書き方・条件・補足つき） |
| Kripke モデル | RC の閉包モデルと RC_BI の有限モデル M_A を図で表示（関係ごとに表示を切り替え） |
| 定義 | wormlab で使う定義の一覧：ゲーム（battle と長さ）・順序数上の関数・表記と順序数の対応・体系の意味論。文字の式・LaTeX・出典・関連する定義・wormlab で計算した例つき。絞り込みと目次。ほかのタブの「定義：」のボタンから該当する定義に飛べる |

どのタブでも結果を LaTeX で表示し、コードをコピーできます（「文書としてコピー」はプリアンブルつき）。
証明は bussproofs の証明木と行番号つきの一覧、モデルは TikZ（図と同じ配置）。数式の表示には
[MathJax](https://www.mathjax.org/) 3.2.2（SVG 出力）を、必要になったときに jsDelivr から読み込みます。
画面の証明図は MathJax ではなく `src/lib/prooftree.ts` が HTML で描きます（MathJax の bussproofs は、大きな木で
規則の名前を隣の部分に重ねてしまうため。bussproofs のコードはコピー用に出します）。

画面は日本語と英語の両方で使えます。最初はブラウザの言語（日本語なら日本語、それ以外は英語）で表示し、
右上の JA / EN で切り替えられます（選んだ言語はブラウザに保存し、次に開いたときも使います）。
Rust 側のエラーや説明の文も、wasm の `set_lang` で同じ言語になります。

見た目は昔のアーケードゲーム風（黒地・ネオングリーン・worm のロゴ）。ドットのフォント（Press Start 2P・DotGothic16）は
Google Fonts から読み込みます（読めないときは普通のフォントで表示）。色はすべて `src/styles/global.css` の変数で決めています。

## 準備（初回だけ）

```sh
rustup target add wasm32-unknown-unknown   # Rust を WebAssembly 向けにコンパイルする部品
cargo install wasm-pack                    # Rust → WebAssembly ＋ JavaScript の糊のコードを作る道具
node -v                                    # Node.js 18.20 以上（なければ brew install node）
cd web
npm install                                # Astro などをダウンロード（web/node_modules に入る）
```

## 動かす

```sh
cd web
npm run wasm      # Rust をビルドして web/src/pkg/ に置く（Rust を変えたら毎回）
npm run dev       # 開発用サーバー。表示された http://localhost:4321/ をブラウザで開く
```

`npm run dev` の間は、`web/src/` を編集すると自動で再読み込みされます。
Rust を変えて `npm run wasm` をやり直したときは、`npm run dev` も起動し直してください。

## 書き出し

```sh
npm run build     # web/dist/ に静的なサイトができる
npm run preview   # 書き出したものを手元で確認
```

GitHub Pages などでサブディレクトリに置くときは、`BASE_PATH=/wormlab npm run build` のように
置き場所を指定します。

## 構成

- `src/pages/index.astro`：ページ本体（タブの切り替え）
- `src/components/*.astro`：6 つのタブ（見た目と、その画面の動きを書いた `<script>`）。順序数電卓の中の
  `NotationPicker.astro`（表示する標準形の選択）・`Explore.astro`（基本列の探検）・`Arith.astro`（演算）・`Expr.astro`（式の標準形）は別の部品で、ほかのカードからは `dom.ts` の
  `exploreOrdinal` で探検に数を送る。選んだ標準形での書き換えは `src/lib/notation.ts`（Rust の `ordinal_render` をまとめて呼んで覚える。
  見せる文字だけを書き換え、計算に渡すのはいつも Veblen 形の文字。切り替えると `wormlab:notation` イベント）。証明と規則のタブは `showRules`・`proveIn` で行き来する。どのタブの `data-def="鍵"` のボタンも、`Glossary.astro`（定義のタブ、Rust の `glossary`）の `showDefinition` でその定義に飛ぶ
- `src/lib/wasm.ts`：WebAssembly の読み込みと呼び出し（Rust の関数は JSON の文字列を返す）
- `src/lib/graph.ts`：Kripke モデルの図（点の配置は Rust 側の `modelview` が計算）、`src/lib/proof.ts`：証明の表示、
  `src/lib/prooftree.ts`：証明図（推論ごとに 2 列の grid、右の列が規則の名前）、`src/lib/rules.ts`：規則の一覧（Rust の `rules`）、
  `src/lib/logo.ts`・`src/lib/hiscore.ts`・`src/lib/devconsole.ts`：隠し機能（中身は画面で探してください）、
  `src/lib/charts.ts`：battle の図、`src/lib/latex.ts`：LaTeX の表示（MathJax）とコピー
- `src/lib/i18n.ts`：言語（日本語・英語）。動的な文は `tr('日本語', 'English')`、.astro の静的な文は
  日本語をそのまま書いて英語を `data-en`（中に要素があれば `data-en-html`、属性は `data-en-aria-label` など）に書く。
  切り替えると `wormlab:lang` イベントが飛び、各タブは表示中の結果をその言語で出し直す
- `src/styles/global.css`：色（黒地だけ。変数で決める）と見た目
- Rust 側の入り口は `crates/wormlab-wasm/src/lib.rs`
