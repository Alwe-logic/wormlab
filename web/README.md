# wormlab-web

wormlab の計算をブラウザで見るためのサイトです。Rust の `wormlab-core` を WebAssembly にして、
[Astro](https://astro.build/) で作ったページから呼び出します。計算はすべてブラウザの中で行います。

画面は 1 ページで、タブが 4 つあります。

| タブ | 中身 |
|---|---|
| battle | worm・括弧語・RC_BI の式の battle を 1 ステップずつ再生（worm は棒グラフ、長さの推移の折れ線つき） |
| 順序数電卓 | 順序数・worm・括弧語の相互変換、標準形、基本列、Hardy 関数、大小の比較。RC_BI の式の比較と基本列 |
| 証明 | RC・WC・BC で判定し、導出を開閉できる木で表示（成り立たなければ反例モデル）。RC_BI は判定とモデル |
| Kripke モデル | RC の閉包モデルと RC_BI の有限モデル M_A を図で表示（関係ごとに表示を切り替え） |

どのタブでも結果を LaTeX で表示し、コードをコピーできます（「文書としてコピー」はプリアンブルつき）。
証明は bussproofs の証明木と行番号つきの一覧、モデルは TikZ（図と同じ配置）。数式の表示には
[MathJax](https://www.mathjax.org/) 3.2.2（SVG 出力、bussproofs 入り）を、必要になったときに jsDelivr から読み込みます。

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
- `src/components/*.astro`：4 つの道具（見た目と、その画面の動きを書いた `<script>`）
- `src/lib/wasm.ts`：WebAssembly の読み込みと呼び出し（Rust の関数は JSON の文字列を返す）
- `src/lib/graph.ts`：Kripke モデルの図（点の配置は Rust 側の `modelview` が計算）、`src/lib/proof.ts`：証明の木、
  `src/lib/charts.ts`：battle の図、`src/lib/latex.ts`：LaTeX の表示（MathJax）とコピー
- `src/styles/global.css`：色（ライト・ダーク）と見た目
- Rust 側の入り口は `crates/wormlab-wasm/src/lib.rs`
