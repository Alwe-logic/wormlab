# wormlab

Beklemishev の worm、多様相証明可能性論理 GLP、Reflection Calculus (RC) を
計算・証明するためのツール群（Rust）。

## 構成

```
crates/
  wormlab-core/   計算エンジン本体（I/O に依存しない純粋なライブラリ）
  wormlab-cli/    コマンドラインツール `wormlab`
```

今後 `wormlab-py`（PyO3 で Python/Jupyter から使う）と
`wormlab-wasm`（Web 可視化用）を追加する予定。

## 準備（初回だけ）

```sh
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

エディタは VS Code に拡張機能 **rust-analyzer** を入れるのがおすすめ。

Web 化に備えた確認（コアが WebAssembly でビルドできるか）：

```sh
rustup target add wasm32-unknown-unknown
cargo build -p wormlab-core --target wasm32-unknown-unknown
```

## 使い方

```sh
cargo test                                   # すべてのテストを実行
cargo run -q -- ord "2 0 1 1"                 # 順序数・標準形・Π 順序数
cargo run -q -- cmp "1 1" "1 0 1 0 1"         # <_0 で比較（3 つの方法で確認）
cargo run -q -- table "1 1" "2" "3" > t.csv   # 複数の worm を CSV に
cargo run -q -- battle "1 1" 20               # worm battle
cargo run -q -- rc "<2>p |- <0><1>p"          # RC で判定（偽なら反例モデル）
cargo run -q -- lt 1 "0 2" "1"                # 一般の worm で A <_n B か
cargo run -q -- wclt 0 "1 1" "2"              # 1 1 <_0 2 の WC 証明（検査済み）
cargo run -q -- wc "2 0 1 |- 1 0 1" --json    # worm シーケントの WC 証明を JSON で
cargo run --release -p wormlab-core --example wc_sizes > sizes.csv   # 証明サイズの実験
cargo run -q -- ordinal "w^e_0 + phi(2,0)"    # Γ0 未満の順序数を正規形に（→ φ(2, 0)）
cargo run -q -- ordinal "ε_0·2" "ω^(ε_0+1)"   # 2 つの順序数を比較
cargo doc --open                              # ドキュメントをブラウザで開く
```

worm `n1 n2 … nk` は式 ⟨n1⟩⟨n2⟩…⟨nk⟩⊤ を表す（左端が一番外側）。
入力は `"1 0 2"`, `"<1><0><2>T"`, `"⟨1⟩⟨0⟩⟨2⟩⊤"` のどれでもよい。

## ロードマップ

- [x] P0: 順序数 (< ε0)、worm の順序数・標準形・worm battle
- [x] P0.5: n 未満の文字を含む worm の <_n（RC 経由）
- [x] P1a: 強正値式・シーケントのパーサ、RC の判定（標準木＋閉包）と反例モデル
- [x] 段階1-1: worm の head/body 比較（Worms & spiders, Thm 3.17）
- [x] 段階1-2/3: Worm Calculus の証明 DAG・検査器・証明器、証明サイズの実験
- [x] 段階1-4/5: 構文的判定器、Π 順序数（Ω_n）、CSV/JSON 出力
- [x] 段階2-1: Veblen 表記（Γ0 未満の順序数）
- [ ] 段階2-2〜: 文字の汎用化、順序数を文字に持つ worm の順序数・逆写像、括弧記法
- [ ] 段階3: Web 可視化
- [ ] 以降: spiders / GLP₀ / 一般 RC の証明（TRC）/ 一般 GLP
