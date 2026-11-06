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
cargo run -q -- rc "<2>p |- <0><1>p"          # RC で判定（真なら導出を作って検査、偽なら反例モデル）
cargo run -q -- rc "<1>p & <0>q |- <1>(p & <0>q)" --proof   # RC の導出を全行表示
cargo run -q -- rc "<ω+1>p & <ω>q |- <ω+1>(p & <ω>q)"      # モダリティが順序数でも可
cargo run --release -p wormlab-core --example rc_sizes      # RC 導出の大きさの実験
cargo run -q -- lt 1 "0 2" "1"                # 一般の worm で A <_n B か
cargo run -q -- wclt 0 "1 1" "2"              # 1 1 <_0 2 の WC 証明（検査済み）
cargo run -q -- wc "2 0 1 |- 1 0 1" --json    # worm シーケントの WC 証明を JSON で
cargo run --release -p wormlab-core --example wc_sizes > sizes.csv   # 証明サイズの実験
cargo run -q -- ordinal "w^e_0 + phi(2,0)"    # Γ0 未満の順序数を正規形に（→ φ(2, 0)）
cargo run -q -- ordinal "ε_0·2" "ω^(ε_0+1)"   # 2 つの順序数を比較
cargo run -q -- cmp "3 3 3" "<ω>"             # 文字が順序数の worm も比較できる
cargo run -q -- ord "<ω+1><0><ε_0>"           # 順序数の worm の o(A)（Γ0 未満）・標準形・Ω_ξ
cargo run -q -- bracket "((()))"              # 括弧記法：((())) = ⟨ω⟩⊤ = ε_0
cargo run -q -- bracketof "φ(2,0) + ε_0"      # 順序数 → 正規形の括弧語
cargo run -q -- bbattle "(()())" 20           # 括弧語の battle（Γ0 版の worm battle）
cargo run -q -- bcmp "((()))" "(()())(())"    # 括弧語を順序数を使わずに比較（Veblen 経由と照合）
cargo run -q -- bc "((()))p |- ()(())p"       # Bracket Calculus で判定・導出・検査（--proof で全行）
cargo run -q -- bc "((((())))) |- ()(((())))" # 括弧語どうしの比較 φ(ε_0,0) > ε_0 を BC で証明
cargo run --release -p wormlab-core --example bc_sizes   # BC と RC_Γ0 の導出の大きさの比較
cargo run -q -- bi "<2>_2<2>_3 T |- <1>(<2>_3 T)"      # RC_BI（Pakhomov–Lazar）で判定：Γ₀ > φ_ω(0)
cargo run -q -- bi "D T |- <2>_2 T" --model   # 偽なら反例モデル M_A を表示
cargo run -q -- bimodel "D <1> T"             # 有限モデル M_A とフレーム条件の検査
cargo run --release -p wormlab-core --example rcbi_sizes # M_A の大きさの実験
cargo run -q -- bicmp "<1>_3<2>_3 T" "<2>_2<2>_3 T"     # RC_BI の順序 <¹₁ で比較
cargo run -q -- bifs "<2>_2<2>_3 T" 4         # 式の形と基本列 (A)_1..4（Γ₀ への基本列）
cargo run -q -- bibattle "D T"                # RC_BI の式の battle
cargo run --release -p wormlab-core --example rcbi_order # 線形性（Thm 4.11）と基本列の共終性の実験
cargo run -q -- thm52 3                       # ATR₀ から独立な命題の出発点
cargo run -q -- fs "ε_0" 5                    # 標準の基本列 ε_0[n] と、worm が作る列の比較
cargo run -q -- hardy "ω^2" 10                # Hardy 関数 H_α(n)・急増加関数 f_α(n)
cargo run -q -- blen "ω^2 + ω"                # worm battle と標準 battle の長さ
cargo run --release -p wormlab-core --example battles   # battle の長さの比較表
cargo run -q -- wclt 0 "<ω><ω>" "<ε_0>"       # 順序数の worm の WC 証明
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
- [x] 段階2-2/3: 文字の汎用化（Letter trait）、順序数を文字に持つ worm で RC・head/body・WC
- [x] 段階2-4: 順序数を文字に持つ worm の順序数 o（超指数関数）・逆写像・Ω_ξ
- [x] 段階2-5: 括弧記法（Beklemishev の autonomous worm）、正規形、基本列と battle
- [x] 順序数の標準基本列 α[n]（Γ0 未満）、Hardy 階層・急増加関数、battle の長さの比較
- [x] RC の導出の構成と検査器（変数・∧ を含む一般の式、順序数モダリティ）
- [x] Bracket Calculus：順序数を使わない括弧語の比較・正規形、BC の判定・導出・検査器
- [x] RC_BI 手順 1：式・パーサ、有限モデル M_A による閉じた式の判定（arXiv:2610.20115）
- [x] RC_BI 手順 2：順序 <¹₁・≡¹₁、基本列 (A)_n、線形性の検証
- [ ] RC_BI 手順 3：o(A) の計算（ε₀ → Γ₀ → Bachmann–Howard）
- [ ] 段階3: Web 可視化
- [ ] 以降: spiders / GLP₀ / 一般 RC の証明（TRC）/ 一般 GLP
