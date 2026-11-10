//! # wormlab-core
//!
//! Beklemishev の worm、多様相証明可能性論理 GLP、Reflection Calculus (RC)
//! を計算するためのコアライブラリ。I/O に依存しない純粋な計算だけを置き、
//! CLI・Python・WebAssembly からはこの crate を呼び出す。
//!
//! 現在の実装範囲（P0）：
//! - [`ordinal`]：ε0 未満の順序数（Cantor 標準形）
//! - [`worm`]：worm の順序・順序数との対応・worm battle
//!
//! P1：
//! - [`spf`]：強正値式とシーケント（パーサつき）
//! - [`rc`]：Reflection Calculus の判定器（標準木＋閉包＋モデル検査）
//! - [`rcproof`]：RC の導出の構成と検査（変数・∧ を含む一般の強正値式、順序数モダリティも可）
//!
//! 段階1：
//! - [`proof`]：証明 DAG と汎用の検査器（体系ごとの違いは 1 ステップの検査だけ）
//! - [`headbody`]：worm の順序の構文的な判定（Worms & spiders, Thm 3.17）
//! - [`wc`]：Worm Calculus の証明・検査・証明構成、構文的判定器
//!
//! 段階2（ε0 を超える）：
//! - [`veblen`]：Γ0 未満の順序数（Veblen 関数 φ による正規形）。Ω・ψ も扱える（下の「Bachmann–Howard まで」）
//! - [`letter`]：worm の文字の型（u32 と Veblen）。worm・RC・head/body・WC はこれについて汎用
//! - [`transfinite`]：文字が順序数の worm の順序数 o(A)（超指数関数）、逆写像、Π 順序数 Ω_ξ
//! - [`bracket`]：Beklemishev の括弧記法（文字も worm で書く）、正規形、基本列と battle。
//!   順序数を使わない比較・正規形と、正規形の括弧語を文字にする [`bracket::NfBracket`]
//! - [`bc`]：Bracket Calculus（モダリティが括弧語の自己完結した体系）の判定・導出・検査
//! - [`bwc`]：括弧語だけの体系 BWC（WC の BC 版。文字の比較もこの体系の導出で示す）の判定・導出・検査
//!
//! Bachmann–Howard まで：
//! - [`veblen`] の Ω・ψ：Worms and spiders Def 6.19 の ψ（ψ(0) = Γ0、ψ(ε_{Ω+1}) = Bachmann–Howard）。
//!   正規形・比較・C(ξ) の判定・任意の引数の ψ（崩し）
//! - [`iworm`]：impredicative autonomous worm（Ω を文字に持つ括弧語）、射影 π、値 p(w) と逆写像（Thm 6.36）
//! - [`rcbi`]：Pakhomov–Lazar の RC_BI / RC_BIω（構文的反射・ω モデル反射・↓・∇）。
//!   有限モデル M_A による閉じた式の判定（arXiv:2610.20115, Thm 3.19）とフレーム条件の検査
//! - [`rcbi_order`]：RC_BI の順序 <¹₁・≡¹₁（Def 4.1）、式の形（零・後続・極限）、基本列 (A)_n（Def 4.6）、battle
//! - [`hierarchy`]：Hardy 階層・急増加関数（標準の基本列 α[n] による）、battle の長さ（多倍長でも）
//! - [`arith`]：順序数の演算（足し算・掛け算・べき乗、Ω・ψ を含む数も）と計算の過程
//! - [`expr`]：順序数の式（+・·・^・φ・ε・超指数関数 e^α・ψ）を、使った定義つきで 1 段ずつ標準形に。定義の一覧（出典つき）
//! - [`notation`]：標準形の書き方を選ぶ（Veblen 形（略記つき・φ だけ）、超指数関数と ψ（Worms and spiders Prop 5.14）、worm、括弧語、impredicative worm）
//! - [`bignum`]：多倍長の自然数（battle の長さや Hardy 関数の値を u128 を超えて計算するため）
//!
//! 書き出し：
//! - [`i18n`]：利用者に見せる文の言語（日本語・英語。既定は日本語、Web が英語に切り替える）
//! - [`cworm`]：繰り返しでまとめたまま進める worm battle（長さは多倍長、順序数も worm を広げずに）
//! - [`repeats`]：長い worm・括弧語を、隣り合う繰り返しでまとめて (ab)^k と書く（battle を読みやすく）
//! - [`glossary`]：定義集。ゲーム・順序数上の関数・表記と順序数の対応・体系の意味論の定義を出典つきで（Web の「定義」タブ・CLI の `defs`）。例は実装を呼んで作る
//! - [`rules`]：各体系（RC・WC・BC・BWC・RC_BI）の公理と規則の一覧（Web の「規則」タブ・CLI の `rules`）
//! - [`latex`]：式・順序数・証明（bussproofs の木と行番号つきの一覧）・battle を LaTeX に
//! - [`modelview`]：Kripke モデルの表示用の形（点の配置つき）と TikZ への書き出し

pub mod arith;
pub mod bc;
pub mod bignum;
pub mod bitset;
pub mod bracket;
pub mod bwc;
pub mod cworm;
pub mod expr;
pub mod glossary;
pub mod headbody;
pub mod hierarchy;
pub mod i18n;
pub mod iworm;
pub mod latex;
pub mod letter;
pub mod modelview;
pub mod notation;
pub mod ordinal;
pub mod proof;
pub mod rc;
pub mod rcbi;
pub mod rcbi_order;
pub mod rcproof;
pub mod repeats;
pub mod rules;
pub mod spf;
pub mod transfinite;
pub mod veblen;
pub mod wc;
pub mod worm;

pub use ordinal::Ordinal;
pub use spf::{Sequent, Spf};
pub use bracket::Bracket;
pub use letter::Letter;
pub use veblen::Veblen;
pub use worm::Worm;
