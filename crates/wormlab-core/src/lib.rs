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
//!
//! 段階1：
//! - [`proof`]：証明 DAG と汎用の検査器（体系ごとの違いは 1 ステップの検査だけ）
//! - [`headbody`]：worm の順序の構文的な判定（Worms & spiders, Thm 3.17）
//! - [`wc`]：Worm Calculus の証明・検査・証明構成、構文的判定器
//!
//! 段階2（ε0 を超える）：
//! - [`veblen`]：Γ0 未満の順序数（Veblen 関数 φ による正規形）
//! - [`letter`]：worm の文字の型（u32 と Veblen）。worm・RC・head/body・WC はこれについて汎用
//! - [`transfinite`]：文字が順序数の worm の順序数 o(A)（超指数関数）、逆写像、Π 順序数 Ω_ξ
//! - [`bracket`]：Beklemishev の括弧記法（文字も worm で書く）、正規形、基本列と battle

pub mod bitset;
pub mod bracket;
pub mod headbody;
pub mod letter;
pub mod ordinal;
pub mod proof;
pub mod rc;
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
