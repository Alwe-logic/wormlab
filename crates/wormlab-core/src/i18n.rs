//! 利用者に見せる文の言語（日本語・英語）。
//!
//! 既定は日本語（CLI とテストはこのまま）。Web（wormlab-wasm）は画面の言語に合わせて
//! [`set_lang`] で英語に切り替える。言語はスレッドごとに持つ（WebAssembly は 1 スレッドで、
//! テストはスレッドごとに独立するので、互いに影響しない）。
//!
//! 文を作る所では、日本語と英語の組を並べて [`tr`] で選ぶ：
//! ```
//! use wormlab_core::i18n::{self, Lang, tr};
//! assert_eq!(tr("式が読めません", "cannot read the formula"), "式が読めません");
//! i18n::set_lang(Lang::En);
//! assert_eq!(tr("式が読めません", "cannot read the formula"), "cannot read the formula");
//! ```

use std::cell::Cell;

/// 言語。
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Lang {
    #[default]
    Ja,
    En,
}

impl Lang {
    /// "ja"・"en"（大文字小文字は問わない。"en-US" なども英語）。それ以外は日本語。
    pub fn parse(s: &str) -> Lang {
        if s.to_ascii_lowercase().starts_with("en") { Lang::En } else { Lang::Ja }
    }
}

// 【Rust メモ】`thread_local!` はスレッドごとに別の値を持つ変数。`Cell` は中身を
// 取り替えられる箱（&self のままで set できる）。
thread_local! {
    static LANG: Cell<Lang> = const { Cell::new(Lang::Ja) };
}

/// 今のスレッドの言語を切り替える。
pub fn set_lang(lang: Lang) {
    LANG.with(|l| l.set(lang));
}

/// 今のスレッドの言語。
pub fn lang() -> Lang {
    LANG.with(|l| l.get())
}

pub fn is_en() -> bool {
    lang() == Lang::En
}

/// 日本語と英語の組から、今の言語のものを選ぶ。
pub fn tr<'a>(ja: &'a str, en: &'a str) -> &'a str {
    if is_en() { en } else { ja }
}
