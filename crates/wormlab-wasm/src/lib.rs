//! wormlab-core をブラウザから呼ぶための層（WebAssembly）。
//!
//! JavaScript とのやりとりは「文字列を渡して、JSON の文字列を受け取る」だけにする。
//! 失敗したときは `{"error": "…"}` を返す（例外は投げない）。
//!
//! 【Rust メモ】`#[wasm_bindgen]` を付けた関数が JavaScript から呼べるようになる。
//! `wasm-pack build` が、Rust の関数を呼ぶための JavaScript（糊のコード）と
//! `.wasm` ファイルを作ってくれる。この crate は普通の Rust ライブラリとしても
//! コンパイルできるので、関数の中身は `cargo test` でそのまま確かめられる。
//!
//! ブラウザは計算中に固まるので、重くなりすぎる入力（長い worm、大きな式）は
//! ここで打ち切る。

use serde_json::{Value, json};
use std::collections::HashMap;
use std::fmt::Display;
use wasm_bindgen::prelude::*;
use wormlab_core::arith;
use wormlab_core::bignum::BigNat;
use wormlab_core::bc::{self, BSeq};
use wormlab_core::bwc::{self, BwSeq};
use wormlab_core::cworm::{self, CWorm, Shape};
use wormlab_core::expr;
use wormlab_core::notation::{self, Notation};
use wormlab_core::hierarchy;
use wormlab_core::i18n::{self, tr};
use wormlab_core::iworm::IWorm;
use wormlab_core::latex::{self, BattleRow, ToLatex};
use wormlab_core::modelview::ModelView;
use wormlab_core::proof::Proof;
use wormlab_core::rcbi::{self, Formula};
use wormlab_core::repeats;
use wormlab_core::{Bracket, Letter, Sequent, Spf, Veblen, Worm, rc, rcbi_order, rcproof, wc};

/// 結果を JSON の文字列にする。エラーは `{"error": …}`。
fn out(r: Result<Value, String>) -> String {
    match r {
        Ok(v) => v.to_string(),
        Err(e) => json!({ "error": e }).to_string(),
    }
}

/// 画面の言語（"ja" か "en"）。エラーや説明の文がこの言語になる（既定は日本語）。
#[wasm_bindgen]
pub fn set_lang(lang: &str) {
    i18n::set_lang(i18n::Lang::parse(lang));
}

/// ライブラリの版。
#[wasm_bindgen]
pub fn version() -> String {
    env!("CARGO_PKG_VERSION").to_string()
}

// ----------------------------------------------------------------------
// 入力の読み取り
// ----------------------------------------------------------------------

/// 順序数電卓・battle の入力。
enum Input {
    Ordinal(Veblen),
    Worm(Worm),
    OWorm(Worm<Veblen>),
    Bracket(Bracket),
    /// impredicative autonomous worm（Ω を文字に持つ括弧語、値は p(w)）
    IWorm(IWorm),
}

/// `kind` は "ordinal"・"worm"・"bracket"・"iworm" のどれか。
fn parse_input(kind: &str, s: &str) -> Result<Input, String> {
    let s = s.trim();
    if s.is_empty() {
        return Err(tr("入力が空です", "the input is empty").to_string());
    }
    match kind {
        // 順序数は式としても読む（Ω^Ω・ε_0·ω など）
        "ordinal" => expr::parse_ordinal(s).map(Input::Ordinal),
        "worm" => match s.parse::<Worm>() {
            Ok(w) => Ok(Input::Worm(w)),
            Err(_) => s.parse::<Worm<Veblen>>().map(Input::OWorm).map_err(|e| e.to_string()),
        },
        "bracket" => s.parse::<Bracket>().map(Input::Bracket).map_err(|e| e.to_string()),
        "iworm" => s.parse::<IWorm>().map(Input::IWorm),
        _ => Err(format!("{}: {kind}", tr("入力の種類が不明です", "unknown input kind"))),
    }
}

impl Input {
    /// 入力の式を LaTeX で（worm は o(…)、括弧語は o^*(…)、順序数そのものは None）。
    fn tex_expr(&self) -> Option<String> {
        match self {
            Input::Ordinal(_) => None,
            Input::Worm(w) => Some(format!("o({})", w.to_latex())),
            Input::OWorm(w) => Some(format!("o({})", w.to_latex())),
            Input::Bracket(b) => Some(format!("o^{{*}}({})", b.to_latex())),
            Input::IWorm(w) => Some(format!("p({})", w.to_latex())),
        }
    }

    fn ordinal(&self) -> Veblen {
        match self {
            Input::Ordinal(a) => a.clone(),
            Input::Worm(w) => Veblen::from(&w.ordinal()),
            Input::OWorm(w) => w.ordinal(),
            Input::Bracket(b) => b.ordinal(),
            Input::IWorm(w) => w.value(),
        }
    }
}

// ----------------------------------------------------------------------
// 順序数電卓
// ----------------------------------------------------------------------

/// 入力（順序数・worm・括弧語）が表す順序数と、その別の書き方・基本列など。
#[wasm_bindgen]
pub fn ordinal_info(kind: &str, input: &str) -> String {
    out(ordinal_info_impl(kind, input))
}

fn ordinal_info_impl(kind: &str, input: &str) -> Result<Value, String> {
    let x = parse_input(kind, input)?;
    let a = x.ordinal();
    let limit = a.is_limit();
    let input_view = match &x {
        Input::Ordinal(v) => {
            // 式として読んだとき（Ω^Ω・ε_0·ω など）は、書いた式を見せる（標準形は「順序数」の行に出る）
            let t = input.trim();
            let text = match t.parse::<Veblen>() {
                Ok(_) => v.to_string(),
                Err(_) => t.parse::<expr::Expr>().map(|e| e.to_string()).unwrap_or_else(|_| v.to_string()),
            };
            json!({ "kind": "ordinal", "text": text })
        }
        Input::Worm(w) => json!({
            "kind": "worm", "text": w.to_string(), "normal_form": w.normal_form().to_string(),
        }),
        Input::OWorm(w) => json!({
            "kind": "worm", "text": w.to_string(), "normal_form": w.normal_form().to_string(),
        }),
        Input::Bracket(b) => json!({
            "kind": "bracket", "text": b.to_string(), "depth": b.depth(),
            "normal_form": b.normal_form_syntactic().to_string(), "is_normal": b.is_normal_syntactic(),
            "worm": b.to_worm().to_string(),
        }),
        Input::IWorm(w) => json!({
            "kind": "iworm", "text": w.to_string(), "normal_form": w.normal_form().to_string(),
            "worm": w.to_worm().to_string(), "ordinal": w.ordinal().to_string(),
        }),
    };
    let fundamental: Vec<String> = if limit {
        (0..6).filter_map(|n| a.fundamental(n)).map(|y| y.to_string()).collect()
    } else {
        Vec::new()
    };
    let worm_fs: Vec<String> = if a.is_zero() {
        Vec::new()
    } else {
        (0..6).filter_map(|n| hierarchy::worm_fundamental(&a, n)).map(|y| y.to_string()).collect()
    };
    // Hardy 関数は ε₀ 未満だけ（ε₀ 以上では α[n] が n 段の項になり、n が大きいと計算が終わらない）。
    // 多倍長で 2^16 ビット（約 2 万桁）まで。ちょうどの値でなくなったら、そこから先の n は計算しない
    let hardy: Vec<Value> = hierarchy::hardy_samples(&a)
        .into_iter()
        .map(|(n, v)| json!({ "n": n.to_string(), "value": v.map(|v| v.describe()) }))
        .collect();
    // 括弧語は Γ0 未満だけ（Ω・ψ を含む数は括弧語で表せない）
    let bracket = a.is_predicative().then(|| Bracket::from_ordinal(&a));
    let input_tex = x.tex_expr();
    Ok(json!({
        "latex": latex::ordinal_block(input_tex.as_deref(), &a, 6),
        "input": input_view,
        "ordinal": a.to_string(),
        "is_zero": a.is_zero(),
        "is_limit": limit,
        "is_successor": a.is_successor(),
        "below_epsilon0": a.to_cnf().is_some(),
        "worm": Worm::from_veblen(&a).to_string(),
        "worm_finite": a.to_cnf().map(|c| Worm::from_ordinal(&c).to_string()),
        "predicative": a.is_predicative(),
        "iworm": IWorm::from_value(&a).map(|w| w.to_string()),
        "countable": a.is_countable(),
        "bracket": bracket.as_ref().map(|b| b.to_string()),
        "bracket_depth": bracket.as_ref().map(|b| b.depth()),
        "fundamental": fundamental,
        "worm_fundamental": worm_fs,
        "hardy": hardy,
    }))
}

/// 2 つの入力が表す順序数の大小。
#[wasm_bindgen]
pub fn ordinal_compare(kind_a: &str, a: &str, kind_b: &str, b: &str) -> String {
    out((|| {
        let (ia, ib) = (parse_input(kind_a, a)?, parse_input(kind_b, b)?);
        let (x, y) = (ia.ordinal(), ib.ordinal());
        let rel = match x.cmp(&y) {
            std::cmp::Ordering::Less => "<",
            std::cmp::Ordering::Equal => "=",
            std::cmp::Ordering::Greater => ">",
        };
        // o(A) = α < β = o^*(b) のように、入力の式も並べる
        let left = match ia.tex_expr() {
            Some(e) => format!("{e} = {}", x.to_latex()),
            None => x.to_latex(),
        };
        let right = match ib.tex_expr() {
            Some(e) => format!("{} = {e}", y.to_latex()),
            None => y.to_latex(),
        };
        let tex = latex::display(&latex::relation(&left, rel, &right));
        Ok(json!({ "a": x.to_string(), "b": y.to_string(), "relation": rel, "latex": tex }))
    })())
}

/// 順序数の演算 α + β・α·β・α^β と、計算の過程。`op` は "+"・"*"・"^"。
/// 入力の種類は [`ordinal_compare`] と同じ（worm・括弧語などはその順序数で計算する）。
#[wasm_bindgen]
pub fn ordinal_arith(op: &str, kind_a: &str, a: &str, kind_b: &str, b: &str) -> String {
    out((|| {
        let o = arith::Op::parse(op).ok_or_else(|| format!("{}: {op}", tr("演算が不明です", "unknown operation")))?;
        let (x, y) = (parse_input(kind_a, a)?.ordinal(), parse_input(kind_b, b)?.ordinal());
        let c = arith::calc(o, &x, &y).map_err(|e| e.to_string())?;
        let steps: Vec<Value> = c.steps.iter().map(|s| json!({ "text": s.plain, "note": s.note })).collect();
        Ok(json!({
            "a": x.to_string(),
            "b": y.to_string(),
            "lhs": c.lhs,
            "result": c.result.to_string(),
            "steps": steps,
            "latex": c.latex(),
        }))
    })())
}

/// 基本列の探検で見る n の上限（α[n] は n とともに長く、入れ子も深くなる）。
const MAX_FS_N: u64 = 500;
/// 1 回に並べる基本列の項の数の上限。
const MAX_FS_COUNT: u64 = 40;
/// 基本列の項の大きさ（主項の数）の上限。これを超えたら、そこから先は並べない。
const MAX_FS_SIZE: usize = 20_000;
/// 標準 battle の道すじとして並べる数の個数。
const DESCENT_SHOWN: usize = 40;
/// 標準 battle の長さを数える回数の上限。
const DESCENT_BUDGET: u64 = 100_000;
/// 標準 battle を数える仕事量（各ステップの順序数の大きさの合計）の上限。数が大きくなっていく
/// battle（ε_0 を k = 20 から、など）で、回数の上限に着く前にブラウザが長く止まらないように。
const DESCENT_WORK: u64 = 300_000;
/// 道すじに並べる数の大きさ（主項の数）の上限。
const MAX_DESCENT_ITEM: usize = 1_500;
/// worm が作る列 α{n} を出す n の上限（括弧語の基本列は n について 2 乗くらいの手間がかかる）。
const MAX_WORM_FS_N: u64 = 150;
/// 標準 battle の k の始まりの上限。
const MAX_DESCENT_START: u64 = 20;

/// 定義のタブの図（worm の基本列 A{n}）：入れる worm の文字数・文字の大きさ・n・結果の文字数の上限。
const MAX_FIG_LETTERS: usize = 40;
const MAX_FIG_LETTER: u32 = 20;
const MAX_FIG_N: u32 = 9;
const MAX_FIG_RESULT: usize = 400;

/// 文字が自然数の worm の基本列 A{n} を図にする材料：元の worm、n、先頭の文字 h と V の長さ（cut）、
/// 結果 A{n}、両方の順序数。図は Web 側で、V（先頭は黄・残りは水色）、U（緑）、V′ の n + 1 回の繰り返しに色を付けて描く。
#[wasm_bindgen]
pub fn worm_fs_figure(input: &str, n: u32) -> String {
    out((|| {
        let a: Worm = input.trim().parse().map_err(|e: wormlab_core::worm::ParseWormError| e.to_string())?;
        if a.is_top() {
            return Err(tr("⊤ には基本列がありません", "⊤ has no fundamental sequence").to_string());
        }
        if a.len() > MAX_FIG_LETTERS || a.letters().iter().any(|&x| x > MAX_FIG_LETTER) || n > MAX_FIG_N {
            return Err(format!(
                "{} {MAX_FIG_LETTERS}{}{MAX_FIG_LETTER}{}{MAX_FIG_N}{}",
                tr("図にできるのは、文字数", "figures allow up to"),
                tr(" 文字・文字の大きさ ", " letters, letters up to "),
                tr("・n が ", " and n up to "),
                tr(" までです", ""),
            ));
        }
        let p = a.fs_parts().expect("⊤ でない");
        let r = p.apply(&a, n as usize);
        if r.len() > MAX_FIG_RESULT {
            return Err(format!("{}{MAX_FIG_RESULT}{}", tr("A{n} が長すぎます（", "A{n} is too long (more than "), tr(" 文字まで）", " letters)")));
        }
        debug_assert_eq!(Some(&r), a.battle_step(n as usize).as_ref());
        Ok(json!({
            "worm": a.letters(),
            "text": a.to_string(),
            "n": n,
            "head": p.head,
            "cut": p.cut,
            "result": r.letters(),
            "result_text": r.to_string(),
            "ordinal": a.ordinal().to_string(),
            "result_ordinal": r.ordinal().to_string(),
        }))
    })())
}

/// 基本列の探検：順序数 α の形（0・後続・極限）、直前の数、標準の基本列 `α[n]` と worm が作る列 `α{n}`
/// （n = from, from+1, …、count 個）、標準 battle の道すじ `α, α[k], α[k][k+1], …`（k = start から、0 まで）。
#[wasm_bindgen]
pub fn ordinal_explore(input: &str, from: u32, count: u32, start: u32) -> String {
    // 【Rust メモ】wasm-bindgen では u64 が JavaScript の BigInt になるので、引数は u32 で受けて広げる
    let (from, count, start) = (u64::from(from), u64::from(count), u64::from(start));
    out((|| {
        let a: Veblen = expr::parse_ordinal(input.trim())?;
        if from > MAX_FS_N {
            return Err(if i18n::is_en() {
                format!("n must be at most {MAX_FS_N}")
            } else {
                format!("n は {MAX_FS_N} 以下にしてください")
            });
        }
        let kind = if a.is_zero() {
            "zero"
        } else if a.is_successor() {
            "successor"
        } else {
            "limit"
        };
        // Ω・ψ を含む数の基本列はまだ定義していない
        let defined = a.is_predicative();
        let to = (from + count.clamp(1, MAX_FS_COUNT) - 1).min(MAX_FS_N);
        let (mut fs, mut wfs) = (Vec::new(), Vec::new());
        if a.is_limit() && defined {
            for n in from..=to {
                let v = a.fundamental(n).expect("Γ0 未満の極限");
                if v.size() > MAX_FS_SIZE {
                    break;
                }
                fs.push(json!({ "n": n, "value": v.to_string() }));
                if n <= MAX_WORM_FS_N
                    && let Some(w) = usize::try_from(n).ok().and_then(|n| hierarchy::worm_fundamental(&a, n))
                    && w.size() <= MAX_FS_SIZE
                {
                    wfs.push(json!({ "n": n, "value": w.to_string() }));
                }
            }
        }
        Ok(json!({
            "ordinal": a.to_string(),
            "latex": a.to_latex(),
            "kind": kind,
            "pred": a.pred().map(|p| p.to_string()),
            "defined": defined,
            "fundamental": fs,
            "worm_fundamental": wfs,
            "max_n": MAX_FS_N,
            "max_worm_n": MAX_WORM_FS_N,
            "descent": descent(&a, start.clamp(1, MAX_DESCENT_START)),
            "start": start.clamp(1, MAX_DESCENT_START),
        }))
    })())
}

/// 標準 battle の道すじ：α_0 = α、α_i = α_{i−1}[k]（k = start, start+1, …。
/// [`hierarchy::ordinal_battle_length`] と同じで、CLI と hierarchy.md の表は start = 1）。
/// 最初の [`DESCENT_SHOWN`] 個を並べ、0 に着くまでの回数も数える（数えきれなければ下界）。
fn descent(a: &Veblen, start: u64) -> Value {
    if !a.is_predicative() {
        return json!({ "path": [a.to_string()], "defined": false });
    }
    let mut path = vec![a.to_string()];
    // 並べている途中か（並べきったか、大きすぎて並べられない数が出たらやめて、数えるのだけ続ける）
    let mut listing = true;
    let (mut cur, mut k, mut steps, mut work) = (a.clone(), start, 0u64, 0u64);
    let result = |path: &Vec<String>, length: u64, exact: bool| {
        json!({ "path": path, "defined": true, "length": length.to_string(), "exact": exact })
    };
    loop {
        if cur.is_zero() {
            return result(&path, steps, true);
        }
        // 有限の m だけが残ったら、あと m 回で終わる（並べている途中なら 1 つずつ進める）
        if !listing && let Some(m) = cur.as_nat() {
            return match steps.checked_add(m) {
                Some(total) => result(&path, total, true),
                None => result(&path, steps, false),
            };
        }
        work += cur.size() as u64;
        if steps >= DESCENT_BUDGET || work > DESCENT_WORK {
            // 数えきれない：ここまでの回数は下界
            return result(&path, steps, false);
        }
        cur = cur.fundamental(k).expect("Γ0 未満");
        k += 1;
        steps += 1;
        if listing {
            if cur.size() > MAX_DESCENT_ITEM {
                path.push("…".to_string());
                listing = false;
            } else {
                path.push(cur.to_string());
                listing = path.len() < DESCENT_SHOWN;
            }
        }
    }
}

// ----------------------------------------------------------------------
// battle
// ----------------------------------------------------------------------

/// 括弧語の文字数・式の記号数の上限（ブラウザが固まらないように）。worm はまとめたまま進めるので長さの上限はない。
const MAX_TEXT_LEN: usize = 6000;
const MAX_FORMULA_SIZE: usize = 120;
/// 1 ステップの式の LaTeX をこれより長くは送らない（長い worm は数万文字になる）。
const MAX_STEP_LATEX: usize = 1500;
/// battle の LaTeX の表に入れる式の文字数の合計の上限。
const MAX_TABLE_LATEX: usize = 30_000;

/// これ以上長い括弧語（記号の数）は、繰り返しでまとめて書く（worm はいつもまとめた形）。
const COMPACT_MIN_CHARS: usize = 40;
/// battle の LaTeX の表で、繰り返しでまとめる手間（文字の数 n の n²/2 の合計）の上限。
const COMPACT_WORK: u64 = 300_000_000;

/// 文字が自然数の worm を、まとめたまま持つ形で読む。
fn parse_cworm(input: &str) -> Result<CWorm, String> {
    let w: Worm = input.trim().parse().map_err(|e: wormlab_core::worm::ParseWormError| e.to_string())?;
    CWorm::new(&w).ok_or_else(|| {
        if i18n::is_en() {
            format!("letters must be at most {}", cworm::MAX_LETTER)
        } else {
            format!("文字は {} 以下にしてください", cworm::MAX_LETTER)
        }
    })
}

/// 1 ステップの表示用の形。
struct WormView {
    shapes: Vec<Shape>,
    truncated: bool,
    plain: Option<Worm>,
    latex: String,
}

/// まとめた worm を表示用の形にする（短い worm はまとめずにそのまま。1 1 を 1^2 と書いても読みやすくならない）。
fn worm_view(c: &CWorm) -> WormView {
    let plain = c.to_worm(MAX_PLAIN_LETTERS);
    let view = match &plain {
        Some(p) if p.len() < COMPACT_MIN_WORM => cworm::View { shapes: p.letters().iter().map(|&x| Shape::Letter(x)).collect(), truncated: false },
        _ => c.view(MAX_VIEW_LETTERS),
    };
    let latex = if c.is_top() {
        "\\top".to_string()
    } else {
        format!("{}{}", cworm::latex(&view.shapes), if view.truncated { "\\cdots" } else { "\\top" })
    };
    WormView { shapes: view.shapes, truncated: view.truncated, plain, latex }
}

/// 最後に進めた worm の battle の途中の状態（SNAPSHOT_EVERY ステップごと）。見ているステップの形は、
/// いちばん近い状態から進め直して作る（全ステップの形を一度に送ると数 MB になるため）。
struct WormCache {
    input: String,
    snaps: Vec<CWorm>,
}

/// 途中の状態を覚えておく間隔。
const SNAPSHOT_EVERY: u64 = 50;

// 【Rust メモ】WebAssembly は 1 スレッドなので、thread_local! に RefCell を入れて「前の呼び出しの結果」を覚えておける
thread_local! {
    static WORM_CACHE: std::cell::RefCell<Option<WormCache>> = const { std::cell::RefCell::new(None) };
}

/// worm の battle の `step` ステップ目の形（まとめた形の木・文字・LaTeX、短ければ元の worm、順序数）。
/// 直前の battle と同じ入力なら、覚えておいた途中の状態から進める。
#[wasm_bindgen]
pub fn battle_worm_view(input: &str, step: u32) -> String {
    out((|| {
        let step = u64::from(step);
        let start = WORM_CACHE.with(|cache| {
            let cache = cache.borrow();
            match cache.as_ref() {
                Some(c) if c.input == input.trim() && !c.snaps.is_empty() => {
                    let i = ((step / SNAPSHOT_EVERY) as usize).min(c.snaps.len() - 1);
                    Some((c.snaps[i].clone(), i as u64 * SNAPSHOT_EVERY))
                }
                _ => None,
            }
        });
        let (mut c, mut at) = match start {
            Some(x) => x,
            None => (parse_cworm(input)?, 0),
        };
        while at < step {
            at += 1;
            if !c.step(at) {
                break;
            }
        }
        let v = worm_view(&c);
        let o = c.ordinal();
        let o_text = o.to_string();
        Ok(json!({
            "step": at,
            "tree": shapes_json(&v.shapes),
            "truncated": v.truncated,
            "text": if c.is_top() { "⊤".to_string() } else { cworm::text(&v.shapes) },
            "plain": v.plain.map(|w| w.to_string()),
            "length": c.len().to_decimal(),
            "latex": short_tex(v.latex),
            "ordinal": clip(&o_text, MAX_ORD_SHOWN),
            "ordinal_chars": o_text.chars().count(),
            "ordinal_latex": short_tex(o.to_latex()),
        }))
    })())
}

// ----------------------------------------------------------------------
// 隠し機能：ロゴの worm
// ----------------------------------------------------------------------

/// ロゴの worm ⟨2⟩⟨0⟩⟨2⟩⊤（o = ω^ω·2。Beklemishev の標準形の worm）。
const LOGO_WORM: &str = "2 0 2";
/// ロゴの battle を進めるステップ数の上限（保存した値が壊れていても固まらないように）。
const MAX_LOGO_STEPS: u64 = 1_000_000;
/// ロゴに描く文字の数の上限（まとめた形）。
const LOGO_LETTERS: usize = 40;

thread_local! {
    /// ロゴの worm の今の状態（ステップ数と worm）。次の呼び出しはここから進める
    static LOGO: std::cell::RefCell<Option<(u64, CWorm)>> = const { std::cell::RefCell::new(None) };
}

/// ⊤ に着くまでの残りのステップ数（閉じた形。worm が標準形の battle の途中であることが前提）。
/// 大きすぎるときは「2^k を超える」の形の確かな下界。
fn battle_remaining(c: &CWorm, done: u64) -> Option<hierarchy::BigValue> {
    let o = Veblen::from(&c.ordinal());
    let budget = hierarchy::BigBudget { max_steps: 100_000, max_bits: 1 << 16 };
    hierarchy::worm_battle_length_big(&o, &BigNat::from(done), budget)
}

/// ロゴの worm の battle を `step` ステップ進めた形（ロゴの頭を押すと 1 ステップ進む隠し機能）。
/// まとめた形の木・長さ・順序数・⊤ までの残りのステップ数（標準形の worm から始めた battle なので
/// 閉じた形で数えられる。ω^ω·2 から始めると 2^(1.19×10^50) を超える）。
#[wasm_bindgen]
pub fn logo_worm(step: u32) -> String {
    out((|| {
        let step = u64::from(step);
        if step > MAX_LOGO_STEPS {
            return Err(tr("ロゴの worm はそこまで進められません", "the logo worm cannot go that far").to_string());
        }
        // 覚えている状態が手前なら、そこから進める（後戻りは最初から）
        let (mut at, mut c) = LOGO.with(|l| match l.borrow().as_ref() {
            Some((s, c)) if *s <= step => (*s, c.clone()),
            _ => (0, parse_cworm(LOGO_WORM).expect("ロゴの worm は読める")),
        });
        while at < step && c.step(at + 1) {
            at += 1;
        }
        LOGO.with(|l| *l.borrow_mut() = Some((at, c.clone())));
        // 短い worm はまとめずに（battle の画面と同じ）、長ければまとめた形を先頭から LOGO_LETTERS 文字まで
        let view = match c.to_worm(COMPACT_MIN_WORM as u64 - 1) {
            Some(p) => cworm::View { shapes: p.letters().iter().map(|&x| Shape::Letter(x)).collect(), truncated: false },
            None => c.view(LOGO_LETTERS),
        };
        let o = c.ordinal().to_string();
        Ok(json!({
            "step": at,
            "tree": shapes_json(&view.shapes),
            "truncated": view.truncated,
            "top": c.is_top(),
            "length": c.len().to_decimal(),
            "ordinal": clip(&o, 300),
            "remaining": battle_remaining(&c, at).map(|v| v.describe()),
        }))
    })())
}

/// まとめた worm の表示で書く文字の数の上限（長い worm でも、まとめた形がこれを超えたら先頭だけ）。
const MAX_VIEW_LETTERS: usize = 400;
/// これより短い worm はまとめずに書く。
const COMPACT_MIN_WORM: usize = 16;
/// 元の worm（まとめない形）を送る長さの上限。
const MAX_PLAIN_LETTERS: u64 = 4000;
/// 順序数がこれより長く（文字数）なったら battle を止める（順序数はステップ数の 2 乗くらいで伸び、
/// 計算の手間もそれに比例するため。worm 4 で 140 ステップくらい）。
const MAX_ORD_CHARS: usize = 20_000;
/// 見ているステップの順序数として送る文字数（長ければ先頭だけ）。
const MAX_ORD_SHOWN: usize = 3_000;
/// 全ステップの順序数の一覧に送る文字数。
const MAX_ORD_LISTED: usize = 200;
/// まとめた worm の項目の数の上限（念のため）。
const MAX_ITEMS: usize = 100_000;

/// 長い文字列は先頭だけにする。
fn clip(s: &str, max: usize) -> String {
    if s.chars().count() <= max { s.to_string() } else { format!("{}…", s.chars().take(max).collect::<String>()) }
}

/// まとめた形を JSON に：文字は数、繰り返しは {"r": [中身], "k": 回数}。
fn shapes_json(shapes: &[Shape]) -> Value {
    Value::Array(
        shapes
            .iter()
            .map(|s| match s {
                Shape::Letter(x) => json!(x),
                Shape::Rep(inner, k) => json!({ "r": shapes_json(inner), "k": k }),
            })
            .collect(),
    )
}


/// battle の表に載せる式を決める：長い worm・括弧語は繰り返しでまとめる（表に収まる所まで、手間の上限まで）。
struct TableBudget {
    used: usize,
    work: u64,
}

impl TableBudget {
    fn formula(&mut self, long: bool, n: usize, compact: impl FnOnce() -> String, raw: &str) -> String {
        let cost = (n * n / 2) as u64;
        let f = if long && self.used <= MAX_TABLE_LATEX && self.work + cost <= COMPACT_WORK {
            self.work += cost;
            compact()
        } else {
            raw.to_string()
        };
        self.used += f.len();
        f
    }
}

/// battle の 1 ステップを繰り返しでまとめた書き方（画面で今のステップを見せるときに呼ぶ）。
/// `kind` は "worm"（`input` は "2 0 1 …"）か "bracket"。
#[wasm_bindgen]
pub fn battle_compact(kind: &str, input: &str) -> String {
    out((|| {
        match kind {
            "worm" => {
                let c = repeats::worm(&input.trim().parse::<Worm>().map_err(|e| e.to_string())?);
                Ok(json!({ "text": c.text, "latex": c.latex, "shown": c.shown }))
            }
            "bracket" => {
                let b: Bracket = input.trim().parse().map_err(|e: wormlab_core::bracket::ParseBracketError| e.to_string())?;
                let c = repeats::bracket(&b);
                Ok(json!({ "text": c.text, "latex": c.latex, "shown": c.shown, "parts": bracket_parts(&b) }))
            }
            _ => Err(format!("{}: {kind}", tr("battle の種類が不明です", "unknown battle kind"))),
        }
    })())
}

/// 括弧語の図のための形：次のステップでの役割ごとに 3 つに分け、それぞれを繰り返しでまとめる。
/// - head：先頭の文字 a₁（a₁{n} に縮む。a₁ = () なら消える）
/// - copy：a₁ と一緒に n+1 回複製される a₂ … a_{ℓ−1}（ℓ は o* が a₁ より小さい最初の文字。[`Bracket::fundamental`] と同じ）
/// - rest：残り
///
/// 文字は {"t": 括弧語, "o": その o*}、繰り返しは {"r": [中身], "k": 回数}。
/// 分けずにまとめると、先頭や複製される部分が後ろの繰り返しに混ざって、色（役割）が付けられない。
fn bracket_parts(b: &Bracket) -> Value {
    let letters = b.letters();
    if letters.is_empty() {
        return json!({ "vanish": false, "head": null, "copy": [], "rest": [] });
    }
    // 文字を番号に置き換える（同じ文字は同じ番号）。順序数は文字ごとに 1 回だけ計算する
    let mut ids: HashMap<&Bracket, usize> = HashMap::new();
    let mut distinct: Vec<&Bracket> = Vec::new();
    let tokens: Vec<usize> = letters
        .iter()
        .map(|l| {
            *ids.entry(l).or_insert_with(|| {
                distinct.push(l);
                distinct.len() - 1
            })
        })
        .collect();
    let ords: Vec<Veblen> = distinct.iter().map(|l| l.ordinal()).collect();
    let vanish = letters[0].is_top();
    let l = if vanish {
        1
    } else {
        let o1 = &ords[tokens[0]];
        (1..tokens.len()).find(|&i| ords[tokens[i]] < *o1).unwrap_or(tokens.len())
    };
    // 文字 a は括弧の対 (a) として書く（中身が空なら ()。Bracket の表示は空の語を ⊤ と書くので使えない）
    let letter = |id: usize| {
        let l = distinct[id];
        let t = if l.is_top() { "()".to_string() } else { format!("({l})") };
        json!({ "t": t, "o": ords[id].to_string() })
    };
    let part = |lo: usize, hi: usize| -> Value {
        fn nodes(pieces: &[repeats::Piece], toks: &[usize], letter: &dyn Fn(usize) -> Value) -> Value {
            Value::Array(
                pieces
                    .iter()
                    .map(|p| match p {
                        repeats::Piece::One(i) => letter(toks[*i]),
                        repeats::Piece::Rep(inner, k) => json!({ "r": nodes(inner, toks, letter), "k": k }),
                    })
                    .collect(),
            )
        }
        let toks = &tokens[lo..hi];
        nodes(&repeats::compress(toks), toks, &letter)
    };
    json!({ "vanish": vanish, "head": letter(tokens[0]), "copy": part(1, l), "rest": part(l, tokens.len()) })
}

/// 長すぎる LaTeX は送らない。
fn short_tex(s: String) -> Option<String> {
    (s.len() <= MAX_STEP_LATEX).then_some(s)
}

/// battle の表：先頭から、式の LaTeX の合計が上限に収まるところまで。
fn battle_table(rows: Vec<BattleRow>, name: &str, ord: Option<&str>, finished: bool) -> Value {
    let mut used = 0;
    let mut take = Vec::new();
    let total = rows.len();
    for r in rows {
        used += r.formula.len();
        // 空の式は「表に入れない」印（worm の battle で、表がいっぱいになった後のステップ）
        if (used > MAX_TABLE_LATEX || r.formula.is_empty()) && !take.is_empty() {
            break;
        }
        take.push(r);
    }
    let rows_in = take.len();
    let more = rows_in < total || !finished;
    json!({ "code": latex::battle_table(&take, name, ord, more), "rows": rows_in, "total": total })
}

/// battle を最大 `limit` ステップ進める。`kind` は "worm"・"bracket"・"rcbi"。
#[wasm_bindgen]
pub fn battle(kind: &str, input: &str, limit: u32) -> String {
    out(battle_impl(kind, input, limit.min(2000) as usize))
}

fn battle_impl(kind: &str, input: &str, limit: usize) -> Result<Value, String> {
    let mut steps = Vec::new();
    let mut rows: Vec<BattleRow> = Vec::new();
    let mut budget = TableBudget { used: 0, work: 0 };
    let mut stopped: Option<String> = None;
    let finished;
    match kind {
        "worm" => {
            // 繰り返しでまとめたまま進める（長さの上限はなく、順序数の大きさで止める）。
            // 各ステップは軽い情報だけを返し、見ているステップの形は battle_worm_view で取る
            let mut c = parse_cworm(input)?;
            let mut snaps = vec![c.clone()];
            let mut since_snap = 0u64;
            let mut m = 0u64;
            loop {
                let o = c.ordinal();
                let o_text = o.to_string();
                let len = c.len();
                // LaTeX の表：表に収まる所まで、まとめた形で
                if budget.used <= MAX_TABLE_LATEX {
                    let v = worm_view(&c);
                    budget.used += v.latex.len();
                    rows.push(BattleRow { formula: v.latex, ordinal: Some(o.to_latex()) });
                } else {
                    rows.push(BattleRow { formula: String::new(), ordinal: None });
                }
                steps.push(json!({
                    "length": len.to_decimal(),
                    "length_num": len.to_u64().map_or_else(|| 10f64.powf(len.log10()), |n| n as f64),
                    "ordinal": clip(&o_text, MAX_ORD_LISTED),
                    "ordinal_chars": o_text.chars().count(),
                }));
                if c.is_top() {
                    finished = true;
                    break;
                }
                if steps.len() > limit {
                    finished = false;
                    break;
                }
                if o_text.len() > MAX_ORD_CHARS || c.items() > MAX_ITEMS {
                    stopped = Some(if i18n::is_en() {
                        format!("stopped: the ordinal got longer than {MAX_ORD_CHARS} characters")
                    } else {
                        format!("順序数が {MAX_ORD_CHARS} 文字を超えたので打ち切り")
                    });
                    finished = false;
                    break;
                }
                m += 1;
                c.step(m);
                // SNAPSHOT_EVERY ステップごとに途中の状態を覚える（m = 50, 100, …）
                since_snap += 1;
                if since_snap == SNAPSHOT_EVERY {
                    snaps.push(c.clone());
                    since_snap = 0;
                }
            }
            // 見ているステップの形を返すために、途中の状態を覚えておく
            WORM_CACHE.with(|cache| *cache.borrow_mut() = Some(WormCache { input: input.trim().to_string(), snaps }));
        }
        "bracket" => {
            let b: Bracket = input.trim().parse().map_err(|e: wormlab_core::bracket::ParseBracketError| e.to_string())?;
            let mut ranks_memo: HashMap<Bracket, Veblen> = HashMap::new();
            let mut it = b.battle();
            loop {
                let Some(cur) = it.next() else {
                    finished = true;
                    break;
                };
                let text = cur.to_string();
                if text.len() > MAX_TEXT_LEN {
                    stopped = Some(if i18n::is_en() {
                        format!("stopped: the bracket word is longer than {MAX_TEXT_LEN} characters")
                    } else {
                        format!("括弧語が {MAX_TEXT_LEN} 文字を超えたので打ち切り")
                    });
                    finished = false;
                    break;
                }
                // 文字ごとの順序数の、異なる値の中での順位（棒グラフの高さに使う）
                let ords: Vec<Veblen> = cur
                    .letters()
                    .iter()
                    .map(|l| ranks_memo.entry(l.clone()).or_insert_with(|| l.ordinal()).clone())
                    .collect();
                let mut distinct = ords.clone();
                distinct.sort();
                distinct.dedup();
                let ranks: Vec<usize> = ords.iter().map(|o| distinct.binary_search(o).unwrap()).collect();
                let letters: Vec<String> = ords.iter().map(|o| o.to_string()).collect();
                let o = cur.ordinal();
                let f = cur.to_latex();
                let n = cur.letters().len();
                let tf = budget.formula(text.len() >= COMPACT_MIN_CHARS, n, || repeats::bracket(&cur).latex, &f);
                rows.push(BattleRow { formula: tf, ordinal: Some(o.to_latex()) });
                steps.push(json!({
                    "text": text,
                    "ordinal": o.to_string(),
                    "ranks": ranks,
                    "letter_ordinals": letters,
                    "latex": short_tex(f),
                    "ordinal_latex": o.to_latex(),
                }));
                if steps.len() > limit {
                    finished = false;
                    break;
                }
            }
        }
        "rcbi" => {
            let a = parse_wbi(input)?;
            let mut it = rcbi_order::battle(&a);
            loop {
                let Some(cur) = it.next() else {
                    finished = true;
                    break;
                };
                if cur.size() > MAX_FORMULA_SIZE {
                    stopped = Some(if i18n::is_en() {
                        format!("stopped: the formula has more than {MAX_FORMULA_SIZE} symbols")
                    } else {
                        format!("式の記号数が {MAX_FORMULA_SIZE} を超えたので打ち切り")
                    });
                    finished = false;
                    break;
                }
                let f = cur.to_latex();
                rows.push(BattleRow { formula: f.clone(), ordinal: None });
                steps.push(json!({ "text": cur.to_string(), "size": cur.size(), "latex": short_tex(f) }));
                if steps.len() > limit {
                    finished = false;
                    break;
                }
            }
        }
        _ => return Err(format!("{}: {kind}", tr("battle の種類が不明です", "unknown battle kind"))),
    }
    let table = match kind {
        "worm" => battle_table(rows, "A", Some("o(A_{k})"), finished),
        "bracket" => battle_table(rows, "a", Some("o^{*}(a_{k})"), finished),
        _ => battle_table(rows, "A", None, finished),
    };
    Ok(json!({ "kind": kind, "steps": steps, "finished": finished, "stopped": stopped, "latex_table": table }))
}

// ----------------------------------------------------------------------
// 証明
// ----------------------------------------------------------------------

/// 証明 DAG を JSON にする（結論と規則は表示用の文字列）。LaTeX（証明木と行番号つきの一覧）も付ける。
fn proof_json<J: Display + ToLatex, R: Display + ToLatex>(p: &Proof<J, R>, verdict: &str) -> Value {
    let nodes: Vec<Value> = p
        .nodes
        .iter()
        .map(|n| json!({ "rule": n.rule.to_string(), "premises": n.premises, "conclusion": n.conclusion.to_string() }))
        .collect();
    // 行番号つきの一覧は DAG のノード数の行になる。大きすぎるものは送らない
    let lines = (p.dag_size() <= 800).then(|| latex::proof_lines(p));
    json!({
        "root": p.root,
        "nodes": nodes,
        "dag_size": p.dag_size(),
        "tree_size": p.tree_size().to_string(),
        "height": p.height(),
        "latex": {
            "verdict": latex::display(verdict),
            "tree": latex::proof_tree(p, latex::TREE_LIMIT),
            "lines": lines,
            "tree_limit": latex::TREE_LIMIT.to_string(),
        },
    })
}

/// モデルを JSON にする（点の配置つき。Web の図と TikZ はこの配置を使う）。
fn model_json(v: &ModelView) -> Value {
    serde_json::to_value(v).unwrap_or_else(|e| json!({ "error": e.to_string() }))
}

/// RC の閉包モデル。`highlight` が真になる点に印を付ける。
fn rc_model_json<L: Letter>(m: &rc::Model<L>, highlight: Option<&Spf<L>>) -> Value {
    model_json(&ModelView::from_rc(m, highlight))
}

/// RC_BI の有限モデル M_A。
fn rcbi_model_json(m: &rcbi::Model, highlight: Option<&Formula>) -> Value {
    let mut v = model_json(&ModelView::from_rcbi(m, highlight));
    // フレーム条件の検査は総当たりで重いので、小さいモデルだけ
    let n = m.num_points();
    v["frame_violations"] = json!((n <= 120).then(|| m.frame_violations()));
    v
}

/// 判定と証明。`system` は "rc"・"wc"・"bc"・"bwc"・"rcbi"。
/// 成り立てば導出（RC_BI は判定だけ）、成り立たなければ反例モデルを返す。
#[wasm_bindgen]
pub fn prove(system: &str, sequent: &str) -> String {
    out(prove_impl(system, sequent))
}

fn rc_prove<L: Letter>(q: Sequent<L>) -> Result<Value, String> {
    let d = rc::decide(&q.lhs, &q.rhs);
    let verdict = latex::verdict(&q.lhs.to_latex(), &q.rhs.to_latex(), d.holds);
    if !d.holds {
        return Ok(json!({
            "holds": false, "sequent": d.sequent.to_string(), "latex": latex::display(&verdict),
            "model": rc_model_json(&d.model, Some(&q.rhs)),
        }));
    }
    let (p, st) = rcproof::derive(&q.lhs, &q.rhs)?;
    rcproof::check(&p).map_err(|e| format!("{}: {e}", tr("検査に失敗（バグです）", "the proof checker rejected the proof (a bug)")))?;
    Ok(json!({
        "holds": true, "sequent": d.sequent.to_string(), "latex": latex::display(&verdict),
        "proof": proof_json(&p, &verdict), "checked": true,
        "stats": { "facts_used": st.facts_used, "facts_total": st.facts_total },
    }))
}

fn wc_prove<L: Letter>(a: Worm<L>, b: Worm<L>) -> Result<Value, String> {
    let seq = format!("{a} ⊢ {b}");
    let holds = wc::decide(&a, &b);
    let verdict = latex::verdict(&a.to_latex(), &b.to_latex(), holds);
    if !holds {
        return Ok(json!({ "holds": false, "sequent": seq, "latex": latex::display(&verdict) }));
    }
    let p = wc::prove(&a, &b)?;
    wc::check(&p).map_err(|e| format!("{}: {e}", tr("検査に失敗（バグです）", "the proof checker rejected the proof (a bug)")))?;
    Ok(json!({
        "holds": true, "sequent": seq, "latex": latex::display(&verdict), "proof": proof_json(&p, &verdict), "checked": true,
    }))
}

fn prove_impl(system: &str, s: &str) -> Result<Value, String> {
    match system {
        "rc" => match s.parse::<Sequent>() {
            Ok(q) => rc_prove(q),
            Err(e) => match s.parse::<Sequent<Veblen>>() {
                Ok(q) => rc_prove(q),
                Err(_) => Err(e.to_string()),
            },
        },
        "wc" => {
            let (l, r) = s.split_once("⊢").or_else(|| s.split_once("|-")).ok_or(tr("'⊢' または '|-' が必要です", "expected '⊢' or '|-'"))?;
            match (l.trim().parse::<Worm>(), r.trim().parse::<Worm>()) {
                (Ok(a), Ok(b)) => wc_prove(a, b),
                _ => {
                    let a: Worm<Veblen> = l.trim().parse().map_err(|e: wormlab_core::worm::ParseWormError| e.to_string())?;
                    let b: Worm<Veblen> = r.trim().parse().map_err(|e: wormlab_core::worm::ParseWormError| e.to_string())?;
                    wc_prove(a, b)
                }
            }
        }
        "bc" => {
            let q: BSeq = s.parse().map_err(|e: bc::ParseError| e.to_string())?;
            let tau = q.tau();
            let holds = bc::decide(&q.lhs, &q.rhs);
            let verdict = latex::verdict(&q.lhs.to_latex(), &q.rhs.to_latex(), holds);
            if !holds {
                let d = rc::decide(&q.lhs.to_rc(), &q.rhs.to_rc());
                return Ok(json!({
                    "holds": false, "sequent": q.to_string(), "tau": tau.to_string(), "latex": latex::display(&verdict),
                    "model": rc_model_json(&d.model, Some(&q.rhs.to_rc())),
                }));
            }
            let (p, st) = bc::derive(&q.lhs, &q.rhs)?;
            bc::check(&p).map_err(|e| format!("{}: {e}", tr("検査に失敗（バグです）", "the proof checker rejected the proof (a bug)")))?;
            Ok(json!({
                "holds": true, "sequent": q.to_string(), "tau": tau.to_string(), "latex": latex::display(&verdict),
                "proof": proof_json(&p, &verdict), "checked": true,
                "stats": { "side_conditions": st.side_conditions, "max_side_depth": st.max_side_depth },
            }))
        }
        "bwc" => {
            let q: BwSeq = s.parse()?;
            let holds = bwc::decide(&q.lhs, &q.rhs);
            let verdict = latex::verdict(&q.lhs.to_latex(), &q.rhs.to_latex(), holds);
            if !holds {
                return Ok(json!({ "holds": false, "sequent": q.to_string(), "latex": latex::display(&verdict) }));
            }
            let (p, st) = bwc::prove(&q.lhs, &q.rhs)?;
            bwc::check(&p).map_err(|e| format!("{}: {e}", tr("検査に失敗（バグです）", "the proof checker rejected the proof (a bug)")))?;
            Ok(json!({
                "holds": true, "sequent": q.to_string(), "latex": latex::display(&verdict),
                "proof": proof_json(&p, &verdict), "checked": true,
                "stats": { "side_conditions": st.side_conditions, "max_side_depth": st.max_side_depth },
            }))
        }
        "rcbi" => {
            let q: rcbi::Sequent = s.parse().map_err(|e: rcbi::ParseError| e.to_string())?;
            check_size(&q.lhs)?;
            check_size(&q.rhs)?;
            let d = rcbi::decide(&q.lhs, &q.rhs)?;
            let verdict = latex::verdict(&q.lhs.to_latex(), &q.rhs.to_latex(), d.holds);
            Ok(json!({
                "holds": d.holds, "sequent": d.sequent.to_string(), "latex": latex::display(&verdict),
                "model": rcbi_model_json(&d.model, Some(&q.rhs)),
            }))
        }
        _ => Err(format!("{}: {system}", tr("体系が不明です", "unknown system"))),
    }
}

// ----------------------------------------------------------------------
// Kripke モデル
// ----------------------------------------------------------------------

/// RC の閉包モデル。入力は式 A か、シーケント A ⊢ B（B が真の点に印を付ける）。
#[wasm_bindgen]
pub fn rc_model(input: &str) -> String {
    out(rc_model_impl(input))
}

fn rc_model_generic<L: Letter>(a: Spf<L>, b: Option<Spf<L>>) -> Value {
    match b {
        Some(b) => {
            let d = rc::decide(&a, &b);
            let mut v = rc_model_json(&d.model, Some(&b));
            v["holds"] = json!(d.holds);
            v["title"] = json!(d.sequent.to_string());
            v
        }
        None => {
            let sig = a.modalities();
            let m = rc::Model::canonical(&a, &sig);
            let mut v = rc_model_json(&m, None);
            v["title"] = json!(a.to_string());
            v
        }
    }
}

fn rc_model_impl(input: &str) -> Result<Value, String> {
    let (l, r) = match input.split_once("⊢").or_else(|| input.split_once("|-")) {
        Some((l, r)) => (l, Some(r)),
        None => (input, None),
    };
    if let Ok(a) = l.parse::<Spf>() {
        let b = r.map(|r| r.parse::<Spf>()).transpose();
        if let Ok(b) = b {
            return Ok(rc_model_generic(a, b));
        }
    }
    let a: Spf<Veblen> = l.parse().map_err(|e: wormlab_core::spf::ParseError| e.to_string())?;
    let b = r.map(|r| r.parse::<Spf<Veblen>>()).transpose().map_err(|e| e.to_string())?;
    Ok(rc_model_generic(a, b))
}

/// RC_BI の有限モデル M_A。入力は変数のない式 A か、シーケント A ⊢ B。
#[wasm_bindgen]
pub fn rcbi_model(input: &str) -> String {
    out(rcbi_model_impl(input))
}

fn check_size(a: &Formula) -> Result<(), String> {
    if a.size() > 60 {
        return Err(if i18n::is_en() {
            format!("the formula is too large ({} symbols > 60); please try a smaller one in the browser", a.size())
        } else {
            format!("式が大きすぎます（記号数 {} > 60）。ブラウザでは小さめの式で試してください", a.size())
        });
    }
    Ok(())
}

fn rcbi_model_impl(input: &str) -> Result<Value, String> {
    if let Ok(q) = input.parse::<rcbi::Sequent>() {
        check_size(&q.lhs)?;
        check_size(&q.rhs)?;
        let d = rcbi::decide(&q.lhs, &q.rhs)?;
        let mut v = rcbi_model_json(&d.model, Some(&q.rhs));
        v["holds"] = json!(d.holds);
        v["title"] = json!(d.sequent.to_string());
        return Ok(v);
    }
    let a: Formula = input.parse().map_err(|e: rcbi::ParseError| e.to_string())?;
    check_size(&a)?;
    if !a.is_closed() {
        return Err(tr("M_A を作れるのは変数を含まない式だけです", "M_A exists only for closed formulas (without variables)").to_string());
    }
    let m = rcbi::Model::of(&a, a.max_rank());
    let mut v = rcbi_model_json(&m, None);
    v["title"] = json!(a.to_string());
    Ok(v)
}

/// モデル（[`rc_model`]・[`rcbi_model`]・[`prove`] が返した JSON の "model"）を TikZ にする。
/// `shown` は閉包後の辺も描く関係の名前の JSON 配列、`base` は骨組みの辺を描くか。
#[wasm_bindgen]
pub fn model_tikz(model: &str, shown: &str, base: bool) -> String {
    out((|| {
        let v: ModelView = serde_json::from_str(model).map_err(|e| format!("{}: {e}", tr("モデルを読めません", "cannot read the model")))?;
        let shown: Vec<String> = serde_json::from_str(shown).map_err(|e| format!("{}: {e}", tr("関係の名前を読めません", "cannot read the relation names")))?;
        Ok(json!({ "tikz": v.tikz(&shown, base) }))
    })())
}

/// LaTeX の断片を、プリアンブルつきの文書にする（JSON ではなく文字列をそのまま返す）。
/// 順序数の式（+・·・^・φ・ε・e^α・ψ）を、内側から 1 段ずつ標準形にする。各段に使った定義・規則を付ける。
#[wasm_bindgen]
pub fn ordinal_expr(input: &str) -> String {
    out((|| {
        let r = expr::eval_str(input)?;
        let steps: Vec<Value> = r
            .steps
            .iter()
            .take(MAX_EXPR_STEPS)
            .map(|st| {
                json!({
                    "node": clip(&st.node, MAX_EXPR_TEXT),
                    "value": clip(&st.value.to_string(), MAX_EXPR_TEXT),
                    "rule": st.rule,
                    "details": st.details.iter().map(|d| clip(d, MAX_EXPR_TEXT)).collect::<Vec<_>>(),
                    "whole": clip(&st.whole, MAX_EXPR_TEXT),
                    // 部分式が書き方まで標準形のまま（ω + 1 = ω + 1 など）。画面では薄く出す
                    "same": st.node == st.value.to_string(),
                })
            })
            .collect();
        let value = r.value.to_string();
        let tex = r.latex();
        Ok(json!({
            "input": clip(&r.input, MAX_EXPR_TEXT),
            "value": clip(&value, MAX_ORD_SHOWN),
            "value_chars": value.chars().count(),
            "value_latex": short_tex(r.value.to_latex()),
            "countable": r.value.is_countable(),
            "predicative": r.value.is_predicative(),
            "size": r.value.size(),
            "steps": steps,
            "steps_total": r.steps.len(),
            "latex": (tex.len() <= MAX_TABLE_LATEX).then_some(tex),
        }))
    })())
}

/// 順序数（Veblen の書き方の文字列）をまとめて別の標準形で書く。`texts` は文字列の JSON 配列、
/// `notation` は "veblen"・"phi"・"hyper"・"worm"・"bracket"・"iworm"。
/// 順序数として読めない文字列（式など）は、そのまま返す（`raw: true`）。
#[wasm_bindgen]
pub fn ordinal_render(texts: &str, notation: &str) -> String {
    out((|| {
        let n = Notation::parse(notation).ok_or_else(|| format!("{}: {notation}", tr("標準形の書き方が不明です", "unknown notation")))?;
        let list: Vec<String> = serde_json::from_str(texts).map_err(|e| format!("{}: {e}", tr("文字列の配列が必要です", "expected an array of strings")))?;
        if list.len() > MAX_RENDER_ITEMS {
            return Err(format!("{} ({MAX_RENDER_ITEMS})", tr("一度に変換できる数を超えました", "too many items at once")));
        }
        let v: Vec<Value> = list
            .iter()
            .map(|t| match t.parse::<Veblen>() {
                // 長すぎる数（battle の途中など）は書き換えない
                Ok(x) if t.chars().count() <= MAX_RENDER_CHARS => {
                    let r = notation::render(&x, n);
                    json!({ "text": clip(&r.text, MAX_ORD_SHOWN), "latex": short_tex(r.latex), "note": r.note, "raw": false })
                }
                _ => json!({ "text": t, "latex": null, "note": null, "raw": true }),
            })
            .collect();
        Ok(json!(v))
    })())
}

/// 標準形の書き方の一覧（選択肢の名前・説明・出典・例）。
#[wasm_bindgen]
pub fn ordinal_notations() -> String {
    out(Ok(json!(notation::notations())))
}

/// ordinal_render で一度に変換する数と、1 つの文字列の長さの上限。
const MAX_RENDER_ITEMS: usize = 500;
const MAX_RENDER_CHARS: usize = 3_000;

/// 定義集（Web の「定義」タブ）：ゲーム・順序数上の関数・表記と順序数・意味論の定義を分類ごとに（今の言語で）。
/// 各定義に文字の式・LaTeX・出典・関連・試せるタブ・wormlab-core で計算した例が付く。
#[wasm_bindgen]
pub fn glossary() -> String {
    out(Ok(json!(wormlab_core::glossary::all())))
}

/// 式の計算で使う定義の一覧（足し算・掛け算・べき乗・φ・ε・e^α・Ω・ψ・標準形。出典つき）。
#[wasm_bindgen]
pub fn ordinal_definitions() -> String {
    out(Ok(json!(expr::definitions())))
}

/// 式の計算の段として送る数の上限と、1 つの文字列の長さの上限。
const MAX_EXPR_STEPS: usize = 300;
const MAX_EXPR_TEXT: usize = 600;

/// 各体系（RC・WC・BC・BWC・RC_BI）の公理と規則の一覧（今の言語で）。
/// 規則ごとに 1 行の書き方 `text` も付ける（証明図の規則名のツールチップに使う）。
#[wasm_bindgen]
pub fn rules() -> String {
    let v: Vec<Value> = wormlab_core::rules::all()
        .iter()
        .map(|s| {
            let mut j = json!(s);
            // 【Rust メモ】`as_array_mut` は JSON の配列を書き換えられる形で取り出す（配列でなければ None）
            if let Some(groups) = j["groups"].as_array_mut() {
                for (g, src) in groups.iter_mut().zip(&s.groups) {
                    if let Some(rs) = g["rules"].as_array_mut() {
                        for (r, rule) in rs.iter_mut().zip(&src.rules) {
                            r["text"] = json!(rule.text());
                        }
                    }
                }
            }
            j
        })
        .collect();
    out(Ok(json!(v)))
}

#[wasm_bindgen]
pub fn latex_document(body: &str) -> String {
    latex::document(body)
}

// ----------------------------------------------------------------------
// RC_BI の順序と基本列
// ----------------------------------------------------------------------

fn parse_wbi(s: &str) -> Result<Formula, String> {
    let a: Formula = s.trim().parse().map_err(|e: rcbi::ParseError| e.to_string())?;
    if !a.in_wbi() {
        return Err(format!("{a} {}", tr("は W_BI の式ではありません（変数・∇・⟨1⟩_ω を含まない式だけ）", "is not a W_BI formula (only formulas without variables, ∇ or ⟨1⟩_ω)")));
    }
    check_size(&a)?;
    Ok(a)
}

/// RC_BI の式の形（零・後続・極限）と、基本列 (A)_1..k。
#[wasm_bindgen]
pub fn rcbi_info(input: &str, k: u32) -> String {
    out((|| {
        let a = parse_wbi(input)?;
        let (form, pred) = match rcbi_order::form(&a)? {
            rcbi_order::Form::Zero => ("zero", None),
            rcbi_order::Form::Successor(p) => ("successor", Some(p.to_string())),
            rcbi_order::Form::Limit => ("limit", None),
        };
        let approx: Vec<String> = if form == "limit" {
            (1..=k.clamp(1, 6)).map(|n| rcbi_order::approx(&a, n).expect("極限形").to_string()).collect()
        } else {
            Vec::new()
        };
        let tex = latex::rcbi_form(&a, k.clamp(1, 6))?;
        Ok(json!({ "formula": a.to_string(), "form": form, "predecessor": pred, "approximations": approx, "latex": tex }))
    })())
}

/// RC_BI の順序 <¹₁・≡¹₁ での比較。
#[wasm_bindgen]
pub fn rcbi_compare(a: &str, b: &str) -> String {
    out((|| {
        let (x, y) = (parse_wbi(a)?, parse_wbi(b)?);
        let o = rcbi_order::compare(&x, &y);
        let rel = match o {
            Some(std::cmp::Ordering::Less) => Some("<"),
            Some(std::cmp::Ordering::Equal) => Some("≡"),
            Some(std::cmp::Ordering::Greater) => Some(">"),
            None => None,
        };
        let tex = o.map(|o| latex::display(&latex::rcbi_relation(&x.to_latex(), o, &y.to_latex())));
        Ok(json!({ "a": x.to_string(), "b": y.to_string(), "relation": rel, "latex": tex }))
    })())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(s: &str) -> Value {
        serde_json::from_str(s).unwrap()
    }

    #[test]
    fn ordinal_calculator() {
        let v = parse(&ordinal_info("ordinal", "ε_0"));
        assert_eq!(v["ordinal"], "ε_0");
        assert_eq!(v["bracket"], "((()))");
        assert_eq!(v["is_limit"], true);
        assert_eq!(v["fundamental"].as_array().unwrap().len(), 6);
        let v = parse(&ordinal_info("worm", "2 0 1"));
        assert!(v["worm_finite"].is_string());
        let v = parse(&ordinal_info("bracket", "(())()"));
        assert_eq!(v["input"]["normal_form"], "(())");
        assert!(parse(&ordinal_info("ordinal", "ω^")).get("error").is_some());
        // Γ0 を超える：ψ と impredicative worm（括弧語は出さない）
        let v = parse(&ordinal_info("iworm", "((()))Ω"));
        assert_eq!(v["ordinal"], "ψ(ε_(Ω + 1))");
        assert_eq!(v["input"]["ordinal"], "ε_(Ω + 1)");
        assert!(v["bracket"].is_null() && v["predicative"] == false);
        let v = parse(&ordinal_info("ordinal", "ψ(Ω + ψ(Ω·2 + 1))"));
        assert_eq!(v["ordinal"], "ψ(Ω·2)");
        assert_eq!(v["iworm"], "Ω()Ω()Ω");
        let v = parse(&ordinal_info("ordinal", "ε_(Ω + 1)"));
        assert!(v["iworm"].is_null() && v["countable"] == false);
        assert_eq!(parse(&ordinal_compare("worm", "1 1", "ordinal", "ω^2"))["relation"], "=");
    }

    #[test]
    fn battles() {
        let v = parse(&battle("worm", "1 1", 100));
        assert_eq!(v["finished"], true);
        assert_eq!(v["steps"][0]["length"], "2");
        let w = parse(&battle_worm_view("1 1", 0));
        assert_eq!(w["tree"], json!([1, 1]));
        assert_eq!(w["text"], "1 1");
        let v = parse(&battle("bracket", "(())", 100));
        assert_eq!(v["steps"].as_array().unwrap().len(), 4); // ω → ()() → () → ⊤
        let v = parse(&battle("rcbi", "D T", 20));
        assert_eq!(v["finished"], true);
        let v = parse(&battle("worm", "3 3", 50));
        assert_eq!(v["finished"], false);
    }

    #[test]
    fn proofs_and_models() {
        let v = parse(&prove("rc", "<1>p & <0>q |- <1>(p & <0>q)"));
        assert_eq!(v["holds"], true);
        assert!(!v["proof"]["nodes"].as_array().unwrap().is_empty());
        let v = parse(&prove("rc", "<0>p |- <1>p"));
        assert_eq!(v["holds"], false);
        assert!(v["model"]["points"].as_array().is_some());
        let v = parse(&prove("wc", "1 1 |- 0 1 0 1"));
        assert_eq!(v["holds"], true);
        let v = parse(&prove("bc", "((()))p |- ()(())p"));
        assert_eq!(v["holds"], true);
        assert!(v["stats"]["side_conditions"].as_u64().unwrap() > 0);
        let v = parse(&prove("bwc", "((())) |- ()(())"));
        assert_eq!(v["holds"], true);
        assert!(v["stats"]["side_conditions"].as_u64().unwrap() > 0);
        assert_eq!(parse(&prove("bwc", "() |- (())"))["holds"], false);
        let v = parse(&prove("rcbi", "<2>_2 T |- <1> D T"));
        assert_eq!(v["holds"], true);
        assert_eq!(v["model"]["frame_violations"], json!([]));
        let v = parse(&rc_model("<2>p & <1>q"));
        assert_eq!(v["points"].as_array().unwrap().len(), 3);
        let v = parse(&rcbi_model("D <1> T"));
        assert_eq!(v["points"].as_array().unwrap().len(), 5);
        assert!(v["base_edges"].as_array().unwrap().len() >= 4);
    }

    #[test]
    fn latex_outputs() {
        let v = parse(&prove("rc", "<1>p & <0>q |- <1>(p & <0>q)"));
        let tree = v["proof"]["latex"]["tree"].as_str().unwrap();
        assert!(tree.starts_with("\\begin{prooftree}"));
        assert!(v["proof"]["latex"]["lines"].as_str().unwrap().contains("\\begin{array}"));
        let v = parse(&prove("rc", "<0>p |- <1>p"));
        assert!(v["latex"].as_str().unwrap().contains("\\nvdash"));
        // モデルを JSON で送り返して TikZ にする
        let model = v["model"].to_string();
        let t = parse(&model_tikz(&model, "[\"R_1\"]", true));
        assert!(t["tikz"].as_str().unwrap().contains("\\begin{tikzpicture}"));
        assert!(parse(&model_tikz("{}", "[]", true)).get("error").is_some());
        let v = parse(&ordinal_info("worm", "2 0 1"));
        assert!(v["latex"].as_str().unwrap().contains("\\begin{align*}"));
        let v = parse(&battle("worm", "1 1", 100));
        assert_eq!(parse(&battle_worm_view("1 1", 0))["latex"], "\\langle 1\\rangle\\langle 1\\rangle\\top");
        assert!(v["latex_table"]["code"].as_str().unwrap().contains("\\hline"));
        assert!(latex_document("x").contains("\\documentclass"));
        let v = parse(&rcbi_info("<2>_2<2>_3 T", 2));
        assert!(v["latex"].as_str().unwrap().contains("(A)_{2}"));
    }

    #[test]
    fn rcbi_order_api() {
        let v = parse(&rcbi_info("<2>_2<2>_3 T", 3));
        assert_eq!(v["form"], "limit");
        assert_eq!(v["approximations"].as_array().unwrap().len(), 3);
        assert_eq!(parse(&rcbi_compare("D T", "<2>_2 T"))["relation"], "<");
        assert!(parse(&rcbi_info("N T", 3)).get("error").is_some());
    }

    /// 英語にしたら、どの関数の出力（エラーを含む）にも日本語が残らない
    #[test]
    fn bracket_parts_roles() {
        for start in ["((()))", "(()(()))", "((())())", "(())()(())", "(()())"] {
            let b: Bracket = start.parse().unwrap();
            let all: Vec<Bracket> = b.battle().take(8).collect();
            for (k, pair) in all.windows(2).enumerate() {
                let (cur, next) = (&pair[0], &pair[1]);
                let v = parse(&battle_compact("bracket", &cur.to_string()))["parts"].clone();
                // 広げた copy の文字の並び
                fn flat(v: &Value, out: &mut Vec<String>) {
                    for x in v.as_array().unwrap() {
                        if let Some(t) = x.get("t") {
                            out.push(t.as_str().unwrap().to_string());
                        } else {
                            for _ in 0..x["k"].as_u64().unwrap() {
                                flat(&x["r"], out);
                            }
                        }
                    }
                }
                let (mut copy, mut rest) = (Vec::new(), Vec::new());
                flat(&v["copy"], &mut copy);
                flat(&v["rest"], &mut rest);
                // 文字 a は (a) と書いてある：つなげると元の語の文字列になる
                let as_letter = |l: &Bracket| if l.is_top() { "()".to_string() } else { format!("({l})") };
                let cur_ls: Vec<String> = cur.letters().iter().map(as_letter).collect();
                assert_eq!(cur_ls.concat(), cur.to_string());
                // 3 つの部分を並べると元の語
                let mut all3 = vec![v["head"]["t"].as_str().unwrap().to_string()];
                all3.extend(copy.iter().cloned());
                all3.extend(rest.iter().cloned());
                assert_eq!(all3, cur_ls, "{start} の {k} ステップ目");
                if v["vanish"] == true {
                    assert!(copy.is_empty());
                    assert_eq!(cur_ls[1..], next.letters().iter().map(as_letter).collect::<Vec<_>>()[..]);
                } else {
                    // 複製される部分は、次の語の 2 文字目から同じ並びで現れる
                    let next_ls: Vec<String> = next.letters().iter().map(as_letter).collect();
                    assert_eq!(next_ls[1..=copy.len()], copy[..], "{start} の {k} ステップ目");
                }
            }
        }
    }

    #[test]
    fn compact_steps() {
        // worm 3 の 32 ステップ目（3730 文字）は、まとめた形で短く書かれ、元の worm も付く
        let b = parse(&battle("worm", "3", 2000));
        let steps = b["steps"].as_array().unwrap();
        assert_eq!(steps[32]["length"], "3730");
        let last = parse(&battle_worm_view("3", 32));
        assert_eq!(last["length"], "3730");
        assert!(last["text"].as_str().unwrap().len() < 400, "{}", last["text"]);
        assert_eq!(last["plain"].as_str().unwrap().split(' ').count(), 3730);
        assert!(last["tree"].as_array().unwrap().iter().any(|x| x.get("k").is_some()));
        // 覚えておいた途中の状態から進めても、最初から進めても同じ
        let cached = parse(&battle_worm_view("3", 1234));
        WORM_CACHE.with(|c| *c.borrow_mut() = None);
        let fresh = parse(&battle_worm_view("3", 1234));
        assert_eq!(cached, fresh);
        assert_eq!(fresh["length"], steps[1234]["length"]);
        // 4000 文字の上限はなくなった：worm 3 は 2000 ステップ進められる（長さは 25 万文字を超える）
        assert_eq!(steps.len(), 2001);
        assert!(steps.last().unwrap()["length_num"].as_f64().unwrap() > 200_000.0);
        assert!(parse(&battle_worm_view("3", 2000))["plain"].is_null());
        // worm 4 は順序数が大きくなりすぎたところで止める
        let four = parse(&battle("worm", "4", 2000));
        assert!(four["stopped"].is_string());
        assert!(four["steps"].as_array().unwrap().len() > 50);
        // 括弧語は今まで通り、その場でまとめる
        let c = parse(&battle_compact("worm", "2 0 1 2 0 1 2 0 1"));
        assert_eq!(c["text"], "(2 0 1)^3");
        assert_eq!(parse(&battle_compact("bracket", "(())(())(())()"))["text"], "(())^3()");
        assert!(parse(&battle_compact("other", "1"))["error"].is_string());
        // 表は繰り返しでまとめた式なので、長い worm のステップも表に入る（30 ステップ目は 1000 文字を超える）
        assert!(b["latex_table"]["rows"].as_u64().unwrap() > 30);
        assert!(b["latex_table"]["code"].as_str().unwrap().contains("^{"));
    }

    #[test]
    fn arith_and_explore() {
        let r = parse(&ordinal_arith("*", "ordinal", "ω + 1", "ordinal", "ω"));
        assert_eq!(r["result"], "ω^2");
        assert_eq!(r["steps"].as_array().unwrap().last().unwrap()["text"], "ω^2");
        // worm・括弧語もその順序数で計算する：o(1 1) = ω、o*((())) = ω
        assert_eq!(parse(&ordinal_arith("^", "worm", "1 1", "bracket", "(())"))["result"], "ω^ω");
        assert!(parse(&ordinal_arith("^", "ordinal", "2", "ordinal", "64"))["error"].is_string());

        let e = parse(&ordinal_explore("ε_0", 2, 3, 1));
        assert_eq!(e["kind"], "limit");
        let fs: Vec<&str> = e["fundamental"].as_array().unwrap().iter().map(|x| x["value"].as_str().unwrap()).collect();
        assert_eq!(fs, ["ω", "ω^ω", "ω^ω^ω"]); // ε_0[n] = ω↑↑(n − 1)
        assert_eq!(e["worm_fundamental"].as_array().unwrap().len(), 3);
        // 標準 battle：ω·2 → ω + 1（[1]）→ ω（後続）→ ω[3] = 3 → 2 → 1 → 0 で 6 回
        let d = parse(&ordinal_explore("ω·2", 0, 1, 1));
        assert_eq!(d["descent"]["length"], "6");
        assert_eq!(d["descent"]["exact"], true);
        assert_eq!(d["descent"]["path"].as_array().unwrap().len(), 7);
        // ε0 から k = 1 で始めると ε0[1] = 1 なので 2 回（hierarchy.md の注意）。k = 3 からだと長い（下界だけ）
        assert_eq!(parse(&ordinal_explore("ε_0", 0, 1, 1))["descent"]["length"], "2");
        assert_eq!(parse(&ordinal_explore("ε_0", 0, 1, 3))["descent"]["exact"], false);
        // 後続順序数は直前の数、Ω・ψ を含む数は基本列なし
        assert_eq!(parse(&ordinal_explore("ω + 3", 0, 4, 1))["pred"], "ω + 2");
        assert_eq!(parse(&ordinal_explore("ψ(0)", 0, 4, 1))["defined"], false);
        assert!(parse(&ordinal_explore("ω", 501, 1, 1))["error"].is_string());
    }

    #[test]
    fn logo_worm_battle() {
        set_lang("ja");
        let v = parse(&logo_worm(0));
        assert_eq!(v["tree"], json!([2, 0, 2]));
        assert_eq!(v["ordinal"], "ω^ω·2");
        assert!(v["remaining"].as_str().unwrap().contains("2^119112383442468587833600313866377066101958502252541"));
        // 進めたり戻したりしても、同じステップなら同じ形（覚えた状態から進めても、最初からでも）
        let a = parse(&logo_worm(25));
        assert_eq!(a["tree"], json!([{ "r": [0], "k": 27 }, 2]));
        assert_eq!(a["length"], "28");
        let b = parse(&logo_worm(3));
        assert_eq!(b["tree"], json!([1, 0, 1, 0, 1, 0, 2]));
        assert_eq!(parse(&logo_worm(25)), a);
        assert!(parse(&logo_worm(2_000_000))["error"].is_string());
    }

    /// 残りのステップ数（閉じた形）が、標準形の worm から実際に動かした battle と合う。
    #[test]
    fn remaining_steps_match_the_battle() {
        // worm と、⊤ までの長さ（bc.md §3 の表：ω → 3、ω·2 → 11、ω² → 19、ω^ω → 51）
        for (w, total) in [("1", 3u64), ("1 0 1", 11), ("1 1", 19), ("2", 51)] {
            let mut c = parse_cworm(w).unwrap();
            let mut at = 0;
            loop {
                let rem = battle_remaining(&c, at).unwrap();
                assert_eq!(rem.exact(), Some(&BigNat::from(total - at)), "{w} at {at}");
                if !c.step(at + 1) {
                    break;
                }
                at += 1;
            }
            assert_eq!(at, total, "{w}");
        }
    }

    #[test]
    fn notations_render() {
        set_lang("ja");
        let v = parse(&ordinal_render(r#"["ε_0", "ψ(0) + 1", "ω·2 + 1", "x + 1"]"#, "hyper"));
        let a = v.as_array().unwrap();
        assert_eq!(a[0]["text"], "e^(e(1))(1)");
        assert_eq!(a[1]["text"], "ψ(0) + 1");
        assert_eq!(a[2]["text"], "e(1)·2 + 1");
        assert_eq!(a[3]["raw"], true);
        let b = parse(&ordinal_render(r#"["ψ(0)"]"#, "bracket"));
        assert!(b[0]["note"].is_string());
        assert!(parse(&ordinal_render("[]", "nothing"))["error"].is_string());
        assert_eq!(parse(&ordinal_notations()).as_array().unwrap().len(), 6);
    }

    #[test]
    fn expressions() {
        set_lang("ja");
        let v = parse(&ordinal_expr("e^(ω + 1)(1) + φ(1, φ(2, 0))"));
        assert_eq!(v["value"], "φ(2, 0)");
        assert_eq!(v["countable"], true);
        assert!(v["steps"].as_array().unwrap().iter().any(|s| s["rule"].as_str().unwrap().contains("超指数関数")));
        assert!(v["latex"].as_str().unwrap().contains("align*"));
        assert!(parse(&ordinal_expr("φ(1,"))["error"].is_string());
        let d = parse(&ordinal_definitions());
        let keys: Vec<&str> = d.as_array().unwrap().iter().map(|x| x["key"].as_str().unwrap()).collect();
        assert!(keys.contains(&"psi") && keys.contains(&"hyp") && keys.contains(&"phi"));
    }

    #[test]
    fn ordinal_inputs_are_expressions() {
        set_lang("ja");
        let r = parse(&ordinal_info("ordinal", "ψ(Ω^Ω)"));
        assert_eq!(r["ordinal"], "ψ(ω^ω^(Ω·2))");
        assert_eq!(r["input"]["text"], "ψ(Ω^Ω)");
        let r = parse(&ordinal_explore("ε_0·ω", 0, 3, 1));
        assert_eq!(r["ordinal"], "ω^(ε_0 + 1)");
        let r = parse(&ordinal_compare("ordinal", "Ω^Ω", "ordinal", "Ω·ω"));
        assert_eq!(r["relation"], ">");
        let r = parse(&ordinal_arith("+", "ordinal", "(ω + 1)^2", "ordinal", "1"));
        assert_eq!(r["result"], "ω^2 + ω + 2");
        let r = parse(&ordinal_info("worm", "<Ω^Ω>"));
        assert!(r.get("error").is_none(), "{r}");
        // 読めなければ、式としてのエラー
        assert!(parse(&ordinal_info("ordinal", "ω^"))["error"].is_string());
    }

    #[test]
    fn glossary_list() {
        set_lang("ja");
        let v = parse(&glossary());
        let cats = v.as_array().unwrap();
        assert_eq!(cats.len(), 5);
        let entries: Vec<&Value> = cats.iter().flat_map(|c| c["entries"].as_array().unwrap()).collect();
        assert!(entries.len() >= 40, "{}", entries.len());
        for e in &entries {
            assert!(e["latex"].as_str().unwrap().starts_with("\\begin{align*}"), "{}", e["key"]);
            assert!(e["lines"].as_array().is_some_and(|l| !l.is_empty()));
        }
        let wb = entries.iter().find(|e| e["key"] == "worm-battle").unwrap();
        assert_eq!(wb["tab"], "battle");
        // 例は場合ごとに {case, text}
        assert!(wb["examples"][0]["text"].as_str().unwrap().contains("1 1 0 2"));
        assert!(!wb["examples"][0]["case"].as_str().unwrap().is_empty());
        // 一般の場合と特殊な場合のリンク
        let fs = entries.iter().find(|e| e["key"] == "fs").unwrap();
        assert!(fs["special"].as_array().unwrap().iter().any(|k| k == "cnf-fs"));
    }

    #[test]
    fn worm_fs_figure_parts() {
        set_lang("ja");
        let v = parse(&worm_fs_figure("2 0 2", 1));
        assert_eq!((v["head"].as_u64(), v["cut"].as_u64()), (Some(2), Some(1)));
        assert_eq!(v["result_text"], "1 1 0 2");
        assert_eq!(v["result"], json!([1, 1, 0, 2]));
        assert_eq!((v["ordinal"].as_str(), v["result_ordinal"].as_str()), (Some("ω^ω·2"), Some("ω^ω + ω^2")));
        // A = 0B は先頭の 0 が消えるだけ、h 未満の文字がなければ U = ⊤
        let z = parse(&worm_fs_figure("0 2 1", 3));
        assert_eq!((z["head"].as_u64(), z["cut"].as_u64(), z["result_text"].as_str()), (Some(0), Some(1), Some("2 1")));
        let t = parse(&worm_fs_figure("1 2", 2));
        assert_eq!((t["cut"].as_u64(), t["result_text"].as_str()), (Some(2), Some("0 2 0 2 0 2")));
        // ⊤、大きすぎる n・文字・長さ、順序数の文字は断る
        for (w, n) in [("⊤", 1), ("1", 10), ("21", 1), ("<ω>", 1)] {
            assert!(parse(&worm_fs_figure(w, n))["error"].is_string(), "{w} {n}");
        }
        assert!(parse(&worm_fs_figure(&vec!["1"; 41].join(" "), 0))["error"].is_string());
    }

    #[test]
    fn rule_lists() {
        set_lang("ja");
        let v = parse(&rules());
        let systems = v.as_array().unwrap();
        assert_eq!(systems.len(), 5);
        assert_eq!(systems[0]["id"], "rc");
        // どの規則にも 1 行の書き方がある
        for s in systems {
            for g in s["groups"].as_array().unwrap() {
                for r in g["rules"].as_array().unwrap() {
                    assert!(r["text"].as_str().is_some_and(|t| t.contains('⊢')), "{r}");
                }
            }
        }
        let bwc = &systems[3];
        assert_eq!(bwc["groups"][1]["rules"][3]["name"], "R3");
        assert_eq!(bwc["groups"][1]["rules"][3]["side"][0], "y ⊢ ()x");
        assert_eq!(bwc["derivations"], true);
        assert_eq!(systems[4]["derivations"], false);
    }

    #[test]
    fn english_output_has_no_japanese() {
        set_lang("en");
        let model = rcbi_model("D <1> T");
        let model_json = parse(&model)["model"].to_string();
        let outputs = vec![
            ordinal_info("ordinal", "ε_0"),
            ordinal_info("ordinal", "ω^3"),
            ordinal_info("ordinal", "ψ(Ω + ψ(Ω·2 + 1))"),
            ordinal_info("worm", "2 0 1"),
            ordinal_info("worm", "<ω><ω>"),
            ordinal_info("bracket", "(())()"),
            ordinal_info("iworm", "((()))Ω"),
            ordinal_info("ordinal", "ω^"),
            ordinal_info("worm", "x"),
            ordinal_info("bracket", "(()"),
            ordinal_info("iworm", "(Ω"),
            ordinal_info("iworm", "Ω)"),
            ordinal_info("ordinal", ""),
            ordinal_info("other", "1"),
            ordinal_compare("worm", "1 1", "ordinal", "ω^2"),
            glossary(),
            ordinal_arith("+", "ordinal", "ω^2 + ω + 1", "ordinal", "ω^2·3 + 1"),
            ordinal_arith("+", "ordinal", "ω^2", "ordinal", "ω^2"),
            ordinal_arith("+", "ordinal", "ω", "ordinal", "1"),
            ordinal_arith("+", "ordinal", "0", "ordinal", "1"),
            ordinal_arith("*", "ordinal", "ω + 1", "ordinal", "ω·2 + 3"),
            ordinal_arith("*", "ordinal", "2", "ordinal", "ω"),
            ordinal_arith("*", "ordinal", "0", "ordinal", "ω"),
            ordinal_arith("^", "ordinal", "ε_0 + ω", "ordinal", "ω + 2"),
            ordinal_arith("^", "ordinal", "3", "ordinal", "ω^2 + ω + 4"),
            ordinal_arith("^", "ordinal", "ω", "ordinal", "0"),
            ordinal_arith("^", "ordinal", "0", "ordinal", "ω"),
            ordinal_arith("^", "ordinal", "1", "ordinal", "ω"),
            ordinal_arith("^", "ordinal", "2", "ordinal", "Ω + 64"),
            ordinal_arith("^", "ordinal", "ω + 1", "ordinal", "1000000000"),
            ordinal_arith("%", "ordinal", "1", "ordinal", "1"),
            ordinal_arith("+", "worm", "1 1", "bracket", "(())"),
            ordinal_explore("ε_0", 0, 8, 1),
            ordinal_explore("ω + 3", 0, 8, 1),
            ordinal_explore("0", 0, 8, 1),
            ordinal_explore("ψ(0)", 0, 8, 3),
            ordinal_explore("ω^ω", 600, 5, 1),
            ordinal_explore("ω^", 0, 5, 1),
            ordinal_explore("ε_0", 0, 3, 3),
            battle("worm", "2 0 2", 50),
            rules(),
            ordinal_expr("e^(ω + 1)(1) + φ(1, φ(2, 0)) + ψ(Ω + ψ(Ω·2 + 1)) + 1 + ω + (ω + 1)^2 + ψ(0) + φ(Ω, 0) + ω^ε_0"),
            ordinal_expr("e^1000000(1)"),
            ordinal_expr("(ω + 1)^1000000000"),
            ordinal_expr("φ(1,"),
            ordinal_expr("e^ω"),
            ordinal_definitions(),
            ordinal_notations(),
            ordinal_render(r#"["ψ(0)", "ω·1000000000", "Ω"]"#, "bracket"),
            ordinal_render(r#"["ω·1000000000"]"#, "worm"),
            ordinal_render(r#"["Ω"]"#, "iworm"),
            ordinal_render("[]", "nothing"),
            ordinal_render("x", "worm"),
            logo_worm(10),
            logo_worm(5_000_000),
            battle_compact("worm", "1 2"),
            battle_worm_view("3", 40),
            battle_worm_view("1 x", 0),
            battle_worm_view("200", 0),
            battle_compact("worm", "1 x"),
            battle_compact("bracket", "(()"),
            battle_compact("other", "1"),
            battle("worm", "3", 2000),
            battle("bracket", "((()))", 40),
            battle("rcbi", "D T", 10),
            battle("other", "1", 1),
            prove("rc", "<1>p & <0>q |- <1>(p & <0>q)"),
            prove("rc", "<0>p |- <1>p"),
            prove("rc", "<0>p"),
            prove("rc", "<0>(p |- q"),
            prove("rc", "<0>P |- q"),
            prove("wc", "2 0 |- 1"),
            prove("wc", "1 |- 2"),
            prove("bc", "((()))p |- ()(())p"),
            prove("bc", "(()p |- q"),
            prove("bwc", "((())) |- ()(())"),
            prove("bwc", "() |- (())"),
            prove("rcbi", "D T |- <1>_w T"),
            prove("rcbi", "<3>_2 T |- T"),
            prove("rcbi", "<1>_x T |- T"),
            prove("other", "T |- T"),
            rc_model("<0>p |- <1>p"),
            model,
            rcbi_model("<2>_2 T |- D T"),
            rcbi_model("p"),
            rcbi_model(&"D ".repeat(70)),
            model_tikz(&model_json, "[]", true),
            model_tikz("{", "[]", true),
            rcbi_info("<2>_2 T", 3),
            rcbi_info("<1><1> T", 3),
            rcbi_info("N T", 3),
            rcbi_compare("<1>_3<2>_3 T", "<2>_2<2>_3 T"),
        ];
        set_lang("ja");
        let japanese = |c: char| ('\u{3040}'..='\u{30ff}').contains(&c) || ('\u{4e00}'..='\u{9fff}').contains(&c);
        for o in &outputs {
            assert!(!o.chars().any(japanese), "日本語が残っている：{}", &o[..o.len().min(400)]);
        }
        // 日本語に戻せば日本語
        assert!(ordinal_info("ordinal", "ω^").chars().any(japanese));
    }
}
