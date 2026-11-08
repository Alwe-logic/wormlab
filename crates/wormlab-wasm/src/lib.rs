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
use wormlab_core::bc::{self, BSeq};
use wormlab_core::hierarchy::{self, Budget};
use wormlab_core::latex::{self, BattleRow, ToLatex};
use wormlab_core::modelview::ModelView;
use wormlab_core::proof::Proof;
use wormlab_core::rcbi::{self, Formula};
use wormlab_core::{Bracket, Letter, Sequent, Spf, Veblen, Worm, rc, rcbi_order, rcproof, wc};

/// 結果を JSON の文字列にする。エラーは `{"error": …}`。
fn out(r: Result<Value, String>) -> String {
    match r {
        Ok(v) => v.to_string(),
        Err(e) => json!({ "error": e }).to_string(),
    }
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
}

/// `kind` は "ordinal"・"worm"・"bracket" のどれか。
fn parse_input(kind: &str, s: &str) -> Result<Input, String> {
    let s = s.trim();
    if s.is_empty() {
        return Err("入力が空です".to_string());
    }
    match kind {
        "ordinal" => s.parse::<Veblen>().map(Input::Ordinal).map_err(|e| e.to_string()),
        "worm" => match s.parse::<Worm>() {
            Ok(w) => Ok(Input::Worm(w)),
            Err(_) => s.parse::<Worm<Veblen>>().map(Input::OWorm).map_err(|e| e.to_string()),
        },
        "bracket" => s.parse::<Bracket>().map(Input::Bracket).map_err(|e| e.to_string()),
        _ => Err(format!("入力の種類が不明です: {kind}")),
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
        }
    }

    fn ordinal(&self) -> Veblen {
        match self {
            Input::Ordinal(a) => a.clone(),
            Input::Worm(w) => Veblen::from(&w.ordinal()),
            Input::OWorm(w) => w.ordinal(),
            Input::Bracket(b) => b.ordinal(),
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
        Input::Ordinal(v) => json!({ "kind": "ordinal", "text": v.to_string() }),
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
    // 値が大きすぎて打ち切ったら、そこから先の n は計算しない
    let budget = Budget { max_steps: 20_000 };
    let mut hardy: Vec<Value> = Vec::new();
    if a.to_cnf().is_some() {
        for n in 1..=5u128 {
            let v = hierarchy::hardy(&a, n, budget);
            hardy.push(json!({ "n": n.to_string(), "value": v.map(|v| v.to_string()) }));
            if v.is_none() {
                break;
            }
        }
    }
    let bracket = Bracket::from_ordinal(&a);
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
        "bracket": bracket.to_string(),
        "bracket_depth": bracket.depth(),
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

// ----------------------------------------------------------------------
// battle
// ----------------------------------------------------------------------

/// worm の文字数・括弧語の文字数・式の記号数の上限（ブラウザが固まらないように）。
const MAX_WORM_LEN: usize = 4000;
const MAX_TEXT_LEN: usize = 6000;
const MAX_FORMULA_SIZE: usize = 120;
/// 1 ステップの式の LaTeX をこれより長くは送らない（長い worm は数万文字になる）。
const MAX_STEP_LATEX: usize = 1500;
/// battle の LaTeX の表に入れる式の文字数の合計の上限。
const MAX_TABLE_LATEX: usize = 30_000;

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
        if used > MAX_TABLE_LATEX && !take.is_empty() {
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
    let mut stopped: Option<String> = None;
    let finished;
    match kind {
        "worm" => {
            let w: Worm = input.trim().parse().map_err(|e: wormlab_core::worm::ParseWormError| e.to_string())?;
            let mut it = w.battle();
            loop {
                let Some(cur) = it.next() else {
                    finished = true;
                    break;
                };
                if cur.letters().len() > MAX_WORM_LEN {
                    stopped = Some(format!("worm が {MAX_WORM_LEN} 文字を超えたので打ち切り"));
                    finished = false;
                    break;
                }
                let o = cur.ordinal();
                let f = cur.to_latex();
                rows.push(BattleRow { formula: f.clone(), ordinal: Some(o.to_latex()) });
                steps.push(json!({
                    "letters": cur.letters(),
                    "ordinal": o.to_string(),
                    "latex": short_tex(f),
                    "ordinal_latex": o.to_latex(),
                }));
                if steps.len() > limit {
                    finished = false;
                    break;
                }
            }
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
                    stopped = Some(format!("括弧語が {MAX_TEXT_LEN} 文字を超えたので打ち切り"));
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
                rows.push(BattleRow { formula: f.clone(), ordinal: Some(o.to_latex()) });
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
                    stopped = Some(format!("式の記号数が {MAX_FORMULA_SIZE} を超えたので打ち切り"));
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
        _ => return Err(format!("battle の種類が不明です: {kind}")),
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

/// 判定と証明。`system` は "rc"・"wc"・"bc"・"rcbi"。
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
    rcproof::check(&p).map_err(|e| format!("検査に失敗（バグです）: {e}"))?;
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
    wc::check(&p).map_err(|e| format!("検査に失敗（バグです）: {e}"))?;
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
            let (l, r) = s.split_once("⊢").or_else(|| s.split_once("|-")).ok_or("'⊢' または '|-' が必要です")?;
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
            bc::check(&p).map_err(|e| format!("検査に失敗（バグです）: {e}"))?;
            Ok(json!({
                "holds": true, "sequent": q.to_string(), "tau": tau.to_string(), "latex": latex::display(&verdict),
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
        _ => Err(format!("体系が不明です: {system}")),
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
        return Err(format!("式が大きすぎます（記号数 {} > 60）。ブラウザでは小さめの式で試してください", a.size()));
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
        return Err("M_A を作れるのは変数を含まない式だけです".to_string());
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
        let v: ModelView = serde_json::from_str(model).map_err(|e| format!("モデルを読めません: {e}"))?;
        let shown: Vec<String> = serde_json::from_str(shown).map_err(|e| format!("関係の名前を読めません: {e}"))?;
        Ok(json!({ "tikz": v.tikz(&shown, base) }))
    })())
}

/// LaTeX の断片を、プリアンブルつきの文書にする（JSON ではなく文字列をそのまま返す）。
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
        return Err(format!("{a} は W_BI の式ではありません（変数・∇・⟨1⟩_ω を含まない式だけ）"));
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
        assert_eq!(parse(&ordinal_compare("worm", "1 1", "ordinal", "ω^2"))["relation"], "=");
    }

    #[test]
    fn battles() {
        let v = parse(&battle("worm", "1 1", 100));
        assert_eq!(v["finished"], true);
        assert_eq!(v["steps"][0]["letters"], json!([1, 1]));
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
        assert_eq!(v["steps"][0]["latex"], "\\langle 1\\rangle\\langle 1\\rangle\\top");
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
}
