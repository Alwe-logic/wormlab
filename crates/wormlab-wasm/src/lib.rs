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
use wormlab_core::bitset::BitSet;
use wormlab_core::hierarchy::{self, Budget};
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
    Ok(json!({
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
        let (x, y) = (parse_input(kind_a, a)?.ordinal(), parse_input(kind_b, b)?.ordinal());
        let rel = match x.cmp(&y) {
            std::cmp::Ordering::Less => "<",
            std::cmp::Ordering::Equal => "=",
            std::cmp::Ordering::Greater => ">",
        };
        Ok(json!({ "a": x.to_string(), "b": y.to_string(), "relation": rel }))
    })())
}

// ----------------------------------------------------------------------
// battle
// ----------------------------------------------------------------------

/// worm の文字数・括弧語の文字数・式の記号数の上限（ブラウザが固まらないように）。
const MAX_WORM_LEN: usize = 4000;
const MAX_TEXT_LEN: usize = 6000;
const MAX_FORMULA_SIZE: usize = 120;

/// battle を最大 `limit` ステップ進める。`kind` は "worm"・"bracket"・"rcbi"。
#[wasm_bindgen]
pub fn battle(kind: &str, input: &str, limit: u32) -> String {
    out(battle_impl(kind, input, limit.min(2000) as usize))
}

fn battle_impl(kind: &str, input: &str, limit: usize) -> Result<Value, String> {
    let mut steps = Vec::new();
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
                steps.push(json!({
                    "letters": cur.letters(),
                    "ordinal": cur.ordinal().to_string(),
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
                steps.push(json!({
                    "text": text,
                    "ordinal": cur.ordinal().to_string(),
                    "ranks": ranks,
                    "letter_ordinals": letters,
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
                steps.push(json!({ "text": cur.to_string(), "size": cur.size() }));
                if steps.len() > limit {
                    finished = false;
                    break;
                }
            }
        }
        _ => return Err(format!("battle の種類が不明です: {kind}")),
    }
    Ok(json!({ "kind": kind, "steps": steps, "finished": finished, "stopped": stopped }))
}

// ----------------------------------------------------------------------
// 証明
// ----------------------------------------------------------------------

/// 証明 DAG を JSON にする（結論と規則は表示用の文字列）。
fn proof_json<J: Display, R: Display>(p: &Proof<J, R>) -> Value {
    let nodes: Vec<Value> = p
        .nodes
        .iter()
        .map(|n| json!({ "rule": n.rule.to_string(), "premises": n.premises, "conclusion": n.conclusion.to_string() }))
        .collect();
    json!({
        "root": p.root,
        "nodes": nodes,
        "dag_size": p.dag_size(),
        "tree_size": p.tree_size().to_string(),
        "height": p.height(),
    })
}

/// 行の集合を辺のリストにする。
fn edges_of(rows: &[BitSet]) -> Vec<[usize; 2]> {
    rows.iter().enumerate().flat_map(|(x, row)| row.iter().map(move |y| [x, y])).collect()
}

/// RC の閉包モデルを JSON にする。`highlight` が真になる点に印を付ける。
fn rc_model_json<L: Letter>(m: &rc::Model<L>, highlight: Option<&Spf<L>>) -> Value {
    let n = m.num_points();
    let points: Vec<Value> = (0..n)
        .map(|x| {
            let vars: Vec<&String> = m.label(x).iter().collect();
            json!({ "id": x, "label": vars.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(","), "kind": "点" })
        })
        .collect();
    let relations: Vec<Value> = m
        .signature()
        .iter()
        .map(|l| {
            let edges: Vec<[usize; 2]> =
                (0..n).flat_map(|x| (0..n).filter(move |&y| m.related(l, x, y)).map(move |y| [x, y])).collect();
            json!({ "name": format!("R_{l}"), "edges": edges })
        })
        .collect();
    let base: Vec<Value> = m.tree_edges().iter().map(|(x, l, y)| json!([x, format!("R_{l}"), y])).collect();
    let hl: Vec<usize> = highlight.map(|b| m.truth_set(b).iter().collect()).unwrap_or_default();
    json!({ "root": 0, "points": points, "relations": relations, "base_edges": base, "highlight": hl })
}

/// RC_BI の有限モデル M_A を JSON にする。
fn rcbi_model_json(m: &rcbi::Model, highlight: Option<&Formula>) -> Value {
    let n = m.num_points();
    let points: Vec<Value> = (0..n)
        .map(|x| {
            let kind = match m.kind(x) {
                rcbi::PointKind::Tree => "構文木".to_string(),
                rcbi::PointKind::Zero => "零点".to_string(),
                rcbi::PointKind::Intermediate => "中間点".to_string(),
                rcbi::PointKind::Copy(b) => format!("{b} のコピー点"),
            };
            json!({ "id": x, "label": "", "kind": kind, "anchor": m.anchor(x) })
        })
        .collect();
    let relations: Vec<Value> =
        m.relations().into_iter().map(|(name, rows)| json!({ "name": name, "edges": edges_of(rows) })).collect();
    let base: Vec<Value> = m.base_edges().into_iter().map(|(x, name, y)| json!([x, name, y])).collect();
    let hl: Vec<usize> = highlight.map(|b| m.truth_set(b).iter().collect()).unwrap_or_default();
    // フレーム条件の検査は総当たりで重いので、小さいモデルだけ
    let violations: Option<Vec<String>> = (n <= 120).then(|| m.frame_violations());
    json!({
        "root": 0, "points": points, "relations": relations, "base_edges": base, "highlight": hl,
        "frame_violations": violations,
    })
}

/// 判定と証明。`system` は "rc"・"wc"・"bc"・"rcbi"。
/// 成り立てば導出（RC_BI は判定だけ）、成り立たなければ反例モデルを返す。
#[wasm_bindgen]
pub fn prove(system: &str, sequent: &str) -> String {
    out(prove_impl(system, sequent))
}

fn rc_prove<L: Letter>(q: Sequent<L>) -> Result<Value, String> {
    let d = rc::decide(&q.lhs, &q.rhs);
    if !d.holds {
        return Ok(json!({ "holds": false, "sequent": d.sequent.to_string(), "model": rc_model_json(&d.model, Some(&q.rhs)) }));
    }
    let (p, st) = rcproof::derive(&q.lhs, &q.rhs)?;
    rcproof::check(&p).map_err(|e| format!("検査に失敗（バグです）: {e}"))?;
    Ok(json!({
        "holds": true, "sequent": d.sequent.to_string(), "proof": proof_json(&p), "checked": true,
        "stats": { "facts_used": st.facts_used, "facts_total": st.facts_total },
    }))
}

fn wc_prove<L: Letter>(a: Worm<L>, b: Worm<L>) -> Result<Value, String> {
    let seq = format!("{a} ⊢ {b}");
    if !wc::decide(&a, &b) {
        return Ok(json!({ "holds": false, "sequent": seq }));
    }
    let p = wc::prove(&a, &b)?;
    wc::check(&p).map_err(|e| format!("検査に失敗（バグです）: {e}"))?;
    Ok(json!({ "holds": true, "sequent": seq, "proof": proof_json(&p), "checked": true }))
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
            if !bc::decide(&q.lhs, &q.rhs) {
                let d = rc::decide(&q.lhs.to_rc(), &q.rhs.to_rc());
                return Ok(json!({
                    "holds": false, "sequent": q.to_string(), "tau": tau.to_string(),
                    "model": rc_model_json(&d.model, Some(&q.rhs.to_rc())),
                }));
            }
            let (p, st) = bc::derive(&q.lhs, &q.rhs)?;
            bc::check(&p).map_err(|e| format!("検査に失敗（バグです）: {e}"))?;
            Ok(json!({
                "holds": true, "sequent": q.to_string(), "tau": tau.to_string(), "proof": proof_json(&p), "checked": true,
                "stats": { "side_conditions": st.side_conditions, "max_side_depth": st.max_side_depth },
            }))
        }
        "rcbi" => {
            let q: rcbi::Sequent = s.parse().map_err(|e: rcbi::ParseError| e.to_string())?;
            check_size(&q.lhs)?;
            check_size(&q.rhs)?;
            let d = rcbi::decide(&q.lhs, &q.rhs)?;
            Ok(json!({ "holds": d.holds, "sequent": d.sequent.to_string(), "model": rcbi_model_json(&d.model, Some(&q.rhs)) }))
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
        Ok(json!({ "formula": a.to_string(), "form": form, "predecessor": pred, "approximations": approx }))
    })())
}

/// RC_BI の順序 <¹₁・≡¹₁ での比較。
#[wasm_bindgen]
pub fn rcbi_compare(a: &str, b: &str) -> String {
    out((|| {
        let (x, y) = (parse_wbi(a)?, parse_wbi(b)?);
        let rel = match rcbi_order::compare(&x, &y) {
            Some(std::cmp::Ordering::Less) => Some("<"),
            Some(std::cmp::Ordering::Equal) => Some("≡"),
            Some(std::cmp::Ordering::Greater) => Some(">"),
            None => None,
        };
        Ok(json!({ "a": x.to_string(), "b": y.to_string(), "relation": rel }))
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
    fn rcbi_order_api() {
        let v = parse(&rcbi_info("<2>_2<2>_3 T", 3));
        assert_eq!(v["form"], "limit");
        assert_eq!(v["approximations"].as_array().unwrap().len(), 3);
        assert_eq!(parse(&rcbi_compare("D T", "<2>_2 T"))["relation"], "<");
        assert!(parse(&rcbi_info("N T", 3)).get("error").is_some());
    }
}
