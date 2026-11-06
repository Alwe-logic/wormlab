//! wormlab コマンドラインツール
//!
//! 使い方：
//!   wormlab ord    "1 0 2"          worm の順序数・標準形・Π 順序数を表示（--json 可）
//!   wormlab table  "1 0" "2" …      複数の worm を CSV で（引数がなければ標準入力から 1 行 1 worm）
//!   wormlab cmp    "1 1" "2"        2 つの worm を <_0 で比較（--json 可）
//!   wormlab battle "1 1 1" [上限]    worm battle を実行
//!   wormlab rc     "<2>p |- <0><1>p" RC で判定。真なら導出を作って検査、偽なら反例モデル
//!                                    （--proof で導出の全行、--json で JSON。<ω+1> などの順序数も可）
//!   wormlab lt     1 "0 2" "1"       一般の worm で A <_n B か
//!   wormlab wc     "1 1 |- 0 1 0 1"  worm シーケントの WC 証明（--json で JSON）
//!   wormlab wclt   0 "1 1" "2"       A <_n B（B ⊢ nA）の WC 証明
//!   wormlab ordinal "ω^ε_0 + 1"      Γ0 未満の順序数を正規形にする（2 つ渡すと比較）
//!   wormlab bracket "((()))"         括弧語の順序数・翻訳・正規形（--json 可）
//!   wormlab bracketof "ε_0 + 1"      順序数を正規形の括弧語にする
//!   wormlab bcmp "((()))" "(()())"   括弧語を順序数を使わずに比較（Veblen 経由の比較と照合）
//!   wormlab bc "((()))p |- ()(())p"  Bracket Calculus で判定。真なら BC の導出を作って検査
//!                                    （--proof で導出の全行、--json で JSON）
//!   wormlab bbattle "(())()" [上限]  括弧語の battle（基本列を繰り返す）
//!   wormlab thm52 3                  Thm 52（ATR₀ から独立）の出発点 a'_m
//!   wormlab bi "<2>_2 T |- <1> D T"  RC_BI（Pakhomov–Lazar）で判定（変数なしの式。--model で M_A を表示）
//!   wormlab bimodel "D <1> T"        RC_BI の有限モデル M_A とフレーム条件の検査
//!   wormlab bicmp "D T" "<2>_2 T"    RC_BI の順序 <¹₁（B ⊢ ⟨1⟩₁A）・≡¹₁（∇A ⊣⊢ ∇B）で比較
//!   wormlab bifs "<2>_2 T" [k]       式の形（零・後続・極限）と基本列 (A)_1..k（Def 4.6）
//!   wormlab bibattle "<1>_2 T" [上限] RC_BI の式の battle（後続なら直前、極限なら (A)_{k+1}）
//!   wormlab fs "ε_0" [k]             標準の基本列 α[0..k] と、worm が作る列の比較
//!   wormlab hardy "ω^2" 10           Hardy 関数 H_α(n) と急増加関数 f_α(n)
//!   wormlab blen "ω^2 + ω"           worm battle と標準 battle の長さ
//!
//! ord・cmp・lt・wc・wclt は、文字が順序数の worm（例 "<ω+1><0><ε_0>"）も受け付ける。

use serde_json::json;
use std::cmp::Ordering;
use std::io::BufRead;
use std::process::ExitCode;
use wormlab_core::wc::{self, WcProof};
use wormlab_core::hierarchy::{self, Budget};
use wormlab_core::bc::{self, BSeq};
use wormlab_core::{Bracket, Letter, Sequent, Veblen, Worm, headbody, rc, rcbi, rcbi_order, rcproof};

fn parse_ordinal(s: &str) -> Result<Veblen, String> {
    s.parse::<Veblen>().map_err(|e| e.to_string())
}

fn parse_bracket(s: &str) -> Result<Bracket, String> {
    s.parse::<Bracket>().map_err(|e| e.to_string())
}

/// 長い語は先頭だけ表示する。
fn shorten(s: String, max: usize) -> String {
    let n = s.chars().count();
    if n <= max { s } else { format!("{} …（{} 文字）", s.chars().take(max).collect::<String>(), n) }
}

fn parse(s: &str) -> Result<Worm, String> {
    s.parse::<Worm>().map_err(|e| e.to_string())
}

/// 文字が順序数の worm として読む（"3 3 3" のような自然数の worm も受け付ける）。
fn parse_o(s: &str) -> Result<Worm<Veblen>, String> {
    if let Ok(w) = s.parse::<Worm>() {
        return Ok(w.map(|&n| Veblen::nat(n as u64)));
    }
    s.parse::<Worm<Veblen>>().map_err(|e| e.to_string())
}

/// すべて自然数の worm として読めるか（読めなければ順序数の worm として扱う）。
fn all_nat(xs: &[&String]) -> bool {
    xs.iter().all(|s| s.parse::<Worm>().is_ok())
}

/// 証明を検査してから表示する（`json` なら JSON で）。
///
/// 【Rust メモ】`<L: Letter>` を付けると、自然数の worm の証明にも
/// 順序数の worm の証明にも使える 1 つの関数になる。
fn show_proof<L: Letter>(p: &WcProof<L>, json: bool) -> Result<(), String> {
    let concl = wc::check(p).map_err(|e| format!("検査に失敗（バグです）: {e}"))?;
    if json {
        println!("{}", serde_json::to_string_pretty(p).map_err(|e| e.to_string())?);
    } else {
        print!("{p}");
        println!("WC で証明: {concl}  （検査済み、DAG {} ノード / 木に展開すると {} ノード / 高さ {}）",
            p.dag_size(), p.tree_size(), p.height());
    }
    Ok(())
}

/// RC の判定と導出（モダリティは自然数でも順序数でもよい）。
fn rc_cmd<L: Letter>(seq: Sequent<L>, show_proof: bool, json: bool) -> Result<(), String> {
    if !rc::entails(&seq.lhs, &seq.rhs) {
        // 反例を見せるときだけ閉包モデルを作る
        let d = rc::decide(&seq.lhs, &seq.rhs);
        println!("RC ⊬ {}", d.sequent);
        println!("反例：左辺の閉包モデルの根 0 で右辺が偽");
        print!("{}", d.model);
        return Ok(());
    }
    let (p, st) = rcproof::derive(&seq.lhs, &seq.rhs)?;
    rcproof::check(&p).map_err(|e| format!("検査に失敗（バグです）: {e}"))?;
    if json {
        println!("{}", serde_json::to_string_pretty(&p).map_err(|e| e.to_string())?);
        return Ok(());
    }
    if show_proof {
        print!("{p}");
    }
    println!("RC で証明: {seq}");
    println!(
        "  導出：検査済み、DAG {} ノード / 木に展開すると {} ノード / 高さ {}（書き足した事実 {} 個 / 飽和で得た事実 {} 個）",
        p.dag_size(), p.tree_size(), p.height(), st.facts_used, st.facts_total
    );
    if !show_proof {
        println!("  （--proof で導出の全行を表示）");
    }
    Ok(())
}

/// RC_BI の W_BI の式として読む。
fn parse_wbi(s: &str) -> Result<rcbi::Formula, String> {
    let a: rcbi::Formula = s.parse().map_err(|e: rcbi::ParseError| e.to_string())?;
    if !a.in_wbi() {
        return Err(format!("{a} は W_BI の式ではありません（変数・∇・⟨1⟩_ω を含まない式だけ）"));
    }
    Ok(a)
}

fn sym(o: Option<Ordering>) -> &'static str {
    match o {
        Some(Ordering::Less) => "<¹₁",
        Some(Ordering::Equal) => "≡¹₁",
        Some(Ordering::Greater) => ">¹₁",
        None => "?（比較できない：Thm 4.11 に反する）",
    }
}

/// Bracket Calculus の判定と導出。判定・導出・検査はすべて順序数を使わない。
/// 最後に τ（括弧語 → 順序数）で RC_Γ0 に翻訳した判定とも照らし合わせる（Thm 38）。
fn bc_cmd(goal: &BSeq, show_proof: bool, json: bool) -> Result<(), String> {
    let holds = bc::decide(&goal.lhs, &goal.rhs);
    let tau = goal.tau();
    if holds != bc::decide_tau(&goal.lhs, &goal.rhs) {
        return Err(format!("BC と RC_Γ0 の判定が食い違いました（バグです）: {goal}"));
    }
    if !holds {
        println!("BC ⊬ {goal}");
        println!("  τ で翻訳：RC_Γ0 ⊬ {} ⊢ {}", tau.lhs, tau.rhs);
        let d = rc::decide(&goal.lhs.to_rc(), &goal.rhs.to_rc());
        println!("反例：左辺の閉包モデルの根 0 で右辺が偽（文字は正規形の括弧語）");
        print!("{}", d.model);
        return Ok(());
    }
    let (p, st) = bc::derive(&goal.lhs, &goal.rhs)?;
    bc::check(&p).map_err(|e| format!("検査に失敗（バグです）: {e}"))?;
    if json {
        println!("{}", serde_json::to_string_pretty(&p).map_err(|e| e.to_string())?);
        return Ok(());
    }
    if show_proof {
        print!("{p}");
    }
    println!("BC で証明: {goal}");
    println!("  τ で翻訳：RC_Γ0 ⊢ {} ⊢ {}（順序数経由の判定とも一致）", tau.lhs, tau.rhs);
    println!(
        "  導出：検査済み（検査に順序数は不使用）、DAG {} ノード / 木に展開すると {} ノード / 高さ {}",
        p.dag_size(), p.tree_size(), p.height()
    );
    println!(
        "  副条件（括弧語どうしの比較）の導出 {} 個、副条件の入れ子は最大 {} 段",
        st.side_conditions, st.max_side_depth
    );
    if !show_proof {
        println!("  （--proof で導出の全行を表示）");
    }
    Ok(())
}

fn run(args: &[String]) -> Result<(), String> {
    let json = args.iter().any(|a| a == "--json");
    let full_proof = args.iter().any(|a| a == "--proof");
    let show_model = args.iter().any(|a| a == "--model");
    let args: Vec<String> =
        args.iter().filter(|a| *a != "--json" && *a != "--proof" && *a != "--model").cloned().collect();
    let args = args.as_slice();
    // 【Rust メモ】スライスに対するパターンマッチで引数の形を場合分けできる
    match args {
        [cmd, a] if cmd == "ord" && !all_nat(&[a]) => {
            // 文字が順序数の worm：o(A) < Γ0、標準形、Ω_ξ（ξ = 0, 1, 2 と A に現れる文字）
            let w = parse_o(a)?;
            let mut xis: Vec<Veblen> = (0..3).map(Veblen::nat).collect();
            xis.extend(w.letters().iter().cloned());
            xis.sort();
            xis.dedup();
            let pis: Vec<(Veblen, Veblen)> = xis.into_iter().map(|x| (x.clone(), w.pi_ordinal(&x))).collect();
            if json {
                let pi_json: Vec<_> = pis.iter().map(|(x, p)| json!({ "xi": x, "omega": p })).collect();
                let v = json!({
                    "worm": w,
                    "formula": w.to_formula(),
                    "ordinal": w.ordinal(),
                    "normal_form": w.normal_form(),
                    "pi_ordinals": pi_json,
                });
                println!("{}", serde_json::to_string_pretty(&v).map_err(|e| e.to_string())?);
            } else {
                println!("worm      : {w}");
                println!("formula   : {}", w.to_formula());
                println!("o(A)      : {}", w.ordinal());
                println!("normal    : {}", w.normal_form());
                for (x, p) in &pis {
                    let label = format!("Ω_{x}");
                    println!("{label:<10}: {p}");
                }
            }
            Ok(())
        }
        [cmd, a] if cmd == "ord" => {
            let w = parse(a)?;
            let k = w.letters().iter().max().map_or(0, |m| m + 1);
            let pis = w.pi_ordinals(k);
            if json {
                let v = json!({
                    "worm": w,
                    "formula": w.to_formula(),
                    "ordinal": w.ordinal(),
                    "normal_form": w.normal_form(),
                    "pi_ordinals": pis,
                });
                println!("{}", serde_json::to_string_pretty(&v).map_err(|e| e.to_string())?);
            } else {
                println!("worm      : {w}");
                println!("formula   : {}", w.to_formula());
                println!("o(A)      : {}", w.ordinal());
                println!("normal    : {}", w.normal_form());
                let shown: Vec<String> = pis.iter().map(|x| x.to_string()).collect();
                println!("Π 順序数  : (Ω_0, …, Ω_{k}) = ({})", shown.join(", "));
            }
            Ok(())
        }
        [cmd, rest @ ..] if cmd == "table" => {
            // 引数がなければ標準入力から 1 行 1 worm で読む
            let inputs: Vec<String> = if rest.is_empty() {
                std::io::stdin()
                    .lock()
                    .lines()
                    .map_while(Result::ok)
                    .filter(|l| !l.trim().is_empty())
                    .collect()
            } else {
                rest.to_vec()
            };
            let worms = inputs.iter().map(|s| parse(s)).collect::<Result<Vec<_>, _>>()?;
            let k = worms.iter().flat_map(|w| w.letters().iter().copied()).max().map_or(0, |m| m + 1);
            let pi_cols: Vec<String> = (0..=k).map(|n| format!("pi{n}")).collect();
            println!("worm,ordinal,normal_form,{}", pi_cols.join(","));
            for w in &worms {
                let pis: Vec<String> = w.pi_ordinals(k).iter().map(|x| x.to_string()).collect();
                println!("{w},{},{},{}", w.ordinal(), w.normal_form(), pis.join(","));
            }
            Ok(())
        }
        [cmd, a, b] if cmd == "cmp" && !all_nat(&[a, b]) => {
            // 文字が順序数の worm：順序数 o・head/body・RC の 3 つの方法で比べる
            let (x, y) = (parse_o(a)?, parse_o(b)?);
            let rel = match x.cmp0(&y) {
                Ordering::Less => "<_0",
                Ordering::Equal => "≡",
                Ordering::Greater => ">_0",
            };
            let by_o = (x.cmp0(&y) == Ordering::Less, y.cmp0(&x) == Ordering::Less);
            let mut hb = headbody::HeadBody::new();
            let by_hb = (hb.lt(x.letters(), y.letters()), hb.lt(y.letters(), x.letters()));
            let by_rc = (x.lt_n(&y, Veblen::zero()), y.lt_n(&x, Veblen::zero()));
            let agree = by_hb == by_o && by_rc == by_o;
            if json {
                let v = json!({
                    "a": x, "b": y, "relation": rel,
                    "ordinal_a": x.ordinal(), "ordinal_b": y.ordinal(),
                    "methods_agree": agree,
                });
                println!("{}", serde_json::to_string_pretty(&v).map_err(|e| e.to_string())?);
            } else {
                println!("{x}  {rel}  {y}");
                println!("  o = {}  vs  {}", x.ordinal(), y.ordinal());
                println!("  順序数 / RC / head-body の判定: {}", if agree { "一致" } else { "不一致（バグです）" });
            }
            Ok(())
        }
        [cmd, a, b] if cmd == "cmp" => {
            let (x, y) = (parse(a)?, parse(b)?);
            let rel = match x.cmp0(&y) {
                Ordering::Less => "<_0",
                Ordering::Equal => "≡",
                Ordering::Greater => ">_0",
            };
            // 3 つの独立な方法で確認
            let by_rc = (x.lt_n(&y, 0), y.lt_n(&x, 0));
            let mut hb = headbody::HeadBody::new();
            let by_hb = (hb.lt(x.letters(), y.letters()), hb.lt(y.letters(), x.letters()));
            let by_o = (x.cmp0(&y) == Ordering::Less, y.cmp0(&x) == Ordering::Less);
            let agree = by_rc == by_o && by_hb == by_o;
            if json {
                let v = json!({
                    "a": x, "b": y, "relation": rel,
                    "ordinal_a": x.ordinal(), "ordinal_b": y.ordinal(),
                    "methods_agree": agree,
                });
                println!("{}", serde_json::to_string_pretty(&v).map_err(|e| e.to_string())?);
            } else {
                println!("{x}  {rel}  {y}");
                println!("  o = {}  vs  {}", x.ordinal(), y.ordinal());
                println!("  順序数 / RC / head-body の判定: {}", if agree { "一致" } else { "不一致（バグです）" });
            }
            Ok(())
        }
        [cmd, a, rest @ ..] if cmd == "battle" && rest.len() <= 1 => {
            let limit: usize = match rest.first() {
                Some(s) => s.parse().map_err(|_| format!("上限が数値ではありません: {s}"))?,
                None => 30,
            };
            let w = parse(a)?;
            let mut steps = 0;
            for (i, cur) in w.battle().take(limit + 1).enumerate() {
                let shown = if cur.len() > 60 {
                    format!("{} … (長さ {})", Worm::new(cur.letters()[..60].to_vec()), cur.len())
                } else {
                    cur.to_string()
                };
                println!("{i:>4}: {shown}    o = {}", cur.ordinal());
                steps = i;
            }
            if steps == limit {
                println!("（{limit} ステップで打ち切り）");
            }
            Ok(())
        }
        [cmd, s] if cmd == "rc" => match s.parse::<Sequent>() {
            Ok(seq) => rc_cmd(seq, full_proof, json),
            // 自然数で読めなければ、モダリティが順序数のシーケントとして読む
            Err(e) => match s.parse::<Sequent<Veblen>>() {
                Ok(seq) => rc_cmd(seq, full_proof, json),
                Err(_) => Err(e.to_string()),
            },
        },
        [cmd, n, a, b] if cmd == "lt" => {
            let say = |x: &dyn std::fmt::Display, n: &dyn std::fmt::Display, y: &dyn std::fmt::Display, ans: bool| {
                println!("{x}  <_{n}  {y}  :  {}", if ans { "成り立つ" } else { "成り立たない" })
            };
            if let (Ok(k), true) = (n.parse::<u32>(), all_nat(&[a, b])) {
                let (x, y) = (parse(a)?, parse(b)?);
                say(&x, &k, &y, x.lt_n(&y, k));
            } else {
                let k: Veblen = n.parse().map_err(|_| format!("n が順序数として読めません: {n}"))?;
                let (x, y) = (parse_o(a)?, parse_o(b)?);
                say(&x, &k, &y, x.lt_n(&y, k.clone()));
            }
            Ok(())
        }
        [cmd, s] if cmd == "wc" => {
            let (l, r) = s
                .split_once("⊢")
                .or_else(|| s.split_once("|-"))
                .ok_or("'⊢' または '|-' が必要です")?;
            let (l, r) = (l.to_string(), r.to_string());
            if all_nat(&[&l, &r]) {
                show_proof(&wc::prove(&parse(&l)?, &parse(&r)?)?, json)
            } else {
                show_proof(&wc::prove(&parse_o(&l)?, &parse_o(&r)?)?, json)
            }
        }
        [cmd, n, a, b] if cmd == "wclt" => {
            if let (Ok(k), true) = (n.parse::<u32>(), all_nat(&[a, b])) {
                show_proof(&wc::prove_lt(k, &parse(a)?, &parse(b)?)?, json)
            } else {
                let k: Veblen = n.parse().map_err(|_| format!("n が順序数として読めません: {n}"))?;
                show_proof(&wc::prove_lt(k, &parse_o(a)?, &parse_o(b)?)?, json)
            }
        }
        [cmd, a] if cmd == "ordinal" => {
            let x: Veblen = a.parse().map_err(|e: wormlab_core::veblen::ParseOrdinalError| e.to_string())?;
            let kind = if x.is_zero() {
                "0"
            } else if x.is_successor() {
                "後続順序数"
            } else {
                "極限順序数"
            };
            let cnf: Vec<String> = x
                .cnf()
                .iter()
                .map(|(e, c)| {
                    let base = if e.is_zero() {
                        return c.to_string();
                    } else if e.is_finite() || e.is_principal() {
                        format!("ω^{e}")
                    } else {
                        format!("ω^({e})")
                    };
                    if *c == 1 { base } else { format!("{base}·{c}") }
                })
                .collect();
            println!("正規形    : {x}");
            println!("種類      : {kind}{}", if x.to_cnf().is_some() { "（ε0 未満）" } else { "（ε0 以上）" });
            println!("CNF       : {}", if cnf.is_empty() { "0".to_string() } else { cnf.join(" + ") });
            println!("ℓ（最後の指数）: {}", x.last_exponent());
            Ok(())
        }
        [cmd, a, b] if cmd == "ordinal" => {
            let p = |s: &str| s.parse::<Veblen>().map_err(|e| e.to_string());
            let (x, y) = (p(a)?, p(b)?);
            let rel = match x.cmp(&y) {
                Ordering::Less => "<",
                Ordering::Equal => "=",
                Ordering::Greater => ">",
            };
            println!("{x}  {rel}  {y}");
            Ok(())
        }
        [cmd, a] if cmd == "bracket" => {
            let x = parse_bracket(a)?;
            let nf = x.normal_form();
            if json {
                let v = json!({
                    "bracket": x,
                    "worm": x.to_worm(),
                    "ordinal": x.ordinal(),
                    "depth": x.depth(),
                    "normal_form": nf,
                    "is_normal": x.is_normal(),
                });
                println!("{}", serde_json::to_string_pretty(&v).map_err(|e| e.to_string())?);
            } else {
                println!("括弧語    : {x}");
                println!("翻訳 a*   : {}", x.to_worm().to_formula());
                println!("o*(a)     : {}", x.ordinal());
                println!("深さ      : {}", x.depth());
                println!("正規形    : {nf}{}", if x.is_normal() { "（この語自身が正規形）" } else { "" });
                let nf2 = x.normal_form_syntactic();
                println!("正規形（順序数なし）: {nf2}{}", if nf2 == nf { "（一致）" } else { "（不一致：バグです）" });
            }
            Ok(())
        }
        [cmd, a, b] if cmd == "bcmp" => {
            let (x, y) = (parse_bracket(a)?, parse_bracket(b)?);
            let sym = |o: Ordering| match o {
                Ordering::Less => "<",
                Ordering::Equal => "=",
                Ordering::Greater => ">",
            };
            let syn = x.cmp_syntactic(&y);
            let (ox, oy) = (x.ordinal(), y.ordinal());
            println!("{x}  {}  {y}    （順序数を使わない比較）", sym(syn));
            println!("o* = {ox}  {}  {oy}    （Veblen 表記を経由した比較{}）",
                sym(ox.cmp(&oy)), if ox.cmp(&oy) == syn { "、一致" } else { "、不一致：バグです" });
            println!("正規形（順序数なし）: {}  と  {}", x.normal_form_syntactic(), y.normal_form_syntactic());
            Ok(())
        }
        [cmd, s] if cmd == "bi" => {
            let q: rcbi::Sequent = s.parse().map_err(|e: rcbi::ParseError| e.to_string())?;
            let d = rcbi::decide(&q.lhs, &q.rhs)?;
            let m = &d.model;
            if d.holds {
                println!("RC_BIω ⊢ {}", d.sequent);
            } else {
                println!("RC_BIω ⊬ {}", d.sequent);
                println!("反例：左辺の有限モデル M_A の根 0 で右辺が偽");
            }
            println!("  M_A：{} 点、持っている添字 1..{} と ω", m.num_points(), m.n_fin());
            if show_model || !d.holds {
                print!("{m}");
            } else {
                println!("  （--model で M_A を表示）");
            }
            Ok(())
        }
        [cmd, s] if cmd == "bimodel" => {
            let a: rcbi::Formula = s.parse().map_err(|e: rcbi::ParseError| e.to_string())?;
            if !a.is_closed() {
                return Err("M_A を作れるのは変数を含まない式だけです".to_string());
            }
            let m = rcbi::Model::of(&a, a.max_rank());
            println!("A = {a}");
            print!("{m}");
            let v = m.frame_violations();
            if v.is_empty() {
                println!("フレーム条件 I〜IV：すべて満たす（RC_BIω モデル）");
            } else {
                println!("フレーム条件の違反（バグです）:");
                for x in v {
                    println!("  {x}");
                }
            }
            Ok(())
        }
        [cmd, a, b] if cmd == "bicmp" => {
            let (x, y) = (parse_wbi(a)?, parse_wbi(b)?);
            println!("{x}  {}  {y}", sym(rcbi_order::compare(&x, &y)));
            Ok(())
        }
        [cmd, a, rest @ ..] if cmd == "bifs" && rest.len() <= 1 => {
            let x = parse_wbi(a)?;
            let k: u32 = match rest.first() {
                Some(s) => s.parse().map_err(|_| format!("k が数値ではありません: {s}"))?,
                None => 4,
            };
            match rcbi_order::form(&x)? {
                rcbi_order::Form::Zero => println!("{x} は零（⊤ と ≡¹₁、o = 0）"),
                rcbi_order::Form::Successor(p) => {
                    println!("{x} は後続形");
                    println!("  直前：{p}（o(A) = o(直前) + 1）");
                }
                rcbi_order::Form::Limit => {
                    println!("{x} は極限形。基本列 (A)_n（Def 4.6）:");
                    let mut prev: Option<rcbi::Formula> = None;
                    for n in 1..=k {
                        let y = rcbi_order::approx(&x, n).expect("極限形");
                        let below = if rcbi_order::lt(&y, &x) { "< A" } else { "≮ A（Lemma 4.7 に反する）" };
                        let step = match &prev {
                            Some(p) => format!("、前の項と {}", sym(rcbi_order::compare(p, &y))),
                            None => String::new(),
                        };
                        println!("  ({n}) {}    [{below}{step}]", shorten(y.to_string(), 100));
                        prev = Some(y);
                    }
                }
            }
            Ok(())
        }
        [cmd, a, rest @ ..] if cmd == "bibattle" && rest.len() <= 1 => {
            let x = parse_wbi(a)?;
            let limit: usize = match rest.first() {
                Some(s) => s.parse().map_err(|_| format!("上限が数値ではありません: {s}"))?,
                None => 30,
            };
            let mut steps = 0;
            for (i, cur) in rcbi_order::battle(&x).take(limit + 1).enumerate() {
                println!("{i:>4}: {}", shorten(cur.to_string(), 100));
                steps = i;
            }
            if steps == limit {
                println!("（{limit} ステップで打ち切り）");
            }
            Ok(())
        }
        [cmd, s] if cmd == "bc" => {
            let goal: BSeq = s.parse().map_err(|e: bc::ParseError| e.to_string())?;
            bc_cmd(&goal, full_proof, json)
        }
        [cmd, a] if cmd == "bracketof" => {
            let x: Veblen = a.parse().map_err(|e: wormlab_core::veblen::ParseOrdinalError| e.to_string())?;
            let w = Bracket::from_ordinal(&x);
            println!("{x}  =  {w}");
            Ok(())
        }
        [cmd, a, rest @ ..] if cmd == "bbattle" && rest.len() <= 1 => {
            let limit: usize = match rest.first() {
                Some(s) => s.parse().map_err(|_| format!("上限が数値ではありません: {s}"))?,
                None => 30,
            };
            let x = parse_bracket(a)?;
            let mut steps = 0;
            for (i, cur) in x.battle().take(limit + 1).enumerate() {
                println!("{i:>4}: {}    o* = {}", shorten(cur.to_string(), 60), cur.ordinal());
                steps = i;
            }
            if steps == limit {
                println!("（{limit} ステップで打ち切り）");
            }
            Ok(())
        }
        [cmd, m] if cmd == "thm52" => {
            let m: usize = m.parse().map_err(|_| format!("m が数値ではありません: {m}"))?;
            let a = Bracket::thm52(m);
            println!("a'_{m} = {a}");
            println!("o*    = {}", a.ordinal());
            println!("（ここから始めた battle が ⊤ に着くまでの長さ G(m) は、ATR₀ が全域性を");
            println!("  証明できるどんな関数よりも速く増える：arXiv:2008.13445, Thm 52）");
            Ok(())
        }
        [cmd, a, rest @ ..] if cmd == "fs" && rest.len() <= 1 => {
            let x = parse_ordinal(a)?;
            let k: u64 = match rest.first() {
                Some(s) => s.parse().map_err(|_| format!("k が数値ではありません: {s}"))?,
                None => 5,
            };
            if !x.is_limit() {
                println!("{x} は極限順序数ではありません（後続なら α[n] は直前の数）");
                return Ok(());
            }
            println!("{:>3}  {:<40} worm の基本列（正規形の worm から 1 ステップ）", "n", format!("{x}[n]（標準）"));
            for n in 0..=k {
                let std = x.fundamental(n).expect("極限").to_string();
                let worm = hierarchy::worm_fundamental(&x, n as usize).map_or("-".to_string(), |y| y.to_string());
                println!("{n:>3}  {:<40} {}", shorten(std, 40), shorten(worm, 60));
            }
            Ok(())
        }
        [cmd, a, n] if cmd == "hardy" => {
            let x = parse_ordinal(a)?;
            let n: u128 = n.parse().map_err(|_| format!("n が数値ではありません: {n}"))?;
            let show = |v: Option<u128>| v.map_or("大きすぎて打ち切り（u128 を超えるか、計算が長すぎる）".to_string(), |v| v.to_string());
            println!("H_{x}({n}) = {}", show(hierarchy::hardy(&x, n, Budget::default())));
            println!("f_{x}({n}) = {}", show(hierarchy::fast_growing(&x, n, Budget::default())));
            Ok(())
        }
        [cmd, a] if cmd == "blen" => {
            let x = parse_ordinal(a)?;
            let budget = Budget { max_steps: 10_000_000 };
            let show = |v: Option<u64>| v.map_or("1000 万ステップで打ち切り".to_string(), |v| v.to_string());
            println!("α = {x}");
            println!("  worm battle（正規形の worm から）: {}", show(hierarchy::worm_battle_length_of(&x, budget)));
            println!("  標準 battle（α ← α[k], k = 1, 2, …）: {}", show(hierarchy::ordinal_battle_length(&x, 1, budget)));
            Ok(())
        }
        _ => Err(USAGE.to_string()),
    }
}

const USAGE: &str = "使い方:
  wormlab ord    <worm>            順序数・標準形・Π 順序数（--json 可）
  wormlab table  [<worm> …]        複数の worm を CSV で（引数なしなら標準入力から）
  wormlab cmp    <worm> <worm>     <_0 で比較（--json 可）
  wormlab battle <worm> [上限]     worm battle を実行
  wormlab rc     \"A |- B\"          RC で判定。真なら導出（--proof で全行）、偽なら反例モデル
  wormlab lt     <n> <worm> <worm> 一般の worm で A <_n B か
  wormlab wc     \"A |- B\"          worm シーケントの WC 証明（--json で JSON 出力）
  wormlab wclt   <n> <worm> <worm> A <_n B（B ⊢ nA）の WC 証明
  wormlab ordinal <順序数> [<順序数>]  Γ0 未満の順序数の正規形（2 つなら比較）
  wormlab bracket <括弧語>         括弧語の順序数・翻訳・正規形（--json 可）
  wormlab bracketof <順序数>       順序数を正規形の括弧語にする
  wormlab bcmp   <括弧語> <括弧語> 順序数を使わない比較（Veblen 経由と照合）
  wormlab bc     \"φ |- ψ\"          Bracket Calculus で判定。真なら BC の導出（--proof で全行）
  wormlab bi     \"A |- B\"          RC_BI（Pakhomov–Lazar）で判定（変数なし。--model で M_A を表示）
  wormlab bimodel <式>             RC_BI の有限モデル M_A とフレーム条件の検査
  wormlab bicmp  <式> <式>         RC_BI の順序 <¹₁・≡¹₁ で比較
  wormlab bifs   <式> [k]          式の形と基本列 (A)_1..k
  wormlab bibattle <式> [上限]     RC_BI の式の battle
  wormlab bbattle <括弧語> [上限]  括弧語の battle
  wormlab thm52  <m>               ATR₀ から独立な命題（Thm 52）の出発点 a'_m
  wormlab fs     <順序数> [k]      標準の基本列 α[0..k] と worm が作る列
  wormlab hardy  <順序数> <n>      Hardy 関数 H_α(n) と急増加関数 f_α(n)
  wormlab blen   <順序数>          worm battle と標準 battle の長さ
worm の書き方: \"1 0 2\", \"<1><0><2>T\", \"⊤\" など
  文字が順序数の worm: \"<ω+1><0><ε_0>\" または \"ω+1, 0, ε_0\"（ord・cmp・lt・wc・wclt で使える）
順序数の書き方: \"ω^(ω + 1)·2 + 3\", \"ε_0\", \"φ(2, 0)\"（ω は w、ε は e、φ は phi でも可）
括弧語の書き方: \"()\" = 1, \"(())\" = ω, \"((()))\" = ε_0（⊤ は省略）
BC の式: \"(a)φ\"（a は括弧語）。例 \"((()))p\" = ⟨ω⟩p、\"(())(p & ()q)\"。括弧語はそのまま式として読む
RC_BI の式: <1>_2 = ⟨1⟩₂、<2>_3 = ⟨2⟩₃、<1>_w = ⟨1⟩_ω、D = ↓、N = ∇、T = ⊤（<1>, <2> だけなら ⟨1⟩₁, ⟨2⟩₂）";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(msg) => {
            eprintln!("{msg}");
            ExitCode::FAILURE
        }
    }
}
