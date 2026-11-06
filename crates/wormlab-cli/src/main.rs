//! wormlab コマンドラインツール
//!
//! 使い方：
//!   wormlab ord    "1 0 2"          worm の順序数・標準形・Π 順序数を表示（--json 可）
//!   wormlab table  "1 0" "2" …      複数の worm を CSV で（引数がなければ標準入力から 1 行 1 worm）
//!   wormlab cmp    "1 1" "2"        2 つの worm を <_0 で比較（--json 可）
//!   wormlab battle "1 1 1" [上限]    worm battle を実行
//!   wormlab rc     "<2>p |- <0><1>p" RC で判定（偽なら反例モデル）
//!   wormlab lt     1 "0 2" "1"       一般の worm で A <_n B か
//!   wormlab wc     "1 1 |- 0 1 0 1"  worm シーケントの WC 証明（--json で JSON）
//!   wormlab wclt   0 "1 1" "2"       A <_n B（B ⊢ nA）の WC 証明
//!   wormlab ordinal "ω^ε_0 + 1"      Γ0 未満の順序数を正規形にする（2 つ渡すと比較）
//!
//! cmp・lt・wc・wclt は、文字が順序数の worm（例 "<ω+1><0><ε_0>"）も受け付ける。

use serde_json::json;
use std::cmp::Ordering;
use std::io::BufRead;
use std::process::ExitCode;
use wormlab_core::wc::{self, WcProof};
use wormlab_core::{Letter, Sequent, Veblen, Worm, headbody, rc};

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

fn run(args: &[String]) -> Result<(), String> {
    let json = args.iter().any(|a| a == "--json");
    let args: Vec<String> = args.iter().filter(|a| *a != "--json").cloned().collect();
    let args = args.as_slice();
    // 【Rust メモ】スライスに対するパターンマッチで引数の形を場合分けできる
    match args {
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
            // 文字が順序数の worm：head/body と RC の 2 つの方法で比べる
            let (x, y) = (parse_o(a)?, parse_o(b)?);
            let mut hb = headbody::HeadBody::new();
            let by_hb = (hb.lt(x.letters(), y.letters()), hb.lt(y.letters(), x.letters()));
            let by_rc = (x.lt_n(&y, Veblen::zero()), y.lt_n(&x, Veblen::zero()));
            let rel = match by_hb {
                (true, _) => "<_0",
                (_, true) => ">_0",
                _ => "≡",
            };
            let agree = by_hb == by_rc;
            if json {
                let v = json!({ "a": x, "b": y, "relation": rel, "methods_agree": agree });
                println!("{}", serde_json::to_string_pretty(&v).map_err(|e| e.to_string())?);
            } else {
                println!("{x}  {rel}  {y}");
                println!("  RC / head-body の判定: {}", if agree { "一致" } else { "不一致（バグです）" });
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
        [cmd, s] if cmd == "rc" => {
            let seq: Sequent = s.parse().map_err(|e: wormlab_core::spf::ParseError| e.to_string())?;
            let d = rc::decide(&seq.lhs, &seq.rhs);
            if d.holds {
                println!("RC ⊢ {}", d.sequent);
            } else {
                println!("RC ⊬ {}", d.sequent);
                println!("反例：左辺の閉包モデルの根 0 で右辺が偽");
                print!("{}", d.model);
            }
            Ok(())
        }
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
        _ => Err(USAGE.to_string()),
    }
}

const USAGE: &str = "使い方:
  wormlab ord    <worm>            順序数・標準形・Π 順序数（--json 可）
  wormlab table  [<worm> …]        複数の worm を CSV で（引数なしなら標準入力から）
  wormlab cmp    <worm> <worm>     <_0 で比較（--json 可）
  wormlab battle <worm> [上限]     worm battle を実行
  wormlab rc     \"A |- B\"          RC で判定（偽なら反例モデル）
  wormlab lt     <n> <worm> <worm> 一般の worm で A <_n B か
  wormlab wc     \"A |- B\"          worm シーケントの WC 証明（--json で JSON 出力）
  wormlab wclt   <n> <worm> <worm> A <_n B（B ⊢ nA）の WC 証明
  wormlab ordinal <順序数> [<順序数>]  Γ0 未満の順序数の正規形（2 つなら比較）
worm の書き方: \"1 0 2\", \"<1><0><2>T\", \"⊤\" など
  文字が順序数の worm: \"<ω+1><0><ε_0>\" または \"ω+1, 0, ε_0\"（cmp・lt・wc・wclt で使える）
順序数の書き方: \"ω^(ω + 1)·2 + 3\", \"ε_0\", \"φ(2, 0)\"（ω は w、ε は e、φ は phi でも可）";

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
