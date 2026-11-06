//! wormlab コマンドラインツール
//!
//! 使い方：
//!   wormlab ord    "1 0 2"          worm の順序数と標準形を表示
//!   wormlab cmp    "1 1" "2"        2 つの worm を <_0 で比較
//!   wormlab battle "1 1 1" [上限]    worm battle を実行
//!   wormlab rc     "<2>p |- <0><1>p" RC で判定（偽なら反例モデル）
//!   wormlab lt     1 "0 2" "1"       一般の worm で A <_n B か
//!   wormlab wc     "1 1 |- 0 1 0 1"  worm シーケントの WC 証明（--json で JSON）
//!   wormlab wclt   0 "1 1" "2"       A <_n B（B ⊢ nA）の WC 証明

use std::cmp::Ordering;
use std::process::ExitCode;
use wormlab_core::wc::{self, WcProof};
use wormlab_core::{Sequent, Worm, headbody, rc};

fn parse(s: &str) -> Result<Worm, String> {
    s.parse::<Worm>().map_err(|e| e.to_string())
}

/// 証明を検査してから表示する（`json` なら JSON で）。
fn show_proof(p: &WcProof, json: bool) -> Result<(), String> {
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
            println!("worm      : {w}");
            println!("formula   : {}", w.to_formula());
            println!("o(A)      : {}", w.ordinal());
            println!("normal    : {}", w.normal_form());
            Ok(())
        }
        [cmd, a, b] if cmd == "cmp" => {
            let (x, y) = (parse(a)?, parse(b)?);
            let rel = match x.cmp0(&y) {
                Ordering::Less => "<_0",
                Ordering::Equal => "≡",
                Ordering::Greater => ">_0",
            };
            println!("{x}  {rel}  {y}");
            println!("  o = {}  vs  {}", x.ordinal(), y.ordinal());
            // 3 つの独立な方法で確認
            let by_rc = (x.lt_n(&y, 0), y.lt_n(&x, 0));
            let mut hb = headbody::HeadBody::new();
            let by_hb = (hb.lt(x.letters(), y.letters()), hb.lt(y.letters(), x.letters()));
            let by_o = (x.cmp0(&y) == Ordering::Less, y.cmp0(&x) == Ordering::Less);
            let agree = by_rc == by_o && by_hb == by_o;
            println!("  順序数 / RC / head-body の判定: {}", if agree { "一致" } else { "不一致（バグです）" });
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
            let n: u32 = n.parse().map_err(|_| format!("n が数値ではありません: {n}"))?;
            let (x, y) = (parse(a)?, parse(b)?);
            let ans = x.lt_n(&y, n);
            println!("{x}  <_{n}  {y}  :  {}", if ans { "成り立つ" } else { "成り立たない" });
            Ok(())
        }
        [cmd, s] if cmd == "wc" => {
            let (l, r) = s
                .split_once("⊢")
                .or_else(|| s.split_once("|-"))
                .ok_or("'⊢' または '|-' が必要です")?;
            let p = wc::prove(&parse(l)?, &parse(r)?)?;
            show_proof(&p, json)
        }
        [cmd, n, a, b] if cmd == "wclt" => {
            let n: u32 = n.parse().map_err(|_| format!("n が数値ではありません: {n}"))?;
            let p = wc::prove_lt(n, &parse(a)?, &parse(b)?)?;
            show_proof(&p, json)
        }
        _ => Err(USAGE.to_string()),
    }
}

const USAGE: &str = "使い方:
  wormlab ord    <worm>            順序数と標準形
  wormlab cmp    <worm> <worm>     <_0 で比較
  wormlab battle <worm> [上限]     worm battle を実行
  wormlab rc     \"A |- B\"          RC で判定（偽なら反例モデル）
  wormlab lt     <n> <worm> <worm> 一般の worm で A <_n B か
  wormlab wc     \"A |- B\"          worm シーケントの WC 証明（--json で JSON 出力）
  wormlab wclt   <n> <worm> <worm> A <_n B（B ⊢ nA）の WC 証明
worm の書き方: \"1 0 2\", \"<1><0><2>T\", \"⊤\" など";

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
