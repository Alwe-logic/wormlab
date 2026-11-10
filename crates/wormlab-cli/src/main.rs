//! wormlab コマンドラインツール
//!
//! 使い方：
//! ```text
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
//!   wormlab bwc "((())) |- ()(())"   括弧語だけの体系 BWC（WC の BC 版）で判定・導出・検査
//!                                    （--proof で導出の全行、--json で JSON、--latex で LaTeX）
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
//!   wormlab rules [体系]             各体系（rc・wc・bc・bwc・rcbi）の公理と規則の一覧（--json 可）
//!   wormlab expr "e^ω(1) + ψ(0)"     順序数の式（+・·・^・φ・ε・e^α・ψ）を使った定義つきで標準形に（--latex 可）
//!   wormlab defs [分類|鍵]           定義集：ゲーム・基本列・順序数上の関数・表記と順序数・意味論（出典・場合ごとの例つき。--json・--latex）
//!   wormlab forms "ε_0 + 1"          同じ順序数をいろいろな標準形で（Veblen・φ だけ・超指数と ψ・worm・括弧語・impredicative worm）
//! ```
//!
//! ord・cmp・lt・wc・wclt は、文字が順序数の worm（例 "<ω+1><0><ε_0>"）も受け付ける。
//!
//! LaTeX：--latex を付けると結果を LaTeX で出す（論文にそのまま貼れる断片）。--standalone なら
//! プリアンブルつきの文書（pdflatex にかけられる）。証明は bussproofs の証明木と行番号つきの一覧、
//! 反例モデル・M_A は TikZ（--rel=all で閉包後の辺も、--rel=1,down のように関係を選んでも描ける）。
//!   例：wormlab rc "<1>p & <0>q |- <1>(p & <0>q)" --latex --standalone > proof.tex && pdflatex proof.tex

use serde_json::json;
use std::cmp::Ordering;
use std::io::BufRead;
use std::process::ExitCode;
use wormlab_core::arith;
use wormlab_core::expr;
use wormlab_core::glossary;
use wormlab_core::notation;
use wormlab_core::repeats;
use wormlab_core::wc::{self, WcProof};
use wormlab_core::bignum::BigNat;
use wormlab_core::hierarchy::{self, BigBudget, BigValue, Budget};
use wormlab_core::bc::{self, BSeq};
use wormlab_core::bwc::{self, BwSeq};
use wormlab_core::cworm::{self, CWorm};
use wormlab_core::iworm::{self, IWorm};
use wormlab_core::latex::{self, BattleRow, ToLatex};
use wormlab_core::modelview::ModelView;
use wormlab_core::proof::Proof;
use wormlab_core::{Bracket, Letter, Sequent, Veblen, Worm, headbody, rc, rcbi, rcbi_order, rcproof};

/// --latex・--standalone・--rel の指定。
struct Tex {
    standalone: bool,
    rel: Option<String>,
}

impl Tex {
    /// 部品を空行で区切って出す（--standalone なら文書に包む）。
    fn emit(&self, parts: Vec<String>) {
        let body = parts.join("\n\n");
        if self.standalone {
            print!("{}", latex::document(&body));
        } else {
            println!("{body}");
        }
    }

    /// TikZ に描く関係（--rel の指定）。名前は記号を省いて比べる（"R¹₁" は "11"、"R↓" は "down"）。
    fn rels(&self, v: &ModelView) -> Vec<String> {
        let key = |s: &str| -> String {
            s.chars()
                .filter_map(|c| match c {
                    'R' | '_' | '^' | ' ' => None,
                    '¹' => Some("1".to_string()),
                    '²' => Some("2".to_string()),
                    '₀'..='₉' => Some(char::from(b'0' + (c as u32 - '₀' as u32) as u8).to_string()),
                    '↓' => Some("down".to_string()),
                    '∇' => Some("nabla".to_string()),
                    'ω' => Some("w".to_string()),
                    _ => Some(c.to_string()),
                })
                .collect()
        };
        match self.rel.as_deref() {
            None => Vec::new(),
            Some("all") => v.relations.iter().map(|r| r.name.clone()).collect(),
            Some(list) => {
                let wanted: Vec<String> = list.split(',').map(|s| key(s.trim())).collect();
                v.relations.iter().filter(|r| wanted.contains(&key(&r.name))).map(|r| r.name.clone()).collect()
            }
        }
    }

    fn model(&self, v: &ModelView) -> String {
        v.tikz(&self.rels(v), true)
    }
}

/// 検査済みの証明を LaTeX の部品にする：結論、証明木（小さければ）、行番号つきの一覧。
fn proof_tex<J: ToLatex, R: ToLatex>(system: &str, verdict: &str, p: &Proof<J, R>) -> Vec<String> {
    let mut parts = vec![
        format!(
            "% {system}: checked derivation (DAG {} nodes, {} nodes as a tree, height {})",
            p.dag_size(),
            p.tree_size(),
            p.height()
        ),
        latex::display(verdict),
    ];
    match latex::proof_tree(p, latex::TREE_LIMIT) {
        Some(t) => parts.push(t),
        None => parts.push(format!(
            "% proof tree omitted: {} nodes as a tree (limit {}); see the numbered lines below",
            p.tree_size(),
            latex::TREE_LIMIT
        )),
    }
    parts.push(latex::proof_lines(p));
    parts
}

fn parse_ordinal(s: &str) -> Result<Veblen, String> {
    // 式としても読む（Ω^Ω・ε_0·ω・(ω + 1)^2 など）
    expr::parse_ordinal(s)
}

fn parse_bracket(s: &str) -> Result<Bracket, String> {
    s.parse::<Bracket>().map_err(|e| e.to_string())
}

/// これ以上長い worm（文字の数）・括弧語（記号の数）の battle は、繰り返しでまとめて表示する。
const COMPACT_MIN_LETTERS: usize = 16;
const COMPACT_MIN_CHARS: usize = 40;

/// battle の 1 ステップの表示：長ければ繰り返しでまとめた形（まとめても長ければ先頭だけ）。
fn battle_line(raw: String, long: bool, compact: impl FnOnce() -> repeats::Compact, size: usize) -> String {
    if !long {
        return raw;
    }
    let c = compact();
    if c.text.chars().count() < raw.chars().count() {
        format!("{}    （長さ {size}）", shorten(c.text, 240))
    } else {
        shorten(raw, 100)
    }
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
fn show_proof<L: Letter>(p: &WcProof<L>, json: bool, tex: Option<&Tex>) -> Result<(), String> {
    let concl = wc::check(p).map_err(|e| format!("検査に失敗（バグです）: {e}"))?;
    if let Some(t) = tex {
        t.emit(proof_tex("WC", &concl.to_latex(), p));
        return Ok(());
    }
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
fn rc_cmd<L: Letter>(seq: Sequent<L>, show_proof: bool, json: bool, tex: Option<&Tex>) -> Result<(), String> {
    if !rc::entails(&seq.lhs, &seq.rhs) {
        // 反例を見せるときだけ閉包モデルを作る
        let d = rc::decide(&seq.lhs, &seq.rhs);
        if let Some(t) = tex {
            let view = ModelView::from_rc(&d.model, Some(&seq.rhs));
            t.emit(vec![
                "% RC: not derivable; counter-model (the right-hand side fails at the root 0)".to_string(),
                latex::display(&latex::verdict(&seq.lhs.to_latex(), &seq.rhs.to_latex(), false)),
                t.model(&view),
            ]);
            return Ok(());
        }
        println!("RC ⊬ {}", d.sequent);
        println!("反例：左辺の閉包モデルの根 0 で右辺が偽");
        print!("{}", d.model);
        return Ok(());
    }
    let (p, st) = rcproof::derive(&seq.lhs, &seq.rhs)?;
    rcproof::check(&p).map_err(|e| format!("検査に失敗（バグです）: {e}"))?;
    if let Some(t) = tex {
        t.emit(proof_tex("RC", &seq.to_latex(), &p));
        return Ok(());
    }
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
fn bc_cmd(goal: &BSeq, show_proof: bool, json: bool, tex: Option<&Tex>) -> Result<(), String> {
    let holds = bc::decide(&goal.lhs, &goal.rhs);
    let tau = goal.tau();
    if holds != bc::decide_tau(&goal.lhs, &goal.rhs) {
        return Err(format!("BC と RC_Γ0 の判定が食い違いました（バグです）: {goal}"));
    }
    if !holds {
        if let Some(t) = tex {
            let d = rc::decide(&goal.lhs.to_rc(), &goal.rhs.to_rc());
            let view = ModelView::from_rc(&d.model, Some(&goal.rhs.to_rc()));
            t.emit(vec![
                "% BC: not derivable; counter-model (letters are normal bracket words)".to_string(),
                latex::display(&latex::verdict(&goal.lhs.to_latex(), &goal.rhs.to_latex(), false)),
                t.model(&view),
            ]);
            return Ok(());
        }
        println!("BC ⊬ {goal}");
        println!("  τ で翻訳：RC_Γ0 ⊬ {} ⊢ {}", tau.lhs, tau.rhs);
        let d = rc::decide(&goal.lhs.to_rc(), &goal.rhs.to_rc());
        println!("反例：左辺の閉包モデルの根 0 で右辺が偽（文字は正規形の括弧語）");
        print!("{}", d.model);
        return Ok(());
    }
    let (p, st) = bc::derive(&goal.lhs, &goal.rhs)?;
    bc::check(&p).map_err(|e| format!("検査に失敗（バグです）: {e}"))?;
    if let Some(t) = tex {
        t.emit(proof_tex("BC", &goal.to_latex(), &p));
        return Ok(());
    }
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

/// worm の比較を LaTeX に：`A <_{0} B`（下に順序数も）。
fn worm_cmp_tex(a: &str, o: Ordering, b: &str, oa: &str, ob: &str) -> String {
    let (rel, orel) = match o {
        Ordering::Less => ("<_{0}", "<"),
        Ordering::Equal => ("\\equiv", "="),
        Ordering::Greater => (">_{0}", ">"),
    };
    latex::align(&[
        (a.to_string(), format!("{rel} {b}")),
        (format!("o({a})"), format!("= {oa} {orel} {ob} = o({b})")),
    ])
}

/// 括弧語だけの体系 BWC（WC の BC 版）の判定と導出。順序数も RC も使わない。
/// 最後に BC（RC 経由）の判定とも照らし合わせる。
fn bwc_cmd(goal: &BwSeq, show_proof: bool, json: bool, tex: Option<&Tex>) -> Result<(), String> {
    let holds = bwc::decide(&goal.lhs, &goal.rhs);
    if holds != bc::decide(&bc::Formula::worm(&goal.lhs), &bc::Formula::worm(&goal.rhs)) {
        return Err(format!("BWC と BC の判定が食い違いました（バグです）: {goal}"));
    }
    if !holds {
        if let Some(t) = tex {
            t.emit(vec![latex::display(&latex::verdict(&goal.lhs.to_latex(), &goal.rhs.to_latex(), false))]);
            return Ok(());
        }
        println!("BWC ⊬ {goal}");
        println!("  （BC・RC_Γ0 でも成り立たない）");
        return Ok(());
    }
    let (p, st) = bwc::prove(&goal.lhs, &goal.rhs)?;
    bwc::check(&p).map_err(|e| format!("検査に失敗（バグです）: {e}"))?;
    if let Some(t) = tex {
        t.emit(proof_tex("BWC", &goal.to_latex(), &p));
        return Ok(());
    }
    if json {
        println!("{}", serde_json::to_string_pretty(&p).map_err(|e| e.to_string())?);
        return Ok(());
    }
    if show_proof {
        print!("{p}");
    }
    println!("BWC で証明: {goal}");
    println!(
        "  導出：検査済み（判定・導出・検査に順序数も RC も不使用）、DAG {} ノード / 木に展開すると {} ノード / 高さ {}",
        p.dag_size(), p.tree_size(), p.height()
    );
    println!("  副条件（文字どうしの比較）の導出 {} 個、入れ子は最大 {} 段", st.side_conditions, st.max_side_depth);
    if !show_proof {
        println!("  （--proof で導出の全行を表示）");
    }
    Ok(())
}

fn run(args: &[String]) -> Result<(), String> {
    let json = args.iter().any(|a| a == "--json");
    let full_proof = args.iter().any(|a| a == "--proof");
    let show_model = args.iter().any(|a| a == "--model");
    let standalone = args.iter().any(|a| a == "--standalone");
    let rel = args.iter().find_map(|a| a.strip_prefix("--rel=").map(|s| s.to_string()));
    let tex = (args.iter().any(|a| a == "--latex") || standalone).then_some(Tex { standalone, rel });
    let tex = tex.as_ref();
    // 多倍長の値：--full で全桁、--bits=N で途中の値の大きさの上限（2 進の桁数）
    let full = args.iter().any(|a| a == "--full");
    let mut big_budget = BigBudget::default();
    if let Some(b) = args.iter().find_map(|a| a.strip_prefix("--bits=")) {
        big_budget.max_bits = b.parse().map_err(|_| format!("--bits= の値が数値ではありません: {b}"))?;
    }
    let flags = ["--json", "--proof", "--model", "--latex", "--standalone", "--full"];
    let args: Vec<String> = args
        .iter()
        .filter(|a| !flags.contains(&a.as_str()) && !a.starts_with("--rel=") && !a.starts_with("--bits="))
        .cloned()
        .collect();
    let args = args.as_slice();
    // --latex に対応していない命令
    let no_latex = ["table", "lt", "thm52", "hardy", "blen", "rules", "forms"];
    if let Some(cmd) = args.first().filter(|c| tex.is_some() && no_latex.contains(&c.as_str())) {
        return Err(format!("{cmd} は --latex に対応していません"));
    }
    // 【Rust メモ】スライスに対するパターンマッチで引数の形を場合分けできる
    match args {
        [cmd, a] if cmd == "ord" && !all_nat(&[a]) => {
            // 文字が順序数の worm：o(A) < Γ0、標準形、Ω_ξ（ξ = 0, 1, 2 と A に現れる文字）
            let w = parse_o(a)?;
            if let Some(t) = tex {
                t.emit(vec![latex::ordinal_block(Some(&format!("o({})", w.to_latex())), &w.ordinal(), 6)]);
                return Ok(());
            }
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
            if let Some(t) = tex {
                let o = Veblen::from(&w.ordinal());
                t.emit(vec![latex::ordinal_block(Some(&format!("o({})", w.to_latex())), &o, 6)]);
                return Ok(());
            }
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
            if let Some(t) = tex {
                t.emit(vec![worm_cmp_tex(&x.to_latex(), x.cmp0(&y), &y.to_latex(), &x.ordinal().to_latex(), &y.ordinal().to_latex())]);
                return Ok(());
            }
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
            if let Some(t) = tex {
                t.emit(vec![worm_cmp_tex(&x.to_latex(), x.cmp0(&y), &y.to_latex(), &x.ordinal().to_latex(), &y.ordinal().to_latex())]);
                return Ok(());
            }
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
            // 繰り返しでまとめたまま進める（長い worm でも速い。長さは多倍長）
            let mut c = CWorm::new(&w).ok_or_else(|| format!("文字は {} 以下にしてください", cworm::MAX_LETTER))?;
            let show = |c: &CWorm| -> String {
                if c.is_top() {
                    return "⊤".to_string();
                }
                match c.to_worm(COMPACT_MIN_LETTERS as u64 - 1) {
                    Some(plain) => plain.to_string(),
                    None => {
                        let v = c.view(200);
                        format!("{}{}", cworm::text(&v.shapes), if v.truncated { " …" } else { "" })
                    }
                }
            };
            if let Some(t) = tex {
                let mut rows = Vec::new();
                for m in 0..=limit as u64 {
                    let formula = if c.is_top() {
                        "\\top".to_string()
                    } else {
                        match c.to_worm(COMPACT_MIN_LETTERS as u64 - 1) {
                            Some(plain) => plain.to_latex(),
                            None => {
                                let v = c.view(200);
                                format!("{}{}", cworm::latex(&v.shapes), if v.truncated { "\\cdots" } else { "\\top" })
                            }
                        }
                    };
                    rows.push(BattleRow { formula, ordinal: Some(c.ordinal().to_latex()) });
                    if c.is_top() {
                        break;
                    }
                    if m < limit as u64 {
                        c.step(m + 1);
                    }
                }
                let more = !c.is_top();
                t.emit(vec![latex::battle_table(&rows, "A", Some("o(A_{k})"), more)]);
                return Ok(());
            }
            let mut steps = 0;
            for m in 0..=limit as u64 {
                let len = c.len();
                let len = if len.decimal_digits() <= 12 { len.to_decimal() } else { len.summary() };
                println!("{m:>4}: {}    （長さ {len}）    o = {}", show(&c), shorten(c.ordinal().to_string(), 200));
                steps = m;
                if c.is_top() || m == limit as u64 {
                    break;
                }
                c.step(m + 1);
            }
            if steps == limit as u64 && !c.is_top() {
                println!("（{limit} ステップで打ち切り）");
            }
            Ok(())
        }
        [cmd, s] if cmd == "rc" => match s.parse::<Sequent>() {
            Ok(seq) => rc_cmd(seq, full_proof, json, tex),
            // 自然数で読めなければ、モダリティが順序数のシーケントとして読む
            Err(e) => match s.parse::<Sequent<Veblen>>() {
                Ok(seq) => rc_cmd(seq, full_proof, json, tex),
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
                let k: Veblen = parse_ordinal(n).map_err(|e| format!("n が順序数として読めません: {e}"))?;
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
                show_proof(&wc::prove(&parse(&l)?, &parse(&r)?)?, json, tex)
            } else {
                show_proof(&wc::prove(&parse_o(&l)?, &parse_o(&r)?)?, json, tex)
            }
        }
        [cmd, n, a, b] if cmd == "wclt" => {
            if let (Ok(k), true) = (n.parse::<u32>(), all_nat(&[a, b])) {
                show_proof(&wc::prove_lt(k, &parse(a)?, &parse(b)?)?, json, tex)
            } else {
                let k: Veblen = parse_ordinal(n).map_err(|e| format!("n が順序数として読めません: {e}"))?;
                show_proof(&wc::prove_lt(k, &parse_o(a)?, &parse_o(b)?)?, json, tex)
            }
        }
        [cmd, a] if cmd == "ordinal" => {
            let x = parse_ordinal(a)?;
            if let Some(t) = tex {
                t.emit(vec![latex::ordinal_block(None, &x, 6)]);
                return Ok(());
            }
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
            let p = |s: &str| parse_ordinal(s);
            let (x, y) = (p(a)?, p(b)?);
            let rel = match x.cmp(&y) {
                Ordering::Less => "<",
                Ordering::Equal => "=",
                Ordering::Greater => ">",
            };
            if let Some(t) = tex {
                t.emit(vec![latex::display(&latex::relation(&x.to_latex(), rel, &y.to_latex()))]);
                return Ok(());
            }
            println!("{x}  {rel}  {y}");
            Ok(())
        }
        [cmd, a] if cmd == "bracket" => {
            let x = parse_bracket(a)?;
            if let Some(t) = tex {
                t.emit(vec![latex::ordinal_block(Some(&format!("o^{{*}}({})", x.to_latex())), &x.ordinal(), 6)]);
                return Ok(());
            }
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
            if let Some(t) = tex {
                let l = format!("o^{{*}}({})", x.to_latex());
                let r = format!("o^{{*}}({})", y.to_latex());
                t.emit(vec![latex::display(&format!(
                    "{l} = {} {} {} = {r}",
                    ox.to_latex(),
                    sym(syn),
                    oy.to_latex()
                ))]);
                return Ok(());
            }
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
            if let Some(t) = tex {
                let view = ModelView::from_rcbi(m, Some(&q.rhs));
                t.emit(vec![
                    format!(
                        "% RC_BI: {}; finite model M_A of the left-hand side (bold: the right-hand side holds)",
                        if d.holds { "derivable" } else { "not derivable" }
                    ),
                    latex::display(&latex::verdict(&q.lhs.to_latex(), &q.rhs.to_latex(), d.holds)),
                    t.model(&view),
                ]);
                return Ok(());
            }
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
            if let Some(t) = tex {
                t.emit(vec![format!("% M_A for A = {}", a.to_latex()), t.model(&ModelView::from_rcbi(&m, None))]);
                return Ok(());
            }
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
            if let Some(t) = tex {
                let o = rcbi_order::compare(&x, &y).ok_or("比較できません（Thm 4.11 に反する）")?;
                t.emit(vec![latex::display(&latex::rcbi_relation(&x.to_latex(), o, &y.to_latex()))]);
                return Ok(());
            }
            println!("{x}  {}  {y}", sym(rcbi_order::compare(&x, &y)));
            Ok(())
        }
        [cmd, a, rest @ ..] if cmd == "bifs" && rest.len() <= 1 => {
            let x = parse_wbi(a)?;
            let k: u32 = match rest.first() {
                Some(s) => s.parse().map_err(|_| format!("k が数値ではありません: {s}"))?,
                None => 4,
            };
            if let Some(t) = tex {
                t.emit(vec![latex::rcbi_form(&x, k)?]);
                return Ok(());
            }
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
            if let Some(t) = tex {
                let all: Vec<rcbi::Formula> = rcbi_order::battle(&x).take(limit + 2).collect();
                let more = all.len() > limit + 1;
                let rows: Vec<BattleRow> =
                    all.iter().take(limit + 1).map(|c| BattleRow { formula: c.to_latex(), ordinal: None }).collect();
                t.emit(vec![latex::battle_table(&rows, "A", None, more)]);
                return Ok(());
            }
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
        [cmd, s] if cmd == "bwc" => {
            let goal: BwSeq = s.parse()?;
            bwc_cmd(&goal, full_proof, json, tex)
        }
        [cmd, s] if cmd == "bc" => {
            let goal: BSeq = s.parse().map_err(|e: bc::ParseError| e.to_string())?;
            bc_cmd(&goal, full_proof, json, tex)
        }
        [cmd, a] if cmd == "bracketof" => {
            let x = parse_ordinal(a)?;
            if !x.is_predicative() {
                return Err(format!("{x} は Γ0 以上（Ω・ψ を含む）なので括弧語で表せません"));
            }
            let w = Bracket::from_ordinal(&x);
            if let Some(t) = tex {
                t.emit(vec![latex::display(&format!("{} = o^{{*}}({})", x.to_latex(), w.to_latex()))]);
                return Ok(());
            }
            println!("{x}  =  {w}");
            Ok(())
        }
        [cmd, a] if cmd == "psi" => psi_cmd(&parse_ordinal(a)?, json, tex),
        [cmd, a] if cmd == "iworm" => iworm_cmd(&a.parse::<IWorm>()?, json, tex),
        [cmd, a] if cmd == "iwormof" => {
            let x = parse_ordinal(a)?;
            let w = IWorm::from_value(&x).ok_or_else(|| {
                format!("{x} は可算で ψ(e_{{Ω+1}}1) = {} 未満の数でないので、impredicative worm で表せません", Veblen::psi(iworm::top()))
            })?;
            if let Some(t) = tex {
                t.emit(vec![latex::display(&format!("{} = p({})", x.to_latex(), w.to_latex()))]);
                return Ok(());
            }
            println!("{x}  =  p({w})");
            println!("  （w^π = {}、o(w^π) = {}）", w.to_worm(), w.ordinal());
            Ok(())
        }
        [cmd, e] if cmd == "expr" => {
            let r = expr::eval_str(e)?;
            if let Some(t) = tex {
                t.emit(vec![r.latex()]);
                return Ok(());
            }
            println!("{}", r.input);
            for st in &r.steps {
                println!("  {} = {}", st.node, st.value);
                println!("      （{}）", st.rule);
                for d in &st.details {
                    println!("        {d}");
                }
            }
            println!("= {}", r.value);
            Ok(())
        }
        [cmd, x] if cmd == "forms" => {
            let v = parse_ordinal(x)?;
            for info in notation::notations() {
                let n = notation::Notation::parse(info.key).expect("一覧の書き方");
                let r = notation::render(&v, n);
                match r.note {
                    Some(why) => println!("{:<26} （{why}）", info.name),
                    None => println!("{:<26} {}", info.name, r.text),
                }
            }
            Ok(())
        }
        [cmd, rest @ ..] if cmd == "defs" && rest.len() <= 1 => {
            // 定義集：引数なしなら全部、分類（games・fundamental・functions・notations・semantics）か定義の鍵なら、それだけ
            let mut cats = glossary::all();
            if let Some(q) = rest.first() {
                if let Some(c) = cats.iter().find(|c| c.id == q.as_str()).cloned() {
                    cats = vec![c];
                } else {
                    let e = glossary::get(q).ok_or_else(|| {
                        let keys: Vec<&str> = glossary::all().iter().flat_map(|c| c.entries.iter().map(|e| e.key).collect::<Vec<_>>()).collect();
                        format!("分類（games・fundamental・functions・notations・semantics）か定義の鍵を指定してください: {q}\n鍵: {}", keys.join(" "))
                    })?;
                    let mut c = cats.into_iter().find(|c| c.entries.iter().any(|x| x.key == e.key)).expect("鍵のある分類");
                    c.entries = vec![e];
                    cats = vec![c];
                }
            }
            if let Some(t) = tex {
                // 【Rust メモ】flat_map で「分類の中の定義」を 1 列に並べ、それぞれの LaTeX を取り出す
                t.emit(cats.iter().flat_map(|c| c.entries.iter().map(|e| format!("% {} {}\n{}", e.key, e.symbol, e.latex))).collect());
                return Ok(());
            }
            if json {
                println!("{}", serde_json::to_string_pretty(&cats).map_err(|e| e.to_string())?);
                return Ok(());
            }
            for c in &cats {
                println!("■ {}（{}）\n  {}\n", c.name, c.id, c.lead);
                for e in &c.entries {
                    let research = if e.research { "（研究中）" } else { "" };
                    println!("{}  {}  [{}]{research}", e.symbol, e.name, e.key);
                    for l in &e.lines {
                        println!("  ・{l}");
                    }
                    if !e.examples.is_empty() {
                        println!("  例（場合ごとに 1 つ、wormlab で計算）:");
                        for x in &e.examples {
                            println!("    {}  ⟶  {}", x.case, x.text);
                            // 同じ場合のほかの例
                            for m in &x.more {
                                println!("        {m}");
                            }
                        }
                    }
                    if !e.general.is_empty() {
                        println!("  一般の場合: {}", e.general.join(" "));
                    }
                    if !e.special.is_empty() {
                        println!("  特殊な場合: {}", e.special.join(" "));
                    }
                    if !e.related.is_empty() {
                        println!("  関連: {}", e.related.join(" "));
                    }
                    println!("  出典: {}\n", e.source);
                }
            }
            Ok(())
        }
        [cmd, rest @ ..] if cmd == "rules" && rest.len() <= 1 => {
            // 【Rust メモ】`rest @ ..` は「残りの引数をまとめて rest という名前で受ける」パターン
            let systems = match rest.first() {
                Some(id) => vec![wormlab_core::rules::get(id).ok_or_else(|| format!("体系は rc・wc・bc・bwc・rcbi のどれかです: {id}"))?],
                None => wormlab_core::rules::all(),
            };
            if json {
                println!("{}", serde_json::to_string_pretty(&systems).map_err(|e| e.to_string())?);
            } else {
                let texts: Vec<String> = systems.iter().map(|s| s.text()).collect();
                print!("{}", texts.join("\n"));
            }
            Ok(())
        }
        [cmd, a, o, b] if cmd == "calc" => {
            // 【Rust メモ】`ok_or_else` は `None` を `Err(…)` に変える（`?` でそのまま返せる）
            let op = arith::Op::parse(o).ok_or_else(|| format!("演算は + か * か ^ です（x・** も可）: {o}"))?;
            let c = arith::calc(op, &parse_ordinal(a)?, &parse_ordinal(b)?).map_err(|e| e.to_string())?;
            if let Some(t) = tex {
                t.emit(vec![c.latex()]);
                return Ok(());
            }
            println!("{}", c.lhs);
            for st in &c.steps {
                println!("  = {}", st.plain);
                println!("      （{}）", st.note);
            }
            Ok(())
        }
        [cmd, a, b] if cmd == "icmp" => {
            let (x, y) = (a.parse::<IWorm>()?, b.parse::<IWorm>()?);
            let (px, py) = (x.value(), y.value());
            let rel = match px.cmp(&py) {
                Ordering::Less => "<",
                Ordering::Equal => "=",
                Ordering::Greater => ">",
            };
            if let Some(t) = tex {
                t.emit(vec![latex::display(&format!(
                    "p({}) = {} {rel} {} = p({})",
                    x.to_latex(),
                    px.to_latex(),
                    py.to_latex(),
                    y.to_latex()
                ))]);
                return Ok(());
            }
            println!("p({x}) = {px}  {rel}  {py} = p({y})");
            Ok(())
        }
        [cmd, a, rest @ ..] if cmd == "bbattle" && rest.len() <= 1 => {
            let limit: usize = match rest.first() {
                Some(s) => s.parse().map_err(|_| format!("上限が数値ではありません: {s}"))?,
                None => 30,
            };
            let x = parse_bracket(a)?;
            if let Some(t) = tex {
                let all: Vec<Bracket> = x.battle().take(limit + 2).collect();
                let more = all.len() > limit + 1;
                let rows: Vec<BattleRow> = all
                    .iter()
                    .take(limit + 1)
                    .map(|c| BattleRow {
                        formula: if c.to_string().len() >= COMPACT_MIN_CHARS { repeats::bracket(c).latex } else { c.to_latex() },
                        ordinal: Some(c.ordinal().to_latex()),
                    })
                    .collect();
                t.emit(vec![latex::battle_table(&rows, "a", Some("o^{*}(a_{k})"), more)]);
                return Ok(());
            }
            let mut steps = 0;
            for (i, cur) in x.battle().take(limit + 1).enumerate() {
                let raw = cur.to_string();
                let size = raw.len();
                let shown = battle_line(raw, size >= COMPACT_MIN_CHARS, || repeats::bracket(&cur), size);
                println!("{i:>4}: {shown}    o* = {}", cur.ordinal());
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
            // 長さ G(m)：括弧語の battle を o* が ε₀ 未満に落ちるまで動かし、そこから閉じた形
            // α{m} = D(α, m+1) を多倍長で（bc.md §3）。a'_2 は 2 ステップで worm 3 3 3 = ω^ω^ω^3 になる
            println!("G({m}) {}", big_line(hierarchy::worm_battle_length_any(&a.ordinal(), big_budget), full));
            match m {
                0 | 1 => {}
                2 => println!("  （2 ステップ後に worm 3 3 3 = ω^ω^ω^3 になり、そこから閉じた形で数えた下界）"),
                _ => println!("  （2 ステップ後の括弧語の o* は Veblen 関数の入れ子で、ε₀ 未満に落ちるまで動かしきれない）"),
            }
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
            if let Some(t) = tex {
                t.emit(vec![latex::ordinal_block(None, &x, k + 1)]);
                return Ok(());
            }
            if !x.is_limit() {
                println!("{x} は極限順序数ではありません（後続なら α[n] は直前の数）");
                return Ok(());
            }
            println!("{:>3}  {:<40} worm の基本列（正規形の worm から 1 ステップ）", "n", format!("{x}[n]（標準）"));
            for n in 0..=k {
                let std = x.fundamental(n).map_or("-（Ω・ψ を含む数は未対応）".to_string(), |y| y.to_string());
                let worm = hierarchy::worm_fundamental(&x, n as usize).map_or("-".to_string(), |y| y.to_string());
                println!("{n:>3}  {:<40} {}", shorten(std, 40), shorten(worm, 60));
            }
            Ok(())
        }
        [cmd, a, n] if cmd == "hardy" => {
            let x = parse_ordinal(a)?;
            if !x.is_predicative() {
                return Err(format!("{x} は Ω・ψ を含むので未対応です（基本列をまだ定義していない）"));
            }
            let n: u128 = n.parse().map_err(|_| format!("n が数値ではありません: {n}"))?;
            let n = BigNat::from(n);
            println!("H_{x}({n}) {}", big_line(hierarchy::hardy_big(&x, &n, big_budget), full));
            println!("f_{x}({n}) {}", big_line(hierarchy::fast_growing_big(&x, &n, big_budget), full));
            Ok(())
        }
        [cmd, a] if cmd == "blen" => {
            let x = parse_ordinal(a)?;
            if !x.is_predicative() {
                return Err(format!("{x} は Ω・ψ を含むので未対応です（基本列をまだ定義していない）"));
            }
            let budget = Budget { max_steps: 10_000_000 };
            let show = |v: Option<u64>| v.map_or("1000 万ステップで打ち切り".to_string(), |v| v.to_string());
            println!("α = {x}");
            // ε₀ 未満は閉じた形 α{m} = D(α, m+1) を多倍長で（G_α の合成、worm を作らないので速い）。
            // ε₀ 以上は括弧語の battle を実際に動かす
            let worm = big_line(hierarchy::worm_battle_length_any(&x, big_budget), full).trim_start_matches("= ").to_string();
            println!("  worm battle（正規形の worm から）: {worm}");
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
  wormlab psi    <順序数>          ψ(ξ)（Worms and spiders Def 6.19）：C(ξ) の判定と崩し（--json 可）
  wormlab iworm  <W_Ω の worm>     impredicative worm の翻訳 w^π・o(w^π)・値 p(w)（--json 可）
  wormlab iwormof <順序数>         p(w) = ξ となる impredicative worm（ξ < ψ(e_{Ω+1}1)）
  wormlab icmp   <worm> <worm>     impredicative worm の値 p の比較
  wormlab calc   <順序数> <+|*|^> <順序数>  順序数の足し算・掛け算・べき乗と計算の過程（* と ^ は '' でくくる）
  wormlab bcmp   <括弧語> <括弧語> 順序数を使わない比較（Veblen 経由と照合）
  wormlab bc     \"φ |- ψ\"          Bracket Calculus で判定。真なら BC の導出（--proof で全行）
  wormlab bwc    \"a |- b\"          括弧語だけの体系 BWC（WC の BC 版）で判定・導出（--proof で全行）
  wormlab bi     \"A |- B\"          RC_BI（Pakhomov–Lazar）で判定（変数なし。--model で M_A を表示）
  wormlab bimodel <式>             RC_BI の有限モデル M_A とフレーム条件の検査
  wormlab bicmp  <式> <式>         RC_BI の順序 <¹₁・≡¹₁ で比較
  wormlab bifs   <式> [k]          式の形と基本列 (A)_1..k
  wormlab bibattle <式> [上限]     RC_BI の式の battle
  wormlab bbattle <括弧語> [上限]  括弧語の battle
  wormlab thm52  <m>               ATR₀ から独立な命題（Thm 52）の出発点 a'_m
  wormlab fs     <順序数> [k]      標準の基本列 α[0..k] と worm が作る列
  wormlab hardy  <順序数> <n>      Hardy 関数 H_α(n) と急増加関数 f_α(n)（多倍長。--full・--bits=N）
  wormlab blen   <順序数>          worm battle と標準 battle の長さ（多倍長。--full で全桁、--bits=N で上限）
  wormlab rules  [体系]            公理と規則の一覧（体系は rc・wc・bc・bwc・rcbi、省略なら全部。--json 可）
  wormlab expr   <式>              順序数の式（+・·・^・φ(α,β)・ε_α・e^α(β)・ψ(α)）を、使った定義つきで 1 段ずつ標準形に
  wormlab defs [分類|鍵]           定義集（games・functions・notations・semantics か、worm-battle などの鍵。--json・--latex 可）
  wormlab forms  <順序数>          同じ順序数をいろいろな標準形で（Veblen・φ だけ・超指数と ψ・worm・括弧語・impredicative worm）
worm の書き方: \"1 0 2\", \"<1><0><2>T\", \"⊤\" など
  文字が順序数の worm: \"<ω+1><0><ε_0>\" または \"ω+1, 0, ε_0\"（ord・cmp・lt・wc・wclt で使える）
順序数の書き方: \"ω^(ω + 1)·2 + 3\", \"ε_0\", \"φ(2, 0)\"（ω は w、ε は e、φ は phi でも可）
  Γ0 以上: \"Ω\"（O でも可）、\"ψ(ε_(Ω + 1))\"（ψ は psi でも可）。ψ(0) = Γ0
impredicative worm: 括弧語に文字 Ω を加えたもの。例 \"Ω\" = Γ0、\"((()))Ω\" = ψ(ε_(Ω+1))
括弧語の書き方: \"()\" = 1, \"(())\" = ω, \"((()))\" = ε_0（⊤ は省略）
BC の式: \"(a)φ\"（a は括弧語）。例 \"((()))p\" = ⟨ω⟩p、\"(())(p & ()q)\"。括弧語はそのまま式として読む
RC_BI の式: <1>_2 = ⟨1⟩₂、<2>_3 = ⟨2⟩₃、<1>_w = ⟨1⟩_ω、D = ↓、N = ∇、T = ⊤（<1>, <2> だけなら ⟨1⟩₁, ⟨2⟩₂）
LaTeX: --latex で LaTeX の断片、--standalone でプリアンブルつきの文書（pdflatex にかけられる）
  証明は bussproofs の証明木（木で 120 ノードまで）と行番号つきの一覧、モデルは TikZ
  --rel=all で閉包後の辺も描く。--rel=1,down のように関係を選べる（R¹₁ → 11、R↓ → down、RC の R_1 → 1）
  table・lt・thm52・hardy・blen は対象外";

/// 多倍長の値の 1 行表示：「= 123…」「> 2^(…)」など。`full` ならちょうどの値は全桁。
fn big_line(v: Option<BigValue>, full: bool) -> String {
    match v {
        None => "は計算できません（基本列が未定義）".to_string(),
        Some(BigValue::Exact(n)) if full => format!("= {}", n.to_decimal()),
        Some(BigValue::Exact(n)) => {
            let s = n.summary();
            if n.bits() > 199 { format!("= {s}（全桁は --full）") } else { format!("= {s}") }
        }
        Some(BigValue::Above2Pow(k)) => {
            let k = k.summary();
            let k = if k.chars().all(|c| c.is_ascii_digit()) { k } else { format!("({k})") };
            format!("> 2^{k}（途中の値が上限を超えたので下界。上限は --bits=N で変えられる）")
        }
        Some(BigValue::AtLeast(n)) => format!("≥ {}（計算の量（回数・語の長さ・仕事量）の上限で打ち切り）", n.summary()),
    }
}

/// ψ(ξ) の計算の中身：K(ξ)、ξ ∈ C(ξ) か、崩した先 z0、impredicative worm での表し方。
fn psi_cmd(x: &Veblen, json: bool, tex: Option<&Tex>) -> Result<(), String> {
    let p = Veblen::psi(x.clone());
    let z0 = p.as_psi().expect("ψ の値").clone();
    let normal = x.in_c(x);
    let iw = IWorm::from_value(&p);
    if let Some(t) = tex {
        let mut s = format!("\\psi({}) = {}", x.to_latex(), p.to_latex());
        if let Some(w) = &iw {
            s.push_str(&format!(" = p({})", w.to_latex()));
        }
        t.emit(vec![latex::display(&s)]);
        return Ok(());
    }
    if json {
        let v = json!({
            "xi": x, "psi": p, "in_c": normal, "max_k": x.max_k(), "z0": z0,
            "iworm": iw.as_ref().map(|w| w.to_string()),
        });
        println!("{}", serde_json::to_string_pretty(&v).map_err(|e| e.to_string())?);
        return Ok(());
    }
    println!("ξ       = {x}");
    match x.max_k() {
        None => println!("K(ξ)    = ∅（ψ を含まない）"),
        Some(k) => println!("max K(ξ) = {k}"),
    }
    if normal {
        println!("ξ ∈ C(ξ)：はい（正規形）");
    } else {
        println!("ξ ∈ C(ξ)：いいえ → ξ 以上で z ∈ C(z) となる最小の z = {z0} に崩す");
    }
    println!("ψ(ξ)    = {p}");
    match &iw {
        Some(w) => println!("impredicative worm：p({w}) = ψ(ξ)（{} 記号）", w.size()),
        None => println!("（ψ(e_{{Ω+1}}1) 以上なので impredicative worm では表せない）"),
    }
    Ok(())
}

fn iworm_cmd(w: &IWorm, json: bool, tex: Option<&Tex>) -> Result<(), String> {
    let (u, o, p) = (w.to_worm(), w.ordinal(), w.value());
    let nf = w.normal_form();
    if let Some(t) = tex {
        t.emit(vec![latex::align(&[
            ("p(".to_string() + &w.to_latex() + ")", format!("= \\pi({})", u.to_latex())),
            (String::new(), format!("= {}", p.to_latex())),
        ])]);
        return Ok(());
    }
    if json {
        let v = json!({
            "iworm": w, "translation": u.to_string(), "ordinal": o, "value": p,
            "normal_form": nf, "depth": w.depth(), "size": w.size(),
        });
        println!("{}", serde_json::to_string_pretty(&v).map_err(|e| e.to_string())?);
        return Ok(());
    }
    println!("w        = {w}（入れ子 {}、{} 記号）", w.depth(), w.size());
    println!("w^π      = {u}");
    println!("o(w^π)   = {o}{}", if o.is_countable() { "（可算なので π = o）" } else { "（Ω 以上なので π = ψ(−Ω + o)）" });
    println!("p(w)     = {p}");
    if nf != *w {
        println!("標準形   = {nf}");
    }
    Ok(())
}

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
