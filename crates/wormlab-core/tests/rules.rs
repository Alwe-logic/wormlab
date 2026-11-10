//! 規則の一覧（rules.rs）の名前が、各体系の検査器の規則（enum）の名前と一致するか。
//! 一致しないと、証明図の規則名の説明（Web のツールチップ）が出なくなる。

use wormlab_core::bc::BcRule;
use wormlab_core::bwc::BwRule;
use wormlab_core::rcproof::RcRule;
use wormlab_core::rules;
use wormlab_core::wc::WcRule;

/// 一覧に載っている規則の名前（並べ替えたもの）。
fn listed(id: &str) -> Vec<String> {
    let s = rules::get(id).unwrap();
    let mut v: Vec<String> = s.groups.iter().flat_map(|g| g.rules.iter().map(|r| r.name.to_string())).collect();
    v.sort();
    v
}

fn sorted(mut v: Vec<String>) -> Vec<String> {
    v.sort();
    v
}

// 【Rust メモ】下の各関数の match は、enum の場合を全部書かないとコンパイルできない。
// 規則が増えたらここがエラーになるので、配列と rules.rs の一覧を直し忘れない。

fn rc_rules() -> Vec<String> {
    use RcRule::*;
    let all = [Id, Top, AndE1, AndE2, AndI, Cut, Nec, Four, Mono, J];
    for r in all {
        match r {
            Id | Top | AndE1 | AndE2 | AndI | Cut | Nec | Four | Mono | J => {}
        }
    }
    all.iter().map(|r| r.to_string()).collect()
}

fn wc_rules() -> Vec<String> {
    use WcRule::*;
    let all = [A1, A2, A3, Cut, Nec, R3];
    for r in all {
        match r {
            A1 | A2 | A3 | Cut | Nec | R3 => {}
        }
    }
    all.iter().map(|r| r.to_string()).collect()
}

fn bc_rules() -> Vec<String> {
    use BcRule::*;
    let all = [Id, Top, AndE1, AndE2, AndI, Cut, R3a, R3b, R4];
    for r in all {
        match r {
            Id | Top | AndE1 | AndE2 | AndI | Cut | R3a | R3b | R4 => {}
        }
    }
    all.iter().map(|r| r.to_string()).collect()
}

fn bwc_rules() -> Vec<String> {
    use BwRule::*;
    let all = [A1, A2, A3, Cut, Nec, R3];
    for r in all {
        match r {
            A1 | A2 | A3 | Cut | Nec | R3 => {}
        }
    }
    all.iter().map(|r| r.to_string()).collect()
}

#[test]
fn names_match_the_checkers() {
    assert_eq!(listed("rc"), sorted(rc_rules()));
    assert_eq!(listed("wc"), sorted(wc_rules()));
    assert_eq!(listed("bc"), sorted(bc_rules()));
    assert_eq!(listed("bwc"), sorted(bwc_rules()));
}

#[test]
fn every_system_is_listed_once() {
    let ids: Vec<&str> = rules::all().iter().map(|s| s.id).collect();
    assert_eq!(ids, ["rc", "wc", "bc", "bwc", "rcbi"]);
    // 導出を作るのは RC_BI 以外
    for s in rules::all() {
        assert_eq!(s.derivations, s.id != "rcbi", "{}", s.id);
        assert!(!s.groups.is_empty() && !s.source.is_empty());
    }
}

/// 副条件の前提の数が、検査器の前提の並び（isSide と同じ位置）と合っている。
#[test]
fn side_conditions_where_the_checkers_expect_them() {
    let bc = rules::get("bc").unwrap();
    for (name, main, side) in [("R3a", 1, 1), ("R3b", 1, 1), ("R4", 0, 1), ("Cut", 2, 0)] {
        let r = bc.rule(name).unwrap();
        assert_eq!((r.premises.len(), r.side.len()), (main, side), "BC {name}");
    }
    let bwc = rules::get("bwc").unwrap();
    for (name, main, side) in [("A3", 0, 1), ("R3", 2, 1), ("A2", 0, 0)] {
        let r = bwc.rule(name).unwrap();
        assert_eq!((r.premises.len(), r.side.len()), (main, side), "BWC {name}");
    }
}
