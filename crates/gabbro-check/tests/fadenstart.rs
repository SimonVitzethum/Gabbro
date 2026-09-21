//! **The hosted thread start `start { f, g };` at the checker** (fix lane F4, review G12
//! F2/F3, 2026-09-22).
//!
//! Poison and positive twins for every rule the statement owes since this lane:
//!
//! * the roots are call-graph edges -- a `pure` starter falls with `E008`, a starter that
//!   declares its roots' effects checks clean;
//! * the statement costs the sum of the roots' declared costs plus two per root -- `K001`
//!   below the sum, clean at it;
//! * `N458` root shape, `N459` duplicate root, `N460` a root the runtime starts already,
//!   `N461` a start under a holding context, `N462` a root that is not pool-safe;
//! * `W003` for a root that resolves to nothing (lane 253's rule, pinned here as its
//!   handoff list asked).

use gabbro_syntax::diag::Stufe;

const KOPF: &str = "static mut g : u64 = 0;
static mut h : u64 = 0;
lock L protects { g } rank 0 held <= 100 ops;
impl fn arbeiterA() effects { writes g, locks L } costs <= 20 ops { locks L { g = 1; } }
impl fn arbeiterB() effects { writes g, locks L } costs <= 20 ops { locks L { g = 2; } }
impl fn leser() effects { reads g, locks L } costs <= 20 ops { locks L { let x = g; } }";

fn codes(rumpf: &str) -> Vec<String> {
    let quelle = format!("module t {{\n{KOPF}\n{rumpf}\n}}\n");
    let (baum, mut absagen) = gabbro_syntax::lies("fadenstart", &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

fn faellt(rumpf: &str, code: &str) {
    let c = codes(rumpf);
    assert!(c.iter().any(|x| x == code), "expected {code}, fell with {c:?}");
}

fn sauber(rumpf: &str) {
    let c = codes(rumpf);
    assert!(c.is_empty(), "the positive twin must check clean, fell with {c:?}");
}

// ---- the clean shape -------------------------------------------------------------

#[test]
fn zwei_bewachte_wurzeln_sind_sauber() {
    sauber(
        "impl fn chef() effects { writes g, locks L } costs <= 100 ops { start { arbeiterA, arbeiterB }; }
concurrent { chef };",
    );
}

#[test]
fn lesende_wurzel_ist_sauber() {
    sauber("impl fn chef() effects { reads g, locks L } costs <= 100 ops { start { leser }; }");
}

// ---- call-graph edge (E008) ------------------------------------------------------

#[test]
fn reiner_starter_faellt_mit_e008() {
    faellt(
        "impl fn chef() effects { pure } costs <= 100 ops { start { arbeiterA }; }",
        "E008",
    );
}

// ---- costs (K001) ----------------------------------------------------------------

#[test]
fn kosten_unter_der_summe_fallen() {
    // 2 x (20 + 2) = 44 > 43.
    faellt(
        "impl fn chef() effects { writes g, locks L } costs <= 43 ops { start { arbeiterA, arbeiterB }; }",
        "K001",
    );
}

#[test]
fn kosten_an_der_summe_halten() {
    sauber(
        "impl fn chef() effects { writes g, locks L } costs <= 44 ops { start { arbeiterA, arbeiterB }; }",
    );
}

// ---- N458 root shape -------------------------------------------------------------

#[test]
fn n458_wurzel_mit_parameter() {
    faellt(
        "impl fn p(x : u64) effects { pure } costs <= 5 ops { }
impl fn chef() effects { pure } costs <= 100 ops { start { p }; }",
        "N458",
    );
}

#[test]
fn n458_wurzel_mit_ergebnis() {
    faellt(
        "impl fn r() -> u64 effects { pure } costs <= 5 ops { return 1; }
impl fn chef() effects { pure } costs <= 100 ops { start { r }; }",
        "N458",
    );
}

#[test]
fn n458_wurzel_mit_signatursperre() {
    faellt(
        "impl fn s() requires Held(L) effects { writes g } costs <= 5 ops { g = 1; }
impl fn chef() effects { writes g } costs <= 100 ops { start { s }; }",
        "N458",
    );
}

#[test]
fn n458_fremde_wurzel() {
    faellt(
        "extern fn fremd() effects { pure } costs <= 5 ops;
impl fn chef() effects { pure } costs <= 100 ops { start { fremd }; }",
        "N458",
    );
}

// ---- N459 duplicate ----------------------------------------------------------------

#[test]
fn n459_wurzel_doppelt() {
    faellt(
        "impl fn chef() effects { writes g, locks L } costs <= 100 ops { start { arbeiterA, arbeiterA }; }",
        "N459",
    );
}

// ---- N460 ownership ----------------------------------------------------------------

#[test]
fn n460_concurrent_mitglied() {
    faellt(
        "impl fn chef() effects { writes g, locks L } costs <= 100 ops { start { arbeiterA }; }
concurrent { arbeiterA, chef };",
        "N460",
    );
}

#[test]
fn n460_zwilling_ohne_mitgliedschaft_ist_sauber() {
    // The same roots, started by the statement only: one owner each.
    sauber(
        "impl fn chef() effects { writes g, locks L } costs <= 100 ops { start { arbeiterA }; }
concurrent { arbeiterB, chef };",
    );
}

// ---- N461 holding context --------------------------------------------------------

#[test]
fn n461_unter_locks() {
    faellt(
        "impl fn chef() effects { writes g, locks L } costs <= 100 ops { locks L { start { arbeiterA }; } }",
        "N461",
    );
}

#[test]
fn n461_unter_signatursperre() {
    faellt(
        "impl fn chef() requires Held(L) effects { writes g, locks L } costs <= 100 ops { start { arbeiterA }; }",
        "N461",
    );
}

#[test]
fn n461_zwilling_nach_dem_block_ist_sauber() {
    sauber(
        "impl fn chef() effects { writes g, locks L } costs <= 100 ops { locks L { g = 3; } start { arbeiterA }; }",
    );
}

// ---- N462 pool-safe roots --------------------------------------------------------

#[test]
fn n462_ungeschuetzte_schreibung() {
    faellt(
        "impl fn frei() effects { writes h } costs <= 5 ops { h = 1; }
impl fn chef() effects { writes h } costs <= 100 ops { start { frei }; }",
        "N462",
    );
}

#[test]
fn n462_ueber_einen_gerufenen() {
    faellt(
        "impl fn hilf() effects { writes h } costs <= 5 ops { h = 1; }
impl fn frei() effects { writes h } costs <= 10 ops { hilf(); }
impl fn chef() effects { writes h } costs <= 100 ops { start { frei }; }",
        "N462",
    );
}

#[test]
fn n462_lesen_eines_geschriebenen_traegers() {
    // The root only READS `h`, but somebody (`schreiber`) writes it unguarded.
    faellt(
        "impl fn schreiber() effects { writes h } costs <= 5 ops { h = 1; }
impl fn liest() effects { reads h } costs <= 5 ops { let x = h; }
impl fn chef() effects { reads h } costs <= 100 ops { start { liest }; }",
        "N462",
    );
}

#[test]
fn n462_zwilling_niemand_schreibt_ist_sauber() {
    sauber(
        "static nur : u64 = 4;
impl fn liest() effects { reads nur } costs <= 5 ops { let x = nur; }
impl fn chef() effects { reads nur } costs <= 100 ops { start { liest }; }",
    );
}

// ---- W003 (lane 253, pinned) -----------------------------------------------------

#[test]
fn w003_unbekannte_wurzel() {
    faellt(
        "impl fn chef() effects { pure } costs <= 100 ops { start { gibtesnicht }; }",
        "W003",
    );
}
