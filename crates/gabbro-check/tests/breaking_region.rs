//! **The region of `breaking I { … }` at the checker** (Opus agent G, OFFEN O1 / L34,
//! 2026-09-26).
//!
//! Poison and positive twins for the two rules this agent adds to `D013`:
//!
//! * `N531` -- a block that writes no carrier of `I` and calls nothing cannot let `I` rest;
//!   the same block named for the invariant it does write checks clean;
//! * `N532` -- a function that `maintains I` is not called inside `breaking I`; the same call
//!   after the block checks clean.

use gabbro_syntax::diag::Stufe;

const KOPF: &str = "const N : u32 = 4;
lock EPS protects { Paare } rank 0 held <= 200 ops;
table Paare count N {
    slot {
        a : u32,
        b : u32,
    }
    invariant paarig cost O(1) runs online :
        forall e in slots of Self : (Self.slots[e].a == 0) == (Self.slots[e].b == 0);
}
table Frei count N {
    slot {
        x : u32,
    }
    invariant frei_ok cost O(1) runs online :
        forall e in slots of Self : Self.slots[e].x == Self.slots[e].x;
}
impl fn setze(p : ptr<normal, rw> Paare, k : index into Paare)
    requires  Held(EPS)
    maintains paarig
    effects   { writes p.slots, locks EPS }
    costs     <= 8 ops
{
    breaking paarig {
        p.slots[k].a = 1;
        p.slots[k].b = 1;
    }
}";

fn codes(rumpf: &str) -> Vec<String> {
    let quelle = format!("module t {{\n{KOPF}\n{rumpf}\n}}\n");
    let (baum, mut absagen) = gabbro_syntax::lies("breaking_region", &quelle);
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

#[test]
fn der_kopf_allein_ist_sauber() {
    sauber("");
}

#[test]
fn n531_falscher_name_faellt() {
    faellt(
        "impl fn loesche(p : ptr<normal, rw> Paare, k : index into Paare)
    requires  Held(EPS)
    maintains paarig
    effects   { writes p.slots, locks EPS }
    costs     <= 8 ops
{
    breaking frei_ok {
        p.slots[k].a = 0;
        p.slots[k].b = 0;
    }
}",
        "N531",
    );
}

#[test]
fn n531_richtiger_name_ist_sauber() {
    sauber(
        "impl fn loesche(p : ptr<normal, rw> Paare, k : index into Paare)
    requires  Held(EPS)
    maintains paarig
    effects   { writes p.slots, locks EPS }
    costs     <= 8 ops
{
    breaking paarig {
        p.slots[k].a = 0;
        p.slots[k].b = 0;
    }
}",
    );
}

#[test]
fn n532_pflegende_im_block_faellt() {
    faellt(
        "impl fn beide(p : ptr<normal, rw> Paare, k : index into Paare)
    requires  Held(EPS)
    maintains paarig
    effects   { writes p.slots, locks EPS }
    costs     <= 30 ops
{
    breaking paarig {
        p.slots[k].a = 0;
        setze(p, k);
    }
}",
        "N532",
    );
}

#[test]
fn n532_pflegende_nach_dem_block_ist_sauber() {
    sauber(
        "impl fn beide(p : ptr<normal, rw> Paare, k : index into Paare)
    requires  Held(EPS)
    maintains paarig
    effects   { writes p.slots, locks EPS }
    costs     <= 30 ops
{
    breaking paarig {
        p.slots[k].a = 0;
        p.slots[k].b = 0;
    }
    setze(p, k);
}",
    );
}
