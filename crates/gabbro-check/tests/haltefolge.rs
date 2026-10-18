//! **The rules the differential harness added, each with its poison and its clean twin.**
//!
//! The harness (`tests/differenzial`) found programs the Rust checker accepted and the Lean model
//! refused. Each class is fixed in the checker; this file pins the boundary on both sides:
//!
//! * `N588` -- a lock taken while the body already holds it (block, signature, callee);
//! * `N587` -- a call whose callee `requires Held(L)` with `L` not held at the call;
//! * `H007`/`H020` -- an access through a pointer parameter, and a READ covered only by the
//!   `effects { locks L }` line;
//! * `E008` -- a callee that writes an arena is a different place from the caller's `writes s`;
//! * `E005` -- a write at a table and a write through a pointer to it are one place (the model
//!   names the table): the checker had refused the pair.

use gabbro_syntax::diag::Stufe;

fn codes(quelle: &str) -> Vec<String> {
    let (baum, mut absagen) = gabbro_syntax::lies("haltefolge", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let mut c: Vec<String> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    c.sort();
    c.dedup();
    c
}

fn sauber(q: &str) {
    let c = codes(q);
    assert!(c.is_empty(), "must be clean, falls with {c:?}:\n{q}");
}

fn faellt(q: &str, code: &str) {
    let c = codes(q);
    assert!(c.iter().any(|x| x == code), "must fall with {code}, got {c:?}:\n{q}");
}

const KOPF: &str = "table T count 4 { slot { v : u32 in 0 .. 100, } }
lock L protects { T } rank 0 held <= 100 ops;
";

fn modul(rumpf: &str) -> String {
    format!("module t {{\n{KOPF}{rumpf}\n}}\n")
}

#[test]
fn n588_gleiche_sperre_im_block() {
    faellt(
        &modul("impl fn f() effects { writes T.slots, locks L } costs <= 100 ops { locks L { locks L { T.slots[0].v = 1; } } }"),
        "N588",
    );
    sauber(&modul(
        "impl fn f() effects { writes T.slots, locks L } costs <= 100 ops { locks L { T.slots[0].v = 1; } }",
    ));
}

#[test]
fn n588_gehalten_per_signatur_und_genommen() {
    faellt(
        &modul("impl fn f() requires Held(L) effects { writes T.slots, locks L } costs <= 100 ops { locks L { T.slots[0].v = 1; } }"),
        "N588",
    );
    sauber(&modul(
        "impl fn f() requires Held(L) effects { writes T.slots, locks L } costs <= 100 ops { T.slots[0].v = 1; }",
    ));
}

#[test]
fn n588_gleiche_sperre_durch_aufruf() {
    let g = "impl fn g() effects { writes T.slots, locks L } costs <= 40 ops { locks L { T.slots[0].v = 1; } }\n";
    faellt(
        &modul(&format!("{g}impl fn f() effects {{ writes T.slots, locks L }} costs <= 100 ops {{ locks L {{ g(); }} }}")),
        "N588",
    );
    // the callee only REQUIRES the lock: held by signature, no second take
    sauber(&modul(
        "impl fn g() requires Held(L) effects { writes T.slots, locks L } costs <= 40 ops { T.slots[0].v = 1; }
impl fn f() effects { writes T.slots, locks L } costs <= 100 ops { locks L { g(); } }",
    ));
}

#[test]
fn n587_aufruf_ohne_geforderte_sperre() {
    let g = "impl fn g() requires Held(L) effects { writes T.slots, locks L } costs <= 40 ops { T.slots[0].v = 1; }\n";
    // the effects line names the lock and holds nothing
    faellt(
        &modul(&format!("{g}impl fn f() effects {{ writes T.slots, locks L }} costs <= 100 ops {{ g(); }}")),
        "N587",
    );
    sauber(&modul(&format!(
        "{g}impl fn f() effects {{ writes T.slots, locks L }} costs <= 100 ops {{ locks L {{ g(); }} }}"
    )));
    sauber(&modul(&format!(
        "{g}impl fn f() requires Held(L) effects {{ writes T.slots, locks L }} costs <= 100 ops {{ g(); }}"
    )));
}

#[test]
fn zugriff_durch_zeiger_braucht_die_sperre() {
    faellt(
        &modul("impl fn f(p : ptr<normal, rw> T, i : index into T) effects { writes p.slots } costs <= 100 ops { p.slots[i].v = 3; }"),
        "H007",
    );
    sauber(&modul(
        "impl fn f(p : ptr<normal, rw> T, i : index into T) requires Held(L) effects { writes p.slots, locks L } costs <= 100 ops { p.slots[i].v = 3; }",
    ));
    // passing the pointer value on is no access
    sauber(&modul(
        "impl fn w(p : ptr<normal, rw> T, i : index into T) requires Held(L) effects { writes p.slots, locks L } costs <= 8 ops { p.slots[i].v = 3; }
impl fn f(p : ptr<normal, rw> T) requires Held(L) effects { writes p.slots, locks L } costs <= 100 ops { w(p, 0); }",
    ));
}

#[test]
fn lesen_nur_unter_der_wirkungszeile_faellt() {
    faellt(
        &modul("impl fn f() -> u32 in 0 .. 100 effects { reads T.slots, writes T.slots, locks L } costs <= 100 ops {
    locks L { T.slots[0].v = 1; }
    let x : u32 in 0 .. 100 = T.slots[1].v;
    return x;
}"),
        "H020",
    );
    sauber(&modul("impl fn f() -> u32 in 0 .. 100 effects { reads T.slots, writes T.slots, locks L } costs <= 100 ops {
    locks L {
        T.slots[0].v = 1;
        let x : u32 in 0 .. 100 = T.slots[1].v;
        return x;
    }
    return 0;
}"));
}

#[test]
fn arena_im_gerufenen_ist_ein_anderer_ort() {
    let kopf = "arena R capacity 2 .. 8 of u32;\nstatic mut s : u32 in 0 .. 100 = 7;\nimpl fn ga() effects { writes R } costs <= 20 ops { reset R; }\n";
    faellt(
        &format!("module t {{\n{kopf}impl fn f() effects {{ writes s }} costs <= 100 ops {{ ga(); s = 1; }}\n}}\n"),
        "E008",
    );
    sauber(&format!(
        "module t {{\n{kopf}impl fn f() effects {{ writes s, writes R }} costs <= 100 ops {{ ga(); s = 1; }}\n}}\n"
    ));
}

#[test]
fn zeiger_und_tabelle_sind_ein_ort() {
    // declared through the pointer, performed at the table: one place, as the model has it
    sauber(&modul(
        "impl fn f(p : ptr<normal, rw> T) requires Held(L) effects { writes p.slots, locks L } costs <= 100 ops { T.slots[0].v = 1; }",
    ));
    // a table the effects do not name stays refused
    faellt(
        &format!(
            "module t {{\n{KOPF}table U count 4 {{ slot {{ v : u32 in 0 .. 100, }} }}\n\
             impl fn f(p : ptr<normal, rw> T) requires Held(L) effects {{ writes p.slots, locks L }} costs <= 100 ops {{ U.slots[0].v = 1; }}\n}}\n"
        ),
        "E005",
    );
}
