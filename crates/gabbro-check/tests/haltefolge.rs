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

#[test]
fn summeninvariante_wird_ausgerechnet() {
    // `x + y == 100` at the release: the section establishes `x == 30` and `y == 70`, and the sum is
    // evaluated (the release analysis knew equalities between cells and constants, not arithmetic).
    let kopf = "table P count 2 { slot { x : u32 in 0 .. 100, } }
table Q count 2 { slot { y : u32 in 0 .. 100, } }
lock K protects { P, Q } rank 0 held <= 50 ops invariant P.slots[0].x + Q.slots[0].y == 100;
";
    let f = |y: u32| {
        format!(
            "module t {{\n{kopf}impl fn f(k : ptr<normal, rw> P, m : ptr<normal, rw> Q) effects {{ writes k.slots, writes m.slots, locks K }} costs <= 40 ops {{
    locks K {{ k.slots[0].x = 30; m.slots[0].y = {y}; }}
}}\n}}\n"
        )
    };
    sauber(&f(70));
    faellt(&f(71), "N511");
}

#[test]
fn traverse_ueber_die_slots_liest_keine_zelle() {
    // a pool of two threads walks `slots of T` and writes each cell under the lock: the walk reads no cell,
    // so the unguarded `T` of the object is no footprint read (the model's `Stmt.traverse`)
    let pool = |rumpf: &str| {
        modul(&format!(
            "impl fn f() effects {{ reads T, writes T.slots, locks L }} costs <= 40000 ops {{
    traverse e over slots of T by unvisited touches writes T.slots {{ {rumpf} }}
}}
concurrent {{ f, f }};"
        ))
    };
    sauber(&pool("locks L { T.slots[e].v = 1; }"));
    // the body's own unguarded read of a cell stays refused
    faellt(&pool("let x : u32 in 0 .. 100 = T.slots[e].v;"), "N291");
}

#[test]
fn adresse_als_argument_traegt_die_wirkung_zum_rufer() {
    // `&T` names the table: the callee's `writes p.slots` is `writes T.slots` at the caller, so the race
    // component reads the pair instead of refusing it as unresolvable (`W003`)
    let kopf = "table T count 4 { slot { v : u32 in 0 .. 100, } }
table U count 4 { slot { v : u32 in 0 .. 100, } }
impl fn w(p : ptr<normal, rw> T, i : index into T) effects { writes p.slots } costs <= 8 ops { p.slots[i].v = 3; }
";
    // two roots writing the same table through the call: a real race
    faellt(
        &format!("module t {{\n{kopf}impl fn a() effects {{ writes T.slots }} costs <= 20 ops {{ w(&T, 0); }}
impl fn b() effects {{ writes T.slots }} costs <= 20 ops {{ w(&T, 1); }}
concurrent {{ a, b }};\n}}\n"),
        "N300",
    );
    // a root writing another table beside it: disjoint, accepted
    sauber(&format!(
        "module t {{\n{kopf}impl fn a() effects {{ writes T.slots }} costs <= 20 ops {{ w(&T, 0); }}
impl fn b() effects {{ writes U.slots }} costs <= 20 ops {{ U.slots[0].v = 1; }}
concurrent {{ a, b }};\n}}\n"
    ));
}

#[test]
fn zeigerkopie_ist_dieselbe_faehigkeit() {
    // a local pointer copy, or `&T` bound to a local, names the table like the parameter does
    for kopf in ["let q : ptr<normal, rw> T = p;", "let q = p;"] {
        faellt(
            &modul(&format!(
                "impl fn f(p : ptr<normal, rw> T, i : index into T) effects {{ writes p.slots }} costs <= 100 ops {{ {kopf} q.slots[i].v = 3; }}"
            )),
            "H007",
        );
        sauber(&modul(&format!(
            "impl fn f(p : ptr<normal, rw> T, i : index into T) requires Held(L) effects {{ writes p.slots, locks L }} costs <= 100 ops {{ {kopf} q.slots[i].v = 3; }}"
        )));
    }
    faellt(
        &modul("impl fn f(i : index into T) effects { writes T.slots } costs <= 100 ops { let q : ptr<normal, rw> T = &T; q.slots[i].v = 3; }"),
        "H007",
    );
}

#[test]
fn lokaler_name_ist_kein_geschuetztes_feld() {
    // a local `v` shares its name with the protected field `v`: reading it reads the local
    sauber(&modul("impl fn f(w : u32 in 0 .. 9) -> u32 in 0 .. 9 effects { pure } costs <= 10 ops { let v : u32 in 0 .. 9 = w; return v; }"));
}
