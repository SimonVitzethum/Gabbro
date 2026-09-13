//! **Export `.gab` to a G program term (`gabbro lean-g`), over snippets.**
//!
//! The file half is `beispiele/104-referenz.gab` (mechanical export checks
//! with `./lean-probe`, pinned in `grammatik/Grammatik/Export104.lean`) and
//! `beispiele/108-disjoint-start-locks.gab` (`Export108.lean`); what stands
//! here pins the same exporter over snippets -- the two positives and every
//! refusal code (`LG001`-`LG005`), so a form that stops being refused fails
//! here even where no corpus file has the shape.

use gabbro_check::lean_g::{export, Refusal};

fn tree(quelle: &str) -> gabbro_syntax::ast::Programm {
    let (baum, _) = gabbro_syntax::lies("lean_g", quelle);
    baum
}

fn refuse_of(quelle: &str) -> Refusal {
    export("lean_g", &tree(quelle)).expect_err("must refuse")
}

const KOPF: &str = "module test::leang {\n\
    table T count 4 { slot { v : u32, } }\n\
    lock L protects { T } rank 0 held <= 100 ops;\n";

fn einheit(extra: &str) -> String {
    format!("{KOPF}{extra}}}\n")
}

fn beispiele(name: &str) -> String {
    let pfad = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../beispiele").join(name);
    std::fs::read_to_string(&pfad).expect("example readable")
}

fn export_file(name: &str) -> String {
    let q = beispiele(name);
    let (baum, _) = gabbro_syntax::lies(name, &q);
    export(name, &baum).expect("example must export")
}

/// **104 exports**: the declaration, the program, the member list and both
/// decidable checks travel; names are file-derived so two exports never
/// collide.
#[test]
fn export_104_succeeds() {
    let text = export_file("104-referenz.gab");
    for teil in [
        "namespace G104_referenz",
        "inductive GTab where",
        "| Konto",
        "inductive GLock where",
        "| M",
        "def gSig_einzahlen",
        "def gSig_lies",
        "theorem gHp_einzahlen_lies",
        "def gP : Programm gD where",
        "def gFs : List gD.Fn",
        "example : programmImFragmentG gP gFs = true := by decide",
        "example : fussOrtGB gP gFs = true := by decide",
    ] {
        assert!(text.contains(teil), "104 export must contain {teil:?}");
    }
}

/// **108 exports**: two tables, two locks, two readers, no calls.
#[test]
fn export_108_succeeds() {
    let text = export_file("108-disjoint-start-locks.gab");
    for teil in [
        "namespace G108_disjoint_start_locks",
        "| T",
        "| U",
        "def gSig_read_a",
        "def gSig_read_c",
        ".int 0 4294967295",
        "example : programmImFragmentG gP gFs = true := by decide",
        "example : fussOrtGB gP gFs = true := by decide",
    ] {
        assert!(text.contains(teil), "108 export must contain {teil:?}");
    }
    assert!(
        !text.contains("RufPasst"),
        "108 has no calls, so no RufPasst proof may travel"
    );
}

/// The namespace is derived from the file name, so two exports never
/// declare the same names.
#[test]
fn namespace_comes_from_filename() {
    let text = export("a/b-c.gab", &tree(&einheit(
        "impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; }\n",
    )))
    .expect("must export");
    assert!(text.contains("namespace b_c"), "stem b-c becomes b_c");
}

/// **LG001**: an `extern fn` has no G form (no body to translate).
#[test]
fn refuses_extern_fn() {
    let w = refuse_of(&einheit(
        "extern fn e(x : u32) -> u32 effects { pure } costs <= 1 ops;\n",
    ));
    assert_eq!(w.code, "LG001", "{w}");
}

/// **LG001**: a `static` has no G form.
#[test]
fn refuses_static() {
    let w = refuse_of(&einheit("static s : u32 = 1;\n"));
    assert_eq!(w.code, "LG001", "{w}");
}

/// **LG001**: `locks L` in the effects without `requires Held(L)` would need
/// the `locks` statement, which has no form here.
#[test]
fn refuses_locks_without_held() {
    let w = refuse_of(&einheit(
        "impl fn f() -> u32 effects { reads T.slots, locks L } costs <= 4 ops\n\
        {\n    return T.slots[0].v;\n}\n",
    ));
    assert_eq!(w.code, "LG001", "{w}");
}

/// **LG001**: nothing to declare over.
#[test]
fn refuses_empty_unit() {
    let w = refuse_of("module test::leer {\n}\n");
    assert_eq!(w.code, "LG001", "{w}");
}

/// **LG002**: a float parameter has no `Ty` form.
#[test]
fn refuses_float_param() {
    let w = refuse_of(&einheit(
        "impl fn f(x : f32) -> u32 effects { pure } costs <= 1 ops { return 1; }\n",
    ));
    assert_eq!(w.code, "LG002", "{w}");
}

/// **LG003**: a call inside an `ensures` has no `Expr` form.
#[test]
fn refuses_call_in_ensures() {
    let w = refuse_of(&einheit(
        "impl fn g() -> u32 ensures g() == 1 effects { pure } costs <= 1 ops\n\
        {\n    return 1;\n}\n",
    ));
    assert_eq!(w.code, "LG003", "{w}");
}

/// **LG003**: an index outside `count` has no G form (held here, so the
/// guard check passes and the range check fires).
#[test]
fn refuses_index_out_of_range() {
    let w = refuse_of(&einheit(
        "impl fn f() -> u32 requires Held(L) effects { reads T.slots, locks L } costs <= 4 ops\n\
        {\n    return T.slots[9].v;\n}\n",
    ));
    assert_eq!(w.code, "LG003", "{w}");
}

/// **LG004**: `if` has no `Stmt` form here.
#[test]
fn refuses_wenn() {
    let w = refuse_of(&einheit(
        "impl fn f(x : u32) -> u32 effects { pure } costs <= 4 ops\n\
        {\n    if x == 1 { return 1; } else { return 0; }\n}\n",
    ));
    assert_eq!(w.code, "LG004", "{w}");
}

/// **LG004**: `let` has no `Stmt` form here (the return names nothing
/// outside the parameters, so the binding itself fires).
#[test]
fn refuses_let() {
    let w = refuse_of(&einheit(
        "impl fn f() -> u32 effects { pure } costs <= 4 ops\n\
        {\n    let z = 1; return 1;\n}\n",
    ));
    assert_eq!(w.code, "LG004", "{w}");
}

/// **LG004**: `+=` has no `Stmt` form here.
#[test]
fn refuses_compound_assign() {
    let w = refuse_of(&einheit(
        "impl fn f() effects { writes T.slots } costs <= 4 ops\n\
        {\n    T.slots[0].v += 1;\n}\n",
    ));
    assert_eq!(w.code, "LG004", "{w}");
}

/// **LG004**: only the last statement may return.
#[test]
fn refuses_mid_return() {
    let w = refuse_of(&einheit(
        "impl fn f() -> u32 effects { pure } costs <= 4 ops\n\
        {\n    return 1; return 2;\n}\n",
    ));
    assert_eq!(w.code, "LG004", "{w}");
}

/// **LG004**: a call across different held sets has no `RufPasst` term
/// (`RufPasst.hh` names exactly the witnesses the caller holds -- the
/// checker accepts the helper, the model cannot type the call).
#[test]
fn refuses_held_mismatch() {
    let w = refuse_of(&einheit(
        "impl fn h() requires Held(L) effects { reads T.slots, locks L } costs <= 4 ops\n\
        {\n    return T.slots[0].v;\n}\n\
         impl fn mit() -> u32 requires Held(L) effects { reads T.slots, locks L } costs <= 8 ops\n\
        {\n    return h();\n}\n\
         impl fn ohne() -> u32 effects { pure } costs <= 8 ops\n\
        {\n    return h();\n}\n",
    ));
    assert_eq!(w.code, "LG004", "{w}");
}

/// **LG005**: a call nobody declares names nothing.
#[test]
fn refuses_unknown_call() {
    let w = refuse_of(&einheit(
        "impl fn f() effects { pure } costs <= 4 ops\n{\n    nope();\n}\n",
    ));
    assert_eq!(w.code, "LG005", "{w}");
}

/// **LG005**: a pointer at an undeclared table names nothing.
#[test]
fn refuses_unknown_table_param() {
    let w = refuse_of(&einheit(
        "impl fn f(p : ptr<normal, r> GibtEsNicht) effects { pure } costs <= 1 ops\n\
        {\n}\n",
    ));
    assert_eq!(w.code, "LG005", "{w}");
}

/// **LG005**: `concurrent` must name declared functions.
#[test]
fn refuses_concurrent_unknown() {
    let w = refuse_of(&einheit(
        "impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; }\n\
         concurrent { f, nope };\n",
    ));
    assert_eq!(w.code, "LG005", "{w}");
}

/// **Lane 156 -- the lock invariant family travels.** A lock with an
/// `invariant` clause exports `gS : SperrInv gD` (`orte` is the `protects`
/// set, `inv` the predicate over the snapshot) plus one `by decide` per
/// protected carrier for the guard half of `SperrInvOk`.
#[test]
fn export_lock_invariant_family() {
    let q = "module test::leang_inv {\n\
        table T count 4 { slot { v : u32, } }\n\
        table U count 4 { slot { w : u32, } }\n\
        lock L protects { T, U } rank 0 held <= 100 ops invariant T.slots[0].v + U.slots[1].w == 7;\n\
        impl fn f(t : ptr<normal, rw> T, u : ptr<normal, rw> U)\n\
        requires Held(L)\n\
        effects { writes t.slots, writes u.slots, locks L } costs <= 16 ops\n\
        {\n    t.slots[0].v = 3;\n    u.slots[1].w = 4;\n}\n\
        }\n";
    let text = export("leang_inv", &tree(q)).expect("must export");
    for teil in [
        "def gS : SperrInv gD where",
        "fun s =>",
        "gS.orte",
        "gD.braucht",
        "by decide",
    ] {
        assert!(text.contains(teil), "invariant export must contain {teil:?}:\n{text}");
    }
}

/// **Lane 156 -- `beispiele/118` exports**: the conserved-sum program prints
/// the family its checker duty stands beside.
#[test]
fn export_118_succeeds() {
    let text = export_file("118-sperrinvariante-erhaltung.gab");
    for teil in [
        "namespace G118_sperrinvariante_erhaltung",
        "def gS : SperrInv gD where",
        "by decide",
    ] {
        assert!(text.contains(teil), "118 export must contain {teil:?}");
    }
}

/// **LG003**: `old` in a lock invariant has no snapshot form.
#[test]
fn refuses_old_in_invariant() {
    let q = "module test::leang_old {\n\
        table T count 4 { slot { v : u32, } }\n\
        lock L protects { T } rank 0 held <= 100 ops invariant T.slots[0].v == old(T.slots[0].v);\n\
        impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; }\n\
        }\n";
    let w = export("leang_old", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG003", "{w}");
}

/// **LG003**: a non-literal index in a lock invariant has no snapshot form.
#[test]
fn refuses_param_index_in_invariant() {
    let q = "module test::leang_idx {\n\
        table T count 4 { slot { v : u32, } }\n\
        lock L protects { T } rank 0 held <= 100 ops invariant T.slots[k].v == 1;\n\
        impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; }\n\
        }\n";
    let w = export("leang_idx", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG003", "{w}");
}
