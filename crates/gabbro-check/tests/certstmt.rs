//! Statement certificates from Rust: positives plus one refusal per family.
//!
//! Positives pin the exact printed `CertEnd2` term; refusals pin the code
//! (`CS001`-`CS005`) and the named form. Probes parse only: the printer reads
//! the AST the same way `zeugnis::erhebe` does.

use gabbro_check::certstmt::{BodyCert, zeuge_funktion};
use gabbro_syntax::ast::Programm;

fn parse(quelle: &str) -> Programm {
    let (baum, absagen) = gabbro_syntax::lies("probe.gab", quelle);
    assert_eq!(
        absagen.fehler_zahl(),
        0,
        "the probe does not parse: {}",
        absagen.zeige(quelle)
    );
    baum
}

fn read(relativ: &str) -> Programm {
    let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join(relativ);
    let quelle =
        std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
    parse(&quelle)
}

fn gedruckt(baum: &Programm, name: &str) -> String {
    match zeuge_funktion(baum, name).unwrap_or_else(|| panic!("no function {name}")) {
        BodyCert::Gedruckt { lean, .. } => lean,
        BodyCert::Abgewiesen { weigerung } => {
            panic!("{name} refused {}: {}", weigerung.code, weigerung.grund)
        }
    }
}

fn abgewiesen(baum: &Programm, name: &str) -> gabbro_check::certstmt::Refusal {
    match zeuge_funktion(baum, name).unwrap_or_else(|| panic!("no function {name}")) {
        BodyCert::Abgewiesen { weigerung } => weigerung,
        BodyCert::Gedruckt { lean, .. } => panic!("{name} printed, expected refusal: {lean}"),
    }
}

/// A bare `return;` prints the `.ret` body.
#[test]
fn bare_return_prints() {
    let b = parse("module m { impl fn f() effects { pure } costs <= 1 ops { return; } }");
    assert_eq!(gedruckt(&b, "f"), "(.liftE .ret)");
}

/// Returning an integer parameter prints `retWert` with the result range.
#[test]
fn return_param_prints() {
    let b = parse(
        "module m { type K = u32 in 0 .. 10;
          impl fn f(x : K) -> K effects { pure } costs <= 1 ops { return x; } }",
    );
    assert_eq!(gedruckt(&b, "f"), "(.liftE (.retWert (.var 0) 0 10))");
}

/// `let` with a range annotation prints `bind`; the tail reads the new head.
#[test]
fn let_binds() {
    let b = parse(
        "module m { type D3 = u32 in 3 .. 3;
          impl fn f() -> D3 effects { pure } costs <= 2 ops
          { let y : D3 = 1 + 2; return y; } }",
    );
    assert_eq!(
        gedruckt(&b, "f"),
        "(.liftE (.bind (.add (.lit 1) (.lit 2)) 3 3 (.retWert (.var 0) 3 3)))"
    );
}

/// A direct table write with a literal index prints `assignSlot`.
#[test]
fn table_write_prints() {
    let b = parse(
        "module m { type X = u32 in 0 .. 100;
          table T count 2 { slot { x : X, } }
          impl fn f() effects { writes T.slots } costs <= 2 ops
          { T.slots[0].x = 42; return; } }",
    );
    assert_eq!(
        gedruckt(&b, "f"),
        "(.liftE (.cons (.assignSlot T x (.wide 0 1 (.lit 0)) (.wide 0 100 (.lit 42))) [] .ret))"
    );
}

/// A literal value narrows to the field range under `wide`, like `weiter`.
#[test]
fn literal_widens() {
    let b = parse(
        "module m { type D10 = u32 in 0 .. 10;
          impl fn f() -> D10 effects { pure } costs <= 1 ops { return 5; } }",
    );
    assert_eq!(
        gedruckt(&b, "f"),
        "(.liftE (.retWert (.wide 0 10 (.lit 5)) 0 10))"
    );
}

/// An integer local assignment prints `assignVar` at its context index.
#[test]
fn local_assign_prints() {
    let b = parse(
        "module m { type K = u32 in 0 .. 10;
          impl fn f(x : K) -> K effects { pure } costs <= 3 ops
          { let y : K = x; y = y + 0; return y; } }",
    );
    let lean = gedruckt(&b, "f");
    assert!(
        lean.contains("(.bind (.var 0) 0 10"),
        "binds x at index 0: {lean}"
    );
    assert!(
        lean.contains("(.assignVar 0 0 10 (.add (.var 0) (.lit 0)))"),
        "assigns y at index 0: {lean}"
    );
}

/// `if` with a printable condition and falling branches prints `ite`.
#[test]
fn if_prints() {
    let b = parse(
        "module m { type K = u32 in 0 .. 10;
          impl fn f(x : K) -> K effects { pure } costs <= 3 ops
          { let y : K = x; if y < 3 { y = y + 0; } return y; } }",
    );
    let lean = gedruckt(&b, "f");
    assert!(
        lean.contains("(.ite (.lt (.var 0) (.lit 3))"),
        "condition prints: {lean}"
    );
    assert!(lean.contains("(.retWert (.var 0) 0 10)"), "tail reads y: {lean}");
}

/// A nullary direct call has the shape but needs `RufPasst` as proof.
#[test]
fn nullary_call_needs_proof() {
    let b = parse(
        "module m { impl fn g() effects { pure } costs <= 1 ops { return; }
          impl fn f() effects { pure } costs <= 2 ops { g(); return; } }",
    );
    let w = abgewiesen(&b, "f");
    assert_eq!(w.code, "CS004", "{}", w.grund);
    assert!(w.grund.contains('g'), "names the callee: {}", w.grund);
}

/// A call with arguments prints `consCall`: the count prints, the
/// `RufPasst` travels as `?hp` (filled at paste, like `refHpLiesAt`).
#[test]
fn call_with_args_prints() {
    let b = parse(
        "module m { type K = u32 in 0 .. 10;
          impl fn g(x : K) effects { pure } costs <= 1 ops { return; }
          impl fn f(a : K) effects { pure } costs <= 2 ops { g(a); return; } }",
    );
    assert_eq!(
        gedruckt(&b, "f"),
        "(.consCall g 1 [] ?hp .ret)"
    );
}

/// A call with the wrong argument count names the mismatch.
#[test]
fn call_arg_count_mismatch_refused() {
    let b = parse(
        "module m { type K = u32 in 0 .. 10;
          impl fn g(x : K) effects { pure } costs <= 1 ops { return; }
          impl fn f(a : K, c : K) effects { pure } costs <= 2 ops { g(a, c); return; } }",
    );
    let w = abgewiesen(&b, "f");
    assert_eq!(w.code, "CS005", "{}", w.grund);
    assert!(w.grund.contains('g'), "names the callee: {}", w.grund);
}

/// A call to an unknown function names the missing declaration.
#[test]
fn call_unknown_callee_refused() {
    let b = parse(
        "module m { impl fn f() effects { pure } costs <= 2 ops { g(1); return; } }",
    );
    // `g` is declared nowhere: without an arity the count cannot print.
    // (`1` is no parameter place either; the callee check fires first.)
    let w = abgewiesen(&b, "f");
    assert_eq!(w.code, "CS005", "{}", w.grund);
    assert!(w.grund.contains('g'), "names the callee: {}", w.grund);
}

/// A call argument that names no parameter place has no printed shape.
#[test]
fn call_literal_arg_refused() {
    let b = parse(
        "module m { type K = u32 in 0 .. 10;
          impl fn g(x : K) effects { pure } costs <= 1 ops { return; }
          impl fn f() effects { pure } costs <= 2 ops { g(1); return; } }",
    );
    let w = abgewiesen(&b, "f");
    assert_eq!(w.code, "CS002", "{}", w.grund);
}

/// A division has no `CertExpr` shape in this printer.
#[test]
fn division_refused() {
    let b = parse(
        "module m { type K = u32 in 0 .. 10;
          impl fn f(x : K) -> K effects { pure } costs <= 2 ops
          { let y : K = x / 2; return y; } }",
    );
    let w = abgewiesen(&b, "f");
    assert_eq!(w.code, "CS002", "{}", w.grund);
    assert!(w.grund.contains('/'), "names the operator: {}", w.grund);
}

/// A direct table write with an index variable prints `assignSlot`: the
/// `index into T` parameter carries `(0, count - 1)` and recomputes.
#[test]
fn index_var_prints() {
    let b = parse(
        "module m { type X = u32 in 0 .. 100;
          table T count 8 { slot { x : X, } }
          impl fn f(i : index into T) effects { writes T.slots } costs <= 2 ops
          { T.slots[i].x = 1; return; } }",
    );
    assert_eq!(
        gedruckt(&b, "f"),
        "(.liftE (.cons (.assignSlot T x (.var 0) (.wide 0 100 (.lit 1))) [] .ret))"
    );
}

/// The first parameter is de Bruijn 0 (the `gCtx` convention of `lean-g`):
/// `return b` with `(a, b)` reads index 1.
#[test]
fn first_param_is_index_zero() {
    let b = parse(
        "module m { type K = u32 in 0 .. 10;
          impl fn f(a : K, c : K) -> K effects { pure } costs <= 1 ops { return c; } }",
    );
    assert_eq!(
        gedruckt(&b, "f"),
        "(.liftE (.retWert (.var 1) 0 10))"
    );
}

/// A write through a read-only pointer has no printable shape.
#[test]
fn readonly_ptr_write_refused() {
    let b = parse(
        "module m { type X = u32 in 0 .. 100;
          table T count 8 { slot { x : X, } }
          impl fn f(k : ptr<normal, r> T, i : index into T) effects { reads T.slots } costs <= 2 ops
          { k.slots[i].x = 1; return; } }",
    );
    let w = abgewiesen(&b, "f");
    assert_eq!(w.code, "CS002", "{}", w.grund);
}

/// A write through an `rw` pointer with an index variable prints
/// `assignDurch` (table number is declaration order).
#[test]
fn ptr_write_var_index_prints() {
    let b = parse(
        "module m { type X = u32 in 0 .. 100;
          table T count 8 { slot { x : X, } }
          impl fn f(k : ptr<normal, rw> T, i : index into T) effects { writes T.slots } costs <= 2 ops
          { k.slots[i].x = 1; return; } }",
    );
    assert_eq!(
        gedruckt(&b, "f"),
        "(.cons2 (.assignDurch T x 0 true (.var 1) (.wide 0 100 (.lit 1))) [] .ret)"
    );
}

/// A return through a pointer prints `retDurch`.
#[test]
fn ptr_return_prints() {
    let b = parse(
        "module m { type X = u32 in 0 .. 100;
          table T count 8 { slot { x : X, } }
          impl fn f(k : ptr<normal, r> T, i : index into T) -> X effects { reads T.slots } costs <= 2 ops
          { return k.slots[i].x; } }",
    );
    assert_eq!(
        gedruckt(&b, "f"),
        "(.retDurch T x 0 (.var 1))"
    );
}

/// A `match` needs arm elaboration the printer does not do.
#[test]
fn match_refused() {
    let b = parse(
        "module probe::grund {
        reason HolFehler {
            Leer   = 1 \"die Quelle war leer\"
            Kaputt = 2 \"die Quelle war unlesbar\"
            exhaustive
        }
        impl fn code() -> u32 effects { pure } costs <= 4 ops {
            match HolFehler::Leer {
                Leer   => { return 0; }
                Kaputt => { return 1; }
            }
            return 2;
        } }",
    );
    let w = abgewiesen(&b, "code");
    assert_eq!(w.code, "CS001", "{}", w.grund);
    assert!(w.grund.contains("match"), "names the form: {}", w.grund);
}

/// A `let-else` needs the error-channel shape the printer does not do.
#[test]
fn let_else_refused() {
    let b = parse(
        "module probe::grund {
        reason HolFehler {
            Leer   = 1 \"die Quelle war leer\"
            Kaputt = 2 \"die Quelle war unlesbar\"
            exhaustive
        }
        impl fn g() -> u32 or HolFehler effects { pure } costs <= 1 ops
        { return HolFehler::Leer; }
        impl fn f() -> u32 effects { pure } costs <= 2 ops
        { let x = g() else (e) { return 0; } return x; } }",
    );
    let w = abgewiesen(&b, "f");
    assert_eq!(w.code, "CS001", "{}", w.grund);
    assert!(w.grund.contains("let-else"), "names the form: {}", w.grund);
}

/// A `traverse` loop is refused by name on a real corpus file.
#[test]
fn loop_refused() {
    let b = read("beispiele/04-schleifen.gab");
    let aus = gabbro_check::certstmt::zeige(&b);
    assert!(
        aus.contains("faellige_wecken") && aus.contains("CS001"),
        "names the loop refusal: {aus}"
    );
}

/// A bare `leave` outside a loop has no printable shape.
#[test]
fn leave_refused() {
    let b = parse(
        "module m { impl fn f() effects { pure } costs <= 1 ops
          { leave a; return; } }",
    );
    let w = abgewiesen(&b, "f");
    assert_eq!(w.code, "CS001", "{}", w.grund);
}

/// A write to an unknown table names the missing declaration.
#[test]
fn unknown_table_refused() {
    let b = parse(
        "module m { impl fn f() effects { pure } costs <= 2 ops
          { T.slots[0].x = 1; return; } }",
    );
    let w = abgewiesen(&b, "f");
    assert_eq!(w.code, "CS005", "{}", w.grund);
    assert!(w.grund.contains('T'), "names the table: {}", w.grund);
}

/// A bare `u32` result type claims no range.
#[test]
fn unranged_result_refused() {
    let b = parse(
        "module m { impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; } }",
    );
    let w = abgewiesen(&b, "f");
    assert_eq!(w.code, "CS005", "{}", w.grund);
}

/// `beispiele/104-referenz.gab`: both bodies print (lane 155 target).
/// `einzahlen` writes through the pointer with the index variable, then
/// calls `lies(k, i)`; `lies` returns through the pointer. The `const`
/// count `NKONTO` resolves, the first parameter is index 0.
#[test]
fn reference_104_prints() {
    let b = read("beispiele/104-referenz.gab");
    assert_eq!(
        gedruckt(&b, "einzahlen"),
        "(.cons2 (.assignDurch Konto stand 0 true (.var 1) (.wide 0 100 (.lit 100))) [] (.consCall lies 2 [] ?hp .ret))"
    );
    assert_eq!(
        gedruckt(&b, "lies"),
        "(.retDurch Konto stand 0 (.var 1))"
    );
}
