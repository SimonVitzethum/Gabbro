//! **`noalias` on a WRITABLE pointer parameter, and the cases that must NOT get it**
//! (`dokumente/A1-OWN-PAPER.md`, slice 4).
//!
//! `noalias` is a promise to the optimiser about the whole call. It is emitted beyond `own`
//! only for a function that is not `pub`, is called from a body of its unit, has its address
//! nowhere taken, is named by no entry/boot/concurrent item, and whose DECLARED `effects` name
//! nothing but its own pointer parameters. *A guard that only asserts the positive case is green
//! for a criterion that is too wide*, so every refusing row differs from the accepting one in
//! exactly one place.

const KOPF: &str = "pub type Z = { x : u32, y : u32, };\n\
                    pub table T count 4 { slot { v : u32, } }\n";

/// The `define` line of `name` in the IR of `<KOPF><zusatz>`.
fn define(zusatz: &str, name: &str) -> String {
    let quelle = format!("module na::t {{\n{KOPF}{zusatz}}}\n");
    let (baum, mut absagen) = gabbro_syntax::lies("noalias.gab", &quelle);
    let ir = gabbro_check::llvm::emittiere_llvm(
        &baum,
        &mut absagen,
        gabbro_check::gatter::Bau::Auslieferung,
        &gabbro_check::llvm::ZIEL_X86_64,
    );
    ir.lines()
        .find(|l| l.starts_with("define") && l.contains(&format!("@\"{name}\"")))
        .unwrap_or_else(|| panic!("no define for {name} in:\n{ir}"))
        .to_string()
}

const SETZE: &str = "impl fn setze(a : ptr<normal, rw> Z, b : ptr<normal, r> Z)\n\
                     \x20   effects { writes a, reads b } costs <= 8 ops { a.x = b.y; }\n";
const RUFER: &str = "pub fn aussen(p : ptr<normal, rw> Z, q : ptr<normal, r> Z)\n\
                     \x20   effects { writes p, reads q } costs <= 32 ops { setze(p, q); }\n";

#[test]
fn eine_intern_gerufene_funktion_traegt_noalias_am_schreibbaren_zeiger() {
    let d = define(&format!("{SETZE}{RUFER}"), "setze");
    assert!(d.contains("noundef noalias %p0"), "{d}");
    // The read-only parameter is NOT marked: a read-only pointer may legitimately alias.
    assert!(!d.contains("noalias %p1"), "{d}");
}

#[test]
fn die_exportierte_funktion_traegt_es_nicht() {
    let d = define(&format!("{SETZE}{RUFER}"), "aussen");
    assert!(!d.contains("noalias"), "{d}");
}

#[test]
fn eine_nicht_gerufene_funktion_traegt_es_nicht() {
    // The twin of the first row: same function, no caller in the unit.
    let d = define(SETZE, "setze");
    assert!(!d.contains("noalias"), "{d}");
}

#[test]
fn eine_funktion_deren_adresse_genommen_wird_traegt_es_nicht() {
    let zusatz = format!(
        "{SETZE}type Tab = {{ f : fn(ptr<normal, rw> Z, ptr<normal, r> Z) effects {{ writes a }} costs <= 8 ops, }};\n\
         impl fn nimm(t : ptr<normal, rw> Tab) effects {{ writes t }} costs <= 8 ops {{ t.f = &setze; }}\n{RUFER}"
    );
    let d = define(&zusatz, "setze");
    assert!(!d.contains("noalias"), "{d}");
}

#[test]
fn eine_funktion_die_einen_traeger_beim_namen_nennt_traegt_es_nicht() {
    // `T` is named in the effects: the pointee may BE that table, reached by name as well.
    let zusatz = "impl fn setze(a : ptr<normal, rw> Z, b : ptr<normal, r> Z)\n\
                  \x20   effects { writes a, reads b, reads T } costs <= 8 ops { a.x = b.y; }\n\
                  pub fn aussen(p : ptr<normal, rw> Z, q : ptr<normal, r> Z)\n\
                  \x20   effects { writes p, reads q, reads T } costs <= 32 ops { setze(p, q); }\n";
    let d = define(zusatz, "setze");
    assert!(!d.contains("noalias"), "{d}");
}
