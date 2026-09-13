//! Lane 126 -- the reference fixture as a real Gabbro program.
//!
//! `beispiele/104-referenz.gab` is the Lean reference fixture
//! (`grammatik/Grammatik/ReferenzB.lean`: `refD`/`refP`) in surface syntax.
//! These tests print the checker's Lean view of it (whatever `lean.rs`
//! produces: the duty register `module` and the program datum `program`)
//! and hold its declaration shape against `refD`: the same tables, the same
//! guard, the same write/read signatures. Every difference is a finding --
//! each assert names the Lean fixture fact it is held against, and
//! `MUSE-REPORT-126.md` books the ones that do not line up.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::Stufe;

fn quelle() -> String {
    let pfad = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("beispiele")
        .join("104-referenz.gab");
    std::fs::read_to_string(&pfad).expect("104-referenz.gab is readable")
}

/// Parse and check; the file is a corpus example, so zero errors are owed.
fn baum() -> Programm {
    let q = quelle();
    let (baum, mut absagen) = gabbro_syntax::lies("104-referenz.gab", &q);
    gabbro_check::pruefe(&baum, &mut absagen);
    let fehler: Vec<String> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| format!("[{}] {}", a.code, a.text.lines().next().unwrap_or("")))
        .collect();
    assert!(fehler.is_empty(), "104-referenz.gab must check clean: {fehler:?}");
    baum
}

/// Every item inside the file's module.
fn items(baum: &Programm) -> Vec<&Item> {
    let mut out = Vec::new();
    for item in &baum.items {
        if let ItemArt::Modul(m) = &item.art {
            out.extend(m.items.iter());
        } else {
            out.push(item);
        }
    }
    out
}

fn funktion<'a>(baum: &'a Programm, name: &str) -> &'a FnDecl {
    items(baum)
        .into_iter()
        .find_map(|i| match &i.art {
            ItemArt::Funktion(f) if f.name.text == name => Some(f),
            _ => None,
        })
        .unwrap_or_else(|| panic!("routine `{name}` is declared"))
}

fn wirkungen(f: &FnDecl) -> Vec<String> {
    f.effects
        .as_ref()
        .map(|w| w.liste.iter().map(|x| x.art.text()).collect())
        .unwrap_or_default()
}

/// The checker accepts the fixture program with zero errors.
#[test]
fn checker_accepts_referenz() {
    let _ = baum();
}

/// The duty register: print it, then hold its shape against `refD`.
#[test]
fn lean_duty_view_matches_refD() {
    let b = baum();
    let duty = gabbro_check::lean::module(&b, "beispiele/104-referenz.gab");
    // The Lean view, printed: this is the checker's reading of the program.
    println!("{duty}");
    // The line that has to add up: 2 routines, 3 duties (2 ensures + 1 call
    // precondition), all carried, none refused.
    assert!(
        duty.contains("@duty 1  beispiele/104-referenz.gab  total 3  goals 3  refused 0"),
        "duty balance line moved:\n{duty}"
    );
    // `refD.typ () () = .int 0 100`: the slot shape carries the range.
    assert!(
        duty.contains("| .slot \"Konto\" _ \"stand\" => some (.intIn 0 100)"),
        "shapeOf must carry stand in 0..100:\n{duty}"
    );
    // `refSigEin.schreibt = true`: the writer writes the table...
    assert!(
        duty.contains("def einzahlen_writes : List String := [\"Konto\"]"),
        "einzahlen must write Konto:\n{duty}"
    );
    // ...`refSigLies.schreibt = false`: the reader writes nothing.
    assert!(
        duty.contains("def lies_writes : List String := []"),
        "lies must write nothing:\n{duty}"
    );
    // `refSigEin.params = [.int 0 10]`: the parameter range travels in the
    // precondition (the index bound `intIn 0 1` is `refD.count = 2`).
    assert!(
        duty.contains("(.hasShape \"b\" (.intIn 0 10))"),
        "einzahlen_pre must bound b in 0..10:\n{duty}"
    );
    // `refEnsEin` (old slot <= new slot): the duty channel carries `old`.
    assert!(
        duty.contains("\"old#1\"") && duty.contains(".bin .le"),
        "einzahlen_post must carry old <= new:\n{duty}"
    );
    // `refEnsLies` (result = slot): the duty channel carries `result`, and
    // `refLies_erg`: the answer is promised in 0..100.
    assert!(
        duty.contains("\"result\"") && duty.contains(".bin .eq"),
        "lies_post must carry result == slot:\n{duty}"
    );
    assert!(
        duty.contains("0 ≤ x ∧ x ≤ 100"),
        "lies_post must promise the answer in 0..100:\n{duty}"
    );
    // Both bodies are expressed (no refusal on either routine).
    let rs = gabbro_check::lean::routines(&b);
    assert_eq!(rs.len(), 2, "two routines, einzahlen and lies");
    for r in &rs {
        assert!(r.body.is_some(), "`{}` has a Lean body", r.name);
        assert!(r.refused.is_none(), "`{}` is not refused", r.name);
    }
}

/// The declaration shape beside `refD`, read from the checker tables and the AST.
#[test]
fn erklaerung_gestalt_matches_refD() {
    let b = baum();
    // One table (`refD.Tab = Unit`), count 2, one field in 0..100.
    let unit = gabbro_check::lean::Unit::sammle(&b);
    assert_eq!(unit.tables.len(), 1, "one table, like refD.Tab = Unit");
    let konto = unit.tables.get("Konto").expect("table Konto");
    assert_eq!(konto.count, Some(2), "count 2, like refD.count");
    assert_eq!(
        konto.fields,
        vec![("stand".to_string(), Some(gabbro_check::lean::Shape::IntIn(0, 100)))],
        "one .int 0 100 field, like refD.typ"
    );
    // One lock (`refD.Lock = Unit`) guarding the field (`refD.braucht`).
    let sperren: Vec<&LockDecl> = items(&b)
        .into_iter()
        .filter_map(|i| match &i.art {
            ItemArt::Lock(l) => Some(l),
            _ => None,
        })
        .collect();
    assert_eq!(sperren.len(), 1, "one lock, like refD.Lock = Unit");
    assert_eq!(sperren[0].name.text, "M");
    assert!(
        sperren[0].schuetzt.iter().any(|o| o.text().contains("stand")),
        "M protects the stand field, like refD.braucht"
    );
    // `einzahlen`: one 0..10 parameter beside the carrier/index the surface
    // needs, no result; writes the table under the lock.
    let ein = funktion(&b, "einzahlen");
    assert!(ein.ergebnis.is_none(), "einzahlen returns nothing, like refEin_erg");
    assert_eq!(ein.parameter.len(), 3, "carrier k, index i, amount b");
    assert_eq!(ein.parameter[2].name.text, "b");
    let w = wirkungen(ein);
    assert!(w.iter().any(|x| x == "writes k.slots"), "einzahlen writes: {w:?}");
    assert!(w.iter().any(|x| x == "locks M"), "einzahlen holds M: {w:?}");
    assert!(
        ein.requires.iter().any(|p| format!("{p:?}").contains("Held")),
        "einzahlen runs under the held lock, like refSigEin.haelt"
    );
    // `lies`: carrier/index only, one 0..100 result; reads under the lock.
    let lies = funktion(&b, "lies");
    assert!(lies.ergebnis.is_some(), "lies returns, like refLies_erg");
    assert_eq!(lies.parameter.len(), 2, "carrier k, index i");
    let w = wirkungen(lies);
    assert!(w.iter().any(|x| x == "reads k.slots"), "lies reads: {w:?}");
    assert!(!w.iter().any(|x| x.starts_with("writes")), "lies writes nothing: {w:?}");
    assert!(w.iter().any(|x| x == "locks M"), "lies holds M: {w:?}");
}

/// The program datum (`gabbro lean`): print it and hold its Lean view against
/// `refD` (lane 141 closes findings F4/F5 of lane 126). Contracts live in the
/// duty register (test above) AND in this datum: each `_post` is stated over
/// entry state, exit state and result, carrying `old` and `result`; the exact
/// ranges stand in `_pre`, `placesRanged` and `wellFormedRanged`; the lock and
/// the guard facts stand in `locks`, `lockProtects`, `tableGuards` and each
/// `<fn>_held`.
#[test]
fn lean_program_view_carries_refD() {
    let b = baum();
    let prog =
        gabbro_check::lean::program(&b, &["beispiele/104-referenz.gab".to_string()]);
    println!("{prog}");
    assert!(
        prog.contains("@program 1  units 1  routines 2  bodies 2  refused 0  places 1"),
        "program balance line moved:\n{prog}"
    );
    // The call survives into the body datum (the write-call-return shape).
    assert!(
        prog.contains("(.call \"lies\""),
        "einzahlen_body must call lies:\n{prog}"
    );
    // `refEnsEin` (old slot <= new slot): the program datum carries it over
    // entry, exit and result -- F4 closed, no drop by name.
    assert!(
        prog.contains("def einzahlen_post (s s' : State) (r : Option Value) : Prop"),
        "einzahlen_post must be two-state:\n{prog}"
    );
    assert!(
        prog.contains("\"old#1\"") && prog.contains(".bin .le"),
        "einzahlen_post must carry old <= new:\n{prog}"
    );
    // `refEnsLies` (result = slot): `result` is bound, not dropped.
    assert!(
        prog.contains("def lies_post (s s' : State) (r : Option Value) : Prop"),
        "lies_post must be two-state:\n{prog}"
    );
    assert!(
        prog.contains("\"result\"") && prog.contains(".bin .eq"),
        "lies_post must carry result == slot:\n{prog}"
    );
    assert!(
        !prog.contains("old-state") && !prog.contains("result-in-ensures"),
        "no ensures may drop by name any more:\n{prog}"
    );
    // `refD.typ () () = .int 0 100`: the exact range beside the shape name.
    assert!(
        prog.contains("(\"Konto\", \"stand\", \"isInt\")"),
        "places keeps the shape name:\n{prog}"
    );
    assert!(
        prog.contains("(\"Konto\", \"stand\", 0, 100)"),
        "placesRanged must carry stand in 0..100:\n{prog}"
    );
    assert!(
        prog.contains(".intIn 0 100"),
        "wellFormedRanged must bound the slot:\n{prog}"
    );
    // `refSigEin.params = [.int 0 10]`: the parameter range in the precondition.
    assert!(
        prog.contains("(.hasShape \"b\" (.intIn 0 10))"),
        "einzahlen_pre must bound b in 0..10:\n{prog}"
    );
    // F5 closed: the lock is named, the guard facts resolve, each signature
    // names what it holds (`refD.braucht`, `refSigEin.haelt`, `refSigLies.haelt`).
    assert!(
        prog.contains("def locks : List String := [\"M\"]"),
        "locks must name M:\n{prog}"
    );
    assert!(
        prog.contains("(\"M\", \"stand\")"),
        "lockProtects must carry M protects stand:\n{prog}"
    );
    assert!(
        prog.contains("(\"Konto\", \"stand\", [\"M\"])"),
        "tableGuards must resolve Konto.stand to M:\n{prog}"
    );
    assert!(
        prog.contains("def einzahlen_held : List String := [\"M\"]"),
        "einzahlen_held must hold M:\n{prog}"
    );
    assert!(
        prog.contains("def lies_held : List String := [\"M\"]"),
        "lies_held must hold M:\n{prog}"
    );
}

/// Lane 141, F1 of lane 126: the `concurrent` set of `104-referenz.gab` is
/// classified by the certificate census (erased: the emitter writes nothing
/// for it), so no `UNCLASSIFIED` remains and stage 7 of the emission check
/// passes over a concurrent program.
#[test]
fn concurrent_is_classified() {
    let b = baum();
    let e = gabbro_check::zeugnis::erhebe(&b);
    assert!(
        e.unzugeordnet.is_empty(),
        "every construct of 104 must classify: {:?}",
        e.unzugeordnet
    );
    assert_eq!(
        e.posten.get("concurrent"),
        Some(&1),
        "the concurrent set must census as one posten: {:?}",
        e.posten
    );
}
