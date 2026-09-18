//! Lane 234 — early exit out of a `traverse` to an outer label (TODO §-1 wave B).
//!
//! What this file pins is the shape the future labelled-traverse exit generalises:
//! today a `traverse` carries no label (`ast.rs`: the `Traverse` struct has no `marke`
//! field; `schleifen.rs:114`), so `leave`/`next` inside one can only name an
//! ENCLOSING `retry`/`forever`. The emitter must route that exit past the generated
//! `for` to the outer label — a `goto`, never a `break` (which would leave the `for`,
//! i.e. the traverse, instead of the named loop) — and release the locks taken
//! inside the traverse body before jumping.
//!
//! What this file does NOT build, and why: the windowed walk (`traverse … from
//! <start> count <len>`) ends at parse with `P001` (lane 222, `parse.rs:4146-4174`;
//! pinned in `sprechprobe.rs` as `lane222_windowed_traverse_refused_by_name`), so no
//! checker pass and no emitter arm ever sees a window — there is no `Domaene`
//! variant and no `Traverse` field for one. A lowering for it is unbuildable from
//! `emit.rs` + `tests/` alone (it needs a parse/AST lane first); an arm for an
//! unrepresentable form would be dead code, not a lowering. The C forms emitted
//! here (`for`, `goto`, labels) already have their `pruefe-cformen.py` rows
//! (`stmt:for-counting`, `stmt:goto`), so no new row is owed.

const HEAD: &str = "module t { table W count 16 { slot { a : bool, } }\n\
    lock L protects { W } rank 0 held <= 400 ops;\n\
    extern fn wacht() -> never effects { diverges } costs <= 0 ops;\n\
    extern fn fertig() -> bool effects { pure } costs <= 1 ops;\n";

fn emit(source: &str) -> String {
    let (tree, mut refusals) = gabbro_syntax::lies("traverse_exit", source);
    assert_eq!(
        refusals.fehler_zahl(),
        0,
        "the probe does not parse:\n{}",
        refusals.zeige(source)
    );
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    assert_eq!(
        refusals.fehler_zahl(),
        0,
        "the probe does not check:\n{}",
        refusals.zeige(source)
    );
    gabbro_check::emit::emittiere(&tree, &mut refusals)
}

/// The refusal codes AND notes of a program that must NOT check: the negative
/// pin below needs the note, not just the code (the note states the scope).
fn fehler_mit_notizen(source: &str) -> Vec<(String, String, Vec<String>)> {
    let (tree, mut refusals) = gabbro_syntax::lies("traverse_exit", source);
    assert_eq!(
        refusals.fehler_zahl(),
        0,
        "the probe does not parse:\n{}",
        refusals.zeige(source)
    );
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == gabbro_syntax::diag::Stufe::Fehler)
        .map(|a| (a.code.to_string(), a.text.clone(), a.notizen.clone()))
        .collect()
}

fn service_with(exit: &str) -> String {
    // No `costs` on `dienst`: the body holds a `forever`, which has no total --
    // its promise is `per_pass`, not `costs` (`K003`; `kosten.rs::ohne_summe`).
    // An omitted `costs` is not a promise, so there is nothing to hold (lane
    // 191); the per-pass budget is still held (`K007`) at the loop itself.
    format!(
        "{HEAD}impl fn dienst(w : ptr<normal, rw> W) effects {{ reads w.slots, writes w.slots, locks L }}\n\
         {{ forever d per_pass bounded 200 ops on_exceeded wacht effects {{ reads w.slots, writes w.slots, locks L }}\n\
           {{ traverse i over slots of w by unvisited touches reads w.slots, writes w.slots, locks L\n\
             {{ w.slots[i].a = fertig(); locks L {{ if w.slots[i].a {{ {exit} d; }} }} }} }} }} }}"
    )
}

/// `leave d;` from inside a `traverse` inside `forever d` leaves the FOREVER, not
/// the generated `for`: the exit is `goto d_ende;` past the loop, with the lock
/// taken inside the traverse body released immediately before the jump.
#[test]
fn leave_from_traverse_reaches_the_outer_label() {
    let c = emit(&service_with("leave"));
    assert!(
        c.contains("for (uint32_t i = 0;"),
        "the traverse is the counting `for`:\n{c}"
    );
    let head = c.find("for (uint32_t i").expect("the traverse header");
    let jump = c.find("goto d_ende;").expect("`leave` becomes a goto");
    assert!(
        jump > head,
        "the goto stands INSIDE the traverse loop, not beside it:\n{c}"
    );
    assert!(
        c.contains("d_ende: ;"),
        "the outer end label stands past the `forever`:\n{c}"
    );
    assert!(
        !c.contains("break;"),
        "a `break` would leave the `for`, not the named loop:\n{c}"
    );
    let release = c[..jump].rfind("L_gib();").expect("the lock is released");
    assert!(
        c[release..jump].lines().count() <= 2,
        "the release stands immediately before the jump:\n{c}"
    );
}

/// `next d;` from inside a `traverse` continues the FOREVER: `goto d_weiter;`
/// with the same release before the jump.
#[test]
fn next_from_traverse_reaches_the_outer_label() {
    let c = emit(&service_with("next"));
    let head = c.find("for (uint32_t i").expect("the traverse header");
    let jump = c.find("goto d_weiter;").expect("`next` becomes a goto");
    assert!(
        jump > head,
        "the goto stands INSIDE the traverse loop, not beside it:\n{c}"
    );
    assert!(
        c.contains("d_weiter: ;"),
        "the continue label stands inside the `forever`:\n{c}"
    );
    assert!(
        !c.contains("continue;"),
        "a `continue` would resume the `for`, not the named loop:\n{c}"
    );
    let release = c[..jump].rfind("L_gib();").expect("the lock is released");
    assert!(
        c[release..jump].lines().count() <= 2,
        "the release stands immediately before the jump:\n{c}"
    );
}

/// `leave suche;` inside a `traverse` with NO enclosing labeled loop is refused:
/// a traverse carries no label (`schleifen.rs`: the `Traverse` arm pushes
/// nothing onto the label scope), so no label is in scope here. This is the
/// negative half of the two probes above — the exit they pin can only name an
/// OUTER loop, never the traverse itself.
#[test]
fn leave_naming_no_label_from_traverse_falls_with_s001() {
    let quelle = format!(
        "{HEAD}impl fn dienst(w : ptr<normal, rw> W) effects {{ reads w.slots, writes w.slots }} \
         costs <= 500 ops\n\
         {{ traverse i over slots of w by unvisited touches reads w.slots, writes w.slots\n\
           {{ w.slots[i].a = fertig(); if w.slots[i].a {{ leave suche; }} }} }} }}"
    );
    let fehler = fehler_mit_notizen(&quelle);
    assert_eq!(
        fehler.iter().map(|(c, _, _)| c.clone()).collect::<Vec<_>>(),
        vec!["S001".to_string()],
        "naming no label from a traverse falls with S001 and nothing else: {fehler:?}"
    );
    assert!(
        fehler.iter().any(|(_, t, n)| t.contains("targets no enclosing loop label")
            && n.iter().any(|x| x.contains("no label is in scope here"))),
        "the refusal states the empty scope — the traverse contributes no label: {fehler:?}"
    );
}

/// `leave suche;` inside a `traverse` inside `forever d` is refused too, and the
/// refusal names the EXACT scope: `d`, nothing more. The traverse adds no label
/// to it — the set a future traverse label would extend.
#[test]
fn leave_past_the_outer_label_from_traverse_falls_with_s001() {
    let quelle = format!(
        "{HEAD}impl fn dienst(w : ptr<normal, rw> W) effects {{ reads w.slots, writes w.slots }}\n\
         {{ forever d per_pass bounded 200 ops on_exceeded wacht effects {{ reads w.slots, writes w.slots }}\n\
           {{ traverse i over slots of w by unvisited touches reads w.slots, writes w.slots\n\
             {{ w.slots[i].a = fertig(); if w.slots[i].a {{ leave suche; }} }} }} }} }}"
    );
    let fehler = fehler_mit_notizen(&quelle);
    assert_eq!(
        fehler.iter().map(|(c, _, _)| c.clone()).collect::<Vec<_>>(),
        vec!["S001".to_string()],
        "naming past the outer label falls with S001 and nothing else: {fehler:?}"
    );
    assert!(
        fehler
            .iter()
            .any(|(_, _, n)| n.iter().any(|x| x.contains("im Geltungsbereich: d"))),
        "the scope note names exactly the outer label — the traverse adds none: {fehler:?}"
    );
}
