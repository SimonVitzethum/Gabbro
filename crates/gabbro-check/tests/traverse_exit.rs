//! Lane 252 -- early exit THROUGH a `traverse` (TODO §-1 wave B).
//!
//! A `traverse` carries no label (`SYNTAX.md` §8; `schleifen.rs`), so a
//! `leave`/`next` inside one can only name an enclosing `retry`/`forever`.
//! That exit is a `goto` past the generated `for` (`emit.rs`, never a
//! `break` -- a `break` would take the innermost loop), with the locks
//! taken inside released on the way out (`Austritt::schleifen`). What this
//! file pins: the checker-clean exit lowers, lands after the loop, and
//! releases on the path; a `leave`/`next` naming the traverse binder, and
//! the windowed walk, stay refused (S001/P001).

use gabbro_syntax::diag::Stufe;

fn fehlercodes(quelle: &str) -> Vec<String> {
    let (baum, mut absagen) = gabbro_syntax::lies("traverse_exit", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

/// Checker-clean programs lower: parse, then full `pruefe`, then `emit`.
fn c_nach_pruefung(quelle: &str) -> String {
    let (baum, mut absagen) = gabbro_syntax::lies("traverse_exit", quelle);
    assert_eq!(absagen.fehler_zahl(), 0, "probe does not parse:\n{}", absagen.zeige(quelle));
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    assert_eq!(absagen.fehler_zahl(), 0, "probe refused by checker:\n{}", absagen.zeige(quelle));
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    assert_eq!(absagen.fehler_zahl(), 0, "probe refused by emitter:\n{}", absagen.zeige(quelle));
    c
}

const KOPF: &str = "module t {\ntable W count 16 { slot { a : bool, } }\n\
    extern fn stop() -> never effects { diverges };\n\
    assume tickt \"The timer interrupts.\" falsifier sonde_tickt;\n";

/// `leave` to the outer label from inside a `slots` walk: the checker is
/// silent, the exit is a `goto` past the loop, and the code after the loop
/// is what runs next.
#[test]
fn leave_outer_lands_after_the_loop() {
    let q = format!(
        "{KOPF}impl fn f(w : ptr<normal, rw> W) effects {{ writes w.slots }}\n\
        {{ forever arbeit per_pass bounded 1024 ops on_exceeded stop \
        effects {{ writes w.slots }} progress tickt\n\
        {{ traverse i over slots of w by unvisited touches writes w.slots\n\
        {{ if w.slots[i].a {{ leave arbeit; }} }} }}\nreturn; }}\n}}"
    );
    assert!(fehlercodes(&q).is_empty(), "clean exit refused: {:?}", fehlercodes(&q));
    let c = c_nach_pruefung(&q);
    let sprung = c.find("goto arbeit_ende;").expect("`leave` lowers to a goto:\n{c}");
    let marke = c.find("arbeit_ende: ;").expect("the label stands after the loop:\n{c}");
    let rueck = c.find("return;").expect("the continuation stands:\n{c}");
    assert!(sprung < marke && marke < rueck, "exit lands at the post-loop point:\n{c}");
}

/// `next` to the outer label from inside the walk: a `goto` to the
/// in-loop continuation label -- and no end label, because nothing leaves.
#[test]
fn next_outer_continues_the_outer_pass() {
    let q = format!(
        "{KOPF}impl fn f(w : ptr<normal, rw> W) effects {{ writes w.slots }}\n\
        {{ forever arbeit per_pass bounded 1024 ops on_exceeded stop \
        effects {{ writes w.slots }} progress tickt\n\
        {{ traverse i over slots of w by unvisited touches writes w.slots\n\
        {{ if w.slots[i].a {{ next arbeit; }} }} }}\nreturn; }}\n}}"
    );
    assert!(fehlercodes(&q).is_empty(), "clean exit refused: {:?}", fehlercodes(&q));
    let c = c_nach_pruefung(&q);
    let sprung = c.find("goto arbeit_weiter;").expect("`next` lowers to a goto:\n{c}");
    let marke = c.find("arbeit_weiter: ;").expect("the continue label stands:\n{c}");
    assert!(sprung < marke, "the jump reaches the in-loop label:\n{c}");
    assert!(!c.contains("arbeit_ende:"), "a label nobody jumps to must not stand:\n{c}");
}

const KOPF_SPERRE: &str = "module t {\ntable W count 16 { slot { a : bool, } }\n\
    lock L protects { W } rank 0 held <= 400 ops;\n\
    extern fn stop() -> never effects { diverges };\n\
    assume tickt \"The timer interrupts.\" falsifier sonde_tickt;\n";

/// The exit path releases what the loop took: the release stands
/// immediately before the jump, never after the label.
#[test]
fn leave_releases_locks_on_the_exit_path() {
    let q = format!(
        "{KOPF_SPERRE}impl fn f(w : ptr<normal, rw> W) effects {{ writes w.slots, locks L }}\n\
        {{ forever arbeit per_pass bounded 4096 ops on_exceeded stop \
        effects {{ writes w.slots, locks L }} progress tickt\n\
        {{ traverse i over slots of w by unvisited touches writes w.slots\n\
        {{ locks L {{ if w.slots[i].a {{ leave arbeit; }} }} }} }}\nreturn; }}\n}}"
    );
    assert!(fehlercodes(&q).is_empty(), "clean exit refused: {:?}", fehlercodes(&q));
    let c = c_nach_pruefung(&q);
    let sprung = c.find("goto arbeit_ende;").expect("`leave` lowers to a goto:\n{c}");
    let gib = c[..sprung].rfind("L_gib();").expect("the lock is released:\n{c}");
    assert!(
        c[gib..sprung].lines().count() <= 2,
        "the release stands immediately before the jump:\n{c}"
    );
    let marke = c.find("arbeit_ende: ;").expect("the label stands after the loop:\n{c}");
    assert!(sprung < marke, "exit lands at the post-loop point:\n{c}");
}

const KOPF_BAUM: &str = "module t {\ntable T count 8 {\n\
    tree { parent p, child k, sibling g }\n\
    slot { a : bool, p : option index into T, k : option index into T, \
    g : option index into T, } }\n\
    extern fn stop() -> never effects { diverges };\n\
    assume tickt \"The timer interrupts.\" falsifier sonde_tickt;\n";

/// The exit escapes the stackless descendant walk too: the jump stands in
/// the body (after the binder is fixed), the walk scaffold is intact, and
/// the label stands after the whole walk.
#[test]
fn leave_escapes_the_descendant_walk() {
    let q = format!(
        "{KOPF_BAUM}impl fn f(t : ptr<normal, rw> T, s : index into T) \
        effects {{ writes t.slots }}\n\
        {{ forever arbeit per_pass bounded 4096 ops on_exceeded stop \
        effects {{ writes t.slots }} progress tickt\n\
        {{ traverse v over descendants of t.slots[s] by unvisited touches writes t.slots\n\
        {{ if t.slots[v].a {{ leave arbeit; }} }} }}\nreturn; }}\n}}"
    );
    assert!(fehlercodes(&q).is_empty(), "clean exit refused: {:?}", fehlercodes(&q));
    let c = c_nach_pruefung(&q);
    let rumpf = c.find("const uint32_t v = _k").expect("the walk binds the node:\n{c}");
    let sprung = c.find("goto arbeit_ende;").expect("`leave` lowers to a goto:\n{c}");
    let marke = c.find("arbeit_ende: ;").expect("the label stands after the walk:\n{c}");
    assert!(rumpf < sprung && sprung < marke, "exit leaves from the body:\n{c}");
}

/// A `traverse` carries no label, so `leave`/`next` naming its binder is
/// S001 -- the negative pin beside the positive ones above.
#[test]
fn exit_naming_the_traverse_binder_falls() {
    let q = format!(
        "{KOPF}impl fn f(w : ptr<normal, rw> W) effects {{ writes w.slots }}\n\
        {{ forever arbeit per_pass bounded 1024 ops on_exceeded stop \
        effects {{ writes w.slots }} progress tickt\n\
        {{ traverse i over slots of w by unvisited touches writes w.slots \
        {{ leave i; }} }}\nreturn; }}\n}}"
    );
    assert_eq!(fehlercodes(&q), vec!["S001".to_string()]);
    let q = format!(
        "{KOPF}impl fn f(w : ptr<normal, rw> W) effects {{ writes w.slots }} costs <= 4096 ops\n\
        {{ traverse i over slots of w by unvisited touches writes w.slots \
        {{ next i; }} }}\n}}"
    );
    assert_eq!(fehlercodes(&q), vec!["S001".to_string()]);
}

/// With no label in scope at all the exit has nowhere to go: S001.
#[test]
fn exit_without_any_label_falls() {
    let q = format!(
        "{KOPF}impl fn f(w : ptr<normal, rw> W) effects {{ writes w.slots }} costs <= 4096 ops\n\
        {{ traverse i over slots of w by unvisited touches writes w.slots \
        {{ if w.slots[i].a {{ leave arbeit; }} }} }}\n}}"
    );
    assert_eq!(fehlercodes(&q), vec!["S001".to_string()]);
}

/// The windowed walk still has no lowering: the reader refuses it with
/// P001 (lane 222) before any pass could read it as a whole-table walk.
/// This row is the handoff pin for the syntax lane -- it goes green the
/// day the window lowers instead.
#[test]
fn windowed_walk_still_has_no_lowering() {
    let q = format!(
        "{KOPF}impl fn f(w : ptr<normal, rw> W) effects {{ writes w.slots }} costs <= 4096 ops\n\
        {{ traverse i over slots of w from 0 count 8 by unvisited touches writes w.slots \
        {{ w.slots[i].a = false; }} }}\n}}"
    );
    assert!(fehlercodes(&q).iter().any(|c| c == "P001"), "window must stay refused: {:?}", fehlercodes(&q));
}
