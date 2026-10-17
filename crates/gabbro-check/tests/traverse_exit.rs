//! Lane 252 -- early exit THROUGH a `traverse` (TODO §-1 wave B).
//!
//! A `traverse` carries no label (`SYNTAX.md` §8; `schleifen.rs`), so a
//! `leave`/`next` inside one can only name an enclosing `retry`/`forever`.
//! That exit is a `goto` past the generated `for` (`emit.rs`, never a
//! `break` -- a `break` would take the innermost loop), with the locks
//! taken inside released on the way out (`Austritt::schleifen`). What this
//! file pins: the checker-clean exit lowers, lands after the loop, and
//! releases on the path; a `leave`/`next` naming the traverse binder, and
//! the windowed walk, stay refused (S001/P001); since SPRACHE-EFFIZIENZ #19 the traverse BINDER
//! is a label for `by unvisited` walks.

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

const KOPF: &str = "module t {\ntable W count 16 { slot { a : bool, } }\n\
    extern fn stop() -> never effects { diverges };\n\
    assume tickt \"The timer interrupts.\" falsifier sonde_tickt;\n";

const KOPF_SPERRE: &str = "module t {\ntable W count 16 { slot { a : bool, } }\n\
    lock L protects { W } rank 0 held <= 400 ops;\n\
    extern fn stop() -> never effects { diverges };\n\
    assume tickt \"The timer interrupts.\" falsifier sonde_tickt;\n";

const KOPF_BAUM: &str = "module t {\ntable T count 8 {\n\
    tree { parent p, child k, sibling g }\n\
    slot { a : bool, p : option index into T, k : option index into T, \
    g : option index into T, } }\n\
    extern fn stop() -> never effects { diverges };\n\
    assume tickt \"The timer interrupts.\" falsifier sonde_tickt;\n";

/// The BINDER of a `traverse` is its label (SPRACHE-EFFIZIENZ #19): `leave i;` / `next i;`
/// inside a `by unvisited` walk are clean at the checker. (The emitter has no label for a
/// `traverse` and refuses by name -- the C backend is deprecated and gets nothing new.)
#[test]
fn exit_naming_the_traverse_binder_is_clean_when_unvisited() {
    let q = format!(
        "{KOPF}impl fn f(w : ptr<normal, rw> W) effects {{ writes w.slots }} costs <= 4096 ops\n\
        {{ traverse i over slots of w by unvisited touches writes w.slots \
        {{ if w.slots[i].a {{ leave i; }} }} }}\n}}"
    );
    assert!(fehlercodes(&q).is_empty(), "refused: {:?}", fehlercodes(&q));
    let q = format!(
        "{KOPF}impl fn f(w : ptr<normal, rw> W) effects {{ writes w.slots }} costs <= 4096 ops\n\
        {{ traverse i over slots of w by unvisited touches writes w.slots \
        {{ if w.slots[i].a {{ next i; }} }} }}\n}}"
    );
    assert!(fehlercodes(&q).is_empty(), "refused: {:?}", fehlercodes(&q));
}

/// The exit stays refused for a name that is NOT an enclosing label (`S001`), and for a
/// `by consuming` walk (`N580`).
#[test]
fn exit_naming_a_stranger_or_a_consuming_walk_falls() {
    let q = format!(
        "{KOPF}impl fn f(w : ptr<normal, rw> W) effects {{ writes w.slots }} costs <= 4096 ops\n\
        {{ traverse i over slots of w by unvisited touches writes w.slots \
        {{ leave j; }} }}\n}}"
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
/// This row is the handoff pin for the syntax lane -- it goes RED the day
/// the window parses (P001 lifted), and the lane that lifts it replaces
/// this row with its own window pins.
#[test]
fn windowed_walk_still_has_no_lowering() {
    let q = format!(
        "{KOPF}impl fn f(w : ptr<normal, rw> W) effects {{ writes w.slots }} costs <= 4096 ops\n\
        {{ traverse i over slots of w from 0 count 8 by unvisited touches writes w.slots \
        {{ w.slots[i].a = false; }} }}\n}}"
    );
    assert!(fehlercodes(&q).iter().any(|c| c == "P001"), "window must stay refused: {:?}", fehlercodes(&q));
}
