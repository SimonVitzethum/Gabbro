//! **Lane 229 -- what a `traverse` reads besides its body.**
//!
//! The `E010` walk used to miss the object of a `traverse`: `traverse v of g
//! over …` evaluates `g` (the walk starts there), so the object reads like a
//! bound. Since lane 229 it stands against the function effects (`E010`) and
//! against the traverse's own `touches` (`E011`) -- the two poison probes are
//! `beispiele/gift/1077` (`E011`) and `/1078` (`E010`).
//!
//! What this file pins is the other side: the shapes that STAY silent.
//!
//! * the object named in both lists -- the clean walk;
//! * no object at all -- the common parameter walk is untouched by the rule;
//! * the CARRIER walk stays out of `touches`: `touches` covers the body (and
//!   now the object), the walk itself is the function effects' business.
//!   `beispiele/09-ohne-zeiger.gab` and `beispiele/57-faedenhalt.gab` pin the
//!   same split at corpus scale; the third row below pins it in reduced form
//!   so a later lane cannot re-add the carrier hold without this file going
//!   red first.

use gabbro_syntax::diag::Stufe;

fn fehler(source: &str) -> Vec<String> {
    let (tree, mut refusals) = gabbro_syntax::lies("traverse_object", source);
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

const KOPF: &str = "module snippet {\nconst N : u32 = 8;\ntable W count N { slot { a : u32 in 0 .. 10, parent : u32 in 0 .. 8, } }\nstatic mut y : u32 = 3;\n";

/// The clean walk: the object in both lists, the carrier in the function
/// effects -- silence.
#[test]
fn objekt_in_beiden_listen_ist_still() {
    let q = format!(
        "{KOPF}impl fn f() effects {{ reads W, reads y }} costs <= 200 ops {{\n\
         traverse v of y over ancestors of W by unvisited touches reads W, reads y \
         {{ let x : u32 = 1; }}\nreturn;\n}}\n}}"
    );
    assert!(fehler(&q).is_empty(), "clean walk refused: {:?}", fehler(&q));
}

/// No object at all: the common parameter walk is untouched by the rule.
#[test]
fn lauf_ohne_gegenstand_ist_still() {
    let q = format!(
        "{KOPF}impl fn f(w : ptr<normal, rw> W) effects {{ reads w.slots, writes w.slots }} \
         costs <= 200 ops {{\n\
         traverse i over slots of w by unvisited touches reads w.slots, writes w.slots \
         {{ w.slots[i].a = 1; }}\nreturn;\n}}\n}}"
    );
    assert!(fehler(&q).is_empty(), "plain walk refused: {:?}", fehler(&q));
}

/// The carrier walk stays out of `touches`: `touches` names the body, the
/// function effects name the walk -- silence. The reduced form of the
/// `beispiele/57` split.
#[test]
fn traegerlauf_bleibt_ausserhalb_von_touches() {
    let q = format!(
        "{KOPF}impl fn f() effects {{ reads W, reads W.slots, writes W.slots }} costs <= 200 ops {{\n\
         traverse i over slots of W by unvisited touches writes W.slots \
         {{ W.slots[i].a = 1; }}\nreturn;\n}}\n}}"
    );
    assert!(fehler(&q).is_empty(), "carrier hold leaked into touches: {:?}", fehler(&q));
}

/// The new bite, self-contained: the object in the effects but missing from
/// `touches` falls with `E011` and nothing else.
#[test]
fn gegenstand_ohne_touches_faellt_mit_e011() {
    let q = format!(
        "{KOPF}impl fn f() effects {{ reads W, reads y }} costs <= 200 ops {{\n\
         traverse v of y over ancestors of W by unvisited touches reads W \
         {{ let x : u32 = 1; }}\nreturn;\n}}\n}}"
    );
    assert_eq!(fehler(&q), vec!["E011".to_string()]);
}

// ---------------------------------------------------------------------------------------
// Fix lane F7 (review G09 F2): the CALLS in a `traverse` body stand against `touches`.
// The poison probes are `beispiele/gift/1169` (a call writing a global) and `/1170` (a
// derived `effects` clause, where `E011` never ran before).
// ---------------------------------------------------------------------------------------

const KOPF_RUF: &str = "module snippet {\nconst N : u32 = 8;\ntable W count N { slot { a : u32 in 0 .. 10, } }\nstatic mut zaehler : u32 = 0;\n\
    impl fn schreibe_zaehler() effects { writes zaehler } costs <= 4 ops { zaehler = 1; }\n\
    impl fn lies_zaehler() -> u32 effects { reads zaehler } costs <= 4 ops { return zaehler; }\n";

/// Positive probe: the callee's write named in `touches` -- silence.
#[test]
fn f7_ruf_mit_touches_ist_still() {
    let q = format!(
        "{KOPF_RUF}impl fn f() effects {{ reads W, writes zaehler }} costs <= 200 ops {{\n\
         traverse i over slots of W by unvisited touches reads W, writes zaehler \
         {{ schreibe_zaehler(); }}\nreturn;\n}}\n}}"
    );
    assert!(fehler(&q).is_empty(), "a call named in touches refused: {:?}", fehler(&q));
}

/// The bite: the callee writes a global `touches` does not name -- `E011` and nothing else.
#[test]
fn f7_ruf_ohne_touches_faellt_mit_e011() {
    let q = format!(
        "{KOPF_RUF}impl fn f() effects {{ reads W, writes zaehler }} costs <= 200 ops {{\n\
         traverse i over slots of W by unvisited touches reads W \
         {{ schreibe_zaehler(); }}\nreturn;\n}}\n}}"
    );
    assert_eq!(fehler(&q), vec!["E011".to_string()], "{:?}", fehler(&q));
}

/// A READ through a call needs `reads` (or `writes`) in `touches`, like a direct read.
#[test]
fn f7_lesender_ruf_braucht_reads() {
    let ohne = format!(
        "{KOPF_RUF}impl fn f() effects {{ reads W, reads zaehler }} costs <= 200 ops {{\n\
         traverse i over slots of W by unvisited touches reads W \
         {{ let x = lies_zaehler(); }}\nreturn;\n}}\n}}"
    );
    assert_eq!(fehler(&ohne), vec!["E011".to_string()], "{:?}", fehler(&ohne));
    let mit = ohne.replace("touches reads W ", "touches reads W, reads zaehler ");
    assert!(fehler(&mit).is_empty(), "a read named in touches refused: {:?}", fehler(&mit));
}

/// A call inside the traverse OBJECT is held too.
#[test]
fn f7_ruf_im_gegenstand_faellt_mit_e011() {
    let q = "module snippet {\nconst N : u32 = 8;\n\
        table W count N { slot { a : u32 in 0 .. 10, parent : u32 in 0 .. 8, } }\n\
        static mut zaehler : u32 = 0;\n\
        impl fn start() -> u32 in 0 .. 8 effects { writes zaehler } costs <= 4 ops { zaehler = 1; return 3; }\n\
        impl fn f() effects { reads W, writes zaehler } costs <= 200 ops {\n\
        traverse v of start() over ancestors of W by unvisited touches reads W \
        { let x : u32 = 1; }\nreturn;\n}\n}";
    assert!(fehler(q).contains(&"E011".to_string()), "{:?}", fehler(q));
}

/// A derived clause (no `effects` line): `E011` holds the direct deeds there too.
#[test]
fn f7_abgeleitete_wirkungen_halten_touches() {
    let q = format!(
        "{KOPF_RUF}impl fn f() costs <= 200 ops {{\n\
         traverse i over slots of W by unvisited touches reads W \
         {{ zaehler = 1; }}\nreturn;\n}}\n}}"
    );
    assert!(fehler(&q).contains(&"E011".to_string()), "{:?}", fehler(&q));
    let mit = q.replace("touches reads W ", "touches reads W, writes zaehler ");
    assert!(!fehler(&mit).contains(&"E011".to_string()), "{:?}", fehler(&mit));
}
