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
