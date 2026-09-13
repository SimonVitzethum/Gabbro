//! **The census counts the origins of the nine second-batch constructors.**
//!
//! `grammatik/Grammatik/ZeugnisStmt2.lean` (lane 146, T1 part 2) certifies nine
//! more statement/block constructors: `assignDurch`, `callInd`, `onTag`,
//! `onGrund`, `bindCallInd`, `gleit`, `gleitLit`, `gleitVon`, `gleitNarrow`.
//! The [`zeugnis`](gabbro_check::zeugnis) census is a surface-form count, not a
//! derivation printer (lane 136 report), so "printing them" means booking
//! their surface origins instead of `UNZUGEORDNET`. One test per form pins
//! that: each parses its input (loud on failure) and asserts the census
//! carries the expected mark with nothing unassigned.

use std::path::{Path, PathBuf};

fn wurzel() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..")
}

fn lies(relativ: &str) -> String {
    let p = wurzel().join(relativ);
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))
}

/// Parse (loud on failure) and run the census.
fn erhebung(quelle: &str) -> gabbro_check::zeugnis::Erhebung {
    let (baum, absagen) = gabbro_syntax::lies("probe.gab", quelle);
    assert_eq!(
        absagen.fehler_zahl(),
        0,
        "the probe does not parse: {}",
        absagen.zeige(quelle)
    );
    gabbro_check::zeugnis::erhebe(&baum)
}

fn marke(e: &gabbro_check::zeugnis::Erhebung, was: &str) -> usize {
    e.posten.get(was).copied().unwrap_or(0)
}

/// **`assignDurch` -- the write through a read-write pointer.**
///
/// `beispiele/104-referenz.gab`: `k.slots[i].stand = 100` with
/// `k : ptr<normal, rw> Konto`. The census books every assignment under
/// `assignment`, pointer or not.
#[test]
fn zeiger_schreiben_ist_eingeordnet() {
    let e = erhebung(&lies("beispiele/104-referenz.gab"));
    assert!(e.unzugeordnet.is_empty(), "{:?}", e.unzugeordnet);
    assert!(marke(&e, "assignment") >= 1, "{:?}", e.posten);
}

/// **`callInd` -- the indirect call.**
///
/// `messung/fnptr-proben/p5.gab`: `t->senden(b)` through
/// `CallTarget::Place`. The census books every call under `call`,
/// whether the callee stands there as a name or at a place.
#[test]
fn mittelbarer_ruf_ist_eingeordnet() {
    let e = erhebung(&lies("messung/fnptr-proben/p5.gab"));
    assert!(e.unzugeordnet.is_empty(), "{:?}", e.unzugeordnet);
    assert!(marke(&e, "call") >= 1, "{:?}", e.posten);
}

/// **`onTag` -- the tagged match.**
///
/// `beispiele/34-markierter-wert.gab`: `match` over the tagged type
/// `Nachricht`. Non-option matches are booked as `match (tagged)`.
#[test]
fn markierter_match_ist_eingeordnet() {
    let e = erhebung(&lies("beispiele/34-markierter-wert.gab"));
    assert!(e.unzugeordnet.is_empty(), "{:?}", e.unzugeordnet);
    assert!(marke(&e, "match (tagged)") >= 1, "{:?}", e.posten);
}

/// **`onGrund` -- the match on a reason value.**
///
/// A `match` over `HolFehler::Leer` has one arm per ground and is neither
/// `Some`/`None`: the census books it as `match (tagged)`, the same arm
/// the tagged elaboration (`Stmt.onGrund`) comes from.
#[test]
fn grund_match_ist_eingeordnet() {
    let quelle = r#"module probe::grund {
reason HolFehler {
    Leer   = 1 "die Quelle war leer"
    Kaputt = 2 "die Quelle war unlesbar"
    exhaustive
}
impl fn code() -> u32 effects { pure } costs <= 4 ops {
    match HolFehler::Leer {
        Leer   => { return 0; }
        Kaputt => { return 1; }
    }
    return 2;
}
}
"#;
    let e = erhebung(quelle);
    assert!(e.unzugeordnet.is_empty(), "{:?}", e.unzugeordnet);
    assert!(marke(&e, "match (tagged)") >= 1, "{:?}", e.posten);
}

/// **`bindCallInd` -- the bound indirect call.**
///
/// `let x : u32 = t->lies();` binds the answer of a call through
/// `CallTarget::Place`. The census books every binding under `let`.
#[test]
fn gebundener_mittelbarer_ruf_ist_eingeordnet() {
    let quelle = r#"module probe::gebunden {
type Treiber = { lies : fn() -> u32, };
impl fn nutze(t : ptr<normal, r> Treiber)
    effects { reads t }
    costs <= 4 ops
{
    let x : u32 = t->lies();
    return;
}
}
"#;
    let e = erhebung(quelle);
    assert!(e.unzugeordnet.is_empty(), "{:?}", e.unzugeordnet);
    assert!(marke(&e, "let") >= 1, "{:?}", e.posten);
}

/// **`gleit` -- float arithmetic.**
///
/// `messung/proben/probe-f32-literal.gab`: `x * 0.1 rounded` over `f32`.
/// The census carries no float-own mark; the form must still book under
/// its surface statement (`return`) and set the float flag.
#[test]
fn gleit_arithmetik_ist_eingeordnet() {
    let e = erhebung(&lies("messung/proben/probe-f32-literal.gab"));
    assert!(e.unzugeordnet.is_empty(), "{:?}", e.unzugeordnet);
    assert!(marke(&e, "return") >= 1, "{:?}", e.posten);
    assert!(e.gleitkomma, "the float file must set the float flag");
}

/// **`gleitLit` -- the float literal step.**
///
/// A float literal bound by `let` (`Block.gleitLit` origin). Booked as
/// `let`, with the float flag set.
#[test]
fn gleit_literal_ist_eingeordnet() {
    let quelle = r#"module probe::gleitlit {
type Bruch = f32 in 0.0 .. 10.0;
impl fn halb() -> Bruch effects { pure } costs <= 2 ops {
    let h : Bruch = 0.5;
    return h;
}
}
"#;
    let e = erhebung(quelle);
    assert!(e.unzugeordnet.is_empty(), "{:?}", e.unzugeordnet);
    assert!(marke(&e, "let") >= 1, "{:?}", e.posten);
    assert!(e.gleitkomma, "the float file must set the float flag");
}

/// **`gleitVon` -- int held against float.**
///
/// An int literal bound at float type (`Block.gleitVon` origin: the int
/// fragment elaboration behind float bounds). Booked as `let`.
#[test]
fn gleit_von_int_ist_eingeordnet() {
    let quelle = r#"module probe::gleitvon {
type Bruch = f32 in 0.0 .. 10.0;
impl fn sieben() -> Bruch effects { pure } costs <= 2 ops {
    let s : Bruch = 7;
    return s;
}
}
"#;
    let e = erhebung(quelle);
    assert!(e.unzugeordnet.is_empty(), "{:?}", e.unzugeordnet);
    assert!(marke(&e, "let") >= 1, "{:?}", e.posten);
    assert!(e.gleitkomma, "the float file must set the float flag");
}

/// **`gleitNarrow` -- the float narrowing.**
///
/// `beispiele/26-gleitkomma.gab`: `narrow x to 0.0 .. 1.0 else { … }`
/// over `f64`. The census books every narrowing under `narrow`, int or
/// float (`Block.narrow` vs `Block.gleitNarrow`).
#[test]
fn gleit_verengung_ist_eingeordnet() {
    let e = erhebung(&lies("beispiele/26-gleitkomma.gab"));
    assert!(e.unzugeordnet.is_empty(), "{:?}", e.unzugeordnet);
    assert!(marke(&e, "narrow") >= 1, "{:?}", e.posten);
    assert!(e.gleitkomma, "the float file must set the float flag");
}
