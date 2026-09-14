//! **The higher-order contract on function-pointer types (lane 177).**
//!
//! A `fn(…) -> T` type carries `requires`/`ensures` beside `effects`/`costs`. Three
//! readings, each with its probe:
//!
//! * an indirect call is checked against the TYPE's contract -- `N295` (the weak `M115`
//!   reading of the slot's `requires`) and `N296` (the `M143` reading of the arity);
//! * assigning or passing `&f` records the refinement implication as a `C` obligation
//!   (`N297` hints at the flow) and decides nothing about it;
//! * effects `⊆`, costs `<=`, arity and signature stay DECIDED (`M128`/`M142`).
//!
//! ## Why the direction is pinned twice
//!
//! The refinement is contravariant in `requires` (`requires_slot ⇒ requires_f`) and
//! covariant in `ensures` (`ensures_f ⇒ ensures_slot`), and the wrong direction is
//! unsound and easy to build by accident. `gift/957` (a stronger `requires` at `&f`
//! than at the slot) and `gift/958` (a stronger `ensures` at the slot than at `&f`)
//! record their `C` obligation and hint -- under swapped logic both would see a trivial
//! truth, record nothing, and these tests go red. *A guard that only asserts a refusal
//! is green for a rule pointing the wrong way.*

use gabbro_syntax::diag::Stufe;
use std::path::{Path, PathBuf};

fn wurzel() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("beispiele")
}

fn lies(datei: &str) -> (String, gabbro_syntax::ast::Programm, gabbro_syntax::diag::Absagen) {
    let pfad = wurzel().join(datei);
    let quelle = std::fs::read_to_string(&pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()));
    let name = pfad.display().to_string();
    let (baum, mut absagen) = gabbro_syntax::lies(&name, &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    (quelle, baum, absagen)
}

fn fehler(absagen: &gabbro_syntax::diag::Absagen) -> Vec<&'static str> {
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code)
        .collect()
}

fn hinweise(absagen: &gabbro_syntax::diag::Absagen) -> Vec<&'static str> {
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Hinweis)
        .map(|a| a.code)
        .collect()
}

fn pflichten(
    quelle: &str,
    baum: &gabbro_syntax::ast::Programm,
    name: &str,
) -> String {
    let (bericht, vollstaendig) = gabbro_check::pflichten::zeige(baum, name, quelle);
    assert!(vollstaendig, "E1 gefallen:\n{bericht}");
    bericht
}

/// **The slot's `requires` is checked at the indirect call, both spellings.**
///
/// `247` excludes by literal (`0` against `b > 0`), `956` by range (`100 .. 200`
/// against `k < 64`). Each must fall exactly once with `N295`: the file-level gift run
/// only asserts the code FIRES, so purity (no second code beside it) is held HERE.
#[test]
fn indirekter_ruf_haelt_requires_des_typs() {
    for datei in [
        "gift/247-fnzeiger-mit-requires.gab",
        "gift/956-indirect-call-violates-requires.gab",
    ] {
        let (_, _, absagen) = lies(datei);
        assert_eq!(
            fehler(&absagen),
            ["N295"],
            "{datei} must fall exactly once with N295"
        );
    }
}

/// **The arity of an indirect call is the slot's, both spellings.**
///
/// `248` keeps its `ensures` flavour (the narrowing stays silent on `bool`), `959` is
/// the minimal shape. Exactly one `N296` each.
#[test]
fn indirekter_ruf_haelt_stelligkeit_des_typs() {
    for datei in [
        "gift/248-fnzeiger-mit-ensures.gab",
        "gift/959-indirect-call-wrong-arity.gab",
    ] {
        let (_, _, absagen) = lies(datei);
        assert_eq!(
            fehler(&absagen),
            ["N296"],
            "{datei} must fall exactly once with N296"
        );
    }
}

/// **A stronger `requires` at `&f` than at the slot records the `requires` half.**
///
/// `957` owes `requires_slot ⇒ requires_f`, i.e. `true ⇒ b > 0` -- contravariant, and
/// not provable in general. The checker records it (kind `C`), hints `N297`, and
/// refuses nothing. Under the swapped direction (`requires_f ⇒ requires_slot`) the
/// implication is trivially true and NEITHER the hint NOR the obligation appears --
/// that is the probe.
#[test]
fn staerkeres_requires_am_erzeuger_wird_gezaehlt() {
    let (quelle, baum, absagen) = lies("gift/957-producer-requires-stronger-than-slot.gab");
    assert!(fehler(&absagen).is_empty(), "nothing decided here");
    assert_eq!(hinweise(&absagen), ["N297"], "one hint at the flow");
    let bericht = pflichten(&quelle, &baum, "957-producer-requires-stronger-than-slot.gab");
    assert!(
        bericht.contains("requires of fn(b : u8) => requires of &hart_senden"),
        "the requires-half implication is not there as written:\n{bericht}"
    );
    assert!(
        bericht.contains("\tC\t"),
        "no contract-refinement line at all:\n{bericht}"
    );
}

/// **A stronger `ensures` at the slot than at `&f` records the `ensures` half.**
///
/// The mirror of the test above: `958` owes `ensures_f ⇒ ensures_slot`, i.e.
/// `true ⇒ result == true` -- covariant. Same hint, same kind, other half; swapped
/// logic (`ensures_slot ⇒ ensures_f`) sees `… ⇒ true` and stays silent.
#[test]
fn staerkeres_ensures_am_typ_wird_gezaehlt() {
    let (quelle, baum, absagen) = lies("gift/958-slot-ensures-stronger-than-producer.gab");
    assert!(fehler(&absagen).is_empty(), "nothing decided here");
    assert_eq!(hinweise(&absagen), ["N297"], "one hint at the flow");
    let bericht = pflichten(&quelle, &baum, "958-slot-ensures-stronger-than-producer.gab");
    assert!(
        bericht.contains("ensures of &hart_bereit => ensures of fn() -> bool"),
        "the ensures-half implication is not there as written:\n{bericht}"
    );
}

/// **The comparator example: clean check, counted refinement, compilable C.**
///
/// `126` sorts through the slot's contract. Producer and slot agree word for word, so
/// the counted `ensures` implication is dischargeable on sight -- the twin of `957`
/// and `958`, where it is not. The `N297` hint stands beside a green check; sortedness
/// itself is the user's (`N` obligations on `sortiere`, unproved here).
#[test]
fn vergleichssortierung_traegt_den_vertrag_durch_den_zeiger() {
    let (quelle, baum, absagen) = lies("126-vergleichssortierung.gab");
    assert!(fehler(&absagen).is_empty(), "{}", absagen.zeige(&quelle));
    assert_eq!(hinweise(&absagen), ["N297"], "one hint at `nimm`");
    let bericht = pflichten(&quelle, &baum, "126-vergleichssortierung.gab");
    assert!(
        bericht.contains("ensures of &kleiner => ensures of fn(a : u32, b : u32) -> bool"),
        "the ensures-half implication is not there as written:\n{bericht}"
    );
    let c = gabbro_check::emit::emittiere(&baum, &mut gabbro_syntax::diag::Absagen::neu("126"));
    assert!(
        c.contains("bool (*cmp)(uint32_t, uint32_t)"),
        "the comparator lowers to a C function pointer:\n{c}"
    );
}

/// **The driver callback: world effects on the slot, decided and counted.**
///
/// `127` carries `effects` and `costs` on the pointer type beside `requires`. The
/// decidable sides hold silently (`M128`: `writes Puffer.slots ⊆ writes Puffer.slots`,
/// `8 <= 8`); the logic half -- `k < 64 ⇒ Held(PUFFER) ∧ k < 64` -- stands as kind
/// `C`, naming the one gap the lane leaves open: no pass holds a `Held` requirement
/// at an indirect call, so the holder discharges it by calling under the lock.
#[test]
fn treiberrueckruf_traegt_wirkungen_und_zaehlt_die_logik() {
    let (quelle, baum, absagen) = lies("127-treiberrueckruf.gab");
    assert!(fehler(&absagen).is_empty(), "{}", absagen.zeige(&quelle));
    assert_eq!(hinweise(&absagen), ["N297"], "one hint at `registriere`");
    let bericht = pflichten(&quelle, &baum, "127-treiberrueckruf.gab");
    assert!(
        bericht.contains("requires of fn(k : u32) => requires of &schreibe"),
        "the requires-half implication is not there as written:\n{bericht}"
    );
}
