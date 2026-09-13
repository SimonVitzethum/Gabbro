//! **Lock invariants on the lock declaration (lane 156).**
//!
//! Each refusal fires ALONE over its probe, and the two positives stay
//! silent: the footprint (`N275`), the purity (`N276`, twice), the names
//! (`N277`), and the recorded release duty (`L` beside the `ensures`).

use gabbro_syntax::diag::Stufe;

fn fehler(quelle: &str) -> Vec<&'static str> {
    let (baum, mut absagen) = gabbro_syntax::lies("<probe>", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code)
        .collect()
}

fn datei(name: &str) -> String {
    let pfad = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join(name);
    std::fs::read_to_string(&pfad).expect("example readable")
}

/// **The positives stay silent.** `118` is two functions over two carriers
/// under one lock with a conserved-sum invariant; `119` is the same duty
/// through `locks` blocks.
#[test]
fn positive_bleiben_sauber() {
    for name in [
        "beispiele/118-sperrinvariante-erhaltung.gab",
        "beispiele/119-sperrinvariante-bloecke.gab",
    ] {
        let q = datei(name);
        assert!(fehler(&q).is_empty(), "{name} falls with {:?}", fehler(&q));
    }
}

/// **The four poison probes, each with its code ALONE.**
#[test]
fn gifte_fallen_allein() {
    for (name, code) in [
        (
            "beispiele/gift/940-invariant-liest-ungeschuetzten-traeger.gab",
            "N275",
        ),
        ("beispiele/gift/941-invariant-mit-old.gab", "N276"),
        ("beispiele/gift/942-invariant-mit-ruf.gab", "N276"),
        ("beispiele/gift/943-invariant-nennt-nichts.gab", "N277"),
    ] {
        let q = datei(name);
        assert_eq!(fehler(&q), vec![code], "{name} draws more than {code}");
    }
}

/// **The release duty is recorded, not refused.** One `L` line per lock
/// invariant, named by its lock -- the same shape as one line per `ensures`.
#[test]
fn ausloesung_wird_gezaehlt() {
    let (baum, _) = gabbro_syntax::lies("118", &datei("beispiele/118-sperrinvariante-erhaltung.gab"));
    let p = gabbro_check::pflichten::sammle(&baum);
    let sperr: Vec<_> = p
        .iter()
        .filter(|x| x.art == gabbro_check::pflichten::Art::Sperrinvariante)
        .collect();
    assert_eq!(sperr.len(), 1, "one lock invariant, one duty");
    assert_eq!(sperr[0].funktion, "K");
    assert_eq!(sperr[0].gegenstand, "invariant");
    // And the register prints it: the header line adds up over nine kinds.
    let (_, vollstaendig) = gabbro_check::pflichten::zeige(
        &baum,
        "118",
        &datei("beispiele/118-sperrinvariante-erhaltung.gab"),
    );
    assert!(vollstaendig, "the register loses no kind (E1 inside the tool)");
}
