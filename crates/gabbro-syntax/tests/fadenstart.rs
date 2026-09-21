//! **The hosted thread-start statement** -- lane 253 (P017).
//!
//! `start { f, g };` names roots, joined before the starter proceeds. Every
//! probe stands pairwise: a clean form passes, a poisoned one falls with a
//! NAMED, pre-existing code -- this lane spends no new diagnostic code.
//!
//! These are PARSE probes only. The fixture below names the same roots in
//! `concurrent` and in `start`, which the checker refuses since fix lane F4
//! (`N460`: a thread has one owner, and boot starts every member); the
//! checker rules live in `gabbro-check/tests/fadenstart.rs`.

use gabbro_syntax::diag::Stufe;

fn faellt_nicht(quelle: &str) {
    let (_, absagen) = gabbro_syntax::lies("<probe>", quelle);
    let fehler: Vec<_> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .collect();
    assert!(
        fehler.is_empty(),
        "sauber, faellt aber:\n{}\n{}",
        quelle,
        absagen.zeige(quelle)
    );
}

fn faellt_mit(quelle: &str, code: &str) {
    let (_, absagen) = gabbro_syntax::lies("<probe>", quelle);
    let codes: Vec<&str> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code)
        .collect();
    assert!(
        codes.contains(&code),
        "erwartet war {code}, gefallen ist {codes:?}\n{quelle}\n{}",
        absagen.zeige(quelle)
    );
}

fn huelle(rumpf: &str) -> String {
    format!(
        r#"
module probe::fadenstart {{
    impl fn hauptA() effects {{ pure }} {{
    }}
    impl fn hauptB() effects {{ pure }} {{
    }}
    impl fn starter() effects {{ pure }} {{
        {rumpf}
    }}
    concurrent {{ hauptA, hauptB }};
}}
"#
    )
}

#[test]
fn start_zwei_wurzeln_parst() {
    faellt_nicht(&huelle("start { hauptA, hauptB };"));
}

#[test]
fn start_eine_wurzel_parst() {
    faellt_nicht(&huelle("start { hauptA };"));
}

#[test]
fn start_schlusskomma_parst() {
    faellt_nicht(&huelle("start { hauptA, hauptB, };"));
}

#[test]
fn start_leere_liste_faellt() {
    faellt_mit(&huelle("start {};"), "P003");
}

#[test]
fn start_ohne_klammer_faellt_mit_p017() {
    // The unbraced `start f;` is NOT the form -- it keeps its P017.
    faellt_mit(&huelle("start hauptA;"), "P017");
}

#[test]
fn start_allein_faellt_mit_p017() {
    faellt_mit(&huelle("start;"), "P017");
}

#[test]
fn start_ohne_semikolon_faellt() {
    faellt_mit(&huelle("start { hauptA }"), "P001");
}

#[test]
fn spawn_bleibt_p017() {
    // `spawn` is not the word -- the hosted form is `start`.
    faellt_mit(&huelle("spawn hauptA;"), "P017");
}

#[test]
fn start_bleibt_ein_name() {
    // No keyword is spent: assignment and call to a name spelled `start`
    // parse exactly as before.
    faellt_nicht(&huelle("start = 1;"));
    faellt_nicht(&huelle("start(hauptA);"));
}
