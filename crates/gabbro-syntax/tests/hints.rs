//! **Permanent probes for the P002 hint (Lane B2).**
//!
//! `P002` refuses a reserved word where a name stands. Since Lane B2 the refusal
//! carries a hint where one is due: the closest NAME-USABLE vocabulary word (at most
//! 2 edits, same initial, table members only, never a reserved word as an
//! identifier -- see `parse.rs::suggest_name`, the twin of the subcommand hint in
//! `gabbro-cli/src/main.rs::suggest`). Where no such word exists the refusal stands
//! alone.
//!
//! Both directions, or neither is a measurement: a firing case asserts code AND
//! hint, a silent case asserts the code AND the absence of any hint.

use gabbro_syntax::diag::Stufe;

fn probe(word: &str) -> String {
    format!("impl fn f() effects {{ pure }} {{ let {word} = 1; }}")
}

/// **The hint fires where due** -- a reserved word one step from a word that IS a
/// name, answered with the spelling that would be accepted there.
#[test]
fn hint_fires_where_due() {
    for (typed, near) in [
        ("return", "returns"),
        ("true", "tree"),
        ("const", "cost"),
        ("bool", "boot"),
        ("static", "state"),
        ("if", "in"),
        ("lenof", "leaf"),
    ] {
        let quelle = probe(typed);
        let (_, absagen) = gabbro_syntax::lies("<probe>", &quelle);
        let wanted = format!("did you mean `{near}`?");
        assert!(
            absagen.absagen.iter().any(|a| a.stufe == Stufe::Fehler
                && a.code == "P002"
                && a.notizen.iter().any(|n| n.contains(&wanted))),
            "`let {typed} = 1` must fall at P002 with a `{wanted}` hint:\n{}",
            absagen.zeige(&quelle)
        );
    }
}

/// **And it stays silent where not** -- the refusal stands, with no guess attached.
/// Exact reserved words with no name-usable neighbour (`Some`, `None`, `Self`),
/// and reserved words far from every name (`extern`, `sizeof`, `lenof`,
/// `aligned`, `forall`, `exists`, `else`, `false`).
#[test]
fn hint_silent_where_not_due() {
    for typed in [
        "Some", "None", "Self", "extern", "sizeof", "aligned", "forall", "exists", "else",
        "false",
    ] {
        let quelle = probe(typed);
        let (_, absagen) = gabbro_syntax::lies("<probe>", &quelle);
        assert!(
            absagen
                .absagen
                .iter()
                .any(|a| a.stufe == Stufe::Fehler && a.code == "P002"),
            "`let {typed} = 1` must still fall at P002:\n{}",
            absagen.zeige(&quelle)
        );
        assert!(
            !absagen
                .absagen
                .iter()
                .flat_map(|a| a.notizen.iter())
                .any(|n| n.contains("did you mean")),
            "`let {typed} = 1` falls at P002 but must carry no hint:\n{}",
            absagen.zeige(&quelle)
        );
    }
}
