//! **Der Waechter ueber dem Wortschatz -- in beide Richtungen.**
//!
//! `pruefe-wortschatz.py` haelt die Tabelle in `SYNTAX.md` gegen die Terminale der EBNF.
//! Dieser Test haelt **den Lexer** gegen dieselbe Tabelle. Ohne ihn gaebe es eine zweite
//! Wortliste, die ein Mensch parallel zur Wahrheit fuehrt -- Falle 80, woertlich.
//!
//! Er faellt in beide Richtungen: ein Wort in `SYNTAX.md`, das der Lexer nicht kennt, ist so
//! gut ein Fehler wie eins im Lexer, das in `SYNTAX.md` fehlt.

use gabbro_syntax::kw::{Kw, ALLE};
use std::collections::BTreeSet;

fn syntax_md() -> String {
    let wurzel = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("SYNTAX.md");
    std::fs::read_to_string(&wurzel)
        .unwrap_or_else(|e| panic!("SYNTAX.md nicht lesbar unter {}: {e}", wurzel.display()))
}

/// Die Wortschatztabelle: der einzige ```-Block, der mit `  Struktur` anfaengt.
fn tabelle(md: &str) -> BTreeSet<String> {
    let anfang = md
        .find("\n  Struktur")
        .expect("die Wortschatztabelle faengt mit `  Struktur` an");
    let rest = &md[anfang..];
    let ende = rest.find("\n```").expect("die Tabelle wird geschlossen");
    let roh = &rest[..ende];

    let mut out = BTreeSet::new();
    for zeile in roh.lines() {
        // **Sonderformen (G6) sind Terminale, aber keine Wortschatzwoerter.** `O` steht als
        // Bezeichner in fester Stellung (`parse.rs:costexpr`), `@version` ist ein
        // zusammengesetztes Zeichen. Der Lexer fuehrt beide nicht als Schluesselwort, und
        // das ist die Zusage -- nicht das Loch. Das Loch war, dass `pruefe-wortschatz.py`
        // sie bis 2026-08-15 gar nicht erst gesehen hat.
        if zeile.trim_start().starts_with("Sonderform") {
            continue;
        }
        // Die Spaltenkoepfe stehen gross am Zeilenanfang und sind keine Woerter.
        let ohne_kopf = match zeile.find(|c: char| c.is_lowercase()) {
            Some(_) => {
                let getrimmt = zeile.trim_start();
                match getrimmt.split_once(char::is_whitespace) {
                    Some((erstes, rest))
                        if erstes.chars().next().is_some_and(|c| c.is_uppercase())
                            && erstes != "Self" =>
                    {
                        rest
                    }
                    _ => getrimmt,
                }
            }
            None => zeile,
        };
        for wort in ohne_kopf.split_whitespace() {
            if wort.chars().all(|c| c.is_alphanumeric() || c == '_') && !wort.is_empty() {
                out.insert(wort.to_string());
            }
        }
    }
    out
}

#[test]
fn lexer_und_syntax_md_fuehren_denselben_wortschatz() {
    let md = syntax_md();
    let aus_md = tabelle(&md);
    let aus_lexer: BTreeSet<String> = ALLE.iter().map(|k| k.text().to_string()).collect();

    let fehlt_im_lexer: Vec<&String> = aus_md.difference(&aus_lexer).collect();
    let fehlt_in_md: Vec<&String> = aus_lexer.difference(&aus_md).collect();

    assert!(
        fehlt_im_lexer.is_empty(),
        "in SYNTAX.md, nicht im Lexer ({}): {:?}",
        fehlt_im_lexer.len(),
        fehlt_im_lexer
    );
    assert!(
        fehlt_in_md.is_empty(),
        "im Lexer, nicht in SYNTAX.md ({}): {:?} -- ein neues Wort ist eine Sprachaenderung \
         und braucht einen Eintrag in der Tabelle",
        fehlt_in_md.len(),
        fehlt_in_md
    );
    assert_eq!(
        aus_md.len(),
        ALLE.len(),
        "die Tabelle und der Lexer zaehlen verschieden"
    );
}

/// Sprechprobe: der Waechter oben muss ueberhaupt fallen koennen.
#[test]
fn sprechprobe_der_waechter_faellt() {
    let aus_lexer: BTreeSet<&str> = ALLE.iter().map(|k| k.text()).collect();
    assert!(
        !aus_lexer.contains("wechsle"),
        "Sprechprobe: ein abgeschafftes Wort darf nicht im Lexer stehen"
    );
    // Ein erfundenes Wort ist kein Wort des Wortschatzes -- sonst prueft `Kw::suche` nichts.
    assert!(Kw::suche("wechsle").is_none());
    assert!(Kw::suche("requires").is_some());
}

/// Jedes Terminal der EBNF muss der Lexer kennen -- dieselbe Pruefung wie in
/// `pruefe-wortschatz.py`, nur gegen den Uebersetzer statt gegen die Tabelle.
#[test]
fn jedes_ebnf_terminal_ist_ein_wort() {
    let md = syntax_md();
    let mut fehlend: BTreeSet<String> = BTreeSet::new();
    for block in md.split("```ebnf").skip(1) {
        let ebnf = block.split("```").next().unwrap_or("");
        let mut zeichen = ebnf.chars().peekable();
        let mut in_text = false;
        let mut aktuell = String::new();
        while let Some(c) = zeichen.next() {
            let _ = &zeichen;
            if c == '"' {
                if in_text {
                    // Ein-Zeichen-Terminale kommen aus Zeichenbereichen ("a" … "z").
                    if aktuell.len() > 1
                        && aktuell
                            .chars()
                            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
                        && aktuell.chars().next().is_some_and(|c| c.is_ascii_alphabetic())
                        && Kw::suche(&aktuell).is_none()
                    {
                        fehlend.insert(aktuell.clone());
                    }
                    aktuell.clear();
                }
                in_text = !in_text;
                continue;
            }
            if in_text {
                aktuell.push(c);
            }
        }
    }
    assert!(
        fehlend.is_empty(),
        "Terminale der EBNF, die der Lexer nicht kennt: {fehlend:?}"
    );
}
