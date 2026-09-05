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
        .join("dokumente/SYNTAX.md");
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

// -- The `res` column against the READER, word by word -------------------------------------
//
// **A column that only a comment explains is a second register beside the truth** -- trap 80,
// and this file's own head says so about the word LIST. Until 2026-09-05 the class column had
// no such guard, and it drifted: six words (`tree`, `parent`, `child`, `sibling`, `observed`,
// `occupied`) had to be prised loose one at a time, each by a separate measurement, because
// nothing said what `res` was supposed to mean or checked that it still meant it.
//
// It now means one thing the reader can be asked: **can a user call a variable this?** The
// two probes below are the two ways a user does -- a parameter and a local -- and each word
// is required to be clean exactly when its column says `ctx`.

/// The program a user writes when a name of his collides: bind it, assign it, read it back.
fn probe_lokal(w: &str) -> String {
    format!(
        "module p {{ impl fn f(a : u32 in 0 .. 10) -> u32 in 0 .. 10 \
         effects {{ pure }} costs <= 8 ops {{ let mut {w} = a; {w} = a; return {w}; }} }}"
    )
}

/// The same question at a parameter -- `messung/K3-BEFUND.md` §3 found seven of its eight
/// there, not at a `let`.
fn probe_parameter(w: &str) -> String {
    format!(
        "module p {{ impl fn f({w} : u32 in 0 .. 10) -> u32 in 0 .. 10 \
         effects {{ pure }} costs <= 4 ops {{ return {w}; }} }}"
    )
}

fn liest_sauber(quelle: &str) -> bool {
    let (_, absagen) = gabbro_syntax::lies("<probe>", quelle);
    !absagen
        .absagen
        .iter()
        .any(|a| a.stufe == gabbro_syntax::diag::Stufe::Fehler)
}

#[test]
fn jedes_wort_ist_ein_name_ausser_den_gebuchten() {
    let mut falsch_res: Vec<&str> = Vec::new();
    let mut falsch_ctx: Vec<&str> = Vec::new();
    for k in ALLE {
        let w = k.text();
        let geht = liest_sauber(&probe_lokal(w)) && liest_sauber(&probe_parameter(w));
        if k.reserviert() && geht {
            falsch_res.push(w);
        }
        if !k.reserviert() && !geht {
            falsch_ctx.push(w);
        }
    }
    assert!(
        falsch_ctx.is_empty(),
        "the column says these are names and the reader refuses them ({}): {:?}\n\
         -- either the reader lost a position or the column is stale",
        falsch_ctx.len(),
        falsch_ctx
    );
    assert!(
        falsch_res.is_empty(),
        "the column says these are NOT names and the reader takes them ({}): {:?}\n\
         -- a word that reads as a name belongs in the `ctx` column",
        falsch_res.len(),
        falsch_res
    );
}

/// **The count itself, so a silent re-reservation cannot pass as a repair.**
///
/// 17 of 221 on 2026-09-05, down from 212. The list stands in `kw.rs`'s head with the reason
/// for each half; whoever moves this number writes the ledger line beside it, the same rule
/// `instrumente/zaehle-wortschatz.py` puts over the word count.
#[test]
fn nur_siebzehn_woerter_sind_keine_namen() {
    let res: Vec<&str> = ALLE
        .iter()
        .filter(|k| k.reserviert())
        .map(|k| k.text())
        .collect();
    assert_eq!(
        res,
        vec![
            "const", "static", "extern", "if", "else", "return", "bool", "sizeof", "lenof",
            "aligned", "forall", "exists", "true", "false", "Self", "Some", "None",
        ],
        "the reserved residue moved -- {} of {}",
        res.len(),
        ALLE.len()
    );
}
