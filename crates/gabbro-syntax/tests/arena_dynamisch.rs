//! **Parse snippets for the dynamic arena (lane 257, wave D).**
//!
//! The `max` ceiling clause and the `grow` statement arrive here first:
//! these probes pin the shapes at the reader, before any checker verdict.
//! Each snippet parses through `gabbro_syntax::lies` alone -- no checker
//! pass runs, so every failure below is the grammar's, not a rule's.

use gabbro_syntax::ast::{FnRumpf, ItemArt, StmtArt};
use gabbro_syntax::diag::Stufe;

fn fehler(quelle: &str) -> Vec<&'static str> {
    let (_, absagen) = gabbro_syntax::lies("<probe>", quelle);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code)
        .collect()
}

fn rahmen(rumpf: &str) -> String {
    format!(
        "module p {{\narena Speicher capacity 2 .. 8 max 64 of u16;\n\
         impl fn f() -> u32 effects {{ writes Speicher }} costs <= 64 ops {{\n{rumpf}}}\n}}"
    )
}

#[test]
fn max_decke_steht_am_baum() {
    let quelle = "module p {\narena Speicher capacity 2 .. 8 max 64 of u16;\n}";
    assert!(fehler(quelle).is_empty(), "max clause parses clean");
    let (baum, _) = gabbro_syntax::lies("<probe>", quelle);
    let mut gefunden = false;
    for i in &baum.items {
        if let ItemArt::Modul(m) = &i.art {
            for j in &m.items {
                if let ItemArt::Arena(a) = &j.art {
                    assert!(a.max.is_some(), "the ceiling travels in the tree");
                    gefunden = true;
                }
            }
        }
    }
    assert!(gefunden, "the arena declaration is in the tree");
}

#[test]
fn ohne_max_bleibt_statisch() {
    // The static prefix reads byte for byte as before: no clause, no
    // ceiling in the tree, and the checker keeps `M = hi`.
    let quelle = "module p {\narena Speicher capacity 2 .. 8 of u16;\n}";
    assert!(fehler(quelle).is_empty(), "static form parses clean");
    let (baum, _) = gabbro_syntax::lies("<probe>", quelle);
    for i in &baum.items {
        if let ItemArt::Modul(m) = &i.art {
            for j in &m.items {
                if let ItemArt::Arena(a) = &j.art {
                    assert!(a.max.is_none(), "no clause, no ceiling");
                }
            }
        }
    }
}

#[test]
fn grow_steht_am_baum() {
    let quelle = rahmen("    grow Speicher by 8 else {\n        return 1;\n    };\n    return 0;\n");
    assert!(fehler(&quelle).is_empty(), "grow parses clean");
    let (baum, _) = gabbro_syntax::lies("<probe>", &quelle);
    let mut gefunden = false;
    for i in &baum.items {
        if let ItemArt::Modul(m) = &i.art {
            for j in &m.items {
                if let ItemArt::Funktion(f) = &j.art {
                    if let FnRumpf::Block(b) = &f.rumpf {
                        for s in &b.anweisungen {
                            if let StmtArt::Grow(g) = &s.art {
                                assert_eq!(g.tisch.text, "Speicher");
                                gefunden = true;
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(gefunden, "the grow statement is in the tree");
}

#[test]
fn grow_ohne_else_ist_kein_satz() {
    // The `else` is always owed: the grammar has no branchless form, so a
    // missing `else` is a parse refusal, not a checker question.
    let quelle = rahmen("    grow Speicher by 8;\n    return 0;\n");
    let f = fehler(&quelle);
    assert!(
        f.contains(&"P001"),
        "missing `else` falls at the reader, got {f:?}"
    );
}

#[test]
fn grow_als_name_bleibt_zuweisung() {
    // The head word decides: `grow = 1;` continues with a place
    // continuation and stays an assignment to a name of that spelling.
    let quelle = rahmen("    grow = 1;\n    return grow;\n");
    assert!(
        fehler(&quelle).is_empty(),
        "`grow` stays a name where no statement stands"
    );
}

#[test]
fn max_als_name_bleibt_name() {
    // `max` is a contextual word: a local of that spelling keeps parsing.
    let quelle = rahmen("    let max = 1;\n    return max;\n");
    assert!(
        fehler(&quelle).is_empty(),
        "`max` stays a name outside the clause position"
    );
}
