//! **Sprechproben in beide Richtungen** -- die Regel, die dieser Ordner an jeden Pruefer legt:
//! *ein Pruefer, der nicht fehlschlagen kann, ist kein Pruefer* (`pruefe-syntax.sh`).
//!
//! Jede Probe steht paarweise: eine **saubere** Form muss durchkommen, eine **vergiftete** muss
//! mit **benanntem** Code fallen. Der Code steht mit im Test, damit eine Absage nicht heimlich
//! ihre Bedeutung wechselt.

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

// -- Die Formen, die es absichtlich nicht gibt -------------------------------------------
// `pruefe-syntax.sh` greift sie im Text ab; hier muss der Uebersetzer sie abweisen.

#[test]
fn verbotene_formen_fallen() {
    faellt_mit("impl fn f() effects { pure } { while (x) { } }", "P035");
    faellt_mit("impl fn f() effects { pure } { for (i) { } }", "P035");
    faellt_mit("impl fn f() effects { pure } { goto ende; }", "P035");
    faellt_mit("impl fn f() effects { pure } { break; }", "P035");
    faellt_mit("impl fn f() effects { pure } { continue; }", "P035");
    // Der Auffangzweig -- die teuerste der vier: eine neue Variante soll brechen.
    faellt_mit(
        "impl fn f() effects { pure } { match k { _ => { } } }",
        "P034",
    );
    // Zuweisung ist kein Ausdruck (E2).
    faellt_mit("impl fn f() effects { pure } { if (x = y) { } }", "P001");
}

#[test]
fn sauberes_kommt_durch() {
    faellt_nicht(
        r#"
module caprock::probe {
    const N : u32 = 8;
    type Idx = u32 in 0 ..< N;
    opaque type Pa = u64;
    tagged type Kind = { Frame(Pa), Endpoint(u32) };
    linear type Parked;
    linear ghost type Held(Lock);

    lock CAPS protects { tabelle, baum } rank 2 masks irqs;
    atomic FERTIG : bool release;
    accumulates hoechststand : u64 merge max;

    spec fn wohlgeformt(c : ptr<normal, r> Raum) -> bool
        effects { pure }
        = forall s in slots of c : c.eintrag[s].benutzt;

    impl fn loeschen(c : ptr<normal, rw> Raum, s : Idx) -> u32
        requires  Held(CAPS), c.eintrag[s].benutzt
        ensures   !c.eintrag[s].benutzt, old(c.zahl) == c.zahl + 1
        maintains wohlgeformt
        effects   { writes c.eintrag, locks CAPS }
        costs     <= 200 ops
        by        induction over descendants of s
    {
        let alt = c.eintrag[s].objekt;
        c.eintrag[s].benutzt = false;
        c.zahl -= 1;
        if c.zahl == 0 {
            match c.eintrag[s].kind {
                Frame(p) => { frei(p); }
                Endpoint(e) => { }
            }
        }
        narrow c.zahl to 1 .. 4096 else { return 0; }
        traverse opfer over descendants of c.eintrag[s] by consuming
            touches consumes c.eintrag, writes c.objekte
        {
            loeschen(c, opfer);
        }
        return 0;
    }
}
"#,
    );
}

// -- Regel fuer Regel -------------------------------------------------------------------

#[test]
fn wortschatzwort_ist_kein_bezeichner() {
    faellt_nicht("impl fn f(zahl : u32) effects { pure } { }");
    faellt_mit("impl fn f(slot : u32) effects { pure } { }", "P002");
}

#[test]
fn feldname_nach_punkt_darf_ein_wort_sein() {
    // `c.slots[s]` steht so in FRAGMENTE.md -- nach `.` kann kein Schluesselwort stehen,
    // also kann dort auch keins verwechselt werden.
    faellt_nicht("impl fn f(c : ptr<normal, rw> T) effects { writes c } { c.slots[0].used = true; }");
}

#[test]
fn quantorendomaene_ist_geschlossen() {
    faellt_nicht("spec fn p(c : T) -> bool effects { pure } = forall s in slots of c : s.x;");
    faellt_mit(
        "spec fn p(c : T) -> bool effects { pure } = forall s in bloedsinn of c : s.x;",
        "P013",
    );
}

#[test]
fn annahme_ohne_klasse_faellt() {
    faellt_nicht(r#"assume a "die MMU tut, was ihr Modell sagt" falsifier sonde_a;"#);
    faellt_nicht(r#"assume a "qemu64 hat kein x2APIC" unfalsifiable "kein Geraet";"#);
    // Die dritte Klasse -- *nicht gefahren* -- ist die Abwesenheit beider Angaben.
    faellt_mit(r#"assume a "irgendwas";"#, "P029");
}

#[test]
fn schleifenformen() {
    faellt_nicht(
        "impl fn f() effects { pure } { forever s per_pass bounded 4096 ops \
         on_exceeded watchdog effects { reads BEREIT } progress tick { next s; } }",
    );
    // `on_exceeded` ist Pflicht (D11) -- der Ueberlauf wird benannt, nicht gedeutet.
    faellt_mit(
        "impl fn f() effects { pure } { forever per_pass bounded 4096 ops \
         effects { reads BEREIT } { } }",
        "P001",
    );
    // `by` ist Pflicht: jede Schleife nennt ihr Abstiegsmass.
    faellt_mit(
        "impl fn f() effects { pure } { traverse t over slots of c { } }",
        "P001",
    );
}

#[test]
fn uebergang_mit_pfeil_und_ortssuffix() {
    // Die aufgeloeste Mehrdeutigkeit: `A -> B` ist hier ein Uebergang, kein Feldzugriff.
    faellt_nicht(
        "device V at mmio { reg ST : u32 @0x0 class rw \
         transition an { ST: ACK -> ACK | TREIBER } effects { writes ST } }",
    );
    // Und ausserhalb bleibt `->` ein Ortssuffix.
    faellt_nicht("impl fn f(p : ptr<normal, rw> T) effects { writes p } { p->feld = 1; }");
}

#[test]
fn lexik() {
    faellt_nicht("const A : u32 = 0xFF_FF; -- ein Kommentar\nconst B : u32 = 0b1010_1010;");
    faellt_mit("const A : u32 = 0X10;", "L004");
    faellt_mit("const A : u32 = 0b12;", "L003");
    faellt_mit("assume a \"unbeendet\n falsifier s;", "L001");
    faellt_mit("const A : u32 = 1 $ 2;", "L006");
}

#[test]
fn zahl_passt_in_keinen_typ() {
    faellt_nicht("const A : u64 = 18_446_744_073_709_551_615;");
    faellt_mit(
        "const A : u64 = 999999999999999999999999999999999999999999;",
        "L005",
    );
}

#[test]
fn erholung_zeigt_mehr_als_einen_befund() {
    // Ein Lauf, der beim ersten Befund aufhoert, misst nicht -- er meldet.
    let quelle = "impl fn f() effects { pure } { let slot = 1; let dma = 2; }";
    let (_, absagen) = gabbro_syntax::lies("<probe>", quelle);
    let fehler = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler && a.code == "P002")
        .count();
    assert_eq!(fehler, 2, "beide Befunde muessen erscheinen:\n{}", absagen.zeige(quelle));
}

// -- The five paper cuts of `PLAN-HARDWARE.md` §49 B3 ------------------------------------
//
// **A poison probe cannot hold any of these**, and that is why they stand here: the corpus
// harness matches CODES, and nothing about these five changes a code. What changed is the
// text under the site -- the shape that was meant, in one line. *A cure that no guardian
// reads is a cure until the next rewrite.*

/// The expected code falls AND its refusal carries the given note.
///
/// **Both halves, or neither is a measurement.** Asserting only the code would pass with the
/// note deleted; asserting only the note would pass with the refusal moved to another rule.
fn faellt_mit_notiz(quelle: &str, code: &str, teil: &str) {
    let (_, absagen) = gabbro_syntax::lies("<probe>", quelle);
    let treffer: Vec<_> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler && a.code == code)
        .collect();
    assert!(
        !treffer.is_empty(),
        "expected {code}:\n{quelle}\n{}",
        absagen.zeige(quelle)
    );
    assert!(
        treffer
            .iter()
            .any(|a| a.notizen.iter().any(|n| n.contains(teil))),
        "{code} fell, but no note carries {teil:?}:\n{quelle}\n{}",
        absagen.zeige(quelle)
    );
}

#[test]
fn effects_ohne_klammern_nennt_die_form() {
    // Attempt 3 of 8, the sharpest: the right word in the right place, and `` `{` expected ``
    // as the whole answer.
    faellt_nicht("impl fn f() effects { pure } { }");
    faellt_mit_notiz(
        "impl fn f() effects pure { }",
        "P001",
        "`effects` takes a brace list",
    );
}

#[test]
fn leere_wirkungsliste_nennt_pure() {
    // Attempt 2 of 8, the ambiguous one -- the refusal STAYS, because `pure` says the same
    // thing on purpose. What was the paper cut is that the old text listed nine words and
    // left the reader to work out which of them means "none".
    faellt_mit_notiz(
        "impl fn f() effects { } { }",
        "P014",
        "writes `effects { pure }`",
    );
}

#[test]
fn fehlender_strichpunkt_nennt_die_regel() {
    // Attempt 5 of 8. `;` expected / `}` found has exactly one meaning wherever it can
    // happen, and the rule fits in a line.
    faellt_mit_notiz(
        "impl fn f() effects { pure } { return 0 }",
        "P001",
        "`;` terminates, it does not separate",
    );
}

#[test]
fn strichpunkt_nach_block_beschreibt_die_seite() {
    // Attempt 6 of 8. Same code, same rule, same accepted programs -- the text now says what
    // stands on the PAGE (`};`) instead of what the parser sees (a `;` on its own).
    let quelle = "impl fn f() effects { pure } { if x { }; }";
    let (_, absagen) = gabbro_syntax::lies("<probe>", quelle);
    let treffer: Vec<_> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler && a.code == "P033")
        .collect();
    assert!(
        treffer.iter().any(|a| a.text.contains("one token too many")),
        "P033 after a block must describe the page:\n{}",
        absagen.zeige(quelle)
    );
    // And the other half of the same code keeps its own wording -- a `;` with no block in
    // front of it IS a semicolon on its own.
    let allein = "impl fn f() effects { pure } { ; }";
    let (_, a2) = gabbro_syntax::lies("<probe>", allein);
    assert!(
        a2.absagen
            .iter()
            .any(|a| a.code == "P033" && a.text.contains("on its own")),
        "P033 without a block in front keeps its wording:\n{}",
        a2.zeige(allein)
    );
}

#[test]
fn modul_mit_strichpunkt_nennt_den_rumpf() {
    // The cut BEFORE the eight attempts, and it stands in line one of the file.
    faellt_nicht("module m { }");
    faellt_mit_notiz("module m;", "P001", "`module` carries a brace body");
}
