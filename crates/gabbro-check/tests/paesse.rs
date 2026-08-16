//! **Sprechproben fuer die gebauten Paesse** -- je Pass ein Gift und ein sauberer Fall.
//!
//! Und eine Probe ueber der Passliste selbst: ein Pass, der als `Gebaut` gefuehrt wird, muss
//! auch etwas fangen koennen. Sonst waere die Liste eine Behauptung ueber Deckung.

use gabbro_check::{passliste, pruefe, Zustand};
use gabbro_syntax::diag::Stufe;

fn codes(quelle: &str) -> Vec<(&'static str, Stufe)> {
    let (baum, mut absagen) = gabbro_syntax::lies("<probe>", quelle);
    let _ = pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .map(|a| (a.code, a.stufe))
        .collect()
}

fn faellt_mit(quelle: &str, code: &str) {
    let c = codes(quelle);
    assert!(
        c.iter().any(|(k, s)| *k == code && *s == Stufe::Fehler),
        "erwartet war {code}, gefallen ist {c:?}\n{quelle}"
    );
}

fn faellt_nicht(quelle: &str) {
    let c = codes(quelle);
    assert!(
        !c.iter().any(|(_, s)| *s == Stufe::Fehler),
        "sauber, faellt aber mit {c:?}\n{quelle}"
    );
}

// -- Pass 1: Namen ----------------------------------------------------------------------

#[test]
fn doppelte_deklaration_faellt() {
    faellt_mit(
        "const A : u32 = 1;\nconst A : u32 = 2;",
        "N001",
    );
    faellt_nicht("const A : u32 = 1;\nconst B : u32 = 2;");
}

#[test]
fn zwei_architekturen_sind_keine_doppelung() {
    // FRAGMENTE.md F5 deklariert `invoke` zweimal -- einmal je Architektur. Wer das als
    // Doppelung meldet, verbietet die bedingte Uebersetzung, die `arch`/`when` tragen.
    faellt_nicht(
        "prim fn invoke(nr : u64) -> u64 effects { writes maschine } arch x86_64;\n\
         prim fn invoke(nr : u64) -> u64 effects { writes maschine } arch aarch64;",
    );
    faellt_mit(
        "prim fn invoke(nr : u64) -> u64 effects { writes maschine } arch x86_64;\n\
         prim fn invoke(nr : u64) -> u64 effects { writes maschine } arch x86_64;",
        "N001",
    );
}

#[test]
fn doppelter_grundwert_faellt() {
    faellt_mit(
        "reason R { A = 1 \"eins\" B = 1 \"auch eins\" exhaustive }",
        "N002",
    );
    faellt_nicht("reason R { A = 1 \"eins\" B = 2 \"zwei\" exhaustive }");
}

#[test]
fn ueberlappende_registerbits_fallen() {
    // D2: jedes Bit eines Wortes ist benannt -- genau einmal.
    faellt_mit(
        "device V at mmio { reg C : u32 @0x0 class rw fields { A @[7:4], B @5, } }",
        "N003",
    );
    faellt_nicht(
        "device V at mmio { reg C : u32 @0x0 class rw fields { A @[7:4], B @3, } }",
    );
}

// -- Pass 3: M1 + V1–V3 -----------------------------------------------------------------

const RAHMEN: &str = "const G : u32 = 65535;\ntype Z = u32 in 0 .. G;\n";

fn m1(rumpf: &str) -> String {
    format!("{RAHMEN}impl fn f(a : Z, b : Z, n : Z) -> Z effects {{ pure }} {{ {rumpf} }}")
}

/// **Zwei verschiedene Befunde, und der Unterschied ist wichtig:**
/// `M104` heisst *der Wert ist auf der Maschine nicht darstellbar* (die Breite ist weg),
/// `M101` heisst *der Wert passt nicht in den deklarierten Bereich seines Ziels*.
/// Wer beides zusammenwirft, verliert die Aussage, die M1 ueberhaupt macht.
#[test]
fn ueberlauf_faellt_ohne_pruefung() {
    faellt_mit(&m1("return a + 1;"), "M101");
    faellt_mit(
        "impl fn f(a : u32, b : u32) -> u32 effects { pure } { return a * b; }",
        "M104",
    );
    // V1: die geprüfte Bereichsbedingung verengt die geprüfte Stelle im Zweig danach.
    faellt_nicht(&m1("if a < G { return a + 1; } return a;"));
}

#[test]
fn unterlauf_faellt_ohne_beziehung() {
    faellt_mit(&m1("return a - b;"), "M104");
    // V2: unter `a >= b` faengt `a - b` bei 0 an.
    faellt_nicht(&m1("if a >= b { return a - b; } return 0;"));
}

#[test]
fn v1_gilt_auch_nach_einem_zweig_der_immer_verlaesst() {
    // Der fruehe Rueckstieg ist die haeufigste Form im Baum; ohne diese Regel braucht
    // jede einzelne ein `narrow`, und die Messlatte faellt an einer Redewendung.
    faellt_nicht(&m1("if a < b { return 0; } return a - b;"));
}

#[test]
fn nenner_ohne_null() {
    faellt_mit(&m1("return a / n;"), "M102");
    faellt_nicht(&m1("if n >= 1 { return a / n; } return 0;"));
}

#[test]
fn ein_fakt_stirbt_beim_schreiben() {
    // „bei jedem Schreiben auf eine beteiligte Stelle stirbt der Fakt" -- zweimal senken
    // ist einmal zu viel.
    faellt_mit(
        &format!(
            "{RAHMEN}type Zelle = {{ w : Z, }};\n\
             impl fn f(z : ptr<normal, rw> Zelle) effects {{ writes z }} \
             {{ if z.w >= 1 {{ z.w -= 1; z.w -= 1; }} }}"
        ),
        "M104",
    );
}

#[test]
fn schleifen_tragen_keine_fakten_hinein() {
    faellt_mit(
        &format!(
            "{RAHMEN}type Zelle = {{ w : Z, }};\n\
             impl fn f(z : ptr<normal, rw> Zelle, c : ptr<normal, rw> T) \
             effects {{ writes z, writes c }} \
             {{ if z.w >= 1 {{ traverse s over slots of c by unvisited {{ z.w -= 1; }} }} }}"
        ),
        "M104",
    );
}

#[test]
fn wrapping_ist_der_erlaubte_ueberlauf() {
    faellt_nicht(
        "table T { slot { m : u32 wrapping, } }\n\
         impl fn f(t : ptr<normal, rw> T, i : u32) effects { writes t.slots } \
         { t.slots[i].m += 1; }",
    );
}

#[test]
fn v3_bindet_die_nutzlast_der_variante() {
    faellt_nicht(
        "const G : u32 = 65535;\ntype Z = u32 in 0 .. G;\n\
         tagged type A = { Eins(Z), Zwei(Z) };\n\
         impl fn f(a : A) -> Z effects { pure } \
         { match a { Eins(x) => { return x; } Zwei(y) => { return y; } } return 0; }",
    );
}

#[test]
fn index_gegen_die_laenge_des_feldes() {
    faellt_mit(
        "type W = u32 in 0 .. 127;\nstatic mut f : [u32; 64] = 0;\n\
         impl fn g(i : W) -> u32 effects { reads f } { return f[i]; }",
        "M103",
    );
    faellt_nicht(
        "type W = u32 in 0 .. 63;\nstatic mut f : [u32; 64] = 0;\n\
         impl fn g(i : W) -> u32 effects { reads f } { return f[i]; }",
    );
}

#[test]
fn m1_zaehlt_was_es_nicht_weiss() {
    // Die Deckungszahl ist der Unterschied zwischen „nichts gefunden" und „nichts angesehen".
    let (baum, mut absagen) = gabbro_syntax::lies("<probe>", &m1("return a;"));
    let bericht = pruefe(&baum, &mut absagen);
    assert!(bericht.m1.gesamt() > 0, "M1 hat nichts angesehen");
    assert_eq!(bericht.m1.unbekannt, 0, "hier ist alles typisierbar");

    let (baum, mut absagen) =
        gabbro_syntax::lies("<probe>", "impl fn f(x : Fremd) effects { pure } { fremd(x); }");
    let bericht = pruefe(&baum, &mut absagen);
    assert!(
        bericht.m1.unbekannt > 0,
        "ein unbekannter Typ muss als unbekannt gezaehlt werden, nicht als geprueft"
    );
}

// -- Pass 6: Schleifen ------------------------------------------------------------------

#[test]
fn leave_ohne_marke_faellt() {
    faellt_mit(
        "impl fn f() effects { pure } { forever s per_pass bounded 8 ops on_exceeded w \
         effects { reads X } { leave anders; } }",
        "S001",
    );
    faellt_nicht(
        "impl fn f() effects { pure } { forever s per_pass bounded 8 ops on_exceeded w \
         effects { reads X } { leave s; } }",
    );
}

#[test]
fn next_zielt_auf_die_umgebende_marke() {
    faellt_mit(
        "impl fn f() effects { pure } { traverse t over slots of c by unvisited { next t; } }",
        "S001",
    );
}

// -- Pass 8: effects --------------------------------------------------------------------

#[test]
fn fehlende_wirkungen_fallen() {
    // Der Kern der Regel: die Pflicht faellt an der ABWESENHEIT.
    faellt_mit("impl fn f() { }", "E001");
    faellt_nicht("impl fn f() effects { pure } { }");
    // `spec fn` hat keine Laufzeitwirkung -- fuer sie ist die Klausel freigestellt.
    faellt_nicht("spec fn p(c : T) -> bool = c.x;");
}

#[test]
fn pure_neben_anderen_wirkungen_faellt() {
    faellt_mit("impl fn f(c : T) effects { pure, writes c } { }", "E002");
    faellt_nicht("impl fn f(c : T) effects { writes c } { }");
}

#[test]
fn praedikatsrumpf_nur_fuer_spec() {
    faellt_mit("impl fn p(c : T) -> bool effects { pure } = c.x;", "E004");
    faellt_nicht("spec fn p(c : T) -> bool effects { pure } = c.x;");
}

// -- Ueber die Liste selbst -------------------------------------------------------------

#[test]
fn die_passliste_sagt_was_sie_nicht_prueft() {
    let liste = passliste();
    assert_eq!(liste.len(), 10, "die Reihenfolge steht in SPRACHE.md Teil III §6");
    let offen = gabbro_check::ungeprueft();
    assert!(
        !offen.is_empty(),
        "solange Paesse fehlen, muss die Liste sie fuehren -- \
         ein Werkzeug, das nur meldet, was es findet, laesst Ungeprueftes wie ein Gruen aussehen"
    );
    for p in &liste {
        if let Zustand::Offen(text) = p.zustand {
            assert!(
                !text.is_empty(),
                "Pass {} ist offen, sagt aber nicht, was damit ungeprueft bleibt",
                p.name
            );
        }
    }
}

#[test]
fn jeder_gebaute_pass_kann_fallen() {
    // Sprechprobe ueber der Liste: fuer jeden `Gebaut`-Pass steht hier ein Gift.
    let gifte: &[(&str, &str)] = &[
        ("Namen", "const A : u32 = 1;\nconst A : u32 = 2;"),
        (
            "M4/Schleifen",
            "impl fn f() effects { pure } { traverse t over slots of c by unvisited { leave t; } }",
        ),
        (
            "M1 + V1–V3",
            "const G : u32 = 65535;\ntype Z = u32 in 0 .. G;\n\
             impl fn f(a : Z) -> Z effects { pure } { return a + 1; }",
        ),
        ("effects", "impl fn f() { }"),
    ];
    for p in passliste() {
        if p.zustand != Zustand::Gebaut {
            continue;
        }
        let gift = gifte
            .iter()
            .find(|(name, _)| *name == p.name)
            .unwrap_or_else(|| panic!("Pass `{}` ist gebaut, hat aber kein Gift", p.name));
        let c = codes(gift.1);
        assert!(
            c.iter().any(|(_, s)| *s == Stufe::Fehler),
            "Pass `{}` faellt bei seinem eigenen Gift nicht",
            p.name
        );
    }
}

// -- Die dritte Zaehlspalte ---------------------------------------------------------------

/// **Die Schablonenliste ist die Ratsche, die die Schablonen bisher nicht hatten.**
/// Wortschatz und Axiomschicht haben ihre; die Erzeuger-Schablonen wuchsen monoton und
/// unbeziffert -- genau wie die Axiomschicht vor ihrer Auszaehlung.
#[test]
fn jede_schablone_nennt_ihre_pflicht() {
    use gabbro_check::schablonen::{ungedeckt, SCHABLONEN};
    assert!(
        SCHABLONEN.len() >= 12,
        "die Liste ist unvollstaendig -- jede erzeugte Form schuldet einen Eintrag"
    );
    for s in SCHABLONEN {
        assert!(
            s.pflicht.len() > 40,
            "`{}` nennt keine Pflicht -- ein Eintrag ohne den Satz, was genau EINMAL gezeigt \
             werden muss, ist ein Name und keine Buchung",
            s.name
        );
        assert!(!s.fundstelle.is_empty(), "`{}` ohne Fundstelle", s.name);
        assert!(!s.konstrukt.is_empty(), "`{}` ohne Konstrukt", s.name);
    }
    // **Die Fallrichtung**: ein Eintrag geht nur bewiesen oder mitsamt seinem Konstrukt.
    // Wer einen Namen still entfernt oder umformuliert, bricht hier.
    use gabbro_check::schablonen::RATSCHE;
    for name in RATSCHE {
        assert!(
            SCHABLONEN.iter().any(|s| s.name == *name),
            "`{name}` ist aus der Schablonenliste verschwunden. Ein Eintrag geht nur \
             BEWIESEN oder MITSAMT SEINEM KONSTRUKT -- nicht durch Umformulierung. \
             Wurde das Konstrukt entfernt, gehoert der Name aus RATSCHE heraus, und das \
             ist eine sichtbare Aenderung statt einer stillen."
        );
    }
    // Solange keine bewiesen ist, muss die Zahl das sagen -- eine Liste, die aussieht wie
    // Deckung, waere schlimmer als keine.
    assert_eq!(
        ungedeckt(),
        SCHABLONEN.len(),
        "wenn eine Schablone nach Isabelle gebracht wurde, gehoert das hierher UND in BEWEIS.md"
    );
}


// -- Die Schablonen-Ratsche, zwei Zaehne ------------------------------------------------

#[test]
fn kein_schablonen_eintrag_ohne_fundstelle() {
    let ohne = gabbro_check::schablonen::ohne_fundstelle();
    assert!(
        ohne.is_empty(),
        "Schablonen ohne Fundstelle: {ohne:?} -- der erste Zahn der Ratsche verlangt einen \
         GEMESSENEN Bedarf je Eintrag, und eine Fundstelle ist sein Mindestbeleg"
    );
}

#[test]
fn das_schablonenregister_reisst_seine_marke_nicht() {
    use gabbro_check::schablonen::{marke_gerissen, MARKE_OHNE_BEWEIS, SCHABLONEN};
    assert!(
        !marke_gerissen(),
        "{} Schablonen, keine bewiesen -- die Marke steht bei {MARKE_OHNE_BEWEIS}. \
         **Das ist ein gefallenes Tor, kein Hinweis.** Der Ausweg ist NICHT, die Marke zu \
         erhoehen: er ist, die erste Schablone zu beweisen. Benannt ist sie seit langem -- \
         `table.induktion`, die kleinste der Liste. Eine bewiesene von achtzehn ist \
         qualitativ etwas anderes als null von siebzehn.",
        SCHABLONEN.len()
    );
}


#[test]
fn schablonen_abhaengigkeiten_zeigen_auf_vorhandene_eintraege() {
    use gabbro_check::schablonen::SCHABLONEN;
    for sch in SCHABLONEN {
        for ziel in sch.haengt_an {
            assert!(
                SCHABLONEN.iter().any(|a| a.name == *ziel),
                "`{}` haengt an `{ziel}` -- diesen Eintrag gibt es nicht. Eine Abhaengigkeit \
                 auf einen fehlenden Namen ist schlechter als keine: sie sieht aus wie eine \
                 gebuchte Beziehung",
                sch.name
            );
        }
    }
}
