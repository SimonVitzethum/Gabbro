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
    // **Zehn aus `SPRACHE.md` Teil III §6, plus einer, der nicht daher stammt.**
    // `Phasen` («B37», 2026-08-17) hat keine Nummer in der Spezifikationsliste -- er haengt
    // hinten an, damit die zehn Fundstellen, die auf sie zeigen, stehenbleiben.
    assert_eq!(liste.len(), 12, "die ersten zehn stehen in SPRACHE.md Teil III §6");
    assert_eq!(
        liste.iter().filter(|p| p.nummer <= 10).count(),
        10,
        "die Numerierung der Spezifikation bleibt unangetastet"
    );
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
    // **Die Zahl ist angenagelt, und das ist der Zweck.** Sie war bis zum 2026-08-16
    // `SCHABLONEN.len()` -- keine einzige bewiesen. Jetzt ist eine bewiesen
    // (`table.induktion`, Isabelle2025-2, `beweise/`), und dieser Test hat die Buchfuehrung
    // dazu erzwungen: er faellt, bis die Zahl HIER und in `BEWEIS.md` nachgezogen ist.
    //
    // *Wer die naechste beweist, faellt wieder hier -- so soll es sein. Eine Zahl, die sich
    // still mitbewegt, ist keine Ratsche.*
    assert_eq!(
        ungedeckt(),
        11,
        "wenn eine Schablone nach Isabelle gebracht wurde, gehoert das hierher UND in BEWEIS.md"
    );
}


// -- Die Schablonen-Ratsche, DREI Zaehne -------------------------------------------------

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
    use gabbro_check::schablonen::{bewiesen, marke_gerissen, zulaessig, SCHABLONEN};
    assert!(
        !marke_gerissen(),
        "{} Schablonen gegen {} zulaessige ({} Grundmarke + {} bewiesene). \
         **Das ist ein gefallenes Tor, kein Hinweis.** Der Ausweg ist NICHT, die Marke zu \
         erhoehen: er ist, die naechste Schablone zu beweisen. Jeder Eintrag ueber der \
         Grundmarke kostet einen Beweis -- dauerhaft, nicht einmal.",
        SCHABLONEN.len(),
        zulaessig(),
        gabbro_check::schablonen::MARKE_OHNE_BEWEIS,
        bewiesen()
    );
}

use gabbro_check::schablonen::{Schablone, Stand};

// -- Die Sprechprobe zu beiden Zaehnen ---------------------------------------------------
//
// **Beide Zahn-Tests oben lesen die ECHTE Liste, und die ist gesund.** Damit sagen sie
// nichts darueber, ob der Mechanismus greift -- sie sagen nur, dass die heutigen Daten in
// Ordnung sind. *Ein Tor, das nie rot war, ist eine Zusage.* Die beiden Proben hier fuettern
// darum absichtlich kaputte Register.

fn probe(name: &'static str, fundstelle: &'static str, stand: Stand) -> Schablone {
    Schablone {
        name,
        haengt_an: &[],
        konstrukt: "Probe",
        pflicht: "Ein Satz, der lang genug ist, um die Pflichtpruefung zu passieren, und zwar deutlich.",
        stand,
        voraussetzungen: &[],
        fundstelle,
    }
}

#[test]
fn der_erste_zahn_spricht() {
    use gabbro_check::schablonen::ohne_fundstelle_in;
    let gesund = [probe("a", "MESSUNGEN.md", Stand::Entworfen)];
    assert!(
        ohne_fundstelle_in(&gesund).is_empty(),
        "ein Eintrag MIT Fundstelle darf nicht anschlagen"
    );

    let krank = [
        probe("a", "MESSUNGEN.md", Stand::Entworfen),
        probe("ohne", "   ", Stand::Entworfen),
    ];
    assert_eq!(
        ohne_fundstelle_in(&krank),
        vec!["ohne"],
        "**der erste Zahn greift nicht.** Ein Eintrag ohne Fundstelle ist genau das, wogegen \
         er gebaut ist -- er muss ihn beim Namen nennen"
    );
}

#[test]
fn der_zweite_zahn_spricht() {
    use gabbro_check::schablonen::{marke_gerissen_in, MARKE_OHNE_BEWEIS};
    // Grundmarke voll, nichts bewiesen: haelt.
    let voll: Vec<_> = (0..MARKE_OHNE_BEWEIS)
        .map(|_| probe("x", "MESSUNGEN.md", Stand::Entworfen))
        .collect();
    assert!(!marke_gerissen_in(&voll), "die Grundmarke selbst darf halten");

    // Einer mehr, nichts bewiesen: reisst.
    let mut zuviel = voll.clone();
    zuviel.push(probe("neunzehnter", "MESSUNGEN.md", Stand::Entworfen));
    assert!(
        marke_gerissen_in(&zuviel),
        "**der zweite Zahn greift nicht.** Genau das war der Fehler bis zum 2026-08-17: \
         die alte Fassung las `alle unbewiesen && zu lang`, und mit der ersten bewiesenen \
         Schablone wurde sie fuer immer falsch"
    );

    // Einer mehr, aber einer bewiesen: haelt wieder -- der Beweis KAUFT den Platz.
    let mut gekauft = zuviel.clone();
    gekauft[0] = probe("x", "MESSUNGEN.md", Stand::Bewiesen);
    assert!(
        !marke_gerissen_in(&gekauft),
        "ein Beweis muss einen Platz kaufen -- sonst ist die Ratsche ein Anschlag"
    );

    // Und zwar GENAU einen: zwei ueber der Marke, ein Beweis -> reisst wieder.
    let mut zweiter = gekauft.clone();
    zweiter.push(probe("zwanzigster", "MESSUNGEN.md", Stand::Entworfen));
    assert!(
        marke_gerissen_in(&zweiter),
        "ein Beweis kauft EINEN Platz, nicht die Marke ab"
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

/// **Die LEBENDE Vertrauensflaeche — die Zahl, die bis zum 2026-08-17 nirgends stand.**
///
/// `ungedeckt()` wirft zwei sehr verschiedene Zustaende zusammen: `Entworfen` ist eine Zusage
/// ueber etwas, das niemand gebaut hat; `Getragen` heisst, **der Uebersetzer stuetzt sich JETZT
/// darauf.** Ist ein getragener Satz falsch, ist das erzeugte C falsch — ab dem naechsten Lauf.
///
/// > *Der Erzeuger hat die lebende Flaeche an einem Tag von 1 auf 4 gebracht, waehrend
/// > `ungedeckt()` sich um eins bewegte.* Wer nur die eine Zahl liest, liest die harmlosere.
///
/// **Dieser Test nagelt beide an**, aus demselben Grund wie die Ratsche: eine Zahl, die sich
/// still mitbewegt, ist keine.
#[test]
fn die_lebende_vertrauensflaeche_ist_gebucht() {
    use gabbro_check::schablonen::{bewiesen, lebend_ungedeckt, ungedeckt, SCHABLONEN, Stand};
    assert_eq!(
        lebend_ungedeckt(),
        1,
        "getragen und unbewiesen: wer eine Schablone in den Erzeuger einbaut, vergroessert \
         die LEBENDE Vertrauensbasis -- und das gehoert hierher UND in BEWEIS.md"
    );
    assert_eq!(ungedeckt(), 11);
    assert_eq!(bewiesen(), 9);

    // **Und die Zustaende muessen sich addieren** -- sonst fuehrt jemand einen vierten ein,
    // und die beiden Zahlen sagen ploetzlich nichts mehr ueber dieselbe Menge.
    let entworfen = SCHABLONEN.iter().filter(|s| s.stand == Stand::Entworfen).count();
    assert_eq!(
        entworfen + lebend_ungedeckt() + bewiesen(),
        SCHABLONEN.len(),
        "entworfen + getragen + bewiesen muss die ganze Liste sein"
    );
}

// -- Zahn 3: die Rueckrichtung ------------------------------------------------------------

#[test]
fn jede_bewiesene_schablone_bindet_ihre_praemissen() {
    let ohne = gabbro_check::schablonen::ohne_rueckrichtung();
    assert!(
        ohne.is_empty(),
        "bewiesene Schablonen ohne Rueckrichtung: {ohne:?} -- **ein Beweis, der nicht sagt, \
         welcher Pass seine Praemissen herstellt, haengt in der Luft.** Er sieht im Zeugnis \
         aus wie Deckung und ist keine"
    );
}

#[test]
fn der_dritte_zahn_spricht() {
    use gabbro_check::schablonen::{in_der_luft_in, ohne_rueckrichtung_in, Voraussetzung};
    // Gesund: bewiesen UND gebunden.
    let mut gesund = probe("a", "MESSUNGEN.md", Stand::Bewiesen);
    gesund.voraussetzungen = &[Voraussetzung { was: "x", durch: Some("M103 (m1.rs)"), braeuchte: None }];
    assert!(ohne_rueckrichtung_in(&[gesund.clone()]).is_empty());
    assert!(in_der_luft_in(&[gesund]).is_empty());

    // Krank I: bewiesen, aber gar keine Praemisse genannt.
    let krank = probe("stumm", "MESSUNGEN.md", Stand::Bewiesen);
    assert_eq!(
        ohne_rueckrichtung_in(&[krank]),
        vec!["stumm"],
        "**der dritte Zahn greift nicht.** Ein bewiesener Eintrag ohne Rueckrichtung ist \
         genau das, wogegen er gebaut ist"
    );

    // Krank II: die Praemisse steht da, und NIEMAND stellt sie her.
    let mut luftig = probe("luftig", "MESSUNGEN.md", Stand::Bewiesen);
    luftig.voraussetzungen = &[Voraussetzung { was: "getrennt r s", durch: None, braeuchte: Some("N009") }];
    assert_eq!(
        in_der_luft_in(&[luftig]),
        vec![("luftig", "getrennt r s")],
        "eine Praemisse ohne Hersteller muss beim Namen genannt werden"
    );

    // Und ein ENTWORFENER Eintrag darf schweigen -- sein Satz ist nicht gefuehrt.
    let entworfen = probe("entwurf", "MESSUNGEN.md", Stand::Entworfen);
    assert!(ohne_rueckrichtung_in(&[entworfen]).is_empty());
}

#[test]
fn die_praemissen_ohne_pass_sind_gezaehlt() {
    // **Die Marke, und sie darf nur FALLEN.** Am 2026-08-18 gemessen: neun bewiesene
    // Schablonen, siebzehn Praemissen, und `device.konstruktor` stellte niemand her.
    //
    // **2026-08-19: die Marke faellt von 8 auf 7** -- und die zweite Zusicherung dreht sich
    // um. Der Fund, der Zahn 3 erzwungen hat (*„zwei `reg` haben getrennte Lagen"* -- der
    // HAUPTSATZ von `Device_Konstruktor.thy` ohne Prueferzeile), ist geschlossen: `N009`
    // rechnet die Byte-Bereiche nach, `N010` faellt `stride 0`.
    //
    // > *Eine Zusicherung, die ein Loch bewacht, muss umgedreht werden, wenn es zu ist --
    // > sonst haelt sie es offen.* Und der Wechsel steht hier, damit er nicht als
    // > Testkosmetik durchgeht.
    let luft = gabbro_check::schablonen::in_der_luft();
    assert!(
        luft.len() <= 7,
        "Praemissen ohne Pass: {} -- die Marke ist 7 und sie geht nach unten:\n{luft:#?}",
        luft.len()
    );
    assert!(
        !luft.iter().any(|(s, _)| *s == "device.konstruktor"),
        "`device.konstruktor` ist seit 2026-08-19 gedeckt (N009/N010) -- \
         steht er wieder in der Luft, ist eine Regel zurueckgegangen"
    );
}
