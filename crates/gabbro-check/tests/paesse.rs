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
        "prim fn invoke(nr : u64) -> u64 effects { writes maschine } arch x86_64;\n \
         prim fn invoke(nr : u64) -> u64 effects { writes maschine } arch aarch64;",
    );
    faellt_mit(
        "prim fn invoke(nr : u64) -> u64 effects { writes maschine } arch x86_64;\n \
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
            "{RAHMEN}type Zelle = {{ w : Z, }};\n \
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
            "{RAHMEN}type Zelle = {{ w : Z, }};\n \
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
        "table T { slot { m : u32 wrapping, } }\n \
         impl fn f(t : ptr<normal, rw> T, i : u32) effects { writes t.slots } \
         { t.slots[i].m += 1; }",
    );
}

#[test]
fn v3_bindet_die_nutzlast_der_variante() {
    faellt_nicht(
        "const G : u32 = 65535;\ntype Z = u32 in 0 .. G;\n \
         tagged type A = { Eins(Z), Zwei(Z) };\n \
         impl fn f(a : A) -> Z effects { pure } \
         { match a { Eins(x) => { return x; } Zwei(y) => { return y; } } return 0; }",
    );
}

#[test]
fn index_gegen_die_laenge_des_feldes() {
    faellt_mit(
        "type W = u32 in 0 .. 127;\nstatic mut f : [u32; 64] = 0;\n \
         impl fn g(i : W) -> u32 effects { reads f } { return f[i]; }",
        "M103",
    );
    faellt_nicht(
        "type W = u32 in 0 .. 63;\nstatic mut f : [u32; 64] = 0;\n \
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
    faellt_nicht("type T = { x : bool, }; spec fn p(c : T) -> bool = c.x;");
}

#[test]
fn pure_neben_anderen_wirkungen_faellt() {
    faellt_mit("type T = { x : bool, }; impl fn f(c : T) effects { pure, writes c } { }", "E002");
    faellt_nicht("type T = { x : bool, }; impl fn f(c : T) effects { writes c } { }");
}

#[test]
fn praedikatsrumpf_nur_fuer_spec() {
    faellt_mit("type T = { x : bool, }; impl fn p(c : T) -> bool effects { pure } = c.x;", "E004");
    faellt_nicht("type T = { x : bool, }; spec fn p(c : T) -> bool effects { pure } = c.x;");
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
            "const G : u32 = 65535;\ntype Z = u32 in 0 .. G;\n \
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
    // **1 -> 2 am 2026-08-28, und der Anstieg ist der Preis von Zuschnitt (c).**
    // `table.ops.erhaltung` ist von ENTWORFEN auf GETRAGEN gegangen, weil `emit.rs::ops` die
    // Operationen jetzt ausliefert. *Genau diese Bewegung soll diese Zahl sichtbar machen:*
    // eine Klempnereipflicht wurde geschlossen, und sie wurde nicht erledigt, sondern in die
    // Erzeugerflaeche verschoben. K100s zweites Tor (`L <= 4`) haelt weiter.
    assert_eq!(
        lebend_ungedeckt(),
        2,
        "getragen und unbewiesen: wer eine Schablone in den Erzeuger einbaut, vergroessert \
         die LEBENDE Vertrauensbasis -- und das gehoert hierher UND in BEWEIS.md"
    );
    assert_eq!(ungedeckt(), 11);
    // **10 seit dem 2026-08-20** -- `restrict.alleinzugriff` ist in Isabelle und baut.
    assert_eq!(bewiesen(), 10);

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
    //
    // **Und am selben Tag von 7 auf 8, aus der anderen Richtung.** `Gruppe_Erhaltung.thy`
    // hat eine Praemisse BENANNT, die vorher unsichtbar war: *ein gehaltener Sperrabdruck
    // haelt einen fremden Kern wirklich fern* -- eine Aussage der Axiomschicht.
    //
    // > **Die Marke faellt durch einen PASS und steigt durch einen BEWEIS.** Das ist keine
    // > Aufweichung der Ratsche, sondern ihre genauere Fassung: ein Beweis, der die Zahl
    // > der offenen Praemissen erhoeht, hat gearbeitet -- der umgekehrte Fall waere der
    // > verdaechtige. *Was verboten bleibt, ist ein Anstieg ohne neuen Beweis.*
    let luft = gabbro_check::schablonen::in_der_luft();
    assert!(
        // **9 seit dem 2026-08-20**, und sie ist genau so gestiegen, wie die Regel es
        // erlaubt: `restrict.alleinzugriff` benennt die `own`-Entscheidung als offene
        // Praemisse. *Ein Beweis, der die Zahl der offenen Praemissen erhoeht, hat
        // gearbeitet.*
        luft.len() <= 9,
        "Praemissen ohne Pass: {} -- die Marke ist 9. Sie faellt durch einen PASS \
         und steigt nur durch einen BEWEIS, der eine neue Praemisse benennt:\n{luft:#?}",
        luft.len()
    );
    assert!(
        !luft.iter().any(|(s, _)| *s == "device.konstruktor"),
        "`device.konstruktor` ist seit 2026-08-19 gedeckt (N009/N010) -- \
         steht er wieder in der Luft, ist eine Regel zurueckgegangen"
    );
}

// --- Stufe 7 ---

/// **Ein `reason` eine Modulebene WEITER AUSSEN als die Funktion, die ihn nennt.**
///
/// Der Fehlerkanal wird zweimal aufgeloest: erst die FUNKTION vom Rufort aus, dann ihr
/// `reason` von IHREM Modul aus. **Die erste Fassung von `Umgebung::fehlerkanaele` hat die
/// zweite Aufloesung vergessen** und den Namen mit `qualifiziere(pfad, …)` an das Modul der
/// Funktion geheftet -- ein Schluessel, den nichts traegt.
///
/// > Der ganze Beispielkorpus deklariert `reason` und Rumpf im SELBEN Modul, und
/// > `beispiele/48` tut es auch. *Diese Probe ist die einzige Stelle, an der der Fehler
/// > auffiele* -- und ohne sie waere er ein `M119` an einem Programm, das in Ordnung ist.
///
/// Gefunden nicht durch Nachdenken, sondern weil `pruefe-zahlen.py` die Zahl der *„Blicke
/// ohne Modulkandidaten -- jeder ein moegliches `M103`-Loch"* um eins steigen sah.
#[test]
fn ein_grund_aus_dem_umgebenden_modul_loest_auf() {
    let quelle = r#"
module probe {
reason HolFehler { Leer = 1 "leer"  Kaputt = 2 "kaputt"  exhaustive }
module innen {
extern fn hol() -> u32 or HolFehler effects { pure } costs <= 1 ops;
impl fn ruf() -> u32 effects { pure } costs <= 12 ops {
    let v = hol() else (e) {
        match e { Leer => { return 1; } Kaputt => { return 2; } }
    }
    return v;
}
}
}
"#;
    let c = codes(quelle);
    let fehler: Vec<&str> = c
        .iter()
        .filter(|(_, s)| *s == Stufe::Fehler)
        .map(|(k, _)| *k)
        .collect();
    assert!(
        fehler.is_empty(),
        "der `reason` steht im umgebenden Modul und loest auf -- gefallen ist {fehler:?}"
    );
}

/// **Die Gegenrichtung derselben Probe:** derselbe Aufbau, ein Fall zu wenig im `match`.
///
/// *Ohne sie sagte die Probe darueber nur, dass NICHTS faellt* -- und das saehe genauso aus,
/// wenn `e` gar keinen Typ bekaeme und `M123` deshalb nie faellig wuerde. **W10: nicht
/// abgewiesen ist nicht bestaetigt.**
#[test]
fn ein_grund_aus_dem_umgebenden_modul_haelt_auch_zu() {
    faellt_mit(
        r#"
module probe {
reason HolFehler { Leer = 1 "leer"  Kaputt = 2 "kaputt"  exhaustive }
module innen {
extern fn hol() -> u32 or HolFehler effects { pure } costs <= 1 ops;
impl fn ruf() -> u32 effects { pure } costs <= 12 ops {
    let v = hol() else (e) {
        match e { Leer => { return 1; } }
    }
    return v;
}
}
}
"#,
        "M123",
    );
}

// -- `N047` / `N048`: the register layout, in both directions -----------------------------

/// **The audit of 2026-09-01, and it came out of the emitted C rather than out of a reading.**
///
/// `clang -Wcast-align` over all 63 emitted units reports 54 casts from `volatile uint8_t *`
/// to a wider type -- every one an MMIO access. On the corpus each is in fact aligned; what
/// was missing was anything that HELD it there.
#[test]
fn unausgerichtete_registerlage_faellt() {
    let d = |reg: &str| {
        format!("module p {{ opaque type Pa = u64;\ndevice D(basis : Pa) at mmio {{\n{reg}\n}}\n}}")
    };
    faellt_mit(&d("reg A : u64 @0x04 class rw"), "N047");
    faellt_mit(&d("reg A : u32 @0x21 class rw"), "N047");
    faellt_mit(&d("reg A : u16 @0x03 class rw"), "N047");

    // **The counter-direction, and the third case is the one that matters:** a byte-wide
    // register is aligned at every offset, and the rule must not invent a refusal for it.
    faellt_nicht(&d("reg A : u64 @0x08 class rw"));
    faellt_nicht(&d("reg A : u8 @0x03 class rw"));
    // The corpus shape itself -- `02-geraet.gab` writes exactly this pair.
    faellt_nicht(&d("reg A : u32 @0x18 class rw\nreg B : u32 @0x1c class rw"));
}

/// **Between `N009` (two registers overlap) and `N010` (`stride 0`) stood the case nobody
/// asked: a register eight bytes wide in a cell four bytes long.**
///
/// `N009` compares registers against EACH OTHER and never against the stride, so `F[0].X`
/// and `F[1].X` named the same bytes and the checker said `0 errors`.
#[test]
fn bankregister_jenseits_der_zelle_faellt() {
    let d = |bank: &str| {
        format!(
            "module p {{ opaque type Pa = u64;\ndevice D(basis : Pa) at mmio {{\n\
             reg C : u64 @0x00 class r\n{bank}\n}}\n}}"
        )
    };
    // wider than the cell
    faellt_mit(&d("bank F at 0x100 stride 4 count 8 { reg X : u64 @0x0 class rw }"), "N048");
    // inside the cell by its offset, past it by its width
    faellt_mit(&d("bank F at 0x100 stride 8 count 8 { reg X : u64 @0x10 class rw }"), "N048");

    // **The counter-direction is the real bank of `02-geraet.gab`:** stride 16, two 64-bit
    // registers at 0 and 8. It fits exactly, and exactly-fitting must stay silent.
    faellt_nicht(&d(
        "bank F at 0x100 stride 16 count 8 { reg X : u64 @0x0 class rw reg Y : u64 @0x8 class rw }",
    ));
}

/// **`N049` -- and the reason it exists is that `N009`'s reason stopped applying.**
///
/// `N009` writes down why it stays out: *"a bank sits at a COMPUTED base; holding it against
/// the main level would mean guessing the base."* True -- and irrelevant the moment the base
/// is a literal. Then the comparison is exact, and the case it protected is real.
#[test]
fn bank_ueber_fremden_bytes_faellt() {
    let d = |inhalt: &str| {
        format!("module p {{ opaque type Pa = u64;\ndevice D(basis : Pa) at mmio {{\n{inhalt}\n}}\n}}")
    };
    faellt_mit(
        &d("reg C : u64 @0x100 class rw\nbank F at 0x100 stride 8 count 8 { reg X : u64 @0x0 class rw }"),
        "N049",
    );
    faellt_mit(
        &d("reg C : u64 @0x138 class rw\nbank F at 0x100 stride 8 count 8 { reg X : u64 @0x0 class rw }"),
        "N049",
    );
    faellt_mit(
        &d("reg C : u64 @0 class r\n\
            bank F at 0x100 stride 8 count 8 { reg X : u64 @0x0 class rw }\n\
            bank G at 0x120 stride 8 count 8 { reg Y : u64 @0x0 class rw }"),
        "N049",
    );

    // **The counter-direction, and the last case is the one that keeps the rule honest:** a
    // COMPUTED base stays silent, exactly as `N009` promises for itself. `02-geraet.gab`
    // writes `bank FRR at CAP.FRO * 16`.
    faellt_nicht(&d(
        "reg C : u64 @0xf8 class rw\nbank F at 0x100 stride 8 count 8 { reg X : u64 @0x0 class rw }",
    ));
    faellt_nicht(&d(
        "reg C : u64 @0 class r\n\
         bank F at 0x100 stride 8 count 4 { reg X : u64 @0x0 class rw }\n\
         bank G at 0x120 stride 8 count 4 { reg Y : u64 @0x0 class rw }",
    ));
    faellt_nicht(&d(
        "reg CAP : u64 @0x08 class r fields { FRO @[33:24], }\n\
         bank F at CAP.FRO * 16 stride 16 count 256 \
           { reg X : u64 @0x0 class rw reg Y : u64 @0x8 class rw }",
    ));
}

/// **`aligned(p, n)` reads `p`, and until 2026-09-01 no pass saw it.**
///
/// `wirkungen::liest_expr` and `geteilt::orte_in` are the same walker word for word: five
/// expression kinds enumerated and `_ => {}` for the rest. `ExprArt::Eingebaut` fell under the
/// catch-all, so the whole subtree vanished — places and all. The 2026-08-20 repair moved the
/// CALL readers onto `alle_ausdruecke` and left the PLACE readers hand-rolled.
#[test]
fn aligned_verbirgt_kein_lesen() {
    let quelle = |rumpf: &str| {
        format!(
            "module p {{\nstatic g : u32 in 0 .. 100 = 4;\n\
             impl fn b() -> u32 in 0 .. 1 effects {{ pure }} costs <= 3 ops {{ {rumpf} }}\n}}"
        )
    };
    // The plain comparison always fell; the wrapped one did not.
    faellt_mit(&quelle("if g == 4 { return 1; } return 0;"), "E010");
    faellt_mit(&quelle("if aligned(g, 4) { return 1; } return 0;"), "E010");

    // **The counter-direction is the decision this fix had to make and not guess.** `lenof`
    // and `sizeof` over a place take their value from the DECLARATION, not from the content —
    // the emitter says so itself (`C001`: *"the length would have to come from somewhere other
    // than the declaration"*). So a place under `lenof` is NOT a read, and a `pure` function
    // may carry one.
    faellt_nicht(
        "module p {\ntype Z = u32 in 0 .. 10;\ntable T count 8 { slot { a : Z, } }\n\
         impl fn f() -> u32 in 0 .. 64 effects { pure } costs <= 2 ops { return lenof(T.slots); }\n}",
    );
}

/// The twin, one pass further — and there it is a race.
#[test]
fn aligned_umgeht_die_sperre_nicht() {
    let quelle = |rumpf: &str| {
        format!(
            "module p {{\nstatic wert : u32 in 0 .. 100 = 4;\n\
             lock L protects {{ wert }} rank 0 held <= 400 ops;\n\
             impl fn b() -> u32 in 0 .. 1 effects {{ reads wert }} costs <= 3 ops {{ {rumpf} }}\n}}"
        )
    };
    faellt_mit(&quelle("if wert == 4 { return 1; } return 0;"), "H007");
    faellt_mit(&quelle("if aligned(wert, 4) { return 1; } return 0;"), "H007");
}

/// **`N050` -- the same audit method one day later, and one layer DOWN.**
///
/// `N047`-`N049` judge the layout. This one judges whether the layout survives the LOWERING:
/// every bank accessor is emitted as
///
/// ```c
/// return *(volatile uint64_t *)(d->basis + (base) + i * <stride>u + <off>u);
/// ```
///
/// with `uint32_t i` and an `unsigned int` stride, so the product is formed in 32 bits and
/// only THEN widened to the pointer. `clang-tidy` names the site
/// `bugprone-implicit-widening-of-multiplication-result` at every one of them.
///
/// The boundary is exact and both sides of it are driven here, because *a rule that only
/// ever fires proves nothing about where it stops*: `0xFFF * 0x100000` is `0xFFF00000` and
/// fits; one more cell does not.
#[test]
fn bankindex_jenseits_der_wortbreite_faellt() {
    let d = |bank: &str| {
        format!("module p {{ opaque type Pa = u64;\ndevice D(basis : Pa) at mmio {{\n{bank}\n}}\n}}")
    };
    // `(0x10000 - 1) * 0x100000` is `0xFFFFF00000` -- 36 bits into a 32-bit multiply.
    faellt_mit(&d("bank F at 0x0 stride 0x100000 count 0x10000 { reg X : u64 @0x0 class rw }"), "N050");
    // The stride alone is enough when the count is large.
    faellt_mit(&d("bank F at 0x0 stride 0x10000 count 0x10001 { reg X : u64 @0x0 class rw }"), "N050");
    // And the register's own offset counts -- it is the `+ offu` of the same expression.
    faellt_mit(
        &d("bank F at 0x0 stride 0x100000 count 0x1000 { reg X : u64 @0x100000 class rw }"),
        "N050",
    );

    // **The counter-direction, and the first case is the boundary itself:**
    // `0xFFF * 0x100000 == 0xFFF00000`, the largest product that still fits.
    faellt_nicht(&d("bank F at 0x0 stride 0x100000 count 0x1000 { reg X : u64 @0x0 class rw }"));
    // The corpus shape -- `02-geraet.gab` writes `stride 16 count 256`.
    faellt_nicht(&d(
        "bank F at 0x100 stride 16 count 256 { reg X : u64 @0x0 class rw reg Y : u64 @0x8 class rw }",
    ));
    // A COMPUTED stride or count stays silent, the same limit `N048`/`N049` set themselves.
    faellt_nicht(&d(
        "reg CAP : u64 @0x08 class r fields { FRO @[33:24], }\n\
         bank F at 0x0 stride 16 count CAP.FRO { reg X : u64 @0x0 class rw }",
    ));
}

/// **`N051`, and the three cases below it are the reason the arithmetic changed too.**
///
/// Gabbro's literals are `u128`; the address arithmetic they lower into is 64-bit. Above
/// `u64::MAX` there is no C constant to write and no address to name -- and until 2026-09-02
/// nothing said so, while the rules that DO read those literals read them through
/// `*v as i128`.
///
/// The last two assertions are the ones that would have caught the old code: at `u128::MAX`
/// the lossy cast produced `-1`, and at `2^127-1` the following `+ width` overflowed `i128`
/// -- a panic in debug, a wrap in release. **They must now answer by NAME in both builds**,
/// and `instrumente/fuzze-grenzen.py` is what holds that over the whole grammar.
#[test]
fn registerlage_jenseits_der_zeigerbreite_faellt() {
    let d = |inhalt: &str| {
        format!("module p {{ opaque type Pa = u64;\ndevice D(basis : Pa) at mmio {{\n{inhalt}\n}}\n}}")
    };
    // 2^68, and a multiple of 8 -- so `N047` has nothing to say about it.
    faellt_mit(&d("reg X : u64 @0x100000000000000000 class rw"), "N051");
    faellt_mit(
        &d("bank F at 0x100000000000000000 stride 8 count 4 { reg X : u64 @0x0 class rw }"),
        "N051",
    );
    faellt_mit(
        &d("bank F at 0x0 stride 8 count 4 { reg X : u64 @0x100000000000000000 class rw }"),
        "N051",
    );
    // The two that used to end in a panic or a silent accept -- now a NAME, in both builds.
    faellt_mit(&d("reg X : u64 @340282366920938463463374607431768211455 class rw"), "N051");
    faellt_mit(&d("reg X : u64 @170141183460469231731687303715884105727 class rw"), "N051");

    // **The counter-direction, and the first case is the boundary itself:** `u64::MAX - 7`
    // is the last 8-aligned offset that still fits, and it must stay silent.
    faellt_nicht(&d("reg X : u64 @0xFFFFFFFFFFFFFFF8 class rw"));
    faellt_nicht(&d("reg X : u64 @0x1000 class rw"));
    // A COMPUTED base is not a literal and stays outside, as everywhere in this family.
    faellt_nicht(&d(
        "reg CAP : u64 @0x08 class r fields { FRO @[33:24], }\n\
         bank F at CAP.FRO * 16 stride 16 count 8 { reg X : u64 @0x0 class rw }",
    ));
}

// -- The index, and the bracket: two blind spots one level under the statement ------------
//
// **`ExprArt` holds 14 variants and the checker held 42 hand-rolled walkers over them**
// (measured 2026-09-02, `instrumente/miss-erschoepfung.py` beside it). The examination
// asked of each one what DROPPING a form costs, and the answer came back the same twice
// over: a walker that names `ExprArt::Ort` without entering its index, and a walker that
// asks what a value IS without stepping through `ExprArt::Klammer`.
//
// *The two shapes point in opposite directions* -- the first loses a guarantee, the second
// refused a correct program -- and each test below therefore carries both directions.

/// **A call in INDEX position took no lock order with it** (`beispiele/gift/590`).
///
/// `geteilt::rufprobe_expr` named `Ruf`, `Klammer`, `Unaer`, `Binaer` and closed with
/// `_ => {}`. `H012` (rank order across a call) and `H005` (exclusive demand under a shared
/// hold) are both decided there.
#[test]
fn ein_ruf_im_index_traegt_die_sperrordnung() {
    // `wirkungen` names the effects `f` declares -- the counter-direction below takes no
    // second lock, and declaring one it never takes would fall at `H011` for a reason that
    // has nothing to do with this test.
    let quelle = |wirkungen: &str, rumpf: &str| {
        format!(
            "module p {{\nstatic mut a : u32 = 0;\nstatic mut b : u32 = 0;\n\
             table T count 4 {{ slot {{ x : u32, }} }}\n\
             lock LA protects {{ a }} rank 5 held <= 100 ops;\n\
             lock LB protects {{ b }} rank 1 held <= 100 ops;\n\
             impl fn nimmt_lb() -> u32 in 0 .. 3 effects {{ writes b, locks LB }} \
             costs <= 8 ops {{ locks LB {{ b = 1; }} return 1; }}\n\
             impl fn frei() -> u32 in 0 .. 3 effects {{ pure }} costs <= 1 ops {{ return 1; }}\n\
             impl fn f(t : ptr<normal, r> T) -> u32 effects {{ {wirkungen} }} \
             costs <= 64 ops {{ locks LA {{ a = 1; {rumpf} }} return 0; }}\n}}"
        )
    };
    let nimmt_beide = "reads t, writes a, writes b, locks LA, locks LB";
    // Both forms of the same body -- the second is the first with the `let` folded in.
    faellt_mit(
        &quelle(nimmt_beide, "let i = nimmt_lb(); return t.slots[i].x;"),
        "H012",
    );
    faellt_mit(&quelle(nimmt_beide, "return t.slots[nimmt_lb()].x;"), "H012");
    // **The counter-direction: a callee that takes NO lock stays legal in an index.**
    // Without it the repair could be "refuse every call in an index" and nothing here would
    // say so.
    faellt_nicht(&quelle(
        "reads t, writes a, locks LA",
        "return t.slots[frei()].x;",
    ));
}

/// **A call in INDEX position carried no `Has(…)` demand with it** (`beispiele/gift/591`).
#[test]
fn ein_ruf_im_index_traegt_die_merkmalsforderung() {
    let quelle = |kopf: &str, rumpf: &str| {
        format!(
            "module p {{\ntable T count 4 {{ slot {{ x : u32, }} }}\n\
             impl fn zeit() -> u32 in 0 .. 3 {kopf} effects {{ pure }} costs <= 2 ops \
             {{ return 1; }}\n\
             impl fn f(t : ptr<normal, r> T) -> u32 effects {{ reads t }} costs <= 32 ops \
             {{ {rumpf} }}\n}}"
        )
    };
    faellt_mit(
        &quelle("requires Has(RDTSCP)", "let i = zeit(); return t.slots[i].x;"),
        "N016",
    );
    faellt_mit(
        &quelle("requires Has(RDTSCP)", "return t.slots[zeit()].x;"),
        "N016",
    );
    // The counter-direction: without the demand the same call in the same place is clean.
    faellt_nicht(&quelle("", "return t.slots[zeit()].x;"));
}

/// **A qualified call in INDEX position crossed the module boundary in silence**
/// (`beispiele/gift/592`).
#[test]
fn ein_qualifizierter_ruf_im_index_trifft_die_modulgrenze() {
    let quelle = |sichtbar: &str, rumpf: &str| {
        format!(
            "module w {{\nmodule a {{\n\
             {sichtbar} fn heimlich() -> u32 in 0 .. 3 effects {{ pure }} costs <= 1 ops \
             {{ return 1; }}\n}}\n\
             module b {{\ntable T count 4 {{ slot {{ x : u32, }} }}\n\
             impl fn f(t : ptr<normal, r> T) -> u32 effects {{ reads t }} costs <= 32 ops \
             {{ {rumpf} }}\n}}\n}}"
        )
    };
    faellt_mit(
        &quelle("impl", "let i = w::a::heimlich(); return t.slots[i].x;"),
        "N025",
    );
    faellt_mit(&quelle("impl", "return t.slots[w::a::heimlich()].x;"), "N025");
    // The counter-direction: with `pub` the very same call is the normal case.
    faellt_nicht(&quelle("pub impl", "return t.slots[w::a::heimlich()].x;"));
}

/// **A hundred operations in index position cost two** (`beispiele/gift/593`, `594`).
///
/// `kosten::ausdruck` is EXHAUSTIVE over `ExprArt` -- all fourteen arms, compiler-forced --
/// and it priced a place as `1 + <number of index suffixes>`. *Exhaustiveness over the
/// enumeration is not descent into the node.*
#[test]
fn ein_ruf_im_index_kostet_was_er_kostet() {
    let quelle = |zusage: &str, rumpf: &str| {
        format!(
            "module p {{\ntable T count 4 {{ slot {{ x : u32, }} }}\n\
             impl fn teuer() -> u32 in 0 .. 3 effects {{ pure }} costs <= 100 ops \
             {{ return 1; }}\n\
             impl fn f(t : ptr<normal, r> T, i : u32 in 0 .. 3) -> u32 \
             effects {{ reads t }} costs <= {zusage} ops {{ {rumpf} }}\n}}"
        )
    };
    faellt_mit(&quelle("3", "let k = teuer(); return t.slots[k].x;"), "K001");
    faellt_mit(&quelle("3", "return t.slots[teuer()].x;"), "K001");
    faellt_mit(
        &quelle("3", "if aligned(teuer(), 4) { return 1; } return 0;"),
        "K001",
    );
    faellt_nicht(&quelle("120", "return t.slots[teuer()].x;"));

    // **The counter-direction is a NUMBER here, not a code.** A repair that raised every
    // place by one would pass every assertion above and quietly refuse working programs.
    // `t.slots[i].x` cost 2 before this change and costs 2 after it: the flat `1` per index
    // suffix WAS the cost of the commonest index, and `ausdruck` now returns it for a bare
    // name of its own accord.
    faellt_nicht(&quelle("2", "return t.slots[i].x;"));
    faellt_mit(&quelle("1", "return t.slots[i].x;"), "K001");
    // And a CONSTANT index costs nothing -- which is what the first line of `ausdruck`
    // already says about every constant. *This one number did move, downwards, on purpose.*
    faellt_nicht(&quelle("1", "return t.slots[1].x;"));
}

/// **`match (a)` named no variants at all** (`beispiele/gift/595`).
///
/// The subject was read with a bare `if let ExprArt::Ort(…)`, so one pair of brackets took
/// the whole `D005` check away -- the rule by which the language forbids its users the
/// catch-all it has forbidden itself (W15).
#[test]
fn eine_klammer_nimmt_dem_match_seine_erschoepfung_nicht() {
    let quelle = |gegenstand: &str, zweige: &str| {
        format!(
            "module p {{\ntype Pa = u64;\n\
             tagged type Art = {{ Speicher(Pa), Endpunkt(u32), Leer }};\n\
             static mut z : u32 = 0;\n\
             impl fn f(a : Art) effects {{ writes z }} costs <= 8 ops \
             {{ match {gegenstand} {{ {zweige} }} }}\n}}"
        )
    };
    let unvollstaendig = "Speicher(p) => { z = 1; } Endpunkt(e) => { z = 2; }";
    let vollstaendig = "Speicher(p) => { z = 1; } Endpunkt(e) => { z = 2; } Leer => { z = 3; }";
    faellt_mit(&quelle("a", unvollstaendig), "D005");
    faellt_mit(&quelle("(a)", unvollstaendig), "D005");
    // The counter-direction: brackets around a COMPLETE `match` are still just brackets.
    faellt_nicht(&quelle("a", vollstaendig));
    faellt_nicht(&quelle("(a)", vollstaendig));
}

/// **A phase step in brackets was invisible** (`beispiele/gift/596`, `597`).
///
/// `gift/258` closed the `return` form on 2026-08-24 with the sentence *"two bodies of the
/// same meaning, one caught and one not -- purely by where the call sits."* It is now:
/// purely by whether a bracket stands around it.
#[test]
fn eine_klammer_verbirgt_keinen_phasenschritt() {
    let quelle = |zusage: &str, rumpf: &str| {
        format!(
            "module p {{\nlinear ghost type BootPhase order {{ roh, mmu, caps, bereit }};\n\
             static mut welt : u32 = 0;\n\
             extern fn schritt(p : BootPhase) -> BootPhase advances roh -> mmu \
             effects {{ consumes p, writes welt }} costs <= 8 ops;\n\
             impl fn f(p : BootPhase) -> BootPhase advances roh -> {zusage} \
             effects {{ consumes p, writes welt }} costs <= 16 ops {{ {rumpf} }}\n}}"
        )
    };
    // The lie, in all four shapes it can take.
    faellt_mit(&quelle("bereit", "return schritt(p);"), "O004");
    faellt_mit(&quelle("bereit", "return (schritt(p));"), "O004");
    faellt_mit(&quelle("bereit", "let q = schritt(p); return q;"), "O004");
    faellt_mit(&quelle("bereit", "let q = (schritt(p)); return q;"), "O004");
    // **The counter-direction: the TRUTH in brackets is still the truth.** Without it the
    // repair could be "a bracketed call reaches no stage at all", which would refuse every
    // honest body written this way.
    faellt_nicht(&quelle("mmu", "return (schritt(p));"));
    faellt_nicht(&quelle("mmu", "let q = (schritt(p)); return q;"));
}

/// **A bracket made a returned linear value open again** (measured 2026-09-02).
///
/// `m2::gehe` books a `return` of a place as "handed on, not open" with a bare
/// `if let ExprArt::Ort(…)`. `return p;` passed; `return (p);` fell at `L107` -- *`p` is
/// created here and consumed on no path.* **The refusal direction of the same defect**, and
/// the more embarrassing of the two: a correct program, refused for its punctuation.
#[test]
fn eine_klammer_macht_keinen_linearen_wert_offen() {
    let quelle = |rumpf: &str| {
        format!(
            "module p {{\nlinear type Parked;\n\
             extern fn parken() -> Parked effects {{ pure }} costs <= 2 ops;\n\
             impl fn weiter() -> Parked effects {{ pure }} costs <= 32 ops {{ {rumpf} }}\n}}"
        )
    };
    faellt_nicht(&quelle("let p = parken(); return p;"));
    faellt_nicht(&quelle("let p = parken(); return (p);"));
    // The counter-direction, and here it is the one that carries the claim: the real leak
    // must still fall, or the repair is just a silenced pass.
    faellt_mit(
        "module p {\nlinear type Parked;\n\
         extern fn parken() -> Parked effects { pure } costs <= 2 ops;\n\
         impl fn leck() effects { pure } costs <= 32 ops { let p = parken(); }\n}",
        "L107",
    );
}

/// **`&f` names a function, and one character took the name check away**
/// (`beispiele/gift/598`).
///
/// `ExprArt::FnWert` carries no sub-expression, so `m1::sammle_namen_pred` treated it like a
/// leaf and let it fall into the catch-all with the leaves. *It is a leaf that NAMES
/// something.*
#[test]
fn ein_fnwert_in_ensures_nennt_einen_namen() {
    let quelle = |zusage: &str| {
        format!(
            "module p {{\nstatic mut Z : u32 = 0;\n\
             type Probe = fn() -> bool effects {{ reads Z }} costs <= 4 ops;\n\
             impl fn hart_bereit() -> bool effects {{ reads Z }} costs <= 3 ops \
             {{ return Z == 1; }}\n\
             impl fn baue() -> Probe ensures {zusage} effects {{ pure }} costs <= 2 ops \
             {{ return &hart_bereit; }}\n}}"
        )
    };
    // The bare name always fell; the one behind an `&` did not.
    faellt_mit(&quelle("result == tippfehler"), "M109");
    faellt_mit(&quelle("result == &tippfehler"), "M109");
    // **The counter-direction, and it is the decision this repair had to make and not
    // guess.** `&hart_bereit` resolves among FUNCTIONS, not among globals -- looking the two
    // up in one table would have refused every honest producer in the corpus.
    faellt_nicht(&quelle("result == &hart_bereit"));
}

/// **A carrier named only inside `aligned(...)` counted for nothing** (measured 2026-09-02).
///
/// `gruppe::expr_namen` collects the carriers a connecting invariant names, and `U007`
/// refuses the group when it names fewer than two. The walker dropped `ExprArt::Eingebaut`
/// under the catch-all, so a second carrier mentioned only inside `aligned(...)` was invisible
/// -- and a VALID group was refused. This is the over-refusal direction of the bracket/index
/// family: fewer names means MORE `U007`, so no single-carrier invariant slips through.
#[test]
fn ein_traeger_in_aligned_verbindet_die_gruppe() {
    let quelle = |inv: &str| {
        format!(
            "module p {{\ntable A count 64 {{ slot {{ wartet : u32, }} }}\n\
             table B count 256 {{ slot {{ gruende : u32, }} }}\n\
             lock LA protects {{ A }} rank 1 held <= 40 ops;\n\
             lock LB protects {{ B }} rank 2 held <= 40 ops;\n\
             group G over {{ A, B }} {{\n\
             invariant conn cost O(n) runs offline :\n\
             forall e in slots of A : {inv};\n}}\n}}"
        )
    };
    // Both carriers named, but the second only inside `aligned` -- a valid connecting
    // invariant, and it must NOT fall.
    faellt_nicht(&quelle("aligned(B.slots[A.slots[e].wartet].gruende, 4)"));
    // **The counter-direction, and it carries the claim:** an invariant that names only ONE
    // carrier -- even through `aligned` -- must still fall, or the fix has blinded `U007`.
    faellt_mit(&quelle("aligned(A.slots[e].wartet, 4)"), "U007");
}

/// **`M139` -- a literal so wide that the TYPE falls away, and every rule with it.**
///
/// `IntBereich` is `i128`; Gabbro's literals are `u128`. Until 2026-09-02 the values in
/// between answered `Typ::Unbekannt`, and *`Unbekannt` is not a refusal -- it is an
/// acquittal that reads like caution.* Each rule below asks for the type first and had
/// nothing to ask.
///
/// **The first two assertions carry the claim, and they are neighbours**: `i128::MAX` fell
/// with `M103` before this rule existed and must keep doing so; `i128::MAX + 1` was
/// accepted, and emitted as an out-of-bounds C subscript over `T_slot slots[8];`.
///
/// Found by `instrumente/fuzze-grenzen.py`; the poison probe is
/// `beispiele/gift/601-an-index-too-wide-to-have-a-type.gab`.
#[test]
fn ein_literal_breiter_als_i128_faellt() {
    let index = |wert: &str| {
        format!(
            "module p {{\ntable T count 8 {{ slot {{ a : u32, }} }}\n\
             impl fn g() -> u32\n    effects {{ reads T.slots }}\n    costs   <= 4 ops\n{{\n\
             return T.slots[{wert}].a;\n}}\n}}"
        )
    };
    // The boundary, from both sides. `i128::MAX` keeps its type and keeps falling at the
    // bound; one above it has no type at all and falls at `M139`.
    faellt_mit(&index("170141183460469231731687303715884105727"), "M103");
    faellt_mit(&index("170141183460469231731687303715884105728"), "M139");
    faellt_mit(&index("340282366920938463463374607431768211455"), "M139");

    // The same silence, in the three other places a literal is read. Each of these was
    // `0 errors` on 2026-09-02.
    let k = |wert: &str| format!("module p {{ const K : u64 = {wert}; }}");
    faellt_mit(&k("170141183460469231731687303715884105728"), "M139");
    faellt_mit(&k("340282366920938463463374607431768211455"), "M139");
    // `2^127 - 1` still has a type, so the WIDTH rule is the one that speaks -- and it must
    // keep speaking, or `M139` has swallowed a case that was already covered.
    faellt_mit(&k("170141183460469231731687303715884105727"), "M101");

    faellt_mit(
        &format!("module p {{ static mut x : u64 = {}; }}", 1u128 << 127),
        "M139",
    );

    // **The counter-direction.** Everything at or below `i128::MAX` keeps its type, and the
    // ordinary values keep going through -- a rule that refuses one literal too many turns
    // a language into a smaller one.
    faellt_nicht(&index("0"));
    faellt_nicht(&index("7"));
    faellt_nicht("module p { const K : u64 = 18446744073709551615; }");
    faellt_nicht("module p { const K : u64 = 0xFFFF_FFFF_FFFF_FFFF; }");
}

/// **The `when` of a compare-exchange RUNS, and no reader of a statement saw it**
/// (`beispiele/gift/636`, measured 2026-09-02).
///
/// `lib.rs::eigene_praedikate` answered `Vec::new()` for every `StmtArt::Exchange`, so the
/// effect hull, the cost of a call and the phase step all stopped at the statement -- while
/// the emitter writes that same predicate into C:
///
/// ```text
/// uint32_t _cx1 = (uint32_t)(schreibt());
/// genommen = atomic_compare_exchange_strong_explicit(&AT, &_cx1, …);
/// ```
///
/// *Word for word the `retry … until` finding of 2026-08-19, one construct further.* It was
/// the last EXECUTABLE predicate position with no reader: the emitter refuses every `when`
/// that is not `old(X) == <expr>` (`C001`), so the surface is one evaluated expression.
#[test]
fn das_when_eines_tauschs_traegt_die_wirkung() {
    let quelle = |wirkungen: &str, bedingung: &str| {
        format!(
            "module p {{\nstatic mut G : u32 = 0;\natomic AT : u32 release;\n\
             impl fn schreibt() -> u32 effects {{ writes G }} costs <= 2 ops \
             {{ G = 1; return 1; }}\n\
             impl fn teuer() -> u32 effects {{ pure }} costs <= 900 ops {{ return 1; }}\n\
             impl fn frei() -> u32 effects {{ pure }} costs <= 1 ops {{ return 0; }}\n\
             impl fn nimmt() -> bool effects {{ {wirkungen} }} costs <= 8 ops {{\n\
             let genommen = AT exchange 1 when old(AT) == {bedingung} returns erfolg \
             publishes nothing;\nreturn genommen;\n}}\n}}"
        )
    };
    // The effect hull: the callee writes `G`, and the caller's frame does not name it.
    faellt_mit(&quelle("writes AT, publishes AT", "schreibt()"), "E008");
    // The cost of that same call -- 900 ops behind an envelope of 8.
    faellt_mit(&quelle("writes AT, publishes AT", "teuer()"), "K001");

    // **The counter-direction, and it is the whole reason this arm is narrow.** A
    // compare-exchange whose expected value is an ordinary expression must stay silent --
    // the literal form the corpus writes (`beispiele/35-tausch.gab`), and a call that keeps
    // its promise.
    faellt_nicht(&quelle("writes AT, publishes AT", "0"));
    faellt_nicht(&quelle("writes AT, publishes AT", "frei()"));
    // And a DECLARED hull is enough: the rule asks for the frame, not for the absence of
    // calls. Without this line the repair could be "refuse every call in a `when`".
    faellt_nicht(&quelle("writes AT, writes G, publishes AT", "schreibt()"));
}

/// **`M140` -- the index bound in a PREDICATE** (`beispiele/gift/637`, measured 2026-09-02).
///
/// `requires T.slots[9].x == 0` on a `table T count 8` gave `0 errors`, and `gabbro lean`
/// wrote it into `<fn>_pre` -- *"what the caller grants"*, an ASSUMPTION over a cell no
/// program can address. The counter-direction is the load-bearing half: **a predicate says
/// things a body cannot**, and every one of those forms must stay silent.
#[test]
fn ein_literalindex_im_praedikat_faellt() {
    let tabelle = "table T count 8 { slot { x : u32, } }\n";
    let fnform = |klausel: &str| {
        format!(
            "module p {{\n{tabelle}\
             impl fn f() -> bool {klausel} effects {{ reads T, reads T.slots }} \
             costs <= 8 ops {{ return true; }}\n}}"
        )
    };
    // The four fn-level positions, and the same literal in each.
    faellt_mit(&fnform("requires T.slots[9].x == 0"), "M140");
    faellt_mit(
        &fnform("ensures result == true && (T.slots[9].x == 0)"),
        "M140",
    );
    faellt_mit(
        &format!("module p {{\n{tabelle}spec fn g() -> bool = T.slots[9].x == 0;\n}}"),
        "M140",
    );
    // A table invariant -- and it is the one position where the SAME statement with a
    // quantifier variable is the ordinary corpus form, tested below.
    faellt_mit(
        &format!(
            "module p {{\ntable U count 8 {{ slot {{ y : u32, }}\n\
             invariant i cost O(1) runs offline : U.slots[9].y == 0; }}\n}}"
        ),
        "M140",
    );
    // A loop invariant and an `until`, inside a body -- the clause order is the grammar's.
    let schleife = |bis: &str, inv: &str| {
        format!(
            "module p {{\n{tabelle}extern fn zuviel() -> never effects {{ diverges }};\n\
             impl fn f() -> u32 effects {{ reads T, reads T.slots }} costs <= 200 ops {{\n\
             retry until {bis} bounded 8 ops on_exceeded zuviel {inv} \
             {{ let a : u32 = 1; }}\n\
             return 0;\n}}\n}}"
        )
    };
    faellt_mit(&schleife("T.slots[9].x == 0", ""), "M140");
    faellt_mit(&schleife("true", "invariant T.slots[9].x == 0"), "M140");

    // **The counter-direction, and it carries the claim.** A predicate says things a body
    // cannot, and a rule that started refusing those would break correct programs.
    //
    // (1) an index INSIDE the declared length;
    faellt_nicht(&fnform("requires T.slots[7].x == 0"));
    // (2) a QUANTIFIER VARIABLE -- the form the corpus writes at every table invariant;
    faellt_nicht(&format!(
        "module p {{\ntable U count 8 {{ slot {{ y : u32, }}\n\
         invariant i cost O(1) runs offline : forall s in slots of Self : \
         Self.slots[s].y == 0; }}\n}}"
    ));
    // (3) `old(…)` and `result`, which no body may write;
    faellt_nicht(&format!(
        "module p {{\n{tabelle}static mut g : u32 = 0;\n\
         impl fn f() -> u32 ensures result == old(g) && T.slots[7].x == 0 \
         effects {{ reads T, reads T.slots, writes g }} costs <= 8 ops \
         {{ g = 1; return 1; }}\n}}"
    ));
    // (4) a COMPUTED index -- `W10`, a lower bound refuses nothing it cannot decide;
    faellt_nicht(&format!(
        "module p {{\n{tabelle}const K : u32 = 3;\n\
         impl fn f() -> bool requires T.slots[K].x == 0 \
         effects {{ reads T, reads T.slots }} costs <= 8 ops {{ return true; }}\n}}"
    ));
    // (5) and the whole clean corpus example that carries a `slots of Self` invariant.
    faellt_nicht(&format!(
        "module p {{\ntable U count 8 {{ slot {{ y : u32, }} }}\n\
         spec fn alle_null() -> bool = forall s in slots of U : U.slots[s].y == 0;\n}}"
    ));
}

/// **The grammar makes a `domain` at TWO productions, and the pass read one**
/// (`beispiele/gift/638`, measured 2026-09-02).
///
/// ```text
/// requires forall i in slots of GIBTSNICHT : i == i   ->  D017
/// requires i in slots of GIBTSNICHT                   ->  0 errors
/// ```
///
/// *Not a second rule and not a new code* -- the same question at the same nonterminal.
/// `quant` was walked and `member` was not.
#[test]
fn ein_member_traegt_dieselbe_domaenenfrage() {
    let quelle = |pred: &str| {
        format!(
            "module p {{\ntable T count 8 {{ slot {{ x : u32, }} }}\n\
             const K : u32 = 3;\n\
             impl fn f(i : u32 in 0 .. 7) -> bool requires {pred} \
             effects {{ reads T, reads T.slots }} costs <= 8 ops {{ return true; }}\n}}"
        )
    };
    // The base name (`D017`) and the KIND of the place (`D018`) -- both halves.
    faellt_mit(&quelle("i in slots of GIBTSNICHT"), "D017");
    faellt_mit(&quelle("i in slots of K"), "D018");
    // The control that made the hole visible: the SAME words under a quantifier always fell.
    faellt_mit(&quelle("forall q in slots of GIBTSNICHT : q == q"), "D017");

    // **The counter-direction.** A `member` over a place that does resolve, and is of the
    // kind the domain needs, stays silent -- in both forms.
    faellt_nicht(&quelle("i in slots of T"));
    faellt_nicht(&quelle("forall q in slots of T : T.slots[q].x == 0"));
}
