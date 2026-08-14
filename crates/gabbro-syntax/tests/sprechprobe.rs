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
