//! **Das Annahmenmanifest -- bis zum 2026-08-17 ohne eine einzige Probe.**
//!
//! `schablonen.rs` nennt die Axiomschicht als das Beispiel einer Ratsche, die es schon gibt
//! (*„Die Axiomschicht hat ihre (`gabbro annahmen`, „bewiesen unter A1…An")"*). **Sie hatte
//! keinen Test und keine Mutation** -- also genau die Lage, die dort ueber die Schablonen
//! beklagt wird, eine Datei weiter.
//!
//! Und die erste Probe fand sofort etwas: `gabbro annahmen beispiele/*.gab` meldete
//! **15 Annahmen**, von denen zwei dieselbe waren.

use gabbro_check::manifest::{sammle, vereinige, Eintrag, Klasse};

fn baum(q: &str) -> gabbro_syntax::ast::Programm {
    gabbro_syntax::lies("probe.gab", q).0
}

#[test]
fn ein_axiom_und_ein_assume_kommen_mit_ihrer_klasse_an() {
    let q = "module t {
axiom write_cr3(p : u64) effects { writes tlb } falsifier sonde_cr3;
assume tlb_leer \"Ein Schreiben auf CR3 verwirft die nicht-globalen Eintraege.\"
    falsifier sonde_tlb;
assume wbinvd_wirkt \"Der Cache ist danach leer.\"
    unfalsifiable \"auf dieser Maschine nicht beobachtbar\";
}";
    let e = sammle(&baum(q));
    assert_eq!(e.len(), 3, "drei Annahmen: {e:?}");

    let cr3 = e.iter().find(|x| x.name == "write_cr3").expect("write_cr3");
    assert_eq!(cr3.art, "axiom");
    assert_eq!(cr3.aussage, "writes tlb", "bei einem Axiom ist die Aussage die Wirkungsliste");
    assert_eq!(
        cr3.klasse,
        Klasse::Falsifizierbar { sonde: "sonde_cr3".into() },
        "die Sonde gehoert ins Manifest -- ob sie lief, sagt der Lauf"
    );

    let wb = e.iter().find(|x| x.name == "wbinvd_wirkt").expect("wbinvd");
    assert!(
        matches!(&wb.klasse, Klasse::NichtFalsifizierbar { grund } if grund.contains("beobachtbar")),
        "**nicht-falsifizierbar nur MIT Grund** -- ohne ihn waere es eine Annahme ohne Rechenschaft: {:?}",
        wb.klasse
    );
}

#[test]
fn annahmen_in_verschachtelten_modulen_gehen_nicht_verloren() {
    let q = "module a { module b {
axiom tief() effects { writes x } falsifier s;
} }";
    assert_eq!(sammle(&baum(q)).len(), 1, "ein Modul im Modul versteckt keine Annahme");
}

// -- Die Menge ist eine MENGE ------------------------------------------------------------

fn e(name: &str, art: &'static str, sonde: &str, aussage: &str) -> Eintrag {
    Eintrag {
        name: name.into(),
        art,
        arch: None,
        klasse: Klasse::Falsifizierbar { sonde: sonde.into() },
        aussage: aussage.into(),
        voraussetzungen: 0,
        voraussetzung_text: None,
    }
}

#[test]
fn dieselbe_annahme_aus_zwei_dateien_zaehlt_einmal() {
    // **Der gefundene Fall, woertlich.** `beispiele/06` und `beispiele/07` erklaeren beide
    // `axiom write_cr3` mit derselben Sonde und denselben Wirkungen; nur der Parametername
    // unterscheidet sich, und den fuehrt das Manifest nicht. Die alte Fassung meldete
    // deshalb **15 Annahmen**, wo es 14 gibt.
    let (aus, streit) = vereinige(vec![
        e("write_cr3", "axiom", "sonde_cr3", "writes tlb, writes aktive_tabelle"),
        e("invlpg", "axiom", "sonde_invlpg", "writes tlb"),
        e("write_cr3", "axiom", "sonde_cr3", "writes tlb, writes aktive_tabelle"),
    ]);
    assert_eq!(aus.len(), 2, "zweimal dasselbe ist EINE Annahme: {aus:?}");
    assert!(streit.is_empty(), "gleicher Inhalt ist kein Streit: {streit:?}");
    assert_eq!(
        aus.iter().map(|x| x.name.as_str()).collect::<Vec<_>>(),
        vec!["invlpg", "write_cr3"],
        "und die Ausgabe bleibt sortiert"
    );
}

#[test]
fn derselbe_name_mit_anderem_inhalt_ist_ein_widerspruch() {
    // **Der eigentliche Grund fuer die Funktion.** Ein Duplikat ist eine falsche Zahl; ZWEI
    // verschiedene Erklaerungen desselben Namens sind ein Widerspruch in der Annahmenmenge --
    // und die Zusage lautet „bewiesen unter A1…An". Welches A gilt dann?
    let (_, streit) = vereinige(vec![
        e("write_cr3", "axiom", "sonde_cr3", "writes tlb"),
        e("write_cr3", "axiom", "sonde_cr3", "writes tlb, writes aktive_tabelle"),
    ]);
    assert_eq!(streit.len(), 1, "der Widerspruch muss beim Namen genannt werden: {streit:?}");
    assert!(streit[0].contains("write_cr3"));

    // Auch die KLASSE zaehlt: einmal falsifizierbar, einmal nicht, ist derselbe Fall.
    let mit_grund = Eintrag {
        name: "write_cr3".into(),
        art: "axiom",
        arch: None,
        klasse: Klasse::NichtFalsifizierbar { grund: "keine Sonde".into() },
        aussage: "writes tlb".into(),
        voraussetzungen: 0,
        voraussetzung_text: None,
    };
    let (_, streit) = vereinige(vec![e("write_cr3", "axiom", "sonde_cr3", "writes tlb"), mit_grund]);
    assert_eq!(
        streit.len(),
        1,
        "eine Annahme, die einmal falsifizierbar heisst und einmal nicht, ist ein Streit"
    );
}

/// **«B40»: the same name for two machines is NO contradiction** (2026-08-31).
///
/// `assume c11_release_acquire arch x86_64` and `… arch aarch64` say different things about
/// different processors, and an estate carrying both architectures needs both lines.
/// **Before `Eintrag::arch`, `vereinige` called that a contradiction** -- and the pattern
/// `SPRACHE.md` §6 writes out would have become unwritable the day `arch` became sayable.
///
/// *The other direction stands and is checked here too:* the same name with the SAME machine
/// and different content is still a dispute.
#[test]
fn zwei_maschinen_sind_zwei_annahmen() {
    let x86 = Eintrag {
        name: "c11_release_acquire".into(),
        art: "assume",
        arch: Some("x86_64".into()),
        klasse: Klasse::Falsifizierbar { sonde: "probe_mp_x86".into() },
        aussage: "TSO: mov genuegt".into(),
        voraussetzungen: 0,
        voraussetzung_text: None,
    };
    let arm = Eintrag {
        name: "c11_release_acquire".into(),
        art: "assume",
        arch: Some("aarch64".into()),
        klasse: Klasse::Falsifizierbar { sonde: "probe_mp_aarch64".into() },
        aussage: "stlr/ldar tragen release/acquire".into(),
        voraussetzungen: 0,
        voraussetzung_text: None,
    };
    let (menge, streit) = vereinige(vec![x86.clone(), arm]);
    assert!(streit.is_empty(), "zwei Maschinen sind kein Widerspruch: {streit:?}");
    assert_eq!(menge.len(), 2, "und beide gehoeren in die Annahmenmenge");

    // Same machine, different content -- the case the function was built against.
    let x86_anders = Eintrag { aussage: "etwas anderes".into(), ..x86.clone() };
    let (_, streit) = vereinige(vec![x86, x86_anders]);
    assert_eq!(streit.len(), 1, "gleiche Maschine, anderer Inhalt: weiterhin ein Streit");
}

#[test]
fn die_zaehlzeile_zaehlt_die_menge_und_nicht_die_liste() {
    let (aus, _) = vereinige(vec![
        e("a", "axiom", "s", "writes x"),
        e("a", "axiom", "s", "writes x"),
    ]);
    let text = gabbro_check::manifest::zeige(&aus);
    assert!(text.contains("-- 1 Annahmen"), "die Zahl unter der Tabelle:\n{text}");
    assert_eq!(
        text.lines().filter(|l| l.starts_with('A')).count(),
        1,
        "eine Zeile je Annahme:\n{text}"
    );
}

/// **The `requires` of an `axiom` reaches the manifest -- and until 2026-09-02 it did not.**
///
/// The promise this file carries reads *proved under A1…An*, and A1 was printed as
/// `rdtscp` where the program declares `rdtscp` UNDER `Has(RDTSCP)`. A reader who went and
/// checked A1 checked a stronger statement than the program made. **Same argument as
/// `Eintrag::arch` one field up:** a side condition is part of the identity.
#[test]
fn die_vorbedingung_eines_axioms_steht_im_manifest() {
    let q = "module t {
axiom rdtscp() -> u64 requires Has(RDTSCP) effects { reads uhr } falsifier sonde_rdtscp;
axiom wbinvd() effects { writes cache } falsifier sonde_wbinvd;
}";
    let e = gabbro_check::manifest::sammle_mit_quelle(&baum(q), q);
    let ts = e.iter().find(|x| x.name == "rdtscp").expect("rdtscp");
    assert_eq!(ts.voraussetzungen, 1, "eine Klausel: {ts:?}");
    assert_eq!(ts.voraussetzung_text.as_deref(), Some("Has(RDTSCP)"), "{ts:?}");

    // **The counter-direction, and it is the one that keeps the column honest:** an axiom
    // WITHOUT a precondition must not grow one, or every line would read as conditional.
    let wb = e.iter().find(|x| x.name == "wbinvd").expect("wbinvd");
    assert_eq!(wb.voraussetzungen, 0);
    assert_eq!(wb.voraussetzung_text, None);

    let text = gabbro_check::manifest::zeige(&e);
    assert!(text.contains("Has(RDTSCP)"), "und es steht in der Tabelle:\n{text}");
    assert!(text.contains("Voraussetzung"), "die Spalte ist ueberschrieben:\n{text}");

    // **Without the source the WORDING is missing and the CLAUSE is not.** `sammle` is used
    // where no source is at hand (the emitted header, the certificate), and a blank cell
    // there would read as "this axiom is unconditional".
    let ohne = sammle(&baum(q));
    let ts = ohne.iter().find(|x| x.name == "rdtscp").expect("rdtscp");
    assert_eq!(ts.voraussetzungen, 1, "die ZAHL ist eine Tatsache des Baums");
    assert_eq!(ts.voraussetzung_text, None, "der Wortlaut braucht die Quelle");
    assert!(
        gabbro_check::manifest::zeige(&ohne).contains("? (1)"),
        "und die Tabelle sagt, dass sie ihn nicht hat"
    );
}

/// **Two files, one axiom name, two different preconditions -- a contradiction.**
///
/// `vereinige` compared name, kind, class and statement. A precondition was none of those,
/// so `axiom rdtscp requires Has(RDTSCP)` in one file and a bare `axiom rdtscp` in another
/// merged into one entry -- *and the merged one was whichever came first.*
#[test]
fn zwei_vorbedingungen_unter_einem_namen_sind_ein_widerspruch() {
    let mit = Eintrag {
        voraussetzungen: 1,
        voraussetzung_text: Some("Has(RDTSCP)".into()),
        ..e("rdtscp", "axiom", "sonde", "reads uhr")
    };
    let ohne = e("rdtscp", "axiom", "sonde", "reads uhr");
    let (_, streit) = vereinige(vec![mit.clone(), ohne]);
    assert_eq!(streit.len(), 1, "bedingt und unbedingt sind zwei Annahmen: {streit:?}");
    assert!(streit[0].contains("rdtscp"));

    // Twice the SAME precondition stays one assumption -- the duplicate case is untouched.
    let (menge, streit) = vereinige(vec![mit.clone(), mit]);
    assert!(streit.is_empty(), "gleiche Vorbedingung ist kein Streit: {streit:?}");
    assert_eq!(menge.len(), 1);
}
