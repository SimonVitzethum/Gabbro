//! **Das Annahmenmanifest -- „bewiesen unter A1…An", maschinenlesbar.**
//!
//! `SYNTAX.md` §12: *„Die Annahmenmenge wird ins Erzeugnis emittiert („bewiesen unter A1…An"),
//! als **Menge von Namen mit Klasse**, nicht als Zahl -- eine Ratsche ueber einer Kardinalzahl
//! greift nicht gegen Austausch."*
//!
//! Deshalb traegt jede Zeile **Name und Klasse**, und die Zaehlung steht darunter statt darueber.
//! Wer eine Annahme austauscht, aendert eine Zeile; die Zahl allein haette sich nicht geruehrt.

use gabbro_syntax::ast::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Klasse {
    /// Eine Sonde ist benannt. Ob sie lief, sagt dieses Manifest nicht -- das sagt der Lauf.
    Falsifizierbar { sonde: String },
    /// Nicht falsifizierbar, **mit Grund**.
    NichtFalsifizierbar { grund: String },
}

#[derive(Debug, Clone)]
pub struct Eintrag {
    pub name: String,
    /// `assume` oder `axiom`.
    pub art: &'static str,
    pub klasse: Klasse,
    /// Bei `assume` der erklaerende Satz, bei `axiom` die Wirkungen.
    pub aussage: String,
}

/// **«F»: die zwei Annahmen, die eine Gleitkommaeinheit MITBRINGT.**
///
/// Sie standen bis 2026-08-18 im erzeugten Kopf und im Zeugnistext -- und **in keiner
/// `assume`-Deklaration**, also in keinem Manifest und mit keiner Sonde. *Genau die Klasse,
/// gegen die `S003` und `N004` stehen: ein Name, den niemand erklaert hat.*
///
/// Sie werden ERZEUGT statt verlangt, aus demselben Grund, aus dem `accumulates` sich
/// `gabbro_kern` selbst in die fremden Ruempfe schreibt: **es sind Maschinenfragen, keine
/// Programmfragen.** Jedes Gleitkommaprogramm haette dieselben zwei Zeilen schreiben muessen,
/// und eine Zeile, die jeder abschreibt, ist eine Zeile, die niemand liest.
fn gleitkommaannahmen(baum: &Programm, out: &mut Vec<Eintrag>) {
    fn im_typ(t: &TypExpr) -> bool {
        match t {
            TypExpr::Float(_) => true,
            TypExpr::Feld(a) => im_typ(&a.element),
            TypExpr::Zeiger(z) => im_typ(&z.ziel),
            TypExpr::Verbund(fs, _) => fs.iter().any(|f| im_typ(&f.typ.typ)),
            _ => false,
        }
    }
    let mut ja = false;
    crate::fuer_jedes_item(baum, &mut |i| match &i.art {
        ItemArt::Konst(k) => ja |= im_typ(&k.typ),
        ItemArt::Statisch(st) => ja |= im_typ(&st.typ),
        ItemArt::Typ(t) => {
            if let Some(r) = &t.rumpf {
                ja |= im_typ(r);
            }
        }
        ItemArt::Funktion(f) => {
            ja |= f.parameter.iter().any(|p| im_typ(&p.typ));
            ja |= f.ergebnis.as_ref().is_some_and(im_typ);
        }
        ItemArt::Accumulates(a) => ja |= im_typ(&a.typ),
        _ => {}
    });
    if !ja {
        return;
    }
    out.push(Eintrag {
        name: "gleitkomma_rundungsmodus_ist_rne".into(),
        art: "assume",
        klasse: Klasse::Falsifizierbar {
            sonde: "sonde_mxcsr_rne".into(),
        },
        aussage: "The rounding mode is round-to-nearest-even. It is GLOBAL state \
                  (MXCSR/FPCR) and therefore an implicit input of every operation -- the \
                  probe reads it and falls if it is a different one."
            .into(),
    });
    out.push(Eintrag {
        name: "gleitkomma_x86_rechnet_mit_sse2".into(),
        art: "assume",
        klasse: Klasse::Falsifizierbar {
            sonde: "sonde_keine_ueberbreite".into(),
        },
        aussage: "On x86 the generated code computes with SSE2 and not on the x87 stack. \
                  The x87 computes with 80 bits and ROUNDS TWICE; every bound the checker \
                  computed then fails to hold. The probe evaluates an expression whose \
                  result differs between 64 and 80 bits."
            .into(),
    });
}

/// **Der SPERRABDRUCK -- die Praemisse, die `Gruppe_Erhaltung.thy` unterstellt hat.**
///
/// `beweise/Gruppe_Erhaltung.thy`, Locale `zug`, nimmt `voll i` als *„der Abdruck ist
/// gehalten"* und schliesst daraus, dass niemand hinsieht. **Dass ein gehaltener Abdruck
/// einen fremden Kern wirklich fernhaelt, ist eine Aussage ueber das SPEICHERMODELL** und
/// faellt nicht in diesen Satz -- `gabbro schablonen` fuehrte sie bis zum 2026-08-21 als
/// haengende Praemisse von `gruppe.ops`, mit der Adresse *„braeuchte: die AXIOMSCHICHT"*.
///
/// *Vorher war die Praemisse unsichtbar; jetzt steht sie in der Zahl.*
///
/// Sie wird **ERZEUGT statt verlangt**, aus demselben Grund wie die zwei
/// Gleitkommaannahmen darueber: es ist eine Maschinenfrage, keine Programmfrage. Jedes
/// Programm mit einer Verbindungs-Invariante haette dieselbe Zeile schreiben muessen, und
/// eine Zeile, die jeder abschreibt, ist eine Zeile, die niemand liest.
///
/// **Nicht falsifizierbar, und zwar aus dem Grund von `release_stellt_sichtbarkeit_her`:**
/// eine Sonde, die den Abdruck haelt und nachsieht, ob jemand hingesehen hat, zeigt nur,
/// dass diesmal niemand hingesehen hat. *Ein Speichermodell ist durch Ausfuehrung nicht
/// widerlegbar.*
fn sperrabdruckannahme(baum: &Programm, out: &mut Vec<Eintrag>) {
    let mut ja = false;
    crate::fuer_jedes_item(baum, &mut |i| {
        if matches!(&i.art, ItemArt::Gruppe(_)) {
            ja = true;
        }
    });
    if !ja {
        return;
    }
    out.push(Eintrag {
        name: "sperrabdruck_haelt_fremde_kerne_fern".into(),
        art: "assume",
        klasse: Klasse::NichtFalsifizierbar {
            grund: "a memory model cannot be refuted by execution -- a probe that holds the \
                    footprint and looks shows only that this time nobody looked"
                .into(),
        },
        aussage: "As long as the mover holds the WHOLE lock footprint of a group, no \
                  foreign core can look at the carriers together. `Gruppe_Erhaltung.thy` \
                  assumes exactly that in the locale `zug` as `abdruck_innen` and proves on \
                  top of it that the intermediate state has no consequence -- the assumption \
                  itself does not fall into the theorem but here."
            .into(),
    });
}

/// **Layer S3 of the boot theorem -- the half that LEAVES the checker.**
///
/// `retires t from boot falsifier <probe>` carries two statements, and only one of them is a
/// statement about the program:
///
/// | | who carries it |
/// |---|---|
/// | after the event the mapping is no longer in the table | **`O012`** -- a `walk` fact over `mappings of`, formulable and demanded |
/// | an address without a mapping is no longer reachable | **here** -- the MMU, the TLB, speculation |
///
/// *No pass sees the second one, not today and not with any proof project.* It is exactly the
/// case the axiom layer exists for, and it comes OUT OF THE CLAUSE instead of out of a second
/// `assume` line beside it: an assumption one can forget to write is an assumption that gets
/// forgotten. **Hence generated, like the two floating-point assumptions and the lock
/// imprint -- and for the same reason: it is a machine question.**
///
/// The probe stands in the clause and not here, and that is the difference to the three
/// generated assumptions above: *which address must fault after the boot end is known to the
/// program and not to the compiler.*
fn stilllegungsannahmen(baum: &Programm, out: &mut Vec<Eintrag>) {
    crate::fuer_jedes_item(baum, &mut |i| {
        let ItemArt::Funktion(f) = &i.art else { return };
        let Some(st) = &f.retires else { return };
        let raum = match &st.raum {
            Raum::Normal => "normal",
            Raum::Mmio => "mmio",
            Raum::Dma => "dma",
            Raum::Code => "code",
            Raum::Boot => "boot",
            Raum::Port => "port",
            Raum::Benannt(n) => n.text.as_str(),
        };
        out.push(Eintrag {
            name: format!("stilllegung_{}_ist_unerreichbar", f.name.text),
            art: "assume",
            klasse: klasse(&st.klasse),
            aussage: format!(
                "After `{}` no address of the space `{raum}` is reachable any more. That \
                 the MAPPING disappears is the postcondition over `mappings of` and is \
                 demanded (`O012`); that an address without a mapping is no longer reachable \
                 is a statement about MMU and TLB and falls under no pass. After the event \
                 the probe accesses an address of the space and must fault.",
                f.name.text
            ),
        });
    });
}

/// Sammelt die Annahmenmenge eines Baums.
pub fn sammle(baum: &Programm) -> Vec<Eintrag> {
    let mut out = Vec::new();
    gleitkommaannahmen(baum, &mut out);
    sperrabdruckannahme(baum, &mut out);
    stilllegungsannahmen(baum, &mut out);
    sammle_items(&baum.items, &mut out);
    out.sort_by(|a, b| a.name.cmp(&b.name));
    out
}

fn sammle_items(items: &[Item], out: &mut Vec<Eintrag>) {
    for i in items {
        match &i.art {
            ItemArt::Modul(m) => sammle_items(&m.items, out),
            ItemArt::Assume(a) => out.push(Eintrag {
                name: a.name.text.clone(),
                art: "assume",
                klasse: klasse(&a.klasse),
                aussage: a.text.text.clone(),
            }),
            ItemArt::Axiom(a) => out.push(Eintrag {
                name: a.name.text.clone(),
                art: "axiom",
                klasse: klasse(&a.klasse),
                aussage: a
                    .effects
                    .liste
                    .iter()
                    .map(|e| e.art.text())
                    .collect::<Vec<_>>()
                    .join(", "),
            }),
            _ => {}
        }
    }
}

/// **Die Annahmenmenge ist eine MENGE, und bis zum 2026-08-17 war sie eine Liste.**
///
/// `SYNTAX.md` §12 verlangt sie als *„Menge von Namen mit Klasse"*. Ueber mehrere Dateien
/// hinweg haengte der Aufruf die Ergebnisse aber schlicht aneinander: `beispiele/06` und
/// `beispiele/07` erklaeren beide `axiom write_cr3` mit derselben Sonde und denselben
/// Wirkungen (nur der Parametername unterscheidet sich, und den fuehrt das Manifest nicht).
/// **Also stand `write_cr3` zweimal drin, und die Zeile darunter meldete 15 statt 14.**
///
/// > *Eine Zusage „bewiesen unter A1…An" mit einem doppelten A behauptet eine groessere
/// > Annahmenmenge, als sie hat.*
///
/// **Der gefaehrlichere Fall ist der andere, und gegen ihn ist diese Funktion eigentlich
/// gebaut:** zwei Dateien erklaeren denselben NAMEN mit verschiedenem Inhalt — andere Sonde,
/// andere Wirkungen, oder einmal falsifizierbar und einmal nicht. Das ist ein **Widerspruch
/// in der Annahmenmenge**, und die alte Fassung haette beide Zeilen nebeneinander gedruckt,
/// ohne ein Wort. Hier faellt er als `Vec<String>` heraus, und der Rufer entscheidet.
pub fn vereinige(alle: Vec<Eintrag>) -> (Vec<Eintrag>, Vec<String>) {
    let mut aus: Vec<Eintrag> = Vec::new();
    let mut streit = Vec::new();
    for e in alle {
        match aus.iter().find(|a| a.name == e.name) {
            None => aus.push(e),
            Some(vorher) => {
                if vorher.art != e.art || vorher.klasse != e.klasse || vorher.aussage != e.aussage {
                    streit.push(format!(
                        "`{}` is declared twice with different content -- \
                         a contradiction in the assumption set, not a duplicate",
                        e.name
                    ));
                }
            }
        }
    }
    aus.sort_by(|a, b| a.name.cmp(&b.name));
    (aus, streit)
}

fn klasse(k: &AnnahmeKlasse) -> Klasse {
    match k {
        AnnahmeKlasse::Falsifizierbar(i) => Klasse::Falsifizierbar {
            sonde: i.text.clone(),
        },
        AnnahmeKlasse::NichtFalsifizierbar(t) => Klasse::NichtFalsifizierbar {
            grund: t.text.clone(),
        },
    }
}

/// **The probes that stand as a PROGRAM** -- kept against `sonden/sonde_*.c`, and
/// `instrumente/pruefe-sonden.sh` runs exactly these.
///
/// *This list is the only route by which a probe name reaches the manifest.*
pub const SONDEN_MIT_PROGRAMM: &[&str] = &["sonde_boot_unerreichbar", "sonde_release_sichtbarkeit"];

/// **A name without a program is STRUCK -- 2026-08-30.**
///
/// `messung/AXIOMSCHICHT.md` measured it on 2026-08-21 and wrote it out: 27 assumptions named
/// a probe, and NONE of them existed as a program. The runner calls it **the indictment**.
///
/// > A `falsifier sonde_xyz` whose probe exists nowhere is an **assurance about the ABSENCE
/// > of a refutation** -- the same class as R15 and W10.
///
/// **"not run" is a translation error, never an intermediate state.** The name read as
/// coverage inside the manifest and was none -- and the manifest is the artefact by which
/// Gabbro carries its promise OUTWARD. So the name falls, and the assurance falls with it:
/// the class then reads `ungedeckt`, and the probe column carries `--`.
///
/// *Whoever wants to keep a name writes the probe.* Entering it is one line in
/// [`SONDEN_MIT_PROGRAMM`], and from then on the name stands again.
///
/// **And the count stays.** The closing line says how many names were struck -- otherwise a
/// list that shrank would be indistinguishable from one that was never larger. Same logic as
/// section E of the certificate: what is not covered is **carried by name** rather than
/// omitted.
pub fn gedeckt(sonde: &str) -> bool {
    SONDEN_MIT_PROGRAMM.contains(&sonde)
}

/// Zeilenformat, stabil und ohne Werkzeug lesbar:
/// `A<n>\t<name>\t<art>\t<klasse>\t<sonde|grund>\t<aussage>`
pub fn zeige(eintraege: &[Eintrag]) -> String {
    let mut out = String::new();
    let mut gestrichen = 0usize;
    out.push_str("-- The assumption set. The promise reads: proved under A1…An.\n");
    out.push_str("-- Nr\tName\tArt\tKlasse\tSonde/Grund\tAussage\n");
    for (n, e) in eintraege.iter().enumerate() {
        let (kl, wie) = match &e.klasse {
            // **The name stands only where the probe stands as a program** -- see [`gedeckt`].
            // Otherwise it is struck, and the closing line says so.
            Klasse::Falsifizierbar { sonde } if gedeckt(sonde) => {
                ("falsifizierbar", sonde.as_str())
            }
            Klasse::Falsifizierbar { .. } => {
                gestrichen += 1;
                ("ungedeckt", "--")
            }
            Klasse::NichtFalsifizierbar { grund } => ("nicht-falsifizierbar", grund.as_str()),
        };
        out.push_str(&format!(
            "A{}\t{}\t{}\t{}\t{}\t{}\n",
            n + 1,
            e.name,
            e.art,
            kl,
            wie,
            e.aussage
        ));
    }
    out.push_str(&format!("-- {} Annahmen\n", eintraege.len()));
    // **The line that stays.** Without it a shrunken list would be indistinguishable from one
    // that was never larger -- and the striking itself would hide the very gap it names.
    if gestrichen > 0 {
        out.push_str(&format!(
            "-- {} probe name(s) STRUCK: no program stands for them. A name without a \
             program asserts the absence of a refutation -- the assumption holds, its \
             falsifiability does not.\n",
            gestrichen
        ));
    }
    out
}
