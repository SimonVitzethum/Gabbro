//! **Die K-Bedingung, mechanisch — und der Prüfer arbeitet damit für die Messung, die vor
//! ihm stehen sollte.**
//!
//! Das Messprotokoll für Messung 2 ([`MESSUNGEN.md`](MESSUNGEN.md)) sagt:
//!
//! > *„«Der Erzeuger zeigt es einmal» gilt nur, wenn **ALLE** Mutationen des Traegers erzeugte
//! > Operationen sind. Eine einzige Handmutation — ein `breaking`-Block, ein Schreibpfad
//! > ausserhalb der `ops`-Liste — und die Erhaltung ist **Menschenarbeit**, also A oder W.
//! > **Je Pflicht ist das eine mechanische Frage: sind alle Schreibstellen des Traegers
//! > erzeugt?**"*
//!
//! **Genau diese Frage beantwortet dieses Modul.** Damit wird der Übersetzer zum Messgerät
//! für die Zählung, die ihn eigentlich blockieren sollte — die einzige Bewegung, die die
//! Schere zwischen gebautem Prüfer und ungefahrener Messung von der anderen Seite schliesst.
//!
//! **Nebenertrag, den das Protokoll ausdrücklich nennt:** dieselbe Prüfung liefert die
//! **Liste der `breaking`-Stellen** — Posten L3 der Restliste.
//!
//! ## Und die Regel dahinter ist ohnehin eine
//!
//! `SPRACHE.md` §10.2: *„Handgeschriebene Mutation an einer `table` mit `ops` ist ein
//! **Uebersetzungsfehler**."* Der Bericht unten ist die Messform derselben Sache; die Absage
//! `D001` ist die Sprachform.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::BTreeMap;

/// Was über einen Träger festgestellt wurde.
#[derive(Debug, Clone)]
pub struct Traeger {
    pub name: String,
    /// Nennt die Tabelle erzeugte Mutationen (`ops …`)?
    pub hat_ops: bool,
    /// Handschriftliche Schreibstellen auf die Slots — Datei:Zeile fällt beim Aufrufer an.
    pub handschrift: Vec<(String, Span)>,
    /// `breaking`-Blöcke, die eine Invariante dieses Trägers ruhen lassen (L3).
    pub breaking: Vec<(String, Span)>,
}

impl Traeger {
    /// **Die K-Bedingung selbst.** Nur wo sie hält, darf eine Pflicht als „durch
    /// Konstruktion" gebucht werden.
    pub fn k_haelt(&self) -> bool {
        self.hat_ops && self.handschrift.is_empty() && self.breaking.is_empty()
    }
}

/// Erhebt je Tabelle, ob alle Schreibstellen erzeugt sind.
pub fn erhebe(baum: &Programm) -> Vec<Traeger> {
    let mut traeger: BTreeMap<String, Traeger> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Tabelle(t) = &item.art {
            traeger.insert(
                t.name.text.clone(),
                Traeger {
                    name: t.name.text.clone(),
                    hat_ops: !t.ops.is_empty(),
                    handschrift: Vec::new(),
                    breaking: Vec::new(),
                },
            );
        }
    });

    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let mut ziele = Vec::new();
        let mut brueche = Vec::new();
        sammle(b, &mut ziele, &mut brueche);
        for (ort, span) in ziele {
            // Auf welche Tabelle zielt der Schreibzugriff? Der Grundname eines Ortes ist
            // entweder die Tabelle selbst (`Kappenraum.slots[s]`) oder ein Zeiger auf sie.
            for (name, t) in traeger.iter_mut() {
                if ort.basis.text == *name
                    || ort
                        .suffixe
                        .iter()
                        .any(|s| matches!(s, OrtSuffix::Feld(i) if i.text == "slots"))
                        && ort.basis.text != *name
                        && ort_zeigt_auf(f, &ort.basis.text, name)
                {
                    t.handschrift.push((f.name.text.clone(), span));
                }
            }
        }
        for (inv, span) in brueche {
            for t in traeger.values_mut() {
                if t.hat_ops {
                    t.breaking.push((format!("{} in {}", inv, f.name.text), span));
                }
            }
        }
    });
    traeger.into_values().collect()
}

/// Zeigt der Parameter `basis` von `f` auf die Tabelle `tabelle`?
fn ort_zeigt_auf(f: &FnDecl, basis: &str, tabelle: &str) -> bool {
    f.parameter.iter().any(|p| {
        p.name.text == basis
            && match &p.typ {
                TypExpr::Zeiger(z) => matches!(&z.ziel, TypExpr::Pfad(pf)
                    if pf.teile.last().is_some_and(|i| i.text == tabelle)),
                TypExpr::Pfad(pf) => pf.teile.last().is_some_and(|i| i.text == tabelle),
                _ => false,
            }
    })
}

fn sammle(b: &Block, ziele: &mut Vec<(Ort, Span)>, brueche: &mut Vec<(String, Span)>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => ziele.push((z.ziel.clone(), s.span)),
            StmtArt::Publish(p) => ziele.push((p.ziel.clone(), s.span)),
            StmtArt::Exchange(e) => ziele.push((e.ort.clone(), s.span)),
            StmtArt::Bricht(x) => {
                for i in &x.invarianten {
                    brueche.push((i.text.clone(), s.span));
                }
                sammle(&x.rumpf, ziele, brueche);
            }
            StmtArt::Wenn(w) => {
                for (_, r) in &w.zweige {
                    sammle(r, ziele, brueche);
                }
                if let Some(r) = &w.sonst {
                    sammle(r, ziele, brueche);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    sammle(&z.rumpf, ziele, brueche);
                }
            }
            StmtArt::Sperrt(x) => sammle(&x.rumpf, ziele, brueche),
            StmtArt::Narrow(x) => sammle(&x.sonst, ziele, brueche),
            StmtArt::LetSonst(x) => sammle(&x.sonst, ziele, brueche),
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(x) => sammle(&x.rumpf, ziele, brueche),
                Schleife::Retry(x) => sammle(&x.rumpf, ziele, brueche),
                Schleife::Forever(x) => sammle(&x.rumpf, ziele, brueche),
            },
            _ => {}
        }
    }
}

/// **`by ops` am Feld — die schärfere Fassung (2026-08-16).**
///
/// `D001` fällt an einer `table`, die `ops` nennt: dort ist **jede** Handmutation ein Fehler.
/// **`by ops` steht am FELD** und trägt damit einen Fall, den `D001` nicht kann: eine Tabelle,
/// deren Slots teils erzeugt und teils von Hand geschrieben werden — *`refcount` gehört den
/// Operationen, `benutzt` nicht.*
///
/// **Und das ist der Unterschied zwischen einer Prüfvorschrift und einer
/// Grammatikeigenschaft:** die K-Bedingung des Messprotokolls lautet *„gilt nur, wenn ALLE
/// Mutationen des Trägers erzeugte Operationen sind"* — mit `by ops` ist sie **je Feld
/// abgeschlossen**, statt je Tabelle nachgezählt.
fn nur_ops_felder(baum: &Programm) -> Vec<(String, String)> {
    let mut aus = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Tabelle(t) = &item.art {
            if let Some(sd) = &t.slot {
                for f in &sd.felder {
                    if f.nur_ops {
                        aus.push((t.name.text.clone(), f.name.text.clone()));
                    }
                }
            }
        }
    });
    aus
}

/// **Die Sprachform:** eine `table` mit `ops` duldet keine Handmutation (`SPRACHE.md` §10.2).
pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    // **D002 -- `by ops` am Feld.** Schärfer als `D001`: es trifft auch dort, wo die Tabelle
    // als Ganzes Handmutationen duldet, das EINE Feld aber nicht.
    let geschuetzt = nur_ops_felder(baum);
    if !geschuetzt.is_empty() {
        crate::fuer_jedes_item(baum, &mut |item| {
            let ItemArt::Funktion(f) = &item.art else {
                return;
            };
            let FnRumpf::Block(b) = &f.rumpf else {
                return;
            };
            let mut ziele = Vec::new();
            let mut brueche = Vec::new();
            sammle(b, &mut ziele, &mut brueche);
            for (ort, span) in &ziele {
                let text = ort.text();
                for (tab, feld) in &geschuetzt {
                    if text.split(['.', '[']).any(|x| x == feld) {
                        absagen.schiebe(
                            Absage::fehler(
                                "D002",
                                *span,
                                format!(
                                    "`{text}` carries `by ops` in `{tab}` and is mutated \
                                        by hand here"
                                ),
                            )
                            .mit_notiz(
                                "`by ops` means: only the generated operations of the \
                                    table write this field",
                            )
                            .mit_notiz(
                                "that is exactly what makes `refcount -= 1` by hand \
                                    unwritable, and it is the point of the clause",
                            ),
                        );
                    }
                }
            }
        });
    }
    for t in erhebe(baum) {
        if !t.hat_ops {
            continue;
        }
        for (fn_name, span) in &t.handschrift {
            absagen.schiebe(
                Absage::fehler(
                    "D001",
                    *span,
                    format!(
                        "`{}` writes `{}` by hand although the table declares `ops`",
                        fn_name, t.name
                    ),
                )
                .mit_notiz(
                    "SPRACHE.md §10.2: a hand-written mutation on a `table` with `ops` is \
                        a compile error",
                )
                .mit_notiz(
                    "otherwise the K condition of the measurement protocol falls: it \
                        holds only if ALL mutations of the carrier are generated operations",
                ),
            );
        }
    }
}

/// **Die Messform:** der Bericht, der in Messung 2 eingeht.
pub fn zeige(traeger: &[Traeger]) -> String {
    let mut out = String::new();
    out.push_str(
        "-- The K condition per carrier: are ALL write sites generated? Only then may a\n",
    );
    let (mut haelt, mut faellt) = (0, 0);
    for t in traeger {
        if t.k_haelt() {
            haelt += 1;
        } else {
            faellt += 1;
        }
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\n",
            t.name,
            if t.hat_ops { "ja" } else { "NEIN" },
            t.handschrift.len(),
            t.breaking.len(),
            if t.k_haelt() { "haelt" } else { "FAELLT" }
        ));
    }
    out.push_str(&format!(
        "-- {} carriers: K holds {haelt} times, falls {faellt} times.\n",
        traeger.len()
    ));
    // Der Nebenertrag, den das Protokoll ausdruecklich nennt: die breaking-Liste ist L3.
    let brueche: Vec<&(String, Span)> = traeger.iter().flat_map(|t| t.breaking.iter()).collect();
    out.push_str(&format!(
        "-- {} `breaking` site(s) -- which is also item L3 of the remaining list.\n",
        brueche.len()
    ));
    out
}
