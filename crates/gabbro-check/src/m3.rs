//! **Pass 4 — M3: Adressräume und Zugriffsrechte am Zeiger. Der letzte ganz fehlende.**
//!
//! `SYNTAX.md` §3: `ptr<raum, rechte> Ziel`. Der Raum steht **am Typ**, nicht in einer
//! Konvention — und daraus fallen drei Pflichten, die sonst ein Mensch tragen müsste:
//!
//! 1. **Rechte.** Ein Lesen braucht `r`, ein Schreiben `w`. Ein Zeiger ohne das Recht ist
//!    kein Laufzeitfehler, sondern ein Übersetzungsfehler.
//! 2. **Die DMA-Grenze.** Ein `dma`-Zeiger erreicht Speicher, in den ein **Gerät** schreibt.
//!    Ihn wie `normal` zu lesen heisst, eine Momentaufnahme für eine Tatsache zu halten.
//! 3. **Die Platzierungsregel.** Ein Träger mit erzeugten Operationen (`ops`) darf **nicht**
//!    in einem `dma`-erreichbaren Raum liegen — sonst umgeht das Gerät jede Grammatik
//!    (`TODO.md`, Durchstich 2 von `by ops`).
//!
//! ## Was dieser Pass NICHT ist
//!
//! **Er ist kein Alias-Analysator.** Zwei `ptr<normal, rw>` auf dasselbe Objekt bleiben
//! ununterscheidbar — dafür steht `own` und die Auflösung aus A1 (*Kernzustand braucht
//! keinen Zeiger*). *Das steht hier, damit niemand die Deckung grösser liest, als sie ist.*
//!
//! ## Die Grobheit hat eine Richtung (W9)
//!
//! Wo der Zeigertyp eines Ortes **nicht auflösbar** ist (fremdes Modul, unbekannter Typ),
//! sagt der Pass **nichts** — statt anzunehmen, es sei `normal`. Eine Annahme wäre hier in
//! die **unsichere** Richtung grob: sie liesse einen `mmio`-Zugriff als gewöhnlichen durch.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::BTreeMap;

/// Was über einen Zeigerparameter bekannt ist.
#[derive(Clone)]
struct Zeiger {
    raum: Raum,
    rechte: Vec<Recht>,
}

impl Zeiger {
    fn darf_lesen(&self) -> bool {
        self.rechte.iter().any(|r| {
            matches!(
                r,
                Recht::Lesen | Recht::LesenSchreiben | Recht::Eigen(_)
            )
        })
    }
    fn darf_schreiben(&self) -> bool {
        self.rechte
            .iter()
            .any(|r| matches!(r, Recht::Schreiben | Recht::LesenSchreiben | Recht::Eigen(_)))
    }
}

fn raumname(r: &Raum) -> String {
    match r {
        Raum::Normal => "normal".into(),
        Raum::Mmio => "mmio".into(),
        Raum::Dma => "dma".into(),
        Raum::Code => "code".into(),
        Raum::Boot => "boot".into(),
        Raum::Port => "port".into(),
        Raum::Benannt(i) => i.text.clone(),
    }
}

/// **`R004` — zweimal `own` auf denselben Gegenstand.**
///
/// `own` war bis 2026-08-19 ein Synonym für `rw`: drei Lesestellen, alle drei behandeln
/// `Recht::Eigen` genau wie `Recht::LesenSchreiben`. Ein Ruf `zwei(q, q)` auf zwei
/// `own`-Parameter ging mit **0 Fehlern** durch — *zwei Besitzer derselben Region*, und
/// `m2.rs`s Modulkopf führt genau diesen Satz als das, wogegen die Linearität steht.
///
/// **Was diese Regel NICHT tut: eine Aliasanalyse.** Zwei verschiedene Namen, die auf
/// dasselbe zeigen, bleiben ununterscheidbar — das ist M3s offener Rest und eine
/// Sprachentscheidung (`own` als Freigabeoperation oder als Signaturvermerk). Hier steht
/// die Hälfte, die **keine Entscheidung braucht**: derselbe Ort, syntaktisch, an zwei
/// `own`-Stellen desselben Rufs. *Unter jeder Lesart von `own` ist das ein Widerspruch.*
///
/// > **Die erste Beissstelle von `own`** — bis hierher war es eine Klausel ohne Leser,
/// > dieselbe Klasse wie `obermenge`, `gates`, `mirrors` und `counterprobe` vor «K5».
fn eigen_doppelt(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    // Welche Parameter einer Funktion tragen `own`? Der Schlüssel ist qualifiziert.
    let mut eigen: BTreeMap<String, Vec<bool>> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            eigen.insert(
                crate::umgebung::qualifiziere(modul, &f.name.text),
                f.parameter
                    .iter()
                    .map(|p| match &p.typ {
                        TypExpr::Zeiger(z) => {
                            z.rechte.iter().any(|r| matches!(r, Recht::Eigen(_)))
                        }
                        _ => false,
                    })
                    .collect(),
            );
        }
    });
    let g = crate::aufrufgraph::erhebe_mit(baum, &u);
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let Some(k) = g.knoten.get(&crate::umgebung::qualifiziere(modul, &f.name.text)) else {
            return;
        };
        for (ziel, args) in &k.rufe {
            let Some(marken) = eigen.get(ziel) else {
                continue;
            };
            // Nur die Argumente, die auf einem `own`-Parameter landen und ein ORT sind.
            let mut gesehen: Vec<&String> = Vec::new();
            for (i, a) in args.iter().enumerate() {
                if !marken.get(i).copied().unwrap_or(false) {
                    continue;
                }
                let Some(ort) = a else { continue };
                if gesehen.iter().any(|g| *g == ort) {
                    absagen.schiebe(
                        Absage::fehler(
                            "R004",
                            f.name.span,
                            format!(
                                "`{}` passes `{ort}` to two `own` parameters of `{}`",
                                f.name.text,
                                crate::umgebung::kurzname(ziel)
                            ),
                        )
                        .mit_notiz(
                            "`own` says: this is the one owner -- two of them on the same \
                             object is two owners of the same region",
                        )
                        .mit_notiz(
                            "this is the syntactic half; two DIFFERENT names pointing at the \
                             same object stay indistinguishable (M3's open alias question)",
                        ),
                    );
                    break;
                }
                gesehen.push(ort);
            }
        }
    });
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    eigen_doppelt(baum, absagen);

    // **Die Platzierungsregel zuerst** -- sie betrifft Deklarationen, nicht Rümpfe.
    let mut mit_ops: Vec<String> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Tabelle(t) = &item.art {
            if !t.ops.is_empty() {
                mit_ops.push(t.name.text.clone());
            }
        }
    });

    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let mut zeiger: BTreeMap<String, Zeiger> = BTreeMap::new();
        for p in &f.parameter {
            if let TypExpr::Zeiger(z) = &p.typ {
                // **Platzierungsregel:** ein `ops`-Traeger in einem `dma`-Raum umgeht die
                // Grammatik -- das Geraet schreibt an den erzeugten Operationen vorbei.
                if z.raum == Raum::Dma {
                    if let TypExpr::Pfad(pf) = &z.ziel {
                        if let Some(n) = pf.teile.last() {
                            if mit_ops.contains(&n.text) {
                                absagen.schiebe(
                                    Absage::fehler(
                                        "R001",
                                        p.name.span,
                                        format!(
                                            "`{}` points into the `dma` space at `{}`, and that \
                                             table declares `ops`",
                                            p.name.text, n.text
                                        ),
                                    )
                                    .mit_notiz(
                                        "the K condition requires that ALL write sites of the \
                                         carrier are generated -- a device writes past any \
                                         grammar there is",
                                    )
                                    .mit_notiz(
                                        "the honest form is a placement rule, like the one for \
                                         the GDT: a `by ops` carrier lies in no \
                                         `dma`-reachable region",
                                    ),
                                );
                            }
                        }
                    }
                }
                zeiger.insert(
                    p.name.text.clone(),
                    Zeiger {
                        raum: z.raum.clone(),
                        rechte: z.rechte.clone(),
                    },
                );
            }
        }
        if zeiger.is_empty() {
            return;
        }
        if let FnRumpf::Block(b) = &f.rumpf {
            block(b, &zeiger, absagen);
        }
    });
}

/// **Der Abstieg geht über `crate::unterbloecke`** — erschöpfend über `StmtArt`, ohne
/// `_`-Zweig. Vorher fehlten `observes` und `exchange`: ein Lesen über einen `ptr<…, r>` in
/// einem RCU-Leseblock oder in einem `update`-Rumpf war für die Rechteprüfung unsichtbar.
fn block(b: &Block, zeiger: &BTreeMap<String, Zeiger>, absagen: &mut Absagen) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => schreibt(&z.ziel, s.span, zeiger, absagen),
            StmtArt::Publish(p) => schreibt(&p.ziel, s.span, zeiger, absagen),
            _ => {}
        }
        for e in crate::eigene_ausdruecke(s) {
            liest_expr(e, s.span, zeiger, absagen);
        }
        for k in crate::unterbloecke(s) {
            block(k, zeiger, absagen);
        }
    }
}

fn schreibt(o: &Ort, span: Span, zeiger: &BTreeMap<String, Zeiger>, absagen: &mut Absagen) {
    let Some(z) = zeiger.get(&o.basis.text) else {
        return; // nicht aufloesbar -- der Pass sagt nichts (W9)
    };
    if !z.darf_schreiben() {
        absagen.schiebe(
            Absage::fehler(
                "R002",
                span,
                format!(
                    "`{}` is written, but the pointer carries no `w`",
                    o.text()
                ),
            )
            .mit_notiz(format!(
                "`{}` is declared `ptr<{}, …>` without write permission -- that is a \
                 compile error, not a runtime check",
                o.basis.text,
                raumname(&z.raum)
            )),
        );
    }
}

fn liest(o: &Ort, span: Span, zeiger: &BTreeMap<String, Zeiger>, absagen: &mut Absagen) {
    let Some(z) = zeiger.get(&o.basis.text) else {
        return;
    };
    if !z.darf_lesen() {
        absagen.schiebe(
            Absage::fehler(
                "R003",
                span,
                format!("`{}` is read, but the pointer carries no `r`", o.text()),
            )
            .mit_notiz("a `w` pointer is not readable -- `class w` on a register means the same"),
        );
    }
}

/// Ueber `crate::alle_orte` -- ein Lesen in Indexposition ist ein Lesen (2026-08-20).
fn liest_expr(e: &Expr, span: Span, zeiger: &BTreeMap<String, Zeiger>, absagen: &mut Absagen) {
    for o in crate::alle_orte(e) {
        liest(o, span, zeiger, absagen);
    }
}
