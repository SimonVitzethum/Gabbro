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

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
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

fn block(b: &Block, zeiger: &BTreeMap<String, Zeiger>, absagen: &mut Absagen) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => schreibt(&z.ziel, s.span, zeiger, absagen),
            StmtArt::Publish(p) => schreibt(&p.ziel, s.span, zeiger, absagen),
            StmtArt::Let(l) => liest_expr(&l.wert, s.span, zeiger, absagen),
            StmtArt::Return(Some(e)) => liest_expr(e, s.span, zeiger, absagen),
            StmtArt::Wenn(w) => {
                for (bed, r) in &w.zweige {
                    liest_expr(bed, s.span, zeiger, absagen);
                    block(r, zeiger, absagen);
                }
                if let Some(r) = &w.sonst {
                    block(r, zeiger, absagen);
                }
            }
            StmtArt::Match(m) => {
                for zw in &m.zweige {
                    block(&zw.rumpf, zeiger, absagen);
                }
            }
            StmtArt::Sperrt(x) => block(&x.rumpf, zeiger, absagen),
            StmtArt::Bricht(x) => block(&x.rumpf, zeiger, absagen),
            StmtArt::Narrow(x) => block(&x.sonst, zeiger, absagen),
            StmtArt::LetSonst(x) => block(&x.sonst, zeiger, absagen),
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(x) => block(&x.rumpf, zeiger, absagen),
                Schleife::Retry(x) => block(&x.rumpf, zeiger, absagen),
                Schleife::Forever(x) => block(&x.rumpf, zeiger, absagen),
            },
            _ => {}
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

fn liest_expr(e: &Expr, span: Span, zeiger: &BTreeMap<String, Zeiger>, absagen: &mut Absagen) {
    match &e.art {
        ExprArt::Ort(o) => liest(o, span, zeiger, absagen),
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => liest_expr(x, span, zeiger, absagen),
        ExprArt::Binaer(_, a, b) => {
            liest_expr(a, span, zeiger, absagen);
            liest_expr(b, span, zeiger, absagen);
        }
        ExprArt::Ruf(r) => {
            for a in &r.argumente {
                liest_expr(a, span, zeiger, absagen);
            }
        }
        _ => {}
    }
}
