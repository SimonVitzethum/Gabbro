//! **Pass 3 -- M1 und die drei Flussregeln V1–V3.**
//!
//! > *„Jede Operation muss im Bereich ihres Ergebnistyps bleiben; passt `a + b` nicht ins
//! > Ziel, ist das ein **Uebersetzungsfehler, keine Laufzeitpruefung**. Division und Rest
//! > verlangen einen Nenner, dessen Bereich die Null ausschliesst."*
//! > ([`SPRACHE.md`](SPRACHE.md) §3)
//!
//! Und die Gegenmessung -- 255 Subtraktionen, 102 flusssensitiv -- hat gezeigt, dass *eine*
//! Regel nicht reicht und `narrow` allein zum Ritual wuerde. Es gibt genau **drei**:
//!
//! | | Regel |
//! |---|---|
//! | **V1** | eine geprüfte **Bereichsbedingung** verengt den Bereich der geprüften Stelle im Zweig danach |
//! | **V2** | eine geprüfte **Beziehung zweier Stellen** wird zum Zweigfakt: unter `a >= b` hat `a - b` den Typ `0 .. a.max − b.min` |
//! | **V3** | ein `match` auf einen `tagged`-Typ verengt im Zweig auf die Variante samt Nutzlast |
//!
//! **Syntaxgesteuert, ohne Fixpunkt, ohne Loeser.** Der Pass fuehrt je Block eine
//! Faktenmenge, die nur an den drei benannten Stellen waechst und bei **jedem Schreiben auf
//! eine beteiligte Stelle stirbt**. Schleifen tragen keine Fakten hinein.
//!
//! ## Was dieser Pass NICHT tut, und es steht hier statt in einer Fussnote
//!
//! * **Er prueft Rümpfe, keine Praedikate.** `requires`, `ensures` und `invariant` sind
//!   Geisterausdruecke ohne Laufzeitwirkung; sie gehoeren dem Beweiser, nicht M1.
//! * **Er kennt keine Aufrufwirkung auf lokale Werte** -- er braucht sie auch nicht: Gabbro
//!   hat keinen Adressoperator, also kann ein Gerufener eine lokale Groesse nicht aendern.
//!   Alles **Nichtlokale** verliert seine Fakten bei jedem Aufruf.
//! * **Er zaehlt, was er nicht weiss.** Jeder Ausdruck ohne Typ geht in die Zaehlung; ein
//!   Lauf ohne diese Zahl sieht aus wie Deckung.

use crate::typen::{self, IntBereich, Typ};
use crate::umgebung::Umgebung;
use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::HashMap;

/// Was der Pass angesehen hat -- die Zahl steht neben dem Ergebnis.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Zaehlung {
    pub typisiert: usize,
    pub unbekannt: usize,
}

impl Zaehlung {
    pub fn gesamt(&self) -> usize {
        self.typisiert + self.unbekannt
    }

    pub fn deckung(&self) -> f64 {
        if self.gesamt() == 0 {
            return 0.0;
        }
        100.0 * self.typisiert as f64 / self.gesamt() as f64
    }
}

/// Ein Zweigfakt. Er lebt bis zum naechsten Schreiben auf eine beteiligte Stelle.
#[derive(Debug, Clone)]
enum Fakt {
    /// V1 -- die Stelle liegt in diesem Bereich.
    Bereich {
        schluessel: String,
        min: i128,
        max: i128,
    },
    /// V2 -- die Beziehung zweier Stellen, ausschliesslich als Vergleich.
    Beziehung {
        links: String,
        op: BinOp,
        rechts: String,
    },
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) -> Zaehlung {
    let umgebung = Umgebung::sammle(baum);
    let mut p = Pruefer {
        u: &umgebung,
        absagen,
        zaehlung: Zaehlung::default(),
    };
    p.programm(baum);
    p.zaehlung
}

struct Pruefer<'a> {
    u: &'a Umgebung,
    absagen: &'a mut Absagen,
    zaehlung: Zaehlung,
}

/// Die Bindungen und Fakten eines Blocks. Ein Block erbt beide und gibt keins zurueck.
#[derive(Clone, Default)]
struct Lage {
    lokal: HashMap<String, Typ>,
    fakten: Vec<Fakt>,
}

impl<'a> Pruefer<'a> {
    fn programm(&mut self, baum: &Programm) {
        crate::fuer_jedes_item(baum, &mut |item| {
            if let ItemArt::Funktion(f) = &item.art {
                // Nur Ruempfe: Praedikate haben keine Laufzeitwirkung.
                if let FnRumpf::Block(b) = &f.rumpf {
                    let mut lage = Lage::default();
                    for prm in &f.parameter {
                        let t = self.u.typ_von_ausdruck_decl(&prm.typ);
                        lage.lokal.insert(prm.name.text.clone(), t);
                    }
                    let ergebnis = f.ergebnis.as_ref().map(|t| self.u.typ_von_ausdruck_decl(t));
                    self.block(b, &mut lage, ergebnis.as_ref());
                }
            }
        });
    }

    // -- Anweisungen --------------------------------------------------------------------

    fn block(&mut self, b: &Block, lage: &mut Lage, ergebnis: Option<&Typ>) {
        for s in &b.anweisungen {
            self.anweisung(s, lage, ergebnis);
        }
    }

    fn anweisung(&mut self, s: &Stmt, lage: &mut Lage, ergebnis: Option<&Typ>) {
        match &s.art {
            StmtArt::Let(l) => {
                let wert = self.ausdruck(&l.wert, lage);
                let ziel = l.typ.as_ref().map(|t| self.u.typ_von_ausdruck_decl(t));
                if let Some(z) = &ziel {
                    self.passt(&wert, z, l.wert.span, "die Bindung");
                }
                lage.lokal
                    .insert(l.name.text.clone(), ziel.unwrap_or(wert));
            }
            StmtArt::LetSonst(l) => {
                let t = self.ruf(&l.ruf, lage);
                lage.lokal.insert(l.name.text.clone(), t);
                self.aufruf_toetet_fakten(lage);
                let mut innen = lage.clone();
                self.block(&l.sonst, &mut innen, ergebnis);
            }
            StmtArt::Zuweisung(z) => {
                let ziel = self.u.typ_von_ort(&z.ziel, &lage.lokal);
                self.buche(&ziel);
                let quelle = self.ausdruck(&z.wert, lage);
                let ergebnis_typ = match z.op {
                    ZuwOp::Setzt => quelle,
                    // `a += b` ist `a = a + b`. Das GELESENE `a` traegt seine Fakten (V1/V2),
                    // das geschriebene seinen deklarierten Bereich -- ohne diese Trennung
                    // sieht `if z >= 1 { z -= 1; }` aus wie `z -= 1`.
                    op => {
                        let gelesen = self.mit_fakt(&z.ziel, ziel.clone(), lage);
                        self.rechnung_zuweisung(&gelesen, &quelle, op, &z.ziel, z.wert.span)
                    }
                };
                // Ein `wrapping`-Slot hat seinen Ueberlauf DEKLARIERT; dort ist er kein Befund.
                if !ziel.laeuft_um() {
                    self.passt(&ergebnis_typ, &ziel, z.wert.span, "die Zuweisung");
                }
                self.schreiben_toetet_fakten(&z.ziel, lage);
            }
            StmtArt::Publish(p) => {
                let ziel = self.u.typ_von_ort(&p.ziel, &lage.lokal);
                self.buche(&ziel);
                let quelle = self.ausdruck(&p.wert, lage);
                self.passt(&quelle, &ziel, p.wert.span, "die Veroeffentlichung");
                self.schreiben_toetet_fakten(&p.ziel, lage);
            }
            StmtArt::Wenn(w) => {
                for (bedingung, rumpf) in &w.zweige {
                    let _ = self.ausdruck(bedingung, lage);
                    let mut innen = lage.clone();
                    // V1 und V2: die geprueften Stellen sind im Zweig danach enger.
                    self.fakten_aus(bedingung, false, &mut innen);
                    self.block(rumpf, &mut innen, ergebnis);
                }
                if let Some(sonst) = &w.sonst {
                    let mut innen = lage.clone();
                    if let Some((bedingung, _)) = w.zweige.first() {
                        self.fakten_aus(bedingung, true, &mut innen);
                    }
                    self.block(sonst, &mut innen, ergebnis);
                }
                // **V1 gilt auch fuer den Weg NACH einem Zweig, der immer verlaesst.**
                // `if a >= b { return a - b; }` -- was danach kommt, ist genau der Fall
                // `a < b`, und zwar syntaktisch, ohne Fixpunkt: der Zweig endet mit
                // `return`, `leave`, `next` oder einem Aufruf nach `never`. Ohne diese
                // Regel braucht der fruehe Rueckstieg ein `narrow`, und die Messlatte
                // („`narrow` <= 24 Fundstellen") faellt an einer Redewendung statt an der
                // Sprache.
                if w.sonst.is_none() && w.zweige.len() == 1 {
                    let (bedingung, rumpf) = &w.zweige[0];
                    if self.endet_immer(rumpf) {
                        self.fakten_aus(bedingung, true, lage);
                    }
                }
            }
            StmtArt::Match(m) => {
                let gegenstand = self.ausdruck(&m.gegenstand, lage);
                for zweig in &m.zweige {
                    let mut innen = lage.clone();
                    // V3: der Binder traegt die Nutzlast SEINER Variante.
                    if let (Some(binder), Typ::Summe { varianten, .. }) =
                        (&zweig.binder, gegenstand.durchgreifen())
                    {
                        let nutzlast = varianten
                            .iter()
                            .find(|(n, _)| *n == zweig.variante.text)
                            .and_then(|(_, t)| t.clone())
                            .unwrap_or(Typ::Unbekannt);
                        innen.lokal.insert(binder.text.clone(), nutzlast);
                    } else if let Some(binder) = &zweig.binder {
                        innen.lokal.insert(binder.text.clone(), Typ::Unbekannt);
                    }
                    self.block(&zweig.rumpf, &mut innen, ergebnis);
                }
            }
            StmtArt::Narrow(n) => {
                let vorher = self.u.typ_von_ort(&n.ort, &lage.lokal);
                self.buche(&vorher);
                let mut innen = lage.clone();
                self.block(&n.sonst, &mut innen, ergebnis);
                // Der `else`-Zweig divergiert oder kehrt zurueck; danach gilt der Bereich.
                let von = self.u.konst_wert(&n.bereich.von);
                let bis = self.u.konst_wert(&n.bereich.bis);
                if let (Some(lo), Some(hi), Some(schluessel)) =
                    (von, bis, schluessel_von(&n.ort))
                {
                    let hi = if n.bereich.exklusiv { hi - 1 } else { hi };
                    lage.fakten.push(Fakt::Bereich {
                        schluessel,
                        min: lo,
                        max: hi,
                    });
                }
            }
            StmtArt::Bricht(b) => {
                let mut innen = lage.clone();
                self.block(&b.rumpf, &mut innen, ergebnis);
            }
            StmtArt::Sperrt(l) => {
                let mut innen = lage.clone();
                self.block(&l.rumpf, &mut innen, ergebnis);
            }
            StmtArt::Schleife(sch) => {
                // Schleifen tragen keine Fakten hinein -- die Invariante der Traversierung
                // tut das, und die gehoert dem Beweiser.
                let mut innen = Lage {
                    lokal: lage.lokal.clone(),
                    fakten: Vec::new(),
                };
                match sch.as_ref() {
                    Schleife::Traverse(t) => {
                        innen
                            .lokal
                            .insert(t.variable.text.clone(), Typ::Unbekannt);
                        if let Some(g) = &t.gegenstand {
                            let _ = self.ausdruck(g, lage);
                        }
                        self.block(&t.rumpf, &mut innen, ergebnis);
                    }
                    Schleife::Retry(r) => {
                        let _ = self.ausdruck_opt(r.schranke.clone(), lage);
                        self.block(&r.rumpf, &mut innen, ergebnis);
                    }
                    Schleife::Forever(f) => {
                        let _ = self.ausdruck_opt(f.je_durchgang.clone(), lage);
                        self.block(&f.rumpf, &mut innen, ergebnis);
                    }
                }
            }
            StmtArt::Return(Some(e)) => {
                let t = self.ausdruck(e, lage);
                if let Some(z) = ergebnis {
                    self.passt(&t, z, e.span, "die Rueckgabe");
                }
            }
            StmtArt::Ruf(r) => {
                let _ = self.ruf(r, lage);
                self.aufruf_toetet_fakten(lage);
            }
            StmtArt::AwaitLoad(a) => {
                let t = self.u.typ_von_ort(&a.quelle, &lage.lokal);
                self.buche(&t);
                lage.lokal.insert(a.name.text.clone(), t);
            }
            StmtArt::Exchange(e) => {
                let t = self.u.typ_von_ort(&e.ort, &lage.lokal);
                self.buche(&t);
                lage.lokal.insert(e.name.text.clone(), t.clone());
                if let XForm::Update { binder, rumpf } = &e.form {
                    let mut innen = lage.clone();
                    innen.lokal.insert(binder.text.clone(), t);
                    self.block(rumpf, &mut innen, ergebnis);
                }
                self.schreiben_toetet_fakten(&e.ort, lage);
            }
            StmtArt::Return(None) | StmtArt::Leave(_) | StmtArt::Next(_) => {}
        }
    }

    /// Verlaesst dieser Block seinen Weg immer? Rein syntaktisch, ohne Fixpunkt.
    fn endet_immer(&self, b: &Block) -> bool {
        let Some(letzte) = b.anweisungen.last() else {
            return false;
        };
        match &letzte.art {
            StmtArt::Return(_) | StmtArt::Leave(_) | StmtArt::Next(_) => true,
            // Ein Aufruf einer Funktion nach `never` kehrt nicht zurueck.
            StmtArt::Ruf(r) => {
                let name = r
                    .pfad
                    .teile
                    .last()
                    .map(|i| i.text.as_str())
                    .unwrap_or_default();
                matches!(
                    self.u.funktionen.get(name).and_then(|s| s.ergebnis.clone()),
                    Some(Typ::Nie)
                )
            }
            StmtArt::Wenn(w) => {
                w.sonst.as_ref().is_some_and(|s| self.endet_immer(s))
                    && w.zweige.iter().all(|(_, r)| self.endet_immer(r))
            }
            StmtArt::Match(m) => m.zweige.iter().all(|z| self.endet_immer(&z.rumpf)),
            _ => false,
        }
    }

    /// `a += b` rechnet im Bereich von `a` -- und genau dort faellt der Ueberlauf.
    fn rechnung_zuweisung(
        &mut self,
        ziel: &Typ,
        quelle: &Typ,
        op: ZuwOp,
        ort: &Ort,
        span: Span,
    ) -> Typ {
        let (Some(a), Some(b)) = (ziel.bereich(), quelle.bereich()) else {
            return Typ::Unbekannt;
        };
        let r = match op {
            ZuwOp::Plus => typen::addiere(&a, &b),
            ZuwOp::Minus => typen::subtrahiere(&a, &b),
            ZuwOp::Und => typen::bitweise(&a, &b, typen::BitOpArt::Und),
            ZuwOp::Oder => typen::bitweise(&a, &b, typen::BitOpArt::Oder),
            ZuwOp::Setzt => return quelle.clone(),
        };
        if r.laeuft_ueber && !ziel.laeuft_um() {
            self.ueberlauf(span, &a, &b, op_wort(op), ort);
        }
        match r.bereich {
            Some(b) => Typ::Ganzzahl(b),
            None => Typ::Unbekannt,
        }
    }

    // -- Ausdruecke ---------------------------------------------------------------------

    fn ausdruck_opt(&mut self, e: Expr, lage: &Lage) -> Typ {
        self.ausdruck(&e, lage)
    }

    fn ausdruck(&mut self, e: &Expr, lage: &Lage) -> Typ {
        let t = self.ausdruck_roh(e, lage);
        self.buche(&t);
        t
    }

    fn ausdruck_roh(&mut self, e: &Expr, lage: &Lage) -> Typ {
        match &e.art {
            ExprArt::Zahl(v) => match i128::try_from(*v) {
                Ok(w) => Typ::Ganzzahl(IntBereich::konstante(w)),
                Err(_) => Typ::Unbekannt,
            },
            ExprArt::Wahr | ExprArt::Falsch => Typ::Wahrheit,
            ExprArt::Ergebnis => Typ::Unbekannt,
            ExprArt::Klammer(i) => self.ausdruck_roh(i, lage),
            ExprArt::Ort(o) => {
                self.index_pruefen(o, lage);
                let grund = self.u.typ_von_ort(o, &lage.lokal);
                self.mit_fakt(o, grund, lage)
            }
            // `old(x)` ist ein Geisterausdruck: er steht in `ensures`, nicht im Rumpf.
            ExprArt::Alt(_) => Typ::Unbekannt,
            ExprArt::Ruf(r) => self.ruf_roh(r, lage),
            ExprArt::Eingebaut(_) => Typ::Unbekannt,
            ExprArt::Unaer(UnOp::Nicht, i) => {
                let _ = self.ausdruck(i, lage);
                Typ::Wahrheit
            }
            ExprArt::Unaer(UnOp::Negativ, i) => {
                let t = self.ausdruck(i, lage);
                match t.bereich() {
                    Some(b) => Typ::Ganzzahl(IntBereich::genau(
                        b.breite,
                        true,
                        -b.max,
                        -b.min,
                    )),
                    None => Typ::Unbekannt,
                }
            }
            ExprArt::Binaer(op, a, b) => self.binaer(*op, a, b, e.span, lage),
        }
    }

    fn binaer(&mut self, op: BinOp, a: &Expr, b: &Expr, span: Span, lage: &Lage) -> Typ {
        let ta = self.ausdruck(a, lage);
        let tb = self.ausdruck(b, lage);
        if op == BinOp::Und || op == BinOp::Oder {
            return Typ::Wahrheit;
        }
        if op.ist_vergleich() {
            return Typ::Wahrheit;
        }
        let (Some(ba), Some(bb)) = (ta.bereich(), tb.bereich()) else {
            return Typ::Unbekannt;
        };

        // V2: unter `a >= b` faengt `a - b` bei 0 an, unter `a > b` bei 1.
        if op == BinOp::Minus {
            if let (ExprArt::Ort(oa), ExprArt::Ort(ob)) = (&a.art, &b.art) {
                if let Some(untergrenze) = self.beziehung(oa, ob, lage) {
                    return Typ::Ganzzahl(IntBereich::genau(
                        ba.breite,
                        ba.vorzeichen,
                        untergrenze,
                        (ba.max - bb.min).max(untergrenze),
                    ));
                }
            }
        }

        let r = match op {
            BinOp::Plus => typen::addiere(&ba, &bb),
            BinOp::Minus => typen::subtrahiere(&ba, &bb),
            BinOp::Mal => typen::multipliziere(&ba, &bb),
            BinOp::Geteilt | BinOp::Rest => {
                if bb.enthaelt_null() {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M102",
                            b.span,
                            format!(
                                "der Nenner hat den Bereich `{}` und schliesst die Null nicht aus",
                                bb.text()
                            ),
                        )
                        .mit_notiz(
                            "SPRACHE.md §3: Division und Rest verlangen einen Nenner, dessen \
                             Bereich die Null ausschliesst",
                        )
                        .mit_notiz(
                            "eine Pruefung `if n >= 1 { … }` verengt ihn (V1), sonst \
                             `narrow n to 1 .. … else { … }`",
                        ),
                    );
                    return Typ::Unbekannt;
                }
                if op == BinOp::Geteilt {
                    typen::teile(&ba, &bb)
                } else {
                    typen::rest(&ba, &bb)
                }
            }
            BinOp::BitUnd => typen::bitweise(&ba, &bb, typen::BitOpArt::Und),
            BinOp::BitOder => typen::bitweise(&ba, &bb, typen::BitOpArt::Oder),
            BinOp::BitXor => typen::bitweise(&ba, &bb, typen::BitOpArt::Xor),
            BinOp::SchiebLinks => typen::schiebe_links(&ba, &bb),
            BinOp::SchiebRechts => typen::schiebe_rechts(&ba, &bb),
            _ => return Typ::Unbekannt,
        };
        if r.laeuft_ueber && !ta.laeuft_um() {
            self.ueberlauf_ausdruck(span, &ba, &bb, op_zeichen(op));
        }
        match r.bereich {
            Some(x) => Typ::Ganzzahl(x),
            None => Typ::Unbekannt,
        }
    }

    fn ruf(&mut self, r: &Ruf, lage: &Lage) -> Typ {
        let t = self.ruf_roh(r, lage);
        self.buche(&t);
        t
    }

    fn ruf_roh(&mut self, r: &Ruf, lage: &Lage) -> Typ {
        let name = r
            .pfad
            .teile
            .last()
            .map(|i| i.text.clone())
            .unwrap_or_default();
        let signatur = self.u.funktionen.get(&name).cloned();
        let mut argtypen = Vec::new();
        for a in &r.argumente {
            argtypen.push((self.ausdruck(a, lage), a.span));
        }
        let Some(sig) = signatur else {
            return Typ::Unbekannt;
        };
        // Die Stelligkeit gehoert dem Namenspass; hier faellt nur der Bereich.
        for ((t, span), (pname, pt)) in argtypen.iter().zip(sig.parameter.iter()) {
            self.passt(t, pt, *span, &format!("das Argument `{pname}`"));
        }
        sig.ergebnis.clone().unwrap_or(Typ::Unbekannt)
    }

    // -- Fakten -------------------------------------------------------------------------

    /// V1/V2 aus einer geprueften Bedingung. `negiert` gilt fuer den `else`-Zweig.
    fn fakten_aus(&mut self, bedingung: &Expr, negiert: bool, lage: &mut Lage) {
        match &bedingung.art {
            ExprArt::Klammer(i) => self.fakten_aus(i, negiert, lage),
            // `a && b` gibt im Ja-Zweig beide Fakten; im Nein-Zweig keinen (es reicht, dass
            // einer faellt, und welcher steht nicht fest).
            ExprArt::Binaer(BinOp::Und, a, b) if !negiert => {
                self.fakten_aus(a, false, lage);
                self.fakten_aus(b, false, lage);
            }
            ExprArt::Binaer(BinOp::Oder, a, b) if negiert => {
                self.fakten_aus(a, true, lage);
                self.fakten_aus(b, true, lage);
            }
            ExprArt::Binaer(op, a, b) if op.ist_vergleich() => {
                let op = if negiert { negiere(*op) } else { *op };
                self.vergleichsfakt(op, a, b, lage);
            }
            _ => {}
        }
    }

    fn vergleichsfakt(&mut self, op: BinOp, a: &Expr, b: &Expr, lage: &mut Lage) {
        // V1 -- Stelle gegen Konstante, in beiden Schreibrichtungen.
        if let (ExprArt::Ort(o), Some(wert)) = (&a.art, self.u.konst_wert(b)) {
            self.bereichsfakt(o, op, wert, lage);
        }
        if let (Some(wert), ExprArt::Ort(o)) = (self.u.konst_wert(a), &b.art) {
            self.bereichsfakt(o, spiegle(op), wert, lage);
        }
        // V2 -- Stelle gegen Stelle, ausschliesslich als Vergleichsfakt.
        if let (ExprArt::Ort(oa), ExprArt::Ort(ob)) = (&a.art, &b.art) {
            if let (Some(links), Some(rechts)) = (schluessel_von(oa), schluessel_von(ob)) {
                lage.fakten.push(Fakt::Beziehung { links, op, rechts });
            }
        }
    }

    fn bereichsfakt(&mut self, o: &Ort, op: BinOp, wert: i128, lage: &mut Lage) {
        let Some(schluessel) = schluessel_von(o) else {
            return;
        };
        let (min, max) = match op {
            BinOp::GroesserGleich => (wert, i128::MAX),
            BinOp::Groesser => (wert + 1, i128::MAX),
            BinOp::KleinerGleich => (i128::MIN, wert),
            BinOp::Kleiner => (i128::MIN, wert - 1),
            BinOp::Gleich => (wert, wert),
            _ => return,
        };
        lage.fakten.push(Fakt::Bereich {
            schluessel,
            min,
            max,
        });
    }

    /// Der Typ eines Ortes, verengt durch die Fakten, die ueber ihn gelten.
    fn mit_fakt(&self, o: &Ort, grund: Typ, lage: &Lage) -> Typ {
        let Some(b) = grund.bereich() else {
            return grund;
        };
        let Some(schluessel) = schluessel_von(o) else {
            return grund;
        };
        let mut min = b.min;
        let mut max = b.max;
        for f in &lage.fakten {
            if let Fakt::Bereich {
                schluessel: s,
                min: lo,
                max: hi,
            } = f
            {
                if *s == schluessel {
                    min = min.max(*lo);
                    max = max.min(*hi);
                }
            }
        }
        if min == b.min && max == b.max {
            return grund;
        }
        Typ::Ganzzahl(IntBereich::genau(b.breite, b.vorzeichen, min, max))
    }

    /// V2 -- gibt die Untergrenze von `a - b`, wenn ein Vergleichsfakt sie traegt.
    fn beziehung(&self, a: &Ort, b: &Ort, lage: &Lage) -> Option<i128> {
        let (ka, kb) = (schluessel_von(a)?, schluessel_von(b)?);
        for f in &lage.fakten {
            if let Fakt::Beziehung { links, op, rechts } = f {
                if *links == ka && *rechts == kb {
                    match op {
                        BinOp::GroesserGleich => return Some(0),
                        BinOp::Groesser => return Some(1),
                        _ => {}
                    }
                }
                if *links == kb && *rechts == ka {
                    match op {
                        BinOp::KleinerGleich => return Some(0),
                        BinOp::Kleiner => return Some(1),
                        _ => {}
                    }
                }
            }
        }
        None
    }

    /// *„bei jedem Schreiben auf eine beteiligte Stelle stirbt der Fakt"*.
    fn schreiben_toetet_fakten(&self, ziel: &Ort, lage: &mut Lage) {
        let Some(k) = schluessel_von(ziel) else {
            lage.fakten.clear();
            return;
        };
        lage.fakten.retain(|f| match f {
            Fakt::Bereich { schluessel, .. } => !beruehrt(schluessel, &k),
            Fakt::Beziehung { links, rechts, .. } => {
                !beruehrt(links, &k) && !beruehrt(rechts, &k)
            }
        });
        // Ein Schreiben durch einen Zeiger kann alles Nichtlokale treffen -- ohne M3 gibt es
        // keine Aliasaussage, also faellt hier alles Nichtlokale mit.
        if k.contains('.') || k.contains("->") || k.contains('[') {
            lage.fakten.retain(|f| match f {
                Fakt::Bereich { schluessel, .. } => ist_lokal(schluessel),
                Fakt::Beziehung { links, rechts, .. } => ist_lokal(links) && ist_lokal(rechts),
            });
        }
    }

    /// Ein Aufruf toetet die Fakten ueber alles **Nichtlokale**. Lokale Groessen kann er
    /// nicht aendern: Gabbro hat keinen Adressoperator.
    fn aufruf_toetet_fakten(&self, lage: &mut Lage) {
        lage.fakten.retain(|f| match f {
            Fakt::Bereich { schluessel, .. } => ist_lokal(schluessel),
            Fakt::Beziehung { links, rechts, .. } => ist_lokal(links) && ist_lokal(rechts),
        });
    }

    // -- Absagen ------------------------------------------------------------------------

    fn buche(&mut self, t: &Typ) {
        if t.ist_unbekannt() {
            self.zaehlung.unbekannt += 1;
        } else {
            self.zaehlung.typisiert += 1;
        }
    }

    fn passt(&mut self, quelle: &Typ, ziel: &Typ, span: Span, was: &str) {
        let (Some(q), Some(z)) = (quelle.bereich(), ziel.bereich()) else {
            return;
        };
        if q.passt_in(&z) {
            return;
        }
        let mut a = Absage::fehler(
            "M101",
            span,
            format!(
                "{was} verlangt `{}`, der Wert hat `{}`",
                z.text(),
                q.text()
            ),
        )
        .mit_notiz(
            "M1: jede Operation muss im Bereich ihres Ergebnistyps bleiben -- \
             das ist ein Uebersetzungsfehler, keine Laufzeitpruefung",
        );
        if q.min < z.min || q.max > z.max {
            a = a.mit_notiz(format!(
                "es fehlt der Nachweis, dass der Wert in {} .. {} liegt; \
                 eine Pruefung davor verengt ihn (V1/V2), sonst `narrow … to … else {{ … }}`",
                z.min, z.max
            ));
        }
        self.absagen.schiebe(a);
    }

    fn ueberlauf(&mut self, span: Span, a: &IntBereich, b: &IntBereich, wort: &str, ort: &Ort) {
        self.absagen.schiebe(
            Absage::fehler(
                "M104",
                span,
                format!(
                    "`{}` {wort} verlaesst den Bereich: `{}` gegen `{}`",
                    ort.text(),
                    a.text(),
                    b.text()
                ),
            )
            .mit_notiz(
                "der Ueberlauf ist ein Uebersetzungsfehler, keine Laufzeitpruefung -- \
                 wer ihn will, deklariert den Slot als `wrapping`",
            )
            .mit_notiz(
                "eine Pruefung davor verengt den Bereich (V1), eine Beziehung zweier \
                 Stellen ebenso (V2)",
            ),
        );
    }

    fn ueberlauf_ausdruck(&mut self, span: Span, a: &IntBereich, b: &IntBereich, zeichen: &str) {
        self.absagen.schiebe(
            Absage::fehler(
                "M104",
                span,
                format!(
                    "`{} {zeichen} {}` verlaesst die Breite des Ergebnistyps",
                    a.text(),
                    b.text()
                ),
            )
            .mit_notiz(
                "SYNTAX.md §4: passt der Ergebnisbereich nicht, ist es ein \
                 Uebersetzungsfehler -- keine Laufzeitpruefung",
            ),
        );
    }

    /// M4 an der Stelle, an der M1 die Zahl hat: ein Index gegen die Laenge seines Feldes.
    fn index_pruefen(&mut self, o: &Ort, lage: &Lage) {
        let mut traeger = lage
            .lokal
            .get(&o.basis.text)
            .cloned()
            .or_else(|| self.u.globale.get(&o.basis.text).cloned())
            .unwrap_or(Typ::Unbekannt);
        for suffix in &o.suffixe {
            match suffix {
                OrtSuffix::Index(idx) => {
                    if let Typ::Feld {
                        element,
                        laenge: Some(n),
                    } = traeger.durchgreifen()
                    {
                        let n = *n as i128;
                        let it = self.ausdruck_roh(idx, lage);
                        if let Some(b) = it.bereich() {
                            if b.max >= n || b.min < 0 {
                                self.absagen.schiebe(
                                    Absage::fehler(
                                        "M103",
                                        idx.span,
                                        format!(
                                            "der Index hat `{}`, das Feld hat {n} Elemente",
                                            b.text()
                                        ),
                                    )
                                    .mit_notiz(
                                        "M4: kein ungeprueftes Indizieren -- die Schranke \
                                         faellt aus dem Typ des Index, nicht aus einer Pruefung \
                                         zur Laufzeit",
                                    ),
                                );
                            }
                        }
                        traeger = (**element).clone();
                    } else {
                        traeger = match traeger.durchgreifen() {
                            Typ::Feld { element, .. } => (**element).clone(),
                            _ => Typ::Unbekannt,
                        };
                    }
                }
                OrtSuffix::Feld(f) | OrtSuffix::Ueber(f) => {
                    traeger = self.u.feld_von(&traeger, &f.text);
                }
            }
        }
    }
}

/// Der Schluessel eines Ortes -- `None`, wenn ein Index kein einfacher Ort und keine Zahl
/// ist. **Ohne Schluessel kein Fakt:** zwei verschiedene Indizes duerfen nicht denselben
/// Namen bekommen, sonst verengt eine Pruefung ueber `a[i]` auch `a[j]`.
fn schluessel_von(o: &Ort) -> Option<String> {
    let mut s = o.basis.text.clone();
    for suffix in &o.suffixe {
        match suffix {
            OrtSuffix::Feld(f) => {
                s.push('.');
                s.push_str(&f.text);
            }
            OrtSuffix::Ueber(f) => {
                s.push_str("->");
                s.push_str(&f.text);
            }
            OrtSuffix::Index(e) => match &e.art {
                ExprArt::Zahl(v) => s.push_str(&format!("[{v}]")),
                ExprArt::Ort(inner) if inner.suffixe.is_empty() => {
                    s.push_str(&format!("[{}]", inner.basis.text));
                }
                _ => return None,
            },
        }
    }
    Some(s)
}

/// Beruehren sich zwei Ortsschluessel? Ein Schreiben auf `c.slots` trifft auch
/// `c.slots[i].benutzt`, und umgekehrt.
fn beruehrt(a: &str, b: &str) -> bool {
    a == b
        || a.starts_with(b) && trennt(a.as_bytes().get(b.len()).copied())
        || b.starts_with(a) && trennt(b.as_bytes().get(a.len()).copied())
}

fn trennt(c: Option<u8>) -> bool {
    matches!(c, Some(b'.') | Some(b'[') | Some(b'-'))
}

/// Eine Stelle ohne Feld- und Indexzugriff ist eine lokale Groesse -- die kann ein
/// Gerufener nicht aendern, weil es keinen Adressoperator gibt.
fn ist_lokal(schluessel: &str) -> bool {
    !schluessel.contains('.') && !schluessel.contains('[') && !schluessel.contains("->")
}

fn negiere(op: BinOp) -> BinOp {
    match op {
        BinOp::Gleich => BinOp::Ungleich,
        BinOp::Ungleich => BinOp::Gleich,
        BinOp::Kleiner => BinOp::GroesserGleich,
        BinOp::KleinerGleich => BinOp::Groesser,
        BinOp::Groesser => BinOp::KleinerGleich,
        BinOp::GroesserGleich => BinOp::Kleiner,
        anderer => anderer,
    }
}

/// `3 <= x` sagt dasselbe wie `x >= 3`.
fn spiegle(op: BinOp) -> BinOp {
    match op {
        BinOp::Kleiner => BinOp::Groesser,
        BinOp::KleinerGleich => BinOp::GroesserGleich,
        BinOp::Groesser => BinOp::Kleiner,
        BinOp::GroesserGleich => BinOp::KleinerGleich,
        anderer => anderer,
    }
}

fn op_wort(op: ZuwOp) -> &'static str {
    match op {
        ZuwOp::Plus => "+=",
        ZuwOp::Minus => "-=",
        ZuwOp::Und => "&=",
        ZuwOp::Oder => "|=",
        ZuwOp::Setzt => "=",
    }
}

fn op_zeichen(op: BinOp) -> &'static str {
    match op {
        BinOp::Plus => "+",
        BinOp::Minus => "-",
        BinOp::Mal => "*",
        BinOp::Geteilt => "/",
        BinOp::Rest => "%",
        BinOp::SchiebLinks => "<<",
        BinOp::SchiebRechts => ">>",
        BinOp::BitUnd => "&",
        BinOp::BitOder => "|",
        BinOp::BitXor => "^",
        _ => "?",
    }
}
