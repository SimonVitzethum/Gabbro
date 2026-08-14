//! **Die Umgebung** -- was ein Name bedeutet, und was ein Ort fuer einen Typ hat.
//!
//! Dazu gehoert die **Konstantenauswertung**: `type SlotIdx = u32 in 0 ..< NSLOTS` ist ohne
//! sie ein Bereich ohne Grenzen, und dann sagt M1 nichts. `constexpr` ist zur
//! Uebersetzungszeit auswertbar -- kein Praeprozessor, keine Textersetzung.
//!
//! **Was hier nicht aufgeloest wird, wird `Typ::Unbekannt`, und der Pass zaehlt es.** Ein
//! Pruefer, der einen unbekannten Typ als „passt schon" liest, meldet Gruen ueber Nichts.

use crate::typen::{grenzen, IntBereich, Typ};
use gabbro_syntax::ast::*;
use gabbro_syntax::kw::Kw;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct Signatur {
    pub parameter: Vec<(String, Typ)>,
    pub ergebnis: Option<Typ>,
    pub span: gabbro_syntax::span::Span,
}

#[derive(Default)]
pub struct Umgebung {
    roh_typen: HashMap<String, TypDecl>,
    roh_konst: HashMap<String, Expr>,
    pub typen: HashMap<String, Typ>,
    pub konstanten: HashMap<String, i128>,
    /// Tabellenname -> Slotfelder.
    pub tabellen: HashMap<String, Vec<(String, Typ)>>,
    pub formate: HashMap<String, Vec<(String, Typ)>>,
    pub geraete: HashMap<String, Vec<(String, Typ)>>,
    /// `static`, `atomic`, `accumulates` -- alles, was ohne Deklaration im Rumpf sichtbar ist.
    pub globale: HashMap<String, Typ>,
    pub funktionen: HashMap<String, Signatur>,
}

impl Umgebung {
    pub fn sammle(baum: &Programm) -> Umgebung {
        let mut u = Umgebung::default();
        u.sammle_roh(&baum.items);
        // Konstanten zuerst: die Bereiche der Typen haengen an ihnen.
        let namen: Vec<String> = u.roh_konst.keys().cloned().collect();
        for n in namen {
            let mut unterwegs = HashSet::new();
            if let Some(w) = u.konst_aufloesen(&n, &mut unterwegs) {
                u.konstanten.insert(n, w);
            }
        }
        let namen: Vec<String> = u.roh_typen.keys().cloned().collect();
        for n in namen {
            let mut unterwegs = HashSet::new();
            let t = u.typ_aufloesen(&n, &mut unterwegs);
            u.typen.insert(n, t);
        }
        u.sammle_traeger(&baum.items);
        u
    }

    fn sammle_roh(&mut self, items: &[Item]) {
        for i in items {
            match &i.art {
                ItemArt::Modul(m) => self.sammle_roh(&m.items),
                ItemArt::Typ(t) => {
                    self.roh_typen.insert(t.name.text.clone(), t.clone());
                }
                ItemArt::Konst(k) => {
                    self.roh_konst.insert(k.name.text.clone(), k.wert.clone());
                }
                ItemArt::Tabelle(t) => {
                    for k in &t.konstanten {
                        self.roh_konst.insert(k.name.text.clone(), k.wert.clone());
                    }
                }
                _ => {}
            }
        }
    }

    /// Traeger sind alles, was einen Typ hat, aber keinen erzeugt.
    fn sammle_traeger(&mut self, items: &[Item]) {
        for i in items {
            match &i.art {
                ItemArt::Modul(m) => self.sammle_traeger(&m.items),
                ItemArt::Konst(k) => {
                    let t = self.typ_von_ausdruck_decl(&k.typ);
                    self.globale.insert(k.name.text.clone(), t);
                }
                ItemArt::Statisch(s) => {
                    let t = self.typ_von_ausdruck_decl(&s.typ);
                    self.globale.insert(s.name.text.clone(), t);
                }
                ItemArt::Atomic(a) => {
                    let t = self.typ_von_ausdruck_decl(&a.typ);
                    self.globale.insert(a.name.text.clone(), t);
                }
                ItemArt::Accumulates(a) => {
                    let t = self.typ_von_ausdruck_decl(&a.typ);
                    self.globale.insert(a.name.text.clone(), t);
                }
                ItemArt::Tabelle(t) => {
                    let felder = t
                        .slot
                        .as_ref()
                        .map(|s| {
                            s.felder
                                .iter()
                                .map(|f| (f.name.text.clone(), self.typ_von_slottyp(&f.typ)))
                                .collect::<Vec<_>>()
                        })
                        .unwrap_or_default();
                    self.tabellen.insert(t.name.text.clone(), felder);
                }
                ItemArt::Format(f) => {
                    let felder = f
                        .felder
                        .iter()
                        .map(|fd| (fd.name.text.clone(), self.typ_von_feld(fd)))
                        .collect();
                    self.formate.insert(f.name.text.clone(), felder);
                }
                ItemArt::Device(d) => {
                    let mut felder = Vec::new();
                    for r in &d.register {
                        felder.push((r.name.text.clone(), self.typ_von_reg(r)));
                    }
                    for b in &d.baenke {
                        let inner: Vec<(String, Typ)> = b
                            .register
                            .iter()
                            .map(|r| (r.name.text.clone(), self.typ_von_reg(r)))
                            .collect();
                        felder.push((
                            b.name.text.clone(),
                            Typ::Feld {
                                element: Box::new(Typ::Verbund(inner)),
                                laenge: self.konst_wert(&b.anzahl).map(|v| v.max(0) as u128),
                            },
                        ));
                    }
                    self.geraete.insert(d.name.text.clone(), felder);
                }
                ItemArt::Funktion(f) => {
                    let sig = Signatur {
                        parameter: f
                            .parameter
                            .iter()
                            .map(|p| (p.name.text.clone(), self.typ_von_ausdruck_decl(&p.typ)))
                            .collect(),
                        ergebnis: f.ergebnis.as_ref().map(|t| self.typ_von_ausdruck_decl(t)),
                        span: f.span,
                    };
                    self.funktionen.insert(f.name.text.clone(), sig);
                }
                ItemArt::Axiom(a) => {
                    let sig = Signatur {
                        parameter: a
                            .parameter
                            .iter()
                            .map(|p| (p.name.text.clone(), self.typ_von_ausdruck_decl(&p.typ)))
                            .collect(),
                        ergebnis: None,
                        span: a.span,
                    };
                    self.funktionen.insert(a.name.text.clone(), sig);
                }
                _ => {}
            }
        }
    }

    // -- Konstanten ---------------------------------------------------------------------

    fn konst_aufloesen(&self, name: &str, unterwegs: &mut HashSet<String>) -> Option<i128> {
        if let Some(w) = self.konstanten.get(name) {
            return Some(*w);
        }
        if !unterwegs.insert(name.to_string()) {
            return None; // Zyklus -- kein Wert, keine Behauptung.
        }
        let e = self.roh_konst.get(name)?.clone();
        self.auswerten(&e, unterwegs)
    }

    /// Der Wert eines `constexpr`, wenn er zur Uebersetzungszeit feststeht.
    pub fn konst_wert(&self, e: &Expr) -> Option<i128> {
        let mut unterwegs = HashSet::new();
        self.auswerten(e, &mut unterwegs)
    }

    fn auswerten(&self, e: &Expr, unterwegs: &mut HashSet<String>) -> Option<i128> {
        match &e.art {
            ExprArt::Zahl(v) => i128::try_from(*v).ok(),
            ExprArt::Wahr => Some(1),
            ExprArt::Falsch => Some(0),
            ExprArt::Klammer(i) => self.auswerten(i, unterwegs),
            ExprArt::Unaer(UnOp::Negativ, i) => self.auswerten(i, unterwegs).map(|v| -v),
            ExprArt::Unaer(UnOp::Nicht, i) => {
                self.auswerten(i, unterwegs).map(|v| i128::from(v == 0))
            }
            ExprArt::Ort(o) => {
                // `u64::max` und `i32::min` -- die Grenzen einer Breite als Konstante.
                if o.suffixe.len() == 1 {
                    if let (Some(kw), OrtSuffix::Feld(f)) =
                        (Kw::suche(&o.basis.text), &o.suffixe[0])
                    {
                        if kw.ist_intty() {
                            let (breite, vz) = breite_von(kw);
                            let (lo, hi) = grenzen(breite, vz);
                            return match f.text.as_str() {
                                "max" => Some(hi),
                                "min" => Some(lo),
                                _ => None,
                            };
                        }
                    }
                }
                if !o.suffixe.is_empty() {
                    return None;
                }
                self.konst_aufloesen(&o.basis.text, unterwegs)
            }
            ExprArt::Binaer(op, a, b) => {
                let x = self.auswerten(a, unterwegs)?;
                let y = self.auswerten(b, unterwegs)?;
                Some(match op {
                    BinOp::Plus => x.checked_add(y)?,
                    BinOp::Minus => x.checked_sub(y)?,
                    BinOp::Mal => x.checked_mul(y)?,
                    BinOp::Geteilt => {
                        if y == 0 {
                            return None;
                        }
                        x / y
                    }
                    BinOp::Rest => {
                        if y == 0 {
                            return None;
                        }
                        x % y
                    }
                    BinOp::BitUnd => x & y,
                    BinOp::BitOder => x | y,
                    BinOp::BitXor => x ^ y,
                    BinOp::SchiebLinks => {
                        if !(0..127).contains(&y) {
                            return None;
                        }
                        x.checked_shl(y as u32)?
                    }
                    BinOp::SchiebRechts => {
                        if !(0..127).contains(&y) {
                            return None;
                        }
                        x >> y
                    }
                    BinOp::Gleich => i128::from(x == y),
                    BinOp::Ungleich => i128::from(x != y),
                    BinOp::Kleiner => i128::from(x < y),
                    BinOp::KleinerGleich => i128::from(x <= y),
                    BinOp::Groesser => i128::from(x > y),
                    BinOp::GroesserGleich => i128::from(x >= y),
                    BinOp::Und => i128::from(x != 0 && y != 0),
                    BinOp::Oder => i128::from(x != 0 || y != 0),
                })
            }
            // `sizeof`/`lenof` brauchen das Layout; das entscheidet die Absenkung, nicht M1.
            _ => None,
        }
    }

    // -- Typen --------------------------------------------------------------------------

    fn typ_aufloesen(&self, name: &str, unterwegs: &mut HashSet<String>) -> Typ {
        if let Some(t) = self.typen.get(name) {
            return t.clone();
        }
        if !unterwegs.insert(name.to_string()) {
            return Typ::Unbekannt;
        }
        let Some(d) = self.roh_typen.get(name) else {
            return Typ::Unbekannt;
        };
        let unter = match &d.rumpf {
            Some(r) => self.typexpr(r, unterwegs),
            // `linear type Parked;` -- ein Typ ohne Rumpf traegt nur seinen Namen.
            None => Typ::Unbekannt,
        };
        if d.tagged {
            if let Typ::Summe { varianten, .. } = unter {
                return Typ::Summe {
                    name: name.to_string(),
                    varianten,
                };
            }
        }
        Typ::Benannt {
            name: name.to_string(),
            undurchsichtig: d.opaque,
            unter: Box::new(unter),
        }
    }

    pub fn typ_von_ausdruck_decl(&self, t: &TypExpr) -> Typ {
        let mut unterwegs = HashSet::new();
        self.typexpr(t, &mut unterwegs)
    }

    fn typexpr(&self, t: &TypExpr, unterwegs: &mut HashSet<String>) -> Typ {
        match t {
            TypExpr::Int(i) => Typ::Ganzzahl(self.intbereich(i, unterwegs)),
            TypExpr::Bool(_) => Typ::Wahrheit,
            TypExpr::Never(_) => Typ::Nie,
            TypExpr::Pfad(p) => {
                let name = p
                    .teile
                    .last()
                    .map(|i| i.text.clone())
                    .unwrap_or_default();
                if self.roh_typen.contains_key(&name) {
                    self.typ_aufloesen(&name, unterwegs)
                } else if self.tabellen.contains_key(&name) || self.ist_tabelle(&name) {
                    Typ::Tabelle(name)
                } else if self.ist_format(&name) || self.ist_geraet(&name) {
                    Typ::Verbundname(name)
                } else {
                    Typ::Unbekannt
                }
            }
            TypExpr::Feld(a) => Typ::Feld {
                element: Box::new(self.typexpr(&a.element, unterwegs)),
                laenge: self.konst_wert(&a.laenge).map(|v| v.max(0) as u128),
            },
            TypExpr::Zeiger(p) => Typ::Zeiger(Box::new(self.typexpr(&p.ziel, unterwegs))),
            TypExpr::Verbund(felder, _) => Typ::Verbund(
                felder
                    .iter()
                    .map(|f| (f.name.text.clone(), self.typ_von_feld(f)))
                    .collect(),
            ),
            TypExpr::FnZeiger(_) => Typ::Unbekannt,
            TypExpr::Varianten(v, _) => Typ::Summe {
                name: String::new(),
                varianten: v
                    .iter()
                    .map(|va| {
                        (
                            va.name.text.clone(),
                            va.nutzlast.as_ref().map(|n| self.typexpr(n, unterwegs)),
                        )
                    })
                    .collect(),
            },
        }
    }

    fn intbereich(&self, i: &IntTy, unterwegs: &mut HashSet<String>) -> IntBereich {
        let (breite, vz) = breite_von(i.wort);
        let Some(b) = &i.bereich else {
            return IntBereich::voll(breite, vz);
        };
        let von = self.auswerten(&b.von, &mut unterwegs.clone());
        let bis = self.auswerten(&b.bis, &mut unterwegs.clone());
        match (von, bis) {
            (Some(lo), Some(hi)) => {
                let hi = if b.exklusiv { hi - 1 } else { hi };
                IntBereich::genau(breite, vz, lo, hi)
            }
            // Eine Grenze, die nicht feststeht, macht den Bereich NICHT enger.
            _ => IntBereich::voll(breite, vz),
        }
    }

    fn typ_von_feld(&self, f: &FeldDecl) -> Typ {
        let mut unterwegs = HashSet::new();
        let grund = self.typexpr(&f.typ.typ, &mut unterwegs);
        match (&f.bitpos, grund.bereich()) {
            // Ein Bitfeld traegt den Bereich seiner Bits, nicht den seines Grundtyps.
            (Some(BitPos::Bit(_)), Some(b)) => {
                Typ::Ganzzahl(IntBereich::genau(b.breite, false, 0, 1))
            }
            (Some(BitPos::Bereich(h, t)), Some(b)) => {
                let breite_feld = (h.max(t) - h.min(t) + 1) as u32;
                let max = if breite_feld >= 127 {
                    b.max
                } else {
                    (1i128 << breite_feld) - 1
                };
                Typ::Ganzzahl(IntBereich::genau(b.breite, false, 0, max.min(b.max)))
            }
            _ => grund,
        }
    }

    fn typ_von_slottyp(&self, s: &SlotTyp) -> Typ {
        let mut unterwegs = HashSet::new();
        match s {
            SlotTyp::Typ(t) => self.typexpr(t, &mut unterwegs),
            // `index into T` traegt seine Schranke aus der Deklaration -- aber `table` nennt
            // keine Slotzahl, also bleibt die Obergrenze offen (s. Befund G8 in TODO.md).
            SlotTyp::Index(t) | SlotTyp::OptionIndex(t) => Typ::Benannt {
                name: format!("index into {}", t.text),
                undurchsichtig: false,
                unter: Box::new(Typ::Ganzzahl(IntBereich::voll(32, false))),
            },
            SlotTyp::Wrapping(i) => Typ::Umlaufend(self.intbereich(i, &mut unterwegs)),
        }
    }

    fn typ_von_reg(&self, r: &RegDecl) -> Typ {
        let mut unterwegs = HashSet::new();
        let bereich = self.intbereich(&r.typ, &mut unterwegs);
        let felder = r
            .felder
            .iter()
            .map(|(name, bp)| {
                let b = match bp {
                    BitPos::Bit(_) => IntBereich::genau(bereich.breite, false, 0, 1),
                    BitPos::Bereich(h, t) => {
                        let w = (h.max(t) - h.min(t) + 1) as u32;
                        let max = if w >= 127 { bereich.max } else { (1i128 << w) - 1 };
                        IntBereich::genau(bereich.breite, false, 0, max)
                    }
                };
                (name.text.clone(), b)
            })
            .collect();
        Typ::Register { bereich, felder }
    }

    fn ist_tabelle(&self, name: &str) -> bool {
        self.tabellen.contains_key(name)
    }
    fn ist_format(&self, name: &str) -> bool {
        self.formate.contains_key(name)
    }
    fn ist_geraet(&self, name: &str) -> bool {
        self.geraete.contains_key(name)
    }

    /// Der Typ eines Ortes, gegeben die lokalen Bindungen.
    pub fn typ_von_ort(&self, ort: &Ort, lokal: &HashMap<String, Typ>) -> Typ {
        let mut aktuell = lokal
            .get(&ort.basis.text)
            .cloned()
            .or_else(|| self.globale.get(&ort.basis.text).cloned())
            .unwrap_or(Typ::Unbekannt);

        for suffix in &ort.suffixe {
            aktuell = match suffix {
                OrtSuffix::Feld(f) | OrtSuffix::Ueber(f) => self.feld_von(&aktuell, &f.text),
                OrtSuffix::Index(_) => match aktuell.durchgreifen() {
                    Typ::Feld { element, .. } => (**element).clone(),
                    _ => Typ::Unbekannt,
                },
            };
            if aktuell.ist_unbekannt() {
                return Typ::Unbekannt;
            }
        }
        aktuell
    }

    pub fn feld_von(&self, traeger: &Typ, name: &str) -> Typ {
        match traeger.durchgreifen() {
            Typ::Tabelle(t) => {
                // `c.slots` ist das Slotfeld der Tabelle; jeder andere Name ist keiner.
                if name == "slots" {
                    let felder = self.tabellen.get(t).cloned().unwrap_or_default();
                    Typ::Feld {
                        element: Box::new(Typ::Verbund(felder)),
                        laenge: None,
                    }
                } else {
                    Typ::Unbekannt
                }
            }
            Typ::Verbundname(n) => {
                let felder = self
                    .formate
                    .get(n)
                    .or_else(|| self.geraete.get(n))
                    .cloned()
                    .unwrap_or_default();
                felder
                    .iter()
                    .find(|(f, _)| f == name)
                    .map(|(_, t)| t.clone())
                    .unwrap_or(Typ::Unbekannt)
            }
            Typ::Verbund(felder) => felder
                .iter()
                .find(|(f, _)| f == name)
                .map(|(_, t)| t.clone())
                .unwrap_or(Typ::Unbekannt),
            Typ::Register { felder, .. } => felder
                .iter()
                .find(|(f, _)| f == name)
                .map(|(_, b)| Typ::Ganzzahl(*b))
                .unwrap_or(Typ::Unbekannt),
            _ => Typ::Unbekannt,
        }
    }
}

pub fn breite_von(k: Kw) -> (u8, bool) {
    match k {
        Kw::U8 => (8, false),
        Kw::U16 => (16, false),
        Kw::U32 => (32, false),
        Kw::U64 => (64, false),
        Kw::I8 => (8, true),
        Kw::I16 => (16, true),
        Kw::I32 => (32, true),
        Kw::I64 => (64, true),
        _ => (64, false),
    }
}
