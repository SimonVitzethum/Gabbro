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
    /// Tabellenname -> `count N`, wenn die Deklaration sie nennt.
    pub kapazitaeten: HashMap<String, u128>,
    pub formate: HashMap<String, Vec<(String, Typ)>>,
    pub geraete: HashMap<String, Vec<(String, Typ)>>,
    /// `static`, `atomic`, `accumulates` -- alles, was ohne Deklaration im Rumpf sichtbar ist.
    pub globale: HashMap<String, Typ>,
    pub funktionen: HashMap<String, Signatur>,
    /// Je Modulpfad die Pfade seiner `use`-Zeilen.
    verwendet: HashMap<String, Vec<String>>,
}

/// Das Modul, in dem ein qualifizierter Name steht.
pub fn modul_von(qualifiziert: &str) -> &str {
    match qualifiziert.rfind("::") {
        Some(i) => &qualifiziert[..i],
        None => "",
    }
}

/// Der letzte Abschnitt eines qualifizierten Namens.
pub fn kurzname(qualifiziert: &str) -> &str {
    qualifiziert.rsplit("::").next().unwrap_or(qualifiziert)
}

/// `""` + `x` = `x`; `a::b` + `x` = `a::b::x`.
fn qualifiziere(pfad: &str, name: &str) -> String {
    if pfad.is_empty() {
        name.to_string()
    } else {
        format!("{pfad}::{name}")
    }
}

impl Umgebung {
    pub fn sammle(baum: &Programm) -> Umgebung {
        let mut u = Umgebung::default();
        u.sammle_roh(&baum.items, "");
        // Konstanten zuerst: die Bereiche der Typen haengen an ihnen.
        let namen: Vec<String> = u.roh_konst.keys().cloned().collect();
        for n in namen {
            let mut unterwegs = HashSet::new();
            if let Some(w) = u.konst_aufloesen(modul_von(&n), kurzname(&n), &mut unterwegs) {
                u.konstanten.insert(n, w);
            }
        }
        let namen: Vec<String> = u.roh_typen.keys().cloned().collect();
        for n in namen {
            let mut unterwegs = HashSet::new();
            let t = u.typ_aufloesen(modul_von(&n), kurzname(&n), &mut unterwegs);
            u.typen.insert(n, t);
        }
        u.sammle_traeger(&baum.items, "");
        u
    }

    /// **Namensaufloesung.** Ein Name gilt zuerst im eigenen Modul, dann in den umgebenden,
    /// dann an der Wurzel, zuletzt ueber eine `use`-Zeile. *Ohne diese Ordnung verdeckt ein
    /// gleichnamiges `fn` in einem fremden Modul die Deklaration -- und mit ihr die
    /// Bereichspruefung, still.*
    fn kandidaten(&self, von: &str, pfad: &str) -> Vec<String> {
        let mut out = Vec::new();
        // Im eigenen Modul und in jedem umgebenden, von innen nach aussen.
        let mut umgebung = von.to_string();
        loop {
            out.push(if umgebung.is_empty() {
                pfad.to_string()
            } else {
                format!("{umgebung}::{pfad}")
            });
            match umgebung.rfind("::") {
                Some(i) => umgebung.truncate(i),
                None => {
                    if umgebung.is_empty() {
                        break;
                    }
                    umgebung.clear();
                }
            }
        }
        // Ueber eine `use`-Zeile des eigenen Moduls: `use a::b::Ding;` macht `Ding` sichtbar.
        let kurz = pfad.rsplit("::").next().unwrap_or(pfad);
        let mut modul = von.to_string();
        loop {
            if let Some(zeilen) = self.verwendet.get(&modul) {
                for z in zeilen {
                    if z.rsplit("::").next() == Some(kurz) {
                        out.push(z.clone());
                    }
                }
            }
            match modul.rfind("::") {
                Some(i) => modul.truncate(i),
                None => {
                    if modul.is_empty() {
                        break;
                    }
                    modul.clear();
                }
            }
        }
        out
    }

    fn suche<'a, T>(
        &self,
        karte: &'a HashMap<String, T>,
        von: &str,
        pfad: &str,
    ) -> Option<&'a T> {
        self.kandidaten(von, pfad)
            .into_iter()
            .find_map(|k| karte.get(&k))
    }

    pub fn funktion(&self, von: &str, pfad: &Pfad) -> Option<&Signatur> {
        self.suche(&self.funktionen, von, &pfad.text())
    }

    fn sammle_roh(&mut self, items: &[Item], pfad: &str) {
        for i in items {
            match &i.art {
                ItemArt::Modul(m) => {
                    let innen = qualifiziere(pfad, &m.pfad.text());
                    self.sammle_roh(&m.items, &innen);
                }
                ItemArt::Use(u) => {
                    self.verwendet
                        .entry(pfad.to_string())
                        .or_default()
                        .push(u.pfad.text());
                }
                ItemArt::Typ(t) => {
                    self.roh_typen
                        .insert(qualifiziere(pfad, &t.name.text), t.clone());
                }
                ItemArt::Konst(k) => {
                    self.roh_konst
                        .insert(qualifiziere(pfad, &k.name.text), k.wert.clone());
                }
                ItemArt::Tabelle(t) => {
                    // Die Konstanten einer Tabelle gehoeren in ihren Modulpfad, nicht in
                    // den der Tabelle -- `table` ist kein Geltungsbereich der Grammatik.
                    for k in &t.konstanten {
                        self.roh_konst
                            .insert(qualifiziere(pfad, &k.name.text), k.wert.clone());
                    }
                }
                _ => {}
            }
        }
    }

    /// Traeger sind alles, was einen Typ hat, aber keinen erzeugt.
    fn sammle_traeger(&mut self, items: &[Item], pfad: &str) {
        for i in items {
            let q = |name: &str| qualifiziere(pfad, name);
            match &i.art {
                ItemArt::Modul(m) => {
                    let innen = qualifiziere(pfad, &m.pfad.text());
                    self.sammle_traeger(&m.items, &innen);
                }
                ItemArt::Konst(k) => {
                    let t = self.typ_von_ausdruck_decl(pfad, &k.typ);
                    self.globale.insert(q(&k.name.text), t);
                }
                ItemArt::Statisch(s) => {
                    let t = self.typ_von_ausdruck_decl(pfad, &s.typ);
                    self.globale.insert(q(&s.name.text), t);
                }
                ItemArt::Atomic(a) => {
                    let t = self.typ_von_ausdruck_decl(pfad, &a.typ);
                    self.globale.insert(q(&a.name.text), t);
                }
                ItemArt::Accumulates(a) => {
                    let t = self.typ_von_ausdruck_decl(pfad, &a.typ);
                    self.globale.insert(q(&a.name.text), t);
                }
                ItemArt::Tabelle(t) => {
                    let felder = t
                        .slot
                        .as_ref()
                        .map(|s| {
                            s.felder
                                .iter()
                                .map(|f| (f.name.text.clone(), self.typ_von_slottyp(pfad, &f.typ)))
                                .collect::<Vec<_>>()
                        })
                        .unwrap_or_default();
                    if let Some(n) = t
                        .kapazitaet
                        .as_ref()
                        .and_then(|e| self.konst_wert(pfad, e))
                        .filter(|n| *n > 0)
                    {
                        self.kapazitaeten.insert(q(&t.name.text), n as u128);
                    }
                    self.tabellen.insert(q(&t.name.text), felder);
                }
                ItemArt::Format(f) => {
                    let felder = f
                        .felder
                        .iter()
                        .map(|fd| (fd.name.text.clone(), self.typ_von_feld(pfad, fd)))
                        .collect();
                    self.formate.insert(q(&f.name.text), felder);
                }
                ItemArt::Device(d) => {
                    let mut felder = Vec::new();
                    for r in &d.register {
                        felder.push((r.name.text.clone(), self.typ_von_reg(pfad, r)));
                    }
                    for b in &d.baenke {
                        let inner: Vec<(String, Typ)> = b
                            .register
                            .iter()
                            .map(|r| (r.name.text.clone(), self.typ_von_reg(pfad, r)))
                            .collect();
                        felder.push((
                            b.name.text.clone(),
                            Typ::Feld {
                                element: Box::new(Typ::Verbund(inner)),
                                laenge: self.konst_wert(pfad, &b.anzahl).map(|v| v.max(0) as u128),
                            },
                        ));
                    }
                    self.geraete.insert(q(&d.name.text), felder);
                }
                ItemArt::Funktion(f) => {
                    let sig = Signatur {
                        parameter: f
                            .parameter
                            .iter()
                            .map(|p| (p.name.text.clone(), self.typ_von_ausdruck_decl(pfad, &p.typ)))
                            .collect(),
                        ergebnis: f.ergebnis.as_ref().map(|t| self.typ_von_ausdruck_decl(pfad, t)),
                        span: f.span,
                    };
                    self.funktionen.insert(q(&f.name.text), sig);
                }
                ItemArt::Axiom(a) => {
                    let sig = Signatur {
                        parameter: a
                            .parameter
                            .iter()
                            .map(|p| (p.name.text.clone(), self.typ_von_ausdruck_decl(pfad, &p.typ)))
                            .collect(),
                        ergebnis: None,
                        span: a.span,
                    };
                    self.funktionen.insert(q(&a.name.text), sig);
                }
                _ => {}
            }
        }
    }

    // -- Konstanten ---------------------------------------------------------------------

    fn konst_aufloesen(
        &self,
        von: &str,
        pfad: &str,
        unterwegs: &mut HashSet<String>,
    ) -> Option<i128> {
        let voll = self
            .kandidaten(von, pfad)
            .into_iter()
            .find(|k| self.konstanten.contains_key(k) || self.roh_konst.contains_key(k))?;
        if let Some(w) = self.konstanten.get(&voll) {
            return Some(*w);
        }
        if !unterwegs.insert(voll.clone()) {
            return None; // Zyklus -- kein Wert, keine Behauptung.
        }
        let e = self.roh_konst.get(&voll)?.clone();
        self.auswerten(modul_von(&voll), &e, unterwegs)
    }

    /// Der Wert eines `constexpr`, wenn er zur Uebersetzungszeit feststeht.
    pub fn konst_wert(&self, von: &str, e: &Expr) -> Option<i128> {
        let mut unterwegs = HashSet::new();
        self.auswerten(von, e, &mut unterwegs)
    }

    fn auswerten(&self, von: &str, e: &Expr, unterwegs: &mut HashSet<String>) -> Option<i128> {
        match &e.art {
            ExprArt::Zahl(v) => i128::try_from(*v).ok(),
            ExprArt::Wahr => Some(1),
            ExprArt::Falsch => Some(0),
            ExprArt::Klammer(i) => self.auswerten(von, i, unterwegs),
            ExprArt::Unaer(UnOp::Negativ, i) => self.auswerten(von, i, unterwegs).map(|v| -v),
            ExprArt::Unaer(UnOp::Nicht, i) => {
                self.auswerten(von, i, unterwegs).map(|v| i128::from(v == 0))
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
                self.konst_aufloesen(von, &o.basis.text, unterwegs)
            }
            ExprArt::Binaer(op, a, b) => {
                let x = self.auswerten(von, a, unterwegs)?;
                let y = self.auswerten(von, b, unterwegs)?;
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

    fn typ_aufloesen(&self, von: &str, pfad: &str, unterwegs: &mut HashSet<String>) -> Typ {
        let Some(voll) = self
            .kandidaten(von, pfad)
            .into_iter()
            .find(|k| self.typen.contains_key(k) || self.roh_typen.contains_key(k))
        else {
            return Typ::Unbekannt;
        };
        let name = voll.as_str();
        if let Some(t) = self.typen.get(name) {
            return t.clone();
        }
        if !unterwegs.insert(name.to_string()) {
            return Typ::Unbekannt;
        }
        let Some(d) = self.roh_typen.get(name) else {
            return Typ::Unbekannt;
        };
        let d = d.clone();
        let von = modul_von(name).to_string();
        let von = von.as_str();
        let unter = match &d.rumpf {
            Some(r) => self.typexpr(von, r, unterwegs),
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

    pub fn typ_von_ausdruck_decl(&self, von: &str, t: &TypExpr) -> Typ {
        let mut unterwegs = HashSet::new();
        self.typexpr(von, t, &mut unterwegs)
    }

    fn typexpr(&self, von: &str, t: &TypExpr, unterwegs: &mut HashSet<String>) -> Typ {
        match t {
            TypExpr::Int(i) => Typ::Ganzzahl(self.intbereich(von, i, unterwegs)),
            TypExpr::Bool(_) => Typ::Wahrheit,
            TypExpr::Never(_) => Typ::Nie,
            TypExpr::Pfad(p) => {
                let name = p
                    .teile
                    .last()
                    .map(|i| i.text.clone())
                    .unwrap_or_default();
                // Der Name wird HIER aufgeloest, im Modul des Gebrauchs -- ein
                // gleichnamiger Typ in einem fremden Modul verdeckt ihn damit nicht mehr.
                let kand = self.kandidaten(von, &name);
                if let Some(k) = kand.iter().find(|k| self.roh_typen.contains_key(*k)) {
                    let k = k.clone();
                    self.typ_aufloesen(modul_von(&k), kurzname(&k), unterwegs)
                } else if let Some(k) = kand.iter().find(|k| self.tabellen.contains_key(*k)) {
                    Typ::Tabelle(k.clone())
                } else if let Some(k) = kand
                    .iter()
                    .find(|k| self.formate.contains_key(*k) || self.geraete.contains_key(*k))
                {
                    Typ::Verbundname(k.clone())
                } else {
                    Typ::Unbekannt
                }
            }
            TypExpr::Feld(a) => Typ::Feld {
                element: Box::new(self.typexpr(von, &a.element, unterwegs)),
                laenge: self.konst_wert(von, &a.laenge).map(|v| v.max(0) as u128),
            },
            TypExpr::Zeiger(p) => Typ::Zeiger(Box::new(self.typexpr(von, &p.ziel, unterwegs))),
            TypExpr::Verbund(felder, _) => Typ::Verbund(
                felder
                    .iter()
                    .map(|f| (f.name.text.clone(), self.typ_von_feld(von, f)))
                    .collect(),
            ),
            TypExpr::FnZeiger(_) => Typ::Unbekannt,
            // **A3.** `index into T` erbt die Schranke aus `T`s `count`. Ohne `count` bleibt
            // sie offen -- und das ist dann eine Aussage der Deklaration, keine Konvention.
            TypExpr::Index { tabelle, .. } => {
                let bereich = self
                    .kandidaten(von, &tabelle.text)
                    .into_iter()
                    .find_map(|k| self.kapazitaeten.get(&k).copied())
                    .map(|n| IntBereich::genau(32, false, 0, n as i128 - 1))
                    .unwrap_or_else(|| IntBereich::voll(32, false));
                Typ::Benannt {
                    name: format!("index into {}", tabelle.text),
                    undurchsichtig: false,
                    unter: Box::new(Typ::Ganzzahl(bereich)),
                }
            }
            TypExpr::Varianten(v, _) => Typ::Summe {
                name: String::new(),
                varianten: v
                    .iter()
                    .map(|va| {
                        (
                            va.name.text.clone(),
                            va.nutzlast.as_ref().map(|n| self.typexpr(von, n, unterwegs)),
                        )
                    })
                    .collect(),
            },
        }
    }

    fn intbereich(&self, von: &str, i: &IntTy, unterwegs: &mut HashSet<String>) -> IntBereich {
        let (breite, vz) = breite_von(i.wort);
        let Some(b) = &i.bereich else {
            return IntBereich::voll(breite, vz);
        };
        let untere = self.auswerten(von, &b.von, &mut unterwegs.clone());
        let obere = self.auswerten(von, &b.bis, &mut unterwegs.clone());
        match (untere, obere) {
            (Some(lo), Some(hi)) => {
                let hi = if b.exklusiv { hi - 1 } else { hi };
                IntBereich::genau(breite, vz, lo, hi)
            }
            // Eine Grenze, die nicht feststeht, macht den Bereich NICHT enger.
            _ => IntBereich::voll(breite, vz),
        }
    }

    fn typ_von_feld(&self, von: &str, f: &FeldDecl) -> Typ {
        let mut unterwegs = HashSet::new();
        let grund = self.typexpr(von, &f.typ.typ, &mut unterwegs);
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

    fn typ_von_slottyp(&self, von: &str, s: &SlotTyp) -> Typ {
        let mut unterwegs = HashSet::new();
        match s {
            SlotTyp::Typ(t) => self.typexpr(von, t, &mut unterwegs),
            SlotTyp::Wrapping(i) => Typ::Umlaufend(self.intbereich(von, i, &mut unterwegs)),
        }
    }

    fn typ_von_reg(&self, von: &str, r: &RegDecl) -> Typ {
        let mut unterwegs = HashSet::new();
        let bereich = self.intbereich(von, &r.typ, &mut unterwegs);
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

    /// Der Typ eines Ortes, gegeben die lokalen Bindungen.
    pub fn typ_von_ort(&self, von: &str, ort: &Ort, lokal: &HashMap<String, Typ>) -> Typ {
        let mut aktuell = lokal
            .get(&ort.basis.text)
            .cloned()
            .or_else(|| self.suche(&self.globale, von, &ort.basis.text).cloned())
            .unwrap_or(Typ::Unbekannt);

        for suffix in &ort.suffixe {
            aktuell = match suffix {
                OrtSuffix::Feld(f) | OrtSuffix::Ueber(f) => self.feld_von(von, &aktuell, &f.text),
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

    pub fn feld_von(&self, _von: &str, traeger: &Typ, name: &str) -> Typ {
        match traeger.durchgreifen() {
            Typ::Tabelle(t) => {
                // `c.slots` ist das Slotfeld der Tabelle; jeder andere Name ist keiner.
                if name == "slots" {
                    let felder = self.tabellen.get(t).cloned().unwrap_or_default();
                    Typ::Feld {
                        element: Box::new(Typ::Verbund(felder)),
                        // **A3.** Mit `count N` bekommt M4 hier zum ersten Mal eine
                        // Schranke aus der Sprache statt aus einer Konvention.
                        laenge: self.kapazitaeten.get(t).copied(),
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
