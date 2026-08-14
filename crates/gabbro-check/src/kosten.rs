//! **Pass 9 -- `costs`. Und ohne ihn ist Terminierung deklariert statt geprueft.**
//!
//! > *„`costs` zaehlt Operationen, und die Einheit ist definiert: 1 op = eine
//! > Gabbro-Primitive (Zuweisung, arithmetische Operation, Laden, Speichern; ein Aufruf
//! > zaehlt die deklarierten `costs` des Gerufenen; eine Traversierung zaehlt Rumpfkosten ×
//! > Domaenenschranke; Zweige zaehlen das Maximum). Das ist eine **Eigenschaft des
//! > Programms**, statisch ausgerechnet, keine Zeitmessung."*
//! > ([`SPRACHE.md`](SPRACHE.md) §7)
//!
//! **Bis dieser Pass stand, waren `costs`, `held`, `per_pass` und `bounded` Deklarationen,
//! die niemand nachrechnete.** Damit galt: `retry … bounded N ops` **behauptete**
//! Terminierung, es prueft sie nicht; die Sperrhaltezeit, an der die ganze Latenzaussage
//! haengt, war unbelegt; und `forever` -- die einzige Form, die unendlich laufen darf --
//! trug ihre Rechtfertigung in einer ungeprueften Zahl.
//!
//! ## Die drei Absagen
//!
//! | | |
//! |---|---|
//! | `K001` | der Rumpf kostet mehr, als die Funktion deklariert |
//! | `K002` | ein `locks`-Block kostet mehr, als die Sperre als `held` deklariert |
//! | `K003` | ein Aufruf nennt eine Funktion **ohne** `costs` in einem Rumpf, der welche zusagt -- die Zusage waere dann eine Zahl ueber Unbekanntem |
//!
//! ## Was der Pass NICHT tut
//!
//! * **Rekursion.** Ein Aufruf zaehlt die **deklarierten** `costs` des Gerufenen, nicht
//!   seine gerechneten. Bei einem Zyklus zaehlt jede Kante einmal -- die Deklaration traegt
//!   die Terminierung, nicht die Rechnung. Das ist die Absicht (§7: *„ein Aufruf zaehlt die
//!   deklarierten `costs`"*), aber es heisst: **`costs` an einer rekursiven Funktion ist eine
//!   Annahme**, kein Ergebnis.
//! * **`per_pass` gegen den Rumpf einer `forever`** wird geprueft; die Schranke **darf von
//!   Eingaben abhaengen** (§9.3, `64 + 12 * lenof(msg)`), und dann ist sie nicht konstant
//!   auswertbar. In dem Fall schweigt der Pass -- und zaehlt es.

use crate::umgebung::Umgebung;
use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::HashMap;

/// Was der Pass nachrechnen konnte -- die Zahl steht neben dem Ergebnis.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Zaehlung {
    /// Funktionen mit `costs`, deren Rumpf ausgerechnet werden konnte.
    pub gerechnet: usize,
    /// Funktionen mit `costs`, bei denen etwas im Rumpf keine Zahl hatte.
    pub offen: usize,
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) -> Zaehlung {
    let u = Umgebung::sammle(baum);
    let mut deklariert: HashMap<String, i128> = HashMap::new();
    let mut haltezeiten: HashMap<String, i128> = HashMap::new();
    let mut geteilte_haltezeiten: HashMap<String, i128> = HashMap::new();

    // Erst alle Deklarationen einsammeln: ein Aufruf zaehlt die deklarierten Kosten des
    // Gerufenen, und der kann weiter unten stehen.
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| match &item.art {
        ItemArt::Funktion(f) => {
            if let Some(c) = &f.costs {
                if let Some(n) = u.konst_wert(modul, c) {
                    deklariert.insert(f.name.text.clone(), n);
                }
            }
        }
        ItemArt::Lock(l) => {
            if let Some(h) = &l.haltezeit {
                if let Some(n) = u.konst_wert(modul, h) {
                    haltezeiten.insert(l.name.text.clone(), n);
                }
            }
            if let Some(h) = &l.geteilte_haltezeit {
                if let Some(n) = u.konst_wert(modul, h) {
                    geteilte_haltezeiten.insert(l.name.text.clone(), n);
                }
            }
        }
        _ => {}
    });

    let mut z = Zaehlung::default();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let lokal = f
            .parameter
            .iter()
            .map(|p| (p.name.text.clone(), u.typ_von_ausdruck_decl(modul, &p.typ)))
            .collect();
        let r = Rechner {
            u: &u,
            modul,
            deklariert: &deklariert,
            haltezeiten: &haltezeiten,
            geteilte_haltezeiten: &geteilte_haltezeiten,
            lokal,
        };

        // -- K002: jeder `locks`-Block gegen die `held`-Zusage seiner Sperre.
        r.sperrbloecke(b, absagen);

        let Some(zusage_expr) = &f.costs else {
            return;
        };
        let Some(zusage) = u.konst_wert(modul, zusage_expr) else {
            return;
        };
        match r.block(b) {
            Kosten::Zahl(n) => {
                z.gerechnet += 1;
                if n > zusage {
                    absagen.schiebe(
                        Absage::fehler(
                            "K001",
                            zusage_expr.span,
                            format!(
                                "`{}` sagt <= {zusage} ops zu, der Rumpf kostet {n}",
                                f.name.text
                            ),
                        )
                        .mit_notiz(
                            "SPRACHE.md §7: 1 op = eine Gabbro-Primitive; ein Aufruf zaehlt \
                             die deklarierten `costs` des Gerufenen, eine Traversierung \
                             Rumpfkosten x Domaenenschranke, Zweige das Maximum",
                        )
                        .mit_notiz(
                            "die Zahl ist statisch ausgerechnet -- sie zu senken heisst, \
                             den Rumpf zu aendern, nicht die Zusage",
                        ),
                    );
                }
            }
            Kosten::Unbekannt(grund, span) => {
                z.offen += 1;
                if let Some(span) = span {
                    absagen.schiebe(
                        Absage::fehler(
                            "K003",
                            span,
                            format!(
                                "`{}` sagt Kosten zu, aber {grund}",
                                f.name.text
                            ),
                        )
                        .mit_notiz(
                            "eine Kostenzusage ueber einer unbekannten Groesse ist eine Zahl \
                             ueber Unbekanntem -- entweder der Gerufene bekommt `costs`, \
                             oder der Rufer gibt seine Zusage auf",
                        ),
                    );
                }
            }
        }
    });
    z
}

/// Kosten eines Rumpfteils -- oder der Grund, warum sie nicht feststehen.
enum Kosten {
    Zahl(i128),
    Unbekannt(String, Option<Span>),
}

impl Kosten {
    fn plus(self, andere: Kosten) -> Kosten {
        match (self, andere) {
            (Kosten::Zahl(a), Kosten::Zahl(b)) => Kosten::Zahl(a + b),
            (Kosten::Unbekannt(g, s), _) => Kosten::Unbekannt(g, s),
            (_, u) => u,
        }
    }
}

struct Rechner<'a> {
    u: &'a Umgebung,
    modul: &'a str,
    deklariert: &'a HashMap<String, i128>,
    haltezeiten: &'a HashMap<String, i128>,
    /// **Der eigene Zweig der geteilten Seite** (MESSUNGEN.md, Nebenbefund N3): `held` ist
    /// fuer exklusive Halter gedacht, und der Kostenpass rechnete bis dahin nur den.
    geteilte_haltezeiten: &'a HashMap<String, i128>,
    /// Die Parameter der Funktion. **Ohne sie hat `c` in `slots of c` keinen Typ**, und die
    /// Domaenenschranke ist unauffindbar -- der Pass haette dann jede Traversierung als
    /// unbekannt gemeldet und damit seine eigene Blindheit gezaehlt.
    lokal: HashMap<String, crate::typen::Typ>,
}

impl<'a> Rechner<'a> {
    /// **Die Summationsregel, und sie ist eine Aussage ueber das Modell:** Anweisungen
    /// addieren sich -- ausser hinter einem Zweig, der **immer verlaesst**. Was nach
    /// `if x { return … }` steht, liegt auf dem ANDEREN Weg, nicht hinter beiden.
    /// Ohne diese Regel zahlt jeder fruehe Rueckstieg zweimal, und die Zahl misst einen
    /// Weg, den kein Durchlauf nimmt.
    fn block(&self, b: &Block) -> Kosten {
        let mut summe = Kosten::Zahl(0);
        for (i, s) in b.anweisungen.iter().enumerate() {
            if let StmtArt::Wenn(w) = &s.art {
                if w.sonst.is_none() && w.zweige.len() == 1 {
                    let (bed, rumpf) = &w.zweige[0];
                    if endet_immer(rumpf) {
                        // Zwei Wege: durch den Zweig, oder daran vorbei und weiter.
                        let durch = self.ausdruck(bed).plus(self.block(rumpf));
                        let vorbei = self.ausdruck(bed).plus(self.rest(&b.anweisungen[i + 1..]));
                        return summe.plus(groesser(durch, vorbei));
                    }
                }
            }
            summe = summe.plus(self.anweisung(s));
        }
        summe
    }

    fn rest(&self, anweisungen: &[Stmt]) -> Kosten {
        let mut summe = Kosten::Zahl(0);
        for (i, s) in anweisungen.iter().enumerate() {
            if let StmtArt::Wenn(w) = &s.art {
                if w.sonst.is_none() && w.zweige.len() == 1 {
                    let (bed, rumpf) = &w.zweige[0];
                    if endet_immer(rumpf) {
                        let durch = self.ausdruck(bed).plus(self.block(rumpf));
                        let vorbei = self.ausdruck(bed).plus(self.rest(&anweisungen[i + 1..]));
                        return summe.plus(groesser(durch, vorbei));
                    }
                }
            }
            summe = summe.plus(self.anweisung(s));
        }
        summe
    }

    fn anweisung(&self, s: &Stmt) -> Kosten {
        match &s.art {
            // Eine Zuweisung ist eine Primitive, dazu was der Ausdruck kostet.
            StmtArt::Let(l) => Kosten::Zahl(1).plus(self.ausdruck(&l.wert)),
            StmtArt::Zuweisung(z) => Kosten::Zahl(1).plus(self.ausdruck(&z.wert)),
            StmtArt::Publish(p) => Kosten::Zahl(1).plus(self.ausdruck(&p.wert)),
            StmtArt::AwaitLoad(_) => Kosten::Zahl(1),
            // `narrow` senkt sich auf eine Bereichspruefung ab -- eine Rechenoperation.
            StmtArt::Exchange(e) => match &e.form {
                XForm::Update { rumpf, .. } => Kosten::Zahl(1).plus(self.block(rumpf)),
                XForm::Vergleich { wert, .. } => Kosten::Zahl(1).plus(self.ausdruck(wert)),
            },
            StmtArt::LetSonst(l) => {
                Kosten::Zahl(1).plus(self.ruf(&l.ruf)).plus(self.block(&l.sonst))
            }
            StmtArt::Ruf(r) => self.ruf(r),
            // Ein Ruecksprung ist keine der vier Primitiven; sein Ausdruck kostet.
            StmtArt::Return(Some(e)) => self.ausdruck(e),
            StmtArt::Return(None) | StmtArt::Leave(_) | StmtArt::Next(_) => Kosten::Zahl(0),
            // **Zweige zaehlen das Maximum** -- und der Zweig selbst kostet nichts: die
            // vier Primitiven des Modells sind Zuweisung, Rechenoperation, Laden, Speichern.
            // Ein `if` ist keine davon; seine BEDINGUNG schon.
            StmtArt::Wenn(w) => {
                let mut hoechste = Kosten::Zahl(0);
                for (bed, rumpf) in &w.zweige {
                    let z = self.ausdruck(bed).plus(self.block(rumpf));
                    hoechste = groesser(hoechste, z);
                }
                if let Some(sonst) = &w.sonst {
                    hoechste = groesser(hoechste, self.block(sonst));
                }
                hoechste
            }
            StmtArt::Match(m) => {
                let mut hoechste = Kosten::Zahl(0);
                for z in &m.zweige {
                    hoechste = groesser(hoechste, self.block(&z.rumpf));
                }
                self.ausdruck(&m.gegenstand).plus(hoechste)
            }
            StmtArt::Bricht(b) => self.block(&b.rumpf),
            StmtArt::Sperrt(l) => self.block(&l.rumpf),
            StmtArt::Narrow(n) => Kosten::Zahl(1).plus(groesser(
                Kosten::Zahl(0),
                self.block(&n.sonst),
            )),

            StmtArt::Schleife(sch) => self.schleife(sch),
        }
    }

    /// **Die Schleifen -- und hier steckt die eigentliche Aussage des Modells.**
    fn schleife(&self, sch: &Schleife) -> Kosten {
        match sch {
            // Rumpfkosten x Domaenenschranke. Steht die Schranke nicht fest, steht auch
            // die Kostenzusage nicht fest -- und dann sagt der Pass das.
            Schleife::Traverse(t) => match (self.block(&t.rumpf), self.domaenenschranke(&t.domaene))
            {
                (Kosten::Zahl(rumpf), Some(n)) => Kosten::Zahl(rumpf * n),
                (Kosten::Unbekannt(g, s), _) => Kosten::Unbekannt(g, s),
                (_, None) => Kosten::Unbekannt(
                    format!(
                        "die Domaene `{}` der Traversierung hat keine Schranke aus der \
                         Deklaration (fehlt der Tabelle ihr `count`?)",
                        t.domaene.benennung()
                    ),
                    Some(t.span),
                ),
            },
            // `retry … bounded N ops` -- die Schranke IST die Zusage.
            Schleife::Retry(r) => match self.u.konst_wert(self.modul, &r.schranke) {
                Some(n) => Kosten::Zahl(n),
                None => Kosten::Unbekannt(
                    "die `bounded`-Schranke des `retry` steht nicht fest".to_string(),
                    Some(r.span),
                ),
            },
            // `forever` endet nicht -- eine Kostenzusage darueber gibt es nicht. Geprueft
            // wird stattdessen der DURCHGANG gegen `per_pass`.
            Schleife::Forever(f) => Kosten::Unbekannt(
                "eine `forever`-Schleife hat keine Gesamtkosten -- ihre Zusage ist \
                 `per_pass`, nicht `costs`"
                    .to_string(),
                Some(f.span),
            ),
        }
    }

    /// Die Schranke einer Domaene, soweit die Deklaration sie nennt.
    fn domaenenschranke(&self, d: &Domaene) -> Option<i128> {
        let tabelle = match d {
            Domaene::SlotsVon(o) | Domaene::NachfahrenVon(o) | Domaene::ElementeVon(o) => {
                // `descendants of c.slots[s]` zeigt IN die Tabelle -- die Schranke ist die
                // der Tabelle, nicht die des Slots.
                self.tabellenname(o).or_else(|| {
                    self.tabellenname(&Ort {
                        basis: o.basis.clone(),
                        suffixe: Vec::new(),
                        span: o.span,
                    })
                })?
            }
            _ => return None,
        };
        self.u.kapazitaeten.get(&tabelle).map(|n| *n as i128)
    }

    /// Auf welche Tabelle zeigt dieser Ort?
    fn tabellenname(&self, o: &Ort) -> Option<String> {
        let t = self.u.typ_von_ort(self.modul, o, &self.lokal);
        match t.durchgreifen() {
            crate::typen::Typ::Tabelle(n) => Some(n.clone()),
            _ => None,
        }
    }

    fn ausdruck(&self, e: &Expr) -> Kosten {
        // **Was zur Uebersetzungszeit feststeht, kostet zur Laufzeit nichts.** `GRENZE`,
        // `4096`, `NSLOTS * 8` -- keine der vier Primitiven wird dafuer emittiert.
        if self.u.konst_wert(self.modul, e).is_some() {
            return Kosten::Zahl(0);
        }
        match &e.art {
            ExprArt::Zahl(_) | ExprArt::Wahr | ExprArt::Falsch | ExprArt::Ergebnis => {
                Kosten::Zahl(0)
            }
            // Ein Laden ist eine Primitive.
            ExprArt::Ort(o) => Kosten::Zahl(
                1 + o
                    .suffixe
                    .iter()
                    .filter(|s| matches!(s, OrtSuffix::Index(_)))
                    .count() as i128,
            ),
            ExprArt::Alt(_) => Kosten::Zahl(0),
            ExprArt::Klammer(i) => self.ausdruck(i),
            ExprArt::Unaer(_, i) => Kosten::Zahl(1).plus(self.ausdruck(i)),
            ExprArt::Binaer(_, a, b) => {
                Kosten::Zahl(1).plus(self.ausdruck(a)).plus(self.ausdruck(b))
            }
            ExprArt::Eingebaut(_) => Kosten::Zahl(1),
            ExprArt::Ruf(r) => self.ruf(r),
        }
    }

    fn ruf(&self, r: &Ruf) -> Kosten {
        let name = r
            .pfad
            .teile
            .last()
            .map(|i| i.text.clone())
            .unwrap_or_default();
        let uebergang = self
            .u
            .kandidaten_oeffentlich(self.modul, &name)
            .into_iter()
            .find_map(|k| self.u.uebergangskosten.get(&k).copied());
        let mut summe = match self.deklariert.get(&name).copied().or(uebergang) {
            Some(n) => Kosten::Zahl(n),
            None => {
                // Kennt die Umgebung die Funktion ueberhaupt? Ein Aufruf ins Unbekannte
                // (extern, prim, Randfunktion) kostet unbekannt viel.
                if self.u.funktion(self.modul, &r.pfad).is_some() {
                    Kosten::Unbekannt(
                        format!("der Aufruf von `{name}` nennt keine `costs`"),
                        Some(r.span),
                    )
                } else {
                    Kosten::Unbekannt(
                        format!("`{name}` ist hier nicht deklariert"),
                        Some(r.span),
                    )
                }
            }
        };
        for a in &r.argumente {
            summe = summe.plus(self.ausdruck(a));
        }
        summe
    }

    /// **K002.** Ein `locks`-Block, dessen Rumpfkosten die `held`-Zusage der Sperre
    /// uebersteigen, ist ein Uebersetzungsfehler (`SPRACHE.md` §9.3, Punkt 1). Daran haengt
    /// die Latenzaussage je Wartestelle -- ohne diese Pruefung ist sie eine Behauptung.
    fn sperrbloecke(&self, b: &Block, absagen: &mut Absagen) {
        for s in &b.anweisungen {
            match &s.art {
                StmtArt::Sperrt(l) => {
                    let (topf, wort, code) = if l.geteilt {
                        (self.geteilte_haltezeiten, "shared held", "K003")
                    } else {
                        (self.haltezeiten, "held", "K002")
                    };
                    if let (Some(zusage), Kosten::Zahl(n)) =
                        (topf.get(&l.sperre.text()), self.block(&l.rumpf))
                    {
                        if n > *zusage {
                            absagen.schiebe(
                                Absage::fehler(
                                    code,
                                    l.sperre.span,
                                    format!(
                                        "der Block haelt `{}`{} fuer {n} ops, die Sperre sagt \
                                         `{wort} <= {zusage} ops` zu",
                                        l.sperre.text(),
                                        if l.geteilt { " geteilt" } else { "" }
                                    ),
                                )
                                .mit_notiz(
                                    "SPRACHE.md §9.3: an dieser Zahl haengt die Latenzaussage \
                                     je Wartestelle -- Ranghoehere halten <= ihrer `held`-Summe",
                                ),
                            );
                        }
                    }
                    self.sperrbloecke(&l.rumpf, absagen);
                }
                StmtArt::Wenn(w) => {
                    for (_, r) in &w.zweige {
                        self.sperrbloecke(r, absagen);
                    }
                    if let Some(r) = &w.sonst {
                        self.sperrbloecke(r, absagen);
                    }
                }
                StmtArt::Match(m) => {
                    for z in &m.zweige {
                        self.sperrbloecke(&z.rumpf, absagen);
                    }
                }
                StmtArt::Bricht(x) => self.sperrbloecke(&x.rumpf, absagen),
                StmtArt::Narrow(x) => self.sperrbloecke(&x.sonst, absagen),
                StmtArt::LetSonst(x) => self.sperrbloecke(&x.sonst, absagen),
                StmtArt::Schleife(sch) => match sch.as_ref() {
                    Schleife::Traverse(x) => self.sperrbloecke(&x.rumpf, absagen),
                    Schleife::Retry(x) => self.sperrbloecke(&x.rumpf, absagen),
                    Schleife::Forever(x) => self.sperrbloecke(&x.rumpf, absagen),
                },
                _ => {}
            }
        }
    }
}

/// Verlaesst der Block seinen Weg immer? Dieselbe syntaktische Frage, die M1 fuer die
/// V1-Verneinung stellt -- hier entscheidet sie, welche Wege sich addieren.
fn endet_immer(b: &Block) -> bool {
    let Some(letzte) = b.anweisungen.last() else {
        return false;
    };
    match &letzte.art {
        StmtArt::Return(_) | StmtArt::Leave(_) | StmtArt::Next(_) => true,
        StmtArt::Wenn(w) => {
            w.sonst.as_ref().is_some_and(endet_immer) && w.zweige.iter().all(|(_, r)| endet_immer(r))
        }
        StmtArt::Match(m) => m.zweige.iter().all(|z| endet_immer(&z.rumpf)),
        _ => false,
    }
}

fn groesser(a: Kosten, b: Kosten) -> Kosten {
    match (a, b) {
        (Kosten::Zahl(x), Kosten::Zahl(y)) => Kosten::Zahl(x.max(y)),
        (Kosten::Unbekannt(g, s), _) => Kosten::Unbekannt(g, s),
        (_, u) => u,
    }
}

/// **Die Nullzusage, als Werkzeug statt als Handgriff.**
///
/// Am 2026-08-14 habe ich die `costs`-Zeilen eines neuen Beispiels ermittelt, indem ich sie
/// absichtlich auf `1 ops` drückte, den Prüfer die wahren Zahlen nennen liess und sie dann
/// eintrug. Das Verfahren ist richtig — **eine `costs`-Zeile soll eine Messung sein, keine
/// Schätzung** —, aber der Handgriff war Handarbeit, und Handarbeit an einer Zahl ist genau
/// die Stelle, an der eine Zahl parallel zur Wahrheit zu laufen beginnt.
///
/// Also nennt der Prüfer sie jetzt selbst. `gabbro kosten datei.gab` druckt je Funktion die
/// **gerechnete** Rumpfzahl neben der **zugesagten**, und je `locks`-Block die gerechnete
/// Haltezeit neben `held` bzw. `shared held`. Wer eine Zusage schreibt, schreibt ab, was
/// dasteht.
///
/// **Was die Spalte `Luft` bedeutet und was nicht:** sie ist die Differenz, nicht ein Urteil.
/// Grosse Luft ist bei `costs` oft richtig (eine Signatur, die nicht bei jeder Rumpfänderung
/// bricht) und bei `held` fast immer falsch (die Latenzaussage rechnet mit der Zusage, nicht
/// mit der Rechnung).
pub fn bericht(baum: &Programm) -> String {
    let u = Umgebung::sammle(baum);
    let mut deklariert: HashMap<String, i128> = HashMap::new();
    let mut haltezeiten: HashMap<String, i128> = HashMap::new();
    let mut geteilte_haltezeiten: HashMap<String, i128> = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| match &item.art {
        ItemArt::Funktion(f) => {
            if let Some(c) = &f.costs {
                if let Some(n) = u.konst_wert(modul, c) {
                    deklariert.insert(f.name.text.clone(), n);
                }
            }
        }
        ItemArt::Lock(l) => {
            if let Some(n) = l.haltezeit.as_ref().and_then(|h| u.konst_wert(modul, h)) {
                haltezeiten.insert(l.name.text.clone(), n);
            }
            if let Some(n) = l
                .geteilte_haltezeit
                .as_ref()
                .and_then(|h| u.konst_wert(modul, h))
            {
                geteilte_haltezeiten.insert(l.name.text.clone(), n);
            }
        }
        _ => {}
    });

    let mut out = String::from(
        "-- Was der Rumpf KOSTET, neben dem, was die Zeile ZUSAGT. Wer eine Zusage\n\
         -- schreibt, schreibt ab, was hier steht -- eine `costs`-Zeile ist eine Messung,\n\
         -- keine Schaetzung.\n\
         -- Stelle\tgerechnet\tzugesagt\tLuft\n",
    );
    let (mut mit, mut ohne) = (0usize, 0usize);
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let lokal = f
            .parameter
            .iter()
            .map(|p| (p.name.text.clone(), u.typ_von_ausdruck_decl(modul, &p.typ)))
            .collect();
        let r = Rechner {
            u: &u,
            modul,
            deklariert: &deklariert,
            haltezeiten: &haltezeiten,
            geteilte_haltezeiten: &geteilte_haltezeiten,
            lokal,
        };
        let zugesagt = f.costs.as_ref().and_then(|c| u.konst_wert(modul, c));
        match r.block(b) {
            Kosten::Zahl(n) => {
                mit += 1;
                out.push_str(&format!("{}\t{n}\t{}\n", f.name.text, spalte(zugesagt, n)));
            }
            Kosten::Unbekannt(warum, _) => {
                ohne += 1;
                out.push_str(&format!(
                    "{}\tOFFEN\t{}\t-- {warum}\n",
                    f.name.text,
                    zugesagt.map(|z| z.to_string()).unwrap_or("--".into())
                ));
            }
        }
        r.bloecke_zeigen(b, &f.name.text, &mut out);
    });
    out.push_str(&format!(
        "-- {mit} Ruempfe ausgerechnet, {ohne} offen.\n\
         -- `Luft` ist eine Differenz, kein Urteil: bei `costs` ist sie oft richtig (eine\n\
         -- Signatur soll nicht bei jeder Rumpfaenderung brechen), bei `held` fast immer\n\
         -- falsch -- die Latenzaussage rechnet mit der ZUSAGE, nicht mit der Rechnung.\n"
    ));
    out
}

fn spalte(zugesagt: Option<i128>, gerechnet: i128) -> String {
    match zugesagt {
        Some(z) => format!("{z}\t{}", z - gerechnet),
        None => "--\t--".to_string(),
    }
}

impl Rechner<'_> {
    /// Je `locks`-Block: was er haelt, gegen das, was die Sperre zusagt.
    fn bloecke_zeigen(&self, b: &Block, wo: &str, out: &mut String) {
        for s in &b.anweisungen {
            if let StmtArt::Sperrt(l) = &s.art {
                let name = l.sperre.text();
                let (topf, wort) = if l.geteilt {
                    (self.geteilte_haltezeiten, "shared held")
                } else {
                    (self.haltezeiten, "held")
                };
                if let Kosten::Zahl(n) = self.block(&l.rumpf) {
                    out.push_str(&format!(
                        "  {wo} / {wort} {name}\t{n}\t{}\n",
                        spalte(topf.get(&name).copied(), n)
                    ));
                }
                self.bloecke_zeigen(&l.rumpf, wo, out);
            }
        }
    }
}
