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
//! | `K005` | die Zusage hat eine Form, die der Pass nicht liest -- **statt sie fallenzulassen** |
//!
//! ## Was der Pass NICHT tut
//!
//! * **Rekursion.** Ein Aufruf zaehlt die **deklarierten** `costs` des Gerufenen, nicht
//!   seine gerechneten. Bei einem Zyklus zaehlt jede Kante einmal -- die Deklaration traegt
//!   die Terminierung, nicht die Rechnung. Das ist die Absicht (§7: *„ein Aufruf zaehlt die
//!   deklarierten `costs`"*), aber es heisst: **`costs` an einer rekursiven Funktion ist eine
//!   Annahme**, kein Ergebnis.
//! * **`per_pass` gegen den Rumpf einer `forever`** wird seit dem 2026-08-19 geprueft
//!   (`K007`), und `bounded` an einem `retry` ebenso (`K006`). *Bis dahin stand dieser
//!   Absatz hier und behauptete es -- ohne dass es im ganzen Pruefer einen Leser gab.* Die
//!   Schranke **darf von Eingaben abhaengen** (§9.3, `64 + 12 * lenof(msg)`), und dann ist
//!   sie nicht konstant auswertbar. In dem Fall schweigt der Pass -- und zaehlt es.
//!
//! ## Die parametrische Zusage -- seit dem 2026-08-18 GELESEN statt fallengelassen
//!
//! `costs <= 4 + 12 * lenof(m) ops` war bis dahin eine Zeile ohne Wirkung: die Zusage war
//! nicht konstant auswertbar, und der Pass kehrte zurueck. Gemessen:
//!
//! ```text
//! impl fn schleife(n : u32 in 0 .. 1000) -> u32 costs <= 0 * n ops { return n; }
//! -> 3 Items, 0 Fehler, 0 Hinweise        (der Rumpf kostet 1)
//! ```
//!
//! > *Ein Vertrag, den niemand liest, ist keine Zusage, sondern eine Zeile.*
//!
//! Gelesen wird eine **Summe aus einer Konstanten und Vielfachen nichtnegativer Groessen**.
//! Verglichen wird gegen die **kleinste Belegung** -- alle Symbole null --, denn dort ist die
//! Zusage am kleinsten und muss GENAU DORT halten. *`costs <= 40 * n` ist bei `n = 0` gleich
//! null; ein Rumpf, der eine Operation kostet, verletzt sie, und das ist keine Haerte,
//! sondern die Wahrheit.*
//!
//! **Die Nichtnegativitaet ist eine Praemisse und wird geprueft** (`K005`): ohne sie gaebe es
//! keine kleinste Belegung. Ein Produkt zweier Symbole ist nicht lesbar -- und **das steht
//! als Absage da, nicht als Schweigen.**
//!
//! **Was damit noch NICHT geht:** ein Rumpf, dessen Kosten selbst symbolisch sind (eine
//! Schleife ueber `n`). Er rechnet heute `Unbekannt`, nicht `40 * n`. *Die Zusage ist
//! lesbar; die Rechnung dagegen ist die naechste Schicht* (`PLAN.md`, wertgetragene
//! Schranke).

use crate::typen::Typ;
use crate::umgebung::Umgebung;
use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::HashMap;

/// **Eine Zusage als SUMME: eine Konstante plus Vielfache nichtnegativer Groessen.**
///
/// `costs <= 4 + 12 * lenof(m)` ist `Term { fest: 4, glieder: {"lenof(m)": 12} }`.
///
/// **Die Form ist mit Absicht klein.** Ein Produkt zweier Symbole (`n * m`) waere nicht mehr
/// koeffizientenweise vergleichbar, und ein Vergleich, den der Pass nicht ENTSCHEIDET, ist
/// dasselbe Schweigen in neuer Verpackung.
#[derive(Debug, Clone, Default)]
struct Term {
    fest: i128,
    glieder: std::collections::BTreeMap<String, i128>,
}

/// Liest eine `costs`-Zusage als Summe. `None`, wenn sie diese Form nicht hat -- **und dann
/// sagt der Rufer es, statt zu schweigen.**
///
/// **Nichtnegativitaet ist eine PRAEMISSE und wird geprueft:** ein Symbol darf nur stehen,
/// wenn sein Typ vorzeichenlos ist oder es ein `lenof` ist. *Mit einer vorzeichenbehafteten
/// Groesse waere `40 * n` nach unten unbeschraenkt, und die kleinste Belegung gaebe es nicht.*
fn symbolisch(
    u: &Umgebung,
    modul: &str,
    lokal: &HashMap<String, Typ>,
    e: &Expr,
) -> Option<Term> {
    // Eine Konstante zuerst -- der haeufigste Fall, und er bleibt eine Zahl.
    if let Some(n) = u.konst_wert(modul, e) {
        return Some(Term { fest: n, glieder: Default::default() });
    }
    match &e.art {
        ExprArt::Klammer(i) => symbolisch(u, modul, lokal, i),
        ExprArt::Binaer(BinOp::Plus, a, b) => {
            let (x, y) = (symbolisch(u, modul, lokal, a)?, symbolisch(u, modul, lokal, b)?);
            let mut g = x.glieder;
            for (k, v) in y.glieder {
                *g.entry(k).or_insert(0) += v;
            }
            Some(Term { fest: x.fest.checked_add(y.fest)?, glieder: g })
        }
        // **Ein Produkt braucht eine konstante Seite.** `n * m` ist nicht lesbar, und das
        // steht in der Absage statt in einem Schweigen.
        ExprArt::Binaer(BinOp::Mal, a, b) => {
            let (ka, kb) = (u.konst_wert(modul, a), u.konst_wert(modul, b));
            let (k, rest) = match (ka, kb) {
                (Some(k), None) => (k, b),
                (None, Some(k)) => (k, a),
                _ => return None,
            };
            // Ein negativer Faktor macht die Zusage bei wachsender Eingabe KLEINER --
            // das ist keine Schranke.
            if k < 0 {
                return None;
            }
            let t = symbolisch(u, modul, lokal, rest)?;
            let mut g = std::collections::BTreeMap::new();
            for (name, v) in t.glieder {
                g.insert(name, v.checked_mul(k)?);
            }
            Some(Term { fest: t.fest.checked_mul(k)?, glieder: g })
        }
        // Ein blanker Ort ist ein Symbol -- **wenn er nichtnegativ ist.**
        ExprArt::Ort(o) => {
            let t = u.typ_von_ort(modul, o, lokal);
            let vorzeichenlos = match t.bereich() {
                Some(b) => b.min >= 0,
                // Ohne bekannten Bereich wird nichts angenommen.
                None => false,
            };
            if !vorzeichenlos {
                return None;
            }
            Some(Term { fest: 0, glieder: [(o.text(), 1)].into_iter().collect() })
        }
        // `lenof(x)` ist eine Laenge, also nichtnegativ -- das ist keine Annahme, sondern
        // die Bedeutung des Wortes.
        ExprArt::Eingebaut(b) => match b.as_ref() {
            Eingebaut::Lenof(TypOderOrt::Ort(o)) => Some(Term {
                fest: 0,
                glieder: [(format!("lenof({})", o.text()), 1)].into_iter().collect(),
            }),
            _ => None,
        },
        _ => None,
    }
}

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
                    deklariert.insert(crate::umgebung::qualifiziere(modul, &f.name.text), n);
                }
            }
        }
        ItemArt::Lock(l) => {
            if let Some(h) = &l.haltezeit {
                if let Some(n) = u.konst_wert(modul, h) {
                    haltezeiten.insert(crate::umgebung::qualifiziere(modul, &l.name.text), n);
                }
            }
            if let Some(h) = &l.geteilte_haltezeit {
                if let Some(n) = u.konst_wert(modul, h) {
                    geteilte_haltezeiten.insert(crate::umgebung::qualifiziere(modul, &l.name.text), n);
                }
            }
        }
        _ => {}
    });

    let g = crate::aufrufgraph::erhebe_mit(baum, &u);
    let mut z = Zaehlung::default();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let lokal: HashMap<String, Typ> = f
            .parameter
            .iter()
            .map(|p| (p.name.text.clone(), u.typ_von_ausdruck_decl(modul, &p.typ)))
            .collect();
        // **Die Parameter gehoeren in die symbolische Lesart.** Ohne sie ist `n` ein Ort
        // ohne Bereich, also nicht nachweislich nichtnegativ -- und der Pass sagt ab, wo er
        // rechnen koennte. *Ein Waechter, der die Haelfte der Karte nicht sieht, verbietet
        // statt zu pruefen.*
        let sym_lokal = lokal.clone();
        let r = Rechner {
            u: &u,
            modul,
            mit_mass: f
                .decreases
                .as_ref()
                .map(|_| (&g, g.schluessel_von(modul, &f.name.text))),
            deklariert: &deklariert,
            haltezeiten: &haltezeiten,
            geteilte_haltezeiten: &geteilte_haltezeiten,
            lokal,
        };

        // -- K002: jeder `locks`-Block gegen die `held`-Zusage seiner Sperre.
        r.sperrbloecke(b, absagen);
        // -- K006/K007: jede Schleifenzusage gegen ihren eigenen Rumpf.
        r.schleifenzusagen(b, absagen);
        // -- K008/K009 («K5.4»): die Rekursion bekommt ein Mass.
        rekursionsmass(f, b, modul, &u, &g, absagen);

        let Some(zusage_expr) = &f.costs else {
            return;
        };
        // **Bis zum 2026-08-18 stand hier ein `return`** -- eine Zusage, die nicht konstant
        // auswertbar war, wurde stillschweigend fallengelassen. Gemessen:
        //
        // ```gabbro
        // impl fn schleife(n : u32 in 0 .. 1000) -> u32 costs <= 0 * n ops { return n; }
        // -> 3 Items, 0 Fehler, 0 Hinweise      (der Rumpf kostet 1)
        // ```
        //
        // > *Ein Vertrag, den niemand liest, ist keine Zusage, sondern eine Zeile.*
        let zusage = match symbolisch(&u, modul, &sym_lokal, zusage_expr) {
            Some(t) => t,
            None => {
                z.offen += 1;
                absagen.schiebe(
                    Absage::fehler(
                        "K005",
                        zusage_expr.span,
                        format!(
                            "`{}` promises costs the pass cannot read",
                            f.name.text
                        ),
                    )
                    .mit_notiz(
                        "readable is a sum of constants and multiples of declared \
                            quantities -- `40`, `NSLOTS * 8`, `64 + 12 * lenof(m)`",
                    )
                    .mit_notiz(
                        "a promise the pass does not read was, until 2026-08-18, an empty \
                            line: `costs <= 0 * n ops` on a body costing 1 op went through \
                            with 0 errors",
                    ),
                );
                return;
            }
        };
        // **Die kleinste Belegung ist die entscheidende.** Alle Symbole sind nichtnegativ
        // (das prueft `symbolisch`), also wird die Zusage bei `n = 0` am kleinsten -- und
        // eine Schranke muss GENAU DORT halten. *`costs <= 40 * n` ist bei `n = 0` gleich
        // null; ein Rumpf, der eine Operation kostet, verletzt sie.*
        let zusage_min = zusage.fest;
        let zusage = zusage_min;
        match r.block(b) {
            Kosten::Zahl(n) => {
                z.gerechnet += 1;
                if n > zusage {
                    absagen.schiebe(
                        Absage::fehler(
                            "K001",
                            zusage_expr.span,
                            format!(
                                "`{}` promises <= {zusage} ops, the body costs {n}",
                                f.name.text
                            ),
                        )
                        .mit_notiz(
                            "SPRACHE.md §7: 1 op = one Gabbro primitive; a call counts \
                                the declared costs of the callee",
                        )
                        .mit_notiz(
                            "the number is computed statically -- lowering it means \
                                writing fewer operations, not promising more",
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
                                "`{}` promises costs, but {grund}",
                                f.name.text
                            ),
                        )
                        .mit_notiz(
                            "a cost promise over an unknown quantity is a promise nobody \
                                can check",
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
            (Kosten::Zahl(a), Kosten::Zahl(b)) => match a.checked_add(b) {
                Some(n) => Kosten::Zahl(n),
                None => Kosten::ueberlauf(None),
            },
            (Kosten::Unbekannt(g, s), _) => Kosten::Unbekannt(g, s),
            (_, u) => u,
        }
    }

    /// **Ein Ueberlauf ist eine unbekannte Zahl, keine kleine.**
    ///
    /// Bis 2026-08-19 rechnete der Pass mit blankem `*` und `+` ueber `i128`. Vier
    /// geschachtelte `traverse` ueber `count 4294967295` ergaben ein NEGATIVES Produkt, und
    /// `n > zusage` war damit falsch: **`costs <= 4 ops` galt fuer einen Rumpf mit
    /// 10^38 Schritten, mit null Meldungen.**
    ///
    /// > *Im Testbau (mit `overflow-checks`) hielt das Programm an; im Auslieferungsbau lief
    /// > es durch. Der lautere der beiden Faelle war der harmlosere.*
    ///
    /// Die Absage heisst `K003` wie jede andere unbekannte Zahl -- der Pass hoert auf zu
    /// rechnen und sagt das, statt eine Zahl zu erfinden (R16).
    fn ueberlauf(span: Option<Span>) -> Kosten {
        Kosten::Unbekannt(
            "the cost calculation overflows -- the bound is beyond what the pass can represent, \
             so nothing is promised here"
                .to_string(),
            span,
        )
    }

    /// Rumpfkosten x Schranke, ohne stillen Ueberlauf.
    fn mal(self, faktor: i128, span: Option<Span>) -> Kosten {
        match self {
            Kosten::Zahl(a) => match a.checked_mul(faktor) {
                Some(n) => Kosten::Zahl(n),
                None => Kosten::ueberlauf(span),
            },
            u => u,
        }
    }
}

struct Rechner<'a> {
    u: &'a Umgebung,
    modul: &'a str,
    /// **Der eigene qualifizierte Name, wenn die Funktion ein `decreases` trägt** («K5.4»).
    ///
    /// Mit einem Mass ist `costs` die Zusage **eines Durchgangs**, nicht der ganzen Rekursion
    /// — die Tiefe steht im Mass. *Ohne diese Lesart wäre die Zeile unerfüllbar:* ein
    /// rekursiver Ruf zählt die deklarierten Kosten des Gerufenen, also seine eigenen, und
    /// der Rumpf käme immer über die eigene Zusage. **`K001` fiel an jeder korrekten
    /// rekursiven Funktion**, und das war der Grund, warum niemand eine schrieb.
    mit_mass: Option<(&'a crate::aufrufgraph::Graph, String)>,
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
                    if crate::endet_immer(rumpf, &[]) {
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
                    if crate::endet_immer(rumpf, &[]) {
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
                // **Ein `place` auszupacken kostet EINE Operation** -- die Ablesung. Ein
                // Ruf kostet, was der Gerufene zusagt.
                let quelle = match l.als_ruf() {
                    Some(r) => self.ruf(r),
                    None => Kosten::Zahl(1),
                };
                Kosten::Zahl(1).plus(quelle).plus(self.block(&l.sonst))
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
            // **`observes` kostet die NAHME nicht** -- RCU nimmt nichts. Was es kostet, ist
            // der Rumpf und die zwei Marken; die zaehlen als eine Primitive.
            StmtArt::Observiert(o) => Kosten::Zahl(1).plus(self.block(&o.rumpf)),
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
                (Kosten::Zahl(rumpf), Some(n)) => Kosten::Zahl(rumpf).mal(n, Some(t.span)),
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
                    "the `bounded` bound of the `retry` is not fixed".to_string(),
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

    /// Die Schranke einer Domaene -- **umgezogen nach `domaene.rs` am 2026-08-19**, weil M1
    /// sie fuer «H2.1» braucht. *Eine Stelle, zwei Leser.*
    fn domaenenschranke(&self, d: &Domaene) -> Option<i128> {
        crate::domaene::Sicht { u: self.u, modul: self.modul, lokal: &self.lokal }
            .domaenenschranke(d)
    }

    fn ausdruck(&self, e: &Expr) -> Kosten {
        // **Was zur Uebersetzungszeit feststeht, kostet zur Laufzeit nichts.** `GRENZE`,
        // `4096`, `NSLOTS * 8` -- keine der vier Primitiven wird dafuer emittiert.
        if self.u.konst_wert(self.modul, e).is_some() {
            return Kosten::Zahl(0);
        }
        match &e.art {
            ExprArt::Zahl(_)
            | ExprArt::Gleitkomma { .. }
            | ExprArt::Wahr
            | ExprArt::Falsch
            | ExprArt::Ergebnis => {
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
        // **«B35»: `Some(x)` und `None` sind KONSTRUKTOREN, keine Aufrufe.** Im Baum sind
        // sie ein `Ruf` (ein Konstruktor ist genau das), aber sie tragen keinen Vertrag und
        // koennen keinen nennen -- `costs` an `None` waere sinnlos. Die Ausnahme steht
        // hier, an der einen Stelle, die sie braucht, mit ihrem Grund.
        //
        // Preis: eine Option zu bauen kostet **1 op** (`Some`) bzw. **0** (`None`) -- ein
        // Etikett setzen, mehr ist es nicht.
        if name == "Some" {
            return r
                .argumente
                .iter()
                .fold(Kosten::Zahl(1), |a, e| a.plus(self.ausdruck(e)));
        }
        if name == "None" {
            return Kosten::Zahl(0);
        }
        // **«B7»: ein Verbundwert ist ein Konstruktor, und seine Kosten stehen fest.**
        //
        // Die bewiesene Schablone sagt, WAS er tut: *setzt jedes Feld genau einmal und laesst
        // keins uninitialisiert.* Damit ist die Rechnung nicht geschaetzt, sondern abgelesen
        // -- **ein Speichern je Feld**, und die Felderzahl steht in der Deklaration.
        //
        // Ohne diesen Zweig faellt der Ruf in den Zweig darunter und traegt keine `costs`
        // (`K003`): eine Zahl ueber Unbekanntem. *Ein Konstruktor kann keine `costs`-Klausel
        // bekommen -- er hat keine Deklaration, an die sie sich schreiben liesse.* Dieselbe
        // Lage wie beim `transition`, und dieselbe Antwort: die Kosten stehen in der Form.
        if r.ist_verbundwert() {
            return r
                .argumente
                .iter()
                .fold(Kosten::Zahl(r.marken.len() as i128), |a, e| {
                    a.plus(self.ausdruck(e))
                });
        }
        let uebergang = self
            .u
            .kandidaten_oeffentlich(self.modul, &name)
            .into_iter()
            .find_map(|k| self.u.uebergangskosten.get(&k).copied());
        // **Modulbewusst seit 2026-08-19.** Vorher gewann der zuletzt eingetragene
        // gleichnamige Name: `a::hilf costs <= 900` und `b::hilf costs <= 1` waren EIN
        // Eintrag, und welcher galt, entschied die Reihenfolge im Quelltext.
        let erklaert = self
            .u
            .kandidaten_oeffentlich(self.modul, &r.pfad.text())
            .into_iter()
            .find_map(|k| self.deklariert.get(&k).copied());
        // **Ein rekursiver Ruf unter einem `decreases` kostet hier NICHTS** («K5.4»): die
        // Tiefe trägt das Mass, die Zusage gilt je Durchgang.
        if let Some((g, selbst)) = &self.mit_mass {
            if let Some(ziel) = g.aufloesen(self.u, self.modul, &r.pfad.text()) {
                if &ziel == selbst || g.im_zyklus(&ziel) {
                    return r
                        .argumente
                        .iter()
                        .fold(Kosten::Zahl(0), |a, e| a.plus(self.ausdruck(e)));
                }
            }
        }
        let mut summe = match erklaert.or(uebergang) {
            Some(n) => Kosten::Zahl(n),
            None => {
                // Kennt die Umgebung die Funktion ueberhaupt? Ein Aufruf ins Unbekannte
                // (extern, prim, Randfunktion) kostet unbekannt viel.
                if self.u.funktion(self.modul, &r.pfad).is_some() {
                    Kosten::Unbekannt(
                        format!("the call to `{name}` declares no `costs`"),
                        Some(r.span),
                    )
                } else {
                    Kosten::Unbekannt(
                        format!("`{name}` is not declared here"),
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

    /// **K006/K007 -- die Schleifenzusage gegen ihren eigenen Rumpf.**
    ///
    /// Bis 2026-08-19 rechnete der Pass fuer ein `retry` schlicht die Schranke: `bounded N
    /// ops` WAR die Zusage, und der Rumpf wurde nie angesehen. Gemessen: `bounded 2 ops` mit
    /// zehn Zuweisungen im Rumpf ergab **0 Fehler**.
    ///
    /// Dasselbe an `forever`: der Kopf dieses Moduls behauptete seit dem 2026-08-14, `per_pass`
    /// werde gegen den Rumpf geprueft. **Es gab im ganzen Pruefer keinen Leser.** Damit hatte
    /// genau die Schleifenform, die unendlich laufen darf, keine geprüfte Kostenaussage.
    ///
    /// Geprueft wird das, was sicher gilt: **EIN Durchgang muss in die Zusage passen.** Wie
    /// viele es werden, entscheidet die Bedingung -- aber schon der erste, der nicht passt,
    /// macht die Zeile falsch. *Ist die Schranke eingabeabhaengig, schweigt der Pass; das ist
    /// dieselbe Stelle, an der `costs <= 4 + 12 * lenof(m)` symbolisch gelesen wird.*
    fn schleifenzusagen(&self, b: &Block, absagen: &mut Absagen) {
        for s in &b.anweisungen {
            if let StmtArt::Schleife(sch) = &s.art {
                let (rumpf, zusage_expr, wort, code, span) = match sch.as_ref() {
                    Schleife::Retry(r) => (&r.rumpf, &r.schranke, "bounded", "K006", r.span),
                    Schleife::Forever(f) => {
                        (&f.rumpf, &f.je_durchgang, "per_pass bounded", "K007", f.span)
                    }
                    Schleife::Traverse(t) => {
                        self.schleifenzusagen(&t.rumpf, absagen);
                        continue;
                    }
                };
                // **Die Zusage darf von EINGABEN abhaengen** (§9.3, `64 + 12 * lenof(msg)`)
                // -- seit 2026-08-19 wird sie dann SYMBOLISCH gelesen statt fallengelassen.
                //
                // Entschieden wird gegen die **kleinste Belegung**: alle Symbole sind
                // nichtnegativ, also ist die Schranke bei `n = 0` am kleinsten, und dort muss
                // sie halten. *Dieselbe Lesart wie bei `costs` (`K001`/`K005`), und derselbe
                // Grund: `per_pass bounded 12 * n` ist bei `n = 0` gleich null.*
                let zahl = self.u.konst_wert(self.modul, zusage_expr).or_else(|| {
                    symbolisch(self.u, self.modul, &self.lokal, zusage_expr).map(|t| t.fest)
                });
                if let (Some(zusage), Kosten::Zahl(n)) = (zahl, self.block(rumpf)) {
                    if n > zusage {
                        absagen.schiebe(
                            Absage::fehler(
                                code,
                                span,
                                format!(
                                    "one pass of this loop costs {n} ops, the loop \
                                     promises `{wort} {zusage} ops`"
                                ),
                            )
                            .mit_notiz(
                                "the bound is a promise about the loop, and one pass \
                                 already exceeds it -- how often it runs does not matter \
                                 any more",
                            ),
                        );
                    }
                }
                self.schleifenzusagen(rumpf, absagen);
            } else {
                match &s.art {
                    StmtArt::Sperrt(l) => self.schleifenzusagen(&l.rumpf, absagen),
                    StmtArt::Bricht(x) => self.schleifenzusagen(&x.rumpf, absagen),
                    StmtArt::Narrow(x) => self.schleifenzusagen(&x.sonst, absagen),
                    StmtArt::LetSonst(x) => self.schleifenzusagen(&x.sonst, absagen),
                    StmtArt::Wenn(w) => {
                        for (_, r) in &w.zweige {
                            self.schleifenzusagen(r, absagen);
                        }
                        if let Some(r) = &w.sonst {
                            self.schleifenzusagen(r, absagen);
                        }
                    }
                    StmtArt::Match(m) => {
                        for z in &m.zweige {
                            self.schleifenzusagen(&z.rumpf, absagen);
                        }
                    }
                    StmtArt::Exchange(e) => {
                        if let XForm::Update { rumpf, .. } = &e.form {
                            self.schleifenzusagen(rumpf, absagen);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    /// **K002.** Ein `locks`-Block, dessen Rumpfkosten die `held`-Zusage der Sperre
    /// uebersteigen, ist ein Uebersetzungsfehler (`SPRACHE.md` §9.3, Punkt 1). Daran haengt
    /// die Latenzaussage je Wartestelle -- ohne diese Pruefung ist sie eine Behauptung.
    fn sperrbloecke(&self, b: &Block, absagen: &mut Absagen) {
        for s in &b.anweisungen {
            match &s.art {
                StmtArt::Sperrt(l) => {
                    let (topf, wort, code) = if l.geteilt {
                        // **K004, nicht K003.** Ich hatte den Code doppelt belegt: K003 fuehrt
                        // seit Pass 9 die unbekannten Aufrufkosten. Zwei verschiedene Absagen
                        // unter einer Kennung machen jede Zaehlung nach Codes falsch -- und
                        // die Giftproben pruefen genau auf Kennungen.
                        (self.geteilte_haltezeiten, "shared held", "K004")
                    } else {
                        (self.haltezeiten, "held", "K002")
                    };
                    let zeit = self
                        .u
                        .kandidaten_oeffentlich(self.modul, &l.sperre.text())
                        .into_iter()
                        .find_map(|k| topf.get(&k));
                    if let (Some(zusage), Kosten::Zahl(n)) = (zeit, self.block(&l.rumpf)) {
                        if n > *zusage {
                            absagen.schiebe(
                                Absage::fehler(
                                    code,
                                    l.sperre.span,
                                    format!(
                                        "the block holds `{}` for {n} ops, the lock \
                                         promises `{wort} <= {zusage} ops`",
                                        l.sperre.text()
                                    ),
                                )
                                .mit_notiz(
                                    "SPRACHE.md §9.3: the latency statement of every \
                                        other core hangs on this number",
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
                    deklariert.insert(crate::umgebung::qualifiziere(modul, &f.name.text), n);
                }
            }
        }
        ItemArt::Lock(l) => {
            if let Some(n) = l.haltezeit.as_ref().and_then(|h| u.konst_wert(modul, h)) {
                haltezeiten.insert(crate::umgebung::qualifiziere(modul, &l.name.text), n);
            }
            if let Some(n) = l
                .geteilte_haltezeit
                .as_ref()
                .and_then(|h| u.konst_wert(modul, h))
            {
                geteilte_haltezeiten.insert(crate::umgebung::qualifiziere(modul, &l.name.text), n);
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
        let lokal: HashMap<String, Typ> = f
            .parameter
            .iter()
            .map(|p| (p.name.text.clone(), u.typ_von_ausdruck_decl(modul, &p.typ)))
            .collect();
        let r = Rechner {
            u: &u,
            modul,
            // Der Bericht rechnet ohne Mass -- er zeigt Zahlen, er entscheidet nicht.
            mit_mass: None,
            deklariert: &deklariert,
            haltezeiten: &haltezeiten,
            geteilte_haltezeiten: &geteilte_haltezeiten,
            lokal,
        };
        // **Der BERICHT zeigt weiter `--` fuer eine parametrische Zusage**, und das bleibt
        // richtig: es gibt dort keine einzelne Zahl zum Danebenstellen. *Entschieden wird sie
        // trotzdem* -- vom Tor oben, gegen die kleinste Belegung (`K001`/`K005`).
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
        "-- {mit} bodies computed, {ohne} open.\n"
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
                let zeit = self
                    .u
                    .kandidaten_oeffentlich(self.modul, &name)
                    .into_iter()
                    .find_map(|k| topf.get(&k).copied());
                if let Kosten::Zahl(n) = self.block(&l.rumpf) {
                    out.push_str(&format!(
                        "  {wo} / {wort} {name}\t{n}\t{}\n",
                        spalte(zeit, n)
                    ));
                }
                self.bloecke_zeigen(&l.rumpf, wo, out);
            }
        }
    }
}

/// **Die Durchgangskosten eines Schleifenrumpfs — für den Erzeuger, nicht für den Pass.**
///
/// `retry … bounded N ops` sagt ein OPERATIONSBUDGET zu, keinen Schleifenzähler. Wer daraus
/// eine Laufzeitschranke machen will, muss durch die Kosten EINES Durchgangs teilen — und die
/// rechnet dieses Modul ohnehin schon aus. *Ein zweiter Kostenrechner im Erzeuger wäre genau
/// das zweite Register, gegen das W7 steht.*
///
/// `None` heißt: die Kosten stehen nicht fest. Der Erzeuger weigert sich dann (`C001`), statt
/// eine Zahl zu raten.
pub fn durchgangskosten(
    baum: &Programm,
    modul: &str,
    r: &Retry,
    lokal: HashMap<String, crate::typen::Typ>,
) -> Option<i128> {
    let u = Umgebung::sammle(baum);
    let mut deklariert: HashMap<String, i128> = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, m| {
        if let ItemArt::Funktion(f) = &item.art {
            if let Some(c) = &f.costs {
                if let Some(n) = u.konst_wert(m, c) {
                    deklariert.insert(crate::umgebung::qualifiziere(modul, &f.name.text), n);
                }
            }
        }
    });
    let leer: HashMap<String, i128> = HashMap::new();
    let rechner = Rechner {
        u: &u,
        modul,
        mit_mass: None,
        deklariert: &deklariert,
        haltezeiten: &leer,
        geteilte_haltezeiten: &leer,
        lokal,
    };
    // **Ein Durchgang ist Rumpf PLUS Bedingung.** Die `until`-Bedingung wird bei jedem
    // Durchgang ausgewertet und kann teurer sein als der Rumpf -- `FRAGMENTE.md` F4 pollt
    // mit leerem Rumpf. *Nur den Rumpf zu zaehlen hiesse, den teuersten Teil zu uebersehen.*
    let rumpf = rechner.block(&r.rumpf);
    let bedingung = match &r.bis {
        Some(p) => pred_kosten(&rechner, p),
        None => Kosten::Zahl(0),
    };
    match rumpf.plus(bedingung) {
        Kosten::Zahl(n) if n > 0 => Some(n),
        _ => None,
    }
}

/// Die Kosten eines Praedikats -- fuer den `until`-Test, der bei jedem Durchgang laeuft.
fn pred_kosten(r: &Rechner, p: &Pred) -> Kosten {
    match &p.art {
        PredArt::Vergleich(e) | PredArt::Element(e, _) => r.ausdruck(e),
        PredArt::Klammer(x) | PredArt::Nicht(x) => pred_kosten(r, x),
        PredArt::Und(a, b) | PredArt::Oder(a, b) => pred_kosten(r, a).plus(pred_kosten(r, b)),
        _ => Kosten::Zahl(1),
    }
}

/// **«K5.4» — die Rekursion bekommt ein Mass** (`K008`/`K009`).
///
/// `SPRACHE.md` §7: *„ein Aufruf zählt die **deklarierten** `costs` des Gerufenen."* Bei einem
/// Zyklus zählt damit jede Kante **einmal**, und die Zusage einer rekursiven Funktion ist eine
/// **Annahme**, kein Ergebnis. `K001` und `E009` benannten das ehrlich — *und ehrlich ist
/// nicht vollständig.*
///
/// * **`K008`** — eine Funktion, die sich selbst erreicht, trägt ein `decreases`.
/// * **`K009`** — an jeder rekursiven Rufstelle ändert sich mindestens eine der Grössen, die
///   das Mass nennt. **Wird jede unverändert durchgereicht, kann das Mass nicht fallen.**
///
/// Geprüft wird die **notwendige** Bedingung, genau wie `S005` am Abstiegsmass einer
/// `traverse`. *DASS es fällt, bleibt Beweisersache (`consuming.ordnung`)* — und diese
/// Trennung ist die Zielform: **die Notation trägt, der Beweis bleibt beim Nutzer.**
fn rekursionsmass(
    f: &FnDecl,
    b: &Block,
    modul: &str,
    u: &Umgebung,
    g: &crate::aufrufgraph::Graph,
    absagen: &mut Absagen,
) {
    let voll = g.schluessel_von(modul, &f.name.text);
    if !g.im_zyklus(&voll) {
        return;
    }
    let Some(mass) = &f.decreases else {
        absagen.schiebe(
            Absage::fehler(
                "K008",
                f.name.span,
                format!("`{}` reaches itself and declares no `decreases`", f.name.text),
            )
            .mit_notiz(
                "a call counts the DECLARED `costs` of the callee, so on a cycle every edge \
                 counts once -- the promise is an assumption, not a result",
            )
            .mit_notiz("`decreases <expr>` names the measure that falls along the recursion"),
        );
        return;
    };
    // Welche Parameter nennt das Mass?
    let mut genannt = Vec::new();
    namen_im_ausdruck(mass, &mut genannt);
    let stellen: Vec<usize> = f
        .parameter
        .iter()
        .enumerate()
        .filter(|(_, p)| genannt.contains(&p.name.text))
        .map(|(i, _)| i)
        .collect();
    if stellen.is_empty() {
        absagen.schiebe(
            Absage::fehler(
                "K009",
                mass.span,
                format!(
                    "the `decreases` of `{}` names no parameter of it",
                    f.name.text
                ),
            )
            .mit_notiz(
                "a measure over something the recursive call cannot change is constant -- \
                 and a constant measure never falls",
            )
            .mit_notiz(
                "checked is the NECESSARY condition, not the sufficient one: THAT it falls \
                 is the prover's business (`consuming.ordnung`)",
            ),
        );
        return;
    }
    // An jeder rekursiven Rufstelle: aendert sich wenigstens eine der genannten Groessen?
    let mut rufe: Vec<(String, Vec<Option<String>>)> = Vec::new();
    crate::aufrufgraph::kanten_von(b, &mut rufe);
    for (pfad, args) in &rufe {
        let Some(ziel) = g.aufloesen(u, modul, pfad) else {
            continue;
        };
        // Nur ZURUECK in den Zyklus: ein Ruf auf etwas, das uns wieder erreicht.
        if ziel != voll && !g.im_zyklus(&ziel) {
            continue;
        }
        let bewegt = stellen.iter().any(|i| match args.get(*i) {
            // Derselbe Name durchgereicht -- diese Groesse aendert sich nicht.
            Some(Some(a)) => *a != f.parameter[*i].name.text,
            // Kein Ort: irgendein gerechneter Ausdruck. Das ZAEHLT als Bewegung -- was er
            // rechnet, kann dieser Pass nicht sagen, und Schweigen ist hier die richtige
            // Antwort (W10).
            Some(None) => true,
            None => false,
        });
        if !bewegt {
            absagen.schiebe(
                Absage::fehler(
                    "K009",
                    f.name.span,
                    format!(
                        "the recursive call to `{pfad}` passes every size of the \
                         `decreases` of `{}` through unchanged",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "then the measure is the same at every level -- and a constant measure \
                     never falls",
                )
                .mit_notiz(
                    "checked is the NECESSARY condition: THAT it falls is the prover's \
                     business (`consuming.ordnung`)",
                ),
            );
        }
    }
}

fn namen_im_ausdruck(e: &Expr, aus: &mut Vec<String>) {
    match &e.art {
        ExprArt::Ort(o) => aus.push(o.basis.text.clone()),
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => namen_im_ausdruck(x, aus),
        ExprArt::Binaer(_, a, b) => {
            namen_im_ausdruck(a, aus);
            namen_im_ausdruck(b, aus);
        }
        ExprArt::Ruf(r) => {
            for a in &r.argumente {
                namen_im_ausdruck(a, aus);
            }
        }
        _ => {}
    }
}
