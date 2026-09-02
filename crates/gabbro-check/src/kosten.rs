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

/// **The names visible at ONE point of a body** -- the parameters plus every `let` of the
/// enclosing blocks. Until 2026-08-31 there were only the parameters, and a `let` in an
/// inner block was invisible to this pass. *The same thing `m1.rs::Lage` carries, after the
/// same model.*
type Bindungen = HashMap<String, Typ>;

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

/// **`K010` -- unter einer Sperre darf der Rahmen NICHT parametrisch sein.**
///
/// Die Kostenklasse vertraegt Symbole: `costs <= 4 + 12 * lenof(m) ops` ist seit dem
/// 2026-08-18 lesbar, und verglichen wird gegen die kleinste Belegung. **Die Sperrklasse
/// vertraegt sie nicht**, und das ist keine Bequemlichkeit, sondern die Bedeutung des Wortes:
///
/// > `held` ist eine **LATENZaussage** -- wie lange ein *anderer* Kern hoechstens wartet.
/// > Ein `held <= 40 * n` mit symbolischem `n` sagt: so lange, wie `n` gross ist. Das ist
/// > keine Schranke, sondern eine Sperre, die unbeschraenkt lange gehalten wird.
///
/// **Und die kleinste Belegung hilft hier gerade NICHT.** Bei `costs` ist sie die scharfe
/// Lesart -- die Zusage ist bei `n = 0` am kleinsten und muss genau dort halten. Bei `held`
/// waere sie die falsche Richtung: die Latenz eines wartenden Kerns haengt an der GROESSTEN
/// Belegung, und die hat ein Symbol nicht.
///
/// **Gemessen 2026-08-20, und der Befund ist das Schweigen:**
///
/// ```text
/// lock KAPPEN protects { eintraege } rank 0 held <= 40 * eintraege ops;
/// impl fn viel() … { locks KAPPEN { <5 Operationen> } }
/// -> 4 Items, 0 Fehler, 0 Hinweise
/// ```
///
/// `haltezeiten` nahm nur auf, was `konst_wert` hergab; alles andere fiel aus der Karte, und
/// mit der Karte fiel `K002`. *Eine Zusage, die den Waechter abschaltet, den sie fuettern
/// sollte, ist teurer als gar keine* -- dieselbe Bauart wie die parametrische `costs`-Zeile
/// vor dem 2026-08-18, nur in die andere Richtung: dort schwieg der Pass ueber die ZUSAGE,
/// hier schweigt er ueber den RUMPF.
fn haltezeit_ist_keine_zahl(l: &LockDecl, wort: &str, span: Span) -> Absage {
    Absage::fehler(
        "K010",
        span,
        format!(
            "`{}` promises `{wort}` with a bound that is not constant",
            l.name.text
        ),
    )
    .mit_notiz(
        "`held` is a LATENCY statement -- how long another core waits at most. A symbolic \
         bound is a lock held for an unbounded time",
    )
    .mit_notiz(
        "and it switches the check off silently: `K002`/`K004` compare the block against a \
         number the pass never got",
    )
    .mit_notiz(
        "the cost class tolerates symbols (`costs <= 40 * n`), the lock class does not -- \
         `costs` is compared at the SMALLEST assignment, latency lives at the largest",
    )
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) -> Zaehlung {
    let u = Umgebung::sammle(baum);
    // **A generated operation declares its cost by COUNTING its own stores** (2026-08-28).
    // Without this line a call to `T::insert` is `K003` -- *"a cost promise over an unknown
    // quantity"* -- and `D001` would forbid the hand-written mutation while making the
    // generated one uncostable. `messung/OPS-RUFFORM.md`.
    let mut deklariert: HashMap<String, i128> = crate::opsruf::kosten(baum);
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
            for (wort, zusage, topf) in [
                ("held", &l.haltezeit, &mut haltezeiten),
                ("shared held", &l.geteilte_haltezeit, &mut geteilte_haltezeiten),
            ] {
                let Some(h) = zusage else { continue };
                match u.konst_wert(modul, h) {
                    Some(n) => {
                        topf.insert(crate::umgebung::qualifiziere(modul, &l.name.text), n);
                    }
                    // **`K010`.** Bis hier stand ein blosses `if let` -- eine nicht konstant
                    // auswertbare Haltezeit fiel aus der Karte und mit ihr `K002`/`K004`.
                    None => absagen.schiebe(haltezeit_ist_keine_zahl(l, wort, h.span)),
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
        r.sperrbloecke(b, &r.lokal.clone(), absagen);
        // -- K006/K007: jede Schleifenzusage gegen ihren eigenen Rumpf.
        r.schleifenzusagen(b, &r.lokal.clone(), absagen);
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
        match r.block(b, &r.lokal.clone()) {
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
#[derive(Clone)]
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
    fn block(&self, b: &Block, aussen: &Bindungen) -> Kosten {
        // **The block scope -- it INHERITS and gives nothing back**, exactly like
        // `m1.rs::Lage`. Without it `typ_von_ort` looks up the parameter that a `let` one
        // line above has shadowed, and the domain bound belongs to the wrong table.
        // *Measured 2026-08-31: 17 promised ops over a C program that runs 64 passes.*
        let mut lokal = aussen.clone();
        let mut summe = Kosten::Zahl(0);
        for (i, s) in b.anweisungen.iter().enumerate() {
            if let StmtArt::Wenn(w) = &s.art {
                if w.sonst.is_none() && w.zweige.len() == 1 {
                    let (bed, rumpf) = &w.zweige[0];
                    if crate::endet_immer(rumpf, &[]) {
                        // Zwei Wege: durch den Zweig, oder daran vorbei und weiter.
                        let durch = self.ausdruck(bed, &lokal).plus(self.block(rumpf, &lokal));
                        let vorbei = self.ausdruck(bed, &lokal).plus(self.rest(&b.anweisungen[i + 1..], &lokal));
                        return summe.plus(groesser(durch, vorbei));
                    }
                }
            }
            summe = summe.plus(self.anweisung(s, &lokal));
            self.binde(s, &mut lokal);
        }
        summe
    }

    fn rest(&self, anweisungen: &[Stmt], aussen: &Bindungen) -> Kosten {
        let mut lokal = aussen.clone();
        let mut summe = Kosten::Zahl(0);
        for (i, s) in anweisungen.iter().enumerate() {
            if let StmtArt::Wenn(w) = &s.art {
                if w.sonst.is_none() && w.zweige.len() == 1 {
                    let (bed, rumpf) = &w.zweige[0];
                    if crate::endet_immer(rumpf, &[]) {
                        let durch = self.ausdruck(bed, &lokal).plus(self.block(rumpf, &lokal));
                        let vorbei = self.ausdruck(bed, &lokal).plus(self.rest(&anweisungen[i + 1..], &lokal));
                        return summe.plus(groesser(durch, vorbei));
                    }
                }
            }
            summe = summe.plus(self.anweisung(s, &lokal));
            self.binde(s, &mut lokal);
        }
        summe
    }

    /// **What a statement leaves behind in NAMES** -- the one step this pass did not take
    /// until 2026-08-31.
    ///
    /// The value stands in the OLD scope (`let t = t;` reads the outer `t`), so the cost is
    /// computed first and the name bound after. **And a name whose type cannot be read here
    /// becomes `Unbekannt` rather than being passed over:** otherwise `typ_von_ort` falls
    /// back to the GLOBAL name, which is the same confusion one level up. *Unknown falls
    /// loud -- `K003` says "no bound" instead of naming a wrong one.*
    fn binde(&self, s: &Stmt, lokal: &mut Bindungen) {
        match &s.art {
            StmtArt::Let(l) => {
                let t = match &l.typ {
                    Some(td) => self.u.typ_von_ausdruck_decl(self.modul, td),
                    None => self.typ_des_wertes(&l.wert, lokal),
                };
                lokal.insert(l.name.text.clone(), t);
            }
            StmtArt::LetSonst(l) => {
                let t = match &l.quelle {
                    crate::LetQuelle::Ort(o) => self.u.typ_von_ort(self.modul, o, lokal),
                    _ => crate::typen::Typ::Unbekannt,
                };
                lokal.insert(l.name.text.clone(), t);
            }
            StmtArt::AwaitLoad(a) => {
                let t = self.u.typ_von_ort(self.modul, &a.quelle, lokal);
                lokal.insert(a.name.text.clone(), t);
            }
            StmtArt::Exchange(e) => {
                let t = match &e.form {
                    XForm::Vergleich { .. } => crate::typen::Typ::Wahrheit,
                    XForm::Update { .. } => self.u.typ_von_ort(self.modul, &e.ort, lokal),
                };
                lokal.insert(e.name.text.clone(), t);
            }
            _ => {}
        }
    }

    /// The type of a `let` value, as far as this pass can read it. **It only needs the
    /// CARRIERS of domains** -- tables, records, `walk` heads, field arrays -- and every one
    /// of those stands at a place. Everything else is `Unbekannt`, and that is the honest
    /// answer: a number here would be a guess.
    fn typ_des_wertes(&self, e: &Expr, lokal: &Bindungen) -> crate::typen::Typ {
        match &e.art {
            ExprArt::Ort(o) => self.u.typ_von_ort(self.modul, o, lokal),
            ExprArt::Klammer(i) => self.typ_des_wertes(i, lokal),
            _ => crate::typen::Typ::Unbekannt,
        }
    }

    fn anweisung(&self, s: &Stmt, lokal: &Bindungen) -> Kosten {
        match &s.art {
            // Eine Zuweisung ist eine Primitive, dazu was der Ausdruck kostet.
            StmtArt::Let(l) => Kosten::Zahl(1).plus(self.ausdruck(&l.wert, lokal)),
            StmtArt::Zuweisung(z) => Kosten::Zahl(1).plus(self.ausdruck(&z.wert, lokal)),
            StmtArt::Publish(p) => Kosten::Zahl(1).plus(self.ausdruck(&p.wert, lokal)),
            StmtArt::AwaitLoad(_) => Kosten::Zahl(1),
            // `narrow` senkt sich auf eine Bereichspruefung ab -- eine Rechenoperation.
            StmtArt::Exchange(e) => match &e.form {
                XForm::Update { rumpf, .. } => Kosten::Zahl(1).plus(self.block(rumpf, lokal)),
                // **A compare-exchange is the swap PLUS the expected value** (2026-09-02).
                //
                // Only `wert` -- the value written on success -- was counted, and the
                // EXPECTED value was not: the emitter computes it into `_cx1` before the
                // `atomic_compare_exchange_strong_explicit`, so a call there is paid for at
                // every attempt. *Word for word the sentence forty lines up about a
                // `retry`'s `until`: only counting the body means missing the most
                // expensive part.* Measured: `when old(AT) == teuer()` with a callee of 900
                // ops behind an envelope of 8 gave `0 errors`.
                XForm::Vergleich { wert, bedingung, .. } => Kosten::Zahl(1)
                    .plus(self.ausdruck(wert, lokal))
                    .plus(pred_kosten(self, bedingung, lokal)),
            },
            StmtArt::LetSonst(l) => {
                // **Ein `place` auszupacken kostet EINE Operation** -- die Ablesung. Ein
                // Ruf kostet, was der Gerufene zusagt.
                let quelle = match l.als_ruf() {
                    Some(r) => self.ruf(r, lokal),
                    None => Kosten::Zahl(1),
                };
                Kosten::Zahl(1).plus(quelle).plus(self.block(&l.sonst, lokal))
            }
            StmtArt::Ruf(r) => self.ruf(r, lokal),
            // Ein Ruecksprung ist keine der vier Primitiven; sein Ausdruck kostet.
            StmtArt::Return(Some(e)) => self.ausdruck(e, lokal),
            StmtArt::Return(None) | StmtArt::Leave(_) | StmtArt::Next(_) => Kosten::Zahl(0),
            // **Branches count the MAXIMUM** -- and the branch itself costs nothing: the
            // four primitives of the model are assignment, arithmetic, load, store. An `if`
            // is none of them; its CONDITION is.
            //
            // **And the conditions ACCUMULATE along the chain** (found 2026-08-24, while
            // writing the soundness argument for `kosten.summation`, `messung/K001.md`).
            // `WennStmt::zweige` is FLAT -- an `else if` is a further entry, not a nested
            // statement. A run that takes arm `i` has therefore evaluated conditions
            // `0..=i`, and a run that reaches `sonst` has evaluated all of them.
            //
            // > Until today each arm was counted as `condition_i + body_i`. Two functions of
            // > IDENTICAL meaning then measured differently: written as an `else if` chain
            // > over three conditions the body computed **2**, written as three sequential
            // > `if`s it computed **6** -- and `costs <= 2 ops` passed on the first with zero
            // > errors. *An UNDER-count, and the only kind that matters: `K001` is a bound.*
            //
            // *The sequential form was right all along* -- `block` walks it statement by
            // statement and sums. Only the flattened chain lost its prefix.
            StmtArt::Wenn(w) => {
                let mut hoechste = Kosten::Zahl(0);
                // The conditions every run reaching THIS arm has already paid for.
                let mut praefix = Kosten::Zahl(0);
                for (bed, rumpf) in &w.zweige {
                    praefix = praefix.plus(self.ausdruck(bed, lokal));
                    let z = praefix.clone().plus(self.block(rumpf, lokal));
                    hoechste = groesser(hoechste, z);
                }
                if let Some(sonst) = &w.sonst {
                    // Reaching `else` means every condition was evaluated and none held.
                    hoechste = groesser(hoechste, praefix.plus(self.block(sonst, lokal)));
                }
                // **Without `sonst` the fall-through path needs no arm of its own:** it costs
                // the full prefix, and the LAST arm already counts that prefix plus its body.
                hoechste
            }
            StmtArt::Match(m) => {
                let mut hoechste = Kosten::Zahl(0);
                for z in &m.zweige {
                    hoechste = groesser(hoechste, self.block(&z.rumpf, lokal));
                }
                self.ausdruck(&m.gegenstand, lokal).plus(hoechste)
            }
            StmtArt::Bricht(b) => self.block(&b.rumpf, lokal),
            StmtArt::Sperrt(l) => self.block(&l.rumpf, lokal),
            // **`observes` kostet die NAHME nicht** -- RCU nimmt nichts. Was es kostet, ist
            // der Rumpf und die zwei Marken; die zaehlen als eine Primitive.
            StmtArt::Observiert(o) => Kosten::Zahl(1).plus(self.block(&o.rumpf, lokal)),
            StmtArt::Narrow(n) => Kosten::Zahl(1).plus(groesser(
                Kosten::Zahl(0),
                self.block(&n.sonst, lokal),
            )),

            StmtArt::Schleife(sch) => self.schleife(sch, lokal),
        }
    }

    /// **Die Schleifen -- und hier steckt die eigentliche Aussage des Modells.**
    fn schleife(&self, sch: &Schleife, lokal: &Bindungen) -> Kosten {
        match sch {
            // Rumpfkosten x Domaenenschranke. Steht die Schranke nicht fest, steht auch
            // die Kostenzusage nicht fest -- und dann sagt der Pass das.
            // **The loop variable is BOUND in the body**, and it is no table -- it is a
            // place index. Where it shadows a parameter, `slots of i` must not inherit that
            // parameter's bound. *`m1.rs` binds it to `Unbekannt` at the same spot.*
            Schleife::Traverse(t) => match (
                self.block(&t.rumpf, &{
                    let mut innen = lokal.clone();
                    innen.insert(t.variable.text.clone(), Typ::Unbekannt);
                    innen
                }),
                self.domaenenschranke(&t.domaene, lokal),
            ) {
                (Kosten::Zahl(rumpf), Some(n)) => Kosten::Zahl(rumpf).mal(n, Some(t.span)),
                (Kosten::Unbekannt(g, s), _) => Kosten::Unbekannt(g, s),
                // **The text names the DECLARATION it is missing, and it is one of three.**
                //
                // Until 2026-08-31 it asked *"is the table missing its `count`?"* for every
                // domain -- and sent the reader of a `mappings of` after a table that does
                // not exist. Measured at `walk W levels 0`: the reader was looking for a
                // `count` while the real answer was three lines up. *A refusal that names
                // the wrong declaration costs more than one that names none.*
                (_, None) => Kosten::Unbekannt(
                    format!(
                        "the domain `{}` of the traversal has no bound from a declaration \
                         -- a table gets it from `count`, a `queue` from the single field \
                         array of its record, and a `walk` from `levels` and its node length",
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
                "a `forever` loop has no total cost -- its promise is `per_pass`, not `costs`"
                    .to_string(),
                Some(f.span),
            ),
        }
    }

    /// Die Schranke einer Domaene -- **umgezogen nach `domaene.rs` am 2026-08-19**, weil M1
    /// sie fuer «H2.1» braucht. *Eine Stelle, zwei Leser.*
    fn domaenenschranke(&self, d: &Domaene, lokal: &Bindungen) -> Option<i128> {
        crate::domaene::Sicht { u: self.u, modul: self.modul, lokal: lokal }
            .domaenenschranke(d)
    }

    fn ausdruck(&self, e: &Expr, lokal: &Bindungen) -> Kosten {
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
            // **`&f` costs NOTHING** («B8», 2026-08-21). It lowers to a link-time address,
            // and no Gabbro primitive is emitted for it -- the same argument as for a
            // constant, and it stands written out for the same reason.
            | ExprArt::FnWert(_)
            // **Ein Grundwert kostet NULL** (Stufe 7). Er wird zu einer
            // `enum`-Konstante -- kein Laden, keine Primitive. *Das ist dieselbe Zeile,
            // die `Some`/`None` hier brauchten, und sie steht aus demselben Grund
            // ausgeschrieben.*
            | ExprArt::Grund { .. }
            | ExprArt::Ergebnis => {
                Kosten::Zahl(0)
            }
            // **A load is a primitive -- and an index is an EXPRESSION.**
            //
            // Until 2026-09-02 this read `1 + <number of index suffixes>`: a figure that
            // COUNTS the index and never looks at it. Measured, the same function twice:
            //
            // ```text
            // let i = teuer(); return t.slots[i].x;   ->  K001  <= 3 ops, the body costs 103
            // return t.slots[teuer()].x;              ->  0 errors
            // ```
            //
            // `teuer` declares `costs <= 100 ops`. **And this `match` is EXHAUSTIVE** -- all
            // fourteen arms stand here and the compiler forces them
            // (`miss-erschoepfung.py`). *Exhaustiveness over the enumeration is not descent
            // into the node:* naming `ExprArt::Ort` and not entering its index is a branch
            // written out that still sees nothing. **The 43 hand-rolled walkers were the
            // question; this arm was never one of them and was blind anyway.**
            //
            // **The flat `1` was the cost of the COMMONEST index, not the cost of
            // indexing:** a bare name costs one load, and that is exactly what `ausdruck`
            // now returns for it. A constant index therefore costs nothing -- which the
            // first line of this very function already says about every constant.
            ExprArt::Ort(o) => crate::ausdruecke_im_ort(o)
                .into_iter()
                .fold(Kosten::Zahl(1), |k, ix| k.plus(self.ausdruck(ix, lokal))),
            ExprArt::Alt(_) => Kosten::Zahl(0),
            ExprArt::Klammer(i) => self.ausdruck(i, lokal),
            ExprArt::Unaer(_, i) => Kosten::Zahl(1).plus(self.ausdruck(i, lokal)),
            ExprArt::Binaer(_, a, b) => {
                Kosten::Zahl(1).plus(self.ausdruck(a, lokal)).plus(self.ausdruck(b, lokal))
            }
            // **`aligned(a, b)` evaluates TWO expressions, and both of them cost.**
            //
            // ```text
            // let i = teuer(); if aligned(i, 4) { … }   ->  K001  <= 3 ops, the body costs 102
            // if aligned(teuer(), 4) { … }              ->  0 errors
            // ```
            //
            // The same decision as in `wirkungen::liest_expr` and `geteilt::orte_in`, per
            // form and with the reason beside it: `aligned` evaluates both sides at run
            // time; `sizeof`/`lenof` over a place take their value from the DECLARATION
            // (`C001`), so the place is not loaded -- **but its indices are**.
            //
            // The `1` stays underneath: the alignment test itself is an operation, and over
            // a TYPE everything else about it is a compile-time constant.
            ExprArt::Eingebaut(g) => match &**g {
                Eingebaut::Aligned(a, b) => Kosten::Zahl(1)
                    .plus(self.ausdruck(a, lokal))
                    .plus(self.ausdruck(b, lokal)),
                Eingebaut::Sizeof(TypOderOrt::Ort(o)) | Eingebaut::Lenof(TypOderOrt::Ort(o)) => {
                    crate::ausdruecke_im_ort(o)
                        .into_iter()
                        .fold(Kosten::Zahl(1), |k, ix| k.plus(self.ausdruck(ix, lokal)))
                }
                Eingebaut::Sizeof(TypOderOrt::Typ(_)) | Eingebaut::Lenof(TypOderOrt::Typ(_)) => {
                    Kosten::Zahl(1)
                }
            },
            ExprArt::Ruf(r) => self.ruf(r, lokal),
        }
    }

    fn ruf(&self, r: &Ruf, lokal: &Bindungen) -> Kosten {
        // **An indirect call costs what its POINTER TYPE promises** («B8», 2026-08-21).
        //
        // This is the second half of why the contract sits at the type. The effect half keeps
        // `E008` compositional; this half keeps `K001` honest -- *without a `costs` clause at
        // the type an indirect call would cost zero, and a body full of them would come in
        // under any bound at all.*
        //
        // Both failure branches are `Unbekannt` WITH A REASON, never `Zahl(0)`: a cost that is
        // not known is a cost that is not known, and `K001` reads that as "cannot decide"
        // rather than as "free".
        if let Some(o) = r.place() {
            let args = r
                .argumente
                .iter()
                .fold(Kosten::Zahl(0), |a, e| a.plus(self.ausdruck(e, lokal)));
            return match self.u.typ_von_ort(self.modul, o, lokal) {
                crate::typen::Typ::FnPtr(v) => match v.costs {
                    Some(n) => args.plus(Kosten::Zahl(n)),
                    None => args.plus(Kosten::Unbekannt(
                        format!(
                            "the indirect call through `{}` has no constant `costs` bound",
                            o.text()
                        ),
                        Some(r.span),
                    )),
                },
                _ => args.plus(Kosten::Unbekannt(
                    format!(
                        "`{}` is not a function pointer here, so the call declares no costs",
                        o.text()
                    ),
                    Some(r.span),
                )),
            };
        }
        let name = r
            .path()
            .and_then(|p| p.teile.last())
            .map(|i| i.text.clone())
            .unwrap_or_default();
        let pfad_text = r.path().map(|p| p.text()).unwrap_or_default();
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
                .fold(Kosten::Zahl(1), |a, e| a.plus(self.ausdruck(e, lokal)));
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
                    a.plus(self.ausdruck(e, lokal))
                });
        }
        let uebergang = self
            .u
            .kandidaten_aufloesbar(self.modul, &name)
            .into_iter()
            .find_map(|k| self.u.uebergangskosten.get(&k).copied());
        // **Modulbewusst seit 2026-08-19.** Vorher gewann der zuletzt eingetragene
        // gleichnamige Name: `a::hilf costs <= 900` und `b::hilf costs <= 1` waren EIN
        // Eintrag, und welcher galt, entschied die Reihenfolge im Quelltext.
        let erklaert = self
            .u
            .kandidaten_aufloesbar(self.modul, &pfad_text)
            .into_iter()
            .find_map(|k| self.deklariert.get(&k).copied());
        // **Ein rekursiver Ruf unter einem `decreases` kostet hier NICHTS** («K5.4»): die
        // Tiefe trägt das Mass, die Zusage gilt je Durchgang.
        if let Some((g, selbst)) = &self.mit_mass {
            if let Some(ziel) = g.aufloesen(self.u, self.modul, &pfad_text) {
                if &ziel == selbst || g.im_zyklus(&ziel) {
                    return r
                        .argumente
                        .iter()
                        .fold(Kosten::Zahl(0), |a, e| a.plus(self.ausdruck(e, lokal)));
                }
            }
        }
        let mut summe = match erklaert.or(uebergang) {
            Some(n) => Kosten::Zahl(n),
            None => {
                // Kennt die Umgebung die Funktion ueberhaupt? Ein Aufruf ins Unbekannte
                // (extern, prim, Randfunktion) kostet unbekannt viel.
                if r.path().is_some_and(|p| self.u.funktion(self.modul, p).is_some()) {
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
            summe = summe.plus(self.ausdruck(a, lokal));
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
    fn schleifenzusagen(&self, b: &Block, aussen: &Bindungen, absagen: &mut Absagen) {
        let mut lokal = aussen.clone();
        for s in &b.anweisungen {
            if let StmtArt::Schleife(sch) = &s.art {
                let (rumpf, zusage_expr, wort, code, span) = match sch.as_ref() {
                    Schleife::Retry(r) => (&r.rumpf, &r.schranke, "bounded", "K006", r.span),
                    Schleife::Forever(f) => {
                        (&f.rumpf, &f.je_durchgang, "per_pass bounded", "K007", f.span)
                    }
                    Schleife::Traverse(t) => {
                        self.schleifenzusagen(&t.rumpf, &lokal, absagen);
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
                    symbolisch(self.u, self.modul, &lokal, zusage_expr).map(|t| t.fest)
                });
                if let (Some(zusage), Kosten::Zahl(n)) = (zahl, self.block(rumpf, &lokal)) {
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
                self.schleifenzusagen(rumpf, &lokal, absagen);
            } else {
                match &s.art {
                    StmtArt::Sperrt(l) => self.schleifenzusagen(&l.rumpf, &lokal, absagen),
                    StmtArt::Bricht(x) => self.schleifenzusagen(&x.rumpf, &lokal, absagen),
                    StmtArt::Narrow(x) => self.schleifenzusagen(&x.sonst, &lokal, absagen),
                    StmtArt::LetSonst(x) => self.schleifenzusagen(&x.sonst, &lokal, absagen),
                    StmtArt::Wenn(w) => {
                        for (_, r) in &w.zweige {
                            self.schleifenzusagen(r, &lokal, absagen);
                        }
                        if let Some(r) = &w.sonst {
                            self.schleifenzusagen(r, &lokal, absagen);
                        }
                    }
                    StmtArt::Match(m) => {
                        for z in &m.zweige {
                            self.schleifenzusagen(&z.rumpf, &lokal, absagen);
                        }
                    }
                    StmtArt::Exchange(e) => {
                        if let XForm::Update { rumpf, .. } = &e.form {
                            self.schleifenzusagen(rumpf, &lokal, absagen);
                        }
                    }
                    _ => {}
                }
            }
            self.binde(s, &mut lokal);
        }
    }

    /// **K002.** Ein `locks`-Block, dessen Rumpfkosten die `held`-Zusage der Sperre
    /// uebersteigen, ist ein Uebersetzungsfehler (`SPRACHE.md` §9.3, Punkt 1). Daran haengt
    /// die Latenzaussage je Wartestelle -- ohne diese Pruefung ist sie eine Behauptung.
    fn sperrbloecke(&self, b: &Block, aussen: &Bindungen, absagen: &mut Absagen) {
        let mut lokal = aussen.clone();
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
                        .kandidaten_aufloesbar(self.modul, &l.sperre.text())
                        .into_iter()
                        .find_map(|k| topf.get(&k));
                    if let (Some(zusage), Kosten::Zahl(n)) = (zeit, self.block(&l.rumpf, &lokal)) {
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
                    self.sperrbloecke(&l.rumpf, &lokal, absagen);
                }
                StmtArt::Wenn(w) => {
                    for (_, r) in &w.zweige {
                        self.sperrbloecke(r, &lokal, absagen);
                    }
                    if let Some(r) = &w.sonst {
                        self.sperrbloecke(r, &lokal, absagen);
                    }
                }
                StmtArt::Match(m) => {
                    for z in &m.zweige {
                        self.sperrbloecke(&z.rumpf, &lokal, absagen);
                    }
                }
                StmtArt::Bricht(x) => self.sperrbloecke(&x.rumpf, &lokal, absagen),
                StmtArt::Narrow(x) => self.sperrbloecke(&x.sonst, &lokal, absagen),
                StmtArt::LetSonst(x) => self.sperrbloecke(&x.sonst, &lokal, absagen),
                StmtArt::Schleife(sch) => match sch.as_ref() {
                    Schleife::Traverse(x) => self.sperrbloecke(&x.rumpf, &lokal, absagen),
                    Schleife::Retry(x) => self.sperrbloecke(&x.rumpf, &lokal, absagen),
                    Schleife::Forever(x) => self.sperrbloecke(&x.rumpf, &lokal, absagen),
                },
                _ => {}
            }
            self.binde(s, &mut lokal);
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
    // **A generated operation declares its cost by COUNTING its own stores** (2026-08-28).
    // Without this line a call to `T::insert` is `K003` -- *"a cost promise over an unknown
    // quantity"* -- and `D001` would forbid the hand-written mutation while making the
    // generated one uncostable. `messung/OPS-RUFFORM.md`.
    let mut deklariert: HashMap<String, i128> = crate::opsruf::kosten(baum);
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
        "-- What the body COSTS, beside what the line PROMISES. Whoever writes a\n\
         -- promise copies down what stands here -- a `costs` line is a measurement,\n\
         -- not an estimate.\n\
         -- site\tcomputed\tpromised\tslack\n",
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
        match r.block(b, &r.lokal.clone()) {
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
        r.bloecke_zeigen(b, &r.lokal.clone(), &f.name.text, &mut out);
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
    fn bloecke_zeigen(&self, b: &Block, aussen: &Bindungen, wo: &str, out: &mut String) {
        let mut lokal = aussen.clone();
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
                    .kandidaten_aufloesbar(self.modul, &name)
                    .into_iter()
                    .find_map(|k| topf.get(&k).copied());
                if let Kosten::Zahl(n) = self.block(&l.rumpf, &lokal) {
                    out.push_str(&format!(
                        "  {wo} / {wort} {name}\t{n}\t{}\n",
                        spalte(zeit, n)
                    ));
                }
                self.bloecke_zeigen(&l.rumpf, &lokal, wo, out);
            }
            self.binde(s, &mut lokal);
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
    // **A generated operation declares its cost by COUNTING its own stores** (2026-08-28).
    // Without this line a call to `T::insert` is `K003` -- *"a cost promise over an unknown
    // quantity"* -- and `D001` would forbid the hand-written mutation while making the
    // generated one uncostable. `messung/OPS-RUFFORM.md`.
    let mut deklariert: HashMap<String, i128> = crate::opsruf::kosten(baum);
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
    let rumpf = rechner.block(&r.rumpf, &rechner.lokal.clone());
    let bedingung = match &r.bis {
        Some(p) => pred_kosten(&rechner, p, &rechner.lokal.clone()),
        None => Kosten::Zahl(0),
    };
    match rumpf.plus(bedingung) {
        Kosten::Zahl(n) if n > 0 => Some(n),
        _ => None,
    }
}

/// Die Kosten eines Praedikats -- fuer den `until`-Test, der bei jedem Durchgang laeuft.
fn pred_kosten(r: &Rechner, p: &Pred, lokal: &Bindungen) -> Kosten {
    match &p.art {
        PredArt::Vergleich(e) | PredArt::Element(e, _) => r.ausdruck(e, lokal),
        PredArt::Klammer(x) | PredArt::Nicht(x) => pred_kosten(r, x, lokal),
        PredArt::Und(a, b) | PredArt::Oder(a, b) => pred_kosten(r, a, lokal).plus(pred_kosten(r, b, lokal)),
        _ => Kosten::Zahl(1),
    }
}

/// **Jeder Ruf im Rumpf, mit seinen Argumentausdruecken.** Ueber die erschoepfenden Laeufer
/// aus `lib.rs` -- ein Ruf in Indexposition ist auch ein Ruf.
fn sammle_rufe_roh<'a>(b: &'a Block, aus: &mut Vec<&'a Ruf>) {
    for s in &b.anweisungen {
        if let StmtArt::Ruf(r) = &s.art {
            aus.push(r);
        }
        for e in crate::eigene_ausdruecke(s) {
            for x in crate::alle_ausdruecke(e) {
                if let ExprArt::Ruf(r) = &x.art {
                    aus.push(r);
                }
            }
        }
        for pr in crate::eigene_praedikate(s) {
            for e in crate::ausdruecke_im_praedikat(pr) {
                for x in crate::alle_ausdruecke(e) {
                    if let ExprArt::Ruf(r) = &x.art {
                        aus.push(r);
                    }
                }
            }
        }
        for k in crate::unterbloecke(s) {
            sammle_rufe_roh(k, aus);
        }
    }
}

/// **Faellt das Mass an dieser Stelle NACHWEISLICH?**
///
/// Zwei Formen werden angenommen, beide mit der Massgroesse links und einer Konstanten
/// rechts:
///
/// ```text
/// n - k     mit k >= 1
/// n / k     mit k >= 2
/// ```
///
/// Alles andere faellt -- auch `m` (eine Vertauschung ist eine Aenderung, aber kein Abstieg)
/// und `n + 1` (eine Aenderung nach OBEN). *Aus der strengen Lesart kann man lockern, nie
/// umgekehrt.*
fn faellt_syntaktisch(arg: Option<&Expr>, mass: &str) -> bool {
    // **This pass had the right line and kept it to itself.** Three others asked the same
    // question with a bare `if let` and a bracket answered no (`O004`, `D005`, `L107`,
    // measured 2026-09-02); the line now stands once, in `lib.rs`.
    use crate::ohne_klammern;
    let Some(a) = arg else { return false };
    let ExprArt::Binaer(op, links, rechts) = &ohne_klammern(a).art else {
        return false;
    };
    let links_ist_mass = matches!(
        &ohne_klammern(links).art,
        ExprArt::Ort(o) if o.suffixe.is_empty() && o.basis.text == mass
    );
    if !links_ist_mass {
        return false;
    }
    let ExprArt::Zahl(k) = ohne_klammern(rechts).art else {
        return false;
    };
    match op {
        BinOp::Minus => k >= 1,
        BinOp::Geteilt => k >= 2,
        _ => false,
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
    // **Die Rufe mit ihren ARGUMENTAUSDRUECKEN**, nicht nur mit deren Namen: `kanten_von`
    // liefert `Option<String>` je Argument, und `None` heisst dort nur *„irgendein
    // gerechneter Ausdruck"*. Genau der ist hier die Frage.
    let mut rufe: Vec<&Ruf> = Vec::new();
    sammle_rufe_roh(b, &mut rufe);
    for r in &rufe {
        // **The descent measure asks after RECURSION, and an indirect call is not one it can
        // see.** `decreases` is checked at the recursive call site, and which site is
        // recursive is decided by resolving the callee's name against the cycle. A place has
        // no name, so this loop skips it -- *and the skip is not free: the cost pass has
        // already refused an indirect call with no `costs` bound (`Kosten::Unbekannt`), so a
        // recursion smuggled through a function pointer cannot come in at zero.*
        let Some(pfad) = &r.path().map(|p| p.text()) else {
            continue;
        };
        let argumente = &r.argumente;
        let Some(ziel) = g.aufloesen(u, modul, pfad) else {
            continue;
        };
        // Nur ZURUECK in den Zyklus: ein Ruf auf etwas, das uns wieder erreicht.
        if ziel != voll && !g.im_zyklus(&ziel) {
            continue;
        }
        // **`bewegt` war zu wenig, und es war die falsche Frage** (Rezension 2026-08-20).
        //
        // Die alte Bedingung fragte nur, ob sich IRGENDETWAS aendert. Eine VERTAUSCHUNG ist
        // eine Aenderung:
        //
        // ```gabbro
        // impl fn g(n : u32 in 0..8, m : u32 in 0..8) decreases n { … return g(m, n); }
        // ```
        //
        // ging mit null Fehlern durch -- `emit`, `cc`, und `g(1,1)` endete mit `SIGSEGV`.
        // Ein STEIGENDES Mass (`g(n + 1, m)`) fiel nur zufaellig, weil `n + 1` den Bereich
        // `0 .. 8` verlaesst; mit einem weiteren Typ waere es durchgegangen.
        //
        // > *Der Code sagte ehrlich „die notwendige Bedingung"; der README fuehrte
        // > `termination` ohne Vorbehalt unter den getragenen Klassen.* Von den zwei
        // > moeglichen Antworten -- Regel schaerfen oder Zusage zuruecknehmen -- ist dies
        // > die erste.
        //
        // Gefordert wird jetzt eine **pruefbare hinreichende Form**: an mindestens einer
        // Massstelle steht `n - k` oder `n / k` mit konstantem `k >= 1` bzw. `>= 2`, und
        // links davon die Massgroesse selbst. Alles andere faellt.
        //
        // **Aus der strengen Lesart kann man lockern, nie umgekehrt** (dieselbe Begruendung
        // wie bei den Phasen, `PLAN.md` K11.1). Der Korpus schreibt ausschliesslich
        // `f(n - 1)`, also kostet die Strenge dort nichts.
        let bewegt = stellen.iter().any(|i| {
            faellt_syntaktisch(argumente.get(*i), &f.parameter[*i].name.text)
        });
        if !bewegt {
            absagen.schiebe(
                Absage::fehler(
                    "K009",
                    f.name.span,
                    format!(
                        "the recursive call to `{pfad}` does not visibly LOWER any size of \
                         the `decreases` of `{}`",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "accepted are `n - k` (k >= 1) and `n / k` (k >= 2) with the measure \
                     itself on the left -- a swap (`g(m, n)`) changes the argument without \
                     lowering the measure, and `n + 1` raises it",
                )
                .mit_notiz(
                    "checked is the NECESSARY condition: THAT it falls is the prover's \
                     business (`consuming.ordnung`)",
                ),
            );
        }
    }
}

/// Ueber `crate::alle_orte` -- ein Name in Indexposition ist ein genannter Name
/// (2026-08-20).
fn namen_im_ausdruck(e: &Expr, aus: &mut Vec<String>) {
    aus.extend(crate::alle_orte(e).into_iter().map(|o| o.basis.text.clone()));
}
