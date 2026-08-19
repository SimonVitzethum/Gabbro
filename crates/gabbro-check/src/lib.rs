//! **Die Pruefpaesse, in fester Reihenfolge.**
//!
//! `SPRACHE.md` Teil III §6 legt die Architektur fest:
//!
//! > Lexer → Parser (aus der vereinigten EBNF, handgeschrieben, kein Generator) → ein Kernbaum
//! > → **Pruefpaesse in fester Reihenfolge** (Namen, D1/D2, M1+V1–V3, M3, M2, M4/Schleifen,
//! > Paarung, effects, costs) → C-Emission.
//! >
//! > *jede Regel dieser drei Dokumente ist genau **ein** Pass oder ein benannter Teil eines
//! > Passes -- die Spezifikation ist die Passliste*
//!
//! Deshalb steht die Liste hier **vollstaendig**, samt der Paesse, die es noch nicht gibt.
//! Ein Pass mit Zustand [`Zustand::Offen`] prueft nichts und **sagt das**: ein Werkzeug, das
//! ungeprueftes Schweigen wie ein Gruen aussehen laesst, ist ein falsches Gruen -- dieselbe
//! Fehlerklasse, die `pruefe-syntax.sh` zweimal bezahlt hat.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::Absagen;

pub mod aufrufgraph;
// **«B24» an EINER Stelle** -- der Namenspass sagt ab, der Erzeuger rechnet damit.
pub mod bitlage;
// Die Domaenenschranke -- kosten.rs und m1.rs lesen dieselbe.
pub mod domaene;
pub mod m2;
pub mod m3;
pub mod paarung;
pub mod gruppe;
pub mod emit;
pub mod geteilt;
pub mod kbedingung;
pub mod kontexte;
pub mod kosten;
mod m1;
mod namen;
mod schleifen;
mod wirkungen;

pub mod typen;
pub mod umgebung;

pub use m1::Zaehlung;
pub use kosten::Zaehlung as Kostenzaehlung;

pub mod korpus;
pub mod manifest;
// **P6, die Messsonde** -- was ein Mensch noch schuldet, gezaehlt statt eingeloest.
pub mod pflichten;
pub mod phasen;
pub mod schablonen;
pub mod zeugnis;

/// Was ein Pass heute leistet.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Zustand {
    /// Gebaut und in diesem Lauf gefahren.
    Gebaut,
    /// **Gebaut, aber mit benannten Loechern.** Die Gegenpruefung vom 2026-08-14 fand
    /// Dateien, die durchkamen und fallen mussten; der Text nennt, was heute noch
    /// durchkommt. *Ein teilgebauter Pass, der sich als gebaut meldet, ist ein falsches
    /// Gruen -- und genau das war er, bis diese Stufe dazukam.*
    Teilgebaut(&'static str),
    /// Nicht gebaut. Der Text nennt, was fehlt -- und was damit **ungeprueft** ist.
    Offen(&'static str),
}

/// Ein Pass der festen Reihenfolge.
pub struct Pass {
    pub nummer: u32,
    pub name: &'static str,
    /// Fundstelle der Regel, die dieser Pass abnimmt.
    pub quelle: &'static str,
    pub zustand: Zustand,
}

/// Die Passliste. **Die Reihenfolge ist Teil der Festlegung, nicht des Geschmacks.**
pub fn passliste() -> Vec<Pass> {
    vec![
        Pass {
            nummer: 1,
            name: "Namen",
            quelle: "E5: every declaration is complete in exactly one place",
            zustand: Zustand::Gebaut,
        },
        Pass {
            nummer: 2,
            name: "D1/D2",
            quelle: "SPRACHE.md §3: undurchsichtige Neutypen, vollstaendige Layouts, \
                     erschoepfende Aufzaehlung",
            zustand: Zustand::Teilgebaut(
                "the K condition is built (`D001`: no hand mutation on a `table` with \
                    `ops`), and since 2026-08-18 opacity BITES: an `opaque type` does not \
                    have the arithmetic of its carrier (`D003`). *Before that `a + b` fell \
                    only by accident -- at `M104`, not at the opacity; wherever the widths \
                    worked out, the nonsense went through.* **And since the same day the \
                    WALL stands behind it** (`D004`): the implicit conversion went through \
                    silently in BOTH directions, so D1 was not enforced at all. The door is \
                    the MODULE BOUNDARY -- inside the declaring module the representation is \
                    known, outside it is not. *On this corpus it has zero bite: all twelve \
                    declarations declare and use in the same module.* **NOT built: \
                    exhaustive `match` over `tagged`**",
            ),
        },
        Pass {
            nummer: 3,
            name: "M1 + V1–V3",
            quelle: "SPRACHE.md §3.2: range types and the three flow rules",
            zustand: Zustand::Gebaut,
        },
        Pass {
            nummer: 4,
            name: "M3",
            quelle: "SYNTAX.md §3: Adressraeume und Zugriffsrechte am Zeiger",
            zustand: Zustand::Teilgebaut(
                "built: rights checking at reads and writes, the placement rule that an \
                    `ops` carrier is not in the `dma` space (`R001`-`R003`). **NOT built: \
                    the barrier from the space** -- which barrier a `dma` access demands is \
                    a statement about the memory model, the same axiom layer as at the \
                    pairing. **And no alias analysis**: two `ptr<normal, rw>` to the same \
                    object stay indistinguishable, and `own` is what stands for that",
            ),
        },
        Pass {
            nummer: 5,
            name: "M2",
            quelle: "SPRACHE.md §4: lineare und geisterhafte Werte",
            zustand: Zustand::Teilgebaut(
                "built: exactly-once per path, branch matching, `consumes` against \
                    borrowed (`L101`-`L105`). **NOT built: the ghost erasure** -- a `ghost`\
                    value does not exist at run time, its linearity is a statement about the \
                    PROOF, and the alias question belongs to M3. **Since 2026-08-17 the \
                    ORDER stands beside it** (pass 11) -- M2 sees the chain, not which one",
            ),
        },
        // **«B37» -- der elfte Pass, und er ist die zweite Haelfte von M2.**
        //
        // Die Nummer haengt hinten, weil die Reihenfolge der Liste die Reihenfolge der Fahrt
        // ist und `phasen` direkt hinter M2 laeuft; die Zaehlung der SPRACHE.md-Liste bleibt
        // damit unangetastet. *Ein Pass, der sich in die Numerierung einer Spezifikation
        // draengt, verschiebt jede Fundstelle, die auf sie zeigt.*
        // **Der zwoelfte -- und er stand die ganze Zeit da, ohne gefuehrt zu werden.**
        //
        // `geteilt.rs` traegt seit dem 2026-08-15 die Sperrdisziplin (`H001`-`H006`) und ist
        // in KEINER Zeile dieser Liste aufgetaucht. Gefunden am 2026-08-17, beim Eintragen
        // von `H007`/`H008` -- *ein Pass mit acht Absagecodes, den die Liste nicht kennt.*
        //
        // > Dieselbe Lage, in der die Schablonen vor ihrer Auszaehlung waren: **vorhanden,
        // > wirksam und unbeziffert.** Die Liste ist die Zaehlspalte des Pruefers; was nicht
        // > drinsteht, kann niemand vermissen.
        Pass {
            nummer: 12,
            name: "Sperren",
            quelle: "SPRACHE.md §9: `rank`, `held`, `protects` -- die Sperrdisziplin",
            zustand: Zustand::Teilgebaut(
                "built: shared against exclusive (`H001`-`H004`), the intermediate rule \
                    at the call boundary (`H005`), the recomputed rank order (`H006`) -- and \
                    since K11.2.1 `protects` bites: every access to a protected place stands \
                    under its lock (`H007`), and a lock that is never taken shows up\
                    (`H008`). **And since «K5» the whole discipline**: a `locks` effect \
                    that nobody redeems (`H011`), the rank order THROUGH calls (`H012`), a \
                    rank that is not constant-evaluable (`H014`), and the EXECUTION \
                    CONTEXTS -- an `entry ... dispatch` names one, and a place written \
                    through it that nothing declares shared falls (`H013`). *The sentence \
                    \"Gabbro does not say who runs concurrently\" was overtaken by its own \
                    `entry` construct.* **NOT built: the finer half** -- `masks IRQ`, \
                    `per cpu` and `nested never` only exempt under `assume ein_kern`, and \
                    on this corpus `H013` has ZERO bite (all four context roots dispatch \
                    to an `extern fn`): `gabbro kontexte` prints the count beside it",
            ),
        },
        Pass {
            nummer: 11,
            name: "Phasen",
            quelle: "MESSUNGEN.md, «B37»: Linearitaet ist keine Ordnung",
            zustand: Zustand::Teilgebaut(
                "built: the stages of an `order` exist and `advances` goes FORWARD\
                    (`O001`/`O002`), the mark stands at its source stage at the call\
                    (`O003`), and the body composes into its own promise (`O004`). **And \
                    since K11.1 the branch**: all branches must reach the same stage\
                    (`O006`); a branch that ENDS with `return` does not join, and a step in \
                    a LOOP is refused -- a step happens once, a loop often. **NOT built: the \
                    softer reading** -- carrying a set of stages and letting all of them \
                    accept the next step. *From the strict reading one can loosen, never the \
                    other way* (PLAN.md, K11.1)",
            ),
        },
        Pass {
            nummer: 6,
            name: "M4/Schleifen",
            quelle: "SYNTAX.md §8: three loop forms, `leave`/`next` target a label",
            zustand: Zustand::Gebaut,
        },
        Pass {
            nummer: 7,
            name: "Paarung",
            quelle: "SPRACHE.md part II §1: ordering is PAIRED, not declared",
            zustand: Zustand::Teilgebaut(
                "built: `publishes`/`awaits`/`exchange` over the united set, name \
                    equality after index substitution (`V001`-`V004`). **NOT built: the \
                    statement about the MEMORY MODEL** -- that `release`/`acquire` establish \
                    the visibility the pairing claims falls into the axiom layer and not \
                    into this pass",
            ),
        },
        Pass {
            nummer: 8,
            name: "effects",
            quelle: "SPRACHE.md §7: `effects` is mandatory and not fail-open",
            zustand: Zustand::Teilgebaut(
                "writes, `locks` **and since 2026-08-16 reads** (reading A, `E010`) are \
                    held against the list. **What is missing is the reach of `E010`:** it \
                    speaks only about known world state (`static`, `atomic`, `table`, \
                    `device`, `state`), because a variant is not a place and an EXCERPT does \
                    not declare its names -- on the fragment corpus the rule therefore has\
                    **zero bite**, and its evidence comes from poison 62 and two mutations, \
                    not from the corpus",
            ),
        },
        // **Pass 10 ist neu, und das ist eine Aenderung an der Spezifikation.**
        //
        // `SPRACHE.md` Teil III §6 legt neun Paesse fest und sagt: *„die Spezifikation IST die
        // Passliste"*. Ein zehnter Pass heisst also nicht „ein Modul mehr", sondern **die
        // Liste ist gewachsen** -- und das gehoert gebucht, nicht eingeschoben. Der Grund ist
        // gemessen (`MESSUNGEN.md`, SWEEP, V4) und nicht entworfen: eine Invariante ZWISCHEN
        // Traegern hat in den neun Paessen keine Stelle. Pass 2 prueft Deklarationen, Pass 8
        // die Wirkungsliste einer Funktion gegen ihren Rumpf -- keiner von beiden kennt einen
        // Verbund.
        Pass {
            nummer: 10,
            name: "Gruppe",
            quelle: "MESSUNGEN.md, SWEEP der Verbindungs-Invarianten (2026-08-16), V4",
            zustand: Zustand::Teilgebaut(
                "built: the LOCK FOOTPRINT (`U001`-`U005`), the MOVE (`U006`) and the \
                    CONNECTING STATEMENT as a form (`U007`: a group invariant names at least \
                    two carriers, otherwise it belongs at the table). **NOT built: the \
                    preservation** -- that the invariant HOLDS under an operation is the \
                    prover's business and falls to S16/S17, not to this pass. It checks the \
                    three conditions under which the question can be asked at all",
            ),
        },
        Pass {
            nummer: 9,
            name: "costs",
            quelle: "SPRACHE.md §7: 1 op = one Gabbro primitive, computed statically",
            zustand: Zustand::Teilgebaut(
                "bodies, `locks` blocks against `held` and calls over the DECLARED costs \
                    of the callee are computed -- **recursion therefore carries an \
                    assumption instead of a computation**, and `per_pass` with an input-\
                    dependent bound is not settled",
            ),
        },
    ]
}

/// Was ein Lauf angesehen hat. **Steht neben dem Ergebnis, nicht dahinter:** eine Zahl
/// ueber die Deckung ist der Unterschied zwischen „nichts gefunden" und „nichts angesehen".
#[derive(Debug, Clone, Copy, Default)]
pub struct Bericht {
    pub m1: Zaehlung,
    pub kosten: Kostenzaehlung,
}

/// Fahrt aller **gebauten** Paesse ueber einen Baum, in der Reihenfolge der Liste.
pub fn pruefe(baum: &Programm, absagen: &mut Absagen) -> Bericht {
    if std::env::var("GABBRO_ZEIT").is_ok() {
        macro_rules! z { ($n:expr, $e:expr) => {{ let t = std::time::Instant::now(); $e; eprintln!("{:>10} {:?}", $n, t.elapsed()); }} }
        z!("namen", namen::pass(baum, absagen));
        z!("kbed", kbedingung::pass(baum, absagen));
        let m1 = { let t = std::time::Instant::now(); let r = m1::pass(baum, absagen); eprintln!("{:>10} {:?}", "m1", t.elapsed()); r };
        z!("schleifen", schleifen::pass(baum, absagen));
        z!("wirkungen", wirkungen::pass(baum, absagen));
        z!("geteilt", geteilt::pass(baum, absagen));
        z!("m3", m3::pass(baum, absagen));
        z!("m2", m2::pass(baum, absagen));
        z!("phasen", phasen::pass(baum, absagen));
        z!("paarung", paarung::pass(baum, absagen));
        z!("gruppe", gruppe::pass(baum, absagen));
        let kosten = { let t = std::time::Instant::now(); let r = kosten::pass(baum, absagen); eprintln!("{:>10} {:?}", "kosten", t.elapsed()); r };
        return Bericht { m1, kosten };
    }
    namen::pass(baum, absagen);
    kbedingung::pass(baum, absagen);
    let m1 = m1::pass(baum, absagen);
    schleifen::pass(baum, absagen);
    wirkungen::pass(baum, absagen);
    geteilt::pass(baum, absagen);
    m3::pass(baum, absagen);
    m2::pass(baum, absagen);
    // **«B37», seit 2026-08-17.** M2 sieht, dass eine lineare Marke genau einmal
    // weitergereicht wird -- nicht, in welcher REIHENFOLGE. Dieser Pass steht direkt
    // dahinter, weil er auf derselben Kette arbeitet und die andere Haelfte prueft.
    phasen::pass(baum, absagen);
    paarung::pass(baum, absagen);
    gruppe::pass(baum, absagen);
    let kosten = kosten::pass(baum, absagen);
    Bericht { m1, kosten }
}

/// Was dieser Lauf **nicht** geprueft hat -- zum Abdrucken neben dem Ergebnis.
pub fn ungeprueft() -> Vec<Pass> {
    passliste()
        .into_iter()
        .filter(|p| matches!(p.zustand, Zustand::Offen(_) | Zustand::Teilgebaut(_)))
        .collect()
}

/// Laeuft ueber jedes Item, auch die in Modulen.
pub(crate) fn fuer_jedes_item(baum: &Programm, f: &mut impl FnMut(&Item)) {
    fuer_jedes_item_im_modul(baum, &mut |i, _| f(i));
}

/// Wie oben, aber **mit dem Modulpfad**. Ohne ihn kann ein Pass einen Namen nicht
/// aufloesen -- er sieht `nimm` und weiss nicht, ob `eins::nimm` oder `zwei::nimm` gemeint
/// ist. Genau daran loeschte M1 bis zum 2026-08-14 Bereichspruefungen stillschweigend.
/// Sammelt die Annahmenschicht: Name -> ist sie falsifizierbar?
///
/// `assume` und `axiom` fuehren dieselbe Klasse (`AnnahmeKlasse`), und beide duerfen einen
/// Fortschritt tragen -- *wer die Schleife beendet, kann eine Umgebungszusage sein oder eine
/// Maschineneigenschaft.*
pub fn annahmen(baum: &Programm) -> std::collections::BTreeMap<String, bool> {
    let mut aus = std::collections::BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        let (name, klasse) = match &item.art {
            ItemArt::Assume(a) => (&a.name, &a.klasse),
            ItemArt::Axiom(a) => (&a.name, &a.klasse),
            _ => return,
        };
        aus.insert(
            name.text.clone(),
            matches!(klasse, AnnahmeKlasse::Falsifizierbar(_)),
        );
    });
    aus
}

pub fn fuer_jedes_item_im_modul(baum: &Programm, f: &mut impl FnMut(&Item, &str)) {
    fn geh(items: &[Item], pfad: &str, f: &mut impl FnMut(&Item, &str)) {
        for i in items {
            f(i, pfad);
            if let ItemArt::Modul(m) = &i.art {
                let innen = if pfad.is_empty() {
                    m.pfad.text()
                } else {
                    format!("{pfad}::{}", m.pfad.text())
                };
                geh(&m.items, &innen, f);
            }
        }
    }
    geh(&baum.items, "", f);
}

/// **Die Unterblöcke einer Anweisung — erschöpfend über `StmtArt`, ohne `_`-Zweig.**
///
/// Der teuerste Einzelbefund vom 2026-08-19, und er war kein Loch, sondern **78 Löcher
/// derselben Bauart**: jeder Pass stieg selbst in die Anweisungen ab, jeder mit einem
/// `_ => {}` am Ende, und **jeder vergass einen anderen Arm**. Gemessen:
///
/// | Anweisungsart | unsichtbar für |
/// |---|---|
/// | `observes` | `m3`, `phasen`, `paarung`, `gruppe`, **`aufrufgraph`** |
/// | `awaits`-Laden | sieben Pässe |
/// | `exchange` | `m2`, `m3`, `phasen` |
///
/// Die Zeile, die es zeigte: ein Ruf **in** einem `observes`-Block kam im Aufrufgraphen
/// nicht an, und damit verschwanden zwei `E008` — `masks IRQ` und `writes G` standen im
/// Gerufenen und in keiner Wirkungsliste. *Derselbe Ruf eine Zeile höher fiel.*
///
/// > **Ein `_`-Zweig ist kein Vorbehalt, sondern eine stille Zusage:** *„hier steht nichts,
/// > was mich angeht"* — und niemand prüft sie nach, wenn eine Anweisungsart dazukommt.
///
/// Wer hier absteigt, bekommt einen **Übersetzungsfehler**, sobald `StmtArt` wächst. Das ist
/// der Unterschied zwischen einer Lücke, die man findet, und einer, die man erbt.
pub fn unterbloecke(s: &Stmt) -> Vec<&Block> {
    match &s.art {
        StmtArt::Wenn(w) => {
            let mut v: Vec<&Block> = w.zweige.iter().map(|(_, b)| b).collect();
            v.extend(w.sonst.as_ref());
            v
        }
        StmtArt::Match(m) => m.zweige.iter().map(|z| &z.rumpf).collect(),
        StmtArt::Schleife(sch) => vec![match sch.as_ref() {
            Schleife::Traverse(x) => &x.rumpf,
            Schleife::Retry(x) => &x.rumpf,
            Schleife::Forever(x) => &x.rumpf,
        }],
        StmtArt::Bricht(x) => vec![&x.rumpf],
        StmtArt::Narrow(x) => vec![&x.sonst],
        StmtArt::Sperrt(x) => vec![&x.rumpf],
        StmtArt::Observiert(x) => vec![&x.rumpf],
        StmtArt::LetSonst(x) => vec![&x.sonst],
        StmtArt::Exchange(e) => match &e.form {
            XForm::Update { rumpf, .. } => vec![rumpf],
            XForm::Vergleich { .. } => Vec::new(),
        },
        // Die blattartigen Formen — und sie stehen **einzeln** da, damit eine neue Art hier
        // auffällt statt in einem Sammelzweig zu verschwinden.
        StmtArt::Let(_)
        | StmtArt::Zuweisung(_)
        | StmtArt::Leave(_)
        | StmtArt::Next(_)
        | StmtArt::Publish(_)
        | StmtArt::AwaitLoad(_)
        | StmtArt::Return(_)
        | StmtArt::Ruf(_) => Vec::new(),
    }
}

/// **Die Ausdrücke, die eine Anweisung SELBST auswertet** — erschöpfend, wie oben.
///
/// Nicht die der Unterblöcke: wer beides will, nimmt beide Helfer. Getrennt, weil die
/// meisten Pässe für einen Rumpf einen eigenen Zustand führen (ein Zweig hat seinen).
pub fn eigene_ausdruecke(s: &Stmt) -> Vec<&Expr> {
    match &s.art {
        StmtArt::Let(l) => vec![&l.wert],
        StmtArt::Zuweisung(z) => vec![&z.wert],
        StmtArt::Return(e) => e.iter().collect(),
        StmtArt::Publish(p) => vec![&p.wert],
        StmtArt::Wenn(w) => w.zweige.iter().map(|(b, _)| b).collect(),
        StmtArt::Match(m) => vec![&m.gegenstand],
        StmtArt::Exchange(e) => match &e.form {
            XForm::Vergleich { wert, .. } => vec![wert],
            XForm::Update { .. } => Vec::new(),
        },
        // `let x = f() else …` trägt seinen Ruf in der Quelle, nicht in einem `Expr`.
        StmtArt::LetSonst(_)
        | StmtArt::Ruf(_)
        | StmtArt::Schleife(_)
        | StmtArt::Bricht(_)
        | StmtArt::Narrow(_)
        | StmtArt::Sperrt(_)
        | StmtArt::Observiert(_)
        | StmtArt::Leave(_)
        | StmtArt::Next(_)
        | StmtArt::AwaitLoad(_) => Vec::new(),
    }
}

/// **Endet der Block auf jedem Weg?** — erschöpfend über `StmtArt`, ohne `_`-Zweig.
///
/// Stand dreimal im Prüfer (`kosten`, `phasen`, `schleifen`), **jedes Mal unvollständig und
/// jedes Mal anders**: alle drei schlossen mit `_ => false`, und damit galt
/// `locks L { return x; }` als *fällt durch* — obwohl es die Funktion verlässt. Für `M2` und
/// die Phasen heisst das: ein Zweig, der über eine Klammer endet, wurde in den Abgleich
/// genommen und musste sich mit den anderen einigen.
///
/// `divergent` nennt die Funktionen, deren Aufruf nicht zurückkehrt (`-> never`); ohne die
/// Liste ist ein `zeitablauf();` als letzte Anweisung nur ein Ruf.
pub fn endet_immer(b: &Block, divergent: &[String]) -> bool {
    let Some(letzte) = b.anweisungen.last() else {
        return false;
    };
    match &letzte.art {
        StmtArt::Return(_) | StmtArt::Leave(_) | StmtArt::Next(_) => true,
        StmtArt::Ruf(r) => r
            .pfad
            .teile
            .last()
            .is_some_and(|n| divergent.iter().any(|d| d == &n.text)),
        StmtArt::Wenn(w) => {
            w.sonst.as_ref().is_some_and(|r| endet_immer(r, divergent))
                && w.zweige.iter().all(|(_, r)| endet_immer(r, divergent))
        }
        StmtArt::Match(m) => m.zweige.iter().all(|z| endet_immer(&z.rumpf, divergent)),
        // **Eine Klammer ist keine Weiche.** Wer im `locks`-, `observes`- oder
        // `breaking`-Rumpf auf jedem Weg endet, endet auch danach.
        StmtArt::Sperrt(x) => endet_immer(&x.rumpf, divergent),
        StmtArt::Observiert(x) => endet_immer(&x.rumpf, divergent),
        StmtArt::Bricht(x) => endet_immer(&x.rumpf, divergent),
        // **Der `else`-Zweig ist der AUSWEG, nicht der Weiterweg** — der Hauptpfad läuft
        // weiter, gleichgültig was darin steht.
        StmtArt::Narrow(_) | StmtArt::LetSonst(_) => false,
        // **Eine Schleife fällt durch.** `forever` tut das nicht, aber ob sie überhaupt
        // beendet wird, entscheidet Pass 6 aus `leave`/`on_exceeded` — nicht diese Zeile.
        StmtArt::Schleife(_) => false,
        StmtArt::Let(_)
        | StmtArt::Zuweisung(_)
        | StmtArt::Publish(_)
        | StmtArt::AwaitLoad(_)
        | StmtArt::Exchange(_) => false,
    }
}

/// **Wohin eine Anweisung schreibt — sie selbst und alles unter ihr.**
///
/// Stand als `m1::sammle_schreibziele` an einer Stelle und wurde ab «K5.1» an zweien
/// gebraucht. *Eine zweite Kopie wäre die Bauart gewesen, die `endet_immer` dreimal ergeben
/// hat.*
pub fn schreibziele(s: &Stmt, out: &mut Vec<Ort>) {
    match &s.art {
        StmtArt::Zuweisung(z) => out.push(z.ziel.clone()),
        StmtArt::Publish(p) => out.push(p.ziel.clone()),
        StmtArt::Exchange(e) => out.push(e.ort.clone()),
        _ => {}
    }
    for k in unterbloecke(s) {
        for i in &k.anweisungen {
            schreibziele(i, out);
        }
    }
}
