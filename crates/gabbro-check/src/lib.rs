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

pub mod alias;
pub mod aufrufgraph;
// **«B24» an EINER Stelle** -- der Namenspass sagt ab, der Erzeuger rechnet damit.
pub mod bitlage;
// **The BINDING SURFACE, since 2026-08-25** -- what binds across the library boundary and
// under which name. Both rules of `bindung.rs` (`N038`, `N039`) are issued there. It gets no
// pass number of its own: the pass list is the specification, and these are rules of the
// "Names" column, not a new one.
pub mod bindung;
// **The BUILD GATE, since 2026-08-28** -- `when TESTBUILD`, and the filter that keeps a
// gated item out of the shipping C. `G001`-`G003` are issued there. Like `bindung` it gets
// no pass number of its own, but it DOES owe sentences: `saetze::GATTER` hangs on pass 1,
// because the question "does this name exist in this build?" is a name question.
pub mod gatter;
// Die Domaenenschranke -- kosten.rs und m1.rs lesen dieselbe.
pub mod domaene;
pub mod m2;
pub mod m3;
pub mod paarung;
pub mod gruppe;
pub mod emit;
pub mod geteilt;
pub mod kbedingung;
pub mod abi;
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
// **Die Zusage eines fremden Rumpfes, als Tatsache im Pruefer** -- der EINE Leser der Frage
// „verengt diese `ensures`-Klausel, und wie?", und die Buchung der Stellen, an denen sie es
// getan hat. M1 nimmt den Typ, das Zeugnis nimmt die Stellen.
pub mod fremdverengung;
pub use m1::fremdverengungen;

pub mod korpus;
pub mod manifest;
// **P6, die Messsonde** -- was ein Mensch noch schuldet, gezaehlt statt eingeloest.
pub mod pflichten;
pub mod phasen;
/// **P6** -- the same obligation register, in the form a prover reads. See `refinement.rs`.
pub mod lean;
pub mod refinement;
pub mod schablonen;
// **Das PASSREGISTER, seit 2026-08-21** (PLAN.md PL.1). Je Pass die Saetze, die er SCHULDET
// -- die Aussage, die gelten muss, wenn er schweigt. Ohne sie ist „formal verifiziert" nicht
// einmal formulierbar, denn niemand wuesste, was zu beweisen waere.
pub mod saetze;
pub mod blindstellen;
pub mod zeugnis;
pub mod zeremonie;

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
    /// **Getragen, soweit ein Pass reicht — und der Rest ist BENANNT.**
    ///
    /// Die vierte Stufe, seit 2026-08-19. Sie kam, als die Frage *„mache alle neun Pässe
    /// fertig"* auf eine Antwort stiess, die keine Bauarbeit ist: **mehrere Reste sind
    /// überhaupt keine Passarbeit.** Sie liegen in der Axiomschicht (das Speichermodell), bei
    /// den Schablonen (die Erhaltung einer Invariante), in einer ENTSCHEIDUNG (die weichere
    /// Phasenlesart, und aus der strengen kann man lockern, aus der weichen nie) oder in einer
    /// bewusst gezogenen Grenze (`E010` spricht nur über bekannten Weltzustand).
    ///
    /// > **`PART` und `CARRIED` sind zwei verschiedene Aussagen, und sie zusammenzuwerfen war
    /// > die Ungenauigkeit.** *Teilgebaut* heisst: hier kommt etwas durch, das fallen müsste.
    /// > *Getragen* heisst: was ein Pass sagen kann, sagt er — und wo der Rest liegt, steht
    /// > daneben, mit Namen.
    ///
    /// Ein Rest ohne Adresse gehört weiter in `Teilgebaut`. **Diese Stufe ist keine
    /// Beförderung, sondern eine Adresse.**
    Getragen(&'static str),
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
    /// **Die Saetze, die dieser Pass SCHULDET** -- was wahr ist an einem Programm, das ihn
    /// ohne Absage passiert hat (PLAN.md PL.1, seit 2026-08-21).
    ///
    /// *Das ist nicht `zustand` und nicht `quelle`.* Jene sagen, wie weit der Pass gebaut ist
    /// und welche Regel er abnimmt; der Satz sagt, **was danach gilt** -- also genau die
    /// Aussage, die ein Beweis zu beweisen haette. **Zwoelf Paesse entscheiden ueber jedes
    /// Programm, und bis zu diesem Feld schuldete keiner einen Satz.**
    ///
    /// Die Liste darf leer sein; `instrumente/pruefe-saetze.py` fuehrt darueber die Ratsche
    /// und meldet jede Kennung, zu der kein Satz gehoert.
    pub saetze: &'static [saetze::Satz],
}

/// Die Passliste. **Die Reihenfolge ist Teil der Festlegung, nicht des Geschmacks.**
pub fn passliste() -> Vec<Pass> {
    vec![
        Pass {
            nummer: 1,
            name: "Namen",
            quelle: "E5: every declaration is complete in exactly one place",
            zustand: Zustand::Gebaut,
            saetze: saetze::NAMEN,
        },
        Pass {
            nummer: 2,
            name: "D1/D2",
            quelle: "SPRACHE.md §3: undurchsichtige Neutypen, vollstaendige Layouts, \
                     erschoepfende Aufzaehlung",
            zustand: Zustand::Getragen(
                "the K condition is built (`D001`: no hand mutation on a `table` with \
                    `ops`), and since 2026-08-18 opacity BITES: an `opaque type` does not \
                    have the arithmetic of its carrier (`D003`). *Before that `a + b` fell \
                    only by accident -- at `M104`, not at the opacity; wherever the widths \
                    worked out, the nonsense went through.* **And since the same day the \
                    WALL stands behind it** (`D004`): the implicit conversion went through \
                    silently in BOTH directions, so D1 was not enforced at all. The door is \
                    the MODULE BOUNDARY -- inside the declaring module the representation is \
                    known, outside it is not. *On this corpus it has zero bite: all twelve \
                    declarations declare and use in the same module.* **And since 2026-08-19 \
                    the exhaustive `match` over `tagged`** (`D005`): a `tagged type` is the \
                    one form in which the language states a CLOSED case distinction, and \
                    there is no catch-all branch -- *until then the closedness was a promise \
                    of the grammar that no pass redeemed.* The residue is a CORPUS \
                    statement, not pass work",
            ),
            saetze: saetze::D1D2,
        },
        Pass {
            nummer: 3,
            name: "M1 + V1–V3",
            quelle: "SPRACHE.md §3.2: range types and the three flow rules",
            zustand: Zustand::Gebaut,
            saetze: saetze::M1,
        },
        Pass {
            nummer: 4,
            name: "M3",
            quelle: "SYNTAX.md §3: Adressraeume und Zugriffsrechte am Zeiger",
            zustand: Zustand::Getragen(
                "built: rights checking at reads and writes, the placement rule that an \
                    `ops` carrier is not in the `dma` space (`R001`-`R004`) -- **and since \
                    2026-08-20 the REGISTER CLASS** (`R005`/`R006`, with «B23»: a class per \
                    FIELD, because `FSTS` is mixed and `FRI` is how a driver finds the record \
                    at all). *That one was booked as discharged BY `R002`/`R003`, which check \
                    pointer rights; the note on `R003` spoke the sentence and no line did it, \
                    so `return d.NUR_W.A;` gave 0 errors.* **The rest, with an ADDRESS: \
                    the barrier from the space** -- which barrier a `dma` access demands is \
                    a statement about the memory model, the same axiom layer as at the \
                    pairing. **And no alias analysis**: two `ptr<normal, rw>` to the same \
                    object stay indistinguishable, and `own` is what stands for that",
            ),
            saetze: saetze::M3,
        },
        Pass {
            nummer: 5,
            name: "M2",
            quelle: "SPRACHE.md §4: lineare und geisterhafte Werte",
            zustand: Zustand::Getragen(
                "built: exactly-once per path, branch matching, `consumes` against \
                    borrowed (`L101`-`L105`). **And since K5 a value that arises in the BODY** (`L107`); the ghost erasure itself is built and sits in the EMITTER, verified 2026-08-19. The rest has an address -- a `ghost` \
                    value does not exist at run time, its linearity is a statement about the \
                    PROOF, and the alias question belongs to M3. **Since 2026-08-17 the \
                    ORDER stands beside it** (pass 11) -- M2 sees the chain, not which one",
            ),
            saetze: saetze::M2,
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
            zustand: Zustand::Getragen(
                "built: shared against exclusive (`H001`-`H004`), the intermediate rule \
                    at the call boundary (`H005`), the recomputed rank order (`H006`) -- and \
                    since K11.2.1 `protects` bites: every access to a protected place stands \
                    under its lock (`H007`), and a lock that is never taken shows up \
                    (`H008`). **And since «K5» the whole discipline**: a `locks` effect \
                    that nobody redeems (`H011`), the rank order THROUGH calls (`H012`), a \
                    rank that is not constant-evaluable (`H014`), and the EXECUTION \
                    CONTEXTS -- an `entry ... dispatch` names one, and a place written \
                    through it that nothing declares shared falls (`H013`). *The sentence \
                    \"Gabbro does not say who runs concurrently\" was overtaken by its own \
                    `entry` construct.* **The rest, with an ADDRESS: the finer half** -- `masks IRQ`, \
                    `per cpu` and `nested never` only exempt under `assume ein_kern`, and \
                    on this corpus `H013` has ZERO bite (all four context roots dispatch \
                    to an `extern fn`): `gabbro kontexte` prints the count beside it. \
                    **And since «B38» the CARRIER is coupled to the entry state** \
                    (`H101`): naming `masks IRQ` in an effect list says that a function \
                    masks, not that it RUNS masked -- an entry that reaches such a carrier \
                    must declare `nested masked`. *Before that, one word in an effect list \
                    bought the exemption from `H013`.* **And since 2026-08-21 every RCU \
                    DOMAIN NAME is explained by a declaration** (`H017`) -- the twin of \
                    `H016` one construct further: `observes NIEDADOM { … }` gave zero \
                    errors, because the RCU walker runs at all only in a unit that declares \
                    a domain. **What no rule of this pass carries, and it is the whole \
                    remainder of the RACE class: the ALIAS.** Two pointers to one object \
                    are indistinguishable here as they are in M3, so a lock that protects \
                    `T` does not protect a second name for `T` -- `gabbro alias` counts how \
                    large that surface is instead of guessing, and `messung/RACE.md` says \
                    per race form what carries it and what it hangs on.",
            ),
            saetze: saetze::SPERREN,
        },
        Pass {
            nummer: 11,
            name: "Phasen",
            quelle: "MESSUNGEN.md, «B37»: Linearitaet ist keine Ordnung",
            zustand: Zustand::Getragen(
                "built: the stages of an `order` exist and `advances` goes FORWARD \
                    (`O001`/`O002`), the mark stands at its source stage at the call \
                    (`O003`), and the body composes into its own promise (`O004`). **And \
                    since K11.1 the branch**: all branches must reach the same stage \
                    (`O006`); a branch that ENDS with `return` does not join, and a step in \
                    a LOOP is refused -- a step happens once, a loop often. **The rest is a DECISION, not a gap: the \
                    softer reading** -- carrying a set of stages and letting all of them \
                    accept the next step. *From the strict reading one can loosen, never the \
                    other way* (PLAN.md, K11.1)",
            ),
            saetze: saetze::PHASEN,
        },
        Pass {
            nummer: 6,
            name: "M4/Schleifen",
            quelle: "SYNTAX.md §8: three loop forms, `leave`/`next` target a label",
            zustand: Zustand::Gebaut,
            saetze: saetze::SCHLEIFEN,
        },
        Pass {
            nummer: 7,
            name: "Paarung",
            quelle: "SPRACHE.md part II §1: ordering is PAIRED, not declared",
            zustand: Zustand::Getragen(
                "built: `publishes`/`awaits`/`exchange` over the united set, name \
                    equality after index substitution (`V001`-`V004`). **The rest has a NAME -- A10: the \
                    statement about the MEMORY MODEL** -- that `release`/`acquire` establish \
                    the visibility the pairing claims falls into the axiom layer and not \
                    into this pass",
            ),
            saetze: saetze::PAARUNG,
        },
        Pass {
            nummer: 8,
            name: "effects",
            quelle: "SPRACHE.md §7: `effects` is mandatory and not fail-open",
            zustand: Zustand::Getragen(
                "writes, `locks` **and since 2026-08-16 reads** (reading A, `E010`) are \
                    held against the list. **What is missing is the reach of `E010`:** it \
                    speaks only about known world state (`static`, `atomic`, `table`, \
                    `device`, `state`), because a variant is not a place and an EXCERPT does \
                    not declare its names -- on the fragment corpus the rule therefore has \
                    **zero bite**, and its evidence comes from poison 62 and two mutations, \
                    not from the corpus",
            ),
            saetze: saetze::WIRKUNGEN,
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
            zustand: Zustand::Getragen(
                "built: the LOCK FOOTPRINT (`U001`-`U005`), the MOVE (`U006`) and the \
                    CONNECTING STATEMENT as a form (`U007`: a group invariant names at least \
                    two carriers, otherwise it belongs at the table). **The rest is the PROVER's: the \
                    preservation** -- that the invariant HOLDS under an operation is the \
                    prover's business and falls to S16/S17, not to this pass. It checks the \
                    three conditions under which the question can be asked at all",
            ),
            saetze: saetze::GRUPPE,
        },
        Pass {
            nummer: 9,
            name: "costs",
            quelle: "SPRACHE.md §7: 1 op = one Gabbro primitive, computed statically",
            zustand: Zustand::Getragen(
                "bodies, `locks` blocks against `held` and calls over the DECLARED costs \
                    of the callee are computed -- **recursion therefore carries an \
                    assumption instead of a computation**, and `per_pass` with an input-\
                    dependent bound is not settled",
            ),
            saetze: saetze::KOSTEN,
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
        z!("bindung", bindung::pass(baum, absagen));
        z!("gatter", gatter::pass(baum, absagen));
        z!("kbed", kbedingung::pass(baum, absagen));
        let m1 = { let t = std::time::Instant::now(); let r = m1::pass(baum, absagen); eprintln!("{:>10} {:?}", "m1", t.elapsed()); r };
        z!("schleifen", schleifen::pass(baum, absagen));
        z!("wirkungen", wirkungen::pass(baum, absagen));
        z!("geteilt", geteilt::pass(baum, absagen));
        z!("kontexte", kontexte::pass(baum, absagen));
        z!("m3", m3::pass(baum, absagen));
        z!("m2", m2::pass(baum, absagen));
        z!("phasen", phasen::pass(baum, absagen));
        z!("paarung", paarung::pass(baum, absagen));
        z!("gruppe", gruppe::pass(baum, absagen));
        let kosten = { let t = std::time::Instant::now(); let r = kosten::pass(baum, absagen); eprintln!("{:>10} {:?}", "kosten", t.elapsed()); r };
        return Bericht { m1, kosten };
    }
    namen::pass(baum, absagen);
    // **Directly behind the names** -- the same question one level up: `N001` in `namen.rs`
    // holds a name against its scope, `bindung.rs` against the surface that binds out of the
    // unit. That one knows no modules.
    bindung::pass(baum, absagen);
    // **Directly behind it again, and one question further out.** `bindung` asks which name
    // leaves the unit; `gatter` asks whether a name exists in THIS BUILD at all. It stands
    // before every pass that reads bodies, because a refusal about a call across the gate is
    // about the artefact, not about the semantics of the call.
    gatter::pass(baum, absagen);
    kbedingung::pass(baum, absagen);
    let m1 = m1::pass(baum, absagen);
    schleifen::pass(baum, absagen);
    wirkungen::pass(baum, absagen);
    geteilt::pass(baum, absagen);
    // **«B38» -- die Kopplung zwischen benanntem Traeger und Eintrittszustand.**
    //
    // Direkt hinter `geteilt`, weil sie zur Kontextmatrix («K5.3») gehoert und dieselbe
    // Erhebung benutzt. *Sie bekommt keine eigene Passnummer: die Liste ist die Spezifikation,
    // und dies ist eine Regel derselben Spalte, keine neue.*
    kontexte::pass(baum, absagen);
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
        .filter(|p| matches!(p.zustand, Zustand::Offen(_) | Zustand::Getragen(_)))
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

/// **Every type expression an item writes down -- exhaustively, without a `_` arm.**
///
/// Built on 2026-08-21 for the function pointer contract (`N035`-`N037`): a rule about a
/// TYPE needs a walk over types, and there was none. Every pass that wanted one descended by
/// hand, and the house record on hand-written descents is the reason this file already holds
/// `unterbloecke` and `alle_ausdruecke`: *78 holes of one build, each pass forgetting a
/// different arm.*
///
/// **Both matches below are exhaustive on purpose.** A new `ItemArt` or a new `TypExpr` is a
/// compile error here, not a type that quietly stops being checked.
///
/// It visits **declared** types only -- the type of a place is computed, not written, and
/// that is `umgebung::typ_von_ort`'s business.
pub fn jeder_typausdruck_im_item(item: &Item, f: &mut impl FnMut(&TypExpr)) {
    fn typ(t: &TypExpr, f: &mut impl FnMut(&TypExpr)) {
        f(t);
        match t {
            TypExpr::Feld(a) => typ(&a.element, f),
            TypExpr::Zeiger(p) => typ(&p.ziel, f),
            TypExpr::Verbund(felder, _) => {
                for x in felder {
                    typ(&x.typ.typ, f);
                }
            }
            TypExpr::Varianten(v, _) => {
                for x in v {
                    if let Some(n) = &x.nutzlast {
                        typ(n, f);
                    }
                }
            }
            // **A function pointer's own parameter and result types are types too.** A
            // `fn(g : fn() effects { pure } costs <= 1 ops)` is admitted by the grammar, and
            // the contract rules have to reach the inner one as well.
            TypExpr::FnZeiger(z) => {
                for p in &z.parameter {
                    typ(&p.typ, f);
                }
                if let Some(e) = &z.ergebnis {
                    typ(e, f);
                }
            }
            TypExpr::Int(_)
            | TypExpr::Float(_)
            | TypExpr::Bool(_)
            | TypExpr::Never(_)
            | TypExpr::Pfad(_)
            | TypExpr::Index { .. } => {}
        }
    }
    match &item.art {
        ItemArt::Typ(d) => {
            for p in d.parameter.iter().flatten() {
                typ(p, f);
            }
            if let Some(r) = &d.rumpf {
                typ(r, f);
            }
        }
        ItemArt::Funktion(d) => {
            for p in &d.parameter {
                typ(&p.typ, f);
            }
            if let Some(e) = &d.ergebnis {
                typ(e, f);
            }
        }
        ItemArt::Konst(d) => typ(&d.typ, f),
        ItemArt::Statisch(d) => typ(&d.typ, f),
        ItemArt::Atomic(d) => typ(&d.typ, f),
        ItemArt::Format(d) => {
            for x in &d.felder {
                typ(&x.typ.typ, f);
            }
        }
        ItemArt::Tabelle(d) => {
            for k in &d.konstanten {
                typ(&k.typ, f);
            }
            for s in d.slot.iter().flat_map(|s| &s.felder) {
                match &s.typ {
                    SlotTyp::Typ(t) => typ(t, f),
                    SlotTyp::Wrapping(_) => {}
                }
            }
        }
        // **These declare no type expression**, and each is written out rather than swept
        // into a `_`: when one of them grows a type, this is the line that must change.
        ItemArt::Modul(_)
        | ItemArt::Use(_)
        | ItemArt::Reason(_)
        | ItemArt::State(_)
        | ItemArt::Device(_)
        | ItemArt::Assume(_)
        | ItemArt::Axiom(_)
        | ItemArt::Check(_)
        | ItemArt::Lock(_)
        | ItemArt::Rcu(_)
        | ItemArt::Gruppe(_)
        | ItemArt::Accumulates(_)
        | ItemArt::Walk(_)
        | ItemArt::Entry(_)
        | ItemArt::Entrust(_)
        | ItemArt::Boot(_) => {}
    }
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
        // **Eine Schleife wertet aus, bevor sie läuft** (2026-08-19). `traverse x over <ort>`
        // liest den Gegenstand, und `by falling <mass>` rechnet das Mass. *Die Schranke
        // (`bounded N ops`, `per_pass N ops`) steht NICHT hier* — sie ist eine Aussage über
        // die Übersetzungszeit und wird nie ausgeführt.
        StmtArt::Schleife(sch) => match sch.as_ref() {
            Schleife::Traverse(t) => {
                let mut v: Vec<&Expr> = t.gegenstand.iter().collect();
                if let Abstieg::Fallend(m) = &t.abstieg {
                    v.push(m);
                }
                v
            }
            Schleife::Retry(_) | Schleife::Forever(_) => Vec::new(),
        },
        // `let x = f() else …` trägt seinen Ruf in der Quelle, nicht in einem `Expr`.
        StmtArt::LetSonst(_)
        | StmtArt::Ruf(_)
        | StmtArt::Bricht(_)
        | StmtArt::Narrow(_)
        | StmtArt::Sperrt(_)
        | StmtArt::Observiert(_)
        | StmtArt::Leave(_)
        | StmtArt::Next(_)
        | StmtArt::AwaitLoad(_) => Vec::new(),
    }
}

/// **Die Prädikate, die eine Anweisung SELBST auswertet** — erschöpfend über `StmtArt`, ohne
/// `_`-Zweig, wie `unterbloecke` und `eigene_ausdruecke`.
///
/// **Der Grund, aus dem es diese Funktion gibt** (2026-08-19): ein `retry … until f()` wertet
/// `f()` bei **jedem** Durchgang aus, und kein Pass sah den Ruf. Gemessen:
///
/// ```gabbro
/// impl fn luegt() effects { pure } {
///     retry warten until tu() == 9 … { }        -- `tu` schreibt. 0 Fehler.
/// }
/// ```
///
/// Der Aufrufgraph stieg über `eigene_ausdruecke` ab, und dort stand `Schleife => Vec::new()`.
/// **Damit war `effects` an dieser Stelle fail-open** — dritte Stelle derselben Klasse an
/// einem Tag, nach dem Diamanten und den 83 `_ => {}`-Zweigen. *Gefunden nicht durch eine
/// Prüfung, sondern durch eine OPTIMIERUNG*: `pruefe-emission.sh` sah unter `-O1`, wie der
/// C-Übersetzer 65 Rufe strich, die ein falsches `__attribute__((pure))` für wirkungslos
/// erklärt hatte.
pub fn eigene_praedikate(s: &Stmt) -> Vec<&Pred> {
    match &s.art {
        StmtArt::Schleife(sch) => match sch.as_ref() {
            Schleife::Retry(r) => r.bis.iter().collect(),
            Schleife::Traverse(_) | Schleife::Forever(_) => Vec::new(),
        },
        // Die Formen ohne eigenes Prädikat — **einzeln**, damit eine neue Art hier auffällt.
        StmtArt::Let(_)
        | StmtArt::LetSonst(_)
        | StmtArt::Zuweisung(_)
        | StmtArt::Return(_)
        | StmtArt::Publish(_)
        | StmtArt::Wenn(_)
        | StmtArt::Match(_)
        | StmtArt::Exchange(_)
        | StmtArt::Ruf(_)
        | StmtArt::Bricht(_)
        | StmtArt::Narrow(_)
        | StmtArt::Sperrt(_)
        | StmtArt::Observiert(_)
        | StmtArt::Leave(_)
        | StmtArt::Next(_)
        | StmtArt::AwaitLoad(_) => Vec::new(),
    }
}

/// Die Ausdrücke in einem Prädikat — ein `until` liest ebenso wie ein Rumpf.
pub fn ausdruecke_im_praedikat(p: &Pred) -> Vec<&Expr> {
    let mut aus = Vec::new();
    fn geh<'a>(p: &'a Pred, aus: &mut Vec<&'a Expr>) {
        // **Erschöpfend, ohne `_`-Zweig** — wie `unterbloecke`. Bis 2026-08-20 stand hier
        // `_ => {}`, und damit war `Folgt` (`a => b`) und der Rumpf eines `Quantor` für
        // JEDEN Leser unsichtbar. Ein `until schreibt() == 1` unter `effects { pure }` fiel
        // deshalb nirgends.
        match &p.art {
            PredArt::Vergleich(e) | PredArt::Element(e, _) => aus.push(e),
            PredArt::Klammer(x) | PredArt::Nicht(x) => geh(x, aus),
            PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
                geh(a, aus);
                geh(b, aus);
            }
            PredArt::Quantor(q) => geh(&q.rumpf, aus),
            // Diese beiden nennen nur NAMEN, keine Ausdrücke — und sie stehen hier
            // ausgeschrieben, damit eine neue `PredArt` den Bau bricht statt zu verschwinden.
            PredArt::Erreicht { .. } | PredArt::Held { .. } => {}
        }
    }
    geh(p, &mut aus);
    aus
}

/// **Jeder Unterausdruck eines Ausdrucks — erschöpfend, ohne `_`-Zweig** (2026-08-20).
///
/// Auf ANWEISUNGSEBENE stand das längst: `unterbloecke`, `eigene_ausdruecke` und
/// `endet_immer` sind erschöpfende `match`es, damit eine neue `StmtArt` den Bau bricht.
/// **Eine Ebene tiefer galt es nirgends** — sechzehn handgerollte Ausdrucksläufer, und nur
/// fünf stiegen in einen `OrtSuffix::Index` ab. Die Folge, von aussen gemessen:
///
/// ```gabbro
/// return t.slots[schreibt()].x;      -- `schreibt` schreibt eine globale Größe
/// ```
///
/// gab **null Fehler**, derselbe Ruf als Anweisung `E008`. Und der Erzeuger schrieb
/// `__attribute__((pure))` darüber — *genau die Klasse, an der `-O1` einmal 65 Rufe
/// gelöscht hat.*
///
/// > Dieselbe Lücke trug `until schreibt() == 1` unter `pure`, `aligned(schreibt(), 4)` und
/// > `H011`/`H012` in Indexposition. **Eine Ursache, fünf Befunde.**
///
/// Geliefert werden die DIREKTEN Kinder; wer alles will, ruft rekursiv — `alle_ausdruecke`
/// tut genau das.
pub fn unterausdruecke(e: &Expr) -> Vec<&Expr> {
    let mut aus = Vec::new();
    match &e.art {
        ExprArt::Zahl(_)
        | ExprArt::Gleitkomma { .. }
        | ExprArt::Wahr
        | ExprArt::Falsch
        // **`&f` carries no sub-expression either** («B8»): the `&` takes a PATH, not an
        // expression, and that restriction is in the parser on purpose.
        | ExprArt::FnWert(_)
        // **Ein Grundwert traegt keinen Unterausdruck** (Stufe 7) -- `R::F` ist ein
        // Blatt, wie `true`. Er steht hier ausgeschrieben und nicht in einem `_`-Zweig:
        // *ein schweigender Auffangzweig ist die haeufigste Lochform dieses Ordners.*
        | ExprArt::Grund { .. }
        | ExprArt::Ergebnis => {}
        // **Ein Ort trägt Ausdrücke** — in jedem `[…]`. Das war die eine vergessene Kante.
        ExprArt::Ort(o) | ExprArt::Alt(o) => aus.extend(ausdruecke_im_ort(o)),
        ExprArt::Ruf(r) => aus.extend(r.argumente.iter()),
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => aus.push(x),
        ExprArt::Binaer(_, a, b) => {
            aus.push(a);
            aus.push(b);
        }
        ExprArt::Eingebaut(g) => match &**g {
            Eingebaut::Aligned(a, b) => {
                aus.push(a);
                aus.push(b);
            }
            Eingebaut::Sizeof(t) | Eingebaut::Lenof(t) => {
                if let TypOderOrt::Ort(o) = t {
                    aus.extend(ausdruecke_im_ort(o));
                }
            }
        },
    }
    aus
}

/// Die Ausdrücke IN einem Ort — jeder Index. `c.slots[i].x` trägt `i`.
pub fn ausdruecke_im_ort(o: &Ort) -> Vec<&Expr> {
    o.suffixe
        .iter()
        .filter_map(|s| match s {
            OrtSuffix::Index(e) => Some(e),
            OrtSuffix::Feld(_) | OrtSuffix::Ueber(_) => None,
        })
        .collect()
}

/// **Jeder ORT in diesem Ausdruck und allem darunter** — das Gegenstück zu
/// `alle_ausdruecke`, für die Pässe, die Plätze sammeln statt Rufe.
///
/// Sechs Läufer im Prüfer sammelten Orte von Hand, und keiner davon stieg vollständig ab.
/// *`H007` (`protects`) schwieg deshalb bei einem Zugriff über `narrow`, über ein `until`
/// und über die Domäne eines `traverse`.*
///
/// Der Ort SELBST kommt mit, und die Orte in seinen Indizes ebenso: `c.slots[d.slots[j].k].x`
/// nennt drei Plätze, und alle drei werden gelesen.
pub fn alle_orte(e: &Expr) -> Vec<&Ort> {
    let mut aus = Vec::new();
    for x in alle_ausdruecke(e) {
        match &x.art {
            ExprArt::Ort(o) | ExprArt::Alt(o) => aus.push(o),
            ExprArt::Eingebaut(g) => {
                if let Eingebaut::Sizeof(TypOderOrt::Ort(o)) | Eingebaut::Lenof(TypOderOrt::Ort(o)) =
                    &**g
                {
                    aus.push(o);
                }
            }
            // **`&f` is not a place** -- it names a function, and no pass that reads
            // places (`reads`, `writes`, M3's rights) has anything to do here.
            ExprArt::FnWert(_)
            | ExprArt::Zahl(_)
            | ExprArt::Gleitkomma { .. }
            | ExprArt::Wahr
            | ExprArt::Falsch
            | ExprArt::Ergebnis
            // **Ein Grundwert ist KEIN Ort** (Stufe 7) -- und genau darum ist er eine
            // eigene Variante: als `Ort` haette ihn `effects` als Lesen einer Stelle
            // gezaehlt, die es gar nicht gibt.
            | ExprArt::Grund { .. }
            | ExprArt::Ruf(_)
            | ExprArt::Klammer(_)
            | ExprArt::Unaer(_, _)
            | ExprArt::Binaer(_, _, _) => {}
        }
    }
    aus
}

/// **Dieser Ausdruck und alle darunter**, in Präordnung. Der Läufer, den sechzehn Stellen
/// von Hand gebaut hatten.
pub fn alle_ausdruecke(e: &Expr) -> Vec<&Expr> {
    let mut aus = vec![e];
    let mut i = 0;
    while i < aus.len() {
        let kinder = unterausdruecke(aus[i]);
        aus.extend(kinder);
        i += 1;
    }
    aus
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
        // **An indirect call never ends a body.** `divergent` lists the functions whose
        // call does not return (`-> never`), and it is a list of NAMES. A `fn(…)` type may
        // promise `diverges` as an effect, but that is a statement about what the callee
        // touches, not about whether control comes back -- *and reading it as the second
        // would let a body end in a place no pass verified.*
        StmtArt::Ruf(r) => r
            .path()
            .and_then(|p| p.teile.last())
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
