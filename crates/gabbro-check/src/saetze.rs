//! **Das PASSREGISTER: was ein Pass SCHULDET, nicht was er tut.**
//!
//! Der Befund, mit dem dieses Modul anfaengt, steht in [`PLAN.md`](PLAN.md) PL und war am
//! 2026-08-21 noch wahr:
//!
//! | Flaeche | Ratsche | Stand |
//! |---|---|---|
//! | Wortschatz | `pruefe-wortschatz.py` | 195 gegen 195 |
//! | Axiomschicht | `gabbro annahmen` | 19, jede mit Sonde oder Grund |
//! | Erzeuger-Schablonen | `gabbro schablonen` | 21, davon 4 bewiesen |
//! | **die Paesse** | **keine** | **zwoelf Paesse, 0 gezaehlte Saetze** |
//!
//! > **Zwoelf Paesse entscheiden ueber jedes Programm, und keiner von ihnen schuldet einen
//! > Satz.** Ohne die Saetze ist *„Gabbro formal verifiziert"* nicht einmal FORMULIERBAR --
//! > man wuesste nicht, was zu beweisen waere.
//!
//! ## Was ein Satz IST -- und was er nicht ist
//!
//! `zustand` und `quelle` gibt es an [`crate::Pass`] schon. Sie sagen, wie weit der Pass
//! gebaut ist und welche Regel er abnimmt. **Der Satz sagt etwas anderes:**
//!
//! > **Was ist WAHR an einem Programm, das diesen Pass ohne Absage passiert hat?**
//!
//! Das ist die Aussage, die ein Beweis zu beweisen haette -- und sie ist erst dann
//! aufschreibbar, wenn jemand nachsieht, was der Pass WIRKLICH leistet.
//!
//! > **Beim Aufschreiben dieser Liste war der haeufigste Einzelbefund, dass der MODULKOPF
//! > eines Passes mehr behauptet als sein Code einloest.** Fuenfmal gemessen, in fuenf
//! > verschiedenen Dateien -- und in zwei Faellen war der Kopf schlicht VERALTET. Genau
//! > dafuer ist die Uebung da: *ein Satz, den niemand aufschreibt, kann auch niemand
//! > widerlegen.*
//!
//! ## Die Vorbedingung, die ueber ALLEN Saetzen steht: `hinweis` ist keine Absage
//!
//! [`gabbro_syntax::diag::Stufe::Hinweis`] zaehlt nicht als Fehler, und nur `Stufe::Fehler`
//! laesst den Uebersetzer scheitern. **Fuenf Kennungen sind Hinweise: `E003`, `E009`,
//! `V003`, `S007`, `N026`.**
//!
//! > **Ein Programm, das „ohne Absage" durchgeht, kann also Funktionen enthalten, deren
//! > Rahmen- oder Paarungsaussage der Pruefer AUSDRUECKLICH fuer unentscheidbar erklaert
//! > hat.** `E009` ist der ehrliche dritte Zustand (R16) -- und er ist sichtbar, nicht gruen.
//! > *Wer die Saetze unten liest, muss diese Zeile mitlesen: sie schwaecht jeden von ihnen.*
//!
//! ## Die ehrliche Haelfte gehoert in den Eintrag, nicht daneben
//!
//! Jeder Satz traegt seinen [`Satz::vorbehalt`] -- **wo er NICHT gilt.** Ein Satz ohne
//! Vorbehalt ist kein staerkerer Satz, sondern ein ungeprueftes Versprechen: dieselbe
//! Bewegung wie ein `_`-Zweig, der eine Vollstaendigkeit behauptet, die er nicht hat (W12).
//!
//! ## Die Fallrichtung -- woertlich die der Schablonen
//!
//! > **Ein Satz verlaesst die Liste nur auf zwei Wegen: BEWIESEN, oder MITSAMT SEINEM
//! > PASS.** Nicht durch Umformulierung, nicht durch Zusammenfassen zweier Saetze zu einem,
//! > nicht dadurch, dass er „eigentlich schon in einem anderen steckt".
//!
//! ## Der zweite Zahn: kein neuer Absagecode ohne seinen Satz
//!
//! [`ohne_satz`] rechnet aus, welche Kennungen zu keinem Satz gehoeren.
//! `instrumente/pruefe-saetze.py` fuehrt darueber die Ratsche -- **sie darf fallen, nicht
//! steigen.** Der Grund, warum der Zahn SOFORT kommt und nicht nach den Saetzen: jede
//! Kennung, die zwischen heute und dem Beweisprojekt dazukommt, ist ein Satz mehr, den
//! spaeter jemand **rueckwaerts** rekonstruieren muss. *An einem einzigen Arbeitstag sind
//! drei dazugekommen.*

/// Wie weit ein Satz ist. **Dieselben drei Stufen wie [`crate::schablonen::Stand`]**, und aus
/// demselben Grund: ein aufgeschriebener Satz ist kein gemessener, und ein gemessener ist
/// kein bewiesener.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Satzstand {
    /// **Aufgeschrieben, und NICHTS rechnet ihn nach.** Der Satz kann falsch sein; er steht
    /// da, damit jemand ihn widerlegen kann. *Genau der Stand `entworfen` einer Schablone.*
    Vermutet,
    /// **Eine Giftprobe faellt, oder eine Mutation wird gefangen.** Das misst die UMSETZUNG
    /// an gepruefte Faelle -- nicht die Regel, und nicht alle Faelle (PLAN.md PL.3, Weg (c)).
    Gemessen,
    /// **A soundness ARGUMENT is written down for it** -- mathematically, human-reviewed,
    /// not machine-checked (PL.1b, 2026-08-24).
    ///
    /// *„If this pass accepts, then P"* -- written out, with the piece of model it needs.
    /// **Between `Gemessen` and `Bewiesen`, and the gap upwards is the larger one:** a paper
    /// argument can be wrong.
    ///
    /// **What it buys is not certainty but the obligation to LOOK.** The first sentence to
    /// reach this state uncovered, in the writing, an UNDER-count in its own pass -- the
    /// `else if` chain counted only its own arm's condition, not the preceding ones
    /// (`messung/K001.md`). *Two bodies of identical meaning measured 2 and 6.*
    ///
    /// > **An `ARGUED` read as `PROVED` is more expensive than an empty field.** That is why
    /// > it stands as a state of its own and not as a footnote on `Gemessen`.
    Argumentiert,
    /// **Einmal nach Isabelle gebracht, ohne `sorry`.** Der einzige Stand, der die
    /// Vertrauensbasis verkleinert.
    ///
    /// **Heute erreicht ihn KEINER, und das ist die Zahl, um die es geht.** Die Stufe steht
    /// trotzdem hier, weil eine Ratsche ohne ihr Ziel keine Richtung hat -- dieselbe Bauart
    /// wie [`crate::Zustand::Teilgebaut`], das in der Passliste ebenfalls null Eintraege hat
    /// und die moegliche Lage trotzdem benennt.
    Bewiesen,
}

impl Satzstand {
    pub const fn text(self) -> &'static str {
        match self {
            Satzstand::Vermutet => "CONJECTURED",
            Satzstand::Gemessen => "measured",
            Satzstand::Argumentiert => "ARGUED",
            Satzstand::Bewiesen => "PROVED",
        }
    }
}

/// **Ein Satz, den ein Pass schuldet.**
///
/// Die Textfelder sind englisch, weil sie ein BERICHT sind (`gabbro paesse`) und die Linie an
/// dieser Stelle laeuft: *was Gabbro sagt, ist englisch; was der Ordner ueber Gabbro sagt,
/// nicht* (`pruefe-englisch.py`).
#[derive(Clone)]
pub struct Satz {
    /// Kurzname, `pass.gegenstand` -- der Schluessel, unter dem die Ratsche ihn fuehrt.
    pub name: &'static str,
    /// **Die Kennungen, mit denen dieser Satz ABSAGT.** Der zweite Zahn haengt hier: eine
    /// Kennung, die in keinem `kennungen` steht, hat keinen Satz.
    ///
    /// *Und die Rueckrichtung ist genauso wichtig:* eine Kennung, die hier steht und im
    /// Pruefer nicht existiert, ist ein Satz ueber einer Regel, die es nicht gibt.
    /// `pruefe-saetze.py` prueft beide Richtungen.
    pub kennungen: &'static [&'static str],
    /// **Was wahr ist an einem Programm, das ohne diese Absagen durchkam.**
    pub aussage: &'static str,
    /// **Wo der Satz NICHT gilt.** Pflichtfeld: ein Satz ohne Vorbehalt behauptet eine
    /// Vollstaendigkeit, die kein Pass dieses Ordners hat.
    pub vorbehalt: &'static str,
    pub stand: Satzstand,
    /// **Woran gemessen** -- eine Giftprobe, eine Mutation, oder der ausdrueckliche Vermerk,
    /// dass es beides nicht gibt. *Ein `Gemessen` ohne diese Angabe waere die Behauptung
    /// einer Messung.*
    pub gemessen_an: &'static str,
    pub fundstelle: &'static str,
}

// ===================================================================================
//  Pass 1 -- Namen
// ===================================================================================

pub const NAMEN: &[Satz] = &[
    Satz {
        name: "namen.doppelung",
        kennungen: &["N001", "N002", "N003", "N009", "N010", "N017"],
        aussage: "Within one scope no name is declared twice, no two `reason` cases carry \
                  the same number, no two register fields sit on the same bits, no two `reg` \
                  overlap in offset, and no register stands in `preserves` and `clobbers` at \
                  once. The pass checks DUPLICATION, not resolution.",
        vorbehalt: "**Three holes, and the first is a real one.** (1) A `when` item switches \
                    the duplicate check off entirely -- two identically named items with \
                    `when` never fall (`arch` in contrast keys correctly per target). \
                    (2) Duplicate FUNCTION PARAMETERS and shadowing `let` names are checked \
                    NOWHERE: the scope walker sees items and a fixed set of construct \
                    bodies. (3) `N009`/`N010` compare only what is a NUMBER LITERAL, and \
                    `N009` only within one level -- bank against main level never.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 4 probes on `N001`, probes on `N002`-`N003` and \
                      `N009`-`N010`.",
        fundstelle: "crates/gabbro-check/src/namen.rs; SPRACHE.md part III E5",
    },
    Satz {
        name: "namen.bitlage",
        kennungen: &["N007", "N008", "N013"],
        aussage: "Every named bit position lies inside the field's OWN word (`hi >= lo`, `hi` \
                  within the word), and no two bit positions of one word overlap. The \
                  decision behind it: a bit position means something inside its own word and \
                  nothing beyond it.",
        vorbehalt: "A field whose carrier is not an integer -- `bool @63` in a `Pte` -- is \
                    checked neither for position nor for overlap (booked under W10). The \
                    word BOUNDARY is a heuristic: a partially named word merges with the \
                    following field of the same width, so `N008` can fire wrongly across two \
                    separate words. After one finding a field is left out of the occupancy \
                    map, so overlaps WITH an already faulty field never appear. And the \
                    third part of «B24» -- a GAP in the word -- is deliberately the \
                    emitter's business (`C001`), not this pass's: `format Elf64Ph` leaves 29 \
                    bits unnamed and passes.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 2 probes on `N007`; probes on `N008` and `N013`.",
        fundstelle: "crates/gabbro-check/src/bitlage.rs; SYNTAX.md, «B24»",
    },
    Satz {
        name: "namen.speicherform",
        kennungen: &["N011", "N019", "F006"],
        aussage: "No ghost or linear type is stored in memory (slot field, record field, \
                  `static`, `format` field), no record contains itself by value, and no \
                  float width the emitter cannot lower is named.",
        vorbehalt: "`N011` is blind at the POINTER and at the VARIANT: `ptr<…> Marke` in a \
                    slot passes, and a ghost payload inside `Varianten` passes. `N019` finds \
                    cycles only through `type … = { … }` -- a ring running through a `tagged` \
                    type or a table tears. `F006` covers four item kinds and NOT slot \
                    fields, `format` fields, register types or `axiom` parameters.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 4 probes on `N011`; probes on `N019` and `F006`.",
        fundstelle: "crates/gabbro-check/src/namen.rs; SPRACHE.md §4",
    },
    Satz {
        name: "namen.modulgrenze",
        kennungen: &["N025"],
        aussage: "No reference across a module boundary reaches an item that is not `pub`.",
        vorbehalt: "**This is the weakest of the large rules, and it is weak in three \
                    directions.** (1) Only 9 of 11 `pub`-carrying declaration kinds are \
                    collected -- `Modul` and `use` are MISSING, so module privacy itself is \
                    not enforced. *It was 5 of 7 until 2026-08-25, when `table`, `device`, \
                    `format` and `lock` got the word and this map got them.* \
                    (2) An unknown target counts as VISIBLE (`unwrap_or(true)`). (3) Only \
                    `use` lines and qualified CALLS are checked -- qualified type, constant \
                    and `static` references are silent.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes on `N025`. None of the three holes above has a \
                      probe -- they were found by READING, and that is the point of writing \
                      the sentence down.",
        fundstelle: "crates/gabbro-check/src/namen.rs; SPRACHE.md §14",
    },
    Satz {
        name: "namen.klauselbindung",
        kennungen: &[
            "N004", "N005", "N006", "N012", "N014", "N016", "N018", "N020", "N021", "N022",
            "N023", "N024", "N026", "N027", "N028", "N029", "N030", "N031", "N032", "N033",
        ],
        aussage: "Every clause that names something -- `entrust`, `offset_into`, `per cpu`, \
                  `requires Has`, `dispatch`, `gates`, `measures`, `mirrors`, a probe \
                  obligation, `observed by`, a `format` `where`, `step`, a nominal type at a \
                  `let`/`return`/comparison/argument -- names something this unit declares, \
                  and names it in the form the clause requires.",
        vorbehalt: "**`N028`/`N029` carry a KEY ASYMMETRY that is a plain bug** (found \
                    2026-08-21 while writing this sentence): the map is filled under the \
                    SHORT name and calls are looked up under the FULL path, so `m::f()` \
                    never matches -- `N029` stays silent and `N028` fires FALSELY although \
                    `f` declares its `or R`. `N030` is silent for anything but a bare \
                    unsuffixed name and says so itself (W10). `N022` sees comparisons only \
                    directly under binary operators -- a parenthesis hides one completely. \
                    `N026` is a HINT, not a refusal. And `N015` deliberately does not exist: \
                    where `counterprobe … expects <ident>` declares its ident is not written \
                    down anywhere, and that is a finding about the SPECIFICATION.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 3 probes on `N030`, 2 each on `N027` and `N031`, and \
                      single probes on 12 further codes of this group.",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md, SPRACHE.md §15",
    },
    Satz {
        name: "namen.asm",
        kennungen: &["A001", "A002", "A003", "A004"],
        aussage: "Every `asm` body declares its `arch`, its `effects` and its `costs`, and \
                  every operand it names is a parameter of the enclosing function (`result` \
                  only with a return type). An `asm` block is therefore never a hole in the \
                  effect and cost accounting.",
        vorbehalt: "The DECLARATIONS are checked, never the instructions. What the assembly \
                    really does is assumption, and it belongs to the assumption layer -- \
                    `gabbro zeugnis` counts `asm` lines for exactly that reason. Missing \
                    `clobbers memory` is a HINT (`N026`), not a refusal.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes on `A001` and `A004`. **`A002` and `A003` have \
                      NO probe** -- an `asm` without `effects` or without `costs` is refused \
                      by a line nothing measures.",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md §12",
    },
    Satz {
        name: "namen.bootkette",
        kennungen: &["O007"],
        aussage: "The boot steps of a unit chain up according to their `advances` clauses: \
                  each step starts on the stage its predecessor reached.",
        vorbehalt: "Gappy by construction: a step WITHOUT `advances` is skipped without \
                    invalidating the state, the FIRST step is held against nothing at all, \
                    and steps that are not a call are skipped. The chain is therefore \
                    checked where it is declared, not where it runs.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: one probe on `O007`.",
        fundstelle: "crates/gabbro-check/src/namen.rs; SPRACHE.md §13",
    },
    Satz {
        name: "namen.fnzeigervertrag",
        kennungen: &["N035", "N036", "N037"],
        aussage: "Every function pointer type in the tree carries an `effects` clause and a \
                  `costs` bound, its effect list uses only words that can be carried across a \
                  call whose callee is not statically known (`reads`, `writes`, `allocs`, \
                  `pure`, `diverges`), and it carries no `requires`. A program that passes \
                  this rule therefore has, at every indirect call site, a static promise from \
                  which the effect hull and the cost sum can be computed.",
        vorbehalt: "**The rule buys the hull by REFUSING the rest, and the refusal is the \
                    gap.** `locks`, `locks shared`, `masks`, `consumes` and `publishes` are \
                    rejected at the type because the passes that read them (`geteilt`, \
                    `kontexte`, `m2`, `paarung`) resolve the callee by NAME. So the lock \
                    order, the interrupt-context rule, linearity and the pairing do **not** \
                    cross an indirect call -- a program needing that does not pass, rather \
                    than passing unchecked. *Measured beside it: Caprock's four indirect call \
                    sites take no lock.* And the `let` scan that supplies the local type \
                    picture is FLAT: two bindings of one name in two branches collapse.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: one probe each on `N035` (240), `N036` (243) and \
                      `N037` (247); the positive side is beispiele/49.",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md fnptr",
    },
    Satz {
        name: "namen.ausfuhrhuelle",
        kennungen: &["N038"],
        aussage: "The EXPORT SET of a unit is closed: no `pub` declaration names, in the part \
                  of it that travels into the `.gabi`, an item that this unit declares \
                  without `pub`. The interface `gabbro abi` writes therefore explains every \
                  name it mentions.",
        vorbehalt: "**Two limits, and the first is deliberate.** (1) A name this unit does \
                    NOT declare counts as fine -- the same reticence as `N025`, and for the \
                    same reason: a FRAGMENT names things from outside the cut, and treating \
                    those as private would refuse every excerpt. (2) What travels is measured \
                    on the AST -- declared types, effect places, contract predicates, the \
                    `count` of a table, a lock's `protects`/`rank`/`masks` -- while \
                    `abi::schreibe` cuts the SOURCE TEXT. Both answers agree on this corpus, \
                    and nothing holds them together: a clause that grows a name shape the AST \
                    walk does not know is a hole here and a name in the `.gabi`. *The two \
                    registers over one question are booked, not denied* (W7). And the rule \
                    speaks about NAMES, not about types: an exported signature may still \
                    name a `pub opaque type` whose body the importer cannot use -- that is \
                    `D004`'s business and not this one's.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/273 (a `pub fn` over a private `table`), and the \
                      counter-direction in `rechenwerk.rs` \
                      `eine_schnittstelle_erklaert_jeden_namen_den_sie_nennt`: the closed \
                      hull passes and its `.gabi` checks itself.",
        fundstelle: "crates/gabbro-check/src/bindung.rs; SYNTAX.md section 1, D2",
    },
    Satz {
        name: "namen.bindungsflaeche",
        kennungen: &["N039"],
        aussage: "Within ONE build no two exported declarations carry the same C binding \
                  name. A build is the translation units of one command line together with \
                  every interface loaded by `--with`. Since the emitter does not mangle, a \
                  program that passes this rule has, for each of its exported names, exactly \
                  one definition to link.",
        vorbehalt: "**The reach is the run, and the linker's reach is larger.** Two SEPARATE \
                    invocations whose objects are linked afterwards are invisible here -- \
                    measured 2026-08-25: two units emitted one after the other still give \
                    `ld: multiple definition of 'lesen'`. Closing that needs a manifest \
                    (`manifest.rs`), not a pass. And the rule counts only what carries \
                    `pub`: a private name binds internally since the same day, so it cannot \
                    collide -- **that half rests on the EMITTER writing `static`, not on \
                    this pass.** Nor does it see the names the emitter INVENTS: a lock \
                    writes `L_nimm`/`L_gib`, a table writes `T_speicher`, and a hand-written \
                    `pub fn L_nimm` beside them collides with neither.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/274 (two modules, one name), plus the three directions \
                      measured by hand on 2026-08-25: two units of one run, a `.gabi` \
                      against a unit, and the clean library pair that must stay silent.",
        fundstelle: "crates/gabbro-check/src/bindung.rs; abi.rs, on the C side",
    },
    Satz {
        name: "namen.baugatter",
        kennungen: &["G001", "G002", "G003"],
        aussage: "Every `when` of the unit gates on the BUILD and on nothing else: it names \
                  `TESTBUILD`, that name is declared nowhere in the unit, and no ungated \
                  function calls a gated one by name. A unit that passes therefore has, for \
                  the shipping build, a call graph that is closed WITHOUT the gated items -- \
                  which is the precondition for `emit::emittiere` dropping them and the \
                  result still linking.",
        vorbehalt: "**Four limits, and the first two are the reach of the rule.** (1) `G001` \
                    follows CALLS BY NAME. An indirect call through a function pointer \
                    (`t->senden()`) reaches a gated body without anyone seeing it -- the \
                    `&f` that put it there is not a call and is not checked either. (2) It \
                    follows calls only; an ungated signature that NAMES a gated `type`, \
                    `table` or `const` is not caught, and in the shipping build that is a C \
                    compile error rather than a link error. (3) `N001` does not see a gated \
                    item at all (booked in `namen.doppelung`), so a gated and an ungated \
                    function may carry the same name -- **in the shipping build that is the \
                    intended pair, in the check build it is a duplicate C definition**, and \
                    the one who says so is `cc`, not this pass. (4) The rule says nothing \
                    about whether the gated code is REACHED in the check build: a `check` \
                    that nobody runs gates just as well as one that runs. \
                    **And on the interface side there is one build, not two:** `abi::schreibe` \
                    drops gated items unconditionally, because a `.gabi` names no build -- so \
                    a consumer's harness cannot reach a library's gated helper across the \
                    interface at all. *Measured on 2026-08-28 before that line existed: the \
                    gate was LOST in the `.gabi` and `emit --with` lowered it to a C \
                    prototype.*",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/311 (`G001`, an ungated `fn` calls a gated one), \
                      /312 (`G002`, `when EINE_KONSTANTE`), /313 (`G003`, `const TESTBUILD`); \
                      the positive side is beispiele/52 plus its emission run, which \
                      compares the shipping C against the check C.",
        fundstelle: "crates/gabbro-check/src/gatter.rs; SYNTAX.md section 1, «TB»",
    },
];

// ===================================================================================
//  Pass 2 -- D1/D2
// ===================================================================================

pub const D1D2: &[Satz] = &[
    Satz {
        name: "d.handmutation",
        kennungen: &["D001", "D002"],
        aussage: "No function hand-writes into a `table` that declares `ops`, and no write \
                  site names a field declared `by ops`. The invariant an `ops` template \
                  establishes is therefore not broken by a write this unit can see.",
        vorbehalt: "**Passing this pass does NOT mean the K condition holds** -- and that is \
                    the sharpest finding in this register. `k_haelt()` requires \
                    `breaking.is_empty()`, but the pass only ever reports hand writes: the \
                    `breaking` blocks are COLLECTED, attached to every `ops` table \
                    indiscriminately, printed in the report of `gabbro k-bedingung` -- and \
                    NEVER refused. Beyond that: a write site is only `=`, `publishes`, \
                    `exchange`, so a mutation THROUGH A CALL is no write site at all; \
                    `D001`'s target matching is name-based and misses a `let` alias or a \
                    field path through an intermediate record; and `D002` is the opposite, \
                    too WIDE -- it never checks that the write touches the table, so any \
                    local variable that happens to be called `refcount` falls.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 2 probes on `D002`, probes on `D001`. **The `breaking` \
                      half is measured by nothing, because it refuses nothing.**",
        fundstelle: "crates/gabbro-check/src/kbedingung.rs; SPRACHE.md §10.2",
    },
    Satz {
        name: "d.erschoepfend",
        kennungen: &["D005"],
        aussage: "Every `match` on a `tagged type` names every variant and has no catch-all \
                  branch. A `tagged type` is the one form in which this language states a \
                  CLOSED case distinction, and after this pass the closedness is redeemed \
                  rather than promised by the grammar.",
        vorbehalt: "Silent in three places: only when the matched object is a plain place; \
                    the local type map holds only PARAMETERS, so `let x = f(); match x { … \
                    }` resolves to `Unbekannt` and says nothing; and variants are compared by \
                    SHORT NAME, so two identically named `tagged` types in different modules \
                    are the same type here. **Only what is MISSING is checked** -- a branch \
                    naming a variant that does not exist, or naming one twice, does not fall.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probe on `D005`.",
        fundstelle: "crates/gabbro-check/src/kbedingung.rs; SPRACHE.md §3",
    },
    Satz {
        name: "d.belegtfeld",
        kennungen: &["D010", "D011"],
        aussage: "A `table` that declares `ops` names the field that carries occupancy, and \
                  that field is a `bool` of its own slot -- so the generated `insert`/`remove` \
                  write the thing `beweise/Table_Ops_Erhaltung.thy` proves about.",
        vorbehalt: "It checks that a field is NAMED and two-valued, not that the program keeps \
                    it truthful. A hand-written body may still set it, unless `D001`/`D002` \
                    forbid that -- and they do exactly where `ops` stands.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes on `D010` and `D011`.",
        fundstelle: "crates/gabbro-check/src/kbedingung.rs; messung/OPS-ERZEUGER.md",
    },
    Satz {
        name: "d.opsruf",
        kennungen: &["D012"],
        aussage: "Wherever a generated operation is called, the premises \
                  `beweise/Table_Ops_Erhaltung.thy` charges to the caller STAND above the \
                  call, about the very slot the call names -- the slot is FRESH for \
                  `insert`, the parent is REACHABLE where the table has a `parent` edge, \
                  `s` is a LEAF for `remove` on such a table, and for `relabel` the new \
                  parent is REACHABLE and `s` does NOT lie on its parent chain, that parent \
                  itself included. They stand in the routine's own `requires`, in an \
                  enclosing `if`, or in an enclosing loop `invariant`.",
        vorbehalt: "**It does not PROVE a premise, and it cannot.** A standing `requires` is \
                    the duty pushed one frame outwards, exactly as `blatt_loeschen`'s \
                    `ist_blatt(c, s)` has been since beispiele/01; what changes is that the \
                    duty exists at all, where until 2026-08-28 it was a comment in the \
                    emitted C. Three further edges: the negation of a previous `if` arm is a \
                    fact this rule does not read; a premise under `||` or behind `=>` is not \
                    taken as standing; and an argument that is not a place-shaped expression \
                    is refused rather than skipped. **`M115` is silent on all of these** -- \
                    they are not range statements, which is why the rule is here and not \
                    there. **And `relabel`'s chain premise is read only in the theorem's own \
                    shape** (`!(t.slots[p] reaches t.slots[s] via <parent>)`): the STRICT \
                    form over `ancestors of` is weaker -- `ancestors of` starts the chain at \
                    the parent, so it says nothing about `p == s` -- and it does not \
                    discharge, which is what beispiele/gift/332 measures.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 7 probes on `D012` (321 missing premise, 322 premise \
                      about a DIFFERENT slot, 323 the second half of `einfuegen_erhaelt` \
                      missing, 324 the weaker leaf clause, 331 `umhaengen_erhaelt`'s chain \
                      premise missing, 332 the weaker STRICT-ancestors form of it, 334 that \
                      premise about a different TARGET). The clean side is `beispiele/47`, \
                      which calls all five generated operations.",
        fundstelle: "crates/gabbro-check/src/opsruf.rs; messung/OPS-RUFFORM.md; \
                     messung/OPS-RELABEL.md",
    },
    Satz {
        name: "d.baumkante",
        kennungen: &["D006", "D007", "D008"],
        aussage: "A `table … tree` names its parent/child/sibling edges as real slot fields, \
                  each edge is an `option index into Self`, and no edge points into a \
                  foreign table -- so a tree is a tree and not a graph across carriers.",
        vorbehalt: "Applies at `table … tree` only. A `SlotTyp::Wrapping` falls through to \
                    `D007` deliberately.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes on `D006`, `D007`, `D008`.",
        fundstelle: "crates/gabbro-check/src/kbedingung.rs; SPRACHE.md §10",
    },
    Satz {
        name: "d.undurchsichtig",
        kennungen: &["D003", "D004"],
        aussage: "Outside the declaring module an `opaque type` has neither the arithmetic \
                  nor the implicit conversions of its carrier: `a + b` on two opaque values \
                  is refused (`D003`), and the silent conversion in BOTH directions is \
                  refused (`D004`). Inside the declaring module the representation is known \
                  -- the door is the MODULE BOUNDARY.",
        vorbehalt: "**On today's corpus this sentence has ZERO bite**: all twelve opaque \
                    declarations declare and use in the same module. Before 2026-08-18 `a + \
                    b` fell only by accident, at `M104` and not at the opacity -- wherever \
                    the widths worked out, the nonsense went through. The rule is built, its \
                    whole evidence is poison.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes on `D003` and `D004`. NO corpus site exercises \
                      it.",
        fundstelle: "crates/gabbro-check/src/m1.rs; SPRACHE.md §3 (D1)",
    },
];

// ===================================================================================
//  Pass 3 -- M1 + V1-V3
// ===================================================================================

pub const M1: &[Satz] = &[
    Satz {
        name: "m1.bereich",
        kennungen: &[
            "M101", "M102", "M103", "M104", "M105", "M106", "M107", "M110", "M111", "M112",
            "M113", "M114", "M115", "M116", "M117", "M118", "M119",
        ],
        aussage: "For every arithmetic operation, assignment, argument, return and index in \
                  the tree the checker has computed an interval for the value, and that \
                  interval fits the declared range of its destination. No overflow, no \
                  truncating width change, no division by a denominator whose interval \
                  contains zero, and no index outside the declared bound of its table \
                  reaches the emitter without a run-time check being emitted for it.",
        vorbehalt: "The interval comes from DECLARED ranges and from flow facts (V1-V3); \
                    where neither carries, the pass refuses instead of assuming. A value \
                    entering through a foreign body carries only what that body's signature \
                    declares. **And a disequality at the range boundary does not narrow**: \
                    `if n == 0 { return 0; }` followed by `n - 1` still reports `M104`, \
                    because `n != 0` is not turned into `n >= 1` although `0` is the \
                    declared lower bound.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 15 probes on `M104`, 12 on `M101`, 8 on `M103`, 3 on \
                      `M102`, single probes on 9 further codes. **`M106`, `M107`, `M110` and \
                      `M114` have NO probe.**",
        fundstelle: "crates/gabbro-check/src/m1.rs; SPRACHE.md §3.2",
    },
    Satz {
        name: "m1.verfeinerung",
        kennungen: &["M130", "M131", "M132"],
        aussage: "Where a body carries `refines g`, the named `g` is a `spec fn` declared in \
                  this unit, it takes the same number of parameters as the body, and the \
                  clause stands at an `impl fn` -- a body Gabbro lowers itself. A unit that \
                  passes therefore carries, for every `refines`, a WELL-FORMED refinement \
                  obligation: one whose specification exists and whose two sides can be \
                  quantified over the same variables.",
        vorbehalt: "**It says nothing about whether the body redeems the specification.** \
                    That is the generated obligation, and it is counted rather than \
                    discharged (`gabbro pflichten`). Measured 2026-08-24: the obligation \
                    arises, goes through `--isabelle`, and is REFUSED there by name -- \
                    `body-effect`, because there is no Isabelle semantics of a Gabbro body. \
                    *The pass makes the obligation well-formed; it does not make it \
                    provable.* And the arity check is a NECESSARY condition, not a \
                    sufficient one: two functions of equal arity may still take unrelated \
                    parameter types, and nothing here compares them.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift 253/254/255, one probe per code; and three mutations \
                      (`refines-auch-an-spec-fn`, `refines-nennt-ins-leere`, \
                      `refines-ungleiche-stelligkeit`). Clean site: \
                      `beispiele/50-verfeinerung.gab`",
        fundstelle: "crates/gabbro-check/src/m1.rs::verfeinert_pruefen; \
                     messung/VERFEINERUNG.md",
    },
    Satz {
        name: "v1.bereichsverengung",
        kennungen: &["M108", "M109"],
        aussage: "A checked range condition narrows the range of the checked place in the \
                  branch after it: after `if x >= 1 { … }` the place `x` has range `1 .. \
                  max` inside the branch, and the `else` branch carries the negated fact. \
                  **Since 2026-08-25 such a fact SURVIVES a call** unless the callee's \
                  declared `effects` -- which `E008` reconciles against its hull -- can write \
                  the place. Before that every call dropped every non-local fact, and three \
                  of four measured cases were false rejections, a `pure` call among them.",
        vorbehalt: "TWO preconditions, both found the hard way. (1) The place must stay the \
                    SAME between check and use -- a place leading through a `device` \
                    register carries NO fact in either direction, because it lowers to a \
                    `volatile` read and the hardware may change it between the two lines. \
                    Until 2026-08-20 V1 narrowed there and the program passed with zero \
                    errors («B33»); the emitted C indexed an eight-slot array with a value \
                    the hardware may set freely. (2) The `else` fact presupposes \
                    TRICHOTOMY -- that the negation of a comparison is itself a comparison. \
                    That holds over integers and breaks for any partially ordered carrier: \
                    with a NaN operand all comparisons are false and `else` yields nothing. \
                    (3) **The survival across a call is refined only where it is safe:** \
                    every written place must be KNOWN world state and must not be a parameter \
                    name of the callee -- otherwise the coarse rule applies and everything \
                    dies. So the precision rests on `E010`, whose reach is a drawn line; \
                    incompleteness there costs precision, not soundness.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 2 probes on `M108`, 2 on `M109`; the «B33» half is \
                      measured by `gift/213` and `gift/214`.",
        fundstelle: "crates/gabbro-check/src/m1.rs (`fakten_aus`); SPRACHE.md §3.2, V1",
    },
    Satz {
        name: "v2.relationale-verengung",
        kennungen: &[],
        aussage: "A checked relation between two places becomes a branch fact: under the \
                  fact `a >= b` the expression `a - b` has range `0 .. a.max - b.min`, and \
                  under `a > b` range `1 .. a.max - b.min`. This is the rule that keeps \
                  `narrow` from becoming a ritual -- 54 relational sites of the 102 \
                  flow-sensitive ones hang on it.",
        vorbehalt: "**Four restrictions, and the fourth is the sharpest.** (1) Comparison \
                    facts only, between DIRECTLY checked places only -- `a >= b + 1` carries \
                    nothing. (2) A fact dies at every write to a place it mentions. (3) A \
                    write THROUGH A POINTER kills every non-local fact, because without an \
                    alias analysis there is no statement about what it hit -- and there is \
                    no alias analysis anywhere in this checker. (4) A place through a \
                    `device` register carries no fact, as for V1. **This sentence has NO \
                    diagnostic code of its own**: V2 WIDENS what passes, and where it does \
                    not carry the refusal arrives as `M104` or `M101` from `m1.bereich`. \
                    That is why it cannot be poisoned directly, and why it is the sentence \
                    in this register with the most weight and the least measurement.",
        stand: Satzstand::Vermutet,
        gemessen_an: "**Still nothing measures this sentence, and 2026-08-24 made that \
                      SHARPER rather than better.** The attempt to build the pair by hand \
                      uncovered a NON-DETERMINISM in the checker instead: the same bytes gave \
                      `M104` on some runs and nothing on others \
                      (`messung/DETERMINISMUS.md`). The measurement rested on one side of \
                      that coin flip and is withdrawn; both corpus halves are removed. \
                      **The argument for halves A and B stands** (`messung/V2.md` §3, §4) -- \
                      but §4d, the alias rule that carries the whole sentence, is now \
                      explicitly UNVERIFIED. *A sentence that looked unmeasured is now \
                      measured as unmeasurable-by-today's-harness, and that is a step.*",
        fundstelle: "crates/gabbro-check/src/m1.rs (`beziehung`, line 1766); SPRACHE.md \
                     §3.2, V2; MESSUNGEN.md:370 (54 of 102)",
    },
    Satz {
        name: "v3.variantenverengung",
        kennungen: &[],
        aussage: "A `match` on a `tagged` type narrows, inside each branch, to that variant \
                  including its payload -- so the payload of the matched variant may be read \
                  without a further check.",
        vorbehalt: "Carries only because `D005` makes the match exhaustive, and `D005` is \
                    itself silent for a matched object that is not a plain place. Like V2 \
                    this rule has no code of its own -- it widens rather than refuses.",
        stand: Satzstand::Vermutet,
        gemessen_an: "No direct probe. The exhaustiveness half is measured (`D005`), the \
                      narrowing half is not.",
        fundstelle: "crates/gabbro-check/src/m1.rs; SPRACHE.md §3.2, V3",
    },
    Satz {
        name: "m1.fnzeiger",
        kennungen: &["M127", "M128", "M129"],
        aussage: "A function pointer value comes only from `&f` where `f` is a declared \
                  function (`M127`), and it goes only into a slot whose contract COVERS the \
                  function's own: every effect `f` declares is one the slot allows, and `f` \
                  costs at most what the slot promises (`M128`). A call through a place is \
                  admitted only where that place has a function pointer type (`M129`), and \
                  its arguments and result are held against the contract's. **What every \
                  pass downstream computes with at an indirect call is therefore a fact about \
                  some real function, not the wish written at the type.**",
        vorbehalt: "Subsumption is checked on the effect SET and the cost NUMBER, and on the \
                    arity -- **not on the parameter types**, which are compared only at the \
                    call. Two pointer types with the same arity and compatible contracts but \
                    different parameter types are therefore interchangeable here, and the \
                    mismatch surfaces one level down, at `M104`, or not at all when nobody \
                    calls through the slot. *`ensures` at the function is not carried into \
                    the pointer type at all* -- a caller through the pointer learns nothing \
                    from it.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: one probe each on `M127` (244), `M128` (241) and \
                      `M129` (245); the positive side is beispiele/49.",
        fundstelle: "crates/gabbro-check/src/m1.rs; SYNTAX.md fnptr",
    },
    Satz {
        name: "m1.endlichkeit",
        kennungen: &["F001", "F002", "F004", "F005"],
        aussage: "Every floating-point value reaching an operation that requires finiteness \
                  carries a finiteness fact -- from a declaration, from `narrow … to finite`, \
                  or from being a literal.",
        vorbehalt: "«F» is deliberately small: the price of full IEEE-754 is a SECOND FACT \
                    LOGIC, not a second number type. `!(x < y)` does not yield `x >= y` when \
                    an operand is NaN, and that is exactly the machinery every narrowing in \
                    this language uses. Finiteness is tracked; rounding mode and error \
                    bounds are not, and whether the rounding mode belongs in the TYPE is an \
                    open question.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 3 probes on `F002`, 2 on `F001`, probes on `F004` and \
                      `F005`.",
        fundstelle: "crates/gabbro-check/src/m1.rs; SPRACHE.md «F»",
    },
];

// ===================================================================================
//  Pass 4 -- M3
// ===================================================================================

pub const M3: &[Satz] = &[
    Satz {
        name: "m3.zeigerrecht",
        kennungen: &["R002", "R003"],
        aussage: "Every write through a pointer PARAMETER goes through one whose declared \
                  right includes writing, and every read through one whose right includes \
                  reading. `own` satisfies both.",
        vorbehalt: "**Only pointer PARAMETERS, and only the BASE NAME.** A `let p = …`, a \
                    global, a field or a return value carries no rights at all. As a WRITE \
                    only `Zuweisung` and `Publish` count -- an `exchange`, an `AwaitLoad` or \
                    a write by a callee (`writes p.x`) is no write for `R002`. Predicates \
                    are never read, so a read over a `w`-only pointer inside a `retry … \
                    until` is invisible. And the two halves of the file are asymmetric: the \
                    register half treats `X |= 1` correctly as read AND write, the pointer \
                    half treats every assignment as a write only, so `p |= 1` over a \
                    `w`-only pointer gives no `R003`.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: one probe each on `R002` and `R003`.",
        fundstelle: "crates/gabbro-check/src/m3.rs; SYNTAX.md §3",
    },
    Satz {
        name: "m3.adressraum",
        kennungen: &["R008"],
        aussage: "A pointer argument that is a bare PARAMETER of the caller reaches a \
                  parameter declared in the SAME address space. `mmio` is volatile and \
                  device-mapped, `normal` is not, and the emitter lowers them differently -- \
                  a program that passes therefore does not launder one space into the other \
                  across a call.",
        vorbehalt: "**Only a bare parameter name is compared, and that is an \
                    UNDER-approximation stated as one.** A field, a local, a `let`, a return \
                    value or a global carries no declared space this pass can read -- because \
                    `Typ::Zeiger(Box<Typ>)` DROPS `Raum` at construction and only the \
                    declaration still has it. *Carrying the space in the semantic type is the \
                    bigger fix and is not built.* And it compares two spaces for equality: \
                    there is no lattice, so nothing says whether any conversion would ever be \
                    legitimate. **`R001` remains the only other space test** (`raum == Dma` \
                    at an `ops` carrier); `code`, `boot` and `port` are still checked by \
                    nothing at all.",
        stand: Satzstand::Gemessen,
        gemessen_an: "**Built 2026-08-24 from the pass register's own finding** -- *the address \
                      space is checked NOWHERE: apart from `R001` there is no test on a space \
                      at all* (2026-08-21, written down and not acted on). \
                      Reproduced first: a `ptr<normal, rw>` reaching a `ptr<mmio, rw>` \
                      parameter gave zero errors. Probe \
                      `beispiele/gift/259-raum-laeuft-durch.gab`, anchor \
                      `adressraum-egal-am-rufort`; zero sites in the corpus.",
        fundstelle: "crates/gabbro-check/src/m3.rs::eigen_doppelt; messung/PASSREGISTER.md",
    },
    Satz {
        name: "m3.syntaktischer-alias",
        kennungen: &["R004", "R007"],
        aussage: "No call passes the SAME syntactic place to two pointer parameters that may \
                  both be written -- neither to two `own` parameters (`R004`) nor to two \
                  writable non-`own` ones (`R007`). A callee with two writable pointer \
                  parameters may therefore assume that its two arguments are distinct places \
                  WHENEVER they are written as distinct places at the call site.",
        vorbehalt: "**This is the syntactic HALF of the alias question, and the only half \
                    decidable without an alias analysis -- which this checker does not have.** \
                    Two DIFFERENT names for one object stay indistinguishable: a re-view \
                    (`fn(ptr A) -> ptr B`), a global reached twice, two indices that happen \
                    to be equal. `messung/RACE.md` carries those as A2 and A3, and nothing \
                    carries them. **Compared is the PLACE, not the root:** `f(p->a, p->b)` \
                    passes, and it should -- two fields of one record are not one place. \
                    *That also means `f(t[i], t[j])` passes with `i == j`.* And only \
                    parameters: a pointer arriving through a `let`, a global or a return \
                    value carries no declared right, so it is not marked writable here.",
        stand: Satzstand::Gemessen,
        gemessen_an: "**`R007` built 2026-08-24** -- `messung/RACE.md` listed form `A1` among \
                      the four that NOTHING carries, and `gabbro alias` had counted the site \
                      since 2026-08-21 (`S3`: one call, writable) without any pass refusing \
                      it. *A measurement without a rule is the state a rule grows out of.* \
                      Probe: `beispiele/gift/257-alias-zwei-schreibbare.gab`; anchor \
                      `syntaktischer-alias-geht-wieder-durch`. `R004` carries the `own` half \
                      and has its own probe.",
        fundstelle: "crates/gabbro-check/src/m3.rs::eigen_doppelt; messung/RACE.md A1",
    },
    Satz {
        name: "m3.registerklasse",
        kennungen: &["R005", "R006"],
        aussage: "A `device` register field is read only if its class permits reading and \
                  written only if its class permits writing -- a class per FIELD, not per \
                  register, because a mixed register like `FSTS` carries both kinds side by \
                  side.",
        vorbehalt: "Built 2026-08-20 («B23»). Until then this was booked as discharged BY \
                    the pointer rights and was not: the note on `R003` spoke the sentence, \
                    no line did it, and `return d.NUR_W.A;` gave zero errors. Devices are \
                    keyed by SHORT NAME without module path, so two identically named \
                    `device` declarations in two modules collide -- M2 and Phasen are \
                    module-aware here, M3's register half is not.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 2 probes on `R006`, one on `R005`.",
        fundstelle: "crates/gabbro-check/src/m3.rs; SYNTAX.md §3, «B23»",
    },
    Satz {
        name: "m3.dma-traeger",
        kennungen: &["R001", "R004"],
        aussage: "No carrier declaring `ops` hangs on a `ptr<dma, …>` parameter, and the \
                  same syntactic place does not stand at two `own` positions of ONE call.",
        vorbehalt: "**`R004` is not an alias analysis and says so**: it compares place TEXT, \
                    so `zwei(q, q.f)` passes, and it reports once per call. ~~**And the \
                    ADDRESS SPACE itself is checked nowhere else**: the only real test on a \
                    space in the whole checker is `R001`'s `raum == Dma`.~~ **Half closed \
                    2026-08-24 by `R008`** (`m3.adressraum`): the space must MATCH at a call, \
                    for arguments that are bare parameters. *`code`, `boot` and `port` are \
                    still checked by nothing, and `Typ` still drops `Raum` -- so a field, a \
                    local or a return value carries no space this pass can read.* The module header's second claim -- *„a \
                    `dma` pointer reaches memory a DEVICE writes; reading it like `normal` \
                    means taking a snapshot for a fact\"* -- **is redeemed by no line in \
                    this file.**",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: one probe each on `R001` and `R004`. The address-space \
                      claim of the module header has no probe because it has no code.",
        fundstelle: "crates/gabbro-check/src/m3.rs; SYNTAX.md §3",
    },
    Satz {
        name: "m3.barriere",
        kennungen: &[],
        aussage: "A `dma` access is separated from the surrounding accesses by the barrier \
                  its address space demands.",
        vorbehalt: "**NOT built, and it is not pass work.** Which barrier a `dma` access \
                    demands is a statement about the MEMORY MODEL -- the same axiom layer as \
                    at the pairing. The sentence stands here so the hole has a name and a \
                    place instead of being absent.",
        stand: Satzstand::Vermutet,
        gemessen_an: "Nothing measures it. There is no probe and no mutation, and there \
                      cannot be one until the memory model is written down.",
        fundstelle: "SYNTAX.md §3; PLAN.md, axiom layer beside A10",
    },
];

// ===================================================================================
//  Pass 5 -- M2
// ===================================================================================

pub const M2: &[Satz] = &[
    Satz {
        name: "m2.linear-genau-einmal",
        kennungen: &["L101", "L102", "L103", "L104", "L105", "L107", "L108", "L109"],
        aussage: "A linear value that is a PARAMETER of the function, or is bound by `let x \
                  = f()` from a direct call, is consumed exactly once on every path the pass \
                  models: branches of an `if`/`match` are walked on copies and reconciled, a \
                  value living before a loop may not be consumed in its body, and neither \
                  zero consumptions (a leak) nor two (a use after its end) pass. **Real \
                  linearity is the one mechanism no existing tool supplies** -- Verus' \
                  `tracked` is AFFINE, Rust is affine, and affine forbids only the second \
                  use, never the missing one.",
        vorbehalt: "**„A linear value that arises\" is too wide, and the module header says \
                    it anyway.** Only two sources are tracked; a linear return value at \
                    STATEMENT POSITION (`erzeuge();`) creates no entry at all, so there \
                    „exactly once\" does not even hold as „at most once\". A call statement \
                    does not descend into nested arguments, so `aussen(wecken(p));` does not \
                    see `wecken`. The statement walker's `_` arm swallows the own \
                    expressions of `publish`, `exchange`, `narrow`, `await` and the loop \
                    heads, so a consumption in `retry … until wecken(p)` is invisible; the \
                    `match` object is never checked; and consumption matches on the BASE \
                    NAME, so `wecken(p.feld)` counts as consuming `p`. The internal \
                    „does this branch end\" test descends through `if` and `match` since \
                    2026-08-25 -- a block whose last statement is a branch in which EVERY \
                    path returns now counts as ending, and the consumption on those paths is \
                    carried over instead of dropped. **It still knows nothing about \
                    divergence**: a call to a `-> never` function, or a `forever` without an \
                    exit, counts as continuing, although the header promises such a branch \
                    does not count. Alias and ghost erasure are explicitly out of scope.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 2 probes on `L104`, probes on `L101`, `L102`, `L103`, \
                      `L107`, `L108`, `L109`.",
        fundstelle: "crates/gabbro-check/src/m2.rs; SPRACHE.md §4",
    },
    Satz {
        name: "m2.leaves",
        kennungen: &["L106"],
        aussage: "Every name in a `leaves` clause is a parameter of this function and its \
                  type is linear -- `leaves` names the values that SURVIVE the loop, and it \
                  deliberately does not consume.",
        vorbehalt: "Only PARAMETERS count as a binding; a `let`-bound linear value in \
                    `leaves` is reported as naming no binding.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probe on `L106`.",
        fundstelle: "crates/gabbro-check/src/m2.rs; SPRACHE.md:858",
    },
    Satz {
        name: "m2.geisterloeschung",
        kennungen: &[],
        aussage: "A ghost value has no representation in the emitted C: `f(m : Marke, v : \
                  u32)` lowers to `uint32_t f(uint32_t v)`.",
        vorbehalt: "**This is NOT this pass.** m2.rs says so in its header: it checks \
                    linearity, not erasure. The erasure lives in the EMITTER, and the two \
                    halves are in different files -- only the pair would carry the sentence. \
                    It stands here because the pass list is the specification and the claim \
                    otherwise has no address.",
        stand: Satzstand::Vermutet,
        gemessen_an: "No probe measures the pair. The emitter half was built and demonstrated \
                      once; nothing holds it against the checker half.",
        fundstelle: "crates/gabbro-check/src/m2.rs (header), emit.rs; SPRACHE.md §4",
    },
];

// ===================================================================================
//  Pass 6 -- M4/Schleifen
// ===================================================================================

pub const SCHLEIFEN: &[Satz] = &[
    Satz {
        name: "schleifen.marke",
        kennungen: &["S001", "S002"],
        aussage: "Every `leave` and `next` names a loop label that exists and ENCLOSES it -- \
                  the parser accepts `leave x;` because `x` is an identifier, and only this \
                  pass can say whether there is a label. And the `else` arm of a `let … \
                  else` diverges or returns instead of falling through silently.",
        vorbehalt: "A `traverse` carries no label, so a `leave` inside one can only target an \
                    enclosing `retry`/`forever`. The descent is hand-written with a `_` arm \
                    rather than the shared one -- today every block-carrying arm is covered, \
                    but a new statement kind with a body escapes `S001`/`S002` SILENTLY, \
                    which is exactly the class the shared walker was written against. \
                    „Diverges\" is decided from the LAST statement only, and a call counts as \
                    diverging only if its short name is in this unit's `-> never` list.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 2 probes on `S001`, 2 on `S002`.",
        fundstelle: "crates/gabbro-check/src/schleifen.rs; SYNTAX.md §8",
    },
    Satz {
        name: "schleifen.fortschritt",
        kennungen: &["S003", "S004", "S005", "S006", "S007", "S008"],
        aussage: "A `progress X` names a declared and FALSIFIABLE assumption, a `by \
                  decreasing` measure names the traversal variable or a name the body writes, \
                  a `by consuming` names at least one `consumes` in its `touches` (`S008`), \
                  and an `on_exceeded` names a function that returns.",
        vorbehalt: "**Necessary, not sufficient, and the pass says so: it is NOT checked \
                    that the measure FALLS.** Those are two different statements and the \
                    folder confused them until 2026-08-20 -- `consuming.ordnung` booked \
                    `abstieg` as having a reader since `S005` exists, and `S005` establishes \
                    neither the fall nor the minimality of the choice. ~~**`by unvisited` and `by consuming` are not \
                    checked for descent AT ALL**~~ -- **half closed 2026-08-24 by `S008`:** \
                    `by consuming` claims the domain SHRINKS, and without a `consumes` in its \
                    `touches` the claim has no carrier. *Necessary, not sufficient, as at \
                    `S005`: THAT it shrinks on every pass stays the prover's business.* \
                    **`by unvisited` needs nothing here and that is not an omission** -- it \
                    visits each element of a FINITE domain at most once, so it terminates by \
                    construction; the domain bound is `K003`'s business. The written-names test \
                    counts only direct writes, so a name changed by a CALLEE counts as \
                    unmoved and `S005` can fire falsely. And `S007` is a HINT: an \
                    `on_exceeded` that names nothing still passes with zero errors.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: one probe each on `S003`, `S004`, `S005`, `S006`, and \
                      since 2026-08-24 probe 260 on `S008` -- built from the pass register's \
                      own finding of 2026-08-21, which was written down and not acted on. \
                      Anchor `consuming-ohne-consumes-geht-durch`; zero sites in the corpus. \
                      `S007` is a hint and has none.",
        fundstelle: "crates/gabbro-check/src/schleifen.rs; SYNTAX.md §8; schablonen.rs \
                     `consuming.ordnung`",
    },
];

// ===================================================================================
//  Pass 7 -- Paarung
// ===================================================================================

pub const PAARUNG: &[Satz] = &[
    Satz {
        name: "paarung.keine-waise",
        kennungen: &["V001", "V002", "V003"],
        aussage: "For every expected payload there is one that publishes it, and the other \
                  way round: no `awaits` without a `publishes` on the same atomic, and no \
                  `publishes` without an `awaits`. An orphaned half is the error nobody sees \
                  -- an `awaits` nobody delivers to reads valid garbage, a `publishes` \
                  nobody expects is a barrier without a reason.",
        vorbehalt: "**The module header says the pairing runs over the TRANSITIVE set; the \
                    code takes the GLOBAL one** (found 2026-08-21 while writing this \
                    sentence). Both sets are unioned over ALL functions of the tree, and the \
                    call graph contributes only an incompleteness flag. A `publishes` in \
                    module A therefore pairs with an `awaits` in module B with no call \
                    relation whatsoever. The true statement is: *somewhere in this \
                    translation unit there is a counterpart* -- coarse in the safe direction \
                    (fewer orphans reported), but far weaker than it reads. The index is \
                    erased, so `c.slots[s]` and `c.slots[i]` pair. An `observed by` atomic \
                    is exempt from BOTH halves -- the assumption layer carries it then. And \
                    `V003` is a HINT whose `continue` also skips `V008`, `V004` and `V005` \
                    for that function, although the relaxed check has nothing to do with the \
                    call graph.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: one probe each on `V001` and `V002`. `V003` is a hint \
                      and has none.",
        fundstelle: "crates/gabbro-check/src/paarung.rs; SPRACHE.md part II §1",
    },
    Satz {
        name: "paarung.ordnung",
        kennungen: &["V004", "V005", "V008"],
        aussage: "An atomic that carries payload has a memory ordering strong enough for it: \
                  neither an explicitly `relaxed` atomic nor one without any ordering word \
                  carries payload, and every published payload lies inside the superset \
                  declared at the `atomic`.",
        vorbehalt: "**The ordering check exists only on the PUBLISH side.** An `awaits` on an \
                    orderless atomic is silent, and an `exchange … publishes` moves its \
                    payload straight through, so `V004`/`V005` do not apply to it at all. If \
                    the base name does not resolve to a declared `atomic` (a device \
                    register, a foreign module), the store counts as an ordered publication \
                    -- fail-open in that direction. The superset is voluntary: no clause, no \
                    check.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: one probe each on `V004`, `V005`, `V008`.",
        fundstelle: "crates/gabbro-check/src/paarung.rs; SPRACHE.md part II §1",
    },
    Satz {
        name: "paarung.reihenfolge",
        kennungen: &["V006", "V007"],
        aussage: "A published payload is not written AFTER its `publishes`, and an expected \
                  payload is not read BEFORE its `awaits` -- so the release/acquire pair \
                  really brackets the data it is supposed to protect.",
        vorbehalt: "**`V007` is not the mirror image of `V006`.** The write side descends \
                    into sub-blocks, the read side does not -- a read inside an `if` branch \
                    before the `awaits` is invisible. Both compare BASE NAMES only, so `n.a` \
                    before and `n.b` after counts as covered. And a payload written both \
                    before AND after the publish falls silently: the check skips any name \
                    already in the written set.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 2 probes on `V006`, one on `V007`.",
        fundstelle: "crates/gabbro-check/src/paarung.rs; SPRACHE.md part II §1",
    },
    Satz {
        name: "paarung.fehlende-paarung",
        kennungen: &["V009"],
        aussage: "No atomic that carries no payload anywhere -- nothing publishes on it, \
                  nothing awaits it, no superset, no `observed by` -- gates a branch behind \
                  which a foreign shared mutable place is read. Where that shape stands, a \
                  pairing is MISSING: the value decides whether another core's place may be \
                  read, and that is a payload nobody named.",
        vorbehalt: "**The corpus triggers this rule ZERO times, and that is the first thing \
                    to know about it.** `messung/ordnung/tore.py` counts 20 bindings out of an \
                    atomic and **0 plain loads** -- the only plain load in the tree is `V009`'s \
                    own poison probe (W23). By the rule that killed `locks ordered` -- no \
                    construct without a measured need -- this would be a candidate for \
                    removal. It stands because its target surface is not the Gabbro corpus but \
                    a real kernel's ordering sites, and THERE nothing is measured yet; the \
                    ordering sample (`messung/ORDNUNGSSTICHPROBE.md`) is the run that decides \
                    it. **Until it has run, the need for `V009` is conjectured at one place \
                    and refuted at the only place available** -- so it is not to be extended. \
                    \n\n**This is the only rule of the pass that looks for an ABSENT clause, and \
                    it finds ONE shape of absence.** A missing pairing without a branch is \
                    invisible to it, and so is one whose payload is read by a CALLEE: only \
                    places named syntactically inside the gated statements count, and \
                    `eigene_ausdruecke` gives a call no arguments. The gate must be a PLAIN \
                    load -- an `exchange` result is not one (the RMW is the third form of \
                    the pairing and has its own slot), so a payload behind a CAS gate falls \
                    nowhere. Three exemptions are unchecked assumptions in the safe \
                    direction: a read under `locks`/`observes`, a place this body writes \
                    itself, and the gating atomic read behind its own gate (the one-shot \
                    latch of the finding's §5.2). It runs over function bodies and over the \
                    `can_fail` body of a probe, and over NOTHING ELSE -- an `axiom` or an \
                    `entry` is invisible to it. And the corpus does not measure this rule AT \
                    ALL: `messung/ordnung/tore.py` counts 20 bindings out of an atomic \
                    over the corpus and NOT ONE of them is a plain load -- the only plain \
                    load in the tree is this rule's own poison probe, so the rule hangs on \
                    that probe and on nothing else.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/301-tor-ohne-paarung.gab -- one probe, and the corpus \
                      contributes nothing (0 plain atomic loads, measured).",
        fundstelle: "crates/gabbro-check/src/paarung.rs; messung/ORDNUNGSFINDER.md §4",
    },
    Satz {
        name: "paarung.schreiber",
        kennungen: &["V010"],
        aussage: "A published payload whose base name is a module-level shared name is \
                  written by the publishing function itself or by one of the functions it \
                  reaches -- never only by a writer outside that hull. A release store \
                  publishes the writes of its OWN thread, so a pairing whose payload comes \
                  from elsewhere type-checks and does not carry.",
        vorbehalt: "**It catches the foreign NAME, not the foreign CORE.** Two cores running \
                    the same function are one writer to the call graph, and nothing in the \
                    language says otherwise -- the finding's case (`seal_cache_granule` \
                    against `record_cache_granule`) is one where the two coincide. It is \
                    silent when the payload has no writer in this unit at all (`beispiele/14`, \
                    `virtio-net`) -- an outside writer is what `observed by` and the \
                    assumption layer are for. Payloads whose base name is a PARAMETER are \
                    excluded on purpose: `b.daten` in two functions is two `b`. And it \
                    inherits `V003`'s `continue`: for a function with an incomplete call \
                    hull it never runs.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/302-fremder-schreiber.gab -- one probe. Over the corpus \
                      it is silent: all 7 payload publications write their payload in their \
                      own body.",
        fundstelle: "crates/gabbro-check/src/paarung.rs; messung/ORDNUNGSFINDER.md §5",
    },
];

// ===================================================================================
//  Pass 8 -- effects
// ===================================================================================

pub const WIRKUNGEN: &[Satz] = &[
    Satz {
        name: "wirkungen.pflicht",
        kennungen: &["E001", "E002", "E003", "E004"],
        aussage: "`effects` is NOT fail-open: a function without an `effects` clause is a \
                  translation error, and whoever touches nothing writes `effects { pure }`. \
                  `pure` stands alone or not at all. The obligation falls at the ABSENCE, \
                  not at the content -- a tool that reads a missing clause as „no effects\" \
                  rewards leaving it out.",
        vorbehalt: "Only `fn` and `axiom` are looked at. A `device` transition (whose \
                    `effects` is optional), a `check`, a probe: no `E001`, no body \
                    comparison. `E003` is a HINT, so a `divergent fn` that does not name \
                    `diverges` passes.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes on `E001` and `E002`. `E003` is a hint; `E004` \
                      has no probe.",
        fundstelle: "crates/gabbro-check/src/wirkungen.rs; SPRACHE.md §7",
    },
    Satz {
        name: "wirkungen.rahmen",
        kennungen: &["E005", "E010", "E011"],
        aussage: "The body writes no non-local place that no write effect covers (`E005`), \
                  reads no KNOWN world state that no `reads`/`publishes` effect covers \
                  (`E010`), and a `traverse` with `touches` touches no more than `touches` \
                  names (`E011`).",
        vorbehalt: "**The two halves are asymmetric and no comment says so:** writing is \
                    strict over all non-local places, reading is checked for GLOBALS only -- \
                    parameters, constants and anything that is not \
                    `static`/`atomic`/`table`/`device`/`state` fall out silently. Coverage \
                    is a PREFIX TEXT COMPARISON on the rendered place, so two names for the \
                    same location are two places. The statement walker is hand-written with \
                    a `_` arm and misses the source of a `let … else`, the `until` predicate \
                    of a `retry` and the object of a `traverse`; `lenof(TABLE)` is not a read \
                    at all. `E011` applies only where `touches` is written, and a `traverse` \
                    over a PARAMETER is not held against it. **And `retry`/`forever` carry \
                    their own `effects` clauses that this pass NEVER checks against the \
                    body** -- only `traverse.touches` has a reader.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 2 probes on `E005`, probes on `E010` and `E011`.",
        fundstelle: "crates/gabbro-check/src/wirkungen.rs; SPRACHE.md §7",
    },
    Satz {
        name: "wirkungen.abschluss",
        kennungen: &["E006", "E007", "E008", "E009"],
        aussage: "The declared `effects` of a function are closed over its call hull: every \
                  effect a reachable callee has has a counterpart in the caller's list, every \
                  `locks` in the body stands in an effect, and a body taking a lock \
                  exclusively does not declare it `locks shared`. **This holds whether the \
                  hull is complete or not** -- the hull is a LOWER bound, so everything IN it \
                  really happens and demanding that it be declared is sound regardless of \
                  what is missing. Where the hull is INCOMPLETE, `E009` says so as a hint, \
                  and what is then unavailable is the other direction: no completeness. \
                  **Since 2026-08-25 this also covers the `can_fail` body of a `check`**, \
                  which carries no clause and is therefore `pure` by construction: a call \
                  with any effect other than `reads` is refused there. *That closes a second \
                  hole with it -- `consumes` is an effect, so no linear value can be consumed \
                  in a probe body, and the double free that M2 does not see there has become \
                  unwritable.*",
        vorbehalt: "~~At a CYCLE the hull is cut, `E009` is emitted as a HINT and the pass \
                    `return`s before any `E008` check -- recursive functions are not checked \
                    for frame fidelity at all; and the reason PROPAGATES UPWARDS, so one \
                    unresolvable edge deep down devalues `E008` for the entire call chain \
                    above it.~~ **Closed 2026-08-24.** The hull is a lower bound, so the \
                    check is sound under incompleteness and now CONTINUES; `E009` still \
                    stands as the third state, for completeness only. *Ten corpus sites \
                    carried `E009` and had their frame unchecked entirely; none of them turns \
                    out to be wrong, and the probe that shows the recovered bite is 261.* \
                    **A hint that switches a check OFF is more expensive than the check is \
                    worth.** The hull is still cut at a cycle, at a callee without `effects`, \
                    an unknown name, more than 100 000 steps, or an argument that is not a \
                    place -- what is lost there is COMPLETENESS, not the refutation. An `extern fn` gets NO body check whatsoever, yet counts as \
                    complete, so its CLAIMED effects enter every caller as truth -- that is \
                    an assumption, not a finding. Closure is computed over SETS, not paths. \
                    And places are compared only for known world state: for everything else \
                    only the KIND is compared, so `writes a` covers `writes b`. `E010`'s \
                    reach is a drawn LINE -- known world state only.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 10 probes on `E008`, probes on `E006` and `E007`. \
                      `E009` is a hint. **Probe 261 measures the recursive case since \
                      2026-08-24** -- the case the sentence used to exclude, and it gave zero \
                      errors before. Anchor: \
                      `rahmen-faellt-unter-unvollstaendiger-huelle-aus`.",
        fundstelle: "crates/gabbro-check/src/wirkungen.rs, aufrufgraph.rs; SPRACHE.md §7; R16",
    },
    Satz {
        name: "wirkungen.probenrumpf",
        kennungen: &["E008"],
        aussage: "The `can_fail` body of a `check` carries no `effects`, no `costs` and no \
                  `locks` clause -- and therefore the strictest contract there is: **`pure` \
                  by construction**. A call whose callee declares any effect other than \
                  `reads` is refused there. What remains is what a counterprobe does: read, \
                  compute, compare, return -- and that is what the corpus does.",
        vorbehalt: "**What closes this is a REFUSAL, not a check of the body -- and a hole \
                    closed by refusal is closed only as far as the refusal reaches.** Most \
                    passes still walk `ItemArt::Funktion` and never enter this block. M2 does \
                    not see a consumption here at all; what makes `nimm(m); nimm(m);` \
                    unwritable is that `consumes` IS an effect, so the call falls one pass \
                    earlier -- the same construction as `N036`. The cost pass has nothing to \
                    compare against, because a `check` promises no bound, and **a `forever` \
                    inside the body is accepted** although a probe that never returns answers \
                    neither `true` nor `false`. M1 reads the block since 2026-08-20, the \
                    effect pass since 2026-08-25; the others do not.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/290 on `E008`. The anchor \
                      `ein_can_fail_rumpf_ist_pure_von_bauart_wegen` measures all THREE \
                      directions -- a writing call falls, a consuming call falls, and a \
                      reading call must still pass. *Without the third the rule would be a \
                      ban on calls, not a contract.*",
        fundstelle: "crates/gabbro-check/src/wirkungen.rs (`probenrumpf`); `N027` in namen.rs",
    },
];

// ===================================================================================
//  Pass 9 -- costs
// ===================================================================================

pub const KOSTEN: &[Satz] = &[
    Satz {
        name: "kosten.summation",
        kennungen: &["K001", "K004", "K005", "K010"],
        aussage: "For every function promising `costs <= E ops`, the statically counted \
                  operation count of its body is <= E. The counting rule is: statements ADD; \
                  a branch counts the MAXIMUM over its arms plus its condition; what follows \
                  an `if` that ALWAYS leaves lies on the other path and is counted once, not \
                  twice. The promise is compared at the SMALLEST assignment of its symbols \
                  (all zero), because a bound must hold exactly there -- `costs <= 40 * n` is \
                  zero at `n = 0`.",
        vorbehalt: "A call counts the DECLARED costs of the callee, never its computed ones. \
                    **At a cycle that makes `costs` on a recursive function an ASSUMPTION \
                    and not a result**, and the pass says so rather than pretending. A body \
                    whose own cost is symbolic (a loop over `n`) counts `Unbekannt`, and the \
                    promise is then not compared at all -- it is refused, not passed. \
                    Non-negativity of every symbol is a PREMISE and is checked (`K005`); \
                    without it there would be no smallest assignment. A product of two \
                    symbols is not readable, and that stands as a refusal rather than as \
                    silence. **And the weakest link of the argument is not recursion:** \
                    `cost(compile-time constant) = 0` is a statement about the EMITTER, and \
                    nothing in this pass checks it -- `emit.rs` carries one code and no \
                    sentence (`messung/K001.md` §5).",
        stand: Satzstand::Argumentiert,
        gemessen_an: "**ARGUED 2026-08-24, `messung/K001.md`** -- and writing it found an \
                      UNDER-count: an `else if` chain counted only its own condition per arm, \
                      so two bodies of identical meaning measured 2 and 6, and `costs <= 2 \
                      ops` passed on the first with zero errors. Corrected, with probe 256 \
                      and the anchor `zweigkette-verliert-praefix`. \
                      beispiele/gift: 3 probes on `K001`, 2 on `K005`. The class is measured \
                      twice in the corpus itself: F1 `revoke` promised 200 ops and cost 16 \
                      452 480, A4 promised 4 096 and cost 831 488 -- both times a HUMAN wrote \
                      the typical case instead of the bound, and this pass caught it.",
        fundstelle: "crates/gabbro-check/src/kosten.rs (`block`, line 463); SPRACHE.md §7",
    },
    Satz {
        name: "kosten.domaenenschranke",
        kennungen: &["K003"],
        aussage: "A `traverse` over a domain costs body x DOMAIN BOUND, and that bound is an \
                  UPPER bound on the cardinality of the domain, read from the declaration -- \
                  a table's `count`, the single field array of a record for `queue`, the \
                  array length in the field type for `elems of`, the `count` of the table \
                  named by an `index into T`, and `node length ^ levels` for `mappings of`. \
                  Where no bound follows from a declaration the pass refuses (`K003`) \
                  instead of guessing.",
        vorbehalt: "**This is the sentence with a MEASURED error in its history, and it is \
                    written so the error stays visible.** For `mappings of` the pass read \
                    `levels x node length` = 2 048 where the domain is the LEAF SET, `node \
                    length ^ levels` = 512^4 = 68 719 476 736 -- **seven orders of \
                    magnitude, carried for three days**, and it was found because the \
                    EMITTER walked into it, not because a test fell. It is corrected, and \
                    the correction bought a consequence rather than defining it away: a \
                    run-time traversal over `mappings of` can hold no cost promise at all. \
                    **And the word is UPPER bound, not cardinality, since 2026-08-31** -- \
                    measuring the four remaining domains is what showed that two of them \
                    were never the cardinality: `descendants of x` visits at most `count`-1 \
                    slots, never `count`, and a `queue` holds at most its array, never \
                    necessarily all of it. *Coarse upwards keeps a cost promise; the 2 048 \
                    was coarse DOWNWARDS, and that is the direction that lies.* What still \
                    stands unchecked: for `queue` the pass takes the record's ONLY field \
                    array to be the queue buffer. Nothing verifies that identification -- it \
                    is a rule, not a proof, and with two arrays the pass refuses instead.",
        stand: Satzstand::Gemessen,
        gemessen_an: "**All five domain bounds carry a probe and a mutation since \
                      2026-08-31, and that is why the state moved -- not a decision, a full \
                      population.** For `mappings of`: the probe named after it in \
                      `rechenwerk.rs` walks levels 1..4 across node lengths 2, 8 and 512 and \
                      reads the number out of the `K001` TEXT per site; the two readings \
                      part at `e = 3, l = 2` (16 against 12), and \
                      `walkschranke-wieder-ein-pfad` puts the historic `e * l` back and is \
                      caught. A second probe pins the overflow edge -- `512^14` fits, `2 x \
                      512^14` does not, and the pass says `K003` instead of wrapping. For \
                      the other four: \
                      `die_vier_uebrigen_domaenenschranken_kommen_aus_ihrer_deklaration` \
                      turns the declared number itself -- `count` at 3/7/13, `elems of` at \
                      2/9/31, `queue` at 3/5/16, `index into T` at 4/6/11 -- and reads the \
                      `K001` text each time. Their mutations are OFF-BY-ONE and not \
                      removals (`count-schranke-um-eins-daneben`, \
                      `elems-schranke-um-eins-daneben`, `queue-schranke-um-eins-daneben`), \
                      because a bound that is GONE was already refused by `K003` and its 2 \
                      poison probes: **the gap was a bound that is present and wrong**, \
                      which is what the 2 048 was. `index-into-tabelle-verloren` is \
                      the exception and is caught TWICE -- by this probe and by the corpus \
                      run, since `beispiele/39` carries the site; the wrong-number half of \
                      that path is covered by `count-schranke-um-eins-daneben`, which it \
                      shares. What is measured is the IMPLEMENTATION against tested cases, \
                      not the rule. See `messung/K001-DOMAENENSCHRANKE.md`.",
        fundstelle: "crates/gabbro-check/src/domaene.rs (line 82), umgebung.rs \
                     (`walkschranken`); MESSUNGEN.md:6307; SPRACHE.md:906",
    },
    Satz {
        name: "kosten.haltezeit",
        kennungen: &["K002", "K006", "K007", "K008", "K009"],
        aussage: "Every `locks` block costs at most what its lock declares as `held`, every \
                  `retry` stays within its `bounded N ops`, and the body of a `forever` stays \
                  within its `per_pass` -- so the latency statement of §9.3 has a branch for \
                  every lock instead of an assertion.",
        vorbehalt: "`per_pass` and `bounded` may depend on INPUTS (`64 + 12 * lenof(msg)`), \
                    and are then not constant-evaluable; in that case the pass is silent AND \
                    COUNTS IT. Until 2026-08-19 this paragraph stood in the module header and \
                    claimed the check without there being a reader for it anywhere in the \
                    checker -- the same class as a proved template no pass establishes.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 2 probes each on `K007` and `K009`, probes on `K002`, \
                      `K006`, `K008`.",
        fundstelle: "crates/gabbro-check/src/kosten.rs; SPRACHE.md §7, §9.3",
    },
];

// ===================================================================================
//  Pass 10 -- Gruppe
// ===================================================================================

pub const GRUPPE: &[Satz] = &[
    Satz {
        name: "gruppe.deklaration",
        kennungen: &["U001", "U002", "U004", "U005", "U007"],
        aussage: "A `group` names at least two DECLARED carriers, every one of them stands \
                  under some lock, no two of its carriers hang under different locks of the \
                  SAME rank, and every `invariant` of the group names at least two of its \
                  carriers.",
        vorbehalt: "~~The rank lookup falls back to 0 for anything the environment cannot \
                    evaluate, and the module context is hard-coded empty -- so two \
                    non-evaluable ranks count as EQUAL and `U005` fires falsely.~~ **Fixed \
                    2026-08-24, and it was WORSE than the entry said:** the empty module path \
                    meant a rank written as a module constant did not resolve AT ALL, so two \
                    locks with different, well-defined ranks both read `0` and a CORRECT \
                    program was refused with a number that stands nowhere in its source. \
                    `H014` stayed silent, because `geteilt.rs` passes the module -- *the only \
                    message the program got was the wrong one.* The rank now resolves in the \
                    declaring module and stays an `Option`; an unknown rank is not a rank, \
                    and two of them are not equal. `U007` can \
                    also fire falsely: its name walker does not know built-ins, so `invariant \
                    : lenof(A) == lenof(B)` names zero carriers. `U001` stays silent about \
                    unknown names -- that is the name pass, not this one.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: one probe on `U007`, and since 2026-08-24 probe 262 \
                      on `U005` -- **the first ever, and writing it is what exposed the false \
                      refusal.** The other half is the test \
                      `ein_modulweiter_rang_loest_auf`, which holds the direction a poison \
                      probe cannot: that a correct program passes. Anchor \
                      `gruppenrang-aus-der-wurzel`. **`U001`, `U002` and `U004` still have NO \
                      probe at all.**",
        fundstelle: "crates/gabbro-check/src/gruppe.rs; MESSUNGEN.md, SWEEP der \
                     Verbindungs-Invarianten (2026-08-16), V4",
    },
    Satz {
        name: "gruppe.sperrabdruck",
        kennungen: &["U003", "U006"],
        aussage: "A function writing two or more carriers of a group holds the FULL lock \
                  imprint of that group at every one of those write sites, and between the \
                  first and the last carrier write there is no `return`, `leave` or `let … \
                  else`. *A lock imprint is a statement about a MOMENT, not about a file: \
                  between two blocks the group is open and every other thread sees it so.*",
        vorbehalt: "**This pass uses no call graph at all** -- a call whose callee writes a \
                    carrier is not a write site for `U003` or `U006`, so the lock imprint \
                    ends at the call boundary, which is exactly what pass 8 stopped doing in \
                    2026-08-15. In the LOUD direction: a `requires Held(X)` precondition does \
                    not count as holding, so a function whose caller must already hold the \
                    lock still falls at `U003` -- the one grossness in this checker that errs \
                    towards false alarms. `U006` uses SOURCE order, not control flow. And a \
                    carrier without a lock contributes nothing to the imprint, so after a \
                    `U002` report `U003` demands nothing for it.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 2 probes on `U003`, 2 on `U006`.",
        fundstelle: "crates/gabbro-check/src/gruppe.rs; templates S16/S17",
    },
    Satz {
        name: "gruppe.invariante",
        kennungen: &[],
        aussage: "The connection invariant of a group holds at the beginning and at the end \
                  of every operation that touches the group.",
        vorbehalt: "**NOT built, and the module header says so: „it checks no invariant\".** \
                    `U007` counts names. The PRESERVATION lives in templates S16/S17 and is \
                    therefore trust surface, not checked surface -- the second S17 obligation \
                    has no checker at all, because the invariant clause it would need does \
                    not exist yet.",
        stand: Satzstand::Vermutet,
        gemessen_an: "Nothing measures it. Named here so the hole has an address.",
        fundstelle: "crates/gabbro-check/src/gruppe.rs (header); schablonen.rs S16/S17",
    },
];

// ===================================================================================
//  Pass 11 -- Phasen
// ===================================================================================

pub const PHASEN: &[Satz] = &[
    Satz {
        name: "m1.schleifeninvariante",
        kennungen: &["M133"],
        aussage: "A loop `invariant` names at least one thing -- a place, a variable, a \
                  declared predicate. `invariant true` is a promise about nothing that reads \
                  like one about something.",
        vorbehalt: "It checks that a NAME is mentioned, not that the invariant is true, not \
                    that it is preserved, and not that it says anything about the loop it \
                    stands at. `invariant x == x` names `x` and passes.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probe on `M133`.",
        fundstelle: "crates/gabbro-check/src/m1.rs; messung/SCHLEIFENINVARIANTE.md §4",
    },
    Satz {
        name: "parser.occupied-einmal",
        kennungen: &["P040"],
        aussage: "A `table` carries at most one `occupied` clause -- the same shape `P022` \
                  holds for `tree` and `P020` for `slot`.",
        vorbehalt: "Purely a shape rule of the parser. That the named field EXISTS and is a \
                    `bool` is `D010`; that a `table` with `ops` carries the clause at all is \
                    `D011`. A second clause in a SECOND table is of course fine.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probe on `P040`.",
        fundstelle: "crates/gabbro-syntax/src/parse.rs; messung/OPS-ERZEUGER.md",
    },
    Satz {
        name: "parser.pub-nur-wo-die-grammatik-es-fuehrt",
        kennungen: &["P041"],
        aussage: "A `pub` stands only at the item kinds whose grammar line carries \
                  `[ \"pub\" ]` -- eleven of them. Where it does not belong it is REFUSED, \
                  not silently dropped, and a program that passed carries no visibility \
                  word the grammar never granted.",
        vorbehalt: "A shape rule of the parser, and nothing else. It says nothing about \
                    whether the visibility is the RIGHT one, nothing about what is actually \
                    reachable from another module, and nothing about the eleven kinds that \
                    do carry it -- there a `pub` is accepted unread.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probe 45 on `P041`.",
        fundstelle: "crates/gabbro-syntax/src/parse.rs; messung/DECKUNGSLUECKE.md",
    },
    Satz {
        name: "bootsatz.schichten",
        kennungen: &["O008", "O009"],
        aussage: "The boot theorem's first two layers: a `raw fn` demands a `linear ghost` \
                  token (`O008`, layer S1 -- it cannot be copied and cannot be restored, so \
                  whoever consumes it ends the boot phase), and no function pointer is made to \
                  a `raw fn` (`O009`, layer S2 -- a pointer into boot code survives the token, \
                  and the jump stands where the call no longer types).",
        vorbehalt: "`O009` sees only `&f` on a name it can resolve to a `raw fn` in the same \
                    program; a pointer that arrives through a foreign module is not covered. \
                    Layer S3 is a sentence of its own (`bootsatz.stilllegung`) and neither of \
                    these two codes says anything about it.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes on `O008` and `O009`.",
        fundstelle: "crates/gabbro-check/src/phasen.rs; SPRACHE.md §12",
    },
    Satz {
        name: "bootsatz.stilllegung",
        kennungen: &["O010", "O011", "O012"],
        aussage: "The boot theorem's third layer as ONE event. A token a `raw fn` demands is \
                  retired by some function (`O010`); the retiring clause and the `effects` \
                  block name the SAME token (`O011`); and a postcondition over `mappings of` \
                  says, negatively, what is gone (`O012`). Consuming the token and unmapping \
                  the space are therefore not two promises one can keep separately.",
        vorbehalt: "**The larger half of layer S3 is NOT proved here and is not provable \
                    here.** `O012` demands a NEGATIVE quantification over `mappings of` and \
                    reads the domain and the negation -- it does not read whether the \
                    predicate really covers the retired space, the same coarseness `maintains` \
                    has. And that an address without a mapping is UNREACHABLE is a statement \
                    about MMU, TLB and speculation which no pass will ever see: it leaves the \
                    checker at `manifest.rs::stilllegungsannahmen`, is booked in `gabbro \
                    annahmen` out of this clause, and carries the probe the clause names. \
                    *A booking into the axiom layer is not a discharge -- it names the duty.* \
                    `O010` also only demands that SOME function retire the token; that exactly \
                    one function consumes it is a statement over bodies, and `beispiele/07` \
                    consumes `BootPhase` twice to this day. And it is program-wide over what \
                    the checker is GIVEN -- `gabbro pruefe` checks per file, so a `raw fn` \
                    whose boot end lives in another module raises a false alarm when checked \
                    alone (`beispiele/gift/300` falls with two codes for that reason). Same \
                    class as `O009`, which also sees only names it can resolve in the same \
                    program.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes on `O010`, `O011` and `O012`; \
                      messung/BOOT-S3.md.",
        fundstelle: "crates/gabbro-check/src/phasen.rs; crates/gabbro-check/src/manifest.rs; \
                     SPRACHE.md §12",
    },
    Satz {
        name: "phasen.ordnung",
        kennungen: &["O001", "O002"],
        aussage: "Every `advances a -> b` names stages the declared order really has, and it \
                  goes FORWARD: the index of the target stage is strictly greater than that \
                  of the source.",
        vorbehalt: "A step whose declaration is faulty is not registered for the flow at all \
                    -- it stops existing for `O003`/`O004`. And if every declaration is \
                    broken the whole rest of the pass stays silent.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes on `O001` and `O002`.",
        fundstelle: "crates/gabbro-check/src/phasen.rs; MESSUNGEN.md «B37»",
    },
    Satz {
        name: "phasen.fluss",
        kennungen: &["O003", "O004", "O006"],
        aussage: "A step meets a token standing on its source stage (`O003`), the body \
                  reaches the stage its own `advances` promises (`O004`), all branches of an \
                  `if`/`match` reach the SAME stage (`O006`), and no step stands in a loop -- \
                  *a step happens once, a loop often.* **A linear value forces a CHAIN but \
                  not WHICH one**: with six boot steps all 720 orders type-check, and M2 sees \
                  only that each token is passed on exactly once.",
        vorbehalt: "~~The statement walker's `_` arm swallows `Return`, so a step in \
                    `return schritt(p);` is neither applied nor checked.~~ **Closed \
                    2026-08-24** -- and it was a PAIR: the same lie written as \
                    `let q = schritt(p); return q;` fell at `O004` while `return schritt(p);` \
                    passed with zero errors. *Two bodies of identical meaning, one caught and \
                    one not, purely by where the call sits* (probe 258). \
                    **`O004` still fires only if the body takes a step at all**, and an \
                    attempt on 2026-08-24 to refuse the empty body was WITHDRAWN: the corpus \
                    refuted it in one run. `stufe_anerkennen` in the virtio driver declares \
                    `advances roh -> anerkannt`, does its work through a helper and hands the \
                    token back -- **a leaf step IS the transition and needs no inner one.** \
                    *The register's earlier framing was too strong; what is missing is not a \
                    rule but a way to tell a leaf step from a body that does nothing.* \
                    The last-reached stage is also not propagated out of branches, so if \
                    every step sits inside a branch the same silence follows. `Zuweisung`, \
                    `Publish`, `Leave`, `Next` and `AwaitLoad` are still swallowed, and only \
                    a DIRECT call counts as a step. With an unknown state the application \
                    returns blind success. **And the flag that was meant to distinguish „a \
                    body without its own `advances` line does not report\" is DEAD CODE** -- \
                    passed through six call sites and never read. The softer reading with a \
                    stage SET is deliberately not built: from the strict one can loosen, from \
                    the soft one never.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes on `O003`, `O004`, `O006`, and since \
                      2026-08-24 probe 258 for the step in a `return` -- the shape that gave \
                      zero errors until then. Anchor: `phasenschritt-im-return-unsichtbar`.",
        fundstelle: "crates/gabbro-check/src/phasen.rs; MESSUNGEN.md «B37»; K11.1",
    },
];

// ===================================================================================
//  Pass 12 -- Sperren
// ===================================================================================

pub const SPERREN: &[Satz] = &[
    Satz {
        name: "sperren.rangordnung",
        kennungen: &["H006", "H012", "H014", "H016"],
        aussage: "Every lock NAME is explained by a declaration (`H016`), every lock carries \
                  a `rank` fixed at compile time (`H014`), and on every path a lock is taken \
                  ONLY while a strictly smaller rank is held (`H006`), through calls as well \
                  (`H012`). Equal rank falls with it: two locks of the same rank have no \
                  order, two holders can take them in two directions, and that is exactly \
                  where a deadlock comes from. **By the classical result this makes a \
                  circular wait impossible, so the program cannot deadlock on declared \
                  locks.** Since 2026-08-21 the sentence survives a LIBRARY BOUNDARY: \
                  `gabbro abi` carries the `lock … rank N` line into the `.gabi`, and \
                  `pruefe --with` recomputes the order over the union.",
        vorbehalt: "**Three conditions the sentence needs and the pass does not fully \
                    supply.** (1) It holds INTERPROCEDURALLY only since 2026-08-19; before \
                    that `locks L2 { … nimmt_l1(); }` with `L1` at rank 1 passed with zero \
                    errors -- a cycle over two functions, which is exactly the shape a real \
                    kernel deadlock has. (2) Over an INCOMPLETE call hull the pass does not \
                    refuse (R16), so a path through an `extern fn` is not covered. (3) The \
                    result covers DECLARED locks only; a wait that is not a `lock` -- a \
                    hardware handshake, a foreign body's internal lock -- is outside it. \
                    **And the fourth, which the ABI made visible on 2026-08-21:** until \
                    `H016` an UNDECLARED lock name was invisible to the whole discipline -- \
                    `H006` and `H012` looked the rank up, found nothing and skipped in \
                    silence, so `effects { locks NIEDA }` plus `locks NIEDA { … }` gave zero \
                    errors. Across a library boundary that was not an edge case but the \
                    normal case. **The ranks are ABSOLUTE numbers, and they do not compose:** \
                    the union of two independently written libraries is ordered by whichever \
                    integers the two authors happened to pick, so a legitimate mixing can be \
                    refused with no repair short of editing the library. *That is a \
                    completeness gap, not a soundness one -- a rank function into the \
                    integers cannot produce a cycle -- and «ABI2» (order instead of rank) is \
                    where it is answered.*",
        stand: Satzstand::Argumentiert,
        gemessen_an: "**ARGUED 2026-08-24, `messung/H006.md`.** The classical argument: a \
                      request for `L` under a held chain `C` needs `r(M) < r(L)` for every \
                      `M in C`, so a wait cycle would give `r(L1) < … < r(Ln) < r(L1)`. \
                      **And the gap I went looking for is closed by CONSTRUCTION:** an \
                      indirect call cannot undercut the order, because `N036` refuses `locks` \
                      at a function pointer type and `M128` refuses storing a lock-taking \
                      function into such a slot. *Measured both ways.* The price stands with \
                      it: **a function that takes a declared lock is not reachable through a \
                      pointer at all** -- dispatch table and lock discipline exclude one \
                      another today. Interprocedural continuation measured at `H012`; poison \
                      probes on `H006`, `H012`, `H014`, `H016`.",
        fundstelle: "crates/gabbro-check/src/geteilt.rs (`rangprobe`, `unerklaerte_sperren`); \
                     crates/gabbro-check/src/abi.rs (`ItemArt::Lock`); SPRACHE.md §9; \
                     messung/ABI.md",
    },
    Satz {
        name: "sperren.geteilt",
        kennungen: &["H001", "H002", "H003", "H004", "H005"],
        aussage: "Holding a lock SHARED means reading the protected places and not writing \
                  them: no write to a `protects` place happens under a shared take (`H001`), \
                  no exclusive take of the same lock happens inside a shared one (`H003`), \
                  every shared take has a `shared held` figure (`H002`), and a shared block \
                  may call `requires Held(L, shared)` but not an exclusive `requires Held(L)` \
                  for the lock it holds shared (`H005`). *Whoever demands MORE than the \
                  caller holds falls; whoever demands less does not.*",
        vorbehalt: "`H005` closes the call boundary only as far as the call hull reaches; \
                    over an incomplete hull it is silent (R16). The rule replaced a coarser \
                    one that forbade ANY `requires Held(…)` call from a shared block, and \
                    the replacement was announced in the refusal text of the coarse version \
                    -- W5.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes on `H001`, `H002`, `H003`, `H005`. **`H004` has \
                      NO probe.**",
        fundstelle: "crates/gabbro-check/src/geteilt.rs; MESSUNGEN.md, Papiertest \
                     CapSpace/CDT (2026-08-14)",
    },
    Satz {
        name: "sperren.schutz",
        kennungen: &["H007", "H008", "H009", "H010", "H011", "H017"],
        aussage: "Every access to a place named in some lock's `protects` happens while that \
                  lock is held (`H007`), every declared `locks` effect is really redeemed by \
                  a take (`H011`), and for RCU-protected places a READ stands inside an \
                  `observes` block (`H009`) while a WRITE stands additionally under a real \
                  lock (`H010`). Since 2026-08-21 every DOMAIN NAME is explained by an `rcu` \
                  declaration (`H017`) -- without it the two RCU halves speak about a domain \
                  that has no `protects` list, and match nothing.",
        vorbehalt: "`H007` counts a DECLARED `locks` effect as held -- so a declaration \
                    covers an access without any take standing anywhere, which is why \
                    `H011` had to be added from the other direction in 2026-08-19. Before \
                    that a unit passed with zero errors while `H007` covered every access \
                    with a line that redeemed nothing. RCU has a grace period, and `H010` is \
                    the stricter of the two rules, so a write under the right lock passes \
                    both while one without falls at `H010`. **And the fourth, the RCU twin \
                    of what `H016` did for locks:** until `H017` an undeclared domain name \
                    was invisible to this whole half -- the RCU walker runs at all only when \
                    the unit declares at least one domain, so `observes NIEDADOM { … }` in a \
                    unit without `rcu` never entered it, and a MISSPELT domain in a unit \
                    with one entered it and matched nothing. *The second is the worse case: \
                    the reader looks protected and is not.*",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 2 probes on `H011`, probes on `H007`, `H009`, `H010`; \
                      `gift/271` and `gift/272` are the two shapes of `H017`. **`H008` has \
                      NO probe.** Hand probe before the `H017` build: \
                      `messung/abi-proben/unbekannte-domaene.gab` passed with 0 errors.",
        fundstelle: "crates/gabbro-check/src/geteilt.rs; K11.2.1",
    },
    Satz {
        name: "sperren.kontext",
        kennungen: &["H013"],
        aussage: "An `entry` point reaches only carriers whose execution context it declares \
                  -- naming `masks IRQ` in an effect list says a function MASKS, not that it \
                  RUNS masked.",
        vorbehalt: "**On today's corpus this rule has ZERO bite.** `gabbro kontexte \
                    beispiele/07` prints it: 4 context roots, 2 with a visible body, 1 place \
                    touched, **0 of them declared in this unit** -- all four roots dispatch \
                    to an `extern fn`. The whole evidence of the rule is poison (Falle 80, \
                    open until the second corpus). The finer half -- `masks IRQ`, `per cpu` \
                    and `nested never` exempting only under `assume ein_kern` -- is carried, \
                    not built.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 2 probes on `H013`. NO corpus site exercises it -- \
                      `gabbro kontexte` prints the zero beside the rule, which is the \
                      difference between „found nothing\" and „looked at nothing\".",
        fundstelle: "crates/gabbro-check/src/geteilt.rs; K11.2.2",
    },
    // --- Die drei Kennungen aus Stufe 6, nachgetragen 2026-08-21 -----------------------
    //
    // **Sie fehlten beim Bau des Registers nicht aus Nachlaessigkeit, sondern weil der
    // Registerbaum acht Commits aelter war.** Der Waechter meldete sie als Ratschenbruch --
    // *und das ist der Beweis, dass der zweite Zahn beisst, bevor jemand ihn braucht.*
    Satz {
        name: "kontexte.traegerkopplung",
        kennungen: &["H101"],
        aussage: "A named carrier `masks IRQ` counts only where the entry context declares \
                  `nested masked`: naming the masking in an effect list says a function \
                  MASKS, not that it RUNS masked, and only the entry knows the state it \
                  hands down.",
        vorbehalt: "**`nested never` does not count, and the distinction is the whole \
                    rule** -- `never` is about re-entry, `masked` about the state. Measured \
                    before the build: 4 carriers `masks X` in the entire corpus, **0** of \
                    them at an entry with `nested masked`, and `nested masked` itself had \
                    ZERO occurrences although the grammar has always carried it. *The \
                    evidence is therefore poison, not corpus* -- same shape as `H013` above. \
                    And the side finding is the sharper one: before this rule, one word in \
                    an effect list bought the exemption from `H013` outright.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/231; 2 mutations, both caught. Hand probe: the same \
                      file with and without `masks IRQ` gave 0 errors against `[H013]`.",
        fundstelle: "crates/gabbro-check/src/kontexte.rs; «B38»",
    },
    Satz {
        name: "geteilt.gnadenfrist",
        kennungen: &["H015"],
        aussage: "An `rcu … reclaims` names the assumption under which no reader still \
                  sees the old object -- the checker demands the assumption, it does not \
                  establish it.",
        vorbehalt: "**This is an ASSUMPTION, not a check, and the statement says so.** \
                    `H011`/`H012` hold the two checkable halves (not inside one\'s own read \
                    section, not without the writer lock); that no reader sees the object \
                    any more is not established by any static pass. *Same rule as `S003`, at \
                    a different construct.* **And the rule hangs on the NAME in the sentence \
                    rather than on a grammar slot** -- the clean form (`rcu … reclaims P \
                    progress G;`, zero new words) is booked and not built, so a misspelt \
                    assumption name is caught by the name pass, not by this one.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/230; 2 mutations, both caught. Hand probe before the \
                      build: `beispiele/43-gegenprobe.gab` carried `rcu … reclaims` without \
                      a grace assumption and passed with 0 errors.",
        fundstelle: "crates/gabbro-check/src/geteilt.rs",
    },
    Satz {
        name: "v1.selbstbezug",
        kennungen: &["M120"],
        aussage: "Every name in an `ensures` resolves to a carrier the caller can see -- \
                  `Self` names none, in either spelling (`Self.field` as a place, \
                  `lenof(Self)` as a type).",
        vorbehalt: "**`Self` was the SMALLER half, and the measurement says so:** five of \
                    six probe units passed with 0 errors before this rule, because five \
                    `PredArt` connectives and `ExprArt::Eingebaut` fell into a silent \
                    catch-all -- *every compound postcondition was unchecked.* And `M111` \
                    fell silent along with them: its condition carries `!namen.is_empty()`, \
                    so a blind branch made the rule above it see „nothing to say\" instead \
                    of „nothing seen\". The `match` no longer carries a catch-all; **that, \
                    not `Self`, is what this statement is worth.**",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/223-225 and 227-229; 6 mutations, all caught.",
        fundstelle: "crates/gabbro-check/src/m1.rs (`sammle_namen_pred`)",
    },
    // --- Stufe 7: der Grunderzeuger ---------------------------------------------------
    //
    // **Die Ratsche hat gebissen, eine Stunde nachdem sie stand.** Sieben neue Kennungen aus
    // dem `reason`-Erzeuger kamen ohne Satz an; der Waechter meldete 52 gegen Marke 45.
    // *Das ist der Zweck des zweiten Zahns, gemessen am zweiten Tag.*
    Satz {
        name: "v1.grundwert",
        kennungen: &["M121", "M122", "M123", "M124", "M125", "M126"],
        aussage: "A reason value that reaches the error exit names a declared case of \
                  EXACTLY the channel the signature declares, and a `match` over it is \
                  complete or the reason says `exhaustive`.",
        vorbehalt: "**The producer was the missing half, not the contract** -- until \
                    2026-08-21 six `-> T or R` signatures stood in the clean corpus, ALL of \
                    them at an `extern fn`, and eight `reason` declarations had their case \
                    names used zero times. *A channel that exists at the declaration and has \
                    no writing form.* The hand probe passed with 0 errors and the emitter \
                    wrote `(void)_grund;` with the finding in it — **the hole stood in the \
                    generated C and in no refusal.**\n\
                    **And `M124` is deliberately STRUCTURAL, not type-wise:** a reason value \
                    slipped silently through seven positions, because 53 `match`es over \
                    `ExprArt` carry a `_` arm while the compiler forced only five. *A rule \
                    that trusted the type checker would have caught five of the seven.*\n\
                    **A FOURTH door since 2026-08-25, and it stayed structural** -- an \
                    argument at a parameter whose DECLARED type is exactly this reason. It \
                    was measured as a FALSE REJECTION of a correct program (W22): \
                    `melde(Status::Ok)` at `melde(st : Status)` fell, and that is the very \
                    position the number in a `reason` line exists for -- *so that a REPORT \
                    can name it.* The door consults the CALLEE's signature, not the type \
                    checker, so no `_` arm can slip past it; `nimm(R::F)` at `nimm(x : u32)` \
                    still falls (`beispiele/gift/293`).\n\
                    **And underneath sat the reason the rule could not be type-wise:** \
                    `reason` was not a `Traegerart`, so `st : Status` resolved to \
                    `Typ::Unbekannt` and every rule looking at such a parameter's type was \
                    silent -- *not by choice, but because its surface was withheld.* Sixth \
                    blind-spot class, third instance.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/48-grund-mit-erzeuger.gab through `pruefe`/`emit`/`cc \
                      -Werror` at -O0 and -O2 and under UBSan; beispiele/gift/232-239; \
                      10 mutations, all caught. The template comes from outside (Regel B): \
                      `FRAGMENTE.md`:269 writes `return Fehler::Buchfuehrung;`.",
        fundstelle: "crates/gabbro-check/src/m1.rs; SYNTAX.md (`reasonval`)",
    },
    Satz {
        name: "namen.typname",
        kennungen: &["N040"],
        aussage: "A type name in a declaration resolves to a declared carrier -- a `type`, \
                  a `table`, a `format`, a `device`, a `walk` bound or a `reason`. A name \
                  that resolves to none of them is refused where it is USED.",
        vorbehalt: "**This is the opposite direction from most of this register: a false \
                    CONFIRMATION.** Measured 2026-08-25 at `messung/fragmente/F01.gab`: \
                    `ptr<normal, rw> Allok` and `ptr<normal, rw+own> PhysAllocator` name \
                    types that exist nowhere; `gabbro pruefe` said *0 errors*, the emitter \
                    wrote `struct Allok;` without a `C001`, and the mistake surfaced at the \
                    FOREIGN compiler as an incompatible pointer. *A checker that confirms \
                    is worse than one that refuses.*\n\
                    **And the first run of the rule paid for itself three times over the \
                    CLEAN corpus** -- `Manifest` (`beispiele/04`), `Bericht` \
                    (`beispiele/14`), `Text` (`beispiele/22`), plus one in `SYNTAX.md`'s own \
                    grammar example. The sharpest is `beispiele/14`: it is DURCHGESTOCHEN, \
                    and it ran green because the C DRIVER wrote `struct Bericht { unsigned \
                    daten; };` itself. *The test program supplied what the Gabbro program \
                    failed to declare.*\n\
                    **What it does NOT do** (W10): it looks at parameters, results and \
                    `static` types. A type named only inside a body -- in a `let` \
                    annotation -- is not yet reached, and the rule says so instead of \
                    looking complete.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/295-zeigerziel-ohne-typ.gab; four real defects found \
                      on the first run over the clean corpus and one in SYNTAX.md:1387.",
        fundstelle: "crates/gabbro-check/src/namen.rs::typname_bekannt",
    },
    Satz {
        name: "namen.kanal_ohne_einloeser",
        kennungen: &["N034"],
        aussage: "A function that declares `or R` has a body that can actually produce a \
                  reason -- a declared error channel with no writing site in its own body is \
                  a promise nobody can keep.",
        vorbehalt: "**This is the rule the whole stage is named after** -- *erst der \
                    Erzeuger, dann der Vertrag.* It bites only where Gabbro SEES the body: \
                    at an `extern fn` the channel stays a pure assumption, and that is \
                    exactly where all six corpus sites stood before this run. *So the rule \
                    is silent on the majority of the surface, and it says so* (W10).",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/237-kanal-ohne-einloeser.gab.",
        fundstelle: "crates/gabbro-check/src/namen.rs",
    },
    // --- The K condition, enforced at last (2026-08-21) --------------------------------
    Satz {
        name: "kbedingung.breaking",
        kennungen: &["D009"],
        aussage: "On a carrier that declares `ops`, EVERY mutation is a generated \
                  operation -- a `breaking` block, which lets an invariant rest, is a write \
                  the generator did not make, and it is refused.",
        vorbehalt: "**This half was collected, counted, PRINTED -- and never refused.** \
                    `k_haelt()` demanded `breaking.is_empty()` from the first day; the pass \
                    reported only `handschrift`. *A program could pass pass 2 without \
                    satisfying the K condition* -- and that condition is not merely a check: \
                    it is the mechanical criterion under which the K/A/W count booked 28 of \
                    73 obligations as by-construction. \
                    **Measured before the build: ZERO `breaking` sites in the clean \
                    corpus**, so no counted number moves -- *a measurement, not a probably-\
                    not*, and this folder does not let the second one through. \
                    **Found by writing down the statement this pass owes, not by a tool:** \
                    thirteen text guardians and 268 mutations did not see it. A tool can \
                    find that a clause has no reader; that a reader reads the WRONG thing \
                    is found only by whoever writes the sentence the rule must hold.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/249-breaking-auf-ops-traeger.gab; one mutation. The \
                      corpus count is zero, so the whole evidence is poison -- and it says \
                      so (W10).",
        fundstelle: "crates/gabbro-check/src/kbedingung.rs; PL.1, finding 1 of 9",
    },
    // --- The subject of `breaking`, resolved at last (2026-08-28) ----------------------
    Satz {
        name: "kbedingung.breaking-nennt-etwas",
        kennungen: &["D013"],
        aussage: "`breaking I { … }` names an invariant this unit really declares -- an \
                  invariant of a `table`, of a `group`, of a `walk`, or a `spec fn`, which \
                  are exactly the four `maintains` accepts. On a name that stands nowhere \
                  the three promises of SPRACHE.md §8.3 have no subject, and the statement \
                  is refused.",
        vorbehalt: "**The rule checks the NAME, not the region.** That the invariant really \
                    rests here, that the block restores it, and that a function with \
                    `requires I` is not callable inside it -- §8.3 promises all three and \
                    NONE of them is checked; `D013` only makes sure they have a subject. \
                    *A `breaking` on the wrong-but-existing invariant still passes.* \
                    **And the deeper gap stays open and is not this rule's:** no pass looks \
                    at an `invariant … runs online` at a statement boundary at all. Measured \
                    through the unchanged checker (W24, 2026-08-28): the two assignments of \
                    `FRAGMENTE.md`:690-691 pass with ZERO errors, with `breaking` and \
                    without it. So nothing forces the region to be named -- what this rule \
                    buys is that a named region names something. \
                    **The measured base is thin and it says so** (W10/W23): before this run \
                    the clean corpus had ZERO `breaking` sites and the poison corpus one. \
                    `beispiele/53-zwei-orte.gab` is the first clean one, written for this \
                    rule -- so it does not count as demand, only as a site.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/351-breaking-nennt-nichts.gab; one mutation \
                      (`breaking-darf-ins-leere-nennen`). The clean side is \
                      beispiele/53-zwei-orte.gab.",
        fundstelle: "crates/gabbro-check/src/kbedingung.rs; messung/ZWEI-ORTE.md",
    },
    // --- «B18»: die Registerklasse je Phase (2026-08-28, Bahn A) ----------------------
    Satz {
        name: "m3.phasenklasse",
        kennungen: &["R009"],
        aussage: "A `device` register may carry a class PER PHASE -- `class rw in setup, r \
                  in live` -- where the stages are those of a declared `linear ghost type \
                  … order { … }`. The list names every stage of that order exactly once, \
                  and the order it belongs to is unambiguous. At an access the class of the \
                  stage the mark stands on decides (`R005`/`R006`); **where no mark of that \
                  order is in scope, what holds is what EVERY stage permits.**",
        vorbehalt: "**It says nothing about the phase of the HARDWARE.** The stage is the \
                    DRIVER's; a hostile or crashed device leaves `live` on its own and no \
                    line here holds it -- making a fact out of the mark would be the «B33» \
                    error again. **It checks no access that goes past the device handle:** \
                    an `asm` block or a raw pointer on the same address is invisible, as it \
                    already is for `R005`/`R006` (W9). **The stage is only as precise as \
                    the body walk:** a function without `advances` that carries a mark has \
                    an UNDETERMINED stage and falls under the intersection, not under a \
                    guessed stage -- and across a call only the signature carries. **A loop \
                    body that also holds a phase step is not checked for register classes** \
                    -- it is already refused whole (`O006`), and a second message at the \
                    same line would be noise. **And it lowers nothing:** `class` was never \
                    a lowering, and the phase is not visible to the emitter. Fields of a \
                    phase-classed register may not carry their own class: «B23» stands per \
                    field, «B18» per phase, and the two do not compose today.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/401-registerklasse-ohne-marke.gab (`R006`, no mark in \
                      scope -- the load-bearing site, measured at 0 errors on 2026-08-26), \
                      402-registerklasse-nach-dem-schritt.gab (`R006`, stage `live` after \
                      the step), 403-phasenklasse-schweigt-ueber-stufe.gab and \
                      404-phasenstufe-gibt-es-nicht.gab (`R009`). The clean side is \
                      beispiele/02-geraet.gab, which writes the form for the first time -- \
                      so it is a SITE and not demand (W23).",
        fundstelle: "crates/gabbro-check/src/m3.rs::phasendeklarationen, ::phasenzugriff; \
                     crates/gabbro-check/src/phasen.rs::registerzugriffe; \
                     messung/PHASENKLASSE.md",
    },
    // --- «B26»: the device promise that lowers (2026-08-28, lane A) ------------------
    Satz {
        name: "m3.geraeteversprechen",
        kennungen: &["R010", "R011"],
        aussage: "`requires <pred> else <R>::<case>` at a device register makes the READ of \
                  that register FALLIBLE. The `else` names a reason case this unit declares \
                  (`R010`), and a plain read of such a register is refused -- it must stand \
                  in a `let … else` (`R011`). The emitter lowers it to exactly ONE volatile \
                  read whose condition is checked on the BINDING, not on a second access.",
        vorbehalt: "**It does not check that the DEVICE keeps its word -- it checks that the \
                    program looks.** Assuming the condition instead would be the «B33» error \
                    one level up: the register is volatile and a hostile device may report \
                    anything. **`e` carries no type here:** in the `else` branch of a \
                    fallible register read `return e;` falls at `M119` -- the type binding \
                    for `fehlername` hangs on the callee's signature and lives in `m1.rs`, \
                    which this lane does not touch. *The loss is small and named: a register \
                    declares exactly ONE reason, so `return R::C;` says the same.* **The \
                    read sites are those of `R005`/`R006` plus the arguments of a bare call** \
                    -- a predicate in the caller's own `requires`, a `narrow` place and a \
                    loop bound are not among them. **And `requires` WITHOUT `else` is \
                    untouched:** it stays a counted obligation, and `gabbro pflichten` keeps \
                    printing it as `D`. The third `let … else` source, an option-valued \
                    place, keeps its `C001` refusal -- `None` carries no reason, which is a \
                    different question with a different answer.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/405-geraeteversprechen-blank-gelesen.gab (`R011` -- the \
                      load-bearing site, measured at 0 errors before the build) and \
                      406-falsifikator-nennt-nichts.gab (`R010`). The clean side is \
                      beispiele/44-register-einmal-lesen.gab, «B33»'s own file, and it goes \
                      through the C compiler -- so the LOWERING is measured and not only the \
                      refusal. Two mutations.",
        fundstelle: "crates/gabbro-check/src/m3.rs::geraeteversprechen, ::fehlbare_lesungen; \
                     crates/gabbro-check/src/emit.rs::fehlbare_lesung; \
                     messung/GERAETEVERSPRECHEN.md",
    },
];

// ===================================================================================
//  Die Auswertung -- der zweite Zahn
// ===================================================================================

/// Alle Saetze des Registers, in Passreihenfolge, mit dem Namen ihres Passes.
pub fn alle() -> Vec<(&'static str, &'static Satz)> {
    let mut aus = Vec::new();
    for p in crate::passliste() {
        for s in p.saetze {
            aus.push((p.name, s));
        }
    }
    aus
}

/// **Jede Kennung, die ein Satz beansprucht.**
pub fn beansprucht() -> std::collections::BTreeSet<&'static str> {
    let mut aus = std::collections::BTreeSet::new();
    for (_, s) in alle() {
        for k in s.kennungen {
            aus.insert(*k);
        }
    }
    aus
}

/// **Der zweite Zahn: die Kennungen aus `vorhanden`, zu denen KEIN Satz gehoert.**
///
/// Der Rufer reicht die Kennungen herein, statt sie hier zu erheben -- der Pruefer kennt
/// seine eigenen Zeichenketten zur Laufzeit nicht. `instrumente/pruefe-saetze.py` liest sie
/// aus den Quellen, mit demselben Ausdruck wie `pruefe-kennungen.py`.
pub fn ohne_satz<'a>(vorhanden: &[&'a str]) -> Vec<&'a str> {
    let b = beansprucht();
    vorhanden.iter().filter(|k| !b.contains(*k)).copied().collect()
}

/// **Der Bericht.** Englisch, wie jeder `gabbro`-Bericht.
pub fn zeige(je_satz: bool) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    let saetze = alle();
    let (mut verm, mut gem, mut arg, mut bew) = (0usize, 0usize, 0usize, 0usize);
    let mut mit_kennung = 0usize;
    for (_, z) in &saetze {
        match z.stand {
            Satzstand::Vermutet => verm += 1,
            Satzstand::Gemessen => gem += 1,
            Satzstand::Argumentiert => arg += 1,
            Satzstand::Bewiesen => bew += 1,
        }
        mit_kennung += z.kennungen.len();
    }
    let _ = writeln!(
        s,
        "\n-- THE PASS REGISTER -- what each pass OWES as a sentence.\n\
         --   A sentence says what is TRUE of a program that passed without a refusal.\n\
         --   `gabbro paesse --je-satz` prints each one in full."
    );
    let _ = writeln!(
        s,
        "--\n\
         --   READ THIS FIRST: a HINT is not a refusal. `E003`, `E009`, `V003`, `S007` and\n\
         --   `N026` are hints, so a program that passes „without a refusal\" may contain\n\
         --   functions whose frame or pairing statement the checker declared UNDECIDABLE.\n\
         --   Every sentence below is weaker by exactly that much.\n--"
    );
    let mut letzter = "";
    for (pass, z) in &saetze {
        if *pass != letzter {
            let _ = writeln!(s, "-- {pass}");
            letzter = pass;
        }
        if je_satz {
            let _ = writeln!(s, "--   [{}] {}", z.stand.text(), z.name);
            let _ = writeln!(s, "--     HOLDS:   {}", z.aussage);
            let _ = writeln!(s, "--     BUT NOT: {}", z.vorbehalt);
            let _ = writeln!(s, "--     measured by: {}", z.gemessen_an);
            let _ = writeln!(s, "--     at: {}", z.fundstelle);
            let _ = writeln!(
                s,
                "--     codes: {}",
                if z.kennungen.is_empty() {
                    "NONE -- this rule widens what passes, or is not built".to_string()
                } else {
                    z.kennungen.join(" ")
                }
            );
        } else {
            let _ = writeln!(
                s,
                "--   [{:<11}] {:<28} {:>2} code(s)",
                z.stand.text(),
                z.name,
                z.kennungen.len()
            );
        }
    }
    let _ = writeln!(
        s,
        "\n--   SENTENCES: {} over {} passes -- {gem} measured, {arg} ARGUED, \
         {verm} CONJECTURED, {bew} proved.\n\
         --   They claim {mit_kennung} diagnostic codes between them.\n\
         --   ARGUED means a soundness argument is WRITTEN DOWN (`messung/K001.md`),\n\
         --   human-reviewed and not machine-checked. It is not a proof.",
        saetze.len(),
        crate::passliste().len()
    );
    let _ = writeln!(
        s,
        "--\n\
         --   AND WHAT THAT NUMBER DOES NOT SAY: a written sentence is not a proved one.\n\
         --   `measured` means a poison probe falls or a mutation is caught -- it measures\n\
         --   the IMPLEMENTATION on checked cases, never the RULE, and never all cases.\n\
         --   {bew} of {} have been to Isabelle. That is the number PL.2 is about."
        , saetze.len()
    );
    s
}
