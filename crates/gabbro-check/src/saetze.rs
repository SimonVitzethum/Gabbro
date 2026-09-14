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
        kennungen: &["N001", "N002", "N003", "N009", "N010", "N017", "N055"],
        aussage: "Within one scope no name is declared twice -- items, the fixed set of \
                  construct bodies, AND the scopes of a function: its parameter list and \
                  every block of its body. No two `reason` cases carry the same number, no \
                  two register fields sit on the same bits, no two `reg` overlap in offset, \
                  and no register stands in `preserves` and `clobbers` at once. A `state`
                  transition names its carrier or checks: without a `requires` and
                  without a place a declared carrier holds it falls at `N055`. The pass \
                  checks DUPLICATION, not resolution.",
        vorbehalt: "**Two holes; the third fell on 2026-08-31.** (1) A `when` item switches \
                    the duplicate check off entirely -- two identically named items with \
                    `when` never fall (`arch` in contrast keys correctly per target). \
                    (2) `N009`/`N010` compare only what is a NUMBER LITERAL, and `N009` only \
                    within one level -- bank against main level never. \
                    **What the function scopes deliberately do NOT refuse is a covering in a \
                    NESTED block**: C accepts it, `19-let-verdeckt.gab` has held it as a \
                    legal program since 2026-08-14, and `m1.rs` carries the block scope that \
                    gives it meaning. That form carries a defect of a DIFFERENT pass -- \
                    `kosten.rs` and `domaene.rs` build `lokal` from the parameters alone and \
                    therefore read the covered binding, accepting a `costs` promise the \
                    emitted loop violates. Measured and NOT built \
                    (`messung/proben/probe-domaenenschatten.gab`).",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 5 probes on `N001` (`432` covers a parameter in the \
                      body's own scope -- the form `cc` refuses), probes on `N002`-`N003` \
                      and `N009`-`N010`, probe `668` on `N055` (a `state` transition over \
                      nothing). Counter-direction 2026-08-31: 480 `.gab` files, \
                      118 error-free before and 118 after.",
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
                  `let`/`return`/comparison/argument/assignment, and a `syscall`'s \
                  assumption -- names something this unit declares, and names it in the \
                  form the clause requires.",
        vorbehalt: "**`N028`/`N029` carry a KEY ASYMMETRY that is a plain bug** (found \
                    2026-08-21 while writing this sentence): the map is filled under the \
                    SHORT name and calls are looked up under the FULL path, so `m::f()` \
                    never matches -- `N029` stays silent and `N028` fires FALSELY although \
                    `f` declares its `or R`. **`N030` was silent for anything but a bare \
                    unsuffixed name until 2026-09-03**, which is the one position a record \
                    holding two axes never has; it now walks `.f`/`->f` from the binding's \
                    declared record and gives up at an `[i]` (W10). `N022` sees comparisons only \
                    directly under binary operators -- a parenthesis hides one completely. \
                    `N026` is a HINT, not a refusal. And `N015` deliberately does not exist: \
                    where `counterprobe … expects <ident>` declares its ident is not written \
                    down anywhere, and that is a finding about the SPECIFICATION.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 5 probes on `N030` (`669`/`670` hold the FIELD, read \
                      and written), 2 each on `N027` and `N031`, `813` on a `syscall` \
                      naming an undeclared assumption (`N004`), and single probes on 12 \
                      further codes of this group.",
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
    // --- 2026-09-04: a falsifier that resolves must be able to go red ---------------------
    //
    // **The rule that was NOT built is the load-bearing half of this sentence.** `falsifier`
    // deliberately does not have to resolve: a probe is a C program in `sonden/`, decided
    // 2026-08-19 and repeated in `sonden/README.md`. What IS decidable is the case where the
    // name resolves anyway -- and then to something that has no way to say "refuted".
    Satz {
        name: "namen.sondenausgang",
        kennungen: &["N056"],
        aussage: "A `falsifier` (or `retires … falsifier`) whose name RESOLVES to a \
                  function declared in this unit names one that can go red: either it \
                  answers `-> bool`, or it is a `-> never` watchdog standing at the \
                  `on_exceeded` of a loop (SYNTAX.md §8.3). A function returning a value, \
                  a function returning nothing, and a diverging function that guards no \
                  loop are all refused -- none of them has a channel on which a refutation \
                  could arrive.",
        vorbehalt: "**The rule does NOT require the name to resolve at all, and that is a \
                    decision and not a gap** -- a probe does not stand in Gabbro because \
                    it RUNS (decided 2026-08-19). 89 of the corpus's 98 `falsifier` \
                    clauses resolve to nothing and are correct; a rule demanding \
                    resolution would refuse the whole hardware corpus. Coverage for those \
                    lives one layer out, at `manifest::gedeckt`, which strikes a name \
                    whose probe stands as no program. **And that a `-> bool` probe ever \
                    returns `false` is NOT decidable here** -- the body is outside the \
                    language. `instrumente/pruefe-sonden.sh` measures that, by running the \
                    program against the `0/1/77` contract; this pass only guarantees the \
                    verdict has somewhere to come from. *A declaration that CAN fall is \
                    not one that DOES.*",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured before the build (2026-09-04, 647 `.gab`): **98 `falsifier` \
                      clauses (94 at `assume`/`axiom`, 4 at `retires`), 59 distinct probe \
                      names, 89 resolving to nothing, 4 \
                      resolving in-file -- and all 4 already satisfy the rule**, so the \
                      corpus sweep before and after is byte-identical in every exit code \
                      (642 files, 456 red, 0 changed). The pre-run is recorded: `assume a \
                      \"…\" falsifier gibt_es_nicht;` gave `0 errors, 0 hints`, exit=0. \
                      Probe `beispiele/gift/677` is the value arm; the `-> never` arm and \
                      all three counter-directions stand in `paesse.rs` \
                      (`ein_falsifikator_muss_rot_werden_koennen`). **3 mutations, one per \
                      arm plus the counter-direction**, all caught. *The effects check -- \
                      an assumption about `writes tlb` whose probe declares `pure` -- is \
                      decidable and was NOT built: of 14 `axiom … falsifier` clauses, 0 \
                      have a declared probe, so its population is EMPTY.*",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md §8.3, §12; sonden/README.md",
    },
    // --- lane E1, 2026-09-12: the unresolved library call ---------------------------
    //
    // **The rule that refuses what resolves nowhere -- narrowed by lane E2.**
    // `@library#function` reads as a run-time call whose region the reader
    // captures without interpreting; where `library` names no used module
    // or the module declares no such `library fn`, there is no declaration,
    // no contract and no payload type to hold the call against. The sentence
    // is therefore not a claim about the call but about the refusal: every
    // such call falls here, in both positions. A call that DOES resolve
    // falls under `N069` instead (`namen.bibliothek_ruf` below).
    Satz {
        name: "namen.library_call",
        kennungen: &["N057"],
        aussage: "Every library call `@library#function ( args ) { region }` that \
                  resolves nowhere is refused -- once per call, in statement \
                  and in binding position, naming whether the library or the \
                  function failed. A form the checker cannot judge is never \
                  silently accepted and never crashed on.",
        vorbehalt: "**The refusal is the whole rule, and that is a decision and not \
                    a gap** -- the arguments ARE judged: they are ordinary \
                    expressions, and every pass reads them through the shared \
                    walkers. Lane E2 narrowed the code to the unresolved call; \
                    the resolved one is `N069`.",
        stand: Satzstand::Gemessen,
        gemessen_an: "`beispiele/gift/802` (unbalanced region, `P001`), `/803` \
                      (missing `#`, `P001`), `/804` (empty library name, `P003`), \
                      `/805` (unresolved, `N057`, in both positions); \
                      `beispiele/gift/821` (unknown library), `/822` (unknown \
                      function); counter-direction in `paesse.rs` \
                      (`library_call_*`, `bibliothek_*`).",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md §7; PLAN-ERWEITUNG.md §6",
    },
    // --- lane E2, 2026-09-12: the checked library call --------------------------------
    //
    // **The structure lane of PLAN-ERWEITUNG.md §6.** A library module declares
    // a run-time function with a contract and a payload type (`library fn`
    // with `payload <table>`, SYNTAX.md §7.1); the call `@lib#f` resolves
    // like any name and is checked like any call -- arguments (`M143` and
    // per-argument shape and range), effects through the call graph
    // (`E008`), costs against the declaration. Four refusals hold the
    // four things no ordinary check can: the still-untranslated call
    // (`N069`, naming the translator lane E3 declares), a foreign body in
    // the hull (`N059`, §0c), a payload naming no table (`N060`), and a
    // direct call bypassing the region (`N061`). The translator linkage
    // itself is `namen.uebersetzer_*` below (lane E3).
    Satz {
        name: "namen.bibliothek_ruf",
        kennungen: &["N069"],
        aussage: "Every resolved library call OUTSIDE the first translation \
                  cut is refused with the translation diagnostic -- once per \
                  call, in both positions, naming the translator that WOULD \
                  run the region. Its arguments, effects, error channel and \
                  costs are checked exactly like an ordinary call's; only the \
                  region is still not interpreted, so until a translator RUNS \
                  it the call cannot pass. Calls the first cut translates \
                  (exact-length integer regions, `namen.ubersetzung_lauf`) \
                  never reach this code.",
        vorbehalt: "The refusal is load-bearing, not provisional: a checked call \
                    without a payload would be a silent acceptance of a region \
                    nobody compiled. `beispiele/gift/820` carries a declaration, \
                    its translator and two calls and falls with nothing but \
                    this code. Since lane E7 the refusal's span sits INSIDE \
                    the region -- at its first token, carried back through \
                    the region span map (`regionkarte.rs`) -- never at the \
                    call around it.",
        stand: Satzstand::Gemessen,
        gemessen_an: "`beispiele/gift/820` (declaration plus translator plus \
                      calls, `N069` only); `/823` (wrong argument type beside \
                      it); `beispiele/gift/870` (the E3-numbered positive); \
                      `/875` and `/876` (multi-line regions, span at the first \
                      region token, in statement and in binding position); \
                      counter-direction in `paesse.rs` (`bibliothek_*`, \
                      `translator_declared_call_names_it_n069`, \
                      `library_n069_points_*`, \
                      `translation_non_integer_region_stays_n069`).",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md §7.1; PLAN-ERWEITUNG.md §6",
    },
    Satz {
        name: "namen.bibliothek_huelle",
        kennungen: &["N059"],
        aussage: "No `library fn` reaches a foreign body: the transitive call \
                  hull of every declared library function holds no `extern`, \
                  `raw`, `prim` or `asm` -- including itself.",
        vorbehalt: "Structure, not prose comparison (PLAN-ERWEITUNG.md §0c): \
                    contradictory hardware assumptions would make every proof \
                    over the combined program vacuous. Calls through a place \
                    have no static callee and stay guarded by `E009` instead.",
        stand: Satzstand::Gemessen,
        gemessen_an: "`beispiele/gift/824` (library body calling an `extern fn`); \
                      counter-direction in `paesse.rs` (`bibliothek_*`).",
        fundstelle: "crates/gabbro-check/src/namen.rs; PLAN-ERWEITUNG.md §0c",
    },
    Satz {
        name: "namen.bibliothek_nutzlast",
        kennungen: &["N060"],
        aussage: "The `payload` clause of every `library fn` names a declared \
                  table -- a tree table is a table, anything else is not a \
                  payload.",
        vorbehalt: "Resolved from the declaring module outward over the same \
                    candidate order every other name uses; a missing clause is \
                    not this rule but the reader's (`P043`).",
        stand: Satzstand::Gemessen,
        gemessen_an: "`beispiele/gift/825` (payload naming no table); \
                      `beispiele/gift/826` (missing clause, `P043`); \
                      counter-direction in `paesse.rs` (`bibliothek_*`).",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md §7.1; PLAN-ERWEITUNG.md §0b",
    },
    Satz {
        name: "namen.bibliothek_direktruf",
        kennungen: &["N061"],
        aussage: "No direct call names a `library fn`: without a region there \
                  is no payload, so the call would silently bypass the \
                  mechanism the declaration stands for. The function is called \
                  through `@lib#f` with a region.",
        vorbehalt: "Fires on the call FORM, in statement, binding, `let … else` \
                    and contract position; constructors, conversions and calls \
                    through a place never resolve to a declared function and \
                    stay silent here.",
        stand: Satzstand::Gemessen,
        gemessen_an: "counter-direction in `paesse.rs` (`bibliothek_direktruf_*`).",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md §7.1",
    },
    // --- lane E5, 2026-09-13: the translation stage, first cut ------------------------
    //
    // **The structure lane of PLAN-ERWEITUNG.md §6 that runs translators.**
    // An exact-length integer region fills the payload table row by row
    // through the identity translator; the call passes one argument short,
    // the region filling the payload pointer, and the emitter hands the
    // function a `static const` table. Five refusals hold the five things
    // no ordinary check can: the arity against the payload count (`N230`),
    // a translator body outside the runnable fragment (`N231`), a value
    // outside the field range (`N232`, at the offending region token), a
    // declaration the first cut cannot carry (`N233`), and a contract over
    // the payload parameter no source value could discharge (`N234`). The
    // translator itself is never verified: the certificate checks the
    // payload's TYPING, every entry in its field range, by `decide`.
    Satz {
        name: "namen.ubersetzung_lauf",
        kennungen: &["N230", "N231", "N232", "N233", "N234"],
        aussage: "Every resolved library call with an exact-length integer \
                  region is translated: the region becomes the payload row by \
                  row through the identity translator, the call passes one \
                  argument short with the region filling the payload pointer, \
                  and the emitter passes the payload as a `static const` \
                  table argument. A mistranslated call is refused in exactly \
                  one of the five codes, at the offending site -- the region \
                  token for arity and range, the declaration for the rest.",
        vorbehalt: "First cut, and narrow in four named directions: \
                    non-integer regions stay `N069` (the region is captured, \
                    not interpreted, exactly as before); payload tables with \
                    anything but one integer field and a constant count are \
                    `N233`; translators between two different tables have no \
                    runnable body and are `N231`; the Lean program-logic \
                    channel still maps every library call to \
                    `CallStatement`. One fault keeps one refusal: declaration \
                    defects fire once per library function, call defects once \
                    per call.",
        stand: Satzstand::Gemessen,
        gemessen_an: "`beispiele/106-summe-uebersetzt` (accepted, emits, the \
                      emission check runs it); `/107` (two calls, both \
                      positions, two payloads); `beispiele/gift/905` \
                      (`N230`, long region, span at the homeless token); \
                      `/906` (`N231`, non-identity body); `/907` (`N232`, \
                      span at the offending token); `/908` (`N233`, no \
                      payload parameter); `/909` (`N234`, contract over the \
                      payload parameter); counter-direction in `paesse.rs` \
                      (`translation_*`) and `tests/uebersetzung.rs` \
                      (acceptance, lowering, certificate mirror).",
        fundstelle: "crates/gabbro-check/src/uebersetzung.rs; SYNTAX.md §7.3; PLAN-ERWEITUNG.md §6",
    },
    // --- lane E6, 2026-09-12: the hardware profile and library requirements ------------
    //
    // **The checker half of `PLAN-ERWEITUNG.md` §0c.** The main program
    // declares ONE hardware profile (`profile { … }`, SYNTAX.md §12.2); a
    // library REQUIRES profile entries by reference (`requires profile
    // { … }`). Five refusals hold the five things no ordinary check can:
    // the key conflict (`N215`, the `einigung` half of `Profil.gut`), the
    // same-named assumption with different content (`N216`, the
    // `namensGleichheit` half), the requirement outside the profile
    // (`N217`, linking as a subset check), the profile against the
    // platform (`N218`: `fp_contract` other than `off` contradicts the
    // float prelude binding `-ffp-contract=off`, an `arch` beside every
    // declared machine), and the profile structure (`N219`: one profile
    // per program, every reference resolving).
    Satz {
        name: "namen.profil_schluessel",
        kennungen: &["N215"],
        aussage: "Two keyed entries with one key and different values are \
                  refused -- once per conflicting key and block, in `profile` \
                  and in `requires profile` alike. Duplicates with one value \
                  are silent: a set holds them once.",
        vorbehalt: "The `einigung` half of `Profil.gut` \
                    (`grammatik/Grammatik/Profil.lean`): contradictory modes \
                    make every proof over the combined program vacuous, so the \
                    refusal stands at the profile itself, never at the use.",
        stand: Satzstand::Gemessen,
        gemessen_an: "`beispiele/gift/890` (conflicting keyed entries); \
                      counter-direction in `paesse.rs` (`profil_*`).",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md §12.2; PLAN-ERWEITUNG.md §0c",
    },
    Satz {
        name: "namen.profil_namensgleichheit",
        kennungen: &["N216"],
        aussage: "A same-named assumption with different content is refused: \
                  where an `assume <name>` reference in a profile block meets \
                  two declarations under that name with different statements, \
                  the reference is ambiguous and falls.",
        vorbehalt: "The `namensGleichheit` half of `Profil.gut`: the profile \
                    holds the NAME, so two statements under it are two \
                    assumptions wearing one name. One declaration under the \
                    name -- however often referenced -- stays silent.",
        stand: Satzstand::Gemessen,
        gemessen_an: "`beispiele/gift/891` (same name, different statements); \
                      counter-direction in `paesse.rs` (`profil_*`).",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md §12.2; PLAN-ERWEITUNG.md §0c",
    },
    Satz {
        name: "namen.profil_bindung",
        kennungen: &["N217"],
        aussage: "Linking refuses a library whose requirements are not in the \
                  profile -- once per uncovered requirement. A keyed \
                  requirement needs the key with the value; an `assume` \
                  requirement needs a profile reference to a declaration with \
                  the same name and content (`Profil.bindet`).",
        vorbehalt: "Unit-wide: the unit IS the program, so a requirement in an \
                    unused module is still a requirement. A requirement the \
                    reference cannot resolve is not this rule but `N219`.",
        stand: Satzstand::Gemessen,
        gemessen_an: "`beispiele/gift/892` (requirement outside the profile); \
                      the positive direction in `beispiele/100` (library \
                      requiring a subset, clean) and in `paesse.rs` \
                      (`profil_*`).",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md §12.2; PLAN-ERWEITUNG.md §0c",
    },
    Satz {
        name: "namen.profil_plattform",
        kennungen: &["N218"],
        aussage: "The profile is held against the platform: `fp_contract` \
                  other than `off` contradicts the float prelude, which binds \
                  `-ffp-contract=off` for every compiler (`PLAN-BITS.md` §5); \
                  an `arch` the unit never declares contradicts the declared \
                  machines. Without declared machines nothing is refused.",
        vorbehalt: "The `arch` leg mirrors the `R16` shape of `annahme_arch`: \
                    a unit with no machine named constrains no machine. The \
                    `fp_contract` leg has no such exit -- the prelude binds \
                    the flag unconditionally.",
        stand: Satzstand::Gemessen,
        gemessen_an: "`beispiele/gift/893` (`fp_contract fast` against the \
                      prelude); counter-direction in `paesse.rs` (`profil_*`).",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md §12.2; PLAN-BITS.md §5",
    },
    Satz {
        name: "namen.profil_gestalt",
        kennungen: &["N219"],
        aussage: "One hardware profile per program: the second `profile` \
                  block falls, never silently merged. An `assume <name>` \
                  reference resolving to no declared assumption falls beside \
                  it -- a link against air.",
        vorbehalt: "Two arms, one code, like `N065`'s three: both refuse the \
                    profile's FORM, and neither judges its content. An empty \
                    `profile {}` passes here -- vacuous, not contradictory.",
        stand: Satzstand::Gemessen,
        gemessen_an: "`beispiele/gift/894` (second profile block); \
                      counter-direction in `paesse.rs` (`profil_*`).",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md §12.2; PLAN-ERWEITUNG.md §0c",
    },
    // --- lane E3, 2026-09-12: the translator declaration ---------------------------------
    //
    // **The DECLARATION side of translators (PLAN-ERWEITUNG.md §6, lane E3).**
    // A library declares, per run-time function, the translator from the
    // region AST to the payload (`translator … for …`, SYNTAX.md §7.2) --
    // a total, effect-free Gabbro function whose body every pass checks
    // like any function body. Running it needs the compile-time evaluator
    // (lane E5); only the declaration and the typing are built now. Five
    // new refusals hold the five things only the linkage can fail.
    Satz {
        name: "namen.uebersetzer_einzigkeit",
        kennungen: &["N200", "N201"],
        aussage: "Every `library fn` with a payload type has exactly one \
                  translator in its module: none is refused on the function, \
                  a second one -- and a translator naming no library function \
                  at all -- on the translator.",
        vorbehalt: "The first declaration by position serves the function; a \
                    function without a payload clause (`P043`) owes no \
                    translator -- one refusal per defect.",
        stand: Satzstand::Gemessen,
        gemessen_an: "`beispiele/gift/871` (missing, `N200`); counter-direction \
                      in `paesse.rs` (`translator_missing_n200`, \
                      `translator_second_n201`, `translator_dangling_n201`).",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md §7.2; PLAN-ERWEITUNG.md §6",
    },
    Satz {
        name: "namen.uebersetzer_signatur",
        kennungen: &["N202", "N203", "N204"],
        aussage: "A serving translator is `effects { pure }` with a \
                  `decreases` clause and answers the served function's \
                  payload table: anything else -- including a missing clause \
                  or a missing result -- is refused on the translator.",
        vorbehalt: "A payload naming no table itself (`N060` beside it) pins \
                    no `N204`: one refusal per defect. The body is ordinary \
                    Gabbro for every other pass; a translator hull reaching a \
                    foreign body falls under `N059` like a library body.",
        stand: Satzstand::Gemessen,
        gemessen_an: "`beispiele/gift/872` (effects, `N202`); `/873` (no \
                      decreases, `N203`); `/874` (foreign result, `N204`); \
                      counter-direction in `paesse.rs` (`translator_effects_n202`, \
                      `translator_no_effects_n202`, `translator_no_decreases_n203`, \
                      `translator_result_mismatch_n204`, \
                      `translator_foreign_hull_n059`, \
                      `translator_without_body_p044`).",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md §7.2; PLAN-ERWEITUNG.md §6",
    },
    // --- «B40», 2026-08-31: `arch` at an assumption --------------------------------------
    //
    // **What bought the clause was a CONJUNCTION, not a missing keyword.** `dma_kohaerent`
    // carried two independent claims under one name and one falsifier, and the second is
    // false on AArch64 -- while that falsifier runs on x86 and passes.
    Satz {
        name: "namen.annahmemaschine",
        kennungen: &["A005"],
        aussage: "An `assume … arch A` names a machine this unit declares somewhere -- \
                  at an `entry`, an `entrust`, a `boot` or an `asm` body. A `syscall` \
                  names its machine the same way (`arch` after `abi`). An assumption \
                  -- or a syscall -- that can never be in force here does not travel in the artefact's \
                  assumption set as though it could.",
        vorbehalt: "**The rule reads the `arch`, never the TEXT.** Whether an assumption \
                    carries two claims under one name is a human judgement; a guard \
                    against conjunctions in prose would be a text guard, not a pass. And \
                    a unit that declares NO `arch` anywhere is not refused (R16) -- it \
                    does not say which machine it runs on, so a refusal would be a \
                    guess. *That silence covers `beispiele/02` itself, the file the rule \
                    came from.*",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured before the build: `arch` existed at `entry`, `entrust`, \
                      `boot` and `asm` (27 `x86_64`, 2 `aarch64` in the corpus) and at \
                      NO `assume`. Of 34 distinct assumption texts **17 are mechanically \
                      flagged** (a semicolon or a German conjunction) and **8 judged to \
                      carry two claims that can fail independently** -- one name, one \
                      falsifier, \
                      two obligations; it was 9 before `dma_kohaerent` was split. *The \
                      mechanical half over-counts by more than a factor of two and is \
                      printed anyway* -- the judgement stands per entry in \
                      `messung/ANNAHMEKONJUNKTIONEN.md`. `beispiele/gift/462` and `/463`; \
                      `beispiele/60` is the counterprobe. **3 hand mutations, all BUILT, \
                      all caught -- but the first witness was worthless**: dropping the \
                      `fn … arch` branch went through `beispiele/60`, because an `entry` \
                      in the same file supplied the machine anyway. *A witness standing \
                      next to a second source of the same answer witnesses nothing.* \
                      `/463` is the one that has no second source. Lane S5 extends the \
                      rule to `syscall … arch`, pinned by `beispiele/gift/833` (a syscall \
                      for `x86_64` in a unit that declares only `aarch64`).",
        fundstelle: "crates/gabbro-check/src/namen.rs; SYNTAX.md §12; «B40»",
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
        kennungen: &["N035", "N036"],
        aussage: "Every function pointer type in the tree carries an `effects` clause and a \
                  `costs` bound, and its effect list uses only words that can be carried across a \
                  call whose callee is not statically known (`reads`, `writes`, `allocs`, \
                  `pure`, `diverges`). The `requires`/`ensures` clauses of the type are \
                  CARRIED, not refused: they ride into the type (`umgebung.rs`) and are read \
                  at the indirect call and at the producer (`m1.fnzeigervertrag`). A program \
                  that passes this rule therefore has, at every indirect call site, a static \
                  promise from which the effect hull and the cost sum can be computed.",
        vorbehalt: "**The rule buys the hull by REFUSING the rest, and the refusal is the \
                    gap.** `locks`, `locks shared`, `masks`, `consumes` and `publishes` are \
                    rejected at the type because the passes that read them (`geteilt`, \
                    `kontexte`, `m2`, `paarung`) resolve the callee by NAME. So the lock \
                    order, the interrupt-context rule, linearity and the pairing do **not** \
                    cross an indirect call -- a program needing that does not pass, rather \
                    than passing unchecked. *Measured beside it: Caprock's four indirect call \
                    sites take no lock.* And the `let` scan that supplies the local type \
                    picture is FLAT: two bindings of one name in two branches collapse. \
                    **Lane 177 retired `N037`** (the refusal of `requires`/`ensures` at the \
                    type): what it refused is read now, by the sentence beside this one.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: one probe each on `N035` (240) and `N036` (243); the \
                      positive side is beispiele/49. `N037` stood here until lane 177 and \
                      is issued nowhere since: `gift/247`-`248` pin the readings that \
                      replaced the refusal (`N295`/`N296`).",
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
        name: "d.kettenkante",
        kennungen: &["D014", "D015", "D016"],
        aussage: "The two field names of `chain(a, b) in <place>` are held against the table \
                  the chain walks: each names a real slot field (`D014`), each is an `option \
                  index into` that table (`D015`), and neither points into a foreign one \
                  (`D016`). **The same three questions as `d.baumkante`, and deliberately \
                  the same wording** -- `chain` is the one domain that names its edge AT THE \
                  WALK instead of at the declaration, and until 2026-08-31 that was the one \
                  edge nobody read.",
        vorbehalt: "**Two of the five measured falsifications still pass, and under Regel A \
                    they must.** `chain(sibling, child)` -- the declared pair with the roles \
                    exchanged -- and `chain(parent, parent)` are structurally well-formed \
                    chains: `chain(x, x)` walks a spine and stands in the corpus \
                    (messung/proben/probe-vier-zellen.gab, `chain(naechst, naechst)`). \
                    Refusing them needs a statement about what the author MEANT. **And when \
                    the place does not resolve to a table the pass is SILENT** -- the type \
                    of a domain's place is checked by nobody, for all nine domains, and that \
                    gap is named and measured in messung/DOMAENENNAMEN.md, not closed here.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 422 (`D014`, the field does not exist), 423 (`D015`, a \
                      `bool` -- no edge, no end), 424 (`D016`, an edge into another table). \
                      The clean side is beispiele/55-kindkette.gab and \
                      messung/proben/probe-neun-domaenen.gab; the counter-direction (the \
                      reversed pair, `chain(parent, parent)`, `chain(child, child)`) is \
                      measured green at each of them.",
        fundstelle: "crates/gabbro-check/src/domaene.rs; messung/DOMAENENNAMEN.md; \
                     SYNTAX.md:1060",
    },
    Satz {
        name: "m.wahrheit_ist_keine_zahl",
        kennungen: &["M135"],
        aussage: "A value does not cross between `bool` and a number. `m1.rs::passt` ends \
                  in a comparison of RANGES, and `Typ::Wahrheit` has none -- so the whole \
                  boundary fell through a silent `else`, at every `return`, every \
                  assignment and every argument. **This is the other half of `N044`'s \
                  sentence**: `N044` sees THAT a verdict is missing, `M135` sees whether \
                  the one that is there is a verdict at all.",
        vorbehalt: "**A range of exactly `0 .. 1` is not a crossing** -- a one-bit device \
                    field admits both truth values and nothing else, and \
                    beispiele/gift/416 reads one into a `bool`. The line is the RANGE and \
                    not the width: `return 1` has `u8 in 1 .. 1` and falls. And it holds \
                    ONLY this boundary. **The float half of this caveat is WITHDRAWN on \
                    2026-09-02**: it read *a float against an integer crosses the same \
                    silent `else` and is not refused*, and that was true until `M140` \
                    closed the `else` itself (satz m1.gestalt). The sentence stands as a \
                    statement about THIS rule's reach and no longer as a statement about \
                    the checker's.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured 2026-08-31 against the UNCHANGED checker: \
                      messung/proben/probe-rueckgabetyp.gab falsifies four returns in one \
                      file and exactly ONE falls (`-> u8 { return 300; }` at `M101`) -- the \
                      one where both sides carry a range. **And no stage after this one \
                      says a word either**: `emit` writes `return 7;` into a `bool` \
                      function and `cc -O0 -Wall -Wextra -Werror` accepts it, because C \
                      converts. A probe returning `7` HOLDS on that path, always. Poison is \
                      beispiele/gift/430. **Its first two finds were in this checker**: a \
                      compare-exchange bound to the atomic's type instead of to `bool` \
                      (`beispiele/35-tausch.gab`, where the emitter had written `bool \
                      genommen` all along), and an `exchange update` body read against the \
                      enclosing function's result instead of the place's type \
                      (beispiele/gift/209). Over all 475 corpus files the rule falls in ZERO \
                      after both repairs.",
        fundstelle: "crates/gabbro-check/src/m1.rs; messung/proben/probe-rueckgabetyp.gab; \
                     messung/proben/probe-probenurteil-typ.gab",
    },
    Satz {
        name: "n.probenurteil",
        kennungen: &["N044", "N045"],
        aussage: "A `can_fail` block yields a VERDICT, and on every path: every `return` in \
                  it carries a value (`N044`), and no path reaches its closing brace \
                  (`N045`). A probe FALLS or it HOLDS -- `return false` and `return true` \
                  are the two things it can say.",
        vorbehalt: "**It says nothing about the TYPE of the value returned**, only that \
                    there is one on every path: `return 7` in a `can_fail` block is not \
                    refused here -- MEASURED 2026-08-31, and all four stages pass it (`cc` \
                    converts `7` to `true`, so there is no fourth stage that refuses). The \
                    gap is not the `check`'s: `m1.rs::passt` compares RANGES, and \
                    `Typ::Wahrheit` had none, so the `bool`/number boundary was unheld \
                    at every `return`, assignment and argument. **Both caveats are gone**: \
                    `M135` holds the boundary since the same day (satz \
                    m.wahrheit_ist_keine_zahl): `crate::endet_immer` treated every \
                    loop as falling through and refused a probe whose only exits stand \
                    inside a `forever`; that was a FALSE refusal (`cc -Werror` accepts the \
                    `for (;;)` it emits), and it is repaired.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured 2026-08-31 against the UNCHANGED checker: six of the twelve \
                      files in messung/tor-proben/ emit C that `cc` refuses -- `bool \
                      pruefe_c(void) { if (k >= 3) { return; } }`. `gabbro pruefe` said 0 \
                      errors and `gabbro emit` no `C001`; three stages passed it and the \
                      fourth is not part of the language. Eighteen corpus files carried the \
                      shape and every one of them was a defect; they are repaired, and the \
                      poison is beispiele/gift/428 (`N044`) and 429 (`N045`). \
                      **beispiele/06-annahmen.gab has carried the finding as a COMMENT \
                      since 2026-08-20 with no rule behind it** -- and six files walked \
                      back into it. messung/TORREICHWEITE.md. **The loop half was measured \
                      2026-08-31** at messung/proben/probe-probenurteil-schleife.gab: \
                      `N045` fell there and should not have. Over all 475 corpus files the \
                      repair changes exactly that one file -- no other rule fell silent, \
                      none newly spoke.",
        fundstelle: "crates/gabbro-check/src/namen.rs; dokumente/SYNTAX.md §13; \
                     beispiele/06-annahmen.gab",
    },
    Satz {
        name: "d.domaenenfeld",
        kennungen: &["D019"],
        aussage: "The FIELD names in the suffix of a domain's place resolve. The third \
                  question at the same place: `D017` reads its base name, `D018` its kind, \
                  `D019` the field names of its suffix. A quantifier over a field that \
                  stands nowhere ranges over nothing -- **the same sentence `D017` says \
                  about the base name, and `M134` about a field access in a body.**",
        vorbehalt: "**It is silent wherever the PREFIX did not resolve**, and that is the \
                    whole discipline: the walk stops at the first suffix whose carrier is \
                    unknown. That makes the rule safe at a `traverse` over a `let` binding \
                    -- the position `D017` has to skip for want of a block scope cannot \
                    produce a false refusal here, because a rule that says nothing about an \
                    unknown carrier says nothing at all.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured 2026-08-31 against the UNCHANGED checker, \
                      messung/proben/probe-elems-feldname.gab: `elems of r.plaetze` \
                      falsified to `elems of r.gibtsnichtfeld` in `ensures`, in `requires` \
                      and in the body of a `spec fn` gave `8 items, 0 errors, 0 hints` -- \
                      **not one of them**, and `ensures` among them, so `M109` does not read \
                      a field name either and the DOMAENENSTELLUNGEN.md §7 cell was too kind \
                      to the checker. The control in the same run: the same place with a \
                      falsified BASE name (`elems of zzznix.plaetze`) does fall, at `M109` \
                      -- *the base is read and the field is not.* Poison is \
                      beispiele/gift/431. Over all 478 corpus files the rule falls in ZERO.",
        fundstelle: "crates/gabbro-check/src/domaene.rs; \
                     messung/proben/probe-elems-feldname.gab; \
                     messung/DOMAENENSTELLUNGEN.md §7",
    },
    Satz {
        name: "d.abbildungsfeld",
        kennungen: &["D020"],
        aussage: "The FIELD names of a bound MAPPING resolve. The fourth question at a \
                  quantifier and the first about the VARIABLE: `D017` reads the base name, \
                  `D018` its kind, `D019` the field names of its suffix -- and all three stop \
                  at the PLACE. **`mappings of` is the one domain that binds a record** \
                  (`SPRACHE.md` §6), so it is the one where `m.field` means anything, and it \
                  was the one nobody read. A mapping carries the fields of the node `format` \
                  plus three the domain synthesises from the POSITION -- `va`, `level`, \
                  `index`.",
        vorbehalt: "**Silent wherever the `walk` did not resolve** -- no walk name, no node \
                    `format`, no field list, no refusal. Same discipline as `D019`. **And \
                    silent under an inner quantifier that REBINDS the name**, which the rule \
                    got wrong on its first day: `forall m in mappings of a : forall m in \
                    mappings of b : m.belegt` was refused against `a`'s node `format`. The \
                    shape is reachable only through `mappings of`, because the other seven \
                    domains bind an index -- *a rule that is right only because the \
                    neighbouring domains cannot express the shape is right by accident.* And \
                    it says nothing about what a field MEANS: whether `m.schreibbar` is the \
                    leaf entry's bit or the conjunction over the path is a reading this tree \
                    has not made, and this rule does not make it either -- it holds that the \
                    name stands somewhere.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured 2026-09-01 against the UNCHANGED checker: a `walk` over `[Pte; \
                      512]` with `forall m in mappings of Self : !m.gibtsnicht` in an \
                      `invariant` gave `3 items, 0 errors, 0 hints` -- **`Pte` has no field of \
                      that name and no pass said so.** The control in the same run: the same \
                      line with a falsified BASE name (`mappings of GibtsNicht`) does fall, at \
                      `D017` -- *the base is read and the variable's field is not.* The cause \
                      stands in `domaene.rs`: `ortsfelder_pruefen` returns early on a bound \
                      name because a quantifier variable carries no type there, and for \
                      `mappings of` the type is no guess. Poison is beispiele/gift/570, whose \
                      two counter-probes (an entry field and `va`) stay silent in the same \
                      file. Over all 533 files -- 171 corpus plus 362 gift -- the rule falls \
                      in ZERO.",
        fundstelle: "crates/gabbro-check/src/domaene.rs; \
                     beispiele/gift/570-mapping-field-not-declared.gab; \
                     dokumente/PLAN-HARDWARE.md §5",
    },
    Satz {
        name: "d.domaenenort",
        kennungen: &["D017", "D018"],
        aussage: "The PLACE a domain runs over is held twice: its base name \
                  resolves (`D017`), and it is of the kind the domain needs (`D018`) -- a \
                  table for `slots of`, a record for `queue`, an array field for `elems \
                  of`, a `walk` for `mappings of`, and a slot for the three that walk the \
                  tree. **`D017` is `M109`'s question in the four positions `M109` does not \
                  read**: `requires`, an `invariant` of a `table`, of a `walk` or of a \
                  `group`, and the body of a `spec fn`. **And it holds BOTH producers of a \
                  domain**: the grammar makes one at a `quant` and one at a `member` \
                  (`expr in domain`), and until 2026-09-02 only the first was walked.",
        vorbehalt: "**`D017` is silent in `ensures` and at a `traverse`, and both are \
                    measured decisions.** `M109` reads every name of a postcondition, so a \
                    second refusal there would be a second refusal for one fault; a domain \
                    in a BODY may run over a `let` binding, and this pass carries no block \
                    scope -- at a `traverse` with a `costs` line `K003` speaks instead, \
                    about the missing bound rather than about the name. It is also silent \
                    on `Self`, which is the carrier question and belongs to `M120`, and on \
                    `fields of` (a path, not a place, and zero corpus sites -- Regel A) and \
                    `threads` (names nothing, `Q3`). **`D018` stays silent whenever the \
                    type of the place does not resolve**: a place the checker cannot type \
                    is not a place of the wrong kind.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Every one of the 53 corpus quantifier sites outside `ensures` was \
                      falsified one by one against the UNCHANGED checker -- the base name \
                      replaced by `zzznix`, the file's own base load subtracted: **51 \
                      silent, 2 answering with `D012`** (a premise at a call, not the \
                      name). After the build all 53 fall with `D017`. Poison: \
                      beispiele/gift/425 (`D017` in an `invariant`), 426 (`D018`, `slots \
                      of` over a record), 427 (`D018`, `queue` over a table -- the shape \
                      the corpus itself carried). The counter-direction is the whole \
                      corpus: 462 files, and the only place either code falls is the one \
                      the measurement found. messung/DOMAENENSTELLUNGEN.md. **The `member` \
                      half was measured 2026-09-02**: `requires i in slots of GIBTSNICHT` \
                      gave `0 errors` while the same words under a `forall` fell at \
                      `D017`. Poison is beispiele/gift/638; on this corpus the widening \
                      has ZERO bite -- no `member` predicate in it names a place that does \
                      not resolve, and no file changed.",
        fundstelle: "crates/gabbro-check/src/domaene.rs; messung/DOMAENENSTELLUNGEN.md; \
                     messung/DOMAENENNAMEN.md",
    },
    Satz {
        name: "d.praedikatsname",
        kennungen: &["D021"],
        aussage: "The base name of a PLACE in a predicate resolves -- in every position this \
                  pass walks, and not only where a domain stands. `M109` asks it of an \
                  `ensures`, `N053` of a device promise, `N032` of a `format … where`; \
                  `D021` asks it of a `requires`, of the body of a `spec fn`, of the \
                  `invariant` of a `table`, a `walk` or a `group`, of all three loop \
                  invariants and the `until` of a `retry`, of the `down` and `leaf` of a \
                  `walk`, of the `requires` of an `axiom`, of the `floor` of a `check` and \
                  of the `when` of a compare-exchange. **A conjunct over a name nothing \
                  declares is not a missing finding but a WRONG PROOF OBJECT**: `gabbro \
                  lean` writes a `requires` into `<fn>_pre`, \"what the caller grants\", and \
                  `Gabbro.Body` reads `.global` out of a TOTAL store -- so the premise is \
                  satisfiable, and unlike a dropped conjunct it is visible in no channel.",
        vorbehalt: "**Silent in `ensures`, on `Self`, and on the argument of `Has(…)` and \
                    `Held(…)` -- each of the three for a different reason and each forced \
                    by a file of the corpus.** `ensures` has `M109`, and a second refusal \
                    for one fault is worse than one; `Self` is the carrier question and \
                    belongs to `M120`; a machine feature is not a program name and a lock \
                    is not a value, and both are spelled as a call, so both would otherwise \
                    be read as places (`beispiele/01-tabelle.gab` writes `Held(KAPPEN)` at \
                    every `impl fn`, `beispiele/11` writes `Has(RDTSCP)`). The exemption of \
                    the two pseudo-calls is by NAME and not by site, the way \
                    `namen.rs::zusagenstelle` does it -- coarse, and coarse in the quiet \
                    direction. **And it reads the BASE name only**: a field of a resolving \
                    carrier is `D019`'s question at a domain and nobody's in a comparison, \
                    which the measurement says out loud rather than hiding.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured 2026-09-02 against the UNCHANGED checker, 19 predicate \
                      positions x 20 name kinds, the phantom name set BESIDE a legitimate \
                      conjunct so that a rule which only fires over an otherwise empty \
                      clause cannot count as a reader: **266 of 380 cells silent**, and \
                      three positions of nineteen resolved a name at all. After the build \
                      125 are silent and the remainder is named per kind. \
                      messung/PREDICATE-NAMES.md. It found one in the tree it was written \
                      against: messung/fragmente/F01.gab:189 wrote `c.slots[s] reaches \
                      WURZEL via parent` -- byte for byte the excerpt's own line -- and no \
                      unit of that file declared `WURZEL`. Poison: beispiele/gift/647 \
                      (`fn … requires`), 648 (`axiom … requires`, the assumption tier), 649 \
                      (the `when` of an exchange, the one position that RUNS). The \
                      counter-direction is the whole corpus: 108 clean files and 415 poison \
                      probes, and after the F01 line the rule falls in ZERO of them.",
        fundstelle: "crates/gabbro-check/src/domaene.rs; messung/PREDICATE-NAMES.md; \
                     messung/fragmente/F01.gab",
    },
    Satz {
        name: "d.binderverwendung",
        kennungen: &["D022"],
        aussage: "The DOMAIN of a quantifier decides what the binder is, and every use of \
                  the binder answers to it. The fifth question at a quantifier and the first \
                  that reads the domain and the BODY together: `D017` reads the place's base \
                  name, `D018` its kind, `D019` the field names of its suffix, `D020` the \
                  fields of a bound mapping -- and after all four the domain itself was \
                  still decoration. Four of the nine domains bind a slot index of a named \
                  table (`slots of`, `descendants of`, `ancestors of`, `chain(a, b) in` -- \
                  the last by `D016`, which refuses an edge that leaves its table); two bind \
                  an index into an array field (`queue`, `elems of`); `threads` binds a \
                  number that addresses nothing this unit declares; `mappings of` binds a \
                  record; `fields of` binds a field NAME. A use that contradicts what bound \
                  it is refused.",
        vorbehalt: "**Silent wherever the domain's place did not resolve to a table**, and \
                    silent when `D017`/`D018`/`D019` have just refused that place -- two \
                    refusals for one fault is worse than one, the sentence `D021` writes \
                    about `ensures` and `M109`. **And it does NOT refuse an `index into T` \
                    used as an ARRAY index**: a `[T; N]` whose `N` is the table's `count` is \
                    a shape this tree writes, and refusing it would be a bound nobody proved \
                    with the sign that rejects a correct program -- *W10, in the expensive \
                    direction.* The fields of a `mappings of` binder belong to `D020`. It \
                    says nothing about whether the statement is TRUE, only that the binder \
                    and the domain are about the same thing.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured 2026-09-08 against the UNCHANGED checker, all NINE domains, \
                      one probe per domain on messung/proben/probe-neun-domaenen.gab with \
                      the domain of one function rewritten and nothing else: **9 of 9 gave \
                      `0 errors, 0 hints` and BYTE-IDENTICAL C** (md5 `dbc3e06b` in every \
                      row). The census of 2026-09-07 §1.1 had the finding at one domain and \
                      asserted the other eight; this is that differential, run. Poison is \
                      beispiele/gift/687 (`threads` indexing a table -- the census's own \
                      shape) and 688 (a `slots of A` binder indexing `B`). Over all 665 \
                      `.gab` files of the tree the rule falls in ONE that was clean before: \
                      beispiele/57-faedenhalt.gab, whose own header had carried the finding \
                      as prose since 2026-08-31 (*\"`forall t in slots of Faden : …` says \
                      exactly the same to the checker, only without the claim\"*) -- the \
                      file now writes what it described.",
        fundstelle: "crates/gabbro-check/src/domaene.rs; \
                     messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md §1.1; \
                     messung/proben/probe-neun-domaenen.gab",
    },
    Satz {
        name: "d.binderungenannt",
        kennungen: &["D023"],
        aussage: "The body of a quantifier MENTIONS its binder. A `forall v in D : P` whose \
                  `P` is free of `v` says the same over one element as over a million, and \
                  the same over `D` as over any other domain -- the domain is decoration by \
                  construction, and it is the one shape no use-rule can reach because there \
                  is no use.",
        vorbehalt: "**A HINT and not a refusal**, and the ground is measured rather than \
                    tidy: the form is vacuous, not inconsistent (`P` weakened by the \
                    emptiness of `D` is a true statement and a useless one), and after \
                    `D022` neither `fields of` nor `threads` can say anything about a \
                    declared carrier at all -- so the vacuous body is the last writable form \
                    of two domains of the nine. *A refusal that makes a word of the grammar \
                    unwritable is a grammar change wearing a rule's clothes*, and that \
                    change is booked elsewhere (`PLAN.md` §9.1, \"a language change, not a \
                    model change\"). **The place of an INNER domain counts as a mention** -- \
                    `forall s in slots of Self : forall x in chain(a, b) in Self.slots[s] : \
                    …` names `s` there and nowhere else.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured 2026-09-08 over all 665 `.gab` files of the tree: the hint \
                      stands at SEVEN sites, all of them in the two measurement carriers \
                      messung/proben/probe-neun-domaenen.gab and probe-stellungen.gab, and \
                      every one of them is a `fields of` or `threads` cell written \
                      `k.slots[0]` because the binder had no usable form. Zero in the \
                      70-file corpus. Poison is beispiele/gift/689. The inner-domain \
                      exemption was forced by probe-stellungen.gab: the first cut called \
                      three invariants of that file unused and all three name the binder in \
                      an inner `chain(…) in` / `descendants of` / `ancestors of` place.",
        fundstelle: "crates/gabbro-check/src/domaene.rs; \
                     messung/proben/probe-stellungen.gab",
    },
    Satz {
        name: "d.threadsohnemenge",
        kennungen: &["D024"],
        aussage: "A `threads` quantifier whose body USES its binder states nothing. \
                  `threads` is the one domain of the nine that hangs on no declaration: \
                  `slots of` hangs on `count N`, `descendants of` and `ancestors of` on the \
                  table's `tree { … }`, `mappings of` on `walk … levels`, `queue` on the \
                  one array field of a record -- and `threads` on nothing. So `forall t in \
                  threads : P(t)` is true over the empty set, false over the naturals, and \
                  nothing in the unit says which set it is. `D022` refuses every use of the \
                  binder as a PLACE or as an INDEX; `D023` hints where the body never \
                  mentions it; between the two sat the binder as a plain NUMBER, and that \
                  is the shape this rule refuses.",
        vorbehalt: "**It does not give `threads` a domain**, and the surface that would is \
                    booked elsewhere as a language change \
                    (messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md §2.3, `PLAN.md` §9.1 and \
                    §15). It is silent where `D022` has already refused the same quantifier \
                    -- two refusals for one fault is worse than one, the sentence `D022` \
                    writes about `D017` and `D023` about `D022`. **And it leaves `D023`'s \
                    vacuous form standing on purpose**: refusing that as well would make a \
                    word of the grammar unwritable, which is a grammar change wearing a \
                    rule's clothes. The word keeps one writable shape, and `D023` goes on \
                    saying what that shape is worth.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured 2026-09-08 against the checker of `6c835eb`, i.e. WITH \
                      `D022` and `D023` already in it: `spec fn alle_klein() -> bool = \
                      forall t in threads : t < N;` gave **4 items, 0 errors, 0 hints**, \
                      and `gabbro pflichten --lean` on it gave `total 0  goals 0  refused \
                      0` -- a claim the checker admitted and the proof channel never even \
                      saw. Poison: beispiele/gift/690. The counter-direction is the whole \
                      tree: over all **686 `.gab` files the rule falls in ZERO** that were \
                      clean before, because every `threads` quantifier the tree writes is \
                      the vacuous one `D023` already hints at (seven sites, all in \
                      messung/proben/probe-neun-domaenen.gab and probe-stellungen.gab). \
                      **A rule with no corpus site and one measured hole is the shape of a \
                      form nobody had probed** -- the 2026-09-07 census's own sentence \
                      about Trap 80.",
        fundstelle: "crates/gabbro-check/src/domaene.rs; \
                     messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md §2.3; \
                     programmlogik/PLAN.md §15; beispiele/gift/690",
    },
    Satz {
        name: "d.zaehlungbrauchtlaenge",
        kennungen: &["D025"],
        aussage: "A `count` RUNS over its domain, so the domain must have a length. \
                  Four domains do -- `slots of`, `descendants of`, `ancestors of`, \
                  `elems of` -- each with a bound the cost pass reads; five do not \
                  (`chain(…) in` ends but has no length, `fields of` binds names not \
                  entries, `threads` hangs on no declaration, `mappings of` holds no \
                  cost promise over a run-time traversal), and each is refused by \
                  name rather than priced at nothing.",
        vorbehalt: "The refusal comes before any binder rule: where `D025` fires, \
                    `D022`/`D023`/`D024` stay silent about the same fault -- one \
                    fault, one refusal (the `D022`-after-`D017` reservation, one \
                    construct over). The cost pass reads the same kind list and \
                    counts open without refusing where this rule fired \
                    (`kosten.rs`, the twin that breaks with it). What it does NOT \
                    do is give `queue` a length: counting dead cells is not a \
                    missing lowering but a wrong set («B10»).",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/693: `count k in threads : k == k` in a body -- \
                      3 items, 1 error, and it is `D025`. The counter-direction is \
                      the corpus: no clean file counts over a refused domain.",
        fundstelle: "crates/gabbro-check/src/domaene.rs (`zaehlbar_pruefen`); \
                     beispiele/gift/693",
    },
    Satz {
        name: "d.eignerbrauchtgeschicht",
        kennungen: &["D026"],
        aussage: "A `table … owner m` clause is parsed and refused by name. The \
                  grammar promises that every access holds the mark and nobody \
                  mints it -- and says nothing about who mints the FIRST one. A \
                  guard nobody holds is a sentence, not a discipline, so until the \
                  producer story stands the clause is unwritable: remove it and \
                  guard the table with `protects`.",
        vorbehalt: "This is deliberately NOT the M2 mark discipline deferred: there \
                    is nothing to defer, because no producer exists to defer it to. \
                    Since lane 151 the sentence has named successors: a mark with a \
                    complete producer (`D265`-`D268` clean, one foreign minter \
                    executed exactly once, a guarded access) lifts this refusal -- \
                    the producer is the rule that holds it, not an extension of \
                    this sentence. An incomplete producer (no minter, no mint \
                    execution, or a minter no guarded access exercises) keeps this \
                    refusal; a malformed one falls under its own code and stays \
                    silent here.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/694: `table Plaetze count 8 owner Marke` -- \
                      3 items, 1 error, and it is `D026`. Zero corpus sites carry \
                      the clause.",
        fundstelle: "crates/gabbro-check/src/kbedingung.rs (`eigner`); \
                     beispiele/gift/694",
    },
    Satz {
        name: "d.ownermarkislinear",
        kennungen: &["D265"],
        aussage: "An `owner m` clause names a declared `linear` type. The guard is a \
                  linear value, and nothing holds it unless the mark is one: without \
                  the declaration the rest of the producer story has no subject.",
        vorbehalt: "The rule checks the KIND, not the shape: a parameterised linear \
                    type passes by name, and whether its arguments can be held is the \
                    holders' rule (`D267`), not this one. Where the mark is no linear \
                    type, `D026` stays silent -- one fault, one refusal.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/934: `owner Marke` over `type Marke = u32` -- \
                      3 items, 1 error, and it is `D265` alone.",
        fundstelle: "crates/gabbro-check/src/kbedingung.rs (`eigner`); \
                     beispiele/gift/934",
    },
    Satz {
        name: "d.ownermintdiscipline",
        kennungen: &["D266"],
        aussage: "An `owner` mark has exactly one minter: a single body-less \
                  (foreign) signature returning the mark without taking it -- a named \
                  assumption, like every foreign body. No signature (re)produces the \
                  mark: a second foreign mint, any `allocs` of the mark, and any \
                  bodied function returning it without taking it are refused. This is \
                  the checker half of `eigner_nie_erzeugt` (`Syntax.lean:149`).",
        vorbehalt: "The rule counts INTRODUCTIONS, not forwards: a bodied function \
                    taking the mark and returning it forwards what it was given and \
                    stays silent, and so does a foreign signature doing the same. \
                    Borrowing the mark back across a call (`consumes` plus `allocs`) \
                    is refused with the `allocs` half -- move-only this lane; the \
                    borrow needs a Lean amendment that is booked, not built. Where \
                    this rule fires, `D026` stays silent -- one fault, one refusal.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/932 (a second `extern fn … -> Marke`): 6 items, \
                      1 error, and it is `D266` alone. beispiele/gift/935 (`allocs \
                      Marke`): 5 items, 1 error, and it is `D266` alone. The bodied \
                      return without the mark is pinned inline in \
                      `crates/gabbro-check/tests/paesse.rs` \
                      (`eigner_rumpf_gibt_nur_weiter_was_er_nimmt`).",
        fundstelle: "crates/gabbro-check/src/kbedingung.rs (`eigner`); \
                     beispiele/gift/932, beispiele/gift/935",
    },
    Satz {
        name: "d.owneraccessholdsmark",
        kennungen: &["D267"],
        aussage: "Every access to an `owner`-guarded carrier happens while the mark \
                  is held: a bodied function whose assignment, `publish` or \
                  `exchange` target -- or whose READ -- resolves to the carrier \
                  (directly or through a pointer parameter into it) owes a linear \
                  parameter of the mark, borrowed or consumed. Reads come through \
                  the very walk `E010` reads (`wirkungen::lese_orte`), not a second \
                  walk. A foreign signature (no checkable body) owes \
                  the same parameter for every declared `reads`/`writes`/`consumes`/ \
                  `publishes` touch. A bare `consumes m` of a linear parameter is a \
                  value, not a carrier touch.",
        vorbehalt: "An `effects` line alone is the call-graph hull, not an access -- a \
                    caller declaring what its callee writes owes no mark for the line. \
                    `spec fn` is exempt, like under `H007`. Where this rule fires, \
                    `D026` stays silent -- one fault, one refusal.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/933 (a bodied write with no mark beside a \
                      standing minter): 5 items, 1 error, and it is `D267` alone. \
                      The pointer-mediated touch, the hull exemption and the read \
                      half are pinned inline in \
                      `crates/gabbro-check/tests/paesse.rs` \
                      (`eigner_zugriff_haelt_marke_d267`, \
                      `eigner_lesen_haelt_marke_d267`); the held read stands as \
                      `beispiele/115`.",
        fundstelle: "crates/gabbro-check/src/kbedingung.rs (`eigner`); \
                     beispiele/gift/933, beispiele/115",
    },
    Satz {
        name: "d.ownermintisingle",
        kennungen: &["D268"],
        aussage: "The single minter executes once: exactly one static call site in \
                  the unit, outside every loop form, in a root no call site \
                  reaches (an entry), and that root started at most once (no two \
                  thread starts name it). A second site, a site inside \
                  `traverse`/`retry`/`forever`, a minting root with a caller, a \
                  minting root named by two starts, and a taken minter address \
                  are each refused -- each mints, or may mint, a second live \
                  mark, hence a second owner. Contract calls count as sites: a \
                  contract calling the minter executes it.",
        vorbehalt: "The count is closed-world: a unit with no starts is a library, \
                    and re-invocation of its root from outside is the importer's \
                    duty, like every `pub fn` called twice. A boot step counts as \
                    a site under a caller-free root (boot runs once). Where this \
                    rule fires, `D026` stays silent -- one fault, one refusal.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Pinned inline in `crates/gabbro-check/tests/paesse.rs` \
                      (`eigner_zweiter_aufruf_d268`, `eigner_aufruf_in_schleife_d268`, \
                      `eigner_gerufene_wurzel_d268`, `eigner_zweimal_gestartet_d268`, \
                      `eigner_adresse_genommen_d268`): each falls with exactly \
                      `D268`; the singly-started and singly-called shapes stay \
                      silent beside `D026`. No gift numbers were left in this \
                      lane, so the shapes stand inline.",
        fundstelle: "crates/gabbro-check/src/kbedingung.rs (`eigner`); \
                     crates/gabbro-check/tests/paesse.rs",
    },
    Satz {
        name: "d.sharedcarriernamesinvariant",
        kennungen: &["D027"],
        aussage: "A `requires`/`ensures` clause of a shared-side function that \
                  reads a table carrier must call a declared invariant -- or a \
                  `spec fn` stating one -- by name; a restated predicate is \
                  refused. Shared-side arrives through a `locks shared` effect \
                  or a `Held(L, shared)` witness, which is the only syntactic \
                  mark a shared carrier leaves.",
        vorbehalt: "The rule is the syntactic shadow of the invariant form, not \
                    the form itself: that the named call coincides with the \
                    carrier invariant (`hForm`) is the prover's, and a bare \
                    invariant name is no resolvable call -- the call graph \
                    names that edge (`H021`), not this rule. Outside contract \
                    position (loop invariants, `spec fn` bodies, functions \
                    without a shared side) non-invariant shapes stay own-logic \
                    debt, and where `D021` already refused the same clause this \
                    rule stays silent -- one fault, one refusal.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/792 (`requires` restates), 793 (`ensures` \
                      restates), 794 (quantifier restates), 795 (reference \
                      beside a restatement): each falls with exactly one \
                      `D027`. The counter-directions stand in \
                      `crates/gabbro-check/tests/paesse.rs` \
                      (`eine_geteilte_klausel_nennt_ihre_invariante`): `spec \
                      fn` reference silent, witness alone silent, \
                      exclusive-side restatement silent.",
        fundstelle: "crates/gabbro-check/src/domaene.rs (`d027_klausel_pruefen`); \
                     beispiele/gift/792-795",
    },
    Satz {
        name: "n.merkmalsform",
        kennungen: &["N054"],
        aussage: "A machine feature demand names ONE feature, and a feature is a bare name. \
                  `Has()` demands nothing, `Has(7)` demands a number, `Has(a.b)` demands a \
                  place, and `Has(RDTSCP, XSAVE)` reads as a demand for two features and is \
                  one for the first -- every reader of the form takes `argumente.first()`.",
        vorbehalt: "**It does NOT decide whether the name is a feature of the machine, and \
                    that half is not decidable in this tree.** `SPRACHE.md` puts the only \
                    generator of `Has(F)` at the CPUID probe (A14); that probe does not \
                    exist, no `mints Has(F)` form exists, and nothing in the language \
                    declares a feature name. A resolver would need a declared list, and who \
                    declares it is an owner's decision with two shapes -- a house table \
                    under `arch`, the way `cnamen.rs::SIGNATUR` carries what C has taken \
                    (no new word), or a language form that mints the witness (a new word, \
                    and the vocabulary ratchet stands at 221/208/333). **Named, not built.** \
                    `N016` carries the demand through the call graph and stops where \
                    somebody DECLARES it; that a `check` or an `assume` could ESTABLISH it \
                    is a form that does not exist.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured 2026-09-02 against the UNCHANGED checker, eleven written \
                      forms across six predicate positions: **64 of 66 accepted**, \
                      including `Has()`, `Has(7)`, `Has(GRENZE + 1)`, `Has(T.slots)` and \
                      `Has(RDTSCP, XSAVE)`. The two that fell did so at `N053` and about \
                      the SECOND argument, not about the form. Poison: \
                      beispiele/gift/650. The counter-direction is in the speech test and \
                      it is the larger half -- four bare names go through, whatever they \
                      are, because that is the question a declared list would answer. Over \
                      108 clean files and 415 poison probes the rule falls in ZERO.",
        fundstelle: "crates/gabbro-check/src/namen.rs; messung/PREDICATE-NAMES.md §5; \
                     dokumente/SPRACHE.md (x86_64 assumption catalogue, A14)",
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
            "M113", "M114", "M115", "M116", "M117", "M118", "M119", "M139", "M140",
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
                    declared lower bound. **The word `every` above rests on `M140`**: \
                    literals are `u128` and the interval is `i128`, and until 2026-09-02 the \
                    values in between answered `Typ::Unbekannt` -- no interval, and therefore \
                    no rule at all. `T.slots[2^127]` on a `count 8` table passed with `0 \
                    errors` while its neighbour `T.slots[2^127 - 1]` fell at `M103`. *A pass \
                    that steps aside where the type is missing needs a rule that the type is \
                    never missing.*",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 15 probes on `M104`, 12 on `M101`, 8 on `M103`, 3 on \
                      `M102`, single probes on 9 further codes, one on `M139` \
                      (`gift/601`). **`M106`, `M107`, `M110` and `M114` have NO probe.**",
        fundstelle: "crates/gabbro-check/src/m1.rs; SPRACHE.md §3.2",
    },
    Satz {
        name: "m1.stelligkeit",
        kennungen: &["M143"],
        aussage: "A direct call passes exactly as many arguments as the callee declares \
                  parameters. Every parameter therefore has a value the caller wrote, and \
                  every value the caller wrote has a slot that reads it -- which is the \
                  precondition of every rule behind this one: the effect hull reads what the \
                  caller may touch through each parameter, `K001` reads the cost the \
                  signature was given, and the range facts that hold after the call are the \
                  callee's.",
        vorbehalt: "**A `transition` is exempt, and it is the only exemption.** Its \
                    `Signatur` is entered with an empty parameter list because the grammar \
                    gives a transition no parameter list at all, while the call \
                    `wurzel_setzen(v)` passes the carrier -- so the count there would be read \
                    off a placeholder. *What the arity of a transition call ought to be is a \
                    question this rule does not answer, and no rule does* (`W10`). The check \
                    also REPORTS and does not return: the overlap still gets its \
                    per-position comparison, because two of three arguments can still be the \
                    wrong shape.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/676. **Reproduced 2026-09-03 against the UNCHANGED \
                      checker, both directions**: `zwei(x)` against `fn(u32, u32)` and \
                      `eins(x, x)` against `fn(u32)` each gave `3 items, 0 errors, 0 hints` \
                      at `100 % coverage`, `gabbro emit` wrote the call out, and `cc` \
                      answered -- *too few arguments to function 'zwei'*. Corpus cost, all \
                      512 files: TWO sites, both in `beispiele/02-geraet.gab` and both \
                      `transition` calls, which is what the reservation above is made of. \
                      The live site outside the corpus is `messung/fragmente/F03.gab`:210, \
                      `owner_core(picked)` against a two-parameter declaration, on a frozen \
                      excerpt line -- it had been surfacing as an `M140` about the wrong \
                      parameter.",
        fundstelle: "crates/gabbro-check/src/m1.rs (ruf_roh); \
                     crates/gabbro-check/src/umgebung.rs (uebergangsnamen, ist_uebergang)",
    },
    Satz {
        name: "m1.praedikatsindex",
        kennungen: &["M141"],
        aussage: "No LITERAL index in a predicate lies outside the length the declaration of \
                  its carrier writes down. It holds at every predicate position this pass \
                  walks: `requires`, `ensures`, the body of a `spec fn`, the invariants of a \
                  `table`, a `walk` and a `group`, and the `invariant` and `until` of all \
                  three loop forms.",
        vorbehalt: "**Only a NUMBER LITERAL, and only against a length the declaration \
                    names.** A computed index stays silent -- `W10`, a lower bound neither \
                    refuses nor confirms -- and so does a quantifier variable, which is the \
                    form the corpus actually writes (`forall s in slots of Self : \
                    Self.slots[s].a == 0`). The same limit `N009` draws at a register \
                    offset, one construct further. **And it says nothing about whether the \
                    predicate is TRUE**: the sentence is about the existence of the cell, \
                    not about its value. The positions it does NOT reach are the ones this \
                    walk does not visit at all -- `axiom … requires`, `reg … requires`, \
                    `transition … requires`, `walk … down/leaf`, `check … floor` and the \
                    `when` of a compare-exchange.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured 2026-09-02 against the UNCHANGED checker: `impl fn f() -> \
                      bool requires T.slots[9].x == 0` on a `table T count 8` gave `4 items, \
                      0 errors, 0 hints`, and `gabbro lean` over the same file wrote it into \
                      `f_pre`, *\"what the caller grants\"* -- an ASSUMPTION over a cell that \
                      does not exist. `Gabbro.Body`'s world is a total map over `slot \
                      (carrier) (index : Int) (field)` and `wellFormed` quantifies over \
                      every `k`, so the premise is satisfiable rather than vacuous: the \
                      sixth class in pure form. Poison is \
                      beispiele/gift/637-an-assumption-over-a-slot-that-is-not-there.gab, \
                      whose counter-probes (a quantifier variable and an in-range literal) \
                      stay silent in the same run. Over all corpus files the rule falls in \
                      ZERO.",
        fundstelle: "crates/gabbro-check/src/domaene.rs; crates/gabbro-check/src/lean.rs; \
                     dokumente/PLAN.md (die sechste Klasse)",
    },
    Satz {
        name: "m1.vorrang",
        kennungen: &["M136"],
        aussage: "No expression in the tree reads one way under Gabbro's grammar and another \
                  way under C's. Gabbro holds `<< >> & ^ |` in ONE flat left-associative \
                  level and puts all five BELOW the comparisons; C grades the five into four \
                  levels and puts `& ^ |` ABOVE the comparisons. Wherever those two tables \
                  disagree and the author wrote no parenthesis, this pass refuses.",
        vorbehalt: "**This is a statement about the READER, not about the product.** The \
                    emitter parenthesises the tree (`emit.rs::geklammert`), so the shipped C \
                    computes what the checker proved even where this rule is silent -- and \
                    `beispiele/gift/436` measures exactly that counterfactual, by demanding \
                    that `cc -Werror` ACCEPT the generated file. The rule refuses only where \
                    the value was measured to move (Rule A): where the left operator binds at \
                    least as tightly as the right, C groups as Gabbro does and nothing is \
                    said. gcc's `-Wparentheses` is wider there and SILENT at six of the nine \
                    that matter -- it is not a second reader for this claim.",
        stand: Satzstand::Gemessen,
        gemessen_an: "`messung/proben/VORRANG-BITSTUFEN.md`: all 25 operator pairs and 4 \
                      comparison forms compiled and RUN, 9 + 2 of them computing a different \
                      value. `beispiele/gift`: 2 probes (`436`, `437`), both `M136` alone. \
                      `crates/gabbro-check/tests/vorrang.rs` pins the reach in both \
                      directions -- 11 forms, each with the verdict it owes.",
        fundstelle: "crates/gabbro-check/src/m1.rs (vorrangfalle); \
                     messung/proben/VORRANG-BITSTUFEN.md",
    },
    Satz {
        name: "m1.komplement",
        kennungen: &["M137", "M138"],
        aussage: "Every `~` this pass accepts stands over an operand whose WIDTH a \
                  declaration gives, and the range it produces is the exact complement over \
                  that width: `MAX - x.max .. MAX - x.min`. A literal and a signed operand \
                  are refused by name, so no accepted `~` takes its width from C's integer \
                  promotion. `M138` closes the same question one form over: an integer word \
                  has `max` and `min`, and a third member is refused rather than lowered as \
                  a place.",
        vorbehalt: "**It says nothing about the EMITTED C**, and that is where the whole \
                    difficulty of this operator lives: `~(uint16_t)x` promotes to `int` in C \
                    and the checked width is gone. The cast is the emitter\u{27}s (`({c})~({c})(x)`) \
                    and is measured there, not here. *Measured 2026-09-01: with the outer \
                    cast stripped at one site, `cc -std=c11 -Wall -Wextra -Werror` compiles \
                    WITHOUT a warning and the program computes `4294905615` where this pass \
                    says `u16 in 0 .. 65535`.*",
        stand: Satzstand::Gemessen,
        gemessen_an: "`beispiele/61-invertierung.gab`, emitted, compiled at `-O0` and `-O2` \
                      and RUN over eight values; `beispiele/62-grenzwort-im-ausdruck.gab` \
                      likewise. `beispiele/gift`: 4 probes (`443` literal, `444` signed, \
                      `445` in a `const`, `447` a third member), each with its code alone. \
                      `crates/gabbro-check/tests/komplement.rs` pins the emitted text in \
                      both directions. Five hand mutations, built: four caught, and the \
                      fifth -- coarsening the range to the full width -- was caught by \
                      NOTHING until `hohes_nibble` was added.",
        fundstelle: "crates/gabbro-check/src/m1.rs; crates/gabbro-check/src/emit.rs; \
                     dokumente/SYNTAX.md \u{a7}4",
    },
    Satz {
        name: "m1.gestalt",
        kennungen: &["M139"],
        aussage: "Two types that meet at a slot -- an argument, a `return`, an assignment, a \
                  `let` with a written type, a `const` or `static` initialiser -- have the \
                  same SHAPE, and where that shape is an aggregate they have the same NAME. \
                  `m1.rs::passt` ends in a comparison of RANGES, and a pointer has none, a \
                  record has none, an array has none -- so at every one of those the \
                  comparison ended in a silent `else`. This is the same `else` `M135` closed \
                  for `bool`, two doors further out.",
        vorbehalt: "**It is the SHAPE and not the type.** Two integers of different width \
                    are one shape (`M101` and `M104` own the range), a range alias is its \
                    carrier (`N030`: taking a scalar alias nominally would be a language \
                    change), and `Unbekannt` and `never` stay silent -- W10, and `Unbekannt` \
                    is what the coverage number counts. Four crossings belong to other \
                    rules and are left to them: `bool` against a number is `M135` with its \
                    `0 .. 1` exception, a reason value is `M124`, the literal zero is the \
                    null pointer and the aggregate zero-initialiser, and an array at a \
                    pointer to its element is C's decay. ~~**And it does NOT compare a \
                    function pointer's parameter or result types** -- `M128` holds arity, \
                    effects and cost at a `fn(...)` slot and nothing else, so `fn(u8)` still \
                    fits a `fn(u32) -> u32` slot with `cc` as the only reader. Nor does it \
                    hold pointer RIGHTS at a call: a `ptr<normal, r>` argument at a \
                    `ptr<normal, rw>` parameter passes here and at `R008`, which compares \
                    the address space alone.~~ **Both closed 2026-09-02, and NEITHER of them \
                    here** -- the two residues were structural, and each landed where its \
                    data lives: the signature as `M142` beside `M128`, because `Typ::FnPtr` \
                    has carried the parameter and result types all along; the rights as \
                    `R013` beside `R008` in M3, because `Typ::Zeiger` carries neither space \
                    nor rights and only the DECLARATION still has them. *This rule still \
                    compares shapes and nothing else -- a `fn(...)` contract and a pointer's \
                    rights are now two other codes' business.*",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured 2026-09-02 against the UNCHANGED checker: 18 parameter kinds \
                      x 18 argument kinds, the wrong thing passed at a call, one file per \
                      cell. **283 of 306 off-diagonal cells went through with `0 errors`, \
                      and the run printed `100 % coverage` at each.** `cc` caught 165, the \
                      emitter refused 96 (`C001`, an array has no lowering as a parameter), \
                      and 22 reached green C -- TWELVE of those carried a value no C \
                      compiler was going to question (four `bool` against a pointer, \
                      eight integer against float); the other ten are correct calls or \
                      `D004`'s, silent inside the declaring module. After the rule: 22 cells silent, and 20 of \
                      them are correct calls or another rule's. **The whole corpus of 495 \
                      files is byte-identical before and after**, which is the \
                      counter-direction. `beispiele/gift`: 603 (the wrong record behind a \
                      pointer), 604 (`M139 allein` -- a pointer at a `bool`, where no later \
                      stage says a word), 605 (`C001`, an array field takes only the zero), \
                      606 (two records with the same field list are two declarations). \
                      `crates/gabbro-check/tests/gestalt.rs` pins both directions -- 9 \
                      correct calls that must stay silent, 4 zero/decay forms the clean \
                      corpus writes, and 7 wrong ones that must fall.",
        fundstelle: "crates/gabbro-check/src/m1.rs (gestalt_passt, gestalt_grund); \
                     crates/gabbro-check/tests/gestalt.rs",
    },
    Satz {
        name: "m3.lese_aendere_schreibe",
        kennungen: &["R012"],
        aussage: "No accepted program writes one bit field of a device word whose READ or \
                  whose WRITE has a side effect. Writing a bit field is a read-modify-write \
                  on the whole word; on a `w1c` word the write-back sets every bit the read \
                  picked up and each of them CLEARS, and on an `rc` word the read is itself \
                  the loss. The rule is over the WORD, not over the addressed field: a plain \
                  `rw` field of a word with `w1c` neighbours carries the same defect.",
        vorbehalt: "**It is not a statement about atomicity.** A read-modify-write on a \
                    device is three generated steps and nothing anywhere says they are one \
                    -- that is a separate open item (`OB4`), and this rule does not touch \
                    it. What it removes is the case where the three steps are wrong even \
                    when nothing interrupts them. *And it says nothing about the exit it \
                    names*: that `d.REG = <bits>;` lowers to a single store is measured in \
                    the emitter, not asserted here.",
        stand: Satzstand::Gemessen,
        gemessen_an: "**A DELIVERED defect**, found 2026-09-01: `beispiele/45` acknowledged \
                      `FSTS.PFO` through a read-modify-write on a word with two `w1c` \
                      fields, green in every pass and compiling under `-Werror`. \
                      `beispiele/gift`: 2 probes (`448` w1c, `449` rc), each `R012` alone; \
                      `218` now carries it as an accompanying code. \
                      `crates/gabbro-check/tests/komplement.rs` RUNS the repaired \
                      acknowledgement over a stand-in register window and demands the word \
                      `1` rather than `3`. Four hand mutations, built, all four caught.",
        fundstelle: "crates/gabbro-check/src/m3.rs (rmw_pruefung); \
                     crates/gabbro-syntax/src/kw.rs",
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
        name: "m1.umlauf_saettigung",
        kennungen: &["M153", "M154"],
        aussage: "The overflow operators check exactness at the operation: wrapping \
                  (`+%`, `-%`, `*%`, `<<%`) lives only on an exact unsigned range \
                  `0 .. 2^N-1` and answers it (`M153` elsewhere, naming `+|`), \
                  saturating (`+|`) lives on one shared integer range and answers \
                  it clamped (`M154` on two ranges). A literal operand takes the \
                  other's range when its value lies in it; two literals wrap in \
                  their common width. Neither ever takes the `M104` width path.",
        vorbehalt: "**Exactness is read off the operand ranges with their V1/V2 \
                    facts, not off the declarations**: a narrowed `0..3` is not \
                    exact and still falls. Mixed widths answer `Unbekannt`, like \
                    plain `+` -- no implicit conversion, and no refusal either. \
                    The shift amount is bounded, never exact. Says nothing about \
                    whether the lowered C computes the wrap -- that is the \
                    emitter's `umlauf_c`/`saettigung_c`, measured separately.",
        stand: Satzstand::Gemessen,
        gemessen_an: "crates/gabbro-check/tests/ueberlauf.rs: exact-shape \
                      acceptance (u32, u13, literals, signed saturation), \
                      `M153`/`M154`/`M104` refusals by code, emitted mask and \
                      helper-call shapes, compiled-and-run values.",
        fundstelle: "crates/gabbro-check/src/m1.rs (`umlauf_oder_saettigung`); \
                     PLAN-BITS.md section 4",
    },
    Satz {
        name: "m1.vorzeichenwechsel",
        kennungen: &["M150"],
        aussage: "Unary minus checks overflow at the operation (`M150`):
                  negating a full-range signed value into a range that cannot
                  hold `-INT_MIN` falls; narrowed and boundary-exact operands
                  stay silent.",
        vorbehalt: "**Reads facts, not declarations** (V1-narrowed `0..100`
                    silent beside an open parameter that falls). Unsigned
                    negation untouched.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/749-751: full-range fall, narrowed
                      silence, one-value-apart boundary.",
        fundstelle: "crates/gabbro-check/src/m1.rs",
    },
    Satz {
        name: "m1.bitintrinsik",
        kennungen: &["M157", "M158", "M159", "M160"],
        aussage: "The seven bit intrinsics (`clz`, `ctz`, `log2_floor`,
                  `popcount`, `rotl`, `rotr`, `bswap`) are typed at the call:
                  the nonzero group needs an operand whose range excludes zero
                  (`M157`); every operand must be an unsigned standard width
                  (`M158` for the unary group, `M159` for rotation, `M160` for
                  swap); rotation needs the exact full `uN` range and an amount
                  in `0 .. w-1` (`M159`); `bswap` needs `u16`, `u32` or `u64`
                  (`M160`). Results are exact: `0 .. w-1` for the nonzero
                  group, `0 .. w` for `popcount`, the full range for rotation
                  and swap -- so the lowering reaches `__builtin_clz/ctz`
                  only with a provably nonzero argument, whose undefined zero
                  case stays unreachable.",
        vorbehalt: "**Reads facts, not declarations**: a V1-narrowed `1 ..`
                    stays silent beside an open `u32` that falls at `M157`.
                    An `Unbekannt` operand stays silent (nothing to hold), and
                    an empty range is `M117`'s at the declaration. The sentence
                    says nothing about the C the call lowers to beyond the
                    zero case -- that the counted width is the declared one is
                    the emitter's own reading (`emit.rs::intrinsik_breite`).",
        stand: Satzstand::Gemessen,
        gemessen_an: "crates/gabbro-check/tests/rechenwerk.rs: one positive
                      probe per intrinsic (checked, emitted, compiled under
                      `cc` and `clang` with `-Wall -Wextra -Werror`, run under
                      both optimisation levels) and three poison probes
                      (`M157` on `u32`, `M159` on `u32 in 0 .. 5`, `M160` on
                      `u8`), each falling with its code alone.",
        fundstelle: "crates/gabbro-check/src/m1.rs (`intrinsik_ruf`,
                      `intrinsik_bereich`); crates/gabbro-check/src/emit.rs
                      (`intrinsik_c`, `DREH_C`)",
    },
    Satz {
        name: "namen.bitintrinsik-name",
        kennungen: &["N058"],
        aussage: "No declaration carries the name of a bit intrinsic (`N058`):
                  a call in one of the seven spellings never reaches a declared
                  callee, so a declaration of the same name would stand
                  uncalled -- a callee the language routes around. Locals and
                  parameters keep the names: they are not callees, and the call
                  form types as the intrinsic the way `u64(a)` converts despite
                  a local named `u64`.",
        vorbehalt: "**The rule holds items, not places.** A field or a local
                    named `clz` stays legal; only the item -- the thing a call
                    could resolve to -- is refused. It says nothing about
                    qualified paths (`m::clz`), which are ordinary calls and
                    fall where undeclared callees fall.",
        stand: Satzstand::Gemessen,
        gemessen_an: "crates/gabbro-check/tests/rechenwerk.rs: a `fn clz`
                      declaration falls with `N058` alone; the clean corpus
                      carries none of the seven names at any item.",
        fundstelle: "crates/gabbro-check/src/namen.rs
                      (`intrinsik_name_vergeben`)",
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
        kennungen: &["M127", "M128", "M129", "M141"],
        aussage: "A function pointer value comes only from `&f` where `f` is a declared \
                  function (`M127`), and it goes only into a slot it can stand in for. That \
                  is TWO independent conditions and they point in opposite directions. The \
                  CONTRACT is subsumed (`M128`): every effect `f` declares is one the slot \
                  allows, `f` costs at most what the slot promises, and the arity agrees -- \
                  a pointer may promise LESS than its slot, never more. The SIGNATURE is \
                  EQUAL (`M141`): each parameter type and the result are the same machine \
                  value on both sides, because nothing converts at an indirect call. A call \
                  through a place is admitted only where that place has a function pointer \
                  type (`M129`), and its arguments and result are held against the \
                  contract's. **What every pass downstream computes with at an indirect call \
                  is therefore a fact about some real function, not the wish written at the \
                  type.**",
        vorbehalt: "~~Subsumption is checked on the effect SET and the cost NUMBER, and on \
                    the arity -- **not on the parameter types**, which are compared only at \
                    the call.~~ **Closed 2026-09-02 by `M141`.** What is still NOT held is \
                    the declared RANGE of a number at a `fn(...)` slot: `u32 in 0 .. 9` and \
                    `u32` are one C type and one ABI, so `M141` passes them -- but a function \
                    declaring the narrower one accepts LESS than the slot promises, and a \
                    caller through the slot may hand it 1000. *`cc` cannot see that half at \
                    all*, and it is a CONTRAVARIANCE rule with its own direction, so it is \
                    booked in TODO.md rather than folded in here. Nor are parameter NAMES \
                    compared, and deliberately: a name at a pointer type binds nothing unless \
                    an effect line reads it (`ast::FnZeigerParam`). *The LOGIC refinement \
                    between the function's contract and the slot's is the sentence beside \
                    this one (`m1.fnzeigervertrag`): this sentence decides effects, costs, \
                    arity and signature, and nothing about logic.*",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: one probe each on `M127` (244), `M128` (241) and \
                      `M129` (245); the positive side is beispiele/49. **`M141` reproduced \
                      2026-09-02 against the UNCHANGED checker at all three stages**: `&eng` \
                      with `eng(b : u8) -> u8` in a `fn(u32) -> u32` slot gave `4 items, 0 \
                      errors, 0 hints` and `100 % coverage`, the emitter wrote `.f = &eng`, \
                      and `cc -Werror` refused it -- *initialization of `uint32_t \
                      (*)(uint32_t)` from incompatible pointer type `uint8_t (*)(uint8_t)`*. \
                      Two probes, one per reading: `608` falsifies a parameter, `609` the \
                      result (`void (*)(uint32_t)`), and the second is not a duplicate -- the \
                      result is reached only after every parameter passed. Speech test \
                      `crates/gabbro-check/tests/rechte.rs` drives BOTH directions, and the \
                      pair `u8` at a `u32` slot AND `u32` at a `u8` slot is the evidence that \
                      this is an equality and not `M128`'s subsumption; one row holds the two \
                      codes apart at an arity mismatch. **Zero sites in the corpus: all 468 \
                      files verdict-identical before and after.**",
        fundstelle: "crates/gabbro-check/src/m1.rs (fnptr_passt, fnptr_signatur_passt, \
                    darstellung_grund); SYNTAX.md fnptr",
    },
    Satz {
        name: "m1.fnzeigervertrag",
        kennungen: &["N295", "N296", "N297"],
        aussage: "A call through a function pointer is checked against the TYPE's contract \
                  as a direct call is checked against its callee's: the arguments are held \
                  against the slot's `requires` (`N295`, the weak `M115` reading -- refused \
                  where the argument's range excludes the condition), the arity is the \
                  slot's (`N296`, the `M143` reading -- the comparison runs on the overlap \
                  and reports beside it), and the answer is narrowed by the slot's \
                  `ensures` as by a direct callee's. Assigning or passing a NAMED function \
                  `&f` to the slot records the refinement implication as a `C` obligation \
                  in `gabbro obligations` (`N297` hints at the site): `requires_slot ⇒ \
                  requires_f` (contravariant) and `ensures_f ⇒ ensures_slot` (covariant). \
                  The implication is the user's logic and is decided by no pass.",
        vorbehalt: "**Two halves the checker does not take.** (1) Where the producer is \
                    unknown -- a slot behind a slot, a parameter of pointer type -- there \
                    is no one to owe the implication, and the question is the \
                    slot-subtyping one this lane leaves open; the decidable sides \
                    (`M128`/`M142`) still hold on every flow. (2) A `let` with a type \
                    ascription stores the DECLARED type, so an aliased `&f` behind an \
                    ascription loses its producer there (the flow that wrote it was \
                    already harvested); without an ascription the producer travels with \
                    the value. *Both are booked, not denied.* Nor is the `C` balance a \
                    proof: a counted implication is not a proved one, and the `V`-less \
                    silence at an indirect site that `N295` does not exclude is the \
                    user's, exactly as at a direct call under `M115`.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: `956` and the rewritten `247` falsify the slot's \
                      `requires` at an indirect call (`N295`, literal and ranged \
                      spelling); `959` and the rewritten `248` miscount the arity \
                      (`N296`); `957` (a stronger `requires` at `&f` than at the slot) \
                      and `958` (a stronger `ensures` at the slot than at `&f`) record \
                      the `C` obligation and hint (`N297`) -- both fail if the two \
                      directions swap. The positive sides are beispiele/126 (a \
                      comparator with its contract, sorted through the slot) and \
                      beispiele/127 (a driver callback over the slot's effects).",
        fundstelle: "crates/gabbro-check/src/m1.rs (zeigerverfeinerung_ernten, indirect \
                    call arm); SYNTAX.md fnptr",
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
    Satz {
        name: "m1.bereichsgrenzen",
        kennungen: &["M146"],
        aussage: "The ENDS of a declared integer range are integers. `type T = u32 in 0.5 \
                  .. 1.5;` checked with `0 errors, 0 hints` until 2026-09-08 and the bound \
                  reached nothing: `umgebung::intbereich` evaluates each end with \
                  `auswerten`, a float literal gives `None`, and the arm for an end that \
                  does not stand fast is `IntBereich::voll` -- the range does not get \
                  NARROWER, it is DROPPED, so the declaration lowers to the full width of \
                  the word and the model is handed `Shape.intIn 0 4294967295`. It walks \
                  every position a range can stand in: a type alias, a record field, a slot \
                  field, a `const`, a `static`, an `atomic`, a parameter, an answer, a \
                  local, an array element, a pointer target, a variant payload, a function \
                  pointer's parameter and result, an `accumulates`, an `axiom` parameter and \
                  answer, a `format` field, a table constant, and a `narrow` -- NINETEEN, \
                  and all nineteen were silent.",
        vorbehalt: "**A FLOAT LITERAL and not `an end that does not evaluate`**, and the \
                    narrower rule is the whole reservation: `u32 in 0 .. N` with an `N` this \
                    file cannot resolve -- an excerpt, a constant from another unit -- is \
                    exactly as silently widened and is NOT refused, because refusing it \
                    would be W10 in the expensive direction, a refusal with the sign that \
                    rejects a correct program. *An unresolvable end is a second finding with \
                    a second measurement.* **`floatty` is not touched**: `f64 in 0.5 .. 1.5` \
                    is the form the range was written for and `umgebung::gleitwert` reads \
                    it. **And at a `narrow` the PLACE decides**, because `narrowstmt` hangs \
                    a range on a place and not on a type: where the place does not resolve \
                    to an integer -- for any reason -- nothing is said.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured 2026-09-08 against the UNCHANGED checker, one probe per \
                      position, NINETEEN of nineteen `0 errors, 0 hints`; after the build \
                      nineteen of nineteen refuse and the `f64` row is still silent. The \
                      differential that says what the silence cost: `type T = <ty>` with a \
                      body `return 9;` gives 0 errors for `u32`, 1 error for `u32 in 0 .. \
                      1` and **0 errors for `u32 in 0.5 .. 1.5`** -- the fractional bound is \
                      the plain word. Poison: beispiele/gift/690. Over all 686 `.gab` files \
                      of the tree it falls in ZERO -- and it fell in ONE before the place \
                      was read at a `narrow`: beispiele/26-gleitkomma.gab:42, `narrow x to \
                      0.0 .. 1.0` at an `f64` parameter, which is the CORRECT spelling. *The \
                      corpus sweep found the over-reach, the design did not.*",
        fundstelle: "crates/gabbro-check/src/m1.rs; \
                     messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md §1.2; \
                     crates/gabbro-check/src/umgebung.rs::intbereich",
    },
    Satz {
        name: "m1.frische",
        kennungen: &["M147"],
        aussage: "No decision reads a stale-named local: beside the M1 fact set each body \
                  carries a taint map from locals to their source carriers, grown only at \
                  `let` with a carrier-read right-hand side (or a callee reads-hull), \
                  expired by any write naming the carrier -- own writes, loops (all), \
                  calls (writes-hull), never device registers -- and refused at decision \
                  positions only (branch/match condition, call argument, return, `narrow` \
                  subject, index), while storing or moving the name stays allowed.",
        vorbehalt: "**The literal `messung/netz/udp-echo.gab` still passes, BY DESIGN**: \
                    its bug is an omission no local holds, so no expiry can fire -- the \
                    rule catches the udp-echo shape (a named stale use), not the missing \
                    recompute. Growth is `let`-shaped only: a carrier read moved through \
                    a bare assignment or an `exchange`/`await` binding does not taint, \
                    and an indirect call names no hull. With ~0 natural stale-use sites \
                    the teeth are poison and mutation, not corpus bites -- the same \
                    standing as `H013`/`H101`/`H017`.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/702 (stale decision falls as `M147` alone) and /703 \
                      (fresh and re-read arms silent, stale control falls once).",
        fundstelle: "crates/gabbro-check/src/m1.rs; messung/FRISCHE-V4-ENTWURF.md",
    },
    Satz {
        name: "m1.rueckgabe_ohne_ergebnis",
        kennungen: &["M148"],
        aussage: "A `return` with a value stands only in a function that declares a result. \
                  `m1.rs` compared the value solely against the declared result (`if let \
                  Some(z) = ergebnis`), so a value in a result-less body fell through the \
                  `if` silently -- and the emitter writes it straight into a `void` \
                  function, where both C families refuse it (`-Werror=return-type`).",
        vorbehalt: "It says nothing about the TYPE of the value -- that stays `M101`'s, \
                    `M135`'s and `M140`'s where a result is declared. The bare `return;` \
                    stays silent: a result-less function ends in `return;` or falls to its \
                    closing brace, which SYNTAX.md reads as sugar for `return;`.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured 2026-09-12 against the UNCHANGED checker: \
                      beispiele/gift/776 carries `return m;` and `return 0;` in a function \
                      without `-> T`; `gabbro pruefe` said 0 errors, `gabbro emit` wrote \
                      `static void kreis` with four valued returns, and `cc` and `clang` \
                      refused every one of them. Poison is beispiele/gift/788, whose twin \
                      `gib` declares `-> u32` and keeps the same lines silent.",
        fundstelle: "crates/gabbro-check/src/m1.rs; beispiele/gift/776-*; \
                     beispiele/gift/788-return-carries-a-value-without-a-result.gab",
    },
    Satz {
        name: "m1.bare_atomic_place",
        kennungen: &["N270", "N271"],
        aussage: "A bare store to an `atomic` is refused (`N270`). `SPRACHE.md` §11.3 says \
                  every store to an atomic IS a `publishstmt`, so `AT = w` has no form -- and \
                  the bare store checked clean while emitting a plain store to an \
                  `_Atomic` object, which C treats as `seq_cst` against the declared \
                  order and which the C model (`C-SPEICHERMODELL.md` §1c) makes stuck. \
                  Lowering the bare store to an explicit `atomic_store_explicit` is no \
                  fix: the store is where the payload promise stands (`publishes { … }` \
                  / `publishes nothing`, held by V001-V004), and an explicit store \
                  without one would carry the pairing past the checker in silence. A \
                  suffixed place over an atomic is refused too (`N271`): the atomic is a \
                  scalar, so `AT[0]` names no element -- it checked clean (the indexed \
                  type falls out as untyped) and emitted an index into a scalar. The \
                  twin half is the emitter's: a bare READ lowers to \
                  `atomic_load_explicit` in the declared load order (a `release` \
                  declaration loads `acquire`), through the one place every runtime \
                  read funnels through -- expressions, `retry … until` conditions, \
                  narrow bounds, indices -- so the §1c census holds with no plain \
                  access left. Refusing the read instead would make payload-free \
                  atomics unreadable and the `retry`-spin inexpressible.",
        vorbehalt: "A parameter or `let` shadowing the atomic stays silent -- the store \
                    is theirs (`typ_von_ort` reads the local first), and the read lowers \
                    as the plain C local. `publishes` and `exchange` are their own \
                    statements and never reach the rule. The read lowering exempts the \
                    same four function-scoped views (parameters, `let`s, record values, \
                    traverse binders); a `match`/`awaits`/`alloc` binder shadowing an \
                    atomic name is not exempt -- no corpus site binds one, and the shape \
                    is booked, not closed.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/936-bare-store-to-atomic.gab falls with N270 ALONE \
                      (and `cc` still accepts the emitted C, hence `allein`); \
                      beispiele/gift/937-bare-store-despite-pairing.gab falls with N270 \
                      ALONE beside a live `publishes`/`awaits` pairing; \
                      beispiele/gift/939-index-into-atomic.gab falls with N271 ALONE. The silent \
                      direction is `beispiele/116` (payload-free counter, bare read \
                      lowering to a `relaxed` load) and `beispiele/117` (the \
                      `publishes`/`awaits` pair); the spin direction is \
                      `messung/proben/probe-transport-poll-used.gab`, whose `until` \
                      now reads `atomic_load_explicit` in the declared `acquire` order.",
        fundstelle: "crates/gabbro-check/src/m1.rs (N270, assignment arm); \
                     crates/gabbro-check/src/emit.rs (`ort`, bare atomic read); \
                     crates/gabbro-check/src/umgebung.rs (`atomare`, `nennt_atomic`); \
                     crates/gabbro-check/tests/bare_atomic.rs",
    },
    Satz {
        name: "m1.whole_array_store",
        kennungen: &["N287"],
        aussage: "A whole array is never a store target (`N287`): C has no assignment \
                  of one array to another, so `M[i] = M[j]` over a nested array -- and \
                  `B = A` over a flat one -- is refused, while `M[i][j] = v` stays \
                  silent. Both sides of the refused form carry the same array shape, \
                  so neither the shape comparison (`M140`) nor any range rule speaks; \
                  the emitter would write the assignment straight into the C, where \
                  `cc` answers *assignment to expression with array type*.",
        vorbehalt: "It holds the TARGET, not the source: a row into a scalar, or a \
                    scalar into a row, is `M140`'s shape mismatch where it stands. A \
                    row read into a `let` stays checker-silent and falls at the \
                    emitter (`C001`, no resolvable `let` type) -- a named refusal \
                    either way, and no corpus site binds one. `Publish` over an \
                    array-typed atomic is unmeasured and stays so: no corpus site \
                    declares one.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured against the UNCHANGED checker: `M[i] = M[j]` and `B = A` \
                      both checked clean and both named an array assignment `cc` \
                      rejects. Poison is beispiele/gift/951-nested-whole-row-store.gab \
                      (falls with N287 alone); the flat twin is pinned inline \
                      (`n287_flat_whole_array_store` in \
                      crates/gabbro-check/tests/nested_arrays.rs). The clean side is \
                      beispiele/122-matrix.gab (element stores at depth two).",
        fundstelle: "crates/gabbro-check/src/m1.rs (N287, assignment arm); \
                     crates/gabbro-check/tests/nested_arrays.rs",
    },
    Satz {
        name: "m1.sum_constructor",
        kennungen: &["N280", "N281", "N282", "N283", "N284"],
        aussage: "A `tagged` case constructs in a body as `Case(payload)`, `Case()` or \
                  the bare `Case` -- the surface of the model's `Expr.fall cs i nutz`: \
                  the case index is the declaration order, the payload is held against \
                  the case's type, and the construction answers the owning sum. A name \
                  that is neither a function nor a visible case falls (`N280`), as does \
                  a case two sums share (the index is read off ONE case list). The \
                  arity is the constructor's own: a missing payload (`N281`), a payload \
                  on a nullary case (`N282`), a bare name over a payload case (`N283`), \
                  labels at a case (`N284` -- a case carries its payload positionally, \
                  like `Some(x)`). The payload RANGE stays `M101`'s and its SHAPE \
                  stays out of the constructor rules -- a truth value against a \
                  number is `M135`'s crossing, anything else misshapen is `M140`'s \
                  -- all through the ordinary `passt`, and a wrong sum at the binding \
                  stays `M140`'s nominal rule. The lowering writes the SAME representation \
                  the `match` reads -- the compound literal `(T){ .marke = T_V, \
                  .last.V = … }` in bodies, the brace form at file scope -- and the \
                  call graph, the cost pass (one op, like `Some`) and the Lean export \
                  read the construction as a value, never as a call edge -- the graph \
                  carries no edge, costs prices the mark store, and `lean.rs` already \
                  carried the call form (`tagOf`) with the bare nullary form joining it.",
        vorbehalt: "A function of the same name wins, and anything the value namespace \
                    already binds wins at the bare form -- no behaviour change where a \
                    name already means something. A function of the name ANYWHERE in the \
                    unit blocks the construction (`N280`): the emitter reads callees \
                    unit-wide, so an invisible same-named function would take the call \
                    lowering while the checker typed a case. Integer words and their sugar \
                    never name a case (`return u13;` stays `M119`'s). A bare case bound in one \
                    `match` arm and read bare in another is typed as the case by the \
                    checker while the emitter withholds the literal -- loud through \
                    `cc`, booked and not closed. A `match` over a constructed (non-place) \
                    scrutinee stays the emitter's `C001`; the Lean bare-case term covers \
                    the nullary form only.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/944-unknown-variant-construction.gab falls with N280 \
                      (beside `H021`/`K003`, which own the call halves); \
                      beispiele/gift/945-variant-payload-out-of-range.gab falls with M101 \
                      (the range half, no constructor rule); \
                      beispiele/gift/946-payload-on-nullary-variant.gab falls with N282; \
                      beispiele/gift/947-missing-variant-payload.gab falls with N281; \
                      beispiele/gift/938-ambiguous-variant-construction.gab falls with N280 \
                      over two sums sharing `Kurz`. The silent direction is \
                      `beispiele/120` (call form and bare form constructed, matched \
                      exhaustively) and `beispiele/121` (both spellings at file scope, \
                      matched over the stored value); `N283`/`N284` are pinned by unit \
                      rows in `crates/gabbro-check/tests/variant_konstruktor.rs`.",
        fundstelle: "crates/gabbro-check/src/m1.rs (`ruf_roh` variant arm, bare-case arm, \
                     `variantenkonstruktor`); crates/gabbro-check/src/umgebung.rs \
                     (`variante`, `ist_variantenkonstruktor`, `hat_markierte`); \
                     crates/gabbro-check/src/emit.rs (`ruf`, `ort`, `wert_ctyp`, static \
                     brace form); crates/gabbro-check/src/aufrufgraph.rs (no edge); \
                     crates/gabbro-check/src/kosten.rs (one op); \
                     crates/gabbro-check/src/lean.rs (bare nullary term); \
                     crates/gabbro-check/tests/variant_konstruktor.rs",
    },
    Satz {
        name: "consts.evaluable",
        kennungen: &["K190"],
        aussage: "A `const` initializer, or a const-table element, outside the total, \
                  effect-free fragment falls (`K190`): carrier reads, layout queries, \
                  indirect calls and block-bodied calls do not fold, and the pass names \
                  the site instead of leaving the emitter's unnamed refusal.",
        vorbehalt: "It says nothing where another rule already speaks: division by zero \
                    stays `M102`'s, `~` stays the emitter's (`C001`, gift 445), floats \
                    stay silent (the fragment is integers), and scalar ranges stay \
                    `M101`'s. A recursive hull without `decreases` is `K008`/`K009`/\
                    `H022` where it stands, never `K190` -- recursion is their \
                    territory, even when a `const` calls into it.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/860 (a table read in an element falls as `K190` \
                      alone); the pure block-bodied call is pinned inline \
                      (`k190_reiner_aufruf_ohne_huelle` in \
                      crates/gabbro-check/tests/konstanten.rs). The clean side is \
                      beispiele/92-const-squares.gab and \
                      beispiele/93-const-scalars.gab.",
        fundstelle: "crates/gabbro-check/src/konstanten.rs (`pruefe_skalar`, \
                     `pruefe_tabelle`); dokumente/SYNTAX.md §1 (`arraylit`)",
    },
    Satz {
        name: "consts.table",
        kennungen: &["K191", "K194"],
        aussage: "A const-table literal holds exactly the declared count (`K191`), and \
                  every element evaluates inside the declared element range (`K194`). \
                  The literal is element-wise: nothing is filled in, and `m1` leaves \
                  the literal `Unbekannt` by construction, so no second rule ranges \
                  the same elements.",
        vorbehalt: "It checks the SHAPE, not the meaning: that the 64 entries are the \
                    squares is the Lean certificate (`Konstanten.quadrate64_zert`), not \
                    this rule. A length the declaration does not name (an unfoldable \
                    count) skips the count check -- the count's own `const` owes the \
                    refusal then, not the table.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/861 (two entries for three fall as `K191` alone) \
                      and /864 (`300` in a `u8` table falls as `K194` alone). The clean \
                      side is beispiele/92-const-squares.gab (64 folded entries, \
                      emitted and compiled).",
        fundstelle: "crates/gabbro-check/src/konstanten.rs (`pruefe_tabelle`); \
                     dokumente/SYNTAX.md §1 (`arraylit`)",
    },
    Satz {
        name: "consts.nested_rows",
        kennungen: &["N285", "N286"],
        aussage: "A nested const-table literal nests the way its type nests, row for \
                  row. A value where the type declares an array, or a row where it \
                  declares a single value, falls (`N285`); a row holding anything but \
                  the declared inner count falls (`N286`) -- a ragged row has no C \
                  shape, and nothing is padded or filled in. The outer count stays \
                  `K191`'s, and every leaf folds and ranges like a flat table's \
                  element (`K190`/`K194`), at whatever depth the nesting ends.",
        vorbehalt: "It checks the SHAPE, not the meaning -- like `consts.table` beside \
                    it. A scalar `0` where a nested table stands is NOT its shape: \
                    the flat `= 0` hole (`const T : [u32; 4] = 0;` emitting \
                    `#define T 0u`) stands unrepaired beside it, booked in lane 170, \
                    and this rule does not widen to close it. The call hull \
                    (`K192`/`K193`) descends through rows without a rule of its own: \
                    `alle_ausdruecke` carries every nested call and name to it.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/949 (`[[1, 2], [3]]` falls as `N286` alone); the \
                      `N285` directions are pinned inline (`n285_scalar_where_row_stands`, \
                      `n285_row_where_scalar_stands` in \
                      crates/gabbro-check/tests/konstanten.rs). The clean side is \
                      beispiele/123-const-matrix.gab (`[[1, 2], [3, 4]]` over \
                      `[[u32; 2]; 2]`, emitted and compiled).",
        fundstelle: "crates/gabbro-check/src/konstanten.rs (`check_eintrag`); \
                     dokumente/SYNTAX.md §1 (`arraylit`)",
    },
    Satz {
        name: "consts.callhull",
        kennungen: &["K192", "K193"],
        aussage: "Every function in a `const`'s call hull is `pure` (`K192`), and a \
                  reference cycle through a `const` falls (`K193`): a `const` carries \
                  no `decreases` by grammar shape, so a cycle through one is unbounded \
                  as const evaluation. The hull descends through single-return \
                  `const fn` bodies; anything else is opaque to it.",
        vorbehalt: "Non-recursive callees without `decreases` are accepted: the bound \
                    is owed where unboundedness lives, the same line `K008` draws. A \
                    cycle of functions ALONE stays `K008`/`K009`/`H022`'s -- this pass \
                    stays silent on it, including the `K190` it would otherwise owe. A \
                    recursive `const fn` WITH `decreases` still exceeds the \
                    single-unfolding folder and falls at `K190`, honestly named.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/862 (a `reads` callee falls as `K192` alone) and \
                      /863 (two consts naming each other fall as `K193`, once per \
                      member); the transitive impurity through a `const fn` is pinned \
                      inline (`k192_through_const_fn`). The clean side is the \
                      `quad` calls of beispiele/92-const-squares.gab.",
        fundstelle: "crates/gabbro-check/src/konstanten.rs (`hull_expr`); \
                     dokumente/SYNTAX.md §1 (`arraylit`)",
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
                    legitimate. **That is the difference to `R013`, which was added beside it \
                    on 2026-09-02**: rights DO have a lattice and narrow at a call, so the \
                    two halves of one pointer declaration are held by two rules pointing \
                    different ways. **`R001` remains the only other space test** (`raum == \
                    Dma` at an `ops` carrier); `code`, `boot` and `port` are still checked by \
                    nothing at all. \
                    \
                    **And from 2026-08-24 to 2026-09-04 this rule fired on every NAMED space \
                    against ITSELF.** `Raum::Benannt(Ident)` derived `PartialEq` over \
                    `{ text, span }` (`ast.rs`), so two DECLARATIONS of `ptr<user, r> u8` -- \
                    necessarily two different spans -- compared unequal, and `R008` refused a \
                    call with the same word on both sides of its own message. Found by «K3» \
                    (`messung/K3-BEFUND.md` §4.2), a corpus this project never wrote and never \
                    looked at while the checker stood: none of the 448 poison probes and none \
                    of the 67 clean examples ever passed a NAMED space to a call, so nothing \
                    here had ever exercised the comparison this rule's own claim rests on. \
                    Repaired by giving `Raum` a manual `PartialEq` that reads `Benannt` by \
                    `text` alone; probe `beispiele/68-named-space-matches-itself.gab` (pass) \
                    and `beispiele/gift/681-two-different-named-spaces-still-clash.gab` \
                    (still refuses two DIFFERENT names). A sweep of the whole tracked corpus \
                    before and after the repair changed the verdict of zero existing files.",
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
        name: "m3.zeigerrechte",
        kennungen: &["R013"],
        aussage: "A pointer argument that is a bare PARAMETER of the caller carries every \
                  access right the parameter it reaches demands. Rights NARROW at a call and \
                  never widen: a `rw` argument fits an `r` parameter -- the callee promises \
                  to do less than it could -- and an `r` argument does not fit a `rw` one. A \
                  callee may therefore act on the rights it declares without asking whether \
                  its caller ever had them.",
        vorbehalt: "**Compared are the three access atoms `r`, `w` and `x`, and NOT `own`.** \
                    Ownership is a linearity question and belongs to `R004`/`R007`; what this \
                    rule answers is what the holder may DO with the memory. `own` therefore \
                    counts AS read and write -- which is the emitter's own answer \
                    (`emit::zeiger_schreibend`, the one home of the `const` decision) and not \
                    a second one -- so a `rw` argument reaches an `own` parameter without a \
                    word, and whether ownership may be handed over at all is asked by nobody. \
                    **And it inherits `R008`'s under-approximation whole**: only a bare \
                    parameter name is compared, because `Typ::Zeiger(Box<Typ>)` drops the \
                    rights exactly as it drops `Raum`, and a field, a local, a `let`, a return \
                    value or a global carries no declared right this pass can read. *Carrying \
                    the rights in the semantic type is the same bigger fix `R008` names, and \
                    it is still not built.* `x` has one site in the whole corpus and that one \
                    is prose in `SPRACHE.md`, so the execute atom is written and unexercised.",
        stand: Satzstand::Gemessen,
        gemessen_an: "**Reproduced 2026-09-02 against the UNCHANGED checker before a line was \
                      written**, at all three stages: `beispiele/gift/607` gave `4 items, 0 \
                      errors, 0 hints`, the emitter wrote `static void ruft(const Text \
                      *restrict q) { schreibt(q); }` into a `Text *restrict` parameter, and \
                      `cc -O0 -Wall -Wextra -Werror` refused it -- *passing argument 1 of \
                      'schreibt' discards 'const' qualifier from pointer target type*. **The \
                      `N041` shape: the checker confirmed and the foreign compiler held the \
                      line.** Probe `beispiele/gift/607-pointer-rights-widen-at-a-call.gab`; \
                      speech test `crates/gabbro-check/tests/rechte.rs` drives BOTH directions \
                      -- 4 rows that must fall, 7 correct calls that must stay silent, \
                      including `rw + own` and `r + w` spelled out. **Zero sites in the \
                      corpus: all 468 files verdict-identical before and after**, which is the \
                      counter-direction, and `tests/gestalt.rs` had already pinned the \
                      narrowing row (*a wider right at a narrower slot*) before this rule \
                      existed.",
        fundstelle: "crates/gabbro-check/src/m3.rs::eigen_doppelt (beside `R008`); TODO.md",
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
        aussage: "A `progress X` names a declared and FALSIFIABLE assumption, a \
                  `decreases` measure names the traversal variable or a name the body \
                  writes, \
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
    Satz {
        name: "schleifen.nierueckkehr",
        kennungen: &["S009"],
        aussage: "A routine declared `-> never` does not come back, and its BODY says so: \
                  no `return` stands anywhere in it, and it does not fall off its end. \
                  `S006` two entries above asks the same question of a WATCHDOG and answers \
                  it from the callee's DECLARATION -- this is the half that was missing, \
                  because a declaration nobody holds against its body is a promise and not a \
                  fact. The cost of the silence is not a wrong answer but an unprovable one: \
                  `PLAN.md` §3.1 writes `False` into the `_post` of a `-> never` routine, so \
                  a body that returns hands the person a goal that is false because of a \
                  form the checker admitted.",
        vorbehalt: "**`extern` and `prim` declarations are not touched** -- there is no \
                    block to read, and the declaration is an assumption about foreign code, \
                    the sentence `E008` writes about extern effect lists. **The \
                    fall-off-the-end arm is `crate::endet_immer`'s answer and inherits its \
                    reservations**: divergence is decided from the LAST statement only, and \
                    a call counts as diverging only if its short name is in this unit's `-> \
                    never` list -- so a body ending in a call to a divergent routine of \
                    ANOTHER unit is refused, and that refusal is W10 in the expensive \
                    direction. *It is the same list `S002` has used since 2026-08-15 and the \
                    same reservation.* It says nothing about whether the routine actually \
                    diverges; that is `S003`/`S004`'s half and it is an assumption with a \
                    falsifier, not a proof.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured 2026-09-08 against the UNCHANGED checker, five bodies under \
                      `divergent fn q() -> never effects { diverges }`: `{ return; }`, `{ \
                      return 1; }`, `{ }`, `{ if b { return; } forever … }` and `{ forever … \
                      }` -- **all five `0 errors, 0 hints`**, and only the last is correct. \
                      After the build the first four refuse and the fifth passes. The C \
                      compiler was the only channel speaking: `cc -std=c11 -Wall -Wextra \
                      -Werror` on the emitted `_Noreturn void q(void) { return; }` answers \
                      *function declared 'noreturn' has a 'return' statement* and *'noreturn' \
                      function does return*. Poison: beispiele/gift/691. Over all 686 `.gab` \
                      files of the tree it falls in ZERO.",
        fundstelle: "crates/gabbro-check/src/schleifen.rs; \
                     messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md §1.3; \
                     programmlogik/PLAN.md §3.1",
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
        vorbehalt: "**`V004`/`V005` check the AWAIT side too (lane 45, 2026-09-10).** \
                    An `awaits` on a `relaxed` atomic -- or on one without any ordering \
                    word, which the emitter lowers to `memory_order_relaxed` on BOTH sides \
                    -- loads without acquire, so the pair goes to `relaxed_mit_last` and \
                    never reaches `erwartet`: no `V002` fires beside it. An `exchange … \
                    publishes` still moves its payload straight through, so `V004`/`V005` \
                    do not apply to it at all. If the base name does not resolve to a \
                    declared `atomic` (a device register, a foreign module), the store \
                    counts as an ordered publication -- fail-open in that direction. The \
                    superset is voluntary: no clause, no check.",
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
        vorbehalt: "**`V007` is the mirror image of `V006` since lane 45 (2026-09-10).** \
                    The read side descends into preceding sibling blocks via `leseziele`, \
                    the mirror of `schreibziele` -- a read inside an earlier `if` branch \
                    now counts. Branches of ONE `if` stay separate all the same: each is \
                    entered with the pre-statement state, so a read in one arm never taints \
                    an `awaits` in another. Descent into a statement's OWN blocks likewise \
                    uses the pre-statement state, so an `awaits` in a loop body does not \
                    see the reads behind it (`beispiele/41` stays silent; measured as a \
                    false positive without the snapshot). Both compare BASE NAMES only, so \
                    `n.a` before and `n.b` after counts as covered. And a payload written \
                    both before AND after the publish falls silently: the check skips any \
                    name already in the written set.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: 2 probes on `V006`, one on `V007`.",
        fundstelle: "crates/gabbro-check/src/paarung.rs; SPRACHE.md part II §1",
    },
    Satz {
        name: "paarung.neuvalidierung",
        kennungen: &["V011"],
        aussage: "A clean `awaits` binding read after a `Publish` to the same
                  carrier without a fresh revalidation falls (`V011`) --
                  branch-local, `Publish`-only, at V007 read positions.",
        vorbehalt: "**No concurrent-corpus churn** (measured 2026-09-11);
                    revalidated, other-carrier and publish-before-load arms
                    stay silent.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/755-757: stale use falls, fresh twin and
                      boundary stay silent.",
        fundstelle: "crates/gabbro-check/src/paarung.rs",
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
        kennungen: &["E001", "E002", "E003", "E004", "N305"],
        aussage: "`effects` is NOT fail-open: a function without an `effects` clause is a \
                  translation error, and whoever touches nothing writes `effects { pure }`. \
                  `pure` stands alone or not at all. The obligation falls at the ABSENCE, \
                  not at the content -- a tool that reads a missing clause as „no effects\" \
                  rewards leaving it out.",
        vorbehalt: "Only `fn` and `axiom` are looked at. A `device` transition (whose \
                    `effects` is optional), a `check`, a probe: no `E001`, no body \
                    comparison. `E003` is a HINT, so a `divergent fn` that does not name \
                    `diverges` passes. Since lane 191 an omitted clause over a body is \
                    DERIVED where the fixpoint settles — `E001` stays for functions \
                    without a body, and `N305` refuses the omission where nothing \
                    settles, with the reason.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes on `E001` and `E002`, probe `968` on `N305`. \
                      `E003` is a hint; `E004` has no probe.",
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
    Satz {
        name: "wirkungen.vertragsfuss",
        kennungen: &["E220", "E221"],
        aussage: "A contract is part of the frame: every known world carrier a `requires` \
                  (`E220`) or `ensures` (`E221`) clause reads is covered by a declared \
                  `reads` or `writes` effect -- unless no function of the program writes \
                  it at all, in which case it is read-only and needs no cover.",
        vorbehalt: "Parameters, quantifier binders, constants and unknown names are no \
                    world reads (the E010 line); `Has`/`Held` name a capability or a lock, \
                    not a read; calls into spec functions count only their arguments. \
                    `syscall`/`axiom` contracts, `maintains` and the `= pred ;` body of a \
                    `spec fn` are not read. Device registers read bare are outside known \
                    world state and stay silent -- the same boundary E010 draws.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/895-896 (requires/ensures over an undeclared \
                      written carrier) and 898 (the index path); read-only and covered \
                      twins pass.",
        fundstelle: "crates/gabbro-check/src/wirkungen.rs (`vertrag_gegen_wirkungen`)",
    },
    Satz {
        name: "wirkungen.fusswache",
        kennungen: &["E245", "E246", "E247", "E248", "E249"],
        aussage: "The footprint guard of the goal theorem: every carrier of a function \
                  footprint -- its `requires` (`E245`) and `ensures` (`E246`) carriers, \
                  its body reads (`E247`), the contract carriers of the functions it \
                  calls directly (`E248`) -- is guarded by a lock the function holds by \
                  signature (`requires Held(L)` over a `lock L protects` line), or no \
                  function of the program writes it. An indirect call (`E249`) is \
                  admitted only if every function behind the pointer keeps its contract \
                  carriers inside the caller footprint. All five report at hint level: \
                  the strict premise refuses ordinary single-threaded corpus programs, \
                  so the condition is exact and only the severity is not.",
        vorbehalt: "Same read detection as the E220/E221 leg (parameters, binders, \
                    constants, unknown names are no reads); device-rooted reads carry \
                    no footprint, the surface cannot declare their carriers. `syscall`/ \
                    `axiom` contracts, `maintains` and `= pred ;` bodies are not read. \
                    Lock identity is by short name; shared holding counts as holding. \
                    Candidates behind a pointer are the address-taken functions, else \
                    every function of the unit.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/930, 916-919 (one leg each, guarded twins pass); \
                      beispiele/110-111 (guarded and admitted shapes, fully silent). \
                      15 of 89 older examples fire -- the strictness finding, not new \
                      noise: readers over written carriers with no lock in the unit.",
        fundstelle: "crates/gabbro-check/src/wirkungen.rs (`footprint_against_guards`)",
    },
    Satz {
        name: "wirkungen.fusswache2",
        kennungen: &["N290", "N291", "N292", "N293", "N294"],
        aussage: "The flagship's decidable footprint premise (`FussS` with thread-local \
                  carriers and lock floors): every footprint carrier -- contract carriers \
                  (`N290`), body reads (`N291`), direct callee contracts at the call site \
                  (`N292`) -- is unwritten, guarded by a signature lock, protected by a \
                  lock invariant, or thread-local (no other started thread writes it). \
                  An indirect call (`N293`) is admitted over the same disjunction. A lock \
                  take or a callee take ranks strictly above every lock held by signature \
                  (`N294`, the floor). All five refuse as errors: the corpus stays green \
                  under the new rule, so every refusal is a real concurrent defect.",
        vorbehalt: "Threads are the `concurrent` members plus the `entry`/`boot` roots; \
                    with none the unit is single-threaded and every carrier is local. \
                    Call graphs come from `aufrufgraph.rs` (indirect calls union the \
                    address-taken pool). May-write is DECLARED permission, as in the \
                    model; holding at the access is `H007`'s question, not this one's. \
                    `N294` fires only against signature-held outers, where `H006`/`H012` \
                    stay silent; same-lock pairs are exempt there as here. Device reads, \
                    `syscall`/`axiom` contracts, `maintains` and `= pred ;` carry no \
                    footprint.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/124 (two-thread witness, silent), beispiele/125 (shared \
                      read under its lock, silent); beispiele/gift/952 (shared read, \
                      N291), 953 (contract leg, N290), 954 (callee leg, N292), 955 (floor, \
                      N294). 0 of 105 older examples refuse -- the analytic table stands \
                      in the lane report.",
        fundstelle: "crates/gabbro-check/src/fusswache2.rs",
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
                      shares. What is measured is the \
                      IMPLEMENTATION against tested cases, not the rule. See \
                      `messung/K001-DOMAENENSCHRANKE.md`.",
        fundstelle: "crates/gabbro-check/src/domaene.rs (line 82), umgebung.rs \
                     (`walkschranken`); MESSUNGEN.md:6307; SPRACHE.md:906",
    },
    Satz {
        name: "kosten.fristzahl",
        kennungen: &["K011"],
        aussage: "A `deadline <= N ops arch X falsifier p` dates with a NUMBER. The \
                  falsifier probes one number per run; a formula is not false, it is \
                  unprobable -- `K005` refused the same shape at `costs` for the same \
                  reason. What the number MEANS, honestly and tightly, is the \
                  writer's logic like `costs` itself: no pass re-measures a cycle \
                  count from the source.",
        vorbehalt: "No rule holds the two numbers against each other, and that is \
                    not an omission: `costs` counts Gabbro primitives, `deadline` \
                    counts cycles on `X` -- different units, and a comparison would \
                    be a conversion lemma wearing a rule's clothes.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/695: `deadline <= n * 2 ops …` over a parameter \
                      -- 2 items, 1 error, and it is `K011`. The unit names no \
                      `arch`, so `K012` stays silent (R16); the probe resolves \
                      nowhere, so `N056` stays silent with it.",
        fundstelle: "crates/gabbro-check/src/kosten.rs; beispiele/gift/695",
    },
    Satz {
        name: "kosten.fristmaschine",
        kennungen: &["K012"],
        aussage: "A `deadline … arch X …` names a machine the unit declares. Same \
                  question `A005` asks of an `assume`: a date on a machine that is \
                  never in force still travels in the artefact beside the assumption \
                  set, and a reader takes a reach out of it that does not exist. \
                  Without a single `arch` declaration nothing is refused (R16, same \
                  as at `A005`).",
        vorbehalt: "The probe the clause names is held by `N056` (same tail, same \
                    reading as `retires`): a probe that resolves in-unit must be \
                    able to refute, one that resolves nowhere is a program next to \
                    the tree. An `unfalsifiable` tail stays legal and marked -- the \
                    manifest entry carries the class, so an unprobed date never \
                    looks measured.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/696: `deadline <= 100 ops arch riscv …` with \
                      `arch x86_64` on the function -- 2 items, 1 error, and it is \
                      `K012`. The number reads, the probe resolves nowhere.",
        fundstelle: "crates/gabbro-check/src/kosten.rs; beispiele/gift/696",
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
        name: "m1.feld_traegt_der_traeger",
        kennungen: &["M134"],
        aussage: "A `.field` access is refused where the carrier's type is KNOWN and cannot \
                  carry it -- either the carrier is a record without that field, or it has no \
                  fields at all.",
        vorbehalt: "**It answers three situations that used to be one.** \
                    `umgebung.rs::feld_von` returned `Typ::Unbekannt` for *the carrier lacks \
                    this field*, *the carrier has no fields* and *the carrier's type never \
                    resolved* alike; two of those are defects and the third is honest \
                    ignorance. `Feldurteil` separates them, and where the type did not \
                    resolve the rule says NOTHING (W10) -- refusing there would hit exactly \
                    the programs M1 already reports as uncovered.\n\
                    **What it therefore does not reach:** a field access whose carrier is a \
                    `tagged type`, an array, a function pointer or `never`. Those return \
                    `Unklar` and are unmeasured, not cleared.\n\
                    **And the first build was WRONG, measured within the minute.** It did not \
                    know that the parameter list of a `device` is readable -- \
                    `messung/fragmente/F04.gab`:146 writes `q.AVAIL_IDX % q.n`, and F04 is \
                    DURCHGESTOCHEN: it emits, compiles under `-Werror` and runs. *A refusal \
                    there could only be the rule's own mistake.*",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes 411 and 412 on `M134` -- a `u64` carrier, and \
                      a declared record asked for a name it does not have. Counter-probe in \
                      messung/proben: record field, register field and DEVICE PARAMETER, 0 \
                      errors. Over the 418 `.gab` files it falls in ONE, \
                      `messung/fragmente/F05.gab`.",
        fundstelle: "crates/gabbro-check/src/m1.rs; \
                     crates/gabbro-check/src/umgebung.rs::feldurteil; \
                     messung/ZWEI-BLINDSTELLEN.md",
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
        name: "syscall.erklaerung",
        kennungen: &["N063", "N064", "N065", "N066", "N067", "N068", "A006"],
        aussage: "A `syscall` declaration holds its own shape: the in-registers are \
                  pairwise distinct (`N063`), no out register is clobbered (`N064`), \
                  every parameter is bound to exactly one register and every binding \
                  names a parameter (`N065`), every named register is an x86_64 general \
                  register (`N066`), the `errors` map answers every listed errno once \
                  and every target is a case of the declared `or R` channel (`N067`), a \
                  `kernel` pairing is refused until the pairing check lands (`N068`), \
                  and the declaration names no sealed architecture (`A006`, x86_64 \
                  only). The `arch` against the declared arches (`A005`) and the named \
                  assumption (`N004`/`N005` shape) are sentences of their own, and the \
                  call site reuses the `extern` path -- the `Signatur` in the shared \
                  map, the call-graph node, and `H007` at the boundary.",
        vorbehalt: "A declaration rule, and nothing else. It says nothing about whether \
                    the number is the kernel's, whether the errno table is the kernel's, \
                    or whether the assumption holds -- those are the counterpart's \
                    business and the falsifier's. A `regs out` pair has no \
                    reading and falls at the parser, not here; two out registers naming \
                    one register are not refused by any code above. The stub the emitter \
                    writes for a checked declaration is a sentence of its own \
                    (`syscall.stub`).",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes `830`/`831`/`835`/`836`/`837` on \
                      `N063`/`N064`/`H007`/`N065`/`N066`, `832`/`839`/`840` on the three \
                      directions of `N067`, `834` on `N068`, `833` on `A005` and `838` \
                      on `A006`; beispiele/74 checks clean and emits the stub, \
                      beispiele/90 the error path.",
        fundstelle: "crates/gabbro-check/src/syscall.rs; dokumente/SYNTAX.md §12.1",
    },
    Satz {
        name: "syscall.stub",
        kennungen: &["C180", "C181", "C182", "C183", "C184"],
        aussage: "A checked `syscall` lowers to one C function: every parameter in its \
                  declared in-register, the number in `rax`, the `syscall` instruction \
                  as extended inline `__asm__` with the declared clobbers plus `memory`, \
                  `rcx` and `r11`, and the raw `rax` answer decoded -- a negative \
                  `-4095..-1` against the `errors` map into the `or R` channel, an \
                  unlisted errno or an out-of-range non-negative value into the hardware \
                  outcome. Five shape rules guard the five places a plausible wrong stub \
                  would stand: no in-register the stub cannot keep (`C180` -- `rax` or a \
                  clobbered register), the answer in `rax` and not scratch (`C181`), the \
                  Linux x86_64 ABI and no other (`C182`), an integer answer with a \
                  checkable range (`C183`), and a number -- and every result bound -- \
                  that folds at translation time (`C184`).",
        vorbehalt: "A template rule, and nothing else. It says nothing about whether the \
                    kernel keeps the contract it decodes against -- that is the named \
                    assumption behind the stub (`Erhaltung.lean`: `syscallStub`), handed \
                    to the C compiler where no value can be delivered. The errno NAME is \
                    never held against a kernel table: the number compared is the \
                    reason case's DECLARED value, and a declaration that numbers its \
                    reasons differently than the kernel numbers its errnos decodes \
                    against its own numbers. A ghost parameter, an `errors` map with no \
                    channel, and an unresolvable reason stay the generic `C001`.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes `850`/`851`/`852`/`853`/`854` on \
                      `C180`/`C181`/`C182`/`C183`/`C184` -- each checker-clean, each \
                      refused by exactly its code; beispiele/74 runs the value path \
                      (a `write(1, \"ok\\n\", 3)` returns 3), beispiele/90 the `EBADF` path.",
        fundstelle: "crates/gabbro-check/src/emit.rs (`syscall_stumpf`); \
                     dokumente/SYNTAX.md §12.1; grammatik/Grammatik/Erhaltung.lean",
    },
    Satz {
        name: "parser.bibliothek-nutzlast",
        kennungen: &["P043"],
        aussage: "A `library fn` carries its `payload <table>` clause: the grammar \
                  line `fndecl` (`SYNTAX.md` §6, «E2») holds the clause behind the \
                  signature, so a library declaration without one falls at the \
                  reader, not in a pass behind it.",
        vorbehalt: "A shape rule of the parser, and nothing else. It says nothing \
                    about whether the named table EXISTS -- that check belongs to \
                    the checker (`N060`). Probes 826 (missing) and 820 (present) \
                    pin both directions.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probe 826 on `P043`.",
        fundstelle: "crates/gabbro-syntax/src/parse.rs; dokumente/SYNTAX.md §6",
    },
    Satz {
        name: "parser.bibliothek-rumpf",
        kennungen: &["P044"],
        aussage: "A `library fn` carries a Gabbro block body: the grammar admits \
                  only the `endblock` arm for it (`SYNTAX.md` §6, «E2»). A \
                  bodyless declaration would be a foreign promise -- exactly \
                  what the library mechanism stands against \
                  (`PLAN-ERWEITUNG.md` §0c) -- and a spec or sealed body leaves \
                  the hull check (`N059`) nothing to walk.",
        vorbehalt: "A shape rule of the parser, and nothing else. What the body \
                    must NOT call is a statement about the program and belongs \
                    to the checker (`N059`). Probe 827 pins the `;` form.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probe 827 on `P044`.",
        fundstelle: "crates/gabbro-syntax/src/parse.rs; dokumente/SYNTAX.md §6",
    },
    // --- lane 182, 2026-09-14: source trust (homoglyphs and bidi) ----------------------
    //
    // Gabbro's promise is that a HUMAN reads a body ("written by hand and read by a
    // person"); a program that reads differently to a human than to the parser breaks
    // exactly that premise (Trojan Source, CVE-2021-42574). Four refusals hold the four
    // classes: bidi control characters anywhere (`P060`, comments and strings included),
    // identifier characters outside the allowed set (`P061`), two scripts in one
    // identifier (`P062`), and invisible characters (`P063`, with the BOM-at-offset-0
    // exception). `P064` is booked with the lane and stays unissued.
    Satz {
        name: "quelle.zeichenvertrauen",
        kennungen: &["P060", "P061", "P062", "P063"],
        aussage: "The source reads the same to a human as to the parser: no bidi \
                  control character stands anywhere in the file (`P060`), every \
                  identifier is ASCII letters, digits and `_` plus ä ö ü ß Ä Ö Ü \
                  (`P061`), no identifier mixes two scripts (`P062`), and no \
                  invisible character stands anywhere except a BOM at offset 0 \
                  (`P063`). What cannot be seen is refused, never interpreted.",
        vorbehalt: "A shape rule of the reader, and nothing else. The script table \
                    is an approximation of UTS#39 (twelve families plus one \
                    rest), not the table itself -- two exotic scripts sharing \
                    one family would pass as one. And a homoglyph inside a \
                    COMMENT or a STRING is prose, not a name: only the bidi and \
                    invisible classes reach in there.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes 960 (`P060`), 961 (`P061`), 962 \
                      (`P062`) and 963 (`P063`); measured clean over 988 `.gab` \
                      files and every `gabbro` block of FRAGMENTE.md, SYNTAX.md, \
                      SPRACHE.md, README.md, MEMO-GLEITKOMMA.md and TUTORIAL.md.",
        fundstelle: "crates/gabbro-syntax/src/lex.rs::quelltext_pruefe; \
                     instrumente/pruefe-kennungen.py::quellvertrauen",
    },
    // --- lane E4, 2026-09-12: the monotone arena, checker half -------------------------
    //
    // **The structure lane of PLAN-ERWEITUNG.md §3.** A heap is allowed but never
    // unbounded: `arena A capacity lo .. hi of T` declares the reservation and the
    // hard bound, `let i = alloc A (v) else { … }` stores into the next free slot,
    // `A[i]` reads, and `reset A` starts a fresh generation. Five refusals hold the
    // five things no ordinary check can: unusable bounds (`N210`), a use outside
    // its generation (`N211`), a missing `else` past the reservation (`N212`), a
    // name that declares no arena (`N213`), and a place or index of another kind
    // (`N214`, at the one place that types every `Ort`).
    Satz {
        name: "arena.erklaerung",
        kennungen: &["N210", "N211", "N212", "N213", "N214"],
        aussage: "Every arena declares two constant bounds with `0 <= lo <= hi` \
                  (`N210`); every `alloc` past the reservation owes its `else` \
                  (`N212`, counted per function like `costs`); no index is read \
                  outside the generation its `alloc` bound it in (`N211`); \
                  `alloc` and `reset` name a declared arena (`N213`); and a \
                  place over an arena is exactly `A[i]` with `i : index into \
                  A`, never written outside `alloc` (`N214`). The emitted array \
                  holds exactly `hi` elements beside its `used` counter -- no \
                  heap allocation in the C -- and `reset` stores zero into the \
                  counter.",
        vorbehalt: "The count is per function body: two functions allocating into \
                    one arena share the runtime counter, and no static count sees \
                    the other -- like `costs`, whose recursion carries an \
                    assumption instead of a computation. A reservation shared \
                    across functions needs the whole-program discipline, and that \
                    is future work, not a silent promise. `beispiele/98` and \
                    `/99` carry the positive direction (emission included); the \
                    five poison probes pin the five refusals.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probe `885` on `N210` (inverted bounds), \
                      `886` on `N211` (stale index after `reset`), `887` on \
                      `N212` (missing `else` past the reservation), `888` on \
                      `N213` (undeclared arena), `889` on `N214` (foreign \
                      index); beispiele/98 checks clean and emits, /99 the \
                      boundary; counter-direction in `paesse.rs` (`arena_*`).",
        fundstelle: "crates/gabbro-check/src/arena.rs (`N210`-`N213`); \
                     crates/gabbro-check/src/m1.rs (`N214`); \
                     dokumente/SYNTAX.md §9.1; PLAN-ERWEITUNG.md §3",
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
        kennungen: &["O010", "O011", "O012", "O013"],
        aussage: "The boot theorem's third layer as ONE event. A token a `raw fn` demands is \
                  retired by some function (`O010`); the retiring clause and the `effects` \
                  block name the SAME token (`O011`); a postcondition over `mappings of` \
                  says, negatively, what is gone (`O012`); and the clause's own assumption \
                  tail is FALSIFIABLE (`O013`). Consuming the token and unmapping \
                  the space are therefore not two promises one can keep separately, and the \
                  half that leaves the checker leaves it with a probe on it.",
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
                    program. **`O013` reads the CLASS of the tail and nothing else**: that \
                    the named probe exists as a program is `manifest::gedeckt`'s question, \
                    that it can go red is `N056`'s, and that its reason is a good one is no \
                    pass's -- `dokumente/UNFALSIFIZIERBAR.md` carries that bar for a reader.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift: probes on `O010`, `O011`, `O012` and `O013`; \
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
        name: "sperren.fenster",
        kennungen: &["H018"],
        aussage: "A driver handoff holds ONE guard across both halves of the window \
                  (`H018`): a function that writes a DMA-visible buffer place AND rings \
                  the device doorbell does both under the same lock -- the checker half \
                  of the `GeraetWache` premise (`Geraet.lean`): handoff before the device \
                  write, take-back after, and the CPU side ordered against the endpoints.",
        vorbehalt: "**Three limits stand beside the rule.** (1) It reads DIRECT writes \
                    only -- a doorbell behind a `transition` call or an `extern fn` \
                    (like `beispiele/41`'s `klingel_ziehen`) is not a site, and a handle \
                    built inside the body is not a root. (2) It is intraprocedural: both \
                    halves have to stand in ONE function body. (3) Strength is not asked \
                    -- a shared-held guard orders as well as an exclusive one, and a \
                    declared `locks` effect counts as held exactly as under `H007`.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/724-726: the unguarded handoff, the handoff under \
                      two different guards, and the guard at one half only -- each with \
                      a guarded twin that stays silent. The clean corpus has zero sites: \
                      `beispiele/02` writes DMA registers with no doorbell in the same \
                      function, and `beispiele/41` rings the bell from behind an \
                      `extern fn`.",
        fundstelle: "crates/gabbro-check/src/geteilt.rs; \
                     grammatik/Grammatik/Geraet.lean (`GeraetWache`, C1)",
    },
    Satz {
        name: "sperren effects-locks-zeile",
        kennungen: &["H020"],
        aussage: "A direct write to a lock-protected place needs more cover
                  than the `effects { locks L }` line alone (`H020`).",
        vorbehalt: "**Exempt with named owners:** `spec fn`, `requires
                    Held(L)`, RCU-touched places, reads, calls. Disjoint from
                    `H007` by construction (no line is H007's case).",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/737 (must fall) and 739 (hull-redeemed
                      boundary); inline test h020_silence_and_single_fire_738
                      in beispiele.rs.",
        fundstelle: "crates/gabbro-check/src/geteilt.rs (`h020`)",
    },
    Satz {
        name: "sperren.invariante",
        kennungen: &["N275", "N276", "N277"],
        aussage: "A lock with an `invariant` clause carries a resource invariant over
                  exactly the carriers it protects: every carrier the predicate reads
                  stands in the lock's `protects` set (`N275`), the predicate is a pure
                  contract expression over a memory snapshot (`N276`), and every name
                  it uses is a protected carrier or a named constant (`N277`).",
        vorbehalt: "**Decided, never proved.** The checker holds the invariant's shape;
                    its TRUTH at every release is the user's obligation, recorded per
                    lock beside the `ensures` duties (`pflichten::Art::Sperrinvariante`)
                    and printed by `gabbro lean-g` as the `SperrInv` family -- like
                    `ensures`, it is counted, not discharged. **Three strictnesses stand
                    beside the rule.** (1) Option constructors are calls (`Some(x)` is a
                    `Ruf`), so an invariant over an option-index field is refused with
                    `N276`: there is no call-free spelling of the constructor. (2)
                    Quantifiers are refused with `N276` even over protected tables: the
                    export fragment (`lean_g.rs`) has no domain form for them. (3)
                    `N278`/`N279` stay reserved for the writer side and the release
                    shape; neither is refused here.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/940 (unprotected read, N275), 941 (`old`, N276),
                      942 (call, N276), 943 (unknown name, N277) -- each falls with
                      its code ALONE. The silent direction is beispiele/118 (two
                      functions, two carriers, one conserved-sum invariant) and
                      beispiele/119 (single carrier with a bound).",
        fundstelle: "crates/gabbro-check/src/sperrinv.rs",
    },
    Satz {
        name: "ableitung.kante",
        kennungen: &["H021"],
        aussage: "A dropped derivation edge falls once per (caller, target) --
                  unknown target, bodyless target without `effects`, or indirect
                  call without a contract at the pointer type (`H021`).",
        vorbehalt: "**Non-place arguments stay `E009`'s.** `Rand` lines,
                    compiler-supplied entries and pointer contracts stay
                    silent. Wired 2026-09-11 (lane-131 built the refusal
                    unwired); clean corpus draws zero H021, measured.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/740-742: stumm edge falls, resolvable
                      twin silent, publish-side pathless pair silent.",
        fundstelle: "crates/gabbro-check/src/ableitung.rs (`fehlende_kanten`)",
    },
    Satz {
        name: "pflichten.masslose-wechselrufe",
        kennungen: &["H022"],
        aussage: "Bare mutual calls without `decreases` fall once per member
                  (`H022`); `K008` keeps firing beside it.",
        vorbehalt: "**Wired 2026-09-11** (lane-133 built the detector
                    unwired); probes pin the exact sets (K008+H022).",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/746-748: mutual, half-measured and
                      three-member bare cycles.",
        fundstelle: "crates/gabbro-check/src/pflichten.rs (`zyklen_ohne_mass`)",
    },
    Satz {
        name: "emitter.reissstelle",
        kennungen: &["T001"],
        aussage: "A multi-instruction sequence on a shared carrier is refused
                  (`T001`): compound assign and merge triples need exclusive
                  access or single-writer-per-cell; single accesses pass.",
        vorbehalt: "**Parked, not wired.** The check module (`tearing.rs`,
                    14 unit tests over measured asm lines) and the hook point
                    (`emit.rs`, `Zuweisung` arm terminal) exist, but wiring
                    the gate red-flags `01-tabelle` and `05` whose discipline
                    is invisible in C text. Stand `Vermutet` until hooked and
                    measured.",
        stand: Satzstand::Vermutet,
        gemessen_an: "lane-47 asm lines as fixtures; `messung/TEARING-RULING.md`
                      per-form verdicts; hook spec in
                      `messung/TEARING-DURCHSETZUNG.md`.",
        fundstelle: "crates/gabbro-check/src/tearing.rs (unwired)",
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
    Satz {
        name: "sperren.ungeteilt",
        kennungen: &["H222"],
        aussage: "A carrier no declaration shares is own state: it is written by the code \
                  of at most one thread (`H222`). The computation is the W5 premise over \
                  the built `Bau` -- the same reachability H013 is built beside, extended \
                  by the thread witnesses, not a second one.",
        vorbehalt: "H013 refuses per entry (one context already shares with every other \
                    core in it); H222 refuses per carrier and only on a pair. No \
                    `ein_kern`/`masks` exemption: masking orders one core against \
                    preemption, while state written by two entries persists across both. \
                    Unknown carriers read shared (S5); unresolvable entries drop out (S4).",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/897 (two entries, one unshared write) and 899 \
                      (the transitive leg); single-thread and guarded twins pass.",
        fundstelle: "crates/gabbro-check/src/geteilt.rs (`H222`); bau.rs \
                     (`ungeteilt_mit_faeden`)",
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
    // --- «B39», 2026-08-31: the wiring between the rank pass and the entry ---------------
    //
    // **Born out of a COUNT, not out of a find.** `zaehle-verdrahtung.py` listed
    // `Entry / Lock` as one of 32 construct pairs that stand together in the corpus and that
    // no single pass function reads together. *Both halves had stood for months; what was
    // missing was the line that hangs them on each other.*
    Satz {
        name: "kontexte.handlersperre",
        kennungen: &["H102"],
        aussage: "An entry that hardware THROWS (`via idt`) takes no lock that fails to \
                  declare `masks irqs`: the path it interrupted may be holding that lock, \
                  and the handler would wait for a holder that only resumes once the \
                  handler returns.",
        vorbehalt: "**The trigger is `via idt`, and that leaves a gap this rule does not \
                    close.** `beispiele/57`'s `halt_ipi vector 0xF0` is thrown too, but it \
                    writes no `via`, so `Kontext::unterbricht` is false and `H102` stays \
                    silent over it. *That is a gap in the LANGUAGE -- `via` is the only \
                    place Gabbro says the difference -- and it is named here rather than \
                    papered over with a second answer to `what is an interrupt context` \
                    (a fourth register over the same set is W7).* And the remedy this rule \
                    demands is a PROMISE, not a lowering: the emitter writes no `cli`/`sti` \
                    out of `masks irqs`.",
        stand: Satzstand::Gemessen,
        gemessen_an: "Measured before the build: 39 lock declarations in the clean corpus, \
                      7 of them `masks irqs`; exactly ONE corpus file carries an `entry` \
                      AND a lock (`beispiele/57`), and that lock masks. **The clean corpus \
                      therefore has zero sites -- the evidence is poison** (Falle 80). \
                      `beispiele/gift/460` gave 0 errors before the rule and `[H102]` \
                      after; `beispiele/59` differs by ONE word and stays clean. **3 hand \
                      mutations, all BUILT: 1 caught at once, 2 went through all 283 \
                      probes** -- the `via idt` gate and the `locks shared ` prefix had no \
                      witness at all. Both now have one (`beispiele/59` module `ruf`, \
                      `beispiele/gift/461`), and the second is the sharper: without the \
                      prefix `locks shared TAKT` resolves to no lock and the rule falls \
                      silent through the SAME `continue` that lets an unknown lock pass. \
                      *A branch that stays quiet for two reasons and means only one.*",
        fundstelle: "crates/gabbro-check/src/kontexte.rs; «B39»",
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
        name: "namen.c_hat_den_namen",
        kennungen: &["N041"],
        aussage: "An item name that C has already taken is refused AT THE DECLARATION. The \
                  generator writes the Gabbro name into C unchanged, so a name C owns is a \
                  name no lowering can use -- and the refusal names which side of C owns it.",
        vorbehalt: "**The population is measured, and it is a measurement of ONE toolchain.** \
                    558 reachable names in three classes -- 37 C11 keywords (44 minus the \
                    seven Gabbro's own vocabulary refuses at `P002`), 366 from the four \
                    headers every generated unit includes, 155 built-in functions of the C \
                    implementation -- plus the hosted entry `main` as a fourth class of one \
                    (lane 73). The third class was measured file by file WITHOUT any \
                    `#include`; a different `cc` can know a different set, and then this \
                    table is a lower bound. *`messung/C-NAMEN.md` carries the command for \
                    every line of it.*\n\
                    **What it deliberately does NOT carry** (W10): the reserved prefixes of \
                    C11 §7.1.3. `__builtin_x`, `_Grosz` and `_klein` are reserved by the \
                    standard and MEASURED not to break, and the corpus holds zero item names \
                    with a leading underscore in 743. Rule A: no construct without a measured \
                    need. Nor does it carry the 883 underscore names the four headers define \
                    -- those are one libc's spelling, not C's.\n\
                    **And it does not look inside bodies.** A `let` or a parameter named \
                    `exit` lowers to a local, and a local shadowing a built-in is measured to \
                    compile.\n\
                    **The rule holds every named item except `module`, `use` -- and \
                    `extern fn`** (2026-09-01). At an `extern fn` taking C's name is the \
                    POINT, so the question is the signature and it is asked by `N046`. *Until \
                    that day this rule held it too, and no Gabbro program could print: \
                    `putchar`, `puts` and `printf` all stand in the table.* **The one \
                    exception to the exception is `main` (lane 73):** an `extern fn main` \
                    binds nothing a hosted unit may define -- the entry rule owns the \
                    hosted entry as a definition -- so it falls here, under `N041`, and \
                    never reaches `N046`.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/410-c-name-schluesselwort.gab (C11 keyword), 409 \
                      (a `<math.h>` name), 510 (a macro at an `extern fn`), 511 (`printf`, \
                      variadic), 796 (a `fn main` that is not the hosted entry); \
                      counter-probe messung/proben/probe-c-namen-frei.gab -- `read` `write` \
                      `open` `close` `signal` are POSIX, not C, and pass with 0 errors. \
                      **Recounted 2026-09-01 with its handle** (`W28`): over the 526 `.gab` \
                      files and their 1012 distinct item names the table has FOUR hits, three \
                      of them this rule's own poison probes. The single corpus site is \
                      `extern fn exit` in `messung/fragmente/F05.gab` -- the construct the \
                      rule no longer holds.",
        fundstelle: "crates/gabbro-check/src/namen.rs::name_gehoert_schon_c; \
                     crates/gabbro-check/src/cnamen.rs; messung/C-NAMEN.md",
    },
    Satz {
        name: "namen.extern_bindet_c_namen",
        kennungen: &["N046"],
        aussage: "An `extern fn` that names a function C already declares must lower to the \
                  SAME signature. Taking the name is the construct's purpose, so the name is \
                  not the question -- the question is whether `int32_t putchar(int32_t);` is \
                  what C knows, and `cc` refuses a declaration that disagrees \
                  (`-Wbuiltin-declaration-mismatch`). Where C's declaration cannot be written \
                  in Gabbro at all, `N041` still refuses and SHOWS that declaration.",
        vorbehalt: "**The signature table is measured and it covers 149 of the 558 names** \
                    (2026-09-02, `./instrumente/miss-c-signaturen.py`). The other 409 can be \
                    bound by no `extern fn` whatever its signature: 37 C11 keywords, 129 \
                    header macros (the preprocessor rewrites the name before the parser sees \
                    a declaration), 67 header typedefs, and 176 functions whose C declaration \
                    RETURNS a pointer or takes `char *`, `_Complex`, `long double` or a \
                    variadic list. *Each of the 149 was handed to `cc -std=c11 -O0 -Wall \
                    -Wextra -Werror` as the declaration `emit.rs` would write: 149 of 149 \
                    green.*\n\
                    **`void *` moved from the second list to the first on 2026-09-02, in a \
                    PARAMETER only.** A `void *` that comes IN takes the writer's own pointer \
                    and erases it -- Gabbro supplies precision C did not ask for, and the \
                    conversion is C's own. A `void *` that goes OUT would make Gabbro invent \
                    an element type nothing can check. *So `write`, `read`, `fwrite` and \
                    `memcmp` are bindable and `memcpy`, `memmove`, `memset` and `memchr` are \
                    not -- all four of the second group for their RESULT.*\n\
                    **And the unit then writes C's declaration and not this lowering** -- \
                    `emit.rs::aus_ctafel` reads the table's own column. For every `extern fn` \
                    that passed this rule before, the two are the same string; the one place \
                    they differ is a `void *` parameter, where C's word has to stand or `cc` \
                    disagrees with the real function the moment a POSIX header is in the same \
                    translation unit.\n\
                    **The equivalences are measured, not assumed.** `int == int32_t` and \
                    `long == int64_t` hold under LP64 and are checked by \
                    `_Static_assert(__builtin_types_compatible_p(...))`; `long long` FAILS \
                    that check against `int64_t` and is therefore absent, which keeps \
                    `llabs`, `llrint` and `llround` out of the table. A different toolchain \
                    can spell these differently, and then the table is a measurement of that \
                    one -- the same footing the 558-name table already stands on.\n\
                    **What it does NOT do** (W10): the comparison lowers only the types that \
                    need no unit context (`emit.rs::ctyp_primitiv`) plus `never` and a missing \
                    result, both `void`. A parameter typed by a `table`, a named range type or \
                    a pointer makes the comparison undecidable -- and then it REFUSES, it does \
                    not pass. *`_Noreturn` is outside the comparison: `cc` accepts \
                    `void exit(int32_t);` and `_Noreturn void exit(int32_t);` alike.* And it \
                    checks the declaration, never the definition on the C side: that the named \
                    function EXISTS is the linker's finding, not this pass's.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/63-druckt.gab -- `extern fn putchar(c : i32) -> i32`, 0 \
                      errors, the generated C compiles under `cc -std=c11 -O0 -Wall -Wextra \
                      -Werror` and the program prints `Hallo`. Poison probes 510-513. The \
                      counter-form `extern fn putchar(c : u32) -> u32` is refused by this \
                      rule AND by `cc`.",
        fundstelle: "crates/gabbro-check/src/namen.rs::extern_bindet_c_namen; \
                     crates/gabbro-check/src/cnamen.rs::SIGNATUR; \
                     instrumente/miss-c-signaturen.py",
    },
    Satz {
        name: "namen.endet_in_den_daten",
        kennungen: &["N052"],
        aussage: "An `extern fn` on a C function that finds the end of its data IN the data \
                  is refused -- not because Gabbro cannot spell `char *`, but because the \
                  obligation such a call puts on the caller cannot be written down. A \
                  pointer with no count beside it means the callee reads until it meets a \
                  terminator, and how far that is stands nowhere in the signature. What CAN \
                  be bound is what takes a count: `write(fd, p, n)` puts the end in the \
                  signature, `requires n <= N` states the obligation, and `M115` discharges \
                  it at the call site.",
        vorbehalt: "**This rule stands BEFORE the spelling refusal, and the order is the \
                    argument.** For `puts` both apply -- C says `const char *` and Gabbro has \
                    no `char` -- but only one survives a change to Gabbro: a `char` type \
                    would take `N041` away and leave the read unbounded. *The reason that \
                    does not depend on today's type table is the one that gets named.*\n\
                    **The population is DERIVED from the declarations and the derivation has \
                    four named exceptions** (44 names over both tables, \
                    `./instrumente/miss-c-signaturen.py --abschluss`). The test is *a `char \
                    *` parameter with no count beside it*. `snprintf`, `vsnprintf` and \
                    `strftime` carry a count that bounds the OUTPUT while the format string \
                    is still scanned; `strncat` carries one that bounds the READ while the \
                    write starts at the destination's own NUL. `strncpy` and `strncmp` look \
                    like the family and are NOT in it: both sides of each are bounded by the \
                    count.\n\
                    **What it does NOT claim** (W10): that a length-taking binding is safe. \
                    It is not -- `write(1, t, 999)` over a 64-byte buffer is the same memory \
                    error one argument over. The rule says the danger is EXPRESSIBLE and the \
                    checker already holds it, and says nothing about whether the writer chose \
                    the right bound. *A terminator scan leaves nothing to hold at all.*",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/630-puts-finds-its-end-in-the-data.gab, 631 (`strlen`), 632 \
                      (`strcpy`); the counter-form is beispiele/64-writes-a-whole-buffer.gab \
                      -- `extern fn write` with `requires n <= KAP`, 0 errors, compiled under \
                      `-Wall -Wextra -Werror` and RUN. And the obligation bites: with the \
                      argument out of range `M115` refuses (measured 2026-09-02, \
                      beispiele/gift/633-length-past-the-buffer.gab).",
        fundstelle: "crates/gabbro-check/src/namen.rs::extern_bindet_c_namen; \
                     crates/gabbro-check/src/cnamen.rs::ABSCHLUSS",
    },
    Satz {
        name: "namen.geraetezusage_nennt_ihre_stelle",
        kennungen: &["N053"],
        aussage: "Every place a `reg … requires` or a `transition … requires` names EXISTS: \
                  a bare name is a register of that device, a parameter of it, a bank of it, \
                  or something the unit declares at top level; a `.field` suffix on one of \
                  its registers is a field that register declares. A premise over a place \
                  that does not exist is a premise nothing can establish, and it is refused \
                  before it can be counted as an assumption.",
        vorbehalt: "**It does not decide whether the premise HOLDS, and that is deliberate.** \
                    `requires GSTS.RTPS == 1` is a statement about HARDWARE: the program \
                    cannot establish it, no pass should pretend to, and `1 == 2` in the same \
                    slot passes this rule in silence. It stays an assumption and is counted \
                    as one -- `gabbro pflichten` prints it under `D`, device promise. *The \
                    cheap and correct answer for an assumption is to make it visible where \
                    assumptions are counted, not to make a pass verify it* -- this rule takes \
                    only the half that needs no machine.\n\
                    **The known set is what THIS unit declares plus the last segment of every \
                    `use`,** the same limit `N033`, `S003`, `S007` and `H016` write down: an \
                    excerpt that names something outside the cut is refused rather than \
                    silently believed. A `Has(…)` argument is a machine feature and no place \
                    (`N016` reads those); a quantifier variable is bound by its quantifier. \
                    **Indices are not judged here** -- a literal index out of a table's \
                    `count` is `M141`, in the pass that already walks predicate positions.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/639-a-device-promise-over-a-field-that-is-not-there.gab \
                      (a `transition` premise over `GSTS.NICHTDA`) and \
                      beispiele/gift/640-a-register-promise-over-a-name-nobody-declares.gab \
                      (a `reg` premise over an undeclared `QMAX`); both fall with N053 ALONE. \
                      The silent direction is the corpus: all 19 sites of the three clauses \
                      (4 `reg`, 13 `transition`, 2 `axiom`) pass, and the whole-tree sweep on \
                      2026-09-02 produced exactly ONE finding -- \
                      `messung/fragmente/F04.gab`:73, a gap that file's own head had carried \
                      as open since 2026-08-20. And the calibration in the other direction: \
                      `requires 1 == 2` and `requires GSTS.RTPS == 99999` stay silent, \
                      because neither is a question this rule asks.",
        fundstelle: "crates/gabbro-check/src/namen.rs::geraetezusage_nennt_ihre_stelle",
    },
    Satz {
        name: "namen.geraetetraeger_nennt_traeger",
        kennungen: &["N255", "N257", "N258"],
        aussage: "Every entry of a `reg … depends { … }` names a CARRIER: a bare table or \
                  global of this unit (or a `use` tail, the N033/N053 house answer). A name \
                  nothing declares (`N255`), a declared item that holds no device state -- \
                  a lock, a device, a register, a bank, a function (`N257`) -- and a dotted \
                  place below carrier granularity (`N258`) are refused before they can enter \
                  any footprint: `GleichAuf` and `fussOrteG` cannot see a slot, so a clause \
                  that named one would establish a footprint the theorem never reads.",
        vorbehalt: "**The clause is named, not verified.** Whether the answer REALLY rests \
                    on those carriers is hardware (`RegLokal`): the program cannot establish \
                    it, no pass should pretend to, and the manifest lists it per register \
                    beside the named assumptions (`hardware (reglokal R)`). What this rule \
                    takes is only the half that needs no machine -- the same cut N053 makes \
                    one clause up. **The known set is this unit**, so a carrier written from \
                    another unit is missed, the N025/N038 reticence. And an imported name \
                    arrives without its kind: it reads as a carrier rather than as a \
                    refusal.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/925-depends-names-nothing-declared.gab (`N255`), \
                      beispiele/gift/927-depends-names-a-lock.gab (`N257`), \
                      beispiele/gift/928-depends-names-a-slot.gab (`N258`); each falls with \
                      its code ALONE. The silent direction is beispiele/112 and /113, whose \
                      `depends` clauses name tables and a global and pass.",
        fundstelle: "crates/gabbro-check/src/namen.rs::geraetetraeger_pruefen",
    },
    Satz {
        name: "namen.geraeteleser_haelt_wache",
        kennungen: &["N256"],
        aussage: "A function that reads a register with `depends` carriers holds, BY \
                  SIGNATURE, a lock guarding every carrier some function declares `writes` \
                  for -- `requires Held(L)` with the carrier in `L`'s `protects` -- or the \
                  carrier is written by no function at all. That is the decidable half of \
                  `ziel_ort_geraet`'s widened footprint check (`fussOrtGB`): the reader's \
                  sequential world agrees with the machine's on the footprint, hence on \
                  the device carriers, hence the sequential answer of a local oracle is \
                  the machine's answer.",
        vorbehalt: "**Signature only, and that is the theorem's shape, not the checker's \
                    strictness.** A lock taken in a `locks` block does not count -- the \
                    repaired machine has no bare lock steps -- and neither does a callee's \
                    hull: the check is per function over its own body, mirroring \
                    `fussOrteG`. **\"Written\" reads the DECLARED `writes` effects** (the \
                    surface of `D.schreibt`/`D.gschreibt`); generated ops force the \
                    caller's declaration, and a body write without declared cover is \
                    refused elsewhere. The strength of `Held` (shared or exclusive) is \
                    H001's question, not this rule's. The writer side -- a function that \
                    WRITES a device carrier owing the guard at its own access -- stays \
                    `H007`'s (`N259` reserved).",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/926-reader-without-signature-guard.gab (no `Held` at \
                      all) and beispiele/gift/929-reader-holding-the-wrong-lock.gab (a \
                       `Held` of a lock guarding elsewhere); both fall with N256 ALONE. The \
                     silent direction is beispiele/112 (guarded reader, written carrier) \
                     and beispiele/113 (unwritten carrier, no guard owed).",
        fundstelle: "crates/gabbro-check/src/namen.rs::geraetetraeger_pruefen",
    },
    Satz {
        name: "namen.immutable_null_pointer",
        kennungen: &["N260"],
        aussage: "An immutable pointer starting at `0` is refused. C11 6.3.2.3p3 \
                  makes the zero a null pointer constant -- the `(uintptr_t)` the \
                  emitter writes around it changes the spelling, not the address \
                  -- and 6.5.3.2p4 makes every dereference undefined behaviour. \
                  Without `mut` the binding can never name another address, so \
                  the null is permanent, not provisional: every use is a null \
                  dereference, measured with UBSan over `beispiele/38` before \
                  its repair.",
        vorbehalt: "**Three boundaries, all booked.** A `static mut` pointer \
                    starting at `0` stays silent -- the NULL-initialised global \
                    idiom, where assignment may precede any use, and that is \
                    flow, not a declaration. A nonzero number at a pointer slot \
                    is `M140`'s. Array decay is not a number at all. **An \
                    un-annotated `let` has no declared pointer type**; what its \
                    inferred zero becomes is `M140`'s at the use site.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/931-null-pointer-through-an-immutable-static.gab \
                      is refused with N260 ALONE. The silent direction is the \
                      `static mut` twin and the decay twin in \
                      `crates/gabbro-check/tests/null_pointer.rs`, \
                      `beispiele/64` (decay at a call), and the repaired \
                      `beispiele/38`, which binds its pointer to declared \
                      storage and holds no null spelling in its C.",
        fundstelle: "crates/gabbro-check/src/namen.rs::immutable_null_pointer",
    },
    Satz {
        name: "namen.erzeugter_name_zweimal",
        kennungen: &["N042"],
        aussage: "Two Gabbro declarations that get the SAME C name are refused at the second \
                  one. The generator forms C names out of a user name plus a fixed suffix \
                  (`{Format}_gueltig`, `{Tabelle}_NONE`, `{Walk}_knoten`, …) and writes the \
                  user name unchanged -- so a collision can arise between two names the \
                  generator built itself, neither of which is a C name and neither of which \
                  is a duplicate in Gabbro.",
        vorbehalt: "**The family is measured and it is NINE forms, not the one that found \
                    it** (`messung/ERZEUGERNAMEN.md` §2). Inside one carrier: a field named \
                    `gueltig`, a field `setz_a` next to a field `a`, a variant named `marke`, \
                    a bank register `setz_LO` next to `LO`. Across two: `table Kappe` next to \
                    `const Kappe_NONE`, `walk Baum` next to `type Baum_knoten`, `reason \
                    Fehler { Leer … }` next to `const Fehler_Leer`, `format Eintrag { a … }` \
                    next to `extern fn Eintrag_a`. All nine check with 0 errors, emit without \
                    a `C001`, and are refused by `cc`.\n\
                    **And the reason `cc` speaks at all is measured, and it is not the \
                    collision** (2026-08-31, `messung/STILLE-KOLLISIONEN.md`). `cc` refuses \
                    only where the two C types disagree, or where both sides define, or where \
                    the INTERNAL declaration comes second -- C11 6.2.2p4 lets a non-static \
                    declaration after a static one inherit the internal linkage, and the \
                    reverse order is the error. *The same two Gabbro declarations, swapped \
                    between two lines, give `cc` exit 0 and exit 1* (`m7-akk` against \
                    `m7b-akk`, byte-identical declarations). **A tool whose answer hangs on a \
                    line number is not an oracle for this question** -- that, and not the odd \
                    case it misses, is why the rule belongs here.\n\
                    So of the nine, **eight are structurally loud** (two definitions, two \
                    anonymous struct typedefs, two macros with different replacement lists -- \
                    C has no loophole there) and the ninth is loud only because the signature \
                    happened to differ: `format Eintrag { a … }` next to `extern fn \
                    Eintrag_a` with the MATCHING signature compiles clean, and the generated \
                    reader answers the writer's call (measured: 42 instead of the 999 in the \
                    writer's own archive).\n\
                    **Three sorts are silent by construction, and all three were RUN, not \
                    reasoned:** (A) external prototypes the generator never defines -- \
                    `{Lock}_nimm`, `{Rcu}_lese_start`, `gabbro_eintritt_{e}`, \
                    `gabbro_boot_{b}`, `gabbro_gast_{t}`, `gabbro_kern`; taking the lock ran \
                    the writer's body and no lock was taken. (B) external names the generator \
                    DEFINES -- `pruefe_{c}`; the writer's own archive member was never \
                    linked. (C) internal `static` names, silent whenever the generated \
                    declaration stands first. *Their probes carry the mirror contract \
                    `-- erwartet: N042 allein`: the checker must refuse AND `cc` must \
                    ACCEPT -- the day a second guard appears, the probe goes red and asks to \
                    be re-classified.*\n\
                    **What it deliberately does NOT enumerate** (W10): `{T}_speicher`, \
                    because the generator writes it only where the source addresses the table \
                    BY NAME and that set lives in the generator's `Namen`, not in the tree -- \
                    a listed name the generator never writes would be a refusal without a \
                    defect. The price is measured and stands as a probe of its own \
                    (`beispiele/gift/414`, contract `-- erwartet: cc`). Also left out: block \
                    labels (`{marke}_wachhund`) and everything inside a body, where a local \
                    shadowing a file-scope name is legal C.\n\
                    **And THREE names it lists only under a condition, each after a measured \
                    false positive** (2026-08-31): `{Atomic}_ORDER` -- the emitter writes the \
                    `#define` only where the ordering is not `relaxed`-without-payload, and \
                    `atomic Z : u32 relaxed` next to `const Z_ORDER` fell here while the unit \
                    held exactly ONE such name and `cc` was happy; \
                    `gabbro_eintritt_{e}_VEKTOR` -- written only for a LITERAL vector, so \
                    `vector NR` with a named constant writes none; and \
                    `gabbro_boot_{b}_s{i}` -- written only where the step calls a declared \
                    function, and `beispiele/07` names an `axiom` at four of its nine steps. \
                    *Same class as the `{T}_speicher` exclusion, with the difference that \
                    decides it: these conditions stand IN THE TREE and can be answered here.*\n\
                    **And it fires only where at least one side carries a GENERATOR-BUILT \
                    name.** Two equal plain declared names are a Gabbro duplicate and belong \
                    to `geltungsbereich` -- W7, one register per thing. That cut was measured, \
                    not guessed: without it the rule spoke a second time over five duplicate \
                    poison samples, and twice where there was no defect at all -- \
                    `beispiele/29-undurchsichtig.gab` (a prototype naming its definition in \
                    another module) and `messung/fragmente/F05.gab` (two `prim fn invoke` \
                    separated by `arch`).",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/413 (both forms: a `format` field spelled like the \
                      validity predicate, and one spelled like another field's writer; the \
                      contract moved from `-- erwartet: cc` to `-- erwartet: N042`); one probe \
                      per SILENT sort, each on the mirror contract `-- erwartet: N042 allein` \
                      -- 417 (`lock` beside `extern fn {L}_nimm`, sort A), 418 (`check` beside \
                      `extern fn pruefe_{c}`, sort B), 419 (`accumulates` beside `extern fn \
                      {n}_lies`, sort C, in the silent line order), 420 (`boot` beside `extern \
                      fn gabbro_boot_{b}` -- the address the machine jumps to); counter-probe \
                      messung/proben/probe-erzeugernamen-frei.gab -- six words that LOOK like \
                      generator suffixes and are none, 0 errors and `cc` accepts. Over the 446 \
                      `.gab` files of the tree the rule has hits in 413 and in those four \
                      probes and in the seven measurement files under \
                      messung/stille-proben/ -- and NOWHERE else.",
        fundstelle: "crates/gabbro-check/src/namen.rs::erzeugter_name_zweimal; \
                     crates/gabbro-check/src/erzeugernamen.rs; messung/ERZEUGERNAMEN.md; \
                     messung/STILLE-KOLLISIONEN.md",
    },
    Satz {
        name: "namen.kanal_ohne_einloeser",
        kennungen: &["N034"],
        aussage: "A function that declares `or R` has a body that can actually produce a \
                  reason -- a declared error channel with no writing site in its own body is \
                  a promise nobody can keep.",
        vorbehalt: "**This is the rule the whole stage is named after** -- *the generator \
                    first, the contract after.* It bites only where Gabbro SEES the body: \
                    at an `extern fn` the channel stays a pure assumption, and that is \
                    exactly where all six corpus sites stood before this run. *So the rule \
                    is silent on the majority of the surface, and it says so* (W10).",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/237-kanal-ohne-einloeser.gab.",
        fundstelle: "crates/gabbro-check/src/namen.rs",
    },
    // --- The report line of a `check`, resolved at last (2026-08-31) -------------------
    Satz {
        name: "namen.berichtszeile",
        kennungen: &["N043"],
        aussage: "Every base name under a `check`'s `measures` resolves to something the \
                  unit declares -- the list IS the report line (`SYNTAX.md` §13), and a \
                  name with nothing behind it describes a state that does not exist.",
        vorbehalt: "**The second subject weighs more than the first, and it is an ABSENT \
                    refusal, not a false one.** `N021` and `N022` find their quantity by \
                    matching a name against `measures`; a name that resolves to nothing \
                    matches nothing, so BOTH fall silent -- and the file looks exactly like \
                    one with nothing to report. *Measured, not supposed:* \
                    `messung/tor-proben/t11` is `beispiele/gift/155` byte for byte with \
                    `measures kk` for `measures k`, and `N021` disappears.\n\
                    **What it does NOT touch** (W10): the names inside `floor`. A predicate \
                    carries binders (`forall i in …`) and built-in forms (`lenof`, `old`), \
                    and resolving names without them would be a false refusal -- \
                    `messung/tor-proben/t12` measures that gap and it stays open. And the \
                    base is resolved against EVERY declared item, not only the places: a \
                    `measures` naming a function is a different mistake, and this rule does \
                    not claim it.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/421-measures-ins-leere.gab, exactly ONE refusal; \
                      1 mutation, caught. **The first run found two cases in the folder's \
                      own corpus:** `beispiele/gift/187-can-fail-schreibt.gab` named \
                      `tiefe_lebend` and `kerne_gemessen`, dropped when it was cut down \
                      from `beispiele/06` -- so `N022` was silent there about \
                      `floor kerne_gemessen >= 2` -- and `messung/fragmente/F06.gab` \
                      measures four fields of a carrier `eich` that the file does not \
                      declare. *The same place `N040` found its first case* \
                      (`messung/fragmente/F01.gab`). Zero hits over the clean corpus.",
        fundstelle: "crates/gabbro-check/src/namen.rs (`check_traegt_seine_pflicht`); \
                     messung/TORREICHWEITE.md; SYNTAX.md §13",
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
    // --- Lane C: declared concurrency (2026-09-10, NEBENLAEUFIGKEIT-ENTWURF.md) --------
    Satz {
        name: "nebeneinander.paar",
        kennungen: &["W001"],
        aussage: "Two bodies of one `concurrent` set write no place both: \
                  `writes(hull f) ∩ writes(hull g)` is empty over the transitive hulls. \
                  Shared reads may overlap freely; shared writes need a lock in BOTH \
                  hulls, a `publishes` pairing, or an `atomic` carrier. Same-table writes \
                  at different places fall too, unless lock-shared.",
        vorbehalt: "**The lock exemption is pair-level, not site-level** (open question 1): \
                    a common `locks L` in both hulls clears the pair even where neither \
                    body holds `L` across the access -- no held-set analysis exists. \
                    **Table identity is the SHORT name**: two modules declaring the same \
                    short table name in one unit read as one carrier. `per cpu` cells are \
                    NOT exempt by shape (open question 3): disjoint by core, refused \
                    without a common lock. `entrust` roots are skipped, not cleared (open \
                    question 2).",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/704-gleichzeitig-schreibt-gleiche-tabelle.gab (`W001` \
                      -- different rows of one table, no lock in either hull). The clean \
                      side is messung/proben/probe-nebeneinander-getrennt.gab (disjoint \
                      write sets, shared read, 0 errors).",
        fundstelle: "crates/gabbro-check/src/nebeneinander.rs; \
                     messung/NEBENLAEUFIGKEIT-ENTWURF.md §2",
    },
    Satz {
        name: "nebeneinander.geschlossen",
        kennungen: &["W002"],
        aussage: "Two context roots (`entry`/`boot` dispatch) whose hulls overlap in \
                  writes share a `concurrent` set: non-declared pairs are NOT concurrent, \
                  so an overlapping pair outside every set falls -- declare the pair or \
                  separate the writes.",
        vorbehalt: "**Asymmetric over incomplete hulls, and the asymmetry is built in**: \
                    on visible overlap the lower bound suffices to refuse (presence, not \
                    absence); where nothing is visible the pair stays silent -- the \
                    fail-closed half belongs to declared sets (`W003`). A root the graph \
                    cannot resolve is skipped here (`N018` already refuses the dangling \
                    `dispatch`).",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/705 (two entries over one `accumulates` cell, \
                      no set -- `W002` alone, no accompanying refusal: the cell is \
                      declared shared, so `H013` stays silent, and per-core cells \
                      are not exempt from the pair check).",
        fundstelle: "crates/gabbro-check/src/nebeneinander.rs; \
                     messung/NEBENLAEUFIGKEIT-ENTWURF.md §4",
    },
    Satz {
        name: "nebeneinander.unentscheidbar",
        kennungen: &["W003"],
        aussage: "A `concurrent` pair is checked only over COMPLETE hulls: a member that \
                  resolves to nothing, or whose hull is a lower bound (cycle, unknown \
                  callee), refuses instead of passing silently.",
        vorbehalt: "It refuses the DECLARATION, not the bodies: the two functions stay \
                    checkable on their own, and what falls is the claim that they may run \
                    together. Like `E009` it is the honest third state beside pass and \
                    refuse -- but here it bites (`Fehler`, not `Hinweis`), because an \
                    unchecked concurrency claim is not a frame anyone may rely on.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/706 (unresolvable member -- `W003` alone) and \
                      /707 (disjoint write sets behind a recursive hull: `W003` as \
                      the only refusal, `E009` beside it as Hinweis -- the shape of \
                      a missed race, clean-looking lower bound, refused).",
        fundstelle: "crates/gabbro-check/src/nebeneinander.rs; \
                     messung/NEBENLAEUFIGKEIT-ENTWURF.md §2 (`unvollstaendig` is fail-closed)",
    },
    // --- Lane 137: TRANSFER of `StartExklusiv` (goal premise over machine G) --------
    Satz {
        name: "nebeneinander.startexklusiv",
        kennungen: &["N240"],
        aussage: "The start functions of distinct threads have disjoint signature-held \
                  lock sets: no lock stands in `requires Held(L)` of two thread starts \
                  (`concurrent` members, `entry`/`boot` dispatch roots), at any strength.",
        vorbehalt: "**No strength exemption, by review**: `StartExklusiv` bans ANY common \
                    signature lock between distinct starts, and the model has no notion \
                    under which two `Held(L, shared)` starts are compatible -- a checker \
                    that accepts a program for which the goal premise is false is the \
                    defect the transfer phase exists to remove. Should a future model \
                    carry per-holder shared locks, this rule is where the relaxation \
                    lands. Unresolvable starts are skipped, not cleared (`W003` refuses \
                    the member, `N018` the dangling `dispatch`); `entrust` roots are \
                    skipped (the guest is unknown). Lock identity is the short name, \
                    like the pair check beside it.",
        stand: Satzstand::Gemessen,
        gemessen_an: "beispiele/gift/910 (two entries, one lock), /911 (declared \
                      pair, one lock) and /915 (boot root plus entry); /912 pins the \
                      same-function shape the audit excludes; /913 the shared-shared \
                      fall; /914 the exclusive-vs-shared fall. The clean side is \
                      beispiele/108 (declared pair, disjoint locks) and /109 (two \
                      entries over lock-free dispatch roots).",
        fundstelle: "crates/gabbro-check/src/startexklusiv.rs; \
                     grammatik/Grammatik/RufMaschineG.lean (`StartExklusiv`); \
                     grammatik/Grammatik/AuditZiel.lean (probe B)",
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
