//! The closed vocabulary.
//!
//! `SYNTAX.md` carries it as **one table** and says of it: *"Everything else is an identifier.
//! A new word is a language change and needs an entry here."* This file is the second version
//! of the same table, and `tests/wortschatz.rs` holds the two against each other -- otherwise
//! it would be a number a human runs parallel to the truth (trap 80).
//!
//! **AND THERE IS A RATCHET OVER THE NUMBER** -- `instrumente/zaehle-wortschatz.py`, two
//! marks, and together they are the rule of `PLAN-HARDWARE.md` §11 mechanically:
//!
//! > *A new word names either the word it displaces, or the measurement saying that no
//! > existing form carries it.*
//!
//! The first mark counts the words (221); the second counts the words WITHOUT a reason at
//! the entry (208). A swap leaves both standing, an addition raises the first, an addition
//! without a reason raises both. **A reason is a comment block of at least two lines
//! directly above the entry** -- it stands there and not in the commit message, because it
//! travels with the word. *Whoever raises a mark writes the ledger line beside it.*
//!
//! **Reserved versus contextual -- and since 2026-09-05 nearly the whole table is
//! contextual.** `messung/WORTSTELLUNG.md` holds the measurement and the decision.
//!
//! The rule used to be *"a word of the table is not an identifier"*, with three
//! single-letter exemptions and six words that a later measurement had to prise loose one at
//! a time (`tree`, `parent`, `child`, `sibling`, `observed`, `occupied`). **«K3» measured
//! what that costs against code written by somebody who has never heard of Gabbro**: over
//! 585 foreign files -- Linux `lib/`, `kernel/`+`mm/`, and Caprock -- **105 of the 221 words
//! are somewhere a name a programmer chose**, and 646 of the 1709 functions «K3» drew from
//! (37.8 %) bind at least one. Seven of the eight «K3» fragments carried one, and the
//! reader's refusal stopped the body from parsing, so everything behind it was invisible.
//!
//! **The rule is now the other one: a word is a keyword only where the grammar EXPECTS one.**
//! At a position where the grammar expects a NAME, every word of the table is a name.
//!
//! **`res` is down to SEVENTEEN of the 221, and every one of them is measured at ZERO
//! foreign declarator sites.** Two reasons, and they are different kinds of reason:
//!
//! * **ten head a primary expression or a predicate atom unconditionally**, so a variable of
//!   that name could be bound and never read back -- `sizeof` `lenof` `aligned` `forall`
//!   `exists` `true` `false` `Self` `Some` `None`. A name that can be written and not read is
//!   worse than one that is refused;
//! * **seven break the EMITTED C as an ordinary local** -- `const` `static` `extern` `if`
//!   `else` `return` `bool`. Measured, not assumed: one file per candidate with the four
//!   headers every generated unit includes and `uint32_t <w> = 1; return <w>;` through
//!   `cc -std=c11 -Wall -Wextra -Werror`. Six are C11 keywords, `bool` is `<stdbool.h>`'s
//!   macro. *They are exactly the seven `cnamen.rs` leaves out of its own tables on the
//!   grounds that this file refuses them, so the two statements stay true together.*
//!
//! **The two reasons meet on the same words for the same underlying fact:** a word no
//! programmer ever binds is a word whose reservation costs nothing. `true`, `false`, `if`,
//! `else`, `const`, `static`, `extern`, `return` and `sizeof` are C's own keywords and
//! `Some`/`None` are Rust's, so no C or Rust file can contain one as a name -- and in 585
//! foreign files none does.
//!
//! > **What this does NOT close** and what a later lane owes: `let int = 1;` emits
//! > `uint32_t int = 1;` and `cc` refuses it, with `gabbro pruefe` reporting `0 errors`.
//! > `N041` asks `cnamen.rs` about ITEM names only. Measured 2026-09-05 by the same method:
//! > **all 37 C11 keywords and 77 of the 366 header names break as a local**, none of the 155
//! > built-ins does. That hole is older than this change and none of the seven above is in it
//! > any more -- but `int`, `while` and `NAN` still are.
//!
//! **`tests/wortschatz.rs` holds this column against the parser word by word** -- it binds
//! every one of the 221 as a parameter and as a local, reads it back, and requires clean iff
//! the column says `ctx`. Without that the column would be a second register beside the
//! truth (trap 80), which is exactly what it was for the six words above.

macro_rules! wortschatz {
    ( $( $variant:ident => $text:literal , $klasse:ident ; )* ) => {
        /// A word of the closed vocabulary.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub enum Kw { $( $variant ),* }

        impl Kw {
            /// The spelling in the source.
            pub const fn text(self) -> &'static str {
                match self { $( Kw::$variant => $text ),* }
            }

            /// The word for a character sequence -- `None` means: identifier.
            pub fn suche(s: &str) -> Option<Kw> {
                match s { $( $text => Some(Kw::$variant), )* _ => None }
            }

            /// Reserved: not an ordinary name. Seventeen of 221 -- see the head of the file.
            pub const fn reserviert(self) -> bool {
                match self { $( Kw::$variant => wortschatz!(@klasse $klasse) ),* }
            }
        }

        /// All words, in the order of the table in `SYNTAX.md`.
        pub const ALLE: &[Kw] = &[ $( Kw::$variant ),* ];
    };
    (@klasse res) => { true };
    (@klasse ctx) => { false };
}

wortschatz! {
    // -- Structure -------------------------------------------------------------------------
    Module        => "module",        ctx;
    Pub           => "pub",           ctx;
    Use           => "use",           ctx;
    Type          => "type",          ctx;
    Opaque        => "opaque",        ctx;
    Linear        => "linear",        ctx;
    Ghost         => "ghost",         ctx;
    Tagged        => "tagged",        ctx;
    Const         => "const",         res;
    Static        => "static",        res;
    Fn            => "fn",            ctx;
    Spec          => "spec",          ctx;
    Impl          => "impl",          ctx;
    Raw           => "raw",           ctx;
    Divergent     => "divergent",     ctx;
    Prim          => "prim",          ctx;
    Extern        => "extern",        res;
    Section       => "section",       ctx;
    Arch          => "arch",          ctx;
    When          => "when",          ctx;

    // -- Contracts ------------------------------------------------------------------------
    Requires      => "requires",      ctx;
    Ensures       => "ensures",       ctx;
    Maintains     => "maintains",     ctx;
    // **`refines <path>` -- the head form of P6** (2026-08-24, `messung/VERFEINERUNG.md`).
    // A NEW word, deliberately: a refinement obligation is the strongest statement this
    // language makes about a body, and it must not arise from two names coinciding
    // (pairing by name) nor from a word doing double duty (`spec` as a clause).
    // *One word, one job -- and the closed vocabulary makes the change countable.*
    Refines       => "refines",       ctx;
    Breaking      => "breaking",      ctx;
    Effects       => "effects",       ctx;
    Costs         => "costs",         ctx;
    Decreases     => "decreases",     ctx;
    Where         => "where",         ctx;
    In            => "in",            ctx;
    Exhaustive    => "exhaustive",    ctx;
    Old           => "old",           ctx;
    Narrow        => "narrow",        ctx;
    To            => "to",            ctx;
    Induction     => "induction",     ctx;

    // -- Effects ------------------------------------------------------------------------
    Reads         => "reads",         ctx;
    Writes        => "writes",        ctx;
    Locks         => "locks",         ctx;
    Masks         => "masks",         ctx;
    Allocs        => "allocs",        ctx;
    Consumes      => "consumes",      ctx;
    Publishes     => "publishes",     ctx;
    Diverges      => "diverges",      ctx;
    Pure          => "pure",          ctx;

    // -- Control flow ---------------------------------------------------------------------------
    If            => "if",            res;
    Else          => "else",          res;
    Match         => "match",         ctx;
    Traverse      => "traverse",      ctx;
    Over          => "over",          ctx;
    By            => "by",            ctx;
    Touches       => "touches",       ctx;
    Retry         => "retry",         ctx;
    Forever       => "forever",       ctx;
    Until         => "until",         ctx;
    Bounded       => "bounded",       ctx;
    Progress      => "progress",      ctx;
    OnExceeded    => "on_exceeded",   ctx;
    PerPass       => "per_pass",      ctx;
    Return        => "return",        res;
    Let           => "let",           ctx;
    Mut           => "mut",           ctx;
    // **`decreasing` FELL here on 2026-09-01 -- 222 words, now 221.**
    //
    // It stood as a third run form beside these two, and the emitter had written down since
    // 2026-08-20 (stage 3) that it is not one: *"`by decreasing` -- the SAME as
    // `by unvisited`; the measure is a termination witness and says nothing about the run
    // that `unvisited` does not."* **Three modes, two runs.** A witness belongs to the
    // CONTRACTS, and the contracts already spell it: `decreases` at a `fn` head is the same
    // measure over the recursion that this one is over the passes («K5.4»).
    //
    // So the word it is displaced BY is `decreases`, which was already there -- the trade
    // this line is the ledger entry for. *Same move, same production, three days earlier:*
    // `invariant` went from the `table` to all three loop forms, and `SYNTAX.md` says of it
    // *"It is not a new word."*
    //
    // **And the grammar got wider while the vocabulary got smaller:** the three used to be
    // exclusive, so `by consuming decreases e` was unwritable; it is writable now.
    // `instrumente/zaehle-wortschatz.py` prints both numbers, and they moved in opposite
    // directions -- which is the only shape in which such a trade is one.
    Unvisited     => "unvisited",     ctx;
    Consuming     => "consuming",     ctx;
    Leave         => "leave",         ctx;
    Leaves        => "leaves",        ctx;
    Next          => "next",          ctx;
    Ops           => "ops",           ctx;
    // **«NL.1», 2026-08-19: die geschlossene Operationsmenge.** `opdecl` nahm bis dahin
    // beliebige Bezeichner, und damit war `table.ops.erhaltung` unbeweisbar in dem einen
    // Sinn, auf den es ankommt: aus einem NAMEN faellt keine Wirkung.
    //
    // Gemessen am zweiten Korpus (`kernel/` + `mm/`, 659 Dateien) vor der Entscheidung:
    // remove 479 · insert 448 · relabel 127 · replace 11. *`init` ist bewusst KEIN Wort --
    // `table … count N` konstruiert, und `table.absenkung` beweist es.*
    Insert        => "insert",        ctx;
    Remove        => "remove",        ctx;
    Relabel       => "relabel",       ctx;
    Result        => "result",        ctx;
    Exchange      => "exchange",      ctx;
    Update        => "update",        ctx;
    Returns       => "returns",       ctx;

    // -- Pointers ---------------------------------------------------------------------------
    Ptr           => "ptr",           ctx;
    Normal        => "normal",        ctx;
    Mmio          => "mmio",          ctx;
    Dma           => "dma",           ctx;
    Code          => "code",          ctx;
    Boot          => "boot",          ctx;
    R             => "r",             ctx;
    W             => "w",             ctx;
    Rw            => "rw",            ctx;
    X             => "x",             ctx;
    Own           => "own",           ctx;

    // -- Library -----------------------------------------------------------------------
    Format        => "format",        ctx;
    Table         => "table",         ctx;
    Slot          => "slot",          ctx;
    Invariant     => "invariant",     ctx;
    Reason        => "reason",        ctx;
    State         => "state",         ctx;
    Transition    => "transition",    ctx;
    Device        => "device",        ctx;
    Reg           => "reg",           ctx;
    Class         => "class",         ctx;
    // **`w1c` and `rc` stand HERE and not among the types** (2026-09-01, `OB4`).
    //
    // They stood in the `-- Types --` block beside `u8` and `bool` until today, and that
    // placement was not a filing mistake -- it was the whole defect in one line. **A
    // write-1-to-clear register is not a number of another type, it is an access
    // BEHAVIOUR**, and as long as it was filed as a type nothing treated it as one: the
    // emitter's read-modify-write asked the REGISTER's class, never the field's, and
    // `beispiele/45` shipped an acknowledgement of `PFO` that cleared `PPF` along with it.
    //
    // The two of them belong to `class`, beside `rw`/`r`/`w` -- those three live one block
    // up under `-- Pointers --` because a pointer right and a register class share the
    // spelling. *These two do not, and that is why they were the ones that drifted.*
    //
    // The refusal is `R012` in `m3.rs`; the word list is the place where it stops looking
    // like a type.
    W1c           => "w1c",           ctx;
    Rc            => "rc",            ctx;
    Fields        => "fields",        ctx;
    Bank          => "bank",          ctx;
    At            => "at",            ctx;
    Stride        => "stride",        ctx;
    Count         => "count",         ctx;
    // **Punkt 1: `count` ist ADRESSRAUM, `backed` ist SPEICHER.**
    //
    // Bis 2026-08-18 fiel beides zusammen, und damit war „30 GiB deklarieren, 100 MiB
    // hinterlegen" keine Aussage der Sprache, sondern eine Hoffnung an den Seitenfehlerpfad.
    // *Der Indextyp sagte `i < N`; gebraucht wird `i ist HINTERLEGT`.*
    Backed        => "backed",        ctx;
    Mirrors       => "mirrors",       ctx;
    From          => "from",          ctx;
    Assume        => "assume",        ctx;
    Falsifier     => "falsifier",     ctx;
    Unfalsifiable => "unfalsifiable", ctx;
    Axiom         => "axiom",         ctx;
    Lock          => "lock",          ctx;
    // **RCU -- und es ist KEINE Sperre.**
    //
    // Der zweite Korpus hat die Klasse gezeigt, die der erste nie zeigte (578 Leseseiten in
    // `kernel/`+`mm/`): die Leseseite nimmt GAR NICHTS, die Schreibseite tauscht einen Zeiger
    // und wartet auf eine Gnadenfrist. `lock`/`protects`/`rank`/`held` beschreibt
    // gegenseitigen Ausschluss; hier gibt es keinen.
    //
    // *Zwei Woerter, und die Maschinerie darunter ist die vorhandene.*
    Rcu           => "rcu",           ctx;
    Observes      => "observes",      ctx;
    // **Die Rueckgewinnung -- der Ort, an dem die Gnadenfrist etwas zu tun bekommt.**
    Reclaims      => "reclaims",      ctx;
    Group         => "group",         ctx;
    Protects      => "protects",      ctx;
    Rank          => "rank",          ctx;
    // «B37»: die ORDNUNG auf einer linearen Geistmarke. Zwei Woerter -- und zwar
    // ZWEI, nicht zwei je Bootschritt: die Stufen sind Bezeichner in EINER Deklaration.
    Order         => "order",         ctx;
    Advances      => "advances",      ctx;
    // **Layer S3 of the boot theorem -- the ONE event.** `advances` moves the token on,
    // `retires` ends it -- and names, in the same clause, the address space that goes with
    // it and the probe that could refute that. *Three parts, one clause: two promises one
    // can keep separately are not one.*
    Retires       => "retires",       ctx;
    Check         => "check",         ctx;
    Claim         => "claim",         ctx;
    Measures      => "measures",      ctx;
    Gates         => "gates",         ctx;
    CanFail       => "can_fail",      ctx;
    Floor         => "floor",         ctx;
    Counterprobe  => "counterprobe",  ctx;
    Expects       => "expects",       ctx;
    Endian        => "endian",        ctx;
    Little        => "little",        ctx;
    Big           => "big",           ctx;
    Reserved      => "reserved",      ctx;
    Cost          => "cost",          ctx;
    Runs          => "runs",          ctx;
    Online        => "online",        ctx;
    Offline       => "offline",       ctx;
    OffsetInto    => "offset_into",   ctx;
    Index         => "index",         ctx;
    Into          => "into",          ctx;
    Option        => "option",        ctx;
    Chain         => "chain",         ctx;
    Wrapping      => "wrapping",      ctx;
    Atomic        => "atomic",        ctx;
    Acquire       => "acquire",       ctx;
    Release       => "release",       ctx;
    Seq           => "seq",           ctx;
    Relaxed       => "relaxed",       ctx;
    Nothing       => "nothing",       ctx;
    Accumulates   => "accumulates",   ctx;
    Merge         => "merge",         ctx;
    Max           => "max",           ctx;
    Min           => "min",           ctx;
    Add           => "add",           ctx;
    Or            => "or",            ctx;
    And           => "and",           ctx;
    Held          => "held",          ctx;
    Shared        => "shared",        ctx;
    Embeds        => "embeds",        ctx;
    Scale         => "scale",         ctx;
    Walk          => "walk",          ctx;
    Levels        => "levels",        ctx;
    Node          => "node",          ctx;
    Down          => "down",          ctx;
    Leaf          => "leaf",          ctx;
    Mappings      => "mappings",      ctx;
    Entry         => "entry",         ctx;
    // **«entrust» -- ein `code`-Raum, dessen INHALT Gabbro nicht kennt.**
    //
    // Das eine Wort, das JIT, JVM und jedes Gastmodul oeffnet. Es erbt den Eintrittsvertrag
    // von `entry` -- und der war bis 2026-08-18 gemessen LEER: zwoelf Felder, und keine
    // Datei ausserhalb des Lesers nannte `EntryDecl`. *Wer `entrust` baut, baut ihn zum
    // ersten Mal.*
    Entrust       => "entrust",       ctx;
    Vector        => "vector",        ctx;
    Regs          => "regs",          ctx;
    Out           => "out",           ctx;
    Preserves     => "preserves",     ctx;
    Clobbers      => "clobbers",      ctx;
    Asm           => "asm",           ctx;
    Stack         => "stack",         ctx;
    Dispatch      => "dispatch",      ctx;
    Per           => "per",           ctx;
    Cpu           => "cpu",           ctx;
    Ist           => "ist",           ctx;
    Nested        => "nested",        ctx;
    Masked        => "masked",        ctx;
    Awaits        => "awaits",        ctx;
    Port          => "port",          ctx;
    Step          => "step",          ctx;
    Via           => "via",           ctx;

    // -- Domains -------------------------------------------------------------------------
    Slots         => "slots",         ctx;
    Of            => "of",            ctx;
    Descendants   => "descendants",   ctx;
    Ancestors     => "ancestors"  ,   ctx;
    // **«B41b»: die KANTE, an der `descendants of` und `ancestors of` laufen** (2026-08-20).
    //
    // Der Erzeuger hat den Befund selbst gestellt und beim Absenken abgelehnt: *„the domain
    // does not name the EDGE it walks -- `CapSpace` carries four candidates (parent,
    // first_child, next_sibling, prev_sibling), and `chain(a, b) in` shows the grammar
    // already knows how to name one. That is an asymmetry in the grammar."*
    //
    // **Die Symmetrie wird ANDERSHERUM hergestellt als `chain` es tut.** `chain(a, b) in
    // <ort>` nennt seine Felder an der Stelle; ein Baum wird aber an vielen Stellen
    // durchlaufen, und zwei Stellen koennten verschiedene Felder nennen, ohne dass irgendwer
    // die beiden vergleicht. **Die Kante ist eine Eigenschaft der STRUKTUR, nicht des
    // Durchlaufs** -- also steht sie einmal an der `table`, wird dort einmal geprueft
    // (`T001`-`T003`) und gilt fuer jede Domaene, die sie braucht.
    //
    // *Vier Woerter, und alle vier sind KONTEXTUELL* -- `parent`, `child`, `sibling` und
    // `tree` bleiben ueberall sonst Bezeichner, auch als Slotfeldnamen.
    // **«V9»: die Gegenseite steht in SILIZIUM** (2026-08-20).
    //
    // `V001` verlangt zu jeder Veroeffentlichung ein `awaits` -- *eine Veroeffentlichung ohne
    // Gegenstueck ordnet nichts*, und das ist richtig **zwischen zwei Stuecken Software**.
    // Bei einem Geraet gibt es kein zweites Programm: wer den avail-Index einer Virtqueue
    // liest, ist die Netzkarte.
    //
    // Gefunden beim ersten Treiber, der nicht aus dem Entwurf kam. Ohne die Klausel bleibt
    // nur, die Gegenseite als Funktion hinzuschreiben -- **dann steht das Modell im
    // Erzeugnis**, und ein Erzeugnis mit einer Luege darin ist schlechter als eine Weigerung.
    //
    // *Null neue Begriffe:* `assume`/`axiom` mit Falsifikator IST Gabbros Wort fuer eine
    // Aussage ueber die Maschine, und A10 bucht die Ordnungsaussage laengst dort. `by` steht
    // schon im Wortschatz; `observed` ist KONTEXTUELL.
    Observed      => "observed",      ctx;
    Tree          => "tree",          ctx;
    Parent        => "parent",        ctx;
    Child         => "child",         ctx;
    Sibling       => "sibling",       ctx;
    // **`occupied f` -- the field at which a slot is OCCUPIED** (2026-08-28, cut (c)).
    //
    // The generator for `ops` needs `sigma n = None` as a PROGRAM, and the corpus names that
    // field under **eleven** names (`belegt` 8, `benutzt` 6, `used` 3, `aktiv` 3, plus seven
    // singletons). *A name heuristic is thereby refuted, not doubted* -- word for word the
    // «B41b» finding, where the slot carried four candidates for the tree edge.
    //
    // CONTEXTUAL like `tree`: everywhere else, a slot field name included, it stays an
    // identifier. The decision, both sides per form: `messung/OPS-ERZEUGER.md`.
    Occupied      => "occupied",      ctx;
    Queue         => "queue",         ctx;
    Elems         => "elems",         ctx;
    Threads       => "threads",       ctx;
    Reaches       => "reaches",       ctx;

    // -- Types ----------------------------------------------------------------------------
    U8            => "u8",            ctx;
    U16           => "u16",           ctx;
    U32           => "u32",           ctx;
    U64           => "u64",           ctx;
    I8            => "i8",            ctx;
    I16           => "i16",           ctx;
    I32           => "i32",           ctx;
    I64           => "i64",           ctx;
    // -- «F»: f32 und f64. Der Wortschatz waechst um DREI Woerter, nicht um zwei --------
    //
    // `rounded` kam aus dem Korpus (F0): an 340 Literalen eines echten Renderers gemessen
    // waeren 53 abgelehnt worden, darunter ln 2 und 2 pi. Verboten ist nicht das Inexakte,
    // sondern das STILLSCHWEIGEND Inexakte -- und `wrapping` sagt dieselbe Sorte Satz ueber
    // den Ueberlauf. *Dieselbe Form, dieselbe Begruendung, kein neues Muster.*
    F32           => "f32",           ctx;
    F64           => "f64",           ctx;
    Rounded       => "rounded",       ctx;
    // Die Verengung, die Nicht-NaN-Sein herstellt: `narrow x to finite else { … }`.
    Finite        => "finite",        ctx;
    Bool          => "bool",          res;
    Never         => "never",         ctx;

    // -- Built-in ------------------------------------------------------------------------
    Sizeof        => "sizeof",        res;
    Lenof         => "lenof",         res;
    Aligned       => "aligned",       res;
    Forall        => "forall",        res;
    Exists        => "exists",        res;
    True          => "true",          res;
    False         => "false",         res;
    SelfWort      => "Self",          res;
    // «B35»: `option index into T` had no constructor. The corpus has always written
    // `Some(x)` -- in `match` patterns, in expressions and in SPRACHE.md:381 itself -- while
    // the grammar knew it nowhere. Pulled in per R9: the corpus decides.
    Some          => "Some",          res;
    None          => "None",          res;
}

// **The renaming table (`M-woerter`) stood here and is GONE** (2026-09-05).
//
// It named a German replacement for fourteen words -- `platz` for `slot`, `knoten` for
// `node`, `anzahl` for `count` -- and the reader printed it as a note under every refusal at
// a name position. Its own docstring stated the choice it was making: *"Of the three ways
// out -- contextual words, a position rule, renaming -- only the last carries the promise
// further: a softening for seven sites is a softening without measured need."*
//
// **The measured need arrived.** Seven sites in a corpus this project wrote itself became
// 105 words over 585 foreign files, and «K3» showed the refusal masking every later
// diagnostic in six of eight excerpts. The way out chosen then is the way the eight failed,
// and the table goes with it: there is nothing left to rename, because there is nothing left
// to refuse. *A note telling a user to rename his kernel's `node` WAS the plumbing.*
//
// The decision it recorded stays readable in the commit graph, which is what a rollback path
// is; `messung/WORTSTELLUNG.md` carries the measurement that replaced it.

impl Kw {
    /// The integer type words -- `intty` in the grammar.
    /// Die Gleitkommawoerter -- `floatty` in der Grammatik.
    pub const fn ist_floatty(self) -> bool {
        matches!(self, Kw::F32 | Kw::F64)
    }

    /// Die Breite in Bits. **Getrennt gefuehrt, weil die Mantisse daran haengt:** 24 Bit bei
    /// `f32`, 53 bei `f64` (je einschliesslich des impliziten Bits).
    pub const fn mantisse(self) -> u32 {
        match self {
            Kw::F32 => 24,
            _ => 53,
        }
    }

    pub const fn ist_intty(self) -> bool {
        matches!(
            self,
            Kw::U8 | Kw::U16 | Kw::U32 | Kw::U64 | Kw::I8 | Kw::I16 | Kw::I32 | Kw::I64
        )
    }
}

impl core::fmt::Display for Kw {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.text())
    }
}
