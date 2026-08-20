//! The closed vocabulary.
//!
//! `SYNTAX.md` carries it as **one table** and says of it: *"Everything else is an identifier.
//! A new word is a language change and needs an entry here."* This file is the second version
//! of the same table, and `tests/wortschatz.rs` holds the two against each other -- otherwise
//! it would be a number a human runs parallel to the truth (trap 80).
//!
//! **Reserved versus contextual.** A word of the table is not an identifier. Exempt are the
//! **single-letter** words `r`, `w`, `x`: `pruefe-wortschatz.py` itself excludes them from the
//! coverage check (*"single-character terminals come from character ranges and are not
//! words"*), and `FRAGMENTE.md` binds `Reply(r)`. At their sites -- `rights`, `class` -- they
//! are recognised by text and are identifiers everywhere else.

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

            /// Reserved: an identifier nowhere.
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
    Module        => "module",        res;
    Pub           => "pub",           res;
    Use           => "use",           res;
    Type          => "type",          res;
    Opaque        => "opaque",        res;
    Linear        => "linear",        res;
    Ghost         => "ghost",         res;
    Tagged        => "tagged",        res;
    Const         => "const",         res;
    Static        => "static",        res;
    Fn            => "fn",            res;
    Spec          => "spec",          res;
    Impl          => "impl",          res;
    Raw           => "raw",           res;
    Divergent     => "divergent",     res;
    Prim          => "prim",          res;
    Extern        => "extern",        res;
    Section       => "section",       res;
    Arch          => "arch",          res;
    When          => "when",          res;

    // -- Contracts ------------------------------------------------------------------------
    Requires      => "requires",      res;
    Ensures       => "ensures",       res;
    Maintains     => "maintains",     res;
    Breaking      => "breaking",      res;
    Effects       => "effects",       res;
    Costs         => "costs",         res;
    Decreases     => "decreases",     res;
    Where         => "where",         res;
    In            => "in",            res;
    Exhaustive    => "exhaustive",    res;
    Old           => "old",           res;
    Narrow        => "narrow",        res;
    To            => "to",            res;
    Induction     => "induction",     res;

    // -- Effects ------------------------------------------------------------------------
    Reads         => "reads",         res;
    Writes        => "writes",        res;
    Locks         => "locks",         res;
    Masks         => "masks",         res;
    Allocs        => "allocs",        res;
    Consumes      => "consumes",      res;
    Publishes     => "publishes",     res;
    Diverges      => "diverges",      res;
    Pure          => "pure",          res;

    // -- Control flow ---------------------------------------------------------------------------
    If            => "if",            res;
    Else          => "else",          res;
    Match         => "match",         res;
    Traverse      => "traverse",      res;
    Over          => "over",          res;
    By            => "by",            res;
    Touches       => "touches",       res;
    Retry         => "retry",         res;
    Forever       => "forever",       res;
    Until         => "until",         res;
    Bounded       => "bounded",       res;
    Progress      => "progress",      res;
    OnExceeded    => "on_exceeded",   res;
    PerPass       => "per_pass",      res;
    Return        => "return",        res;
    Let           => "let",           res;
    Mut           => "mut",           res;
    Unvisited     => "unvisited",     res;
    Consuming     => "consuming",     res;
    Decreasing    => "decreasing",    res;
    Leave         => "leave",         res;
    Leaves        => "leaves",        res;
    Next          => "next",          res;
    Ops           => "ops",           res;
    // **«NL.1», 2026-08-19: die geschlossene Operationsmenge.** `opdecl` nahm bis dahin
    // beliebige Bezeichner, und damit war `table.ops.erhaltung` unbeweisbar in dem einen
    // Sinn, auf den es ankommt: aus einem NAMEN faellt keine Wirkung.
    //
    // Gemessen am zweiten Korpus (`kernel/` + `mm/`, 659 Dateien) vor der Entscheidung:
    // remove 479 · insert 448 · relabel 127 · replace 11. *`init` ist bewusst KEIN Wort --
    // `table … count N` konstruiert, und `table.absenkung` beweist es.*
    Insert        => "insert",        res;
    Remove        => "remove",        res;
    Relabel       => "relabel",       res;
    Result        => "result",        res;
    Exchange      => "exchange",      res;
    Update        => "update",        res;
    Returns       => "returns",       res;

    // -- Pointers ---------------------------------------------------------------------------
    Ptr           => "ptr",           res;
    Normal        => "normal",        res;
    Mmio          => "mmio",          res;
    Dma           => "dma",           res;
    Code          => "code",          res;
    Boot          => "boot",          res;
    R             => "r",             ctx;
    W             => "w",             ctx;
    Rw            => "rw",            res;
    X             => "x",             ctx;
    Own           => "own",           res;

    // -- Library -----------------------------------------------------------------------
    Format        => "format",        res;
    Table         => "table",         res;
    Slot          => "slot",          res;
    Invariant     => "invariant",     res;
    Reason        => "reason",        res;
    State         => "state",         res;
    Transition    => "transition",    res;
    Device        => "device",        res;
    Reg           => "reg",           res;
    Class         => "class",         res;
    Fields        => "fields",        res;
    Bank          => "bank",          res;
    At            => "at",            res;
    Stride        => "stride",        res;
    Count         => "count",         res;
    // **Punkt 1: `count` ist ADRESSRAUM, `backed` ist SPEICHER.**
    //
    // Bis 2026-08-18 fiel beides zusammen, und damit war „30 GiB deklarieren, 100 MiB
    // hinterlegen" keine Aussage der Sprache, sondern eine Hoffnung an den Seitenfehlerpfad.
    // *Der Indextyp sagte `i < N`; gebraucht wird `i ist HINTERLEGT`.*
    Backed        => "backed",        res;
    Mirrors       => "mirrors",       res;
    From          => "from",          res;
    Assume        => "assume",        res;
    Falsifier     => "falsifier",     res;
    Unfalsifiable => "unfalsifiable", res;
    Axiom         => "axiom",         res;
    Lock          => "lock",          res;
    // **RCU -- und es ist KEINE Sperre.**
    //
    // Der zweite Korpus hat die Klasse gezeigt, die der erste nie zeigte (578 Leseseiten in
    // `kernel/`+`mm/`): die Leseseite nimmt GAR NICHTS, die Schreibseite tauscht einen Zeiger
    // und wartet auf eine Gnadenfrist. `lock`/`protects`/`rank`/`held` beschreibt
    // gegenseitigen Ausschluss; hier gibt es keinen.
    //
    // *Zwei Woerter, und die Maschinerie darunter ist die vorhandene.*
    Rcu           => "rcu",           res;
    Observes      => "observes",      res;
    // **Die Rueckgewinnung -- der Ort, an dem die Gnadenfrist etwas zu tun bekommt.**
    Reclaims      => "reclaims",      res;
    Group         => "group",         res;
    Protects      => "protects",      res;
    Rank          => "rank",          res;
    // «B37»: die ORDNUNG auf einer linearen Geistmarke. Zwei Woerter -- und zwar
    // ZWEI, nicht zwei je Bootschritt: die Stufen sind Bezeichner in EINER Deklaration.
    Order         => "order",         res;
    Advances      => "advances",      res;
    Check         => "check",         res;
    Claim         => "claim",         res;
    Measures      => "measures",      res;
    Gates         => "gates",         res;
    CanFail       => "can_fail",      res;
    Floor         => "floor",         res;
    Counterprobe  => "counterprobe",  res;
    Expects       => "expects",       res;
    Endian        => "endian",        res;
    Little        => "little",        res;
    Big           => "big",           res;
    Reserved      => "reserved",      res;
    Cost          => "cost",          res;
    Runs          => "runs",          res;
    Online        => "online",        res;
    Offline       => "offline",       res;
    OffsetInto    => "offset_into",   res;
    Index         => "index",         res;
    Into          => "into",          res;
    Option        => "option",        res;
    Chain         => "chain",         res;
    Wrapping      => "wrapping",      res;
    Atomic        => "atomic",        res;
    Acquire       => "acquire",       res;
    Release       => "release",       res;
    Seq           => "seq",           res;
    Relaxed       => "relaxed",       res;
    Nothing       => "nothing",       res;
    Accumulates   => "accumulates",   res;
    Merge         => "merge",         res;
    Max           => "max",           res;
    Min           => "min",           res;
    Add           => "add",           res;
    Or            => "or",            res;
    And           => "and",           res;
    Held          => "held",          res;
    Shared        => "shared",        res;
    Embeds        => "embeds",        res;
    Scale         => "scale",         res;
    Walk          => "walk",          res;
    Levels        => "levels",        res;
    Node          => "node",          res;
    Down          => "down",          res;
    Leaf          => "leaf",          res;
    Mappings      => "mappings",      res;
    Entry         => "entry",         res;
    // **«entrust» -- ein `code`-Raum, dessen INHALT Gabbro nicht kennt.**
    //
    // Das eine Wort, das JIT, JVM und jedes Gastmodul oeffnet. Es erbt den Eintrittsvertrag
    // von `entry` -- und der war bis 2026-08-18 gemessen LEER: zwoelf Felder, und keine
    // Datei ausserhalb des Lesers nannte `EntryDecl`. *Wer `entrust` baut, baut ihn zum
    // ersten Mal.*
    Entrust       => "entrust",       res;
    Vector        => "vector",        res;
    Regs          => "regs",          res;
    Out           => "out",           res;
    Preserves     => "preserves",     res;
    Clobbers      => "clobbers",      res;
    Asm           => "asm",           res;
    Stack         => "stack",         res;
    Dispatch      => "dispatch",      res;
    Per           => "per",           res;
    Cpu           => "cpu",           res;
    Ist           => "ist",           res;
    Nested        => "nested",        res;
    Masked        => "masked",        res;
    Awaits        => "awaits",        res;
    Port          => "port",          res;
    Step          => "step",          res;
    Via           => "via",           res;

    // -- Domains -------------------------------------------------------------------------
    Slots         => "slots",         res;
    Of            => "of",            res;
    Descendants   => "descendants",   res;
    Ancestors     => "ancestors"  ,   res;
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
    Queue         => "queue",         res;
    Elems         => "elems",         res;
    Threads       => "threads",       res;
    Reaches       => "reaches",       res;

    // -- Types ----------------------------------------------------------------------------
    U8            => "u8",            res;
    U16           => "u16",           res;
    U32           => "u32",           res;
    U64           => "u64",           res;
    I8            => "i8",            res;
    I16           => "i16",           res;
    I32           => "i32",           res;
    I64           => "i64",           res;
    // -- «F»: f32 und f64. Der Wortschatz waechst um DREI Woerter, nicht um zwei --------
    //
    // `rounded` kam aus dem Korpus (F0): an 340 Literalen eines echten Renderers gemessen
    // waeren 53 abgelehnt worden, darunter ln 2 und 2 pi. Verboten ist nicht das Inexakte,
    // sondern das STILLSCHWEIGEND Inexakte -- und `wrapping` sagt dieselbe Sorte Satz ueber
    // den Ueberlauf. *Dieselbe Form, dieselbe Begruendung, kein neues Muster.*
    F32           => "f32",           res;
    F64           => "f64",           res;
    Rounded       => "rounded",       res;
    // Die Verengung, die Nicht-NaN-Sein herstellt: `narrow x to finite else { … }`.
    Finite        => "finite",        res;
    Bool          => "bool",          res;
    Never         => "never",         res;
    W1c           => "w1c",           res;
    Rc            => "rc",            res;

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

/// **The renaming table (`M-woerter`, provisionally applied 2026-08-15).**
///
/// The closed vocabulary collides with ordinary naming at seven measured sites of the fragment
/// corpus. Of the three ways out -- contextual words, a position rule, renaming -- only the
/// last carries the promise further: **a softening for seven sites is a softening without
/// measured need** (`WERKZEUGKASTEN.md` W3).
///
/// So that the decision is not pushed onto the writer ("keep the list in your head"), **the
/// compiler names the replacement itself.** That is the entire price difference between
/// "renaming" and "renaming with a tool".
///
/// **Rollback path:** this table and the seven corpus sites are one commit; `git revert`
/// restores the state. The decision stays with the folder (`memos/M-woerter.md`).
pub fn ersatzvorschlag(k: Kw) -> Option<&'static str> {
    Some(match k {
        Kw::Slots => "plaetze",
        Kw::Slot => "platz",
        Kw::Ops => "dienste",
        Kw::Next => "naechst",
        Kw::From => "von",
        Kw::Boot => "startwert",
        Kw::Stack => "stapel",
        Kw::Check => "pruefung",
        Kw::State => "zustand",
        Kw::Node => "knoten",
        Kw::Step => "schritt",
        Kw::Port => "tor",
        Kw::Out => "aus",
        Kw::Count => "anzahl",
        _ => return None,
    })
}

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
