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
    Mirrors       => "mirrors",       res;
    From          => "from",          res;
    Assume        => "assume",        res;
    Falsifier     => "falsifier",     res;
    Unfalsifiable => "unfalsifiable", res;
    Axiom         => "axiom",         res;
    Lock          => "lock",          res;
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
    Vector        => "vector",        res;
    Regs          => "regs",          res;
    Out           => "out",           res;
    Preserves     => "preserves",     res;
    Clobbers      => "clobbers",      res;
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
