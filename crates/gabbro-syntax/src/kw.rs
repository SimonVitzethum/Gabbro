//! Der geschlossene Wortschatz.
//!
//! `SYNTAX.md` fuehrt ihn als **eine Tabelle** und sagt dazu: *„Alles andere ist ein Bezeichner.
//! Ein neues Wort ist eine Sprachaenderung und braucht einen Eintrag hier."* Diese Datei ist die
//! zweite Fassung derselben Tabelle, und `tests/wortschatz.rs` haelt beide gegeneinander --
//! sonst waere sie eine Zahl, die ein Mensch parallel zur Wahrheit fuehrt (Falle 80).
//!
//! **Reserviert gegen kontextuell.** Ein Wort der Tabelle ist kein Bezeichner. Ausgenommen sind
//! die **einbuchstabigen** Woerter `r`, `w`, `x`: `pruefe-wortschatz.py` nimmt sie selbst von der
//! Deckungspruefung aus (*„Ein-Zeichen-Terminale stammen aus Zeichenbereichen und sind keine
//! Woerter"*), und `FRAGMENTE.md` bindet `Reply(r)`. Sie werden an ihren Stellen -- `rights`,
//! `class` -- nach Text erkannt und sind sonst Bezeichner.

macro_rules! wortschatz {
    ( $( $variant:ident => $text:literal , $klasse:ident ; )* ) => {
        /// Ein Wort des geschlossenen Wortschatzes.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub enum Kw { $( $variant ),* }

        impl Kw {
            /// Die Schreibweise in der Quelle.
            pub const fn text(self) -> &'static str {
                match self { $( Kw::$variant => $text ),* }
            }

            /// Das Wort zu einer Zeichenfolge -- `None` heisst: Bezeichner.
            pub fn suche(s: &str) -> Option<Kw> {
                match s { $( $text => Some(Kw::$variant), )* _ => None }
            }

            /// Reserviert: an keiner Stelle ein Bezeichner.
            pub const fn reserviert(self) -> bool {
                match self { $( Kw::$variant => wortschatz!(@klasse $klasse) ),* }
            }
        }

        /// Alle Woerter, in der Reihenfolge der Tabelle in `SYNTAX.md`.
        pub const ALLE: &[Kw] = &[ $( Kw::$variant ),* ];
    };
    (@klasse res) => { true };
    (@klasse ctx) => { false };
}

wortschatz! {
    // -- Struktur --------------------------------------------------------------------------
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

    // -- Vertraege -------------------------------------------------------------------------
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

    // -- Wirkungen -------------------------------------------------------------------------
    Reads         => "reads",         res;
    Writes        => "writes",        res;
    Locks         => "locks",         res;
    Masks         => "masks",         res;
    Allocs        => "allocs",        res;
    Consumes      => "consumes",      res;
    Publishes     => "publishes",     res;
    Diverges      => "diverges",      res;
    Pure          => "pure",          res;

    // -- Ablauf ----------------------------------------------------------------------------
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

    // -- Zeiger ----------------------------------------------------------------------------
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

    // -- Bibliothek ------------------------------------------------------------------------
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

    // -- Domaenen --------------------------------------------------------------------------
    Slots         => "slots",         res;
    Of            => "of",            res;
    Descendants   => "descendants",   res;
    Ancestors     => "ancestors"  ,   res;
    Queue         => "queue",         res;
    Elems         => "elems",         res;
    Threads       => "threads",       res;
    Reaches       => "reaches",       res;

    // -- Typen -----------------------------------------------------------------------------
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

    // -- Eingebaut -------------------------------------------------------------------------
    Sizeof        => "sizeof",        res;
    Lenof         => "lenof",         res;
    Aligned       => "aligned",       res;
    Forall        => "forall",        res;
    Exists        => "exists",        res;
    True          => "true",          res;
    False         => "false",         res;
    SelfWort      => "Self",          res;
    // «B35»: `option index into T` hatte keinen Konstruktor. Der Bestand schreibt `Some(x)`
    // seit jeher -- in `match`-Mustern, in Ausdruecken und in SPRACHE.md:381 selbst --, die
    // Grammatik kannte es an keiner Stelle. Nachgezogen nach R9: der Bestand entscheidet.
    Some          => "Some",          res;
    None          => "None",          res;
}

/// **Die Umbenennungstabelle (`M-woerter`, provisorisch umgesetzt 2026-08-15).**
///
/// Der geschlossene Wortschatz kollidiert an sieben gemessenen Stellen des Fragmentkorpus mit
/// gewoehnlicher Benennung. Von den drei Auswegen — kontextuelle Woerter, Positionsregel,
/// Umbenennen — traegt nur der letzte die Zusage weiter: **eine Aufweichung fuer sieben
/// Stellen ist eine Aufweichung ohne gemessenen Bedarf** (`WERKZEUGKASTEN.md` W3).
///
/// Damit die Entscheidung nicht auf den Schreiber abgewaelzt wird („trag die Liste im Kopf"),
/// **nennt der Uebersetzer den Ersatz selbst.** Das ist der ganze Preisunterschied zwischen
/// „Umbenennen" und „Umbenennen mit Werkzeug".
///
/// **Rueckbaupfad:** diese Tabelle und die sieben Korpusstellen sind ein Commit; `git revert`
/// stellt den Zustand her. Die Entscheidung bleibt dem Ordner (`memos/M-woerter.md`).
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
    /// Die ganzzahligen Typwoerter -- `intty` in der Grammatik.
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
