//! The core tree. **One EBNF rule -- one node here.**
//!
//! The tree interprets nothing: it removes no parenthesis, reorders no contract clause and
//! knows no default. What is optional in `SYNTAX.md` is `Option` here; what is mandatory there
//! is a field without `Option` here. A pass that checks an obligation therefore checks the
//! **content**, never the presence -- except for `effects`, where the presence IS the
//! obligation (`SPRACHE.md` §7: not fail-open).

use crate::kw::Kw;
use crate::span::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
    pub text: String,
    pub span: Span,
}

/// `path = ident { "::" ident }`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pfad {
    pub teile: Vec<Ident>,
    pub span: Span,
}

impl Pfad {
    pub fn einfach(&self) -> Option<&Ident> {
        if self.teile.len() == 1 {
            self.teile.first()
        } else {
            None
        }
    }

    pub fn text(&self) -> String {
        self.teile
            .iter()
            .map(|t| t.text.as_str())
            .collect::<Vec<_>>()
            .join("::")
    }
}

// ---------------------------------------------------------------------------------------
// 1. Program, modules, constants
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Programm {
    pub items: Vec<Item>,
}

#[derive(Debug, Clone)]
pub struct Item {
    /// `when constexpr` -- conditional compilation, on every item.
    pub when: Option<Expr>,
    pub art: ItemArt,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ItemArt {
    Modul(Modul),
    Use(UseDecl),
    Typ(TypDecl),
    Konst(KonstDecl),
    Statisch(StatischDecl),
    Funktion(FnDecl),
    Format(Format),
    Tabelle(Tabelle),
    Reason(Reason),
    State(StateDecl),
    Device(Device),
    Assume(Assume),
    Axiom(Axiom),
    Check(Check),
    Atomic(AtomicDecl),
    Lock(LockDecl),
    /// **RCU -- eine Domaene, kein Schloss.** Siehe `RcuDecl`.
    Rcu(RcuDecl),
    /// `group N over { A, B };` -- a carrier group with a connecting invariant.
    Gruppe(GruppeDecl),
    Accumulates(AccDecl),
    Walk(WalkDecl),
    Entry(EntryDecl),
    Entrust(EntrustDecl),
    Boot(BootDecl),
}

impl ItemArt {
    /// The name the item is declared under -- for the name pass.
    pub fn name(&self) -> Option<&Ident> {
        match self {
            ItemArt::Modul(m) => m.pfad.teile.last(),
            ItemArt::Use(_) => None,
            ItemArt::Typ(t) => Some(&t.name),
            ItemArt::Konst(k) => Some(&k.name),
            ItemArt::Statisch(s) => Some(&s.name),
            ItemArt::Gruppe(g) => Some(&g.name),
            ItemArt::Funktion(f) => Some(&f.name),
            ItemArt::Format(f) => Some(&f.name),
            ItemArt::Tabelle(t) => Some(&t.name),
            ItemArt::Reason(r) => Some(&r.name),
            ItemArt::State(s) => Some(&s.name),
            ItemArt::Device(d) => Some(&d.name),
            ItemArt::Assume(a) => Some(&a.name),
            ItemArt::Axiom(a) => Some(&a.name),
            ItemArt::Check(c) => Some(&c.name),
            ItemArt::Atomic(a) => Some(&a.name),
            ItemArt::Lock(l) => Some(&l.name),
            ItemArt::Rcu(r) => Some(&r.name),
            ItemArt::Accumulates(a) => Some(&a.name),
            ItemArt::Walk(w) => Some(&w.name),
            ItemArt::Entry(e) => Some(&e.name),
            ItemArt::Entrust(e) => Some(&e.name),
            ItemArt::Boot(b) => Some(&b.name),
        }
    }

    /// How the kind is named in a refusal.
    pub fn benennung(&self) -> &'static str {
        match self {
            ItemArt::Modul(_) => "Modul",
            ItemArt::Use(_) => "use",
            ItemArt::Typ(_) => "Typ",
            ItemArt::Konst(_) => "Konstante",
            ItemArt::Statisch(_) => "static",
            ItemArt::Funktion(_) => "Funktion",
            ItemArt::Format(_) => "format",
            ItemArt::Tabelle(_) => "table",
            ItemArt::Reason(_) => "reason",
            ItemArt::State(_) => "state",
            ItemArt::Device(_) => "device",
            ItemArt::Assume(_) => "assume",
            ItemArt::Axiom(_) => "axiom",
            ItemArt::Check(_) => "check",
            ItemArt::Atomic(_) => "atomic",
            ItemArt::Lock(_) => "lock",
            ItemArt::Rcu(_) => "rcu",
            ItemArt::Gruppe(_) => "group",
            ItemArt::Accumulates(_) => "accumulates",
            ItemArt::Walk(_) => "walk",
            ItemArt::Entry(_) => "entry",
            ItemArt::Entrust(_) => "entrust",
            ItemArt::Boot(_) => "boot",
        }
    }
}

#[derive(Debug, Clone)]
pub struct Modul {
    pub oeffentlich: bool,
    pub pfad: Pfad,
    pub items: Vec<Item>,
}

#[derive(Debug, Clone)]
pub struct UseDecl {
    pub oeffentlich: bool,
    pub pfad: Pfad,
}

#[derive(Debug, Clone)]
pub struct KonstDecl {
    pub oeffentlich: bool,
    pub name: Ident,
    pub typ: TypExpr,
    pub wert: Expr,
}

#[derive(Debug, Clone)]
pub struct StatischDecl {
    pub oeffentlich: bool,
    pub veraenderlich: bool,
    pub name: Ident,
    pub typ: TypExpr,
    pub wert: Expr,
    pub section: Option<Textliteral>,
}

/// A string together with its site. Strings exist only in `claim`, `reason`, `assume`,
/// `section` and `unfalsifiable`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Textliteral {
    pub text: String,
    pub span: Span,
}

// ---------------------------------------------------------------------------------------
// 2. Types
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct TypDecl {
    pub oeffentlich: bool,
    pub opaque: bool,
    pub linear: bool,
    pub ghost: bool,
    pub tagged: bool,
    pub name: Ident,
    /// `type Duty(check)` -- the parameter list of a linear witness.
    pub parameter: Option<Vec<TypExpr>>,
    /// **«B37»: `order { roh, mmu, caps, … }` -- die Stufen einer linearen Geistmarke.**
    ///
    /// Der Befund des Bootfragments lautete: *„die Marke traegt die Reihenfolge, aber sie
    /// traegt sie als LINEARITAET, nicht als ORDNUNG."* Ein linearer Wert erzwingt eine
    /// **Kette, aber nicht WELCHE** -- bei sechs Bootschritten typpruefen alle 720
    /// Reihenfolgen.
    ///
    /// Das Fragment nannte beide Auswege und verwarf keinen:
    ///
    /// > *„entweder je eine eigene Marke (dann waechst der Wortschatz mit jedem Bootschritt)
    /// > oder eine Ordnung auf Marken -- und die gibt es nicht."*
    ///
    /// **Gewaehlt ist die zweite.** Die Stufen sind Bezeichner in EINER Deklaration; der
    /// Wortschatz waechst um zwei Woerter, einmal, nicht je Schritt.
    pub ordnung: Option<Vec<Ident>>,
    pub rumpf: Option<TypExpr>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TypExpr {
    Int(IntTy),
    Float(FloatTy),
    Bool(Span),
    Never(Span),
    Pfad(Pfad),
    Feld(Box<ArrayTy>),
    Zeiger(Box<PtrTy>),
    Verbund(Vec<FeldDecl>, Span),
    FnZeiger(Box<FnZeiger>),
    Varianten(Vec<Variante>, Span),
    /// `[option] index into T` -- the index type **generated** from `T`'s `count`.
    Index {
        tabelle: Ident,
        optional: bool,
        span: Span,
    },
}

impl TypExpr {
    pub fn span(&self) -> Span {
        match self {
            TypExpr::Int(i) => i.span,
            TypExpr::Float(f) => f.span,
            TypExpr::Bool(s) | TypExpr::Never(s) => *s,
            TypExpr::Pfad(p) => p.span,
            TypExpr::Feld(a) => a.span,
            TypExpr::Zeiger(p) => p.span,
            TypExpr::Verbund(_, s) => *s,
            TypExpr::FnZeiger(f) => f.span,
            TypExpr::Varianten(_, s) => *s,
            TypExpr::Index { span, .. } => *span,
        }
    }
}

/// **«F»: `f32` / `f64`, mit optionalem Bereich.**
///
/// Bewusst dieselbe Gestalt wie `IntTy` -- Wort plus Bereich. *Ein Gleitkommatyp ist im
/// Prueferblick eine Zahl mit einer Schranke; was ihn unterscheidet, sind zwei Bits
/// (`kann_nan`, `kann_unendlich`) und die Rundung, und beide gehoeren ins Typmodell, nicht
/// in die Grammatik.*
#[derive(Debug, Clone)]
pub struct FloatTy {
    pub wort: Kw,
    pub bereich: Option<Bereich>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct IntTy {
    pub wort: Kw,
    pub bereich: Option<Bereich>,
    pub span: Span,
}

/// `range = expr ".." expr | expr "..<" expr`
#[derive(Debug, Clone)]
pub struct Bereich {
    pub von: Expr,
    pub bis: Expr,
    /// `..<` -- upper bound excluded.
    pub exklusiv: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ArrayTy {
    pub element: TypExpr,
    pub laenge: Expr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct PtrTy {
    pub raum: Raum,
    pub rechte: Vec<Recht>,
    pub ziel: TypExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Raum {
    Normal,
    Mmio,
    Dma,
    Code,
    Boot,
    Port,
    Benannt(Ident),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Recht {
    Lesen,
    Schreiben,
    LesenSchreiben,
    Ausfuehren,
    /// `own [ "@" ident ]`
    Eigen(Option<Ident>),
}

#[derive(Debug, Clone)]
pub struct FeldDecl {
    pub name: Ident,
    pub typ: FeldTy,
    pub bitpos: Option<BitPos>,
    pub offset_into: Option<Ident>,
    pub bedingung: Option<Pred>,
    pub reserviert: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FeldTy {
    pub typ: TypExpr,
    /// `embeds [ hi : lo ] [ scale const ]` -- a pointer that is also a bitfield.
    pub embeds: Option<(u128, u128)>,
    pub scale: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BitPos {
    Bit(u128),
    Bereich(u128, u128),
}

#[derive(Debug, Clone)]
pub struct Variante {
    pub name: Ident,
    pub nutzlast: Option<TypExpr>,
}

#[derive(Debug, Clone)]
pub struct FnZeiger {
    pub parameter: Vec<TypExpr>,
    pub ergebnis: Option<TypExpr>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: Ident,
    pub typ: TypExpr,
}

// ---------------------------------------------------------------------------------------
// 4. Expressions
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Expr {
    pub art: ExprArt,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExprArt {
    Zahl(u128),
    /// **«F»: ein Gleitkommaliteral.** Bits einer `f64`, ob der Dezimalbruch dyadisch ist,
    /// und ob `rounded` dahinterstand.
    ///
    /// **`rounded` kam aus dem Korpus, nicht aus dem Entwurf** (`FRAGMENTE.md`, «F0»): an
    /// 340 Literalen eines echten Renderers waeren ohne dieses Wort 53 abgelehnt worden,
    /// darunter ln 2 und 2 pi. *Verboten ist nicht das Inexakte, sondern das
    /// STILLSCHWEIGEND Inexakte.*
    Gleitkomma {
        bits: u64,
        dyadisch: bool,
        gerundet: bool,
    },
    Wahr,
    Falsch,
    Ort(Ort),
    Ruf(Ruf),
    Klammer(Box<Expr>),
    Eingebaut(Box<Eingebaut>),
    /// `old(place)` -- expression, not predicate; only in `ensures`.
    Alt(Ort),
    /// `result` -- the return value in `ensures`.
    Ergebnis,
    Unaer(UnOp, Box<Expr>),
    Binaer(BinOp, Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Nicht,
    Negativ,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Oder,
    Und,
    Gleich,
    Ungleich,
    Kleiner,
    KleinerGleich,
    Groesser,
    GroesserGleich,
    BitUnd,
    BitOder,
    BitXor,
    SchiebLinks,
    SchiebRechts,
    Plus,
    Minus,
    Mal,
    Geteilt,
    Rest,
}

impl BinOp {
    pub const fn ist_vergleich(self) -> bool {
        matches!(
            self,
            BinOp::Gleich
                | BinOp::Ungleich
                | BinOp::Kleiner
                | BinOp::KleinerGleich
                | BinOp::Groesser
                | BinOp::GroesserGleich
        )
    }
}

/// `place = ident { placesuffix }`
#[derive(Debug, Clone)]
pub struct Ort {
    pub basis: Ident,
    pub suffixe: Vec<OrtSuffix>,
    pub span: Span,
}

impl Ort {
    /// The place as it stood in the source -- for the manifest and for refusals.
    pub fn text(&self) -> String {
        let mut s = self.basis.text.clone();
        for suffix in &self.suffixe {
            match suffix {
                OrtSuffix::Feld(i) => {
                    s.push('.');
                    s.push_str(&i.text);
                }
                OrtSuffix::Ueber(i) => {
                    s.push_str("->");
                    s.push_str(&i.text);
                }
                // The index is an expression; the manifest names the site, not the value.
                OrtSuffix::Index(_) => s.push_str("[…]"),
            }
        }
        s
    }
}

#[derive(Debug, Clone)]
pub enum OrtSuffix {
    /// `.ident`
    Feld(Ident),
    /// `[expr]`
    Index(Expr),
    /// `->ident`
    Ueber(Ident),
}

/// `call = path "(" [ arglist ] ")"` -- syntactically the same form as `cast`.
///
/// **«B7»: ein Verbundwert ist ein Ruf mit MARKEN.** `P(a: 1, b: true)` stellt einen
/// `type P = { a : u32, b : bool }` her. Warum als Ruf und nicht als `P { a: 1 }`, steht in
/// `SYNTAX.md` unter „Was es absichtlich nicht gibt" -- kurz: ein geschweiftes Literal waere
/// die ERSTE Ausdrucksform, die mit `{` weitergeht, und an 76 Korpusstellen folgt ein `{`
/// direkt auf einen Ausdruck. Der Fehlerfall eines Kontextschalters ist STILL.
#[derive(Debug, Clone)]
pub struct Ruf {
    pub pfad: Pfad,
    pub argumente: Vec<Expr>,
    /// **Invariante: leer, oder genauso lang wie `argumente`.**
    ///
    /// Sie wird an genau einer Stelle hergestellt (`parse::ruf_ab`, eine Schleife, die Marke
    /// und Wert zusammen anhaengt) und an genau einer Stelle geprueft
    /// (`m1::verbundwert`, die den Schluesselstrom gegen die Felderliste haelt).
    ///
    /// **Leer heisst nicht „keine Marken erlaubt", sondern „keine geschrieben".** Ob das
    /// zulaessig ist, entscheidet M1 am Gerufenen: ein Verbund verlangt sie, eine Funktion
    /// verbietet sie.
    pub marken: Vec<Ident>,
    pub span: Span,
}

impl Ruf {
    /// **Der syntaktische Unterscheider: ein markierter Ruf ist ein Verbundwert.**
    ///
    /// Er braucht keine Umgebung, keine Namensaufloesung und keine Karte -- und genau das ist
    /// der Punkt. Die Paesse, die einen Konstruktor anders behandeln muessen als einen Aufruf
    /// (Kosten, Wirkungen, Aufrufgraph), fragen hier und koennen sich nicht an einer
    /// fehlenden Karteneintragung stillschweigend vorbeimogeln.
    pub fn ist_verbundwert(&self) -> bool {
        !self.marken.is_empty()
    }
}

#[derive(Debug, Clone)]
pub enum Eingebaut {
    /// `sizeof(typeexpr | place)`
    Sizeof(TypOderOrt),
    /// `lenof(typeexpr | place)`
    Lenof(TypOderOrt),
    /// `aligned(expr, constexpr)`
    Aligned(Expr, Expr),
}

#[derive(Debug, Clone)]
pub enum TypOderOrt {
    Typ(TypExpr),
    Ort(Ort),
}

// ---------------------------------------------------------------------------------------
// 5. Predicates -- this is where the line runs
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Pred {
    pub art: PredArt,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum PredArt {
    /// A `cmpexpr` as an atom.
    Vergleich(Expr),
    Quantor(Box<Quantor>),
    /// `expr in domain`
    Element(Expr, Domaene),
    /// `place reaches place via ident`
    Erreicht {
        von: Ort,
        nach: Ort,
        via: Ident,
    },
    /// `Held(L)` resp. `Held(L, shared)` -- **the lock witness WITH its strength.**
    ///
    /// Until 2026-08-15 this was an ordinary call inside the predicate and carried no
    /// strength; `requires Held-shared` was therefore unwritable, and the interim rule
    /// `H005` had to bar EVERY witness under shared acquisition.
    Held {
        sperre: Ident,
        geteilt: bool,
        span: Span,
    },
    Klammer(Box<Pred>),
    Nicht(Box<Pred>),
    Und(Box<Pred>, Box<Pred>),
    Oder(Box<Pred>, Box<Pred>),
    /// `=>` -- implication.
    Folgt(Box<Pred>, Box<Pred>),
}

#[derive(Debug, Clone)]
pub struct Quantor {
    pub art: QuantorArt,
    pub variable: Ident,
    pub domaene: Domaene,
    pub rumpf: Pred,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuantorArt {
    Alle,
    Existiert,
}

/// The eight domains. **Closed** -- there is no user-defined one.
#[derive(Debug, Clone)]
pub enum Domaene {
    SlotsVon(Ort),
    KetteIn { a: Ident, b: Ident, ort: Ort },
    NachfahrenVon(Ort),
    /// `ancestors of <place>` -- **the same edge, the other direction.**
    ///
    /// Measured («B41», B3 sweep): four bodies in DMAR/PCIe walk the device topology
    /// UPWARDS (`cur = topo[cur].parent`). Downwards it was a domain, upwards it was none --
    /// and so 226 of the 584 non-traversable lines fell into an area nobody had suspected.
    VorfahrenVon(Ort),
    Schlange(Ort),
    FelderVon(Pfad),
    ElementeVon(Ort),
    Threads,
    AbbildungenVon(Ort),
}

impl Domaene {
    pub fn benennung(&self) -> &'static str {
        match self {
            Domaene::SlotsVon(_) => "slots of",
            Domaene::KetteIn { .. } => "chain(…) in",
            Domaene::NachfahrenVon(_) => "descendants of",
            Domaene::VorfahrenVon(_) => "ancestors of",
            Domaene::Schlange(_) => "queue",
            Domaene::FelderVon(_) => "fields of",
            Domaene::ElementeVon(_) => "elems of",
            Domaene::Threads => "threads",
            Domaene::AbbildungenVon(_) => "mappings of",
        }
    }
}

// ---------------------------------------------------------------------------------------
// 6. Functions and contracts
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct FnDecl {
    pub oeffentlich: bool,
    pub klasse: Option<FnKlasse>,
    pub name: Ident,
    pub parameter: Vec<Parameter>,
    pub ergebnis: Option<TypExpr>,
    pub requires: Vec<Pred>,
    pub ensures: Vec<Pred>,
    pub maintains: Vec<Ident>,
    /// `None` means: the clause is missing. That is an error except for `spec fn`
    /// -- `effects` is not fail-open.
    pub effects: Option<Wirkungen>,
    pub costs: Option<Expr>,
    pub by: Vec<Induktion>,
    pub section: Option<Textliteral>,
    pub arch: Option<Ident>,
    pub when: Option<Expr>,
    /// **«B37»: `advances roh -> mmu`** -- welchen Schritt diese Funktion auf der Marke tut.
    ///
    /// Sie steht an der DEKLARATION, nicht am Rufer: *wer den Schritt macht, weiss, welcher
    /// es ist; wer ruft, soll es nicht wiederholen muessen.* Der Pruefer haelt sie gegen die
    /// `order` der Marke und gegen den Zustand am Rufort.
    pub advances: Option<(Ident, Ident)>,
    pub rumpf: FnRumpf,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FnKlasse {
    Spec,
    /// **`const fn` -- comptime, das WERTE rechnet.**
    ///
    /// Die Linie, an der dieser Zusatz haengt (`PLAN.md`, „Wozu Gabbro taugen wird"):
    ///
    /// ```text
    /// comptime, das WERTE rechnet   ->  kostet keine Schablone
    /// comptime, das CODE  erzeugt   ->  kostet eine, und die will bewiesen werden
    /// ```
    ///
    /// Ein `const fn` erzeugt keinen Code -- es liefert eine Zahl, und die steht dann in
    /// `count`, in `costs` oder in einer Bereichsgrenze. *Deshalb bekommt es KEINEN
    /// Schabloneneintrag, und deshalb ist es der einzige comptime-Zusatz, den die Ratsche
    /// zulaesst.*
    Konst,
    Impl,
    Raw,
    Divergent,
    Prim,
    Extern,
}

impl FnKlasse {
    pub const fn text(self) -> &'static str {
        match self {
            FnKlasse::Spec => "spec",
            FnKlasse::Konst => "const",
            FnKlasse::Impl => "impl",
            FnKlasse::Raw => "raw",
            FnKlasse::Divergent => "divergent",
            FnKlasse::Prim => "prim",
            FnKlasse::Extern => "extern",
        }
    }
}

#[derive(Debug, Clone)]
pub enum FnRumpf {
    Block(Block),
    /// `= pred ;` -- only for `spec fn`.
    Pred(Pred),
    /// `;` -- declaration without a body.
    Keiner,
}

#[derive(Debug, Clone)]
pub struct Wirkungen {
    pub liste: Vec<Wirkung>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Wirkung {
    pub art: WirkungArt,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum WirkungArt {
    Liest(Ort),
    Schreibt(Ort),
    Sperrt(Ort),
    /// `locks shared N` -- **shared acquisition.** Permits reading the protected places,
    /// forbids writing; mechanically checkable against `protects`.
    SperrtGeteilt(Ort),
    Maskiert(Ident),
    Belegt(Ident),
    Verbraucht(Ort),
    Veroeffentlicht(Ort),
    Divergiert,
    Rein,
}

impl WirkungArt {
    /// Effect together with its subject: `writes c.slots`, not merely `writes`.
    pub fn text(&self) -> String {
        match self {
            WirkungArt::Liest(o) => format!("reads {}", o.text()),
            WirkungArt::Schreibt(o) => format!("writes {}", o.text()),
            WirkungArt::Sperrt(o) => format!("locks {}", o.text()),
            WirkungArt::SperrtGeteilt(o) => format!("locks shared {}", o.text()),
            WirkungArt::Maskiert(i) => format!("masks {}", i.text),
            WirkungArt::Belegt(i) => format!("allocs {}", i.text),
            WirkungArt::Verbraucht(o) => format!("consumes {}", o.text()),
            WirkungArt::Veroeffentlicht(o) => format!("publishes {}", o.text()),
            WirkungArt::Divergiert => "diverges".to_string(),
            WirkungArt::Rein => "pure".to_string(),
        }
    }

    pub fn benennung(&self) -> &'static str {
        match self {
            WirkungArt::Liest(_) => "reads",
            WirkungArt::Schreibt(_) => "writes",
            WirkungArt::Sperrt(_) => "locks",
            WirkungArt::SperrtGeteilt(_) => "locks shared",
            WirkungArt::Maskiert(_) => "masks",
            WirkungArt::Belegt(_) => "allocs",
            WirkungArt::Verbraucht(_) => "consumes",
            WirkungArt::Veroeffentlicht(_) => "publishes",
            WirkungArt::Divergiert => "diverges",
            WirkungArt::Rein => "pure",
        }
    }
}

/// `induct = "induction" "over" domain` -- **names** the generated scheme, proves nothing.
#[derive(Debug, Clone)]
pub struct Induktion {
    pub domaene: Domaene,
    pub span: Span,
}

// ---------------------------------------------------------------------------------------
// 7./8. Statements and loops
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Block {
    pub anweisungen: Vec<Stmt>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Stmt {
    pub art: StmtArt,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum StmtArt {
    Let(LetStmt),
    /// `let ident = call else (ident) block` -- the only error propagation.
    LetSonst(LetSonst),
    Zuweisung(Zuweisung),
    Wenn(WennStmt),
    Match(MatchStmt),
    Schleife(Box<Schleife>),
    /// `breaking identlist block`
    Bricht(BrichtStmt),
    /// `narrow place to range else block`
    Narrow(NarrowStmt),
    /// `locks place block`
    Sperrt(SperrtStmt),
    /// `observes D { … }` -- die RCU-Leseseite.
    Observiert(ObserviertStmt),
    Leave(Ident),
    Next(Ident),
    /// `place = expr publishes (placelist | nothing) ;`
    Publish(PublishStmt),
    /// `let ident = place awaits { placelist } ;`
    AwaitLoad(AwaitLoad),
    /// `let ident = place exchange xform … ;`
    Exchange(Box<ExchangeStmt>),
    Return(Option<Expr>),
    Ruf(Ruf),
}

#[derive(Debug, Clone)]
pub struct LetStmt {
    pub veraenderlich: bool,
    pub name: Ident,
    pub typ: Option<TypExpr>,
    pub wert: Expr,
}

#[derive(Debug, Clone)]
pub struct LetSonst {
    pub name: Ident,
    /// **«B14b» geschlossen 2026-08-17: die Quelle darf auch ein `place` sein.**
    ///
    /// Der Befund lautete: *„`let … else` verlangt RECHTS einen `call`. Ein `option`-wertiges
    /// `place` laesst sich damit nicht auspacken -- und ein Atomic IST ein `place`."*
    /// Genau daran zerbrach die Messstelle in `FRAGMENTE.md` F6.
    pub quelle: LetQuelle,
    pub fehlername: Ident,
    pub sonst: Block,
}

/// Woraus ein `let … else` auspackt.
#[derive(Debug, Clone)]
pub enum LetQuelle {
    Ruf(Ruf),
    /// Ein `place` -- ein Atomic, ein Slotfeld, alles mit `option`-Wert.
    Ort(Ort),
}

impl LetSonst {
    /// Der Ruf, falls die Quelle einer ist. **Die Paesse, die nur Rufe interessieren, fragen
    /// so** -- statt dass jede von ihnen die neue Form kennen muss.
    pub fn als_ruf(&self) -> Option<&Ruf> {
        match &self.quelle {
            LetQuelle::Ruf(r) => Some(r),
            LetQuelle::Ort(_) => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Zuweisung {
    pub ziel: Ort,
    pub op: ZuwOp,
    pub wert: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ZuwOp {
    Setzt,
    Plus,
    Minus,
    Und,
    Oder,
}

#[derive(Debug, Clone)]
pub struct WennStmt {
    /// The condition and its block; further entries are `else if`.
    pub zweige: Vec<(Expr, Block)>,
    pub sonst: Option<Block>,
}

#[derive(Debug, Clone)]
pub struct MatchStmt {
    pub gegenstand: Expr,
    pub zweige: Vec<MatchZweig>,
}

#[derive(Debug, Clone)]
pub struct MatchZweig {
    pub variante: Ident,
    pub binder: Option<Ident>,
    pub rumpf: Block,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct BrichtStmt {
    pub invarianten: Vec<Ident>,
    pub rumpf: Block,
}

#[derive(Debug, Clone)]
pub struct NarrowStmt {
    pub ort: Ort,
    pub ziel: NarrowZiel,
    pub sonst: Block,
}

/// **Wohin verengt wird.**
///
/// `finite` kam mit «F» dazu, und es ist **keine** Bereichsverfeinerung: *Endlichkeit ist im
/// Gitter kein Intervall.* NaN liegt in keinem Intervall, und dieselbe Aussage ist trotzdem
/// nicht „der Bereich ist enger". Darum eine eigene Form statt eines Bereichs mit
/// Sonderwerten.
///
/// **Und es gibt kein `isnan` in der Sprache.** `narrow … to finite else { … }` IST die
/// Prüfung, und ihr `else`-Zweig ist der NaN-Weg -- genau die Gestalt, die der Korpus von
/// Hand schreibt (`FRAGMENTE.md`, «F0»/FF1).
#[derive(Debug, Clone)]
pub enum NarrowZiel {
    Bereich(Bereich),
    /// Nicht NaN UND nicht unendlich -- zwei Bits, auf einmal gesetzt.
    Endlich(Span),
}

/// **Eine RCU-Domaene. KEINE Sperre.**
///
/// Der zweite Korpus zeigte die Klasse, die der erste nie zeigte: die Leseseite nimmt gar
/// nichts, die Schreibseite tauscht einen Zeiger und wartet auf eine Gnadenfrist.
/// `lock`/`protects`/`rank`/`held` beschreibt gegenseitigen Ausschluss -- **hier gibt es
/// keinen.**
///
/// *Darum kein `rank` und kein `held`: es gibt keine Haltezeit, gegen die eine Latenzaussage
/// rechnen koennte, und keine Ordnung, in der etwas genommen wuerde.*
#[derive(Debug, Clone)]
pub struct RcuDecl {
    pub name: Ident,
    pub schuetzt: Vec<Ort>,
    /// **`reclaims <ort>` -- wo ein Platz zurueckgegeben wird.**
    ///
    /// Der Kopf der Freiliste. *Ohne einen genannten Ort haette die Gnadenfrist nichts, an
    /// dem sie haengen koennte* -- und mit ihm sind zwei Regeln pruefbar, die es vorher nicht
    /// waren.
    pub gibt_zurueck: Option<Ort>,
    pub span: Span,
}

/// `observes D { … }` -- die LESESEITE. Ein Bereich, in dem ein gelesener Zeiger gueltig
/// bleibt; kein Ausschluss, keine Nahme.
#[derive(Debug, Clone)]
pub struct ObserviertStmt {
    pub domaene: Ident,
    pub rumpf: Block,
}

#[derive(Debug, Clone)]
pub struct SperrtStmt {
    pub sperre: Ort,
    /// `locks shared N { … }` -- shared acquisition. **The hot path of a kernel takes it
    /// this way**: capability resolution only reads (MESSUNGEN.md, paper test: 33 against 44).
    pub geteilt: bool,
    pub rumpf: Block,
}

#[derive(Debug, Clone)]
pub struct PublishStmt {
    pub ziel: Ort,
    pub wert: Expr,
    pub nutzlast: Nutzlast,
}

/// `publishes ( placelist | "nothing" )` -- `nothing` is a word, not an empty list hole.
#[derive(Debug, Clone)]
pub enum Nutzlast {
    Orte(Vec<Ort>),
    Nichts(Span),
}

#[derive(Debug, Clone)]
pub struct AwaitLoad {
    pub name: Ident,
    pub quelle: Ort,
    pub erwartet: Vec<Ort>,
}

#[derive(Debug, Clone)]
pub struct ExchangeStmt {
    pub name: Ident,
    pub ort: Ort,
    pub form: XForm,
    pub nutzlast: Option<Nutzlast>,
    pub erwartet: Option<Vec<Ort>>,
}

#[derive(Debug, Clone)]
pub enum XForm {
    /// `update(ident) block` -- the body computes old -> new.
    Update { binder: Ident, rumpf: Block },
    /// `expr when pred returns ident` -- compare-exchange.
    Vergleich {
        wert: Expr,
        bedingung: Pred,
        ergebnis: Ident,
    },
}

#[derive(Debug, Clone)]
pub enum Schleife {
    Traverse(Traverse),
    Retry(Retry),
    Forever(Forever),
}

#[derive(Debug, Clone)]
pub struct Traverse {
    pub variable: Ident,
    pub gegenstand: Option<Expr>,
    pub domaene: Domaene,
    pub abstieg: Abstieg,
    pub touches: Option<Wirkungen>,
    pub rumpf: Block,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Abstieg {
    Unbesucht,
    Verbrauchend,
    Fallend(Expr),
}

#[derive(Debug, Clone)]
pub struct Retry {
    pub marke: Option<Ident>,
    pub bis: Option<Pred>,
    pub schranke: Expr,
    pub fortschritt: Option<Ident>,
    pub bei_ueberschreitung: Ident,
    pub effects: Option<Wirkungen>,
    pub rumpf: Block,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Forever {
    pub marke: Option<Ident>,
    pub je_durchgang: Expr,
    pub bei_ueberschreitung: Ident,
    pub effects: Wirkungen,
    pub fortschritt: Option<Ident>,
    pub verlaesst: Vec<Ident>,
    pub rumpf: Block,
    pub span: Span,
}

// ---------------------------------------------------------------------------------------
// 9. Tables, traversals, formats
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Tabelle {
    pub name: Ident,
    /// `count N` -- the number of slots. **Without it `index into T` has no upper bound from
    /// the declaration**, and "no unchecked indexing" rests on the convention that someone
    /// picked a fitting index type by hand (finding G8).
    pub kapazitaet: Option<Expr>,
    /// **`backed k` -- der WERT, bis zu dem die Plaetze hinterlegt sind.**
    ///
    /// `count` ist Adressraum, `backed` ist Speicher. Ohne die Trennung sagt der Indextyp
    /// `i < N` -- und gebraucht wird `i ist HINTERLEGT`. *Ein Zugriff auf einen nicht
    /// hinterlegten Platz ist sonst typkorrekt und trotzdem ein Fehlzugriff, und in einem
    /// Kernel ist das besonders scharf: er ist selbst die Instanz, die Seiten hinterlegt.*
    pub hinterlegt: Option<Ident>,
    pub konstanten: Vec<KonstDecl>,
    pub slot: Option<SlotDecl>,
    pub invarianten: Vec<Invariante>,
    /// `ops identlist ;` -- the **generated** mutations.
    pub ops: Vec<Ident>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct SlotDecl {
    pub felder: Vec<SlotFeld>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct SlotFeld {
    pub name: Ident,
    pub typ: SlotTyp,
    /// **`by ops`** -- only the table's generated operations write this field. The K
    /// condition thereby turns from a checking rule into a property of the grammar.
    pub nur_ops: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum SlotTyp {
    Typ(TypExpr),
    /// `intty wrapping`
    Wrapping(IntTy),
}

#[derive(Debug, Clone)]
pub struct Invariante {
    pub name: Ident,
    pub kosten: Expr,
    pub laeuft: Laeuft,
    pub by: Vec<Induktion>,
    pub pred: Pred,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Laeuft {
    Online,
    Offline,
}

#[derive(Debug, Clone)]
pub struct WalkDecl {
    pub name: Ident,
    pub ebenen: Expr,
    pub knoten: ArrayTy,
    pub ab: Ident,
    pub ab_wenn: Pred,
    pub blatt: Pred,
    pub invarianten: Vec<Invariante>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Format {
    pub name: Ident,
    pub version: Option<u128>,
    pub endian: Option<Endian>,
    pub felder: Vec<FeldDecl>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Endian {
    Klein,
    Gross,
}

#[derive(Debug, Clone)]
pub struct Reason {
    pub name: Ident,
    pub faelle: Vec<ReasonFall>,
    pub erschoepfend: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ReasonFall {
    pub name: Ident,
    pub wert: u128,
    pub text: Textliteral,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct StateDecl {
    pub name: Ident,
    pub uebergaenge: Vec<Uebergang>,
    pub span: Span,
}

// ---------------------------------------------------------------------------------------
// 10. Devices
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Device {
    pub name: Ident,
    pub parameter: Vec<Parameter>,
    pub raum: Raum,
    pub mirrors: Option<Mirrors>,
    pub register: Vec<RegDecl>,
    pub baenke: Vec<Bank>,
    pub uebergaenge: Vec<Uebergang>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Mirrors {
    pub ziel: Ort,
    pub quelle: Ort,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Bank {
    pub name: Ident,
    pub basis: Expr,
    pub schritt: Expr,
    pub anzahl: Expr,
    pub register: Vec<RegDecl>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct RegDecl {
    pub name: Ident,
    pub typ: IntTy,
    /// **«B32»:** the wraparound is SPOKEN at the register, not tolerated. It then holds for
    /// every computation on that register -- the stronger form, because it sits at the
    /// declaration and not at the one computation somebody thought of.
    pub umlaufend: bool,
    pub versatz: Expr,
    pub klasse: RegKlasse,
    pub felder: Vec<(Ident, BitPos)>,
    pub requires: Option<Pred>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegKlasse {
    Lesen,
    Schreiben,
    LesenSchreiben,
    /// `w1c` -- writing a one clears.
    W1c,
    /// `rc` -- reading clears.
    Rc,
}

#[derive(Debug, Clone)]
pub struct Uebergang {
    pub name: Ident,
    /// `transset` -- SEVERAL places in ONE move.
    pub schritte: Vec<OrtSchritt>,
    pub requires: Option<Pred>,
    pub effects: Option<Wirkungen>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct OrtSchritt {
    pub ort: Ort,
    pub von: Expr,
    pub nach: Expr,
    pub span: Span,
}

// ---------------------------------------------------------------------------------------
// 11. Concurrency
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct AtomicDecl {
    pub oeffentlich: bool,
    pub name: Ident,
    pub typ: TypExpr,
    /// The **superset** of the payload at the declaration (SPRACHE.md §11.3). The obligation
    /// sits at the store; this entry is voluntary and is checked against every store payload.
    /// It is **not** in the EBNF today -- see refusal `P031`.
    pub obermenge: Option<Nutzlast>,
    pub ordnung: Option<Ordnung>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ordnung {
    Acquire,
    Release,
    Seq,
    Relaxed,
}

/// **`group N over { A, B };` -- the carrier group.**
///
/// The measured need is in the SWEEP der Verbindungs-Invarianten (`MESSUNGEN.md`,
/// 2026-08-16): four invariants between two carriers each, and **one of them (V4) runs across
/// two crates with two locks.** What a single table cannot express: *"the counter in A equals
/// the number of references in B"* -- no `table` invariant can say it, because it quantifies
/// only over its own carrier.
///
/// **The lock order is NOT declared again.** It already stands: every carrier lies under a
/// `lock … protects { … } rank N`, and the ranks give the order. A second declaration would be
/// a second truth about the same thing.
#[derive(Debug, Clone)]
pub struct GruppeDecl {
    pub name: Ident,
    /// The carriers. **At least two** -- a group with one member is a table.
    pub traeger: Vec<Ident>,
    /// **The connecting invariants.** The reason the group exists: a statement that
    /// quantifies over SEVERAL carriers and therefore cannot sit on any single
    /// `table … invariant`.
    pub invarianten: Vec<Invariante>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct LockDecl {
    pub name: Ident,
    pub schuetzt: Vec<Ort>,
    pub rang: Expr,
    /// `held <= constexpr ops` -- without it the lock cannot be taken in service loops.
    pub haltezeit: Option<Expr>,
    /// `shared held <= constexpr ops` -- **the separate branch for reader-writer locks.**
    /// `held` is meant for EXCLUSIVE holders; on the shared side the quantity computed is a
    /// different one, and without this number the latency statement of §9.3 has no branch for
    /// a lock taken shared (MESSUNGEN.md, side finding N3).
    pub geteilte_haltezeit: Option<Expr>,
    pub maskiert: Option<Ident>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct AccDecl {
    pub name: Ident,
    pub typ: TypExpr,
    pub merge: MergeOp,
    /// **`per cpu <constexpr>` -- wie viele Zellen** (2026-08-18).
    ///
    /// `SPRACHE.md` §11.4 sagt seit jeher *„one cell per core, merged over the
    /// NCORES-bounded loop"* -- **und nannte die Zahl nirgends.** Der Erzeuger haette
    /// `NCORES` raten oder einen Namen suchen muessen; genau das Raten, gegen das `C001`
    /// steht.
    ///
    /// *Die Woerter gab es schon* (`per cpu` am `stack` eines `entry`), also kostet die
    /// Entscheidung keinen Wortschatz -- nur eine Stelle, an der die Zahl steht.
    pub pro_kern: Option<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MergeOp {
    Max,
    Min,
    Add,
    Or,
    And,
}

// ---------------------------------------------------------------------------------------
// 12. Hardware assumptions and axioms
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Assume {
    pub name: Ident,
    pub text: Textliteral,
    pub klasse: AnnahmeKlasse,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Axiom {
    pub name: Ident,
    pub parameter: Vec<Parameter>,
    /// **G2.** `axiom rdtscp() -> u64 requires Has(RDTSCP) …` was unwritable until
    /// 2026-08-15. Concerns the axiom layer, i.e. the largest unproven item.
    pub rueckgabe: Option<TypExpr>,
    pub requires: Vec<Pred>,
    pub effects: Wirkungen,
    pub klasse: AnnahmeKlasse,
    pub span: Span,
}

/// Three classes, and the third does not exist syntactically: *not run* is the **absence of
/// both entries** and therefore a compile error.
#[derive(Debug, Clone)]
pub enum AnnahmeKlasse {
    Falsifizierbar(Ident),
    NichtFalsifizierbar(Textliteral),
}

// ---------------------------------------------------------------------------------------
// 13. `check`
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Check {
    pub name: Ident,
    pub claim: Textliteral,
    pub measures: Vec<Ort>,
    pub gates: Vec<Ident>,
    pub can_fail: Block,
    pub floor: Vec<Pred>,
    pub counterprobe: Option<(Textliteral, Ident)>,
    pub span: Span,
}

// ---------------------------------------------------------------------------------------
// 14. Entry and boot
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct EntryDecl {
    pub name: Ident,
    pub vektor: Option<Expr>,
    pub via: Option<Ident>,
    pub arch: Ident,
    pub regs_in: Vec<(Ident, Ident)>,
    pub regs_out: Vec<(Ident, Ident)>,
    pub preserves: Vec<Ident>,
    pub clobbers: Vec<Ident>,
    pub stack: Ident,
    pub pro_kern: bool,
    pub ist: Option<Expr>,
    pub verschachtelt: Option<Verschachtelt>,
    pub dispatch: Pfad,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Verschachtelt {
    Nie,
    Maskiert,
    Begrenzt(Expr),
}

/// **«entrust» -- der Raum, dessen INHALT Gabbro nicht kennt** (2026-08-18).
///
/// Gabbro sagt ueber den Gast **nichts**: keine Kosten, keine Wirkungen, keine Terminierung,
/// keine Blattheit. Was es sagt, ist der **Vertrag am Eintritt**. *Das ist keine Luecke,
/// sondern der Zweck eines Mikrokernels -- fuer den Gast gilt Isolation statt Beweis.*
///
/// **Der Vertrag ist derselbe wie bei `entry`** -- und der war am Tag, an dem dieses Item
/// entstand, gemessen leer: zwoelf Felder, und keine Datei ausserhalb des Lesers nannte
/// `EntryDecl` (`pruefe-klauseln.py`). *Wer `entrust` baut, baut ihn zum ersten Mal.*
#[derive(Debug, Clone)]
pub struct EntrustDecl {
    pub name: Ident,
    /// Der `code`-Raum -- ein **Name**, kein Ausdruck.
    ///
    /// *Ein `entrust` auf einen gerechneten Wert waere ein Sprung an eine ausgerechnete
    /// Adresse* -- genau das, was nicht nennbar sein soll. `N006` haelt ihn gegen die
    /// Deklarationen dieser Einheit.
    pub raum: Ident,
    pub arch: Ident,
    /// Was der Gast beim Eintritt in den Registern hat.
    pub regs_gast: Vec<(Ident, Ident)>,
    /// Auf welchem Stapel er laeuft.
    pub stapel: Ident,
    /// **Pflicht, und nicht schmueckend.** Dass der Gast seinen Vertrag haelt, ist eine
    /// Aussage ueber die Umgebung; sie muss erklaert und FALSIFIZIERBAR sein
    /// (`N004`/`N005`) -- dieselbe Regel wie `progress` (`S003`/`S004`).
    pub annahme: Ident,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct BootDecl {
    pub name: Ident,
    pub arch: Ident,
    pub schritte: Vec<BootSchritt>,
    pub dispatch: Pfad,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum BootSchritt {
    Ruf(Ruf),
    Setzt { name: Ident, wert: Expr },
}
