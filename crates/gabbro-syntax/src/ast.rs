//! Der Kernbaum. **Eine Regel der EBNF -- ein Knoten hier.**
//!
//! Der Baum deutet nichts: er hebt keine Klammer auf, sortiert keine Vertragsklausel um und
//! kennt keine Voreinstellung. Was in `SYNTAX.md` fakultativ ist, ist hier `Option`; was dort
//! Pflicht ist, ist hier ein Feld ohne `Option`. Ein Pass, der eine Pflicht prueft, prueft
//! damit den **Inhalt**, nie die Anwesenheit -- ausser bei `effects`, wo die Anwesenheit die
//! Pflicht ist (`SPRACHE.md` §7: nicht fail-open).

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
// 1. Programm, Module, Konstanten
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Programm {
    pub items: Vec<Item>,
}

#[derive(Debug, Clone)]
pub struct Item {
    /// `when constexpr` -- die bedingte Uebersetzung, an jedem Item.
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
    /// `group N over { A, B };` -- ein Traegerverbund mit Verbindungs-Invariante.
    Gruppe(GruppeDecl),
    Accumulates(AccDecl),
    Walk(WalkDecl),
    Entry(EntryDecl),
    Boot(BootDecl),
}

impl ItemArt {
    /// Der Name, unter dem das Item deklariert ist -- fuer den Namenspass.
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
            ItemArt::Accumulates(a) => Some(&a.name),
            ItemArt::Walk(w) => Some(&w.name),
            ItemArt::Entry(e) => Some(&e.name),
            ItemArt::Boot(b) => Some(&b.name),
        }
    }

    /// Wie die Art in einer Absage heisst.
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
            ItemArt::Gruppe(_) => "group",
            ItemArt::Accumulates(_) => "accumulates",
            ItemArt::Walk(_) => "walk",
            ItemArt::Entry(_) => "entry",
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

/// Eine Zeichenkette samt Fundstelle. Zeichenketten gibt es nur in `claim`, `reason`,
/// `assume`, `section` und `unfalsifiable`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Textliteral {
    pub text: String,
    pub span: Span,
}

// ---------------------------------------------------------------------------------------
// 2. Typen
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct TypDecl {
    pub oeffentlich: bool,
    pub opaque: bool,
    pub linear: bool,
    pub ghost: bool,
    pub tagged: bool,
    pub name: Ident,
    /// `type Duty(check)` -- die Parameterliste eines linearen Zeugen.
    pub parameter: Option<Vec<TypExpr>>,
    pub rumpf: Option<TypExpr>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TypExpr {
    Int(IntTy),
    Bool(Span),
    Never(Span),
    Pfad(Pfad),
    Feld(Box<ArrayTy>),
    Zeiger(Box<PtrTy>),
    Verbund(Vec<FeldDecl>, Span),
    FnZeiger(Box<FnZeiger>),
    Varianten(Vec<Variante>, Span),
    /// `[option] index into T` -- der aus `T`s `count` **erzeugte** Indextyp.
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
    /// `..<` -- obere Grenze ausgeschlossen.
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
    /// `embeds [ hoch : tief ] [ scale konst ]` -- ein Zeiger, der zugleich Bitfeld ist.
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
// 4. Ausdruecke
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Expr {
    pub art: ExprArt,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExprArt {
    Zahl(u128),
    Wahr,
    Falsch,
    Ort(Ort),
    Ruf(Ruf),
    Klammer(Box<Expr>),
    Eingebaut(Box<Eingebaut>),
    /// `old(place)` -- Ausdruck, nicht Praedikat; nur in `ensures`.
    Alt(Ort),
    /// `result` -- der Rueckgabewert in `ensures`.
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
    /// Der Ort, wie er in der Quelle stand -- fuer Manifest und Absagen.
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
                // Der Index ist ein Ausdruck; das Manifest nennt die Stelle, nicht den Wert.
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

/// `call = path "(" [ arglist ] ")"` -- syntaktisch dieselbe Form wie `cast`.
#[derive(Debug, Clone)]
pub struct Ruf {
    pub pfad: Pfad,
    pub argumente: Vec<Expr>,
    pub span: Span,
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
// 5. Praedikate -- hier liegt die Linie
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Pred {
    pub art: PredArt,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum PredArt {
    /// Ein `cmpexpr` als Atom.
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
    /// `Held(L)` bzw. `Held(L, shared)` -- **der Sperrzeuge MIT seiner Staerke.**
    ///
    /// Bis 2026-08-15 war das ein gewoehnlicher Aufruf im Praedikat und trug keine
    /// Staerke; damit war `requires Held-shared` nicht schreibbar, und die Zwischenregel
    /// `H005` musste JEDEN Zeugen unter geteilter Nahme sperren.
    Held {
        sperre: Ident,
        geteilt: bool,
        span: Span,
    },
    Klammer(Box<Pred>),
    Nicht(Box<Pred>),
    Und(Box<Pred>, Box<Pred>),
    Oder(Box<Pred>, Box<Pred>),
    /// `=>` -- Implikation.
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

/// Die acht Domaenen. **Geschlossen** -- es gibt keine benutzerdefinierte.
#[derive(Debug, Clone)]
pub enum Domaene {
    SlotsVon(Ort),
    KetteIn { a: Ident, b: Ident, ort: Ort },
    NachfahrenVon(Ort),
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
            Domaene::Schlange(_) => "queue",
            Domaene::FelderVon(_) => "fields of",
            Domaene::ElementeVon(_) => "elems of",
            Domaene::Threads => "threads",
            Domaene::AbbildungenVon(_) => "mappings of",
        }
    }
}

// ---------------------------------------------------------------------------------------
// 6. Funktionen und Vertraege
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
    /// `None` heisst: die Klausel fehlt. Das ist ein Fehler ausser bei `spec fn`
    /// -- `effects` ist nicht fail-open.
    pub effects: Option<Wirkungen>,
    pub costs: Option<Expr>,
    pub by: Vec<Induktion>,
    pub section: Option<Textliteral>,
    pub arch: Option<Ident>,
    pub when: Option<Expr>,
    pub rumpf: FnRumpf,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FnKlasse {
    Spec,
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
    /// `= pred ;` -- nur fuer `spec fn`.
    Pred(Pred),
    /// `;` -- Deklaration ohne Rumpf.
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
    /// `locks shared N` -- **geteilte Nahme.** Erlaubt Lesen der geschuetzten Plaetze,
    /// verbietet Schreiben; mechanisch gegen `protects` pruefbar.
    SperrtGeteilt(Ort),
    Maskiert(Ident),
    Belegt(Ident),
    Verbraucht(Ort),
    Veroeffentlicht(Ort),
    Divergiert,
    Rein,
}

impl WirkungArt {
    /// Wirkung samt Gegenstand: `writes c.slots`, nicht bloss `writes`.
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

/// `induct = "induction" "over" domain` -- **nennt** das erzeugte Schema, beweist nicht.
#[derive(Debug, Clone)]
pub struct Induktion {
    pub domaene: Domaene,
    pub span: Span,
}

// ---------------------------------------------------------------------------------------
// 7./8. Anweisungen und Schleifen
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
    /// `let ident = call else (ident) block` -- die einzige Fehlerfortpflanzung.
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
    pub ruf: Ruf,
    pub fehlername: Ident,
    pub sonst: Block,
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
    /// Die Bedingung und ihr Block; weitere Eintraege sind `else if`.
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
    pub bereich: Bereich,
    pub sonst: Block,
}

#[derive(Debug, Clone)]
pub struct SperrtStmt {
    pub sperre: Ort,
    /// `locks shared N { … }` -- die geteilte Nahme. **Der heisse Pfad eines Kernels nimmt
    /// so**: die Cap-Aufloesung liest nur (MESSUNGEN.md, Papiertest: 33 gegen 44).
    pub geteilt: bool,
    pub rumpf: Block,
}

#[derive(Debug, Clone)]
pub struct PublishStmt {
    pub ziel: Ort,
    pub wert: Expr,
    pub nutzlast: Nutzlast,
}

/// `publishes ( placelist | "nothing" )` -- `nothing` ist ein Wort, kein leeres Listenloch.
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
    /// `update(ident) block` -- der Rumpf rechnet alt -> neu.
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
// 9. Tabellen, Traversierungen, Formate
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Tabelle {
    pub name: Ident,
    /// `count N` -- die Zahl der Slots. **Ohne sie hat `index into T` keine Obergrenze aus
    /// der Deklaration**, und „kein ungeprueftes Indizieren" ruht auf der Konvention, dass
    /// jemand von Hand einen passenden Indextyp gewaehlt hat (Befund G8).
    pub kapazitaet: Option<Expr>,
    pub konstanten: Vec<KonstDecl>,
    pub slot: Option<SlotDecl>,
    pub invarianten: Vec<Invariante>,
    /// `ops identlist ;` -- die **erzeugten** Mutationen.
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
    /// **`by ops`** — dieses Feld schreiben nur die erzeugten Operationen der Tabelle.
    /// Die K-Bedingung wird damit von einer Pruefvorschrift zu einer Grammatikeigenschaft.
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
// 10. Geraete
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
    /// **«B32»:** der Umlauf ist am Register AUSGESPROCHEN, nicht geduldet. Er gilt dann
    /// fuer jede Rechnung auf diesem Register -- die staerkere Form, weil sie an der
    /// Deklaration steht und nicht an der einen Rechnung, an die jemand gedacht hat.
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
    /// `w1c` -- Schreiben einer Eins loescht.
    W1c,
    /// `rc` -- Lesen loescht.
    Rc,
}

#[derive(Debug, Clone)]
pub struct Uebergang {
    pub name: Ident,
    /// `transset` -- MEHRERE Orte in EINEM Zug.
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
// 11. Nebenlaeufigkeit
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct AtomicDecl {
    pub oeffentlich: bool,
    pub name: Ident,
    pub typ: TypExpr,
    /// Die **Obermenge** der Nutzlast an der Deklaration (SPRACHE.md §11.3). Die Pflicht sitzt
    /// am Store; diese Angabe ist freiwillig und wird gegen jede Store-Nutzlast geprueft.
    /// Sie steht heute **nicht** in der EBNF -- s. Absage `P031`.
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

/// **`group N over { A, B };` -- der Traegerverbund.**
///
/// Der gemessene Bedarf steht im SWEEP der Verbindungs-Invarianten (`MESSUNGEN.md`,
/// 2026-08-16): vier Invarianten zwischen je zwei Traegern, und **eine davon (V4) laeuft
/// ueber zwei Kisten mit zwei Sperren.** Was eine einzelne Tabelle nicht ausdruecken kann:
/// *„der Zaehler in A entspricht der Zahl der Verweise in B"* -- keine `table`-Invariante
/// kann das, weil sie nur ueber ihrem eigenen Traeger quantifiziert.
///
/// **Die Sperrordnung wird NICHT erneut deklariert.** Sie steht schon: jeder Traeger liegt
/// unter einer `lock … protects { … } rank N`, und die Raenge geben die Ordnung. Eine zweite
/// Deklaration waere eine zweite Wahrheit ueber dieselbe Sache.
#[derive(Debug, Clone)]
pub struct GruppeDecl {
    pub name: Ident,
    /// Die Traeger. **Mindestens zwei** -- eine Gruppe mit einem Mitglied ist eine Tabelle.
    pub traeger: Vec<Ident>,
    /// **Die Verbindungs-Invarianten.** Der Grund, warum es die Gruppe gibt: eine Aussage,
    /// die ueber MEHREREN Traegern quantifiziert und die deshalb an keiner einzelnen
    /// `table … invariant` stehen kann.
    pub invarianten: Vec<Invariante>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct LockDecl {
    pub name: Ident,
    pub schuetzt: Vec<Ort>,
    pub rang: Expr,
    /// `held <= constexpr ops` -- ohne sie ist die Sperre in Dienstschleifen nicht nehmbar.
    pub haltezeit: Option<Expr>,
    /// `shared held <= constexpr ops` -- **der eigene Zweig fuer Leser-Schreiber-Sperren.**
    /// `held` ist fuer EXKLUSIVE Halter gedacht; auf der geteilten Seite ist die
    /// Rechengroesse eine andere, und ohne diese Zahl hat die Latenzaussage aus §9.3 fuer
    /// eine geteilt genommene Sperre keinen Zweig (MESSUNGEN.md, Nebenbefund N3).
    pub geteilte_haltezeit: Option<Expr>,
    pub maskiert: Option<Ident>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct AccDecl {
    pub name: Ident,
    pub typ: TypExpr,
    pub merge: MergeOp,
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
// 12. Hardwareannahmen und Axiome
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
    /// **G2.** `axiom rdtscp() -> u64 requires Has(RDTSCP) …` war bis 2026-08-15 nicht
    /// schreibbar. Betrifft die Axiomschicht, also den groessten unbewiesenen Posten.
    pub rueckgabe: Option<TypExpr>,
    pub requires: Vec<Pred>,
    pub effects: Wirkungen,
    pub klasse: AnnahmeKlasse,
    pub span: Span,
}

/// Drei Klassen, und die dritte gibt es syntaktisch nicht: *nicht gefahren* ist die
/// **Abwesenheit beider Angaben** und damit ein Uebersetzungsfehler.
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
// 14. Eintritt und Boot
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
