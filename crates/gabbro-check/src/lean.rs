//! **The BODY channel: a Gabbro body as a Lean 4 term, and its obligation as a theorem.**
//!
//! `refinement.rs` writes the same register as Isabelle quoted and refuses seventeen of its
//! obligations with one word: `body-effect` -- *"speaks about the world AFTER a body ran,
//! and there is no semantics of a Gabbro body"*. **This module is that semantics' other
//! half.** The meaning itself lives in `programmlogik/Gabbro/Body.lean`, written once by
//! hand; what stands here only translates a body into a datum of it.
//!
//! ## Why the meaning is not in this file
//!
//! A translator that both *defines* what a body means and *decides* whether the obligation
//! holds has no independent reader. `Body.lean` is readable Lean with its own theorems, and
//! this file emits data against it. *That split is the whole reason a prover is worth
//! anything here* -- the same relation `lean4export` has to the Lean kernel.
//!
//! ## What the plumbing pays for, and it is the reason this file is short
//!
//! Nine of eleven classes are carried by the language, so the model underneath needs no
//! heap, no separation logic, no pointers and no concurrency (`Body.lean`, header). The
//! places a body touches are the declared `effects` list, and that this covers the
//! transitive effect is proved -- `Passlogik.Wirkung.huelle_deckt`.
//!
//! ## The two gates, and they carry the same weight as in `refinement.rs`
//!
//! 1. **A typing hypothesis is read from the DECLARATION, never from the use.** Guessing
//!    `c.slots[s].elter` is an option because the body matches on it would make the goal
//!    easier, not harder -- the exact shape of quiet weakening this channel exists against.
//! 2. **The goal is the STRONG form**: the body runs to an end *and* the postcondition
//!    holds. `\forall l', end = some l' -> P l'` would be vacuously true for a body that
//!    gets stuck, and a vacuous theorem reads exactly like a proved one.

use gabbro_syntax::ast::*;
use std::collections::HashMap;

/// **Why an obligation carries no Lean goal.** Exhaustive, and each arm names a different
/// missing thing -- a single "not supported" would hide that they have different prices.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LeanReason {
    /// An `ensures` at a body Gabbro never sees. **An assumption, not a goal.**
    ForeignBody,
    /// `maintains I` -- a table invariant, and a table invariant is a QUANTIFIED statement
    /// over every slot. This channel has no quantifier, and inventing one that ranges over
    /// `Int` instead of over the declared capacity would prove a different sentence.
    Invariant,
    /// A precondition at a call site. **Not a gap:** the Isabelle channel carries these, and
    /// twelve of them are discharged by the lock passes before any prover sees them.
    CallSite,
    /// A promise at a device register -- hardware Gabbro does not see.
    DevicePromise,
    /// An invariant of a `walk`. **Quantified over `mappings of`, whose bound is `node
    /// length ^ levels`** -- a set this channel has no quantifier for, exactly as with a
    /// table invariant. *It is refused here for the same reason and booked separately,
    /// because the two are owed by different things:* a table invariant by a function that
    /// names it in `maintains`, a walk invariant by nobody at all.
    WalkInvariant,
    /// A CALL. **The biggest single item of the register, and it is not an oversight**: a
    /// call is to be taken compositionally over the callee's CONTRACT, never over its body.
    /// Inlining the body would make the goal a statement about a program nobody wrote.
    CallStatement,
    /// A loop -- `traverse`, `retry`, `forever`. The measure is carried by the language
    /// (`K008`/`K009`); what is missing is the INVARIANT, and Gabbro has no word for one at
    /// a loop (`Traverse`/`Retry`/`Forever` have no such field, `Tabelle` does).
    Loop,
    /// `locks S { … }`. **The one concurrent statement that costs no memory model** -- see
    /// `LockStatement` for why it is now carried and this arm is only the fallback.
    Concurrent,
    /// `publishes` -- a release store with a payload. **Here one state stops carrying**: it
    /// takes VISIBILITY, and that is a memory model.
    Publish,
    /// `awaits` -- the other half of the pairing.
    Await,
    /// `exchange` -- an atomic swap. Visibility plus atomicity as a notion.
    Exchange,
    /// `observes D { … }` -- the RCU read side: a view that MAY be stale. Semantically the
    /// dearest of the five; it needs "valid but not current" as a notion.
    Observe,
    /// `let … else` -- the one error propagation, two exits out of a call. It waits on the
    /// call gate and on nothing else.
    ErrorPropagation,
    /// `narrow … to … else` -- and the range lattice underneath is already proved
    /// (`Passlogik.Bereich`, 46 theorems). This one is close.
    Narrowing,
    /// `leave` and `next` -- a non-local exit out of a named loop.
    ///
    /// **`breaking` left this arm on 2026-08-28 and it never belonged in it**
    /// (`messung/AUSSETZUNG.md`): a suspension changes which DUTY holds, not
    /// which statements run, so it is carried like a `locks`. All four obligations this
    /// reason held were `breaking`, and the number therefore said the channel was waiting on
    /// a loop gate that would have taken none of them.
    ///
    /// What is left is a real exit, and what it needs is now nameable: **a fourth
    /// `Outcome`.** `Outcome` has `running`, `returned` and `stuck`; a `leave` leaves a block
    /// without returning, and no arm of the three says that.
    NonLocalExit,
    /// `+=` and its kin. It desugars to `x = x + e` -- **but the two are not the same
    /// statement in Gabbro's overflow accounting, and this channel does not get to decide
    /// that.**
    CompoundAssign,
    /// A `match` over something other than an `option`. A declared sum type would need one
    /// value constructor per variant.
    MatchNotOption,
    /// A floating-point value. The model has no float, and one that rounded differently from
    /// the hardware would prove the wrong thing quietly.
    Float,
    /// `old(x)` -- a predicate over TWO states. Everything here speaks about one.
    OldState,
    /// A QUANTIFIER, `reaches`, or a set membership. This is where a `spec fn` runs out and
    /// a hand-written Lean specification does not -- `gabbro lean` exists for it.
    Quantified,
    /// A call inside an expression: a `spec fn` or a pure function. **It waits on the same
    /// gate as a call statement** -- over the CONTRACT, never over the body.
    CallInExpression,
    /// A built-in: `lenof`, `sizeof`, `aligned`, `offset_into`. Each names something about
    /// the LAYOUT, and this model has none.
    Builtin,
    /// `Held(L)`. **Not a gap at all** -- the lock passes discharge it (`H005`, `H006`,
    /// `H012`, `H016`). Reporting it as "no term" counted a carried obligation as a missing
    /// translation; the Isabelle channel has said the true thing about it since day one.
    LockWitness,
    /// `result` in a clause of the EXPORT datum. **Not a gap and not a gate**: the datum's
    /// `post` list is what a CALLER may assume, and a caller reads the callee's result at its
    /// own call site rather than out of a name this datum binds. *A promise fewer makes a
    /// caller's goal harder, never wrong.*
    ///
    /// **The obligation channel does NOT refuse this** -- it binds `result` and writes the
    /// goal. Until 2026-08-30 this variant carried the sentence *"one gate away, not far"*
    /// and BOTH cases below, and the sentence had outlived the gate: the gate is built.
    Result,
    /// `result` in a BODY -- a statement, or the invariant of a loop inside one.
    ///
    /// **This is a PROGRAM error and no gate of this channel will ever carry it.** `result`
    /// names the returned value; inside a body nothing has returned yet, so the word names
    /// nothing. It is a RESERVED word, so no `let` and no parameter can have bound it either.
    ///
    /// *It stands apart from `Result` because the two point opposite ways*: one is a promise
    /// this channel declines to repeat, the other is a source that says something it cannot
    /// mean. A reader who finds them under one name looks for a missing gate and reads a
    /// gap where a refusal stands.
    ResultInBody,
    /// An error reason value (`R::F`) or a function pointer.
    OtherValue,
    /// An expression or predicate form with no Lean term here.
    Expression,
    /// A place whose carrier cannot be resolved to a declared `table`. **Without the
    /// declaration there is no field shape**, and without the field shape the hypothesis
    /// would have to be guessed -- see gate 1.
    Carrier,
    /// A field whose declared type has no shape in this channel -- `wrapping`, a float, a
    /// record, or an OPAQUE new type whose representation `D1` forbids reading.
    ///
    /// **It stands beside `Carrier` and not inside it**, and the split was measured: the
    /// first run reported `carrier-not-a-table` for `Buch.slots[p].wert`, where `Buch` is a
    /// table and `wert` is a `Zaehler`. *A refusal filed under the wrong reason names a
    /// missing declaration where a missing translation stands* -- the same lesson
    /// `messung/P6.md` §3.2 books for twelve obligations.
    FieldShape,
    /// A `refines` whose named `spec fn` is not a plain expression body.
    SpecShape,
    /// A call to a GENERATED table operation -- `Verzeichnis::insert(v, i)`.
    ///
    /// **It stands apart from `CallStatement`, and the split was measured** (2026-08-28,
    /// `messung/RUF-TOR.md`): six of the seventeen refusals filed as "a call, and that gate
    /// is not built" are these, and no gate over a CONTRACT would take one of them. *An
    /// operation has no `ensures` to carry.* What it has is a SCHEMA -- `opsruf::koepfe`
    /// cuts the premises, `schablonen.rs` registers them -- and a schema is a different
    /// thing to assume than a callee's promise.
    GeneratedOp,
    /// A `transition` of a `device` -- `anerkennen(g)`, `wurzel_setzen(v)`.
    ///
    /// It looks exactly like a call and is a REGISTER WRITE. Five of the seventeen. It waits
    /// on hardware this model does not have, which is the same place `DevicePromise` waits
    /// -- but that arm is about an obligation AT a register, and this one is a statement in
    /// a body. *Two different things under one name is how seventeen came about.*
    Transition,
    /// A constructor whose VALUE this model has no form for -- a record, a `tagged`, or a
    /// device handle: `Completion(id: k, len: n)`, `Dma(GERAETEBASIS)`.
    ///
    /// `Value` is four forms and the list is closed (`Body.lean` §1). A record is not among
    /// them, and neither is a handle. **The price is a model extension**, and it is a
    /// different price from a missing gate.
    ConstructedValue,
}

impl LeanReason {
    pub fn tag(self) -> &'static str {
        match self {
            LeanReason::ForeignBody => "foreign-body",
            LeanReason::Invariant => "table-invariant",
            LeanReason::CallSite => "call-site",
            LeanReason::DevicePromise => "device-promise",
            LeanReason::WalkInvariant => "walk-invariant",
            LeanReason::CallStatement => "call-not-compositional",
            LeanReason::Loop => "loop",
            LeanReason::Concurrent => "concurrent-statement",
            LeanReason::Publish => "publish",
            LeanReason::Await => "await",
            LeanReason::Exchange => "exchange",
            LeanReason::Observe => "observe",
            LeanReason::ErrorPropagation => "let-else",
            LeanReason::Narrowing => "narrow",
            LeanReason::NonLocalExit => "non-local-exit",
            LeanReason::CompoundAssign => "compound-assignment",
            LeanReason::MatchNotOption => "match-not-option",
            LeanReason::Float => "float",
            LeanReason::OldState => "old-state",
            LeanReason::Quantified => "quantified",
            LeanReason::CallInExpression => "call-in-expression",
            LeanReason::Builtin => "builtin",
            LeanReason::LockWitness => "lock-witness",
            LeanReason::Result => "result-in-ensures",
            LeanReason::ResultInBody => "result-in-body",
            LeanReason::OtherValue => "other-value",
            LeanReason::Expression => "no-term",
            LeanReason::Carrier => "carrier-not-a-table",
            LeanReason::FieldShape => "no-shape-for-field",
            LeanReason::SpecShape => "spec-not-an-expression",
            LeanReason::GeneratedOp => "generated-op",
            LeanReason::Transition => "device-transition",
            LeanReason::ConstructedValue => "constructed-value",
        }
    }
    pub fn sentence(self) -> &'static str {
        match self {
            LeanReason::ForeignBody => {
                "an `ensures` at a body Gabbro never sees: an ASSUMPTION, not a goal"
            }
            LeanReason::Invariant => {
                "`maintains` names a table invariant, and that is quantified over every slot"
            }
            LeanReason::CallSite => {
                "a precondition at a call site -- the Isabelle channel carries these"
            }
            LeanReason::DevicePromise => "a promise at hardware Gabbro does not see",
            LeanReason::WalkInvariant => {
                "an invariant of a `walk`, quantified over `mappings of` -- and no pass \
                 decides it either"
            }
            LeanReason::CallStatement => {
                "a call -- compositional over the CONTRACT, and that gate is not built"
            }
            LeanReason::Loop => "a loop -- the measure is carried, the INVARIANT has no word",
            LeanReason::Concurrent => {
                "a concurrent statement -- one state and one transition stop carrying here"
            }
            LeanReason::Publish => "`publishes` -- a release store; it takes VISIBILITY",
            LeanReason::Await => "`awaits` -- the other half of the pairing",
            LeanReason::Exchange => "`exchange` -- visibility plus atomicity as a notion",
            LeanReason::Observe => "`observes` -- a view that MAY be stale",
            LeanReason::ErrorPropagation => "`let … else` -- two exits out of a call",
            LeanReason::Narrowing => "`narrow` -- the range lattice under it is proved",
            LeanReason::NonLocalExit => {
                "`leave`/`next` -- a real exit, and `Outcome` has no fourth form for one"
            }
            LeanReason::CompoundAssign => "`+=` and its kin -- a different overflow accounting",
            LeanReason::MatchNotOption => "a `match` over something other than an `option`",
            LeanReason::Float => "a floating-point value -- this model has no float",
            LeanReason::OldState => "`old(x)` -- a predicate over TWO states",
            LeanReason::Quantified => {
                "a quantifier, `reaches` or a membership -- where a `spec fn` runs out"
            }
            LeanReason::CallInExpression => "a call inside an expression -- same gate as a call",
            LeanReason::Builtin => "a built-in about the LAYOUT, and this model has none",
            LeanReason::LockWitness => {
                "`Held(…)` -- carried by the lock passes (H005/H006/H012/H016), not by a prover"
            }
            LeanReason::Result => {
                "`result` in an `ensures` -- the export datum drops it; the goal channel CARRIES it"
            }
            LeanReason::ResultInBody => {
                "`result` in a BODY, where it names nothing -- a program error, not a gap"
            }
            LeanReason::OtherValue => "an error reason value or a function pointer",
            LeanReason::Expression => "a form this channel has no Lean term for",
            LeanReason::Carrier => {
                "the carrier of a place is not a declared `table`, so no field shape is known"
            }
            LeanReason::FieldShape => {
                "the declared type of a slot field has no shape in this channel"
            }
            LeanReason::SpecShape => "the named `spec fn` is not a plain expression body",
            LeanReason::GeneratedOp => {
                "a generated table operation -- its contract is a SCHEMA, not an `ensures`"
            }
            LeanReason::Transition => "a `transition` of a `device` -- a register write",
            LeanReason::ConstructedValue => {
                "a record, a `tagged` or a device handle -- this model has no value for one"
            }
        }
    }
    /// **All of them, so a report cannot omit one by forgetting to ask.**
    pub const ALL: [LeanReason; 32] = [
        LeanReason::ForeignBody,
        LeanReason::Invariant,
        LeanReason::CallSite,
        LeanReason::DevicePromise,
        LeanReason::CallStatement,
        LeanReason::Loop,
        LeanReason::Concurrent,
        LeanReason::Publish,
        LeanReason::Await,
        LeanReason::Exchange,
        LeanReason::Observe,
        LeanReason::ErrorPropagation,
        LeanReason::Narrowing,
        LeanReason::NonLocalExit,
        LeanReason::CompoundAssign,
        LeanReason::MatchNotOption,
        LeanReason::Float,
        LeanReason::OldState,
        LeanReason::Quantified,
        LeanReason::CallInExpression,
        LeanReason::Builtin,
        LeanReason::LockWitness,
        LeanReason::Result,
        LeanReason::ResultInBody,
        LeanReason::OtherValue,
        LeanReason::Expression,
        LeanReason::Carrier,
        LeanReason::FieldShape,
        LeanReason::SpecShape,
        LeanReason::GeneratedOp,
        LeanReason::Transition,
        LeanReason::ConstructedValue,
    ];
}

/// One closed Lean goal over a body.
pub struct LeanGoal {
    /// `duty_7` -- the position in the register `gabbro pflichten` prints.
    pub name: String,
    /// The body, as a `Gabbro.Body.Stmt` list term.
    pub body: String,
    /// `(label, term, where it came from)` -- every hypothesis, read from a declaration.
    pub hypotheses: Vec<(String, String, String)>,
    /// The postcondition, as a `Gabbro.Body.Expr` that must evaluate to `true`.
    pub conclusion: String,
    /// **Whether the postcondition names `result`** -- and with it, whether the goal also
    /// demands that the body PRODUCED a value. A body that runs off the end has no result,
    /// and a goal that let such a body pass would prove the promise of a routine that never
    /// makes one.
    pub names_result: bool,
    /// **The `obtain` lines the proof opens with.** A hypothesis `\exists n, l.locals "p" =
    /// .z n` tells `simp` nothing until the witness is named; without these the goal stalls
    /// on an unreduced `match` over `l.locals "p"`. *Measured on the first run of this
    /// emitter, and it is why the tactic is generated rather than fixed.*
    pub opening: Vec<String>,
    /// The equation names those `obtain`s bind, for the `simp` set.
    pub equations: Vec<String>,
    /// **The `rcases` fragments, and they are kept apart from `opening` because they must
    /// be CHAINED.** An `rcases` splits the goal, and a plain next line applies only to the
    /// first half -- measured: the second split reported its own witness as an unknown
    /// identifier in every branch the first split had left behind.
    pub splits: Vec<String>,
}

pub enum LeanVerdict {
    Proved(Box<LeanGoal>),
    Refused(LeanReason),
}

/// **What a table declares.** Field name to the shape its declaration gives it.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Shape {
    Int,
    Bool,
    Opt,
}

impl Shape {
    fn predicate(self) -> &'static str {
        match self {
            Shape::Int => "isInt",
            Shape::Bool => "isBool",
            Shape::Opt => "isOption",
        }
    }
}

/// The shape a declared type gives a value. `None` where this channel has no shape for it --
/// **and a place of such a field is refused, not defaulted.**
///
/// **The option distinction is read SYNTACTICALLY and the rest through the environment**,
/// and the split is not tidiness. `option index into T` and `index into T` both resolve to
/// an integer -- the sentinel lowering is the point of `Option_Sonderwert.thy` -- so a
/// resolved type cannot tell them apart. *Asking the resolved type here would silently make
/// every option field a number, and a `match` over it would then be unreachable rather than
/// refused.*
fn shape_of(t: &TypExpr, u: &crate::umgebung::Umgebung, module: &str) -> Option<Shape> {
    if let TypExpr::Index { optional, .. } = t {
        return Some(if *optional { Shape::Opt } else { Shape::Int });
    }
    shape_of_typ(&u.typ_von_ausdruck_decl(module, t))
}

fn shape_of_typ(t: &crate::typen::Typ) -> Option<Shape> {
    use crate::typen::Typ;
    match t {
        Typ::Ganzzahl(_) => Some(Shape::Int),
        Typ::Wahrheit => Some(Shape::Bool),
        Typ::Tabelle(_) => Some(Shape::Int),
        // **An OPAQUE new type stops here and a transparent one does not.** Reading the
        // representation of an `opaque` is exactly the implicit conversion `D1` forbids;
        // a transparent one is a range with a name, and a name is not a wall.
        Typ::Benannt {
            undurchsichtig: false,
            unter,
            ..
        } => shape_of_typ(unter),
        // `wrapping` gives no shape: overflow is the POINT of the type, so unbounded `Int`
        // arithmetic over it would compute something Gabbro does not.
        Typ::Umlaufend(_)
        | Typ::Benannt { .. }
        | Typ::Gleitkomma(_)
        | Typ::Nie
        | Typ::Zeiger(_)
        | Typ::Summe { .. }
        | Typ::Verbund(_)
        | Typ::Feld { .. }
        | Typ::Register { .. }
        | Typ::Verbundname(_)
        | Typ::FnPtr(_)
        | Typ::Unbekannt
        | Typ::Grund(_) => None,
    }
}

/// **Where the thing being translated stands, as far as the word `result` is concerned.**
///
/// The three cases are not three degrees of one permission -- they are three different
/// answers, and two of them are refusals that mean opposite things. Keeping them in one
/// `bool` made `result-in-ensures` name a body.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ResultSite {
    /// A body: a statement, or the invariant of a loop inside one. `result` names nothing
    /// here and never will.
    Body,
    /// A `requires` or `ensures` of the EXPORT datum, which does not bind `result` on purpose.
    Contract,
    /// The postcondition of an obligation. The goal binds `result` as a local before
    /// evaluating, exactly as a parameter is read from `local'`.
    Bound,
}

/// Everything the translation of one body may look at.
struct Ctx<'a> {
    /// Table name to its slot fields, as declared.
    tables: &'a HashMap<String, Vec<(String, Option<Shape>)>>,
    /// Record and `format` declarations: name to its fields, with the shape each declares.
    /// **Beside the tables and not among them** -- a record is ONE object, a table is a row
    /// of them, and one map would let a slot field alias a record field.
    records: &'a HashMap<String, Vec<(String, Option<Shape>)>>,
    /// Base name to the record or `format` it stands for.
    record_carrier: HashMap<String, String>,
    /// The declaring function's parameters: name to the table its type points at, if any.
    carrier: HashMap<String, String>,
    /// Parameter and `let` names -- these read from `locals`, not from the world.
    locals: Vec<String>,
    /// **Whether a CALL may be translated.** The program export says yes: it writes a datum,
    /// and a datum of a call is honest -- the callee is named, not inlined. The obligation
    /// channel says no: it writes a GOAL, and a goal over a body that calls needs the
    /// callee's contract as a hypothesis. *Emitting the goal without it would state
    /// something no proof can close, and a red guard is not a measurement.*
    allow_calls: bool,
    /// Callee name to its parameter names, so a call can bind them.
    callees: &'a HashMap<String, Vec<String>>,
    /// **WHERE the thing being translated stands**, which decides both whether `result` may
    /// be translated and -- when it may not -- which refusal is honest.
    ///
    /// It was a `bool` until 2026-08-30, and a `bool` has two states where the channel has
    /// three: a body, a clause of the export datum, and the postcondition of a goal. *The two
    /// that refuse refuse for opposite reasons*, and under one flag they had to share one
    /// name. The field is set at each call site rather than toggled globally, so the site is
    /// a fact about what is being read and not about how far the run has got.
    result_site: ResultSite,
    /// Set while translating the conclusion, where `result` really occurred. **The goal
    /// shape depends on it**: only a postcondition that names the returned value has to
    /// demand that the body produced one.
    uses_result: bool,
    /// **What a call path names when it is NOT a routine call.** Empty means "a routine
    /// call, or nothing this unit declares" -- see `foreign_calls`.
    foreign: &'a HashMap<String, LeanReason>,
    /// Collected while translating: `(carrier, field, form, origin)`, deduplicated.
    seen: Vec<(String, String, Shape, String)>,
    /// `(carrier, field, shape)` for every RECORD field touched.
    seen_records: Vec<(String, String, Shape)>,
    /// The routine's name and how many loops have been numbered in it. **Every loop needs an
    /// id of its own** -- two loops under one name would share an environment entry, and a
    /// hypothesis about the first would silently cover the second.
    routine: String,
    loops: usize,
    /// **Every `(carrier, field, index-parameter)` read at an option-shaped field.**
    ///
    /// `istWahl` is a DISJUNCTION, and `simp` cannot open one: without the case split the
    /// goal stalls on an unreduced `match` over the field. *Measured on the first corpus
    /// run of this channel -- `aushaengen` was the one red module of sixty-eight, and the
    /// reason was this and nothing else.*
    option_reads: Vec<(String, String, String)>,
}

impl Ctx<'_> {
    /// **Which table does this base name stand for?** A bare table name stands for itself;
    /// a parameter stands for the table its pointer type names.
    fn table_of(&self, base: &str) -> Option<&String> {
        self.carrier.get(base)
    }

    /// A place whose index is a bare parameter, at an option-shaped field: the proof will
    /// have to split on it.
    fn note_option(&mut self, carrier: &str, feld: &str, form: Shape, index: &Expr) {
        if form != Shape::Opt {
            return;
        }
        let ExprArt::Ort(o) = &index.art else { return };
        if !o.suffixe.is_empty() {
            return;
        }
        let p = o.basis.text.clone();
        if !self
            .option_reads
            .iter()
            .any(|(t, f, i)| t == carrier && f == feld && *i == p)
        {
            self.option_reads
                .push((carrier.to_string(), feld.to_string(), p));
        }
    }

    /// A record field that was read or written, for the well-formedness hypothesis.
    fn note_record(&mut self, carrier: &str, feld: &str, shape: Shape) {
        if !self
            .seen_records
            .iter()
            .any(|(t, n, _)| t == carrier && n == feld)
        {
            self.seen_records
                .push((carrier.to_string(), feld.to_string(), shape));
        }
    }

    fn note(&mut self, carrier: &str, feld: &str, f: Shape, origin: &str) {
        if !self
            .seen
            .iter()
            .any(|(t, n, _, _)| t == carrier && n == feld)
        {
            self.seen.push((
                carrier.to_string(),
                feld.to_string(),
                f,
                origin.to_string(),
            ));
        }
    }
}

fn quoted(s: &str) -> String {
    // Gabbro identifiers are ASCII words; this fires on nothing in today's corpus, and that
    // is exactly why it stands here instead of being assumed.
    format!("\"{}\"", s.replace('\\', "").replace('"', ""))
}

/// **Carrier, field, shape -- and the two refusals are DIFFERENT ones.**
///
/// A base that names no table is `Carrier`; a field the table does declare but whose type
/// this channel has no shape for is `FieldShape`. *The first says a declaration is missing,
/// the second says a translation is.* Folding them would report `Buch.slots[p].wert` as an
/// unknown carrier, and `Buch` is right there in the file.
fn field_shape(base: &str, feld: &str, c: &Ctx) -> Result<(String, Shape, String), LeanReason> {
    let tab = c.table_of(base).ok_or(LeanReason::Carrier)?.clone();
    let fields = c.tables.get(&tab).ok_or(LeanReason::Carrier)?;
    let (_, form) = fields
        .iter()
        .find(|(n, _)| n == feld)
        .ok_or(LeanReason::Carrier)?;
    let form = form.ok_or(LeanReason::FieldShape)?;
    Ok((base.to_string(), form, tab))
}

/// **Carrier and shape of a RECORD field.** The two refusals stay apart for the same reason
/// they do at a table: a base that names no declaration is `Carrier`, a field whose declared
/// type has no shape here is `FieldShape`.
fn record_field(base: &str, field: &str, c: &Ctx) -> Result<(String, Shape), LeanReason> {
    let rec = c.record_carrier.get(base).ok_or(LeanReason::Carrier)?;
    let fields = c.records.get(rec).ok_or(LeanReason::Carrier)?;
    let (_, shape) = fields
        .iter()
        .find(|(n, _)| n == field)
        .ok_or(LeanReason::Carrier)?;
    Ok((base.to_string(), shape.ok_or(LeanReason::FieldShape)?))
}

/// A place, as a `Gabbro.Body.Expr`. **Three forms and nothing else:** a bare name,
/// `carrier.slots[i].field`, and `carrier.field`.
fn place_term(o: &Ort, c: &mut Ctx) -> Result<String, LeanReason> {
    if o.suffixe.is_empty() {
        let n = &o.basis.text;
        return Ok(if c.locals.iter().any(|l| l == n) {
            format!("(.name {})", quoted(n))
        } else {
            format!("(.global {})", quoted(n))
        });
    }
    // **One field and no index is a RECORD field.** `s.len`, `header.e_entry` -- one object,
    // not a row of them.
    if let [OrtSuffix::Feld(f)] = &o.suffixe[..] {
        let (base, shape) = record_field(&o.basis.text, &f.text, c)?;
        c.note_record(&base, &f.text, shape);
        return Ok(format!("(.fieldOf {} {})", quoted(&base), quoted(&f.text)));
    }
    let [OrtSuffix::Feld(slots), OrtSuffix::Index(i), OrtSuffix::Feld(f)] = &o.suffixe[..] else {
        return Err(LeanReason::Carrier);
    };
    if slots.text != "slots" {
        return Err(LeanReason::Carrier);
    }
    let (base, shape, tab) = field_shape(&o.basis.text, &f.text, c)?;
    let idx = expr_term(i, c)?;
    c.note(&base, &f.text, shape, &format!("`{}` in `{}`", f.text, tab));
    c.note_option(&base, &f.text, shape, i);
    Ok(format!(
        "(.place {} {} {})",
        quoted(&base),
        idx,
        quoted(&f.text)
    ))
}

/// An expression as a `Gabbro.Body.Expr`.
///
/// **The `match` has no catch-all**, and that is deliberate even though every unlisted arm
/// would refuse: a new expression form must be DECIDED here, not defaulted.
fn expr_term(e: &Expr, c: &mut Ctx) -> Result<String, LeanReason> {
    match &e.art {
        ExprArt::Zahl(n) => Ok(format!("(.lit (.int {n}))")),
        ExprArt::Wahr => Ok("(.lit (.bool true))".into()),
        ExprArt::Falsch => Ok("(.lit (.bool false))".into()),
        ExprArt::Klammer(x) => expr_term(x, c),
        ExprArt::Ort(o) => place_term(o, c),
        ExprArt::Unaer(UnOp::Nicht, x) => Ok(format!("(.un .not {})", expr_term(x, c)?)),
        ExprArt::Unaer(UnOp::Negativ, x) => Ok(format!("(.un .neg {})", expr_term(x, c)?)),
        // **`~` has no term here, and the reason is the model and not the operator.**
        //
        // `Gabbro.Body` carries `.un .not` and `.un .neg`, both of which are width-free over
        // `Int`. A complement is NOT: `~x` is `2^n - 1 - x`, and the `n` is nowhere in this
        // channel -- an expression carries no declared type into `expr_term`. *A term that
        // picked a width would prove a theorem about a program the checker never checked.*
        ExprArt::Unaer(UnOp::BitNicht, _) => Err(LeanReason::Expression),
        ExprArt::Binaer(op, a, b) => {
            let z = match op {
                BinOp::Plus => "add",
                BinOp::Minus => "sub",
                BinOp::Mal => "mul",
                BinOp::Gleich => "eq",
                BinOp::Ungleich => "ne",
                BinOp::Kleiner => "lt",
                BinOp::KleinerGleich => "le",
                BinOp::Groesser => "gt",
                BinOp::GroesserGleich => "ge",
                BinOp::Und => "and",
                BinOp::Oder => "or",
                // **Division and the bit operations, and the honesty is in the MODEL and
                // not in a refusal here.**
                //
                // They stood refused as `division-or-bits` with the sentence *"Lean rounds
                // down where C truncates"*. That sentence was true and the conclusion was
                // not: `Gabbro.Body` now takes `Int.tdiv`/`Int.tmod`, which are the C
                // operators, and §3.2 of the model holds them against Lean's own `/` in a
                // theorem. **What the sentence really named was a case the model could not
                // state, and a case is refused by GETTING STUCK, not by refusing the whole
                // form.** `binop` is `none` at a zero denominator and at a negative operand
                // of a mask or a shift -- so a proof that goes through one of these has to
                // establish the premise, and the goal gets harder rather than easier.
                //
                // *Refusing the form here would have cost five bodies of the corpus for a
                // hazard that lives in two of their operands.*
                BinOp::Geteilt => "div",
                BinOp::Rest => "rem",
                BinOp::BitUnd => "band",
                BinOp::BitOder => "bor",
                BinOp::BitXor => "bxor",
                BinOp::SchiebLinks => "shl",
                BinOp::SchiebRechts => "shr",
            };
            Ok(format!(
                "(.bin .{z} {} {})",
                expr_term(a, c)?,
                expr_term(b, c)?
            ))
        }
        // `None` is a value of the option shape and the commonest right-hand side in the
        // corpus. `Some(e)` is refused: it would need a second value constructor, and no
        // obligation in today's corpus asks for one.
        ExprArt::Ruf(r) => match r.path().and_then(|p| p.teile.last()).map(|i| &i.text) {
            Some(n) if n == "None" && r.argumente.is_empty() => Ok("(.lit .absent)".into()),
            Some(n) if n == "Some" && r.argumente.len() == 1 => {
                Ok(format!("(.someOf {})", expr_term(&r.argumente[0], c)?))
            }
            _ => Err(LeanReason::CallInExpression),
        },
        ExprArt::Gleitkomma { .. } => Err(LeanReason::Float),
        ExprArt::Eingebaut(_) => Err(LeanReason::Builtin),
        ExprArt::Alt(_) => Err(LeanReason::OldState),
        // **`result` is a NAME bound to the returned value, and that is the whole gate.**
        //
        // The model has carried `finalValue` since its first day -- its own doc line says
        // *"For an `ensures` that names `result`"* -- and what was missing was not a form
        // but the binding: a postcondition is evaluated over a `State`, and a result is not
        // part of one. So the goal binds it as a local before evaluating, exactly as a
        // parameter is read from `local'`. *No arm of the model changed for this.*
        //
        // `result` is a RESERVED word, so no `let` and no parameter can carry the name --
        // the binding cannot shadow anything a body wrote.
        ExprArt::Ergebnis => match c.result_site {
            // **Inside a body the word names nothing, and nothing will ever make it.**
            ResultSite::Body => Err(LeanReason::ResultInBody),
            // A clause of the export datum: sayable, deliberately not said.
            ResultSite::Contract => Err(LeanReason::Result),
            ResultSite::Bound => {
                c.uses_result = true;
                Ok("(.name \"result\")".into())
            }
        },
        ExprArt::FnWert(_) | ExprArt::Grund { .. } => Err(LeanReason::OtherValue),
    }
}

/// A predicate as a `Gabbro.Body.Expr` that must evaluate to `true`.
fn pred_term(p: &Pred, c: &mut Ctx) -> Result<String, LeanReason> {
    match &p.art {
        PredArt::Vergleich(e) => expr_term(e, c),
        PredArt::Klammer(q) => pred_term(q, c),
        PredArt::Nicht(q) => Ok(format!("(.un .not {})", pred_term(q, c)?)),
        PredArt::Und(a, b) => Ok(format!(
            "(.bin .and {} {})",
            pred_term(a, c)?,
            pred_term(b, c)?
        )),
        PredArt::Oder(a, b) => Ok(format!(
            "(.bin .or {} {})",
            pred_term(a, c)?,
            pred_term(b, c)?
        )),
        // `a -> b` is `!a || b`. **Not a shortcut:** `Value` has no implication, and adding
        // one to the model for a form that desugars exactly would be a second way to say
        // one thing.
        PredArt::Folgt(a, b) => Ok(format!(
            "(.bin .or (.un .not {}) {})",
            pred_term(a, c)?,
            pred_term(b, c)?
        )),
        PredArt::Held { .. } => Err(LeanReason::LockWitness),
        PredArt::Quantor(_) | PredArt::Element(_, _) | PredArt::Erreicht { .. } => {
            Err(LeanReason::Quantified)
        }
    }
}

/// **`Some(e)` and `None` are VALUES, not calls.**
///
/// The model has carried `.someOf` and `.absent` since its first day (`Body.lean` §3), and
/// `expr_term` translates both. The `let` and `return` arms of `stmt_term` never reached
/// that arm: they saw an `ExprArt::Ruf` and sent it to `call_parts`, which looked up a
/// callee named `Some` in a table that has none and refused the WHOLE body as
/// `call-not-compositional`.
///
/// *Measured on 2026-08-28: `beispiele/27-freiliste.gab :: belegen` was refused as a call
/// although it contains none* (`messung/RUF-TOR.md`). A refusal filed under the wrong reason
/// names a missing gate where a missing route stands -- the same lesson the `Carrier` /
/// `FieldShape` split books above.
fn is_option_value(r: &Ruf) -> bool {
    match r.path().and_then(|p| p.teile.last()).map(|i| i.text.as_str()) {
        Some("None") => r.argumente.is_empty(),
        Some("Some") => r.argumente.len() == 1,
        _ => false,
    }
}

/// **What a call path names when it is not a routine call** -- or `None` where it is one.
///
/// Four different things parse as a call in Gabbro, and until 2026-08-28 all four were
/// refused with the single word `call-not-compositional`. **They have four different
/// prices**, and one number over all of them said the register was waiting on a gate that
/// would have taken none of them (`messung/RUF-TOR.md` §1.1).
fn foreign_kind(r: &Ruf, c: &Ctx) -> Option<LeanReason> {
    // A record or a `tagged` constructor carries FIELD LABELS, and nothing else does --
    // `Ruf::marken` is built at one place and checked at one place (`ast.rs`).
    if r.ist_verbundwert() {
        return Some(LeanReason::ConstructedValue);
    }
    let p = r.path()?;
    // The written path first (`Verzeichnis::insert`), then the bare name -- an operation is
    // only ever an operation under its table's name.
    let full: Vec<String> = p.teile.iter().map(|i| i.text.clone()).collect();
    if let Some(k) = c.foreign.get(&full.join("::")) {
        return Some(*k);
    }
    c.foreign.get(full.last()?).copied()
}

/// **Every call path of the program that is NOT a routine call, with what it is instead.**
///
/// Read once per program out of the DECLARATIONS, never out of the use -- gate 1 of this
/// file. Three sources, and each names a different price:
///
/// * `opsruf::koepfe` -- the generated operations, whose contract is a schema;
/// * a `device`'s name -- the handle constructor, whose value this model has no form for;
/// * a `device`'s `transition`s -- register writes, which take hardware.
fn foreign_calls(baum: &Programm) -> HashMap<String, LeanReason> {
    let mut out = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _| match &item.art {
        ItemArt::Tabelle(t) => {
            for k in crate::opsruf::koepfe(t) {
                out.insert(k.pfad(), LeanReason::GeneratedOp);
            }
        }
        ItemArt::Device(d) => {
            out.insert(d.name.text.clone(), LeanReason::ConstructedValue);
            for u in &d.uebergaenge {
                out.insert(u.name.text.clone(), LeanReason::Transition);
            }
        }
        _ => {}
    });
    out
}

/// **Callee, parameter names and argument terms of a call.** One place, because three
/// statement forms carry a call and each one writing its own lookup is three chances for
/// them to drift apart.
fn call_parts(r: &Ruf, c: &mut Ctx) -> Result<(String, String, String), LeanReason> {
    // **What this path really names, asked BEFORE the gate.** A `transition` refused as
    // "the call gate is not built" would go on waiting for a gate that cannot help it.
    let kind = foreign_kind(r, c);
    let Some(name) = r.path().and_then(|p| p.teile.last()).map(|i| i.text.clone()) else {
        return Err(kind.unwrap_or(LeanReason::CallStatement));
    };
    if let Some(k) = kind {
        return Err(k);
    }
    if !c.allow_calls {
        return Err(LeanReason::CallStatement);
    }
    // **The callee has to be DECLARED here.** A call into a unit this run never read would
    // bind arguments to parameters nobody counted.
    let Some(ps) = c.callees.get(&name).cloned() else {
        return Err(LeanReason::CallStatement);
    };
    if ps.len() != r.argumente.len() {
        return Err(LeanReason::CallStatement);
    }
    let mut args = Vec::new();
    for a in &r.argumente {
        args.push(expr_term(a, c)?);
    }
    let names: Vec<String> = ps.iter().map(|n| quoted(n)).collect();
    Ok((quoted(&name), names.join(", "), args.join(", ")))
}

/// The payload of a `publishes`, as a list of place names. `publishes nothing` is the empty
/// list -- **a word, not an empty hole**, and the datum keeps the distinction.
fn nutzlast(n: &Nutzlast) -> String {
    match n {
        Nutzlast::Orte(os) => os
            .iter()
            .map(|o| quoted(&o.text()))
            .collect::<Vec<_>>()
            .join(", "),
        Nutzlast::Nichts(_) => String::new(),
    }
}

/// A block as a `Gabbro.Body.Stmt` list term.
fn block_term(b: &Block, c: &mut Ctx) -> Result<String, LeanReason> {
    let depth = c.locals.len();
    let mut teile = Vec::new();
    for s in &b.anweisungen {
        teile.push(stmt_term(s, c)?);
    }
    // A `let` name leaves scope with its block -- the model binds by name, so a name that
    // outlived its block would silently shadow one further out.
    c.locals.truncate(depth);
    Ok(format!("[{}]", teile.join(", ")))
}

fn stmt_term(s: &Stmt, c: &mut Ctx) -> Result<String, LeanReason> {
    match &s.art {
        StmtArt::Let(l) => {
            // **`let n = f(a);` is a CALL, not an expression.** A callee may write, so an
            // expression carrying one would no longer be pure -- and `eval` would have to
            // take the environment, which would put the whole model one level up.
            // **`Some(e)` is a VALUE and not a call**, and the test comes first -- see
            // `is_option_value`.
            if let ExprArt::Ruf(r) = &l.wert.art {
                if !is_option_value(r) {
                    let (n, ps, args) = call_parts(r, c)?;
                    c.locals.push(l.name.text.clone());
                    return Ok(format!(
                        "(.bindCall {} {n} [{ps}] [{args}])",
                        quoted(&l.name.text)
                    ));
                }
            }
            let w = expr_term(&l.wert, c)?;
            c.locals.push(l.name.text.clone());
            Ok(format!("(.bindName {} {})", quoted(&l.name.text), w))
        }
        StmtArt::Zuweisung(z) => {
            // **`x += e` is `x = x + e`, and my own refusal of it did not hold.**
            //
            // It stood here with the reason *"the two are not the same statement in Gabbro's
            // overflow accounting"*. They are: `M104` says the RESULT fits the declared
            // range, and both forms have the same result. Plain `+` was already being
            // translated under exactly that assumption -- so the refusal was inconsistent
            // with the arm three lines below it. *Four routines of the corpus paid for a
            // sentence that was never checked.*
            //
            // The operator is chosen by the field's declared SHAPE, not guessed: `&=` on a
            // BOOL field is a truth value and on an INTEGER field a bit mask, and the two
            // compute different things.
            //
            // **The integer arms were missing while the comment claimed they were refused
            // "for the division reason".** They were not -- they fell out as
            // `compound-assignment`, a reason that names something else entirely. *A
            // refusal filed under the wrong reason names a missing form where a missing
            // translation stands*, the same lesson the `FieldShape` split books. Now that
            // the model has the masks, the arms say what the comment always said.
            let mischung = |op: ZuwOp, shape: Shape| -> Option<&'static str> {
                match (op, shape) {
                    (ZuwOp::Plus, Shape::Int) => Some("add"),
                    (ZuwOp::Minus, Shape::Int) => Some("sub"),
                    (ZuwOp::Und, Shape::Bool) => Some("and"),
                    (ZuwOp::Oder, Shape::Bool) => Some("or"),
                    (ZuwOp::Und, Shape::Int) => Some("band"),
                    (ZuwOp::Oder, Shape::Int) => Some("bor"),
                    _ => None,
                }
            };
            let w = expr_term(&z.wert, c)?;
            if z.ziel.suffixe.is_empty() {
                // **`n = e;` at a LOCAL rebinds the name; it does not store into the world.**
                //
                // Until 2026-08-28 this arm wrote `.assignGlobal` for every suffix-less
                // target, local or not -- and that is not a refusal but a WRONG PROGRAM.
                // Measured at `messung/abi-proben/zaehlwerk.gab :: hole_stand`, whose datum
                // read: bind `s` to 0, store to a world place called "s" that nothing
                // declares, return the LOCAL `s`. *The datum said the routine always returns
                // zero, and it returns the slot's value.*
                //
                // The export is what a hand-written Lean specification is held against
                // (`programmlogik/beispiel/`), so a person could have proved a true theorem
                // about a program nobody wrote. **`place_term` has always made this
                // distinction when READING a name** -- only the write side did not, which is
                // why nothing was refused and nothing looked wrong.
                //
                // Same class as the `traverse` variable that once fell through to
                // `.global "opfer"`, and the reason that comment stands three arms below.
                let ist_lokal = c.locals.iter().any(|l| *l == z.ziel.basis.text);
                let ziel = quoted(&z.ziel.basis.text);
                if z.op == ZuwOp::Setzt {
                    return Ok(if ist_lokal {
                        format!("(.bindName {ziel} {w})")
                    } else {
                        format!("(.assignGlobal {ziel} {w})")
                    });
                }
                // A `static` target carries no shape here, so a compound form has no
                // operator to choose -- refused rather than guessed.
                if !ist_lokal {
                    return Err(LeanReason::CompoundAssign);
                }
                // **At a LOCAL, `+=` and `-=` name their operation and nothing is guessed.**
                //
                // The ambiguity this arm was refusing lives in `&=` and `|=`: on a truth
                // value they are conjunction and disjunction, on an integer they are bit
                // masks, and without a declared shape there is no way to choose. `+=` has no
                // second reading.
                //
                // **And the model is safe by construction where a shape would have been
                // guessed**: `binop .add` is `none` on anything but two integers, so a body
                // that somehow added to a non-number gets STUCK rather than computing
                // something the machine does not. *That is why reading the OPERATOR here is
                // not the quiet weakening gate 1 stands against -- there is no premise being
                // made easier, only a form being translated.*
                let op = match z.op {
                    ZuwOp::Plus => "add",
                    ZuwOp::Minus => "sub",
                    _ => return Err(LeanReason::CompoundAssign),
                };
                return Ok(format!("(.bindName {ziel} (.bin .{op} (.name {ziel}) {w}))"));
            }
            if let [OrtSuffix::Feld(f)] = &z.ziel.suffixe[..] {
                let (base, shape) = record_field(&z.ziel.basis.text, &f.text, c)?;
                c.note_record(&base, &f.text, shape);
                if z.op != ZuwOp::Setzt {
                    let Some(op) = mischung(z.op, shape) else {
                        return Err(LeanReason::CompoundAssign);
                    };
                    return Ok(format!(
                        "(.assignField {} {} (.bin .{op} (.fieldOf {} {}) {}))",
                        quoted(&base),
                        quoted(&f.text),
                        quoted(&base),
                        quoted(&f.text),
                        w
                    ));
                }
                return Ok(format!(
                    "(.assignField {} {} {})",
                    quoted(&base),
                    quoted(&f.text),
                    w
                ));
            }
            let [OrtSuffix::Feld(slots), OrtSuffix::Index(i), OrtSuffix::Feld(f)] =
                &z.ziel.suffixe[..]
            else {
                return Err(LeanReason::Carrier);
            };
            if slots.text != "slots" {
                return Err(LeanReason::Carrier);
            }
            let (base, shape, tab) = field_shape(&z.ziel.basis.text, &f.text, c)?;
            let idx = expr_term(i, c)?;
            let w = if z.op == ZuwOp::Setzt {
                w
            } else {
                let Some(op) = mischung(z.op, shape) else {
                    return Err(LeanReason::CompoundAssign);
                };
                format!(
                    "(.bin .{op} (.place {} {} {}) {})",
                    quoted(&base),
                    idx,
                    quoted(&f.text),
                    w
                )
            };
            c.note(&base, &f.text, shape, &format!("`{}` in `{}`", f.text, tab));
            Ok(format!(
                "(.assign {} {} {} {})",
                quoted(&base),
                idx,
                quoted(&f.text),
                w
            ))
        }
        StmtArt::Wenn(w) => {
            // An `else if` chain folds from the back: one conditional statement per branch.
            let mut otherwise = match &w.sonst {
                Some(b) => block_term(b, c)?,
                None => "[]".to_string(),
            };
            for (bed, blk) in w.zweige.iter().rev() {
                let b = expr_term(bed, c)?;
                let d = block_term(blk, c)?;
                otherwise = format!("[(.ite {b} {d} {otherwise})]");
            }
            // The fold produced a one-element list; a statement is wanted, so unwrap it.
            Ok(otherwise
                .strip_prefix('[')
                .and_then(|s| s.strip_suffix(']'))
                .unwrap_or(&otherwise)
                .to_string())
        }
        StmtArt::Match(m) => {
            // **Exactly the option shape, and nothing else.** A `match` over a declared sum
            // type would need a value constructor per variant; refusing here is a number,
            // guessing would be a meaning.
            let g = expr_term(&m.gegenstand, c)?;
            let mut onp = None;
            let mut ona = None;
            for z in &m.zweige {
                match (z.variante.text.as_str(), &z.binder) {
                    ("Some", Some(b)) => {
                        let depth = c.locals.len();
                        c.locals.push(b.text.clone());
                        let blk = block_term(&z.rumpf, c)?;
                        c.locals.truncate(depth);
                        onp = Some((b.text.clone(), blk));
                    }
                    ("None", None) => ona = Some(block_term(&z.rumpf, c)?),
                    _ => return Err(LeanReason::MatchNotOption),
                }
            }
            match (onp, ona) {
                (Some((b, present)), Some(absent)) => {
                    Ok(format!("(.onOption {g} {} {present} {absent})", quoted(&b)))
                }
                _ => Err(LeanReason::MatchNotOption),
            }
        }
        StmtArt::Return(None) => Ok("(.ret none)".into()),
        StmtArt::Return(Some(e)) => {
            // **`return Some(i);` is a VALUE and not a call**, and the test comes first --
            // see `is_option_value`.
            if let ExprArt::Ruf(r) = &e.art {
                if !is_option_value(r) {
                    let (n, ps, args) = call_parts(r, c)?;
                    return Ok(format!("(.retCall {n} [{ps}] [{args}])"));
                }
            }
            Ok(format!("(.ret (some {}))", expr_term(e, c)?))
        }
        // Everything else is refused BY NAME. `Ruf` and `LetSonst` belong to the sequential
        // core and are the next two to build: a call is compositional over the CONTRACT of
        // the callee, never over its body, and that gate is not built.
        StmtArt::Ruf(r) => {
            let (n, ps, args) = call_parts(r, c)?;
            Ok(format!("(.call {n} [{ps}] [{args}])"))
        }
        StmtArt::LetSonst(_) => Err(LeanReason::ErrorPropagation),
        StmtArt::Schleife(sch) => {
            let (inv, rumpf) = match sch.as_ref() {
                Schleife::Traverse(x) => (&x.invariante, &x.rumpf),
                Schleife::Retry(x) => (&x.invariante, &x.rumpf),
                Schleife::Forever(x) => (&x.invariante, &x.rumpf),
            };
            // **A loop without an `invariant` is refused, and that is the whole point of the
            // word.** The measure is carried by the language; what is missing without the
            // clause is the STATEMENT, and a loop datum with no statement about it would let
            // a proof conclude from a loop exactly nothing while looking like it concluded
            // something.
            let Some(inv) = inv else {
                return Err(LeanReason::Loop);
            };
            let p = pred_term(inv, c)?;
            c.loops += 1;
            let id = format!("{}#{}", c.routine, c.loops);
            // **A `traverse` BINDS its variable, and the body reads it as a local.**
            //
            // Without this it fell through to `.global "opfer"` -- a bound name read as a
            // world name. *That is not a refusal but a wrong translation:* the datum would
            // say the body reads a global nobody declared, and a proof over it would be
            // about a program that does not exist. Found by reading the first emitted loop.
            let depth = c.locals.len();
            if let Schleife::Traverse(x) = sch.as_ref() {
                c.locals.push(x.variable.text.clone());
            }
            let body = block_term(rumpf, c)?;
            c.locals.truncate(depth);
            Ok(format!("(.loop {} {p} {body})", quoted(&id)))
        }
        StmtArt::Narrow(_) => Err(LeanReason::Narrowing),
        // **`breaking I { … }` is a SUSPENSION and not an exit**, and it stood in one arm
        // with `leave` and `next` under the sentence "a non-local exit out of a named loop".
        // It is neither: what it changes is which DUTY holds inside the block, not which
        // statements run -- so its meaning is its body's, exactly as at a `locks`.
        //
        // *Measured on 2026-08-28: all four obligations behind `non-local-exit` were
        // `breaking`, and not one was an exit* (`messung/AUSSETZUNG.md`). The
        // reading holds exactly as far as this channel cannot state a table invariant --
        // and it cannot; the `maintains` duty stands beside it and is refused by name.
        //
        // **The suspended names travel into the datum.** That is the half a later invariant
        // channel has to read: a record that dropped them would hide where the suspension
        // lay, the same reason the lock's name stays.
        StmtArt::Bricht(b) => {
            let namen: Vec<String> = b.invarianten.iter().map(|i| quoted(&i.text)).collect();
            Ok(format!(
                "(.breaking [{}] {})",
                namen.join(", "),
                block_term(&b.rumpf, c)?
            ))
        }
        StmtArt::Leave(_) | StmtArt::Next(_) => Err(LeanReason::NonLocalExit),
        // **The pairing costs no memory model either, and the ground is the same as at a
        // lock**: `release_stellt_sichtbarkeit_her` is an ASSUMPTION of the axiom layer
        // (`beispiele/06-annahmen.gab`, `unfalsifiable` with its reason written out, rebooked
        // there by `K100.2`) -- not a proof obligation. In a single world the visibility is
        // automatic; the assumption is what licenses reading it that way.
        //
        // The payload travels into the datum: it is the surface that rests on the assumption
        // rather than on the transition, and a record that dropped it would hide which places
        // those are.
        StmtArt::Publish(pb) => {
            if !pb.ziel.suffixe.is_empty() {
                return Err(LeanReason::Publish);
            }
            let w = expr_term(&pb.wert, c)?;
            Ok(format!(
                "(.publish {} {w} [{}])",
                quoted(&pb.ziel.basis.text),
                nutzlast(&pb.nutzlast)
            ))
        }
        StmtArt::AwaitLoad(a) => {
            if !a.quelle.suffixe.is_empty() {
                return Err(LeanReason::Await);
            }
            let payload: Vec<String> = a.erwartet.iter().map(|o| quoted(&o.text())).collect();
            c.locals.push(a.name.text.clone());
            Ok(format!(
                "(.awaitLoad {} {} [{}])",
                quoted(&a.name.text),
                quoted(&a.quelle.basis.text),
                payload.join(", ")
            ))
        }
        // **`exchange` stays refused, and the reason is the FORM and not the visibility.**
        // Both of its shapes are conditional: `update` carries a whole body (a CAS loop) and
        // `compare` stores only if a predicate holds. *A plain swap would store something the
        // program does not* -- the same class as taking `&=` for a truth value.
        StmtArt::Exchange(_) => Err(LeanReason::Exchange),
        StmtArt::Observiert(_) => Err(LeanReason::Observe),
        // **`locks S { … }` -- the one concurrent statement that costs no memory model.**
        // The plumbing already carries what it says: `Held(S)` inside is what makes the
        // sequential reading of this whole model sound, and H005/H006/H012/H016 discharge
        // it. The name travels into the datum so the critical section stays visible.
        StmtArt::Sperrt(l) => Ok(format!(
            "(.locked {} {})",
            quoted(&l.sperre.basis.text),
            block_term(&l.rumpf, c)?
        )),
    }
}

/// **Every table of the unit, with the shape its declaration gives each slot field.**
///
/// A field whose type has no shape is kept with `None` and NOT dropped -- a dropped field
/// looks like an undeclared one, and the refusal would then name the wrong thing.
fn tables(
    baum: &Programm,
    u: &crate::umgebung::Umgebung,
) -> HashMap<String, Vec<(String, Option<Shape>)>> {
    let mut out = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, module| {
        let ItemArt::Tabelle(tb) = &item.art else { return };
        let mut fields = Vec::new();
        if let Some(s) = &tb.slot {
            for f in &s.felder {
                let form = match &f.typ {
                    SlotTyp::Typ(te) => shape_of(te, u, module),
                    SlotTyp::Wrapping(_) => None,
                };
                fields.push((f.name.text.clone(), form));
            }
        }
        out.insert(tb.name.text.clone(), fields);
    });
    out
}

/// **Which base name stands for which table**, for one function.
fn carriers_of(
    f: &FnDecl,
    tab: &HashMap<String, Vec<(String, Option<Shape>)>>,
    statics: &HashMap<String, String>,
) -> HashMap<String, String> {
    let mut out = HashMap::new();
    // A table name stands for itself.
    for name in tab.keys() {
        out.insert(name.clone(), name.clone());
    }
    // A `static` that points at a table stands for it, in every function.
    for (n, table) in statics {
        out.insert(n.clone(), table.clone());
    }
    // A parameter stands for the table its pointer type names.
    for p in &f.parameter {
        if let Some(table) = points_at(&p.typ, tab) {
            out.insert(p.name.text.clone(), table);
        }
    }
    out
}

/// Does this declared type point at one of these declarations? **Through a pointer or
/// directly.** Used for tables and for records alike -- the lookup is the same, the map is
/// not.
fn points_at(
    typ: &TypExpr,
    decls: &HashMap<String, Vec<(String, Option<Shape>)>>,
) -> Option<String> {
    let target = match typ {
        TypExpr::Zeiger(z) => &z.ziel,
        t => t,
    };
    let TypExpr::Pfad(pf) = target else { return None };
    let last = pf.teile.last()?;
    decls.contains_key(&last.text).then(|| last.text.clone())
}

/// **Every record and `format` of the unit, with the shape its declaration gives each
/// field.** Two declarations carry fields without being a table: `format T { … }` and
/// `type T = { … }`.
fn records(
    baum: &Programm,
    u: &crate::umgebung::Umgebung,
) -> HashMap<String, Vec<(String, Option<Shape>)>> {
    let mut out = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, module| {
        match &item.art {
            ItemArt::Format(fo) => {
                let fields = fo
                    .felder
                    .iter()
                    // **A `reserved` field is not readable**, so it gets no shape and any
                    // place naming it is refused rather than given one.
                    .map(|f| {
                        (
                            f.name.text.clone(),
                            if f.reserviert { None } else { shape_of(&f.typ.typ, u, module) },
                        )
                    })
                    .collect();
                out.insert(fo.name.text.clone(), fields);
            }
            ItemArt::Typ(td) => {
                if let Some(TypExpr::Verbund(fs, _)) = &td.rumpf {
                    // An `opaque` new type's representation may not be read (`D1`), and a
                    // record behind one is exactly that.
                    if td.opaque {
                        return;
                    }
                    let fields = fs
                        .iter()
                        .map(|f| (f.name.text.clone(), shape_of(&f.typ.typ, u, module)))
                        .collect();
                    out.insert(td.name.text.clone(), fields);
                }
            }
            _ => {}
        }
    });
    out
}

/// Which base name stands for which record: parameters and statics whose type points at one.
fn record_carriers(
    f: &FnDecl,
    recs: &HashMap<String, Vec<(String, Option<Shape>)>>,
    statics: &HashMap<String, String>,
) -> HashMap<String, String> {
    let mut out = HashMap::new();
    for (n, r) in statics {
        out.insert(n.clone(), r.clone());
    }
    for p in &f.parameter {
        if let Some(r) = points_at(&p.typ, recs) {
            out.insert(p.name.text.clone(), r);
        }
    }
    out
}

/// **Every routine of the program with its parameter NAMES.** A call binds them, so the
/// datum of a call cannot be written without them.
fn callee_params(baum: &Programm) -> HashMap<String, Vec<String>> {
    let mut out = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _| {
        if let ItemArt::Funktion(f) = &item.art {
            out.insert(
                f.name.text.clone(),
                f.parameter.iter().map(|p| p.name.text.clone()).collect(),
            );
        }
    });
    out
}

/// **Every `static` that points at a table.** Read once per program, not per function.
///
/// *Measured, and the refusal had been naming the wrong thing:* `beispiele/38` writes
/// `tz.slots[i].a` where `tz` is a `static ptr<normal, rw> Platz`. `carriers_of` looked only
/// at parameters, so the place was refused as `carrier-not-a-table` -- and `Platz` is
/// declared four lines above. **A static is not a parameter, and it is a carrier all the
/// same.**
fn static_carriers(
    baum: &Programm,
    tab: &HashMap<String, Vec<(String, Option<Shape>)>>,
) -> HashMap<String, String> {
    let mut out = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _| {
        let ItemArt::Statisch(st) = &item.art else { return };
        if let Some(table) = points_at(&st.typ, tab) {
            out.insert(st.name.text.clone(), table);
        }
    });
    out
}

/// **The one function this module exists for**: a body obligation as a Lean goal, or a
/// named refusal.
fn judge(
    f: &FnDecl,
    post: &Pred,
    u: &crate::umgebung::Umgebung,
    module: &str,
    tab: &HashMap<String, Vec<(String, Option<Shape>)>>,
    recs: &HashMap<String, Vec<(String, Option<Shape>)>>,
    statics: &HashMap<String, String>,
    callees: &HashMap<String, Vec<String>>,
    foreign: &HashMap<String, LeanReason>,
    number: usize,
) -> LeanVerdict {
    let FnRumpf::Block(b) = &f.rumpf else {
        return LeanVerdict::Refused(LeanReason::ForeignBody);
    };
    let mut c = Ctx {
        tables: tab,
        records: recs,
        record_carrier: record_carriers(f, recs, &HashMap::new()),
        carrier: carriers_of(f, tab, statics),
        // **The obligation channel writes a GOAL, so it may not translate a call**: without
        // the callee's contract as a hypothesis the goal states something no proof closes.
        //
        // *And the gate is `allow_calls` ALONE.* It used to be doubled by an empty callee
        // table, and a mutation that removed the flag then changed nothing -- two guards
        // saying one thing, so neither carried. The real table travels here now; the flag is
        // the only thing that refuses.
        allow_calls: false,
        // **The body is translated first, and there `result` names nothing.**
        result_site: ResultSite::Body,
        uses_result: false,
        callees,
        foreign,
        locals: f.parameter.iter().map(|p| p.name.text.clone()).collect(),
        seen: Vec::new(),
        seen_records: Vec::new(),
        option_reads: Vec::new(),
        routine: f.name.text.clone(),
        loops: 0,
    };
    let body = match block_term(b, &mut c) {
        Ok(t) => t,
        Err(r) => return LeanVerdict::Refused(r),
    };
    // **The site changes here and nowhere earlier.** The body is translated above; a
    // `result` inside one is refused as `result-in-body`, because there it names nothing.
    // What follows is the postcondition, and the goal binds `result` over it.
    c.result_site = ResultSite::Bound;
    let conclusion = match pred_term(post, &mut c) {
        Ok(t) => t,
        Err(r) => return LeanVerdict::Refused(r),
    };
    // **The hypotheses, and every one of them read from a declaration.**
    let mut hypotheses = Vec::new();
    let mut opening = Vec::new();
    let mut splits: Vec<String> = Vec::new();
    let mut equations = Vec::new();
    for p in &f.parameter {
        if let Some(form) = shape_of(&p.typ, u, module) {
            let n = &p.name.text;
            hypotheses.push((
                format!("p_{n}"),
                format!("{} (s.local' {})", form.predicate(), quoted(n)),
                format!("the declared type of `{n}`"),
            ));
            // `istWahl` is a DISJUNCTION, not an existential -- there is no single witness
            // to name, so it stays whole and the goal that needs it is refused rather than
            // half-opened.
            if form != Shape::Opt {
                opening.push(format!("  obtain \\<langle>w_{n}, e_{n}\\<rangle> := p_{n}"));
                equations.push(format!("e_{n}"));
            }
        }
    }
    for (carrier, feld, form, origin) in &c.seen {
        hypotheses.push((
            format!("f_{carrier}_{feld}"),
            format!(
                "\\<forall> k, {} (s.world (.slot {} k {}))",
                form.predicate(),
                quoted(carrier),
                quoted(feld)
            ),
            origin.clone(),
        ));
    }
    // **The case split, one per option-shaped field read at a parameter index.**
    //
    // The split is emitted only where the WITNESS exists -- a parameter whose declared type
    // gave a shape and was therefore opened above. Without the witness there is no `w_p` to
    // apply the hypothesis to, and a split written anyway would not elaborate.
    for (carrier, field, index) in &c.option_reads {
        if !equations.iter().any(|g| *g == format!("e_{index}")) {
            continue;
        }
        let h = format!("h_{carrier}_{field}_{index}");
        splits.push(format!(
            "rcases f_{carrier}_{field} w_{index} with {h} | \\<langle>m_{carrier}_{field}_{index}, {h}\\<rangle>"
        ));
        equations.push(h);
    }
    LeanVerdict::Proved(Box::new(LeanGoal {
        name: format!("duty_{number}"),
        body,
        hypotheses,
        conclusion,
        names_result: c.uses_result,
        opening,
        equations,
        splits,
    }))
}

/// **The whole register, judged for the Lean channel.** One entry per obligation of
/// `pflichten::sammle`, in the same order -- so the two channels can be held against each
/// other, obligation by obligation.
pub fn verdicts(baum: &Programm) -> Vec<(crate::pflichten::Pflicht, LeanVerdict)> {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let tab = tables(baum, &u);
    let recs = records(baum, &u);
    let statics = static_carriers(baum, &tab);
    let callees = callee_params(baum);
    let foreign = foreign_calls(baum);
    // The module a function is declared in travels with it: `typ_von_ausdruck_decl` is
    // module-aware, and asking it from the wrong module answers about the wrong type.
    let mut fns: HashMap<String, (String, FnDecl)> = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, module| {
        if let ItemArt::Funktion(f) = &item.art {
            fns.insert(f.name.text.clone(), (module.to_string(), f.clone()));
        }
    });

    crate::pflichten::sammle(baum)
        .into_iter()
        .enumerate()
        .map(|(i, p)| {
            let n = i + 1;
            let v = match p.art {
                crate::pflichten::Art::Vorbedingung => LeanVerdict::Refused(LeanReason::CallSite),
                crate::pflichten::Art::Geraetezusage => {
                    LeanVerdict::Refused(LeanReason::DevicePromise)
                }
                crate::pflichten::Art::Fremdpflicht => {
                    LeanVerdict::Refused(LeanReason::ForeignBody)
                }
                crate::pflichten::Art::Erhaltung => LeanVerdict::Refused(LeanReason::Invariant),
                // **The obligation channel writes a GOAL over a whole body**, and a loop's
                // goal is the loop RULE -- the body preserves the invariant. That is a
                // theorem over the loop's own body and not over the routine's, so it does
                // not fit the shape this channel emits. Refused by name; the export carries
                // the datum a person needs to state it.
                crate::pflichten::Art::Schleifeninvariante => {
                    LeanVerdict::Refused(LeanReason::Loop)
                }
                // **The `walk` invariant, and it is refused for the SAME reason as the
                // table one** -- a quantifier over a domain this channel cannot express.
                // What is new is that it now HAS a number; until 2026-08-31 it stood in a
                // C comment and in no register.
                crate::pflichten::Art::Walkinvariante => {
                    LeanVerdict::Refused(LeanReason::WalkInvariant)
                }
                crate::pflichten::Art::Nachbedingung => match fns.get(&p.funktion) {
                    Some((module, f)) => {
                        // `ensures #k` -- the index is in the register's own wording.
                        let k = p
                            .gegenstand
                            .rsplit('#')
                            .next()
                            .and_then(|s| s.parse::<usize>().ok())
                            .unwrap_or(0);
                        match f.ensures.get(k.wrapping_sub(1)) {
                            Some(q) => judge(f, q, &u, module, &tab, &recs, &statics, &callees, &foreign, n),
                            None => LeanVerdict::Refused(LeanReason::Expression),
                        }
                    }
                    None => LeanVerdict::Refused(LeanReason::Expression),
                },
                crate::pflichten::Art::Verfeinerung => match fns.get(&p.funktion) {
                    Some((module, f)) => match specification(f, &fns) {
                        Ok(q) => judge(f, &q, &u, module, &tab, &recs, &statics, &callees, &foreign, n),
                        Err(r) => LeanVerdict::Refused(r),
                    },
                    None => LeanVerdict::Refused(LeanReason::SpecShape),
                },
            };
            (p, v)
        })
        .collect()
}

/// **`refines g` -- the head form.** The obligation is *what this body establishes is what
/// `g` describes*, so the postcondition IS the `spec fn`'s expression body, with its own
/// parameter names replaced by the implementation's. `M132` has already checked that both
/// carry the same number of parameters.
fn specification(
    f: &FnDecl,
    fns: &HashMap<String, (String, FnDecl)>,
) -> Result<Pred, LeanReason> {
    let path = f.verfeinert.as_ref().ok_or(LeanReason::SpecShape)?;
    let name = path.teile.last().ok_or(LeanReason::SpecShape)?;
    let (_, spec) = fns.get(&name.text).ok_or(LeanReason::SpecShape)?;
    let FnRumpf::Pred(p) = &spec.rumpf else {
        return Err(LeanReason::SpecShape);
    };
    let pairs: Vec<(String, String)> = spec
        .parameter
        .iter()
        .zip(f.parameter.iter())
        .map(|(s, i)| (s.name.text.clone(), i.name.text.clone()))
        .collect();
    Ok(renamed_pred(p, &pairs))
}

fn renamed_pred(p: &Pred, pairs: &[(String, String)]) -> Pred {
    let art = match &p.art {
        PredArt::Vergleich(e) => PredArt::Vergleich(renamed_expr(e, pairs)),
        PredArt::Klammer(q) => PredArt::Klammer(Box::new(renamed_pred(q, pairs))),
        PredArt::Nicht(q) => PredArt::Nicht(Box::new(renamed_pred(q, pairs))),
        PredArt::Und(a, b) => PredArt::Und(
            Box::new(renamed_pred(a, pairs)),
            Box::new(renamed_pred(b, pairs)),
        ),
        PredArt::Oder(a, b) => PredArt::Oder(
            Box::new(renamed_pred(a, pairs)),
            Box::new(renamed_pred(b, pairs)),
        ),
        PredArt::Folgt(a, b) => PredArt::Folgt(
            Box::new(renamed_pred(a, pairs)),
            Box::new(renamed_pred(b, pairs)),
        ),
        other => other.clone(),
    };
    Pred { art, ..p.clone() }
}

fn renamed_expr(e: &Expr, pairs: &[(String, String)]) -> Expr {
    let art = match &e.art {
        ExprArt::Ort(o) => {
            let mut o = o.clone();
            if let Some((_, fresh)) = pairs.iter().find(|(old, _)| *old == o.basis.text) {
                o.basis.text = fresh.clone();
            }
            for s in &mut o.suffixe {
                if let OrtSuffix::Index(i) = s {
                    *i = renamed_expr(i, pairs);
                }
            }
            ExprArt::Ort(o)
        }
        ExprArt::Klammer(x) => ExprArt::Klammer(Box::new(renamed_expr(x, pairs))),
        ExprArt::Unaer(op, x) => ExprArt::Unaer(*op, Box::new(renamed_expr(x, pairs))),
        ExprArt::Binaer(op, a, b) => ExprArt::Binaer(
            *op,
            Box::new(renamed_expr(a, pairs)),
            Box::new(renamed_expr(b, pairs)),
        ),
        other => other.clone(),
    };
    Expr { art, ..e.clone() }
}

/// **The module name of a unit.** Lean demands that it match the file, so the stem is what
/// this derives from.
pub fn module_name(datei: &str) -> String {
    let stem = datei
        .rsplit('/')
        .next()
        .unwrap_or(datei)
        .trim_end_matches(".gab");
    let mut s = String::from("Duty");
    let mut gross = true;
    for ch in stem.chars() {
        if ch.is_ascii_alphanumeric() {
            s.push(if gross { ch.to_ascii_uppercase() } else { ch });
            gross = false;
        } else {
            gross = true;
        }
    }
    s
}

/// **The unit's obligation register, as a Lean 4 module.**
pub fn module(baum: &Programm, datei: &str) -> String {
    let entries = verdicts(baum);
    let proved = entries
        .iter()
        .filter(|(_, v)| matches!(v, LeanVerdict::Proved(_)))
        .count();
    let refused = entries.len() - proved;
    let name = module_name(datei);
    let mut s = String::new();
    s.push_str("/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the\n");
    s.push_str("    `.gab`, and a second register over the same thing is the very class this\n");
    s.push_str("    folder is written against.\n\n");
    s.push_str("    Every obligation of the register appears below, as a theorem or as a\n");
    s.push_str("    NAMED refusal. The line that has to add up:\n\n");
    s.push_str(&format!(
        "        @duty 1  {datei}  total {}  goals {proved}  refused {refused}\n",
        entries.len()
    ));
    s.push_str("\n    The meaning of a body is `Gabbro.Body`, written by hand and read by a\n");
    s.push_str("    person. What stands here is a DATUM of it -- this file defines nothing.\n\n");
    s.push_str("    ASSUMED, and visible because it is written down: two different carrier\n");
    s.push_str("    names are two different objects. That is the alias statement, and the\n");
    s.push_str("    alias passes carry it -- no line of this file does.\n-/\n\n");
    s.push_str("import Gabbro.Body\n\n");
    // **`autoImplicit` off, and it is a GUARD, not tidiness.** With it on, a name Lean does
    // not know becomes an implicitly bound variable of unknown type -- measured on the very
    // first run of this emitter: a hypothesis `istZahl (l.locals "p")` whose predicate was
    // not in scope elaborated to a BINDER instead of failing. *A misspelt hypothesis that
    // silently turns into an unconstrained variable is a theorem about nothing, and it
    // reads exactly like a proved one.*
    s.push_str("set_option autoImplicit false\n\nopen Gabbro.Body\n\n");
    s.push_str(&format!("namespace GabbroDuty.{name}\n\n"));

    s.push_str("/-! ## What is NOT here, and why -/\n\n");
    if refused == 0 {
        s.push_str("-- Nothing was refused in this unit.\n\n");
    } else {
        s.push_str("/-\n  These obligations of the register carry no theorem. A duty that\n");
        s.push_str("  vanishes is noticed; one that gets weaker is not -- so each stands\n");
        s.push_str("  here with its reason.\n\n");
        for r in LeanReason::ALL {
            let mine: Vec<(usize, &crate::pflichten::Pflicht)> = entries
                .iter()
                .enumerate()
                .filter(|(_, (_, v))| matches!(v, LeanVerdict::Refused(x) if *x == r))
                .map(|(i, (p, _))| (i, p))
                .collect();
            if mine.is_empty() {
                continue;
            }
            s.push_str(&format!("  {} ({}): {}\n", r.tag(), mine.len(), r.sentence()));
            for (i, p) in mine {
                s.push_str(&format!(
                    "    duty_{}  {}  {} :: {}\n",
                    i + 1,
                    p.art.marke(),
                    p.funktion,
                    p.gegenstand
                ));
            }
            s.push('\n');
        }
        s.push_str("-/\n\n");
    }

    if proved > 0 {
        s.push_str("/-! ## The obligations that stand closed -/\n\n");
    }
    for (p, v) in entries.iter() {
        let LeanVerdict::Proved(g) = v else { continue };
        s.push_str(&format!(
            "/-- {} -- `{}` :: `{}` -/\n",
            p.art.name(),
            p.funktion,
            p.gegenstand
        ));
        s.push_str(&format!("def body_{} : List Stmt :=\n  {}\n\n", g.name, g.body));
        s.push_str(&format!("def post_{} : Expr :=\n  {}\n\n", g.name, g.conclusion));
        s.push_str(&format!("theorem {} (\\<rho> : Env) (s : State)\n", g.name));
        for (label, term, origin) in &g.hypotheses {
            s.push_str(&format!("    -- {origin}\n"));
            s.push_str(&format!("    ({label} : {term})\n"));
        }
        if g.names_result {
            // **The goal over a postcondition that names `result` demands THREE things**, and
            // the middle one is the new half: the body ends, it PRODUCED a value, and the
            // promise holds with that value bound. *A body that runs off the end has no
            // result, and `finalValue` is `none` there* -- so this form is strictly stronger
            // than the two-part one, which is the direction a goal may move.
            s.push_str(&format!(
                "    : \\<exists> s' v, finalState (exec \\<rho> body_{} s) = some s'\n",
                g.name
            ));
            s.push_str(&format!(
                "        \\<and> finalValue (exec \\<rho> body_{} s) = some v\n",
                g.name
            ));
            // `result` is bound as a LOCAL, exactly as a parameter is read -- see
            // `expr_term`. The model needed no arm for it.
            s.push_str(&format!(
                "        \\<and> eval {{ s' with local' := bindLocal s'.local' \"result\" v }} \
                 post_{} = some (.bool true) := by\n",
                g.name
            ));
        } else {
            s.push_str(&format!(
                "    : \\<exists> s', finalState (exec \\<rho> body_{} s) = some s'\n",
                g.name
            ));
            s.push_str(&format!(
                "        \\<and> eval s' post_{} = some (.bool true) := by\n",
                g.name
            ));
        }
        for z in &g.opening {
            s.push_str(z);
            s.push('\n');
        }
        let mut set = vec![
            format!("body_{}", g.name),
            format!("post_{}", g.name),
            "exec".into(),
            "step".into(),
            "eval".into(),
            "unop".into(),
            "binop".into(),
            "finalState".into(),
            "store".into(),
            "bindLocal".into(),
        ];
        // **`finalValue` joins the set only where the goal is about one.** Lean's linter
        // reports an unused simp argument, and a tactic that carries lemmas it never needs
        // teaches a reader the wrong thing about what the proof rests on.
        if g.names_result {
            set.push("finalValue".into());
        }
        set.extend(g.equations.iter().cloned());
        // **Every `rcases` splits the goal, so the whole chain is joined with `<;>`.** A
        // line standing on its own would serve only the first half -- and the other half,
        // in a file nobody builds, looks exactly like a proved one.
        let tactic = format!("simp [{}]", set.join(", "));
        if g.splits.is_empty() {
            s.push_str(&format!("  {tactic}\n\n"));
        } else {
            s.push_str(&format!("  {}\n", g.splits.join(" <;>\n    ")));
            s.push_str(&format!("    <;> {tactic}\n\n"));
        }
    }
    s.push_str(&format!("end GabbroDuty.{name}\n"));
    s.replace("\\<forall>", "∀")
        .replace("\\<exists>", "∃")
        .replace("\\<and>", "∧")
        .replace("\\<rho>", "ρ")
        .replace("\\<langle>", "⟨")
        .replace("\\<rangle>", "⟩")
}

// ===========================================================================================
// THE PROGRAM EXPORT -- a whole Gabbro program as a Lean 4 datum, so that a HAND-WRITTEN
// specification can be held against it.
//
// **This is a different artefact from `module` above, and the difference is the direction.**
// `gabbro pflichten --lean` takes the obligations Gabbro's own `spec fn`/`refines` pair
// states and writes them as theorems. This one takes NO specification at all: it writes the
// program -- bodies, contracts, the shape of every declared place -- and stops. *What is to
// be proved about it is then said in Lean, by a person, in a file this emitter never sees.*
//
// ## Why the specification is not in Gabbro
//
// A `spec fn` is a Gabbro expression, so it has Gabbro's expressiveness: no quantifier, no
// recursion, no induction. That is exactly the ceiling `maintains` runs into -- a table
// invariant is quantified over every slot, and this channel refuses all six of them. **A
// specification written in Lean has none of those limits.**
//
// And it costs no second register, which is the objection that would otherwise stand
// (`W7`): the program is stated once, here; the specification is stated once, in the user's
// file. *Nothing is said twice, and that is the whole difference from naming a Lean identifier
// inside the Gabbro source.*
//
// ## The one hazard, and it gets a guard
//
// A hand-written specification names places by STRING -- `.slot "Konten" k "offen"`. A typo
// there is a specification about a place that does not exist, and a theorem about a place
// that does not exist is vacuous rather than false. **Hence the export carries the place
// dictionary**, and `instrumente/pruefe-lean-programm.sh` holds every place a specification
// mentions against it.
// ===========================================================================================

/// One routine of the program, as a datum -- or a named refusal.
pub struct Routine {
    pub name: String,
    /// The body as a `Stmt` list term. `None` where the body is outside the fragment.
    pub body: Option<String>,
    pub refused: Option<LeanReason>,
    /// `(parameter, shape)` -- the shape is what the declaration gives, `None` where this
    /// channel has none.
    pub params: Vec<(String, Option<Shape>)>,
    /// The `requires` this channel can express, as `Expr` terms.
    pub pre: Vec<String>,
    /// The `requires` it cannot -- **dropped, not refused.**
    ///
    /// A precondition is a HYPOTHESIS. Dropping one can only make the theorem harder to
    /// prove, never wrong -- the same direction `refinement.rs` argues for its caller
    /// `requires`. *Refusing the whole routine over a `Held(L)` it cannot say would cost a
    /// body for a clause that carries nothing here.* They are listed by name.
    pub dropped: Vec<String>,
    /// The `ensures` this channel can express -- what a CALLER may assume.
    pub post: Vec<String>,
    /// The ones it cannot. **Not said, not refused**: a promise fewer makes a caller's
    /// goal harder, never wrong -- the same direction as a dropped precondition, mirrored.
    pub post_dropped: Vec<String>,
}

/// Every place the program declares, with the shape its declaration gives it.
fn dictionary(tab: &HashMap<String, Vec<(String, Option<Shape>)>>) -> Vec<(String, String, Shape)> {
    let mut out: Vec<(String, String, Shape)> = Vec::new();
    let mut names: Vec<&String> = tab.keys().collect();
    names.sort();
    for t in names {
        for (f, shape) in &tab[t] {
            if let Some(shape) = shape {
                out.push((t.clone(), f.clone(), *shape));
            }
        }
    }
    out
}

/// Every routine of the program, in declaration order.
pub fn routines(baum: &Programm) -> Vec<Routine> {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let tab = tables(baum, &u);
    let recs = records(baum, &u);
    let statics = static_carriers(baum, &tab);
    let callees = callee_params(baum);
    let foreign = foreign_calls(baum);
    let mut out = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, module| {
        let ItemArt::Funktion(f) = &item.art else { return };
        if f.klasse == Some(FnKlasse::Spec) {
            return;
        }
        let params: Vec<(String, Option<Shape>)> = f
            .parameter
            .iter()
            .map(|p| (p.name.text.clone(), shape_of(&p.typ, &u, module)))
            .collect();
        let FnRumpf::Block(b) = &f.rumpf else {
            out.push(Routine {
                name: f.name.text.clone(),
                body: None,
                refused: Some(LeanReason::ForeignBody),
                params,
                pre: Vec::new(),
                dropped: Vec::new(),
                post: Vec::new(),
                post_dropped: Vec::new(),
            });
            return;
        };
        let mut c = Ctx {
            tables: &tab,
            records: &recs,
            record_carrier: record_carriers(f, &recs, &HashMap::new()),
            carrier: carriers_of(f, &tab, &statics),
            // **The export writes a DATUM, so a call is honest here**: the callee is named,
            // never inlined, and what it does is looked up in an environment the reader's
            // theorem quantifies over.
            allow_calls: true,
            // **The export does NOT say `result`, and that is the conservative direction.**
            // Its `post` list is what a CALLER may assume, and a caller reads the callee's
            // result at its own call site -- not out of a name this datum binds. A promise
            // fewer makes a caller's goal harder, never wrong, and it is listed by name in
            // `post_dropped`. *The same direction as a dropped precondition, mirrored.*
            //
            // **It opens on `Body` and not on `Contract`**: `block_term` runs first here too,
            // and a `result` in a body is a program error in this channel just as much as in
            // the other one. The site moves to `Contract` below, where the clauses are read.
            result_site: ResultSite::Body,
            uses_result: false,
            callees: &callees,
            foreign: &foreign,
            locals: f.parameter.iter().map(|p| p.name.text.clone()).collect(),
            seen: Vec::new(),
            seen_records: Vec::new(),
            option_reads: Vec::new(),
            routine: f.name.text.clone(),
            loops: 0,
        };
        let body = block_term(b, &mut c);
        // **The body is done; what follows are the CLAUSES.** A `result` met from here on is
        // a promise this datum declines to repeat, not a body saying something it cannot mean
        // -- and the two are booked under different names.
        c.result_site = ResultSite::Contract;
        let mut pre = Vec::new();
        let mut dropped = Vec::new();
        for (i, q) in f.requires.iter().enumerate() {
            match pred_term(q, &mut c) {
                Ok(t) => pre.push(t),
                Err(r) => dropped.push(format!("requires #{} ({})", i + 1, r.tag())),
            }
        }
        // **The postcondition, so a CALLER has something to assume.** A call is taken over
        // the contract; without the contract written down there is no contract to take.
        let mut post = Vec::new();
        let mut post_dropped = Vec::new();
        for (i, q) in f.ensures.iter().enumerate() {
            match pred_term(q, &mut c) {
                Ok(t) => post.push(t),
                Err(r) => post_dropped.push(format!("ensures #{} ({})", i + 1, r.tag())),
            }
        }
        match body {
            Ok(t) => out.push(Routine {
                name: f.name.text.clone(),
                body: Some(t),
                refused: None,
                params,
                pre,
                dropped,
                post,
                post_dropped,
            }),
            Err(r) => out.push(Routine {
                name: f.name.text.clone(),
                body: None,
                refused: Some(r),
                params,
                pre,
                dropped,
                post,
                post_dropped,
            }),
        }
    });
    out
}

/// **The whole program, as a Lean 4 module.**
pub fn program(baum: &Programm, quellen: &[String]) -> String {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let tab = tables(baum, &u);
    let recs = records(baum, &u);
    let dict = dictionary(&tab);
    let rdict = dictionary(&recs);
    let rs = routines(baum);
    let carried = rs.iter().filter(|r| r.body.is_some()).count();
    let refused = rs.len() - carried;

    let mut s = String::new();
    s.push_str("/-  Written by `gabbro lean`. Do not edit -- the source is the `.gab` files,\n");
    s.push_str("    and a second register over the same thing is the very class this folder\n");
    s.push_str("    is written against.\n\n");
    s.push_str("    THIS FILE CARRIES NO SPECIFICATION. It carries the PROGRAM: every body\n");
    s.push_str("    this channel can express, every precondition it can say, and the shape of\n");
    s.push_str("    every declared place. What is to hold about it is said in Lean, by a\n");
    s.push_str("    person, in a file this emitter never sees.\n\n");
    s.push_str("    The line that has to add up:\n\n");
    s.push_str(&format!(
        "        @program 1  units {}  routines {}  bodies {carried}  refused {refused}  places {}\n",
        quellen.len(),
        rs.len(),
        dict.len() + rdict.len()
    ));
    s.push_str("\n    Sources:\n");
    for q in quellen {
        s.push_str(&format!("        {q}\n"));
    }
    s.push_str("\n    ASSUMED, and visible because it is written down: two different carrier\n");
    s.push_str("    names are two different objects. That is the alias statement, and the\n");
    s.push_str("    alias passes carry it -- no line of this file does.\n-/\n\n");
    s.push_str("import Gabbro.Body\n\n");
    s.push_str("set_option autoImplicit false\n\nopen Gabbro.Body\n\n");
    s.push_str("namespace GabbroProgram\n\n");

    // ---- the place dictionary -----------------------------------------------------------
    s.push_str("/-! ## The declared places\n\n");
    s.push_str("    **A specification names a place by STRING, and a typo in that string is a\n");
    s.push_str("    specification about a place that does not exist** -- vacuous rather than\n");
    s.push_str("    false, and vacuous reads like proved. This list is what a specification is\n");
    s.push_str("    held against; `instrumente/pruefe-lean-programm.sh` does the holding.\n-/\n\n");
    s.push_str("/-- `(carrier, field, shape)` for every declared slot field. -/\n");
    s.push_str("def places : List (String \\<times> String \\<times> String) :=\n");
    if dict.is_empty() {
        s.push_str("  []\n\n");
    } else {
        s.push_str("  [ ");
        let items: Vec<String> = dict
            .iter()
            .map(|(t, f, sh)| format!("({}, {}, {})", quoted(t), quoted(f), quoted(sh.predicate())))
            .collect();
        s.push_str(&items.join("\n  , "));
        s.push_str("\n  ]\n\n");
    }

    // ---- the well-formed state ----------------------------------------------------------
    s.push_str("/-- `(carrier, field, shape)` for every declared RECORD or `format` field. -/\n");
    s.push_str("def fields : List (String \\<times> String \\<times> String) :=\n");
    if rdict.is_empty() {
        s.push_str("  []\n\n");
    } else {
        s.push_str("  [ ");
        let items: Vec<String> = rdict
            .iter()
            .map(|(t, f, sh)| format!("({}, {}, {})", quoted(t), quoted(f), quoted(sh.predicate())))
            .collect();
        s.push_str(&items.join("\n  , "));
        s.push_str("\n  ]\n\n");
    }

    s.push_str("/-- **The well-formed state** -- that a slot field carries a value of its\n");
    s.push_str("    declared shape. It is a HYPOTHESIS and not a consequence (`Body.lean`, U2);\n");
    s.push_str("    it stands here once for the whole program instead of once per theorem. -/\n");
    s.push_str("def wellFormed (s : State) : Prop :=\n");
    let mut parts: Vec<String> = dict
        .iter()
        .map(|(t, f, sh)| {
            format!(
                "(\\<forall> k, {} (s.world (.slot {} k {})))",
                sh.predicate(),
                quoted(t),
                quoted(f)
            )
        })
        .collect();
    // A record field carries no index: one object, not a row of them.
    parts.extend(rdict.iter().map(|(t, f, sh)| {
        format!(
            "({} (s.world (.field {} {})))",
            sh.predicate(),
            quoted(t),
            quoted(f)
        )
    }));
    if parts.is_empty() {
        s.push_str("  True\n\n");
    } else {
        s.push_str(&format!("  {}\n\n", parts.join("\n  \\<and> ")));
    }

    // ---- the routines -------------------------------------------------------------------
    s.push_str("/-! ## The routines -/\n\n");
    for r in &rs {
        if let Some(reason) = r.refused {
            s.push_str(&format!(
                "-- REFUSED  {}  ({}): {}\n\n",
                r.name,
                reason.tag(),
                reason.sentence()
            ));
            continue;
        }
        let Some(body) = &r.body else { continue };
        s.push_str(&format!("/-- `{}` -- the body, statement by statement.", r.name));
        if !r.dropped.is_empty() {
            s.push_str(&format!(
                "\n\n    DROPPED from the precondition (a hypothesis fewer makes the goal harder,\n    never the proof wrong): {}",
                r.dropped.join(", ")
            ));
        }
        s.push_str(" -/\n");
        s.push_str(&format!("def {}_body : List Stmt :=\n  {}\n\n", r.name, body));
        s.push_str(&format!(
            "/-- `{}` -- what the caller grants: the declared parameter shapes and the\n    `requires` this channel can say. -/\n",
            r.name
        ));
        s.push_str(&format!("def {}_pre (s : State) : Prop :=\n", r.name));
        let mut parts: Vec<String> = r
            .params
            .iter()
            .filter_map(|(n, sh)| {
                sh.map(|sh| format!("{} (s.local' {})", sh.predicate(), quoted(n)))
            })
            .collect();
        for t in &r.pre {
            parts.push(format!("eval s {t} = some (.bool true)"));
        }
        if parts.is_empty() {
            s.push_str("  True\n\n");
        } else {
            s.push_str(&format!("  {}\n\n", parts.join("\n  \\<and> ")));
        }
        s.push_str(&format!(
            "/-- `{}` -- what it PROMISES: the `ensures` this channel can say. A caller takes\n    a call over this and never over the body.",
            r.name
        ));
        if !r.post_dropped.is_empty() {
            s.push_str(&format!(
                "\n\n    NOT SAID here (a promise fewer makes a caller's goal harder, never\n    wrong): {}",
                r.post_dropped.join(", ")
            ));
        }
        s.push_str(" -/\n");
        s.push_str(&format!("def {}_post (s : State) : Prop :=\n", r.name));
        if r.post.is_empty() {
            s.push_str("  True\n\n");
        } else {
            let ps: Vec<String> = r
                .post
                .iter()
                .map(|x| format!("eval s {x} = some (.bool true)"))
                .collect();
            s.push_str(&format!("  {}\n\n", ps.join("\n  \\<and> ")));
        }
    }

    s.push_str("/-! ## Proving something about this program\n\n");
    s.push_str("    A specification is a Lean predicate over `State`; the obligation is that a\n");
    s.push_str("    body establishes it. The tactic that unfolds the model is `gabbro_simp`,\n");
    s.push_str("    and it lives in `Gabbro.Body` -- not here, so that a change to the model\n");
    s.push_str("    reaches every proof through one place.\n\n");
    s.push_str("        theorem meets_spec (\\<rho> : Env) (s : State) (k : Int)\n");
    s.push_str("            (wf : wellFormed s) (hk : s.local\' \"k\" = .int k)\n");
    s.push_str("            : \\<exists> s\', finalState (exec \\<rho> f_body s) = some s\'\n");
    s.push_str("                \\<and> mySpec k s\' := by\n");
    s.push_str("          gabbro_simp [mySpec, hk]\n-/\n\n");
    s.push_str("end GabbroProgram\n");
    s.replace("\\<forall>", "∀")
        .replace("\\<exists>", "∃")
        .replace("\\<and>", "∧")
        .replace("\\<times>", "×")
        .replace("\\<rho>", "ρ")
}
