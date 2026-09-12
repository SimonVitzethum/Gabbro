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
//!
//! ## What changed on 2026-09-07, and why the register now closes
//!
//! Until that day the channel wrote a goal only over a body that CALLED nothing, LOOPED
//! nowhere and named no quantifier -- 14 of 175 obligations over the corpus. The rest was
//! refused by name, and every refusal named a piece of plumbing the person had to write in
//! Lean by hand: the composition over a callee's contract, the loop rule, the bounded
//! quantifier of a table invariant, the precondition at a call site. **None of that is the
//! person's logic**, and this module now writes all of it:
//!
//! * **A call is taken over the callee's CONTRACT** (`Body.lean` §4.1). The caller's theorem
//!   carries `Contract ρ g g_pre g_post` and `Frame ρ g g_writes` as hypotheses, read off
//!   the callee's `requires`/`ensures`/`effects`; the callee's own `requires` is the
//!   stuck-condition of the call, so the STRONG goal demands it -- that is the `V` duty,
//!   carried by the caller's theorem instead of by a goal of its own.
//! * **A loop is an anonymous routine with a rule.** Its body gets a theorem of its own --
//!   *from a well-formed state satisfying the invariant, one pass leaves one* -- and the
//!   routine's theorem carries `LoopRule` as a hypothesis. The shapes of the locals in scope
//!   travel inside the invariant, as `hasShape` conjuncts this file adds.
//! * **A table invariant is a bounded quantifier** (`Expr.forallSlots`, with the declared
//!   `count`), and `reaches` is the chain with the count as fuel. Both are expressions, so
//!   a callee may DEMAND them.
//! * **The wiring is generated.** `unit_closed` takes the duty statements and `Program ρ`
//!   (that the environment runs the bodies) and yields every contract and every loop rule
//!   of the unit, in dependency order -- `contract_of_duty` and `looprule_of_body` do the
//!   induction once, in the model.
//!
//! What a person still writes is the proof of each `_statement` -- and every hypothesis
//! such a proof can need stands in front of its turnstile. What stays ASSUMED is named in
//! `Assumed ρ`: the contracts of foreign bodies and the frames of device transitions --
//! the `F` and `D` duties of the register, which no body of Gabbro's can discharge.

use gabbro_syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// **Why an obligation carries no Lean goal.** Exhaustive, and each arm names a different
/// missing thing -- a single "not supported" would hide that they have different prices.
///
/// Since 2026-09-07 the arms fall into three kinds, and `kind` says which: an ASSUMPTION
/// (hardware, foreign code -- no body of Gabbro's can discharge it), a REFUSAL of a form
/// this channel has no term for, and a REFUSAL of a shape this channel's wiring cannot yet
/// close. The count line of every emitted file keeps the three apart.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LeanReason {
    /// An `ensures` at a body Gabbro never sees. **An assumption, not a goal** -- it stands
    /// in `Assumed ρ` as the callee's `Contract`, visibly, and every caller's wiring rests
    /// on it.
    ForeignBody,
    /// `maintains I` names an invariant this channel could not translate -- a domain other
    /// than `slots of`, or a form without a term. (A translatable one is carried by the
    /// routine's theorem since 2026-09-07.)
    Invariant,
    /// **`passes` where the loop cannot count** (agent b, 2026-09-08): the pass counter is
    /// readable in a `traverse` whose domain has a `count` -- the number that bounds how
    /// often the body runs. Where there is no such number the name would go out as a place
    /// of the world (`.global "passes"`), and that is the wrong-proof-object `D021` names.
    /// So it is refused, and the refusal carries its own tag.
    PassCounter,
    /// A precondition at a call site whose CALLER's body this channel could not translate;
    /// where it could, the `V` duty is carried by the caller's theorem (the call gets stuck
    /// without it -- `Body.lean` `step`).
    CallSite,
    /// A promise at a device register or a `transition` -- hardware Gabbro does not see.
    /// An assumption; the transition's frame stands in `Assumed ρ`.
    DevicePromise,
    /// An invariant of a `walk`, or its `down`/`leaf` classifier -- a statement about a
    /// HARDWARE table, owed by no function. An assumption, like the device promise.
    WalkInvariant,
    /// A call whose callee this unit does not declare and that is not foreign either --
    /// nothing to take a contract from.
    CallStatement,
    /// A loop without an `invariant`. The measure is carried by the language (`K008`/`K009`);
    /// without the clause there is no statement to preserve, and a loop datum with none
    /// would let a proof conclude from a loop exactly nothing while looking like it did.
    Loop,
    /// `locks S { … }` -- carried since 2026-08-28; this arm is only the fallback.
    Concurrent,
    /// `publishes` at a place with a suffix -- the datum carries the bare atomic only.
    Publish,
    /// `awaits` at a place with a suffix.
    Await,
    /// `exchange` -- both of its shapes are conditional, and a plain swap would store
    /// something the program does not.
    Exchange,
    /// `observes D { … }` -- the RCU read side: a view that MAY be stale.
    Observe,
    /// `let … else` -- the one error propagation, two exits out of a call; the model has no
    /// reason value to carry the second exit on.
    ErrorPropagation,
    /// `narrow … to … else` -- the range lattice underneath is proved
    /// (`Passlogik.Bereich`), the model has no ranges to narrow into.
    Narrowing,
    /// `leave`/`next` aimed at an OUTER loop. The innermost is carried (`Stmt.exit`); a mark
    /// further out would have to travel through a `.loop` step that does not run the body.
    NonLocalExit,
    /// `+=` and its kin at a target whose shape this channel does not know.
    CompoundAssign,
    /// A `match` over something other than an `option`.
    MatchNotOption,
    /// A floating-point value. The model has no float.
    Float,
    /// `old(x)` in a BODY or in a `requires` -- there is no earlier state to read there. In
    /// an `ensures` it is carried: the contract sees the entry state.
    OldState,
    /// A quantifier over a domain other than `slots of`, a `chain(…) in`, `mappings of`,
    /// `queue`, `elems of`, `threads`, `fields of`, or a set membership -- the model has the
    /// index domain and the parent chain, and nothing else.
    Quantified,
    /// **`count k in D : p` -- the model counts nothing** («SG-24»). `Body.lean` carries
    /// `forallSlots`/`existsSlots` as expressions but no cardinality: a count is a
    /// FOLD over the domain, and this channel folds nothing. Bodies lower it to C
    /// through the emitter's counter functions; contracts stating one are refused
    /// here, by name, until the model grows a `countSlots` term. *`forall`/`exists`
    /// stay writable in contracts -- only the number is not one.*
    Counted,
    /// **`threads` -- and the language declares no thread set** (2026-09-08). Every other
    /// domain hangs on a declaration (`slots of` on `count N`, `descendants of` on
    /// `tree { … }`, `mappings of` on `walk … levels`, `queue` on the one field array of a
    /// record); `threads` hangs on nothing, so there is no index domain to cut. Kept apart
    /// from `Quantified` because its way out is a LANGUAGE change, not a rewrite.
    QuantifiedThreads,
    /// **`mappings of <walk>`** (2026-09-08) -- the mappings a page-table walk reaches are
    /// hardware, the same object a `walk` invariant speaks about; those are ASSUMED by name
    /// (`WalkInvariant`), and this model has no term for one inside a routine's clause.
    QuantifiedMappings,
    /// **The LENGTH of a buffer nothing declares** (2026-09-08) -- `lenof(p)` where `p`
    /// points at a `format`. `lenof` over a fixed-length array IS carried (its length stands
    /// in the declaration); a buffer's length is a run-time quantity this model has no place
    /// for. Kept apart from `Builtin`, whose ground is the LAYOUT and not the length.
    BufferLength,
    /// **A field of a record value whose RECORD TYPE no declaration here gives**
    /// (2026-09-08).
    ///
    /// `let c = f(x); c.len` **is carried** since 2026-09-08: a `let` that binds a record
    /// opens a ghost carrier for its fields (`Ctx::record_value`), fresh per BINDING, so
    /// two values of one type are two places and the declared shape still reaches the
    /// proof through `shapeOf`. *Nothing stores into those places*, so the channel can
    /// read a `u32` off `c.len` and never a value -- which is exactly what the checker
    /// knows about a record a call handed back.
    ///
    /// What falls here is the binding whose record this channel cannot NAME: a foreign
    /// callee's answer (`ForeignInfo` carries a shape, not a type), or a `let` of a
    /// pointer type. Without the declaration there is no field list and no shape, and a
    /// carrier named after a guess would be a place nothing declares.
    RecordValue,
    /// **An array inside a record held in a table SLOT** (2026-09-08) --
    /// `e.slots[i].receivers.buf[j]`. A record type is ONE object of this model (the module
    /// header says so), so every slot's copy of the record would be the SAME place -- and a
    /// body that writes two slots' queues would be modelled as writing one. Refused because
    /// serving it would be unsound, not because it is hard.
    ///
    /// **And the ground was MEASURED, not estimated** (2026-09-08, agent a). The one duty
    /// in the corpus that stands behind it -- `probe-ipc-fastpath-durchgestochen`,
    /// `call :: antwortpflicht_paarig` -- was run three times, each against a build of this
    /// file:
    ///
    ///   1. as it stands: `refused (slot-record-array)`;
    ///   2. with the nested place SERVED (any term at all): `refused (no-shape-for-field)`
    ///      -- `enqueue(e.slots[core].senders, caller)` passes a record held in a slot BY
    ///      VALUE, and this model has no record `Value`;
    ///   3. with record-typed slot fields given a shape as well: carried.
    ///
    /// *A `Place` with two indices would therefore carry NOTHING on its own*; the same duty
    /// falls one step later. What both steps want is the same thing -- a record that knows
    /// which slot holds it -- and that is `Place.field carrier name` becoming
    /// `Place.field owner carrier name`, which reverses the 2026-09-07 decision written at
    /// `record_field`: the carrier is the RECORD's name so that a callee's promise about
    /// `s.len` is readable by a caller writing `t.len`.
    SlotRecordArray,
    /// A call inside an expression: a `spec fn` or a pure function used as a value.
    CallInExpression,
    /// A built-in: `lenof`, `sizeof`, `aligned`, `offset_into`. Each names something about
    /// the LAYOUT, and this model has none.
    Builtin,
    /// `Held(L)`/`Has(F)` -- **not a gap**: the lock passes discharge it
    /// (`H005`/`H006`/`H012`/`H016`), and in a contract it is written as `true`.
    LockWitness,
    /// `result` in a clause of the EXPORT datum -- the datum's `post` list drops it.
    Result,
    /// `result` in a BODY, where it names nothing -- a program error, not a gap.
    ResultInBody,
    /// An error reason value (`R::F`) or a function pointer.
    OtherValue,
    /// An expression or predicate form with no Lean term here (`~`, and nothing else today).
    Expression,
    /// A place whose carrier cannot be resolved to a declared `table`, record or `format`.
    Carrier,
    /// A field whose declared type has no shape in this channel -- `wrapping`, a float, a
    /// record, or an OPAQUE new type whose representation `D1` forbids reading.
    FieldShape,
    /// A `refines` whose named `spec fn` is not a plain expression body.
    SpecShape,
    /// A call to a GENERATED table operation whose premises this channel cannot write -- an
    /// `insert` whose `reaches` premise names a root the table's invariants do not name.
    GeneratedOp,
    /// A `transition` of a `device` with a `requires` this channel has no term for.
    Transition,
    /// A constructor whose VALUE this model has no form for -- a record, a `tagged`, or a
    /// device handle.
    ConstructedValue,
    /// A callee whose `requires` this channel cannot write as an expression. **The
    /// precondition is the stuck-condition of the call**, so dropping a clause of it would
    /// make the caller's goal EASIER -- the one direction a refusal exists against.
    CalleeContract,
    /// `return` inside the body of a loop. The loop's meaning is looked up in `Env` as a
    /// state transformer; a body that may leave the ROUTINE from inside would need the
    /// environment to carry a second exit, and it does not.
    ReturnInLoop,
    /// The routine stands on a CYCLE of the call graph. Its duty is written and its contract
    /// is stated, but the wiring from the one to the other needs an induction over the
    /// declared `decreases`, and `unit_closed` does not write one.
    Recursion,
}

/// The three kinds of "no goal" -- see `LeanReason`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    Assumption,
    NoTerm,
    NoWiring,
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
            LeanReason::PassCounter => "pass-counter",
            LeanReason::NonLocalExit => "non-local-exit",
            LeanReason::CompoundAssign => "compound-assignment",
            LeanReason::MatchNotOption => "match-not-option",
            LeanReason::Float => "float",
            LeanReason::OldState => "old-state",
            LeanReason::Quantified => "quantified",
            LeanReason::Counted => "counted",
            LeanReason::QuantifiedThreads => "quantified-threads",
            LeanReason::QuantifiedMappings => "quantified-mappings",
            LeanReason::BufferLength => "layout-buffer-length",
            LeanReason::RecordValue => "record-value",
            LeanReason::SlotRecordArray => "slot-record-array",
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
            LeanReason::CalleeContract => "callee-requires-no-term",
            LeanReason::ReturnInLoop => "return-in-loop",
            LeanReason::Recursion => "recursion",
        }
    }
    pub fn sentence(self) -> &'static str {
        match self {
            LeanReason::ForeignBody => {
                "an `ensures` at a body Gabbro never sees: an ASSUMPTION, stated in `Assumed`"
            }
            LeanReason::Invariant => {
                "`maintains` names an invariant this channel has no term for"
            }
            LeanReason::CallSite => {
                "a precondition at a call site whose caller this channel could not translate"
            }
            LeanReason::DevicePromise => {
                "a promise at hardware Gabbro does not see: an ASSUMPTION"
            }
            LeanReason::WalkInvariant => {
                "an invariant of a `walk` -- a statement about a hardware table: an ASSUMPTION"
            }
            LeanReason::CallStatement => "a call to a routine this unit does not declare",
            LeanReason::Loop => "a loop without an `invariant` -- nothing to preserve",
            LeanReason::Concurrent => {
                "a concurrent statement -- one state and one transition stop carrying here"
            }
            LeanReason::Publish => "`publishes` at a place with a suffix",
            LeanReason::Await => "`awaits` at a place with a suffix",
            LeanReason::Exchange => "`exchange` -- a conditional store, not a swap",
            LeanReason::Observe => "`observes` -- a view that MAY be stale",
            LeanReason::ErrorPropagation => "`let … else` -- two exits out of a call",
            LeanReason::Narrowing => "`narrow` -- the model has no range to narrow into",
            LeanReason::PassCounter => {
                "`passes` in a loop whose domain has no `count` -- nothing bounds the passes"
            }
            LeanReason::NonLocalExit => {
                "`leave`/`next` aimed at an OUTER loop -- the innermost is carried"
            }
            LeanReason::CompoundAssign => "`+=` and its kin at a target without a shape",
            LeanReason::MatchNotOption => "a `match` over something other than an `option`",
            LeanReason::Float => "a floating-point value -- this model has no float",
            LeanReason::OldState => "`old(x)` outside an `ensures` -- no earlier state there",
            LeanReason::Quantified => {
                "a quantifier whose domain names no index range here -- rewrite it over \
                 `slots of <table>`, `elems of <array>`, `queue <record>` or \
                 `chain(a, b) in <slot>`, which do"
            }
            LeanReason::Counted => {
                "a `count` -- this model folds nothing; state the property with \
                 `forall`/`exists`, which it carries"
            }
            // **The way out named here was measured on 2026-09-08 and is a decoration.**
            // A `threads over T` -- or any mark that hangs `threads` on a table -- makes
            // `forall t in threads : P` the SAME index set, the SAME proposition and the
            // same C as `forall t in slots of T : P`. A synonym is exactly the "form that
            // means nothing" of `messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md` §1, so a
            // refusal must not send a reader to it. `PLAN.md` §15 has the differential and
            // the alternative that would NOT be one.
            LeanReason::QuantifiedThreads => {
                "`threads` -- no declaration names the thread set (every other domain hangs \
                 on one); write `slots of <the thread table>`. A `threads over T` would be \
                 a SYNONYM of that and state nothing more -- the surface that would carry \
                 more has to say which slots are LIVE, and Gabbro has no such declaration \
                 (`PLAN.md` §15)"
            }
            LeanReason::QuantifiedMappings => {
                "`mappings of <walk>` -- the mappings of a page-table walk are hardware; \
                 state it as an `invariant` OF the `walk`, which is ASSUMED by name"
            }
            LeanReason::BufferLength => {
                "`lenof` over a buffer whose length no declaration gives -- `lenof` over a \
                 fixed-length array IS carried; give the parameter an array type, or drop \
                 the clause"
            }
            LeanReason::RecordValue => {
                "a field of a record value whose record TYPE no declaration here gives -- a \
                 `let` from a FOREIGN callee, or a pointer binding; annotate the `let` with \
                 the record type, and its fields are carried"
            }
            LeanReason::SlotRecordArray => {
                "an array inside a record held in a table SLOT (`e.slots[i].q.buf[j]`) -- one \
                 object per record TYPE here, so every slot's copy would be the SAME place; \
                 lift the array into a table"
            }
            LeanReason::CallInExpression => "a call inside an expression",
            LeanReason::Builtin => {
                "`sizeof`/`offset_into` -- Gabbro computes no byte layout (the C emitter \
                 refuses `sizeof(T)` for the same reason); there is nothing for the clause \
                 to agree with"
            }
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
                "the carrier of a place is not a declared `table`, record or `format` -- \
                 name it through a parameter of that type, so the place has a declaration \
                 to take its shape from"
            }
            LeanReason::FieldShape => {
                "the declared type of a slot field has no shape in this channel"
            }
            LeanReason::SpecShape => "the named `spec fn` is not a plain expression body",
            LeanReason::GeneratedOp => {
                "a generated table operation whose premises name a root no invariant names"
            }
            LeanReason::Transition => "a `transition` whose `requires` has no term here",
            LeanReason::ConstructedValue => {
                "a record, a `tagged` or a device handle -- this model has no value for one"
            }
            LeanReason::CalleeContract => {
                "a callee whose `requires` has no term -- and a dropped precondition would \
                 make the caller's goal easier"
            }
            LeanReason::ReturnInLoop => {
                "`return` inside a loop body -- the loop's environment carries no second exit"
            }
            LeanReason::Recursion => {
                "a routine on a cycle of the call graph -- the wiring needs an induction \
                 over `decreases`, and none is written"
            }
        }
    }
    pub fn kind(self) -> Kind {
        match self {
            LeanReason::ForeignBody
            | LeanReason::DevicePromise
            | LeanReason::WalkInvariant => Kind::Assumption,
            LeanReason::Recursion => Kind::NoWiring,
            _ => Kind::NoTerm,
        }
    }
    /// **All of them, so a report cannot omit one by forgetting to ask.**
    ///
    /// **`PassCounter` was declared on 2026-09-08 and left out of here** -- the third time
    /// this list has been one step behind the enum beside it (`WalkInvariant`, 2026-09-01,
    /// is the same entry in `zaehle-lean.py`'s own comment). A reason missing here is
    /// refused by the emitter, printed by nobody, and the module's balance line counts it
    /// among the refusals it does not name -- *smaller, which is the direction that
    /// flatters.* The speech test now reads the enum out of THIS FILE and holds every
    /// variant against this array, instead of only checking that what is here is not mute.
    pub const ALL: [LeanReason; 43] = [
        LeanReason::PassCounter,
        LeanReason::QuantifiedThreads,
        LeanReason::QuantifiedMappings,
        LeanReason::BufferLength,
        LeanReason::RecordValue,
        LeanReason::SlotRecordArray,
        LeanReason::ForeignBody,
        LeanReason::Invariant,
        LeanReason::CallSite,
        LeanReason::DevicePromise,
        LeanReason::WalkInvariant,
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
        LeanReason::CalleeContract,
        LeanReason::ReturnInLoop,
        LeanReason::Recursion,
        LeanReason::Counted,
    ];
}

/// **What became of one obligation of the register.**
pub enum LeanVerdict {
    /// Carried by a theorem of the unit -- the routine's, or a loop's. The string names it.
    /// Several obligations may name the same theorem: every `ensures` of a routine, every
    /// `V` at its call sites and every invariant it maintains are one theorem over one body.
    Carried(String),
    /// Carried by several theorems -- a `table` invariant nobody maintains is preserved by
    /// EVERY routine that writes the carrier, and each of them owes it.
    CarriedBy(Vec<String>),
    /// An assumption: hardware, foreign code. Named, never discharged.
    Assumed(LeanReason),
    /// Refused by name.
    Refused(LeanReason),
}

impl LeanVerdict {
    pub fn is_goal(&self) -> bool {
        matches!(self, LeanVerdict::Carried(_) | LeanVerdict::CarriedBy(_))
    }
}

/// **What a table declares.** Field name to the shape its declaration gives it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Shape {
    Int,
    /// **A number with its declared range** (2026-09-08). A place of type `u8 in 0 .. 15`
    /// holds a number the checker keeps in range (`M1`), and the well-typed world says so:
    /// a read from it is `∃ n, σ p = .int n ∧ 0 ≤ n ∧ n ≤ 15`, and a store into it owes the
    /// range -- the same arithmetic the checker decided, now decided by `omega` over the
    /// guards the model carries. Without it a routine that returns such a field could not
    /// promise its own declared range (`13-zeuge-mit-staerke`).
    IntIn(i128, i128),
    Bool,
    Opt,
    /// A `tagged` value -- one of the declared cases, with its payload where the case has
    /// one. The cases are interned (`sum_cases`), so that the shape stays a `Copy` and the
    /// datum still names every case: `.sum [("Kurz", true), ("Leer", false)]`.
    Sum(u32),
}

/// The interned case lists of every `tagged` type this process has read: `(name, has a
/// payload)` per case. **The model has to know the cases**: a `match` over a `tagged`
/// value has an arm per case, and a value the type excludes would get the model stuck
/// where the program cannot go.
/// **A case's payload, as the model types it**: `None` -- no payload; `Some(None)` -- a
/// number without a range; `Some(Some((lo, hi)))` -- a number in its declared range. The
/// range is part of the type, and the checker keeps every payload in it -- so the model
/// says so, or a `match` arm that reads the payload could not use the range it has.
type Payload = Option<Option<(i128, i128)>>;

fn sum_cases() -> &'static std::sync::Mutex<Vec<Vec<(String, Payload)>>> {
    static CASES: std::sync::OnceLock<std::sync::Mutex<Vec<Vec<(String, Payload)>>>> = std::sync::OnceLock::new();
    CASES.get_or_init(|| std::sync::Mutex::new(Vec::new()))
}

fn intern_sum(cases: Vec<(String, Payload)>) -> u32 {
    let mut all = sum_cases().lock().unwrap();
    if let Some(i) = all.iter().position(|c| *c == cases) {
        return i as u32;
    }
    all.push(cases);
    (all.len() - 1) as u32
}

impl Shape {
    /// A number, ranged or not.
    fn is_int(self) -> bool {
        matches!(self, Shape::Int | Shape::IntIn(..))
    }
    /// The declared range, where the shape carries one.
    fn range(self) -> Option<(i128, i128)> {
        match self {
            Shape::IntIn(lo, hi) => Some((lo, hi)),
            _ => None,
        }
    }
    fn predicate(self) -> &'static str {
        match self {
            Shape::Int | Shape::IntIn(..) => "isInt",
            Shape::Bool => "isBool",
            Shape::Opt => "isOption",
            Shape::Sum(_) => "isTagged",
        }
    }
    fn lean(self) -> String {
        match self {
            Shape::Int => ".int".into(),
            Shape::IntIn(lo, hi) => format!("(.intIn {} {})", int_lit(lo), int_lit(hi)),
            Shape::Bool => ".bool".into(),
            Shape::Opt => ".opt".into(),
            Shape::Sum(i) => {
                let all = sum_cases().lock().unwrap();
                let cases: Vec<String> = all[i as usize]
                    .iter()
                    .map(|(n, p)| format!("({}, {})", quoted(n), payload_lean(*p)))
                    .collect();
                format!("(.sum [{}])", cases.join(", "))
            }
        }
    }
}

/// The shape a declared type gives a value. `None` where this channel has no shape for it --
/// **and a place of such a field is refused, not defaulted.**
///
/// **The option distinction is read SYNTACTICALLY and the rest through the environment**,
/// and the split is not tidiness. `option index into T` and `index into T` both resolve to
/// an integer -- the sentinel lowering is the point of `Option_Sonderwert.thy` -- so a
/// resolved type cannot tell them apart.
/// **The declared range of every integer parameter of `f`** -- what the checker holds at
/// every call site, and what the body may therefore assume. A parameter whose type has
/// no range (a pointer, a boolean) has no entry.
fn param_ranges(f: &FnDecl, u: &crate::umgebung::Umgebung, module: &str) -> HashMap<String, (i128, i128)> {
    let mut out = HashMap::new();
    for p in &f.parameter {
        if !shape_of(&p.typ, u, module).is_some_and(Shape::is_int) {
            continue;
        }
        if let Some(b) = u.typ_von_ausdruck_decl(module, &p.typ).bereich() {
            out.insert(p.name.text.clone(), (b.min, b.max));
        }
    }
    out
}

/// The declared range of an integer type, where it has one.
fn result_range_of(t: &TypExpr, u: &crate::umgebung::Umgebung, module: &str) -> Option<(i128, i128)> {
    if !shape_of(t, u, module).is_some_and(Shape::is_int) {
        return None;
    }
    u.typ_von_ausdruck_decl(module, t).bereich().map(|b| (b.min, b.max))
}

fn shape_of(t: &TypExpr, u: &crate::umgebung::Umgebung, module: &str) -> Option<Shape> {
    if let TypExpr::Index { tabelle, optional, .. } = t {
        if *optional {
            return Some(Shape::Opt);
        }
        // **F3 (S4, 2026-09-11): `index into T` is `0 ..< count`, not `.int`.** The
        // type carries the bound by construction (`Umgebung::indextyp` builds it from
        // the same `count N`), and the checker holds it at every call site -- so the
        // emitted shape says it, and `schluss` (`Ausdruck.lean`, `.place`) sees the
        // `intIn` it demands. A table without a `count` keeps `.int` (W10: an unproved
        // bound is not narrowed).
        if let Some(q) = u.nennt_tabelle(module, &tabelle.text) {
            if let Some(n) = u.kapazitaeten.get(&q).copied() {
                let hi = i128::try_from(n).unwrap_or(i128::MAX).saturating_sub(1);
                return Some(Shape::IntIn(0, hi.max(0)));
            }
        }
        return Some(Shape::Int);
    }
    shape_of_typ(&u.typ_von_ausdruck_decl(module, t))
}

fn shape_of_typ(t: &crate::typen::Typ) -> Option<Shape> {
    use crate::typen::Typ;
    match t {
        // a declared size has a range; a literal's width is borrowed and says nothing
        Typ::Ganzzahl(b) if !b.literal => Some(Shape::IntIn(b.min, b.max)),
        Typ::Ganzzahl(_) => Some(Shape::Int),
        Typ::Wahrheit => Some(Shape::Bool),
        Typ::Tabelle(_) => Some(Shape::Int),
        // **A new type -- opaque or not -- has the shape of what it is over.** Until
        // 2026-09-07 an `opaque` stopped here: reading its representation is the implicit
        // conversion `D1` forbids THE PROGRAM. The model is not the program: a slot field
        // `kind : ObjectKind` over a `u8` holds a number the world has to type, or every
        // store into the slot is unchecked and every invariant over the field has no term.
        // `D1` stands where it stood -- in the checker, over the source.
        Typ::Benannt { unter, .. } => shape_of_typ(unter),
        // `wrapping` is a NUMBER; what makes it wrap is the store (`Expr.wrapTo`), and the
        // emitter writes that at every store into a wrapping field (`wrap_of`).
        Typ::Umlaufend(_) => Some(Shape::Int),
        // **A `tagged` type is a SUM** -- one of its cases, with a numeric payload where
        // the case has one (`Value.tagged`).
        Typ::Summe { varianten, .. } => Some(Shape::Sum(intern_sum(
            varianten
                .iter()
                .map(|(n, p)| (n.clone(), p.as_ref().map(|t| t.bereich().filter(|b| !b.literal).map(|b| (b.min, b.max)))))
                .collect(),
        ))),
        Typ::Gleitkomma(_)
        | Typ::Nie
        | Typ::Zeiger(_)
        | Typ::Verbund(_)
        | Typ::Feld { .. }
        | Typ::Register { .. }
        | Typ::Verbundname(_)
        | Typ::FnPtr(_)
        | Typ::Unbekannt
        | Typ::Grund(_) => None,
    }
}

/// **Where the thing being translated stands, as far as the words `result` and `old` are
/// concerned.**
#[derive(Clone, Copy, PartialEq, Eq)]
enum ResultSite {
    /// A body: a statement, or the invariant of a loop inside one. `result` names nothing
    /// here and never will; `old` has no earlier state.
    Body,
    /// A `requires` -- of the export datum or of a contract. `result` is not bound and `old`
    /// has no earlier state.
    Contract,
    /// An `ensures`. `result` is bound as a local, `old(e)` is bound as a local too --
    /// `old#1`, `old#2`, … -- and the goal quantifies the values over the ENTRY state.
    Bound,
    /// An `ensures` as the RETURN PATH of a loop reads it: `result` is the local `#ret`
    /// the desugared `return` bound, and `old` has no state to read.
    LoopRet,
}

/// A table, as this channel reads its declaration.
#[derive(Clone)]
pub struct TableInfo {
    pub fields: Vec<(String, Option<Shape>)>,
    /// `(field) -> (bits, signed)` for every `wrapping` slot field.
    pub wraps: HashMap<String, (u8, bool)>,
    /// `count N` -- the bound of every quantifier over the table and the fuel of every
    /// `reaches` through it. `None` where the declaration names none.
    pub count: Option<i128>,
    /// The occupancy field, where the table has `ops`.
    pub belegt: Option<String>,
    /// The parent edge of a `tree` table.
    pub elter: Option<String>,
    /// The root a `reaches`-invariant of this table names, if one does.
    pub root: Option<Expr>,
}

/// One routine, as this channel reads its declaration.
#[derive(Clone)]
struct RoutineInfo {
    module: String,
    decl: FnDecl,
    params: Vec<(String, Option<Shape>)>,
    /// **The declared range of every integer parameter** -- `n : u32 in 0 .. TIEFE` -- as
    /// the bounds the checker guarantees at every call site (`M1xx`). They travel in the
    /// precondition beside the shape, so that a body's arithmetic has what the checker had.
    ranges: HashMap<String, (i128, i128)>,
    /// The carriers the declared `effects` list writes -- `writes X` and `consumes X`.
    writes: Vec<String>,
    /// The invariants this routine has to preserve: the ones `maintains` names, and every
    /// `table`/`group` invariant of a carrier it writes that no `maintains` names -- a global
    /// invariant is preserved by its writers, and that is the whole meaning of "global".
    maintained: Vec<String>,
}

/// Everything the translation of one body may look at.
struct Ctx<'a> {
    unit: &'a Unit,
    /// Base name to the table it stands for, for this routine.
    carrier: HashMap<String, String>,
    /// Base name to the record or `format` it stands for.
    record_carrier: HashMap<String, String>,
    /// **A `let`-bound record VALUE, and the ghost carrier its fields are named under**
    /// (2026-09-08): `let c = fertig(k, 7); c.len` maps `c` to `("Completion", "c#r1")`,
    /// and `c.len` is the place `.field "c#r1" "len"`.
    ///
    /// **Why a carrier of its OWN and not the record type's.** A place named
    /// `.field "Completion" "len"` is the one object of that TYPE (`record_field`), and a
    /// binding is not that object -- two bindings of one type would be one place, and a
    /// body that reads both would read one. The ghost carrier is fresh per BINDING
    /// (`record_binds` counts them), so a `let` that binds the name a second time gets a
    /// second carrier and the two never meet. **`#` is not a Gabbro identifier character**,
    /// so no declared carrier can collide with one of these.
    ///
    /// *What it does NOT claim*: nothing stores into these places, so the model can prove
    /// no VALUE for `c.len` -- only the declared SHAPE, which `shapeOf` gives it like any
    /// other record field and `wellFormed` then carries. An `ensures` about the field's
    /// value stays the person's; a clause that only needs `c.len` to be a `u32` closes.
    record_value: HashMap<String, (String, String)>,
    /// How many record values this body has bound -- the number in the ghost carrier.
    record_binds: usize,
    /// Parameter and `let` names -- these read from `locals`, not from the world -- with the
    /// shape each has, where it is known. **The shape is what a loop invariant carries
    /// across the pass** (`Body.lean`, `hasShape`).
    locals: Vec<(String, Option<Shape>)>,
    /// The declared ranges of the integer parameters (`RoutineInfo::ranges`).
    ranges: HashMap<String, (i128, i128)>,
    /// The parameters that point at a `device` -- a place under one is a register, and
    /// what a register reads is the device's promise, not the model's computation.
    device_carrier: BTreeSet<String>,
    /// `Self` inside a `table`/`group` invariant stands for the carrier.
    self_carrier: Option<String>,
    /// The module the routine is declared in -- a declared type resolves there.
    module: String,
    /// Whether a CALL may be translated -- the export datum says yes and so does the
    /// obligation channel since 2026-09-07; `false` only for a contract clause.
    allow_calls: bool,
    result_site: ResultSite,
    uses_result: bool,
    /// The `old(e)` sub-expressions met in an `ensures`, in order; `old#i` is bound to the
    /// value of the i-th one in the entry state.
    olds: Vec<String>,
    /// Collected while translating: `(carrier, field, form, origin)`, deduplicated.
    seen: Vec<(String, String, Shape, String)>,
    /// `(carrier, field, shape)` for every RECORD field touched.
    seen_records: Vec<(String, String, Shape)>,
    /// How many call results have been hoisted into locals (`#m1`, `#m2`, …).
    hoists: usize,
    /// The calls of the statement being translated that ARE hoisted -- by the address of
    /// the `Ruf` in the tree -- and the local each one's result is bound to.
    hoisted: HashMap<usize, String>,
    /// The routine's name and how many loops have been numbered in it.
    routine: String,
    loops: usize,
    /// The loops met in this body, innermost first as they close.
    loop_infos: Vec<LoopInfo>,
    /// The marks of the loops currently open, innermost last -- `None` for an unmarked one.
    loop_stack: Vec<Option<String>>,
    /// Every callee this body calls -- routine names, generated ops and transitions alike.
    callees: BTreeSet<String>,
    /// Every slot field read at a BARE LOCAL index -- `(carrier, field, index, shape)` --
    /// for the witnesses the proof opens with: a read at a witnessed index is a value the
    /// well-typed world gives a shape to.
    option_reads: Vec<(String, String, String, Shape)>,
    /// **What a `return` inside a loop has to establish** -- the routine's `ensures` (with
    /// `result` read as the local `#ret`) and the invariants it keeps, as one expression.
    /// `None` where an `ensures` has no such reading (`old`), and then a `return` in a loop
    /// is refused.
    ret_post: Option<String>,
    /// Whether the routine returns a value -- decides the shape of the desugared `return`.
    has_result: bool,
    /// **The invariants the routine keeps, as terms** -- every loop's invariant carries them
    /// across the pass, because a call inside the loop demands them at its entry and the
    /// routine's promise demands them at its end.
    kept: Vec<String>,
}

/// **The type of a loop's rule** -- `LoopRuleP` where the loop counts its passes,
/// `LoopRule` everywhere else (agent b, 2026-09-08).
fn loop_rule_type(l: &LoopInfo, wf: &str) -> String {
    let lid = lean_ident(&l.id);
    match l.passes {
        Some(_) => format!(
            "LoopRuleP ρ {} {wf} {lid}_inv {}",
            quoted(&l.id),
            quoted(crate::PASSZAEHLER_LEAN)
        ),
        None => format!("LoopRule ρ {} {wf} {lid}_inv", quoted(&l.id)),
    }
}

/// One loop of a routine, with everything its own theorem needs.
#[derive(Clone)]
pub struct LoopInfo {
    /// `f#1` -- the id the environment is looked up under.
    pub id: String,
    /// The invariant, strengthened by the shapes of the locals in scope.
    pub inv: String,
    /// The loop variable, or a name nothing reads.
    pub var: String,
    pub body: String,
    /// The callees of the loop body and the loop ids nested in it -- the hypotheses its
    /// theorem carries.
    pub callees: BTreeSet<String>,
    pub nested: Vec<String>,
    /// The locals whose shape the invariant carries, in conjunct order.
    pub shapes: Vec<(String, Shape)>,
    /// How many conjuncts the invariant has -- the path to each shape runs through them.
    pub parts: usize,
    /// The slot fields the body reads at a bare local index.
    pub reads: Vec<(String, String, String, Shape)>,
    /// The declared ranges of the parameters in scope -- the ranged shape conjuncts of the
    /// invariant open with their bounds.
    pub ranges: HashMap<String, (i128, i128)>,
    /// The record fields the routine has read up to and inside this loop.
    pub records: Vec<(String, String, Shape)>,
    /// **The index range the loop visits** -- `[lo, hi)` for a `traverse` over a domain
    /// inside one table (its `count`); `None` for a `retry`/`forever` pass. A pass may
    /// assume its index is in the range (`RunsLoopIn`, `looprule_of_body_in`).
    pub range: Option<(i128, i128)>,
    /// **The bound on the NUMBER of passes** -- the domain's `count` -- for a loop whose
    /// invariant names `passes` (agent b, 2026-09-08). `None` for every other loop, and
    /// then nothing of the pass counter is emitted at all.
    pub passes: Option<i128>,
    /// **The locals in scope at the loop's entry, oldest first, WITH duplicates and
    /// WITHOUT shapes where the walk knows none** (S4, 2026-09-10). A clone of
    /// `Ctx::locals` taken beside `shapes`: the seam witness replays `binde` over it to
    /// rebuild the exact `Umgebung` `pruefe` threads to the `.loop` -- duplicates for
    /// the keep-on-equal rule, `None`s for the skip rule (`#ret` excepted, see there).
    /// Read-only for every other consumer: nothing of the duty channel looks at it.
    pub entry_locals: Vec<(String, Option<Shape>)>,
}

impl Ctx<'_> {
    fn table_of(&self, base: &str) -> Option<&String> {
        if base == "Self" {
            return self.self_carrier.as_ref();
        }
        self.carrier.get(base)
    }

    fn is_local(&self, n: &str) -> bool {
        self.locals.iter().any(|(l, _)| l == n)
    }

    fn push_local(&mut self, n: &str, sh: Option<Shape>) {
        // a binding of a parameter's name shadows it -- and its declared range with it
        self.ranges.remove(n);
        self.locals.push((n.to_string(), sh));
    }

    fn note_option(&mut self, carrier: &str, feld: &str, form: Shape, index: &Expr) {
        let ExprArt::Ort(o) = &crate::ohne_klammern(index).art else { return };
        if !o.suffixe.is_empty() || !self.is_local(&o.basis.text) {
            return;
        }
        let p = o.basis.text.clone();
        if !self
            .option_reads
            .iter()
            .any(|(t, f, i, _)| t == carrier && f == feld && *i == p)
        {
            self.option_reads
                .push((carrier.to_string(), feld.to_string(), p, form));
        }
    }

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
fn field_shape(base: &str, feld: &str, c: &Ctx) -> Result<(String, Shape, String), LeanReason> {
    let tab = c.table_of(base).ok_or(LeanReason::Carrier)?.clone();
    let info = c.unit.tables.get(&tab).ok_or(LeanReason::Carrier)?;
    let (_, form) = info
        .fields
        .iter()
        .find(|(n, _)| n == feld)
        .ok_or(LeanReason::Carrier)?;
    let form = form.ok_or(LeanReason::FieldShape)?;
    let base = if base == "Self" { tab.clone() } else { base.to_string() };
    Ok((base, form, tab))
}

/// **A record field, as the carrier it is written under and its shape.** The carrier is
/// the RECORD'S name, not the parameter's -- `s.len` at `s : ptr<…> Text` is the place
/// `.field "Text" "len"` -- for the reason tables have (`place_carrier`): a callee's
/// promise about `s.len` has to be readable by a caller writing `t.len`, and `shapeOf`
/// types the place by the declaration. *What that assumes is written in the module
/// header: two objects of one record type are one object of the model.* Until
/// 2026-09-07 the parameter name stood here, and no contract about a record composed
/// and no read from one had a shape.
fn record_field(base: &str, field: &str, c: &Ctx) -> Result<(String, Shape), LeanReason> {
    // **A local that is not a carrier is a record VALUE** (2026-09-08) -- `let c = f(x);
    // c.len`. Its own refusal: the carrier is not missing a declaration, it is not a place
    // at all, and naming one would make two different values the same place.
    // **A `let`-bound record value is carried under its own ghost carrier** (2026-09-08).
    // See `Ctx::record_value`: the binding, not the type, names the place.
    if let Some((rec, ghost)) = c.record_value.get(base) {
        let fields = c.unit.records.get(rec).ok_or(LeanReason::Carrier)?;
        let (_, shape) = fields
            .iter()
            .find(|(n, _)| n == field)
            .ok_or(LeanReason::Carrier)?;
        return Ok((ghost.clone(), shape.ok_or(LeanReason::FieldShape)?));
    }
    let rec = c
        .record_carrier
        .get(base)
        .ok_or(if c.is_local(base) { LeanReason::RecordValue } else { LeanReason::Carrier })?;
    let fields = c.unit.records.get(rec).ok_or(LeanReason::Carrier)?;
    let (_, shape) = fields
        .iter()
        .find(|(n, _)| n == field)
        .ok_or(LeanReason::Carrier)?;
    Ok((rec.clone(), shape.ok_or(LeanReason::FieldShape)?))
}

/// **The carrier name a place is written under in the datum.** A parameter that points at a
/// table stands for the table -- `t.slots[i].x` at `t : ptr<…> Buch` is the place
/// `.slot "Buch" i "x"`, not `.slot "t" …`: two functions naming the same table through
/// two parameter names name ONE object, and the contract of the one has to be readable by
/// the other. *Until 2026-09-07 the parameter name stood in the place, and a callee's
/// `ensures` about `t.slots[…]` said nothing to a caller writing `c.slots[…]`.*
fn place_carrier(base: &str, tab: &str) -> String {
    let _ = base;
    tab.to_string()
}

/// A place, as a `Gabbro.Body.Expr`. **Three forms and nothing else:** a bare name,
/// `carrier.slots[i].field`, and `carrier.field`.
fn place_term(o: &Ort, c: &mut Ctx) -> Result<Carried, LeanReason> {
    if o.suffixe.is_empty() {
        let n = &o.basis.text;
        if c.is_local(n) {
            return Ok(LeanCarried::PlaceLocal.term(format!("(.name {})", quoted(n))));
        }
        // **`passes` in a loop invariant is the pass counter** (agent b, 2026-09-08): the
        // ghost local the emitter binds to 0 before the loop and the pass increases by one.
        // It is read only where that local exists -- and `passes_is_free` has already
        // decided that no declared name of that spelling is in the way.
        if n == crate::PASSZAEHLER && passes_is_free(c) {
            return if c.is_local(crate::PASSZAEHLER_LEAN) {
                Ok(LeanCarried::PlacePassCounter
                    .term(format!("(.name {})", quoted(crate::PASSZAEHLER_LEAN))))
            } else {
                Err(LeanReason::PassCounter)
            };
        }
        // **A constant is its VALUE**, not a place: `WURZEL` names `0`, and a world place
        // called "WURZEL" would be a place nothing declares. Table constants are looked up
        // under the tables in scope as well.
        if let Some(v) = const_value(n, c) {
            return Ok(LeanCarried::PlaceConstant.term(format!("(.lit (.int {}))", int_lit(v))));
        }
        return Ok(LeanCarried::PlaceGlobal.term(format!("(.global {})", quoted(n))));
    }
    if let [OrtSuffix::Feld(f)] = &o.suffixe[..] {
        let (base, shape) = record_field(&o.basis.text, &f.text, c)?;
        c.note_record(&base, &f.text, shape);
        return Ok(LeanCarried::PlaceRecordField
            .term(format!("(.fieldOf {} {})", quoted(&base), quoted(&f.text))));
    }
    // **A register of a device is the device's promise** -- `v.GSTS.TES` reads what the
    // hardware answers, and a clause over it is an assumption by name, not a refusal.
    if c.device_carrier.contains(&o.basis.text) {
        return Err(LeanReason::DevicePromise);
    }
    // **An array element is a slot of the array's pseudo-table**: `r.plaetze[j]` and
    // `buf[i]` (see `Unit::record_arrays`).
    if let Some((tab, i)) = array_place(o, c) {
        let shape = array_elem_shape(&tab, c)?;
        let idx = expr_term(i, c)?;
        c.note(&tab, "elem", shape, &format!("element of `{tab}`"));
        c.note_option(&tab, "elem", shape, i);
        return Ok(LeanCarried::PlaceArrayElement
            .term(format!("(.place {} {} \"elem\")", quoted(&tab), idx)));
    }
    // **`T.slots[i].f.g[j]` -- an array inside a record held in a SLOT** (2026-09-08). The
    // place exists in the program and the C emitter writes it; this model cannot, and the
    // ground is soundness and not effort: a record type is ONE object here, so the copy in
    // slot 3 and the copy in slot 7 would be the same place, and a body writing both would
    // be modelled as writing one. Named apart from `Carrier` so a reader is not sent looking
    // for a missing declaration.
    if let [OrtSuffix::Feld(slots), OrtSuffix::Index(_), OrtSuffix::Feld(_), ..] = &o.suffixe[..] {
        if slots.text == "slots" && o.suffixe.len() > 3 {
            return Err(LeanReason::SlotRecordArray);
        }
    }
    let [OrtSuffix::Feld(slots), OrtSuffix::Index(i), OrtSuffix::Feld(f)] = &o.suffixe[..] else {
        return Err(LeanReason::Carrier);
    };
    if slots.text != "slots" {
        return Err(LeanReason::Carrier);
    }
    let (base, shape, tab) = field_shape(&o.basis.text, &f.text, c)?;
    let idx = expr_term(i, c)?;
    let carrier = place_carrier(&base, &tab);
    c.note(&carrier, &f.text, shape, &format!("`{}` in `{}`", f.text, tab));
    c.note_option(&carrier, &f.text, shape, i);
    Ok(LeanCarried::PlaceSlotField.term(format!(
        "(.place {} {} {})",
        quoted(&carrier),
        idx,
        quoted(&f.text)
    )))
}

/// **The pseudo-table and the index of an array place** -- `r.f[i]` at a record carrier
/// `r` whose `f` is an array, or `buf[i]` at a static array -- and `None` for any other
/// form.
fn array_place<'a>(o: &'a Ort, c: &Ctx) -> Option<(String, &'a Expr)> {
    match &o.suffixe[..] {
        [OrtSuffix::Feld(f), OrtSuffix::Index(i)] => {
            let rec = c.record_carrier.get(&o.basis.text)?;
            let arrays = c.unit.record_arrays.get(rec)?;
            let (_, tab) = arrays.iter().find(|(n, _)| *n == f.text)?;
            Some((tab.clone(), i))
        }
        [OrtSuffix::Index(i)] => {
            let tab = c.carrier.get(&o.basis.text)?;
            let info = c.unit.tables.get(tab)?;
            if info.fields.len() == 1 && info.fields[0].0 == "elem" {
                Some((tab.clone(), i))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// The shape of the elements of an array pseudo-table.
fn array_elem_shape(tab: &str, c: &Ctx) -> Result<Shape, LeanReason> {
    let info = c.unit.tables.get(tab).ok_or(LeanReason::Carrier)?;
    info.fields.first().and_then(|(_, s)| *s).ok_or(LeanReason::FieldShape)
}

/// The value of a constant in scope -- module constants, and the constants of every table
/// of the unit (`WURZEL` inside `table Kappenraum { const WURZEL … }`).
fn const_value(n: &str, c: &Ctx) -> Option<i128> {
    if let Some(v) = c.unit.u.konst_wert_von_namen(&c.module, n) {
        return Some(v);
    }
    let mut names: Vec<&String> = c.unit.tables.keys().collect();
    names.sort();
    for t in names {
        if let Some(v) = c.unit.u.konst_wert_von_namen(&c.module, &format!("{t}::{n}")) {
            return Some(v);
        }
    }
    None
}

/// **The index of a slot place `T.slots[i]` -- the operand of `reaches`.** A bare name is
/// an index too -- `WURZEL`, a constant -- and then the table is the other operand's.
fn slot_index(o: &Ort, c: &mut Ctx) -> Result<(Option<String>, String), LeanReason> {
    if o.suffixe.is_empty() {
        return Ok((None, place_term(o, c)?.into_term()));
    }
    let [OrtSuffix::Feld(slots), OrtSuffix::Index(i)] = &o.suffixe[..] else {
        return Err(LeanReason::Quantified);
    };
    if slots.text != "slots" {
        return Err(LeanReason::Quantified);
    }
    let tab = c.table_of(&o.basis.text).ok_or(LeanReason::Carrier)?.clone();
    Ok((Some(tab), expr_term(i, c)?.into_term()))
}

/// An expression as a `Gabbro.Body.Expr`.
///
/// **The `match` has no catch-all**, and that is deliberate even though every unlisted arm
/// would refuse: a new expression form must be DECIDED here, not defaulted.
fn expr_term(e: &Expr, c: &mut Ctx) -> Result<Carried, LeanReason> {
    match &e.art {
        ExprArt::Zahl(n) => Ok(LeanCarried::ExprLiteral.term(format!("(.lit (.int {n}))"))),
        ExprArt::Wahr => Ok(LeanCarried::ExprLiteral.term("(.lit (.bool true))")),
        ExprArt::Falsch => Ok(LeanCarried::ExprLiteral.term("(.lit (.bool false))")),
        ExprArt::Klammer(x) => expr_term(x, c),
        ExprArt::Ort(o) => place_term(o, c),
        ExprArt::Unaer(UnOp::Nicht, x) => {
            Ok(LeanCarried::ExprUnary.term(format!("(.un .not {})", expr_term(x, c)?)))
        }
        ExprArt::Unaer(UnOp::Negativ, x) => {
            Ok(LeanCarried::ExprUnary.term(format!("(.un .neg {})", expr_term(x, c)?)))
        }
        // **`~` has no term here, and the reason is the model and not the operator.** A
        // complement is `2^n - 1 - x`, and the `n` is nowhere in this channel.
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
                // Division and the bit operations: `Gabbro.Body` takes `Int.tdiv`/`Int.tmod`
                // and gets STUCK at a zero denominator or a negative operand of a mask, so
                // a proof through one has to establish the premise.
                BinOp::Geteilt => "div",
                BinOp::Rest => "rem",
                BinOp::BitUnd => "band",
                BinOp::BitOder => "bor",
                BinOp::BitXor => "bxor",
                BinOp::SchiebLinks => "shl",
                BinOp::SchiebRechts => "shr",
                // PLAN-BITS section 4 (lane 88): the overflow operators have no
                // term here. `Ueberlauf.lean` carries `Zahl.addW/subW/mulW/shlW`
                // as proof-level functions, but `Syntax.lean`'s `Expr` has no
                // wrapping or saturating constructor -- and the modulus `N`
                // is nowhere in this channel, the same reason `~` is refused
                // two arms above. Carrying them as plain `add`/`sub` would
                // prove what `pruefe` refuses.
                BinOp::PlusWrap
                | BinOp::MinusWrap
                | BinOp::MalWrap
                | BinOp::SchiebLinksWrap
                | BinOp::PlusSat => return Err(LeanReason::Expression),
            };
            Ok(LeanCarried::ExprBinary.term(format!(
                "(.bin .{z} {} {})",
                expr_term(a, c)?,
                expr_term(b, c)?
            )))
        }
        ExprArt::Ruf(r) if c.hoisted.contains_key(&(r as *const Ruf as usize)) => {
            Ok(LeanCarried::ExprHoistedCall
                .term(format!("(.name {})", quoted(&c.hoisted[&(r as *const Ruf as usize)]))))
        }
        ExprArt::Ruf(r) => match r.path().and_then(|p| p.teile.last()).map(|i| &i.text) {
            Some(n) if n == "None" && r.argumente.is_empty() => {
                Ok(LeanCarried::ExprOption.term("(.lit .absent)"))
            }
            Some(n) if n == "Some" && r.argumente.len() == 1 => {
                // **F10 (S4): `Some(x)` is refused where `x` is provably not a number.**
                // `schluss` (`Ausdruck.lean:246`) gives `.someOf` a shape only over a
                // `zahl` inner, and `eval` gets stuck on anything else -- a `someOf`
                // over a truth value, an option or a `tagged` value has no model value
                // at all, so carrying it would prove what `pruefe` refuses. The tracked
                // shape says it where it is known: an index stays `Int`/`IntIn` and
                // passes, exactly as before. An unknown shape (`None`) still passes --
                // an unproved bound is not a false one (W10). What this does NOT close
                // is a well-shaped value outside the TARGET option's bound (`gift/170`,
                // `Some(8)` on `count 8`): the bound lives at the use site, and reading
                // it here would be a guess -- that half needs the target type threaded
                // down, or `Shape.optIn` on the model side (S3 finding 2).
                if matches!(
                    shape_of_expr(&r.argumente[0], c),
                    Some(Shape::Bool) | Some(Shape::Opt) | Some(Shape::Sum(_))
                ) {
                    return Err(LeanReason::Expression);
                }
                Ok(LeanCarried::ExprOption.term(format!("(.someOf {})", expr_term(&r.argumente[0], c)?)))
            }
            // **`Case(e)` of a `tagged type` is a VALUE**, and so is a bare `Case`.
            Some(n) if c.unit.variants.contains_key(n.as_str()) => {
                match (c.unit.variants[n.as_str()], r.argumente.len()) {
                    (Some(false), 0) => {
                        Ok(LeanCarried::ExprTagged.term(format!("(.tagOf {} none)", quoted(n))))
                    }
                    (Some(true), 1) => Ok(LeanCarried::ExprTagged.term(format!(
                        "(.tagOf {} (some {}))",
                        quoted(n),
                        expr_term(&r.argumente[0], c)?
                    ))),
                    _ => Err(LeanReason::ConstructedValue),
                }
            }
            // **A `spec fn` in a predicate is INLINED.** It is a pure expression over its
            // parameters (`M113`), so its meaning at a call is its body with the arguments
            // for the parameters -- and the arguments of the corpus are bare names, which
            // is the one substitution this channel makes. *Anything else stays a call.*
            Some(n) if c.unit.specs.contains_key(n.as_str()) => {
                let spec = c.unit.specs[n.as_str()].clone();
                let FnRumpf::Pred(body) = &spec.rumpf else {
                    return Err(LeanReason::SpecShape);
                };
                if spec.parameter.len() != r.argumente.len() {
                    return Err(LeanReason::CallInExpression);
                }
                let mut pairs = Vec::new();
                for (p, a) in spec.parameter.iter().zip(r.argumente.iter()) {
                    let ExprArt::Ort(o) = &crate::ohne_klammern(a).art else {
                        return Err(LeanReason::CallInExpression);
                    };
                    if !o.suffixe.is_empty() {
                        return Err(LeanReason::CallInExpression);
                    }
                    pairs.push((p.name.text.clone(), o.basis.text.clone()));
                }
                let inlined = renamed_pred(body, &pairs);
                pred_term(&inlined, c)
            }
            _ => Err(LeanReason::CallInExpression),
        },
        ExprArt::Gleitkomma { .. } => Err(LeanReason::Float),
        // **«SG-24»** -- the model folds nothing (`LeanReason::Counted`); bodies
        // lower the count to C, contracts stating one are refused here, by name.
        ExprArt::Zaehle { .. } => Err(LeanReason::Counted),
        // **Lane E2:** a library call lowers to no term -- the checker
        // refuses every one (`N057`/`N069`), so the channel maps it to the
        // existing `CallStatement` refusal like any undeclared call.
        ExprArt::LibraryCall(_) => Err(LeanReason::CallStatement),
        // **Two built-ins have a meaning here, and the third has none.** `aligned(e, n)` is
        // `e % n == 0`; `lenof` of an array is its declared length, a constant of the
        // declaration and not of the run. `sizeof` is about the LAYOUT, and `lenof` of a
        // buffer pointer about the run -- this model has neither.
        ExprArt::Eingebaut(b) => match b.as_ref() {
            Eingebaut::Aligned(x, n) => Ok(LeanCarried::ExprAligned.term(format!(
                "(.bin .eq (.bin .rem {} {}) (.lit (.int 0)))",
                expr_term(x, c)?,
                expr_term(n, c)?
            ))),
            Eingebaut::Lenof(TypOderOrt::Ort(o)) => {
                let tab = match &o.suffixe[..] {
                    [OrtSuffix::Feld(f)] => c
                        .record_carrier
                        .get(&o.basis.text)
                        .and_then(|rec| c.unit.record_arrays.get(rec))
                        .and_then(|arrays| arrays.iter().find(|(n, _)| *n == f.text))
                        .map(|(_, t)| t.clone()),
                    [] => c.carrier.get(&o.basis.text).cloned(),
                    _ => None,
                };
                let count = tab
                    .and_then(|t| c.unit.tables.get(&t))
                    .filter(|info| info.fields.len() == 1 && info.fields[0].0 == "elem")
                    .and_then(|info| info.count);
                match count {
                    Some(n) => {
                        Ok(LeanCarried::ExprArrayLength.term(format!("(.lit (.int {}))", int_lit(n))))
                    }
                    // **A `lenof` whose place is not a fixed-length array** -- a pointer to
                    // a `format`, say. Its own refusal since 2026-09-08: the ground is that
                    // NOTHING DECLARES the length, not that the layout is unknown, and the
                    // way out (an array type on the parameter) is a different one.
                    None => Err(LeanReason::BufferLength),
                }
            }
            Eingebaut::Lenof(TypOderOrt::Typ(_)) => Err(LeanReason::BufferLength),
            _ => Err(LeanReason::Builtin),
        },
        // **`old(e)` is a NAME bound to the value of `e` in the entry state.** Only an
        // `ensures` has an entry state to read; the goal quantifies `old#i` over it.
        ExprArt::Alt(o) => match c.result_site {
            ResultSite::Bound => {
                let inner = place_term(o, c)?;
                let n = c.olds.len() + 1;
                c.olds.push(inner.into_term());
                Ok(LeanCarried::ExprOldState.term(format!("(.name \"old#{n}\")")))
            }
            ResultSite::Body | ResultSite::Contract | ResultSite::LoopRet => Err(LeanReason::OldState),
        },
        ExprArt::Ergebnis => match c.result_site {
            ResultSite::Body => Err(LeanReason::ResultInBody),
            ResultSite::Contract => Err(LeanReason::Result),
            ResultSite::Bound => {
                c.uses_result = true;
                Ok(LeanCarried::ExprResultName.term("(.name \"result\")"))
            }
            ResultSite::LoopRet => Ok(LeanCarried::ExprResultName.term("(.name \"#ret\")")),
        },
        // **A reason is a VALUE** (2026-09-07): `Buchfehler::Unbelegt` is `.reason "Unbelegt"`
        // -- the case's name, which is how a `match` arm spells it.
        ExprArt::Grund { fall, .. } => {
            Ok(LeanCarried::ExprLiteral.term(format!("(.lit (.reason {}))", quoted(&fall.text))))
        }
        ExprArt::FnWert(_) => Err(LeanReason::OtherValue),
        // **Lane 111:** a table literal has no term in this channel either --
        // the model has no array literal form.
        ExprArt::ArrayLit(_) => Err(LeanReason::OtherValue),
    }
}

/// **Does this predicate name the pass counter?** (agent b, 2026-09-08) A `traverse` gets
/// its counter emitted only when its `invariant` reads it -- see `LoopInfo::passes`.
fn pred_names_passes(p: &Pred) -> bool {
    let in_expr = |e: &Expr| {
        crate::alle_orte(e)
            .into_iter()
            .any(|o| o.basis.text == crate::PASSZAEHLER)
    };
    match &p.art {
        PredArt::Vergleich(e) => in_expr(e),
        PredArt::Element(e, _) => in_expr(e),
        PredArt::Klammer(q) | PredArt::Nicht(q) => pred_names_passes(q),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            pred_names_passes(a) || pred_names_passes(b)
        }
        PredArt::Quantor(q) => pred_names_passes(&q.rumpf),
        PredArt::Erreicht { von, nach, .. } => {
            von.basis.text == crate::PASSZAEHLER || nach.basis.text == crate::PASSZAEHLER
        }
        PredArt::Held { .. } => false,
    }
}

/// **Is the spelling `passes` free for the ghost here?** A local, a parameter, a constant,
/// a global, a type, a table or a `walk` of that name is a PROGRAM name, and a program name
/// wins: the invariant then says what it always said. *Coarse in the quiet direction* --
/// the same rule `D021` uses to decide whether a name resolves at all.
fn passes_is_free(c: &Ctx) -> bool {
    let n = crate::PASSZAEHLER;
    !c.is_local(n)
        && const_value(n, c).is_none()
        && c.unit.u.suche_global(&c.module, n).is_none()
        && !c.unit.u.nennt_typ_oder_konstante(&c.module, n)
        && c.unit.u.nennt_tabelle(&c.module, n).is_none()
        && !c.unit.u.nennt_walk(&c.module, n)
        && !c.unit.u.nennt_kopf(&c.module, n)
}

/// A predicate as a `Gabbro.Body.Expr` that must evaluate to `true`.
fn pred_term(p: &Pred, c: &mut Ctx) -> Result<Carried, LeanReason> {
    match &p.art {
        PredArt::Vergleich(e) => expr_term(e, c),
        PredArt::Klammer(q) => pred_term(q, c),
        PredArt::Nicht(q) => {
            Ok(LeanCarried::PredConnective.term(format!("(.un .not {})", pred_term(q, c)?)))
        }
        PredArt::Und(a, b) => Ok(LeanCarried::PredConnective.term(format!(
            "(.bin .and {} {})",
            pred_term(a, c)?,
            pred_term(b, c)?
        ))),
        PredArt::Oder(a, b) => Ok(LeanCarried::PredConnective.term(format!(
            "(.bin .or {} {})",
            pred_term(a, c)?,
            pred_term(b, c)?
        ))),
        PredArt::Folgt(a, b) => Ok(LeanCarried::PredConnective.term(format!(
            "(.bin .or (.un .not {}) {})",
            pred_term(a, c)?,
            pred_term(b, c)?
        ))),
        // **`Held(L)` in a contract is `true` here and it is not a weakening**: the lock
        // passes decide it for every call site (`H005`/`H006`/`H012`/`H016`), and a
        // precondition that this channel could not write would refuse the whole callee.
        PredArt::Held { .. } => match c.result_site {
            ResultSite::Body => Err(LeanReason::LockWitness),
            ResultSite::Contract | ResultSite::Bound | ResultSite::LoopRet => {
                Ok(LeanCarried::PredLockHeld.term("(.lit (.bool true))"))
            }
        },
        // **The bounded quantifier over the index domain** -- `forall s in slots of T : P`
        // is `forallSlots "s" N P`, with `N` the declared `count`. Every other domain is
        // refused by name.
        // **The quantifier over a domain.** Every domain this channel has is a SUBSET of
        // the index domain `0 ..< count` of one table, cut by a membership expression:
        // `slots of` is the whole of it; `descendants of T.slots[p]` the slots whose parent
        // chain reaches `p`; `ancestors of` the slots `p`'s chain reaches; `chain(h, n) in
        // T.slots[p]` the slots the `n`-chain from `p.h` reaches. So `forall x in D : P`
        // is `forallSlots x count (x ∈ D → P)` and `exists` is `existsSlots x count
        // (x ∈ D ∧ P)`. The five other domains have no term here.
        PredArt::Quantor(q) => {
            // **`fields of <format|record>` is a FINITE, statically known domain**
            // (2026-09-08), and the emitter knows the list: `forall f in fields of Wort : P`
            // is the conjunction of `P` over the declared fields, `exists` the disjunction.
            // Where the body does not read the binder -- the whole of the corpus's use of
            // this domain -- every conjunct is the same `P`, so the quantifier collapses to
            // `P` for a NON-EMPTY list, to `true`/`false` for an empty one. A body that DOES
            // read the binder is refused: a field NAME is not a value of this model, and a
            // conjunction over five copies of a term that mentions `f` would be five copies
            // of a name nothing binds.
            if let Some(n) = field_count(&q.domaene, c) {
                let depth = c.locals.len();
                c.push_local(&q.variable.text, Some(Shape::Int));
                let body = pred_term(&q.rumpf, c);
                c.locals.truncate(depth);
                let body = body?;
                if body.as_str().contains(&format!("(.name {})", quoted(&q.variable.text))) {
                    return Err(LeanReason::Quantified);
                }
                return Ok(LeanCarried::PredQuantFields.term(match (q.art, n) {
                    (QuantorArt::Alle, 0) => "(.lit (.bool true))".to_string(),
                    (QuantorArt::Existiert, 0) => "(.lit (.bool false))".to_string(),
                    _ => body.into_term(),
                }));
            }
            let (tab, member) = domain_of(&q.domaene, &q.variable.text, c)?;
            let count = c
                .unit
                .tables
                .get(&tab)
                .and_then(|t| t.count)
                .ok_or(LeanReason::Quantified)?;
            let depth = c.locals.len();
            c.push_local(&q.variable.text, Some(Shape::Int));
            let body = pred_term(&q.rumpf, c);
            c.locals.truncate(depth);
            let body = body?;
            let schnitt = member.as_str();
            let (word, cut) = match q.art {
                QuantorArt::Alle => (
                    "forallSlots",
                    if schnitt.is_empty() {
                        body.into_term()
                    } else {
                        format!("(.bin .or (.un .not {schnitt}) {body})")
                    },
                ),
                QuantorArt::Existiert => (
                    "existsSlots",
                    if schnitt.is_empty() {
                        body.into_term()
                    } else {
                        format!("(.bin .and {schnitt} {body})")
                    },
                ),
            };
            Ok(LeanCarried::PredQuantIndexDomain
                .term(format!("(.{word} {} {count} {cut})", quoted(&q.variable.text))))
        }
        // **`a reaches b via f`** -- the chain with the table's count as fuel.
        PredArt::Erreicht { von, nach, via } => {
            let (tab, from) = slot_index(von, c)?;
            let (tab2, to) = slot_index(nach, c)?;
            let tab = match (tab, tab2) {
                (Some(a), Some(b)) if a == b => a,
                (Some(a), None) | (None, Some(a)) => a,
                _ => return Err(LeanReason::Quantified),
            };
            let count = c
                .unit
                .tables
                .get(&tab)
                .and_then(|t| t.count)
                .ok_or(LeanReason::Quantified)?;
            c.note(&tab, &via.text, Shape::Opt, &format!("`{}` in `{tab}`", via.text));
            Ok(LeanCarried::PredReaches.term(format!(
                "(.reaches {} {from} {to} {} {count})",
                quoted(&tab),
                quoted(&via.text)
            )))
        }
        // `e in D` -- the membership itself, as an expression over the index `e`.
        PredArt::Element(e, d) => {
            let ExprArt::Ort(o) = &crate::ohne_klammern(e).art else {
                return Err(LeanReason::Quantified);
            };
            if !o.suffixe.is_empty() {
                return Err(LeanReason::Quantified);
            }
            let (tab, member) = domain_of(d, &o.basis.text, c)?;
            let count = c
                .unit
                .tables
                .get(&tab)
                .and_then(|t| t.count)
                .ok_or(LeanReason::Quantified)?;
            let x = place_term(o, c)?;
            let in_range = format!(
                "(.bin .and (.bin .ge {x} (.lit (.int 0))) (.bin .lt {x} (.lit (.int {count}))))"
            );
            let schnitt = member.as_str();
            Ok(LeanCarried::PredMembership.term(if schnitt.is_empty() {
                in_range
            } else {
                format!("(.bin .and {in_range} {schnitt})")
            }))
        }
    }
}

/// **A domain, as the table it lives in and the membership of the variable `x` in it** --
/// `None` for the whole index domain. The tree edges are read off the table's `tree`
/// clause; a domain over a table without one has no term.
fn domain_of(d: &Domaene, x: &str, c: &mut Ctx) -> Result<(String, Carried), LeanReason> {
    let xv = format!("(.name {})", quoted(x));
    match d {
        Domaene::SlotsVon(ort) => {
            if !ort.suffixe.is_empty() {
                return Err(LeanReason::Quantified);
            }
            let tab = c.table_of(&ort.basis.text).ok_or(LeanReason::Carrier)?.clone();
            Ok((tab, LeanCarried::DomainSlots.term("")))
        }
        Domaene::NachfahrenVon(ort) | Domaene::VorfahrenVon(ort) => {
            let (Some(tab), p) = slot_index(ort, c)? else {
                return Err(LeanReason::Quantified);
            };
            let info = c.unit.tables.get(&tab).ok_or(LeanReason::Carrier)?;
            let count = info.count.ok_or(LeanReason::Quantified)?;
            let elter = info.elter.clone().ok_or(LeanReason::Quantified)?;
            // strict: the slot itself is neither its own descendant nor its own ancestor
            let reach = match d {
                Domaene::NachfahrenVon(_) => {
                    format!("(.reaches {} {xv} {p} {} {count})", quoted(&tab), quoted(&elter))
                }
                _ => format!("(.reaches {} {p} {xv} {} {count})", quoted(&tab), quoted(&elter)),
            };
            c.note(&tab, &elter, Shape::Opt, &format!("`{elter}` in `{tab}`"));
            Ok((
                tab.clone(),
                LeanCarried::DomainReach.term(format!("(.bin .and (.bin .ne {xv} {p}) {reach})")),
            ))
        }
        Domaene::KetteIn { a, b, ort } => {
            let (Some(tab), p) = slot_index(ort, c)? else {
                return Err(LeanReason::Quantified);
            };
            let count = c.unit.tables.get(&tab).and_then(|t| t.count).ok_or(LeanReason::Quantified)?;
            let head = format!("(.place {} {p} {})", quoted(&tab), quoted(&a.text));
            c.note(&tab, &a.text, Shape::Opt, &format!("`{}` in `{tab}`", a.text));
            c.note(&tab, &b.text, Shape::Opt, &format!("`{}` in `{tab}`", b.text));
            Ok((
                tab.clone(),
                LeanCarried::DomainChain.term(format!(
                    "(.chainFrom {} {head} {xv} {} {count})",
                    quoted(&tab),
                    quoted(&b.text)
                )),
            ))
        }
        // **`elems of r.f` and `elems of buf` are the index domain of the array's
        // pseudo-table**; `queue r` is that of the ONE array of the record `r` (`K003`
        // makes one the rule). The binder is the index, as every use in the corpus reads it.
        Domaene::ElementeVon(ort) => {
            let tab = match &ort.suffixe[..] {
                [OrtSuffix::Feld(f)] => {
                    let rec = c.record_carrier.get(&ort.basis.text).ok_or(LeanReason::Quantified)?;
                    let arrays = c.unit.record_arrays.get(rec).ok_or(LeanReason::Quantified)?;
                    arrays.iter().find(|(n, _)| *n == f.text).map(|(_, t)| t.clone()).ok_or(LeanReason::Quantified)?
                }
                [] => {
                    let tab = c.carrier.get(&ort.basis.text).ok_or(LeanReason::Quantified)?.clone();
                    let info = c.unit.tables.get(&tab).ok_or(LeanReason::Quantified)?;
                    if info.fields.len() != 1 || info.fields[0].0 != "elem" {
                        return Err(LeanReason::Quantified);
                    }
                    tab
                }
                _ => return Err(LeanReason::Quantified),
            };
            Ok((tab, LeanCarried::DomainElems.term("")))
        }
        Domaene::Schlange(ort) => {
            // **`queue T.slots[i].f`** -- the queue in a slot field of record type: its
            // record's one array is the domain, as for a record carrier (2026-09-08)
            if let [OrtSuffix::Feld(slots), OrtSuffix::Index(_), OrtSuffix::Feld(f)] = &ort.suffixe[..] {
                if slots.text == "slots" {
                    let tab = c.table_of(&ort.basis.text).ok_or(LeanReason::Carrier)?.clone();
                    let rec = c.unit.field_records.get(&(tab, f.text.clone())).ok_or(LeanReason::Quantified)?;
                    let arrays = c.unit.record_arrays.get(rec).ok_or(LeanReason::Quantified)?;
                    if arrays.len() != 1 {
                        return Err(LeanReason::Quantified);
                    }
                    return Ok((arrays[0].1.clone(), LeanCarried::DomainQueue.term("")));
                }
            }
            if !ort.suffixe.is_empty() {
                return Err(LeanReason::Quantified);
            }
            let rec = c.record_carrier.get(&ort.basis.text).ok_or(LeanReason::Quantified)?;
            let arrays = c.unit.record_arrays.get(rec).ok_or(LeanReason::Quantified)?;
            if arrays.len() != 1 {
                return Err(LeanReason::Quantified);
            }
            Ok((arrays[0].1.clone(), LeanCarried::DomainQueue.term("")))
        }
        // **The three domains that are NOT an index range of a table, each by its own
        // name** (2026-09-08). `fields of` is served one level up (`PredArt::Quantor`),
        // where the field LIST is known and the quantifier collapses over it; the other two
        // have nothing to collapse over, and their reasons differ (`threads` lacks a
        // declaration, `mappings of` speaks about hardware).
        Domaene::FelderVon(_) => Err(LeanReason::Quantified),
        Domaene::Threads => Err(LeanReason::QuantifiedThreads),
        Domaene::AbbildungenVon(_) => Err(LeanReason::QuantifiedMappings),
    }
}

/// **How many fields a `fields of <path>` domain runs over.** A `format` and a record both
/// declare their field list statically, and that list is the whole domain. `None` when the
/// path names neither -- then there is nothing to run over.
fn field_count(d: &Domaene, c: &Ctx) -> Option<usize> {
    let Domaene::FelderVon(p) = d else { return None };
    let name = &p.teile.last()?.text;
    if let Some(fs) = c.unit.u.suche_formate(&c.module, name) {
        return Some(fs.len());
    }
    c.unit.records.get(name).map(|fs| fs.len())
}

/// **`Some(e)` and `None` are VALUES, not calls.**
fn is_option_value(r: &Ruf) -> bool {
    match r.path().and_then(|p| p.teile.last()).map(|i| i.text.as_str()) {
        Some("None") => r.argumente.is_empty(),
        Some("Some") => r.argumente.len() == 1,
        _ => false,
    }
}

/// **A value constructor -- `Some`, `None`, or a case of a `tagged type`.** These go to
/// `expr_term`, never to `call_parts`.
fn is_value_constructor(r: &Ruf, c: &Ctx) -> bool {
    if is_option_value(r) {
        return true;
    }
    r.path()
        .and_then(|p| p.teile.last())
        .is_some_and(|n| c.unit.variants.contains_key(&n.text))
}

/// **What a call path names**: a routine of this unit, a generated operation, a device
/// transition, a foreign routine -- or nothing this channel can call.
enum Callee<'a> {
    Routine(&'a RoutineInfo),
    Op(&'a OpInfo),
    Transition(&'a TransitionInfo),
    Foreign(&'a ForeignInfo),
}

fn resolve_callee<'a>(r: &Ruf, u: &'a Unit) -> Result<Callee<'a>, LeanReason> {
    if r.ist_verbundwert() {
        return Err(LeanReason::ConstructedValue);
    }
    let p = r.path().ok_or(LeanReason::CallStatement)?;
    let full: Vec<String> = p.teile.iter().map(|i| i.text.clone()).collect();
    let joined = full.join("::");
    let last = full.last().ok_or(LeanReason::CallStatement)?;
    if let Some(op) = u.ops.get(&joined) {
        return Ok(Callee::Op(op));
    }
    if u.devices.contains(last) {
        return Err(LeanReason::ConstructedValue);
    }
    if let Some(t) = u.transitions.get(last) {
        return Ok(Callee::Transition(t));
    }
    if let Some(f) = u.routines.get(last) {
        return Ok(Callee::Routine(f));
    }
    if let Some(f) = u.foreign.get(last) {
        return Ok(Callee::Foreign(f));
    }
    Err(LeanReason::CallStatement)
}

/// **Callee, parameter names, argument terms and the PRECONDITION of a call.** One place,
/// because three statement forms carry a call and each one writing its own lookup is three
/// chances for them to drift apart.
///
/// The precondition is the callee's `requires`, read from its declaration, as ONE
/// expression -- and it is complete or the call is refused (`CalleeContract`): it is the
/// stuck-condition of the call, and a dropped clause would make the caller's goal easier.
/// **Is this `Ruf` a CALL** -- a routine, an op, a transition, a foreign body -- and not a
/// value (`Some`, `None`, a case of a `tagged` type) or an inlined `spec fn`?
fn is_real_call(r: &Ruf, c: &Ctx) -> bool {
    if is_value_constructor(r, c) {
        return false;
    }
    let name = r.path().and_then(|p| p.teile.last()).map(|i| i.text.clone());
    !name.is_some_and(|n| c.unit.specs.contains_key(&n))
}

/// **The calls inside an expression, in evaluation order** -- left to right, the arguments
/// of a call before the call, and NOT under `&&`/`||`, because a call the short-circuit
/// would skip must not be hoisted in front of it.
fn calls_in<'a>(e: &'a Expr, c: &Ctx, out: &mut Vec<&'a Ruf>) {
    match &e.art {
        // the calls in the arguments run before the call itself
        ExprArt::Ruf(r) if is_real_call(r, c) => {
            for a in &r.argumente {
                calls_in(a, c, out);
            }
            out.push(r);
        }
        // **Lane E1:** the library call itself is no hoistable call, but the
        // calls in its arguments run before it like any call's.
        ExprArt::LibraryCall(r) => {
            for a in &r.args {
                calls_in(a, c, out);
            }
        }
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => calls_in(x, c, out),
        ExprArt::Binaer(BinOp::Und, _, _) | ExprArt::Binaer(BinOp::Oder, _, _) => {}
        ExprArt::Binaer(_, a, b) => {
            calls_in(a, c, out);
            calls_in(b, c, out);
        }
        _ => {}
    }
}

/// **An expression with its calls hoisted in front of it**: every call it contains (see
/// `calls_in`) becomes a `bindCall` into a local `#m<i>` written BEFORE the statement, and
/// the expression reads the local. `x = f(a) + 1` is `let #m1 = f(a); x = #m1 + 1` -- what
/// a person would write, and what the model, in which a call is a statement, can run.
/// Returns the prefix (statements, each followed by `, `) and the expression's term.
fn hoisted_expr(e: &Expr, c: &mut Ctx) -> Result<(String, String), LeanReason> {
    let mut calls = Vec::new();
    calls_in(e, c, &mut calls);
    let mut prefix = String::new();
    for r in calls {
        let (n, ps, args, pre) = call_parts(r, c)?;
        let sh = shape_of_call(r, c);
        c.hoists += 1;
        let tmp = format!("#m{}", c.hoists);
        c.push_local(&tmp, sh);
        prefix.push_str(&format!("(.bindCall {} {n} [{ps}] [{args}] {pre}), ", quoted(&tmp)));
        c.hoisted.insert(r as *const Ruf as usize, tmp);
    }
    let t = expr_term(e, c);
    c.hoisted.clear();
    Ok((prefix, t?.into_term()))
}

/// **A call statement whose arguments may call**: the calls in the arguments are hoisted
/// in front (`hoisted_expr`), then the call itself is read. Returns the prefix and the
/// parts of the call.
fn hoisted_call(r: &Ruf, c: &mut Ctx) -> Result<(String, (String, String, String, String)), LeanReason> {
    let mut calls = Vec::new();
    for a in &r.argumente {
        calls_in(a, c, &mut calls);
    }
    let mut prefix = String::new();
    for x in calls {
        let (n, ps, args, pre) = call_parts(x, c)?;
        let sh = shape_of_call(x, c);
        c.hoists += 1;
        let tmp = format!("#m{}", c.hoists);
        c.push_local(&tmp, sh);
        prefix.push_str(&format!("(.bindCall {} {n} [{ps}] [{args}] {pre}), ", quoted(&tmp)));
        c.hoisted.insert(x as *const Ruf as usize, tmp);
    }
    let parts = call_parts(r, c);
    c.hoisted.clear();
    Ok((prefix, parts?))
}

fn call_parts(r: &Ruf, c: &mut Ctx) -> Result<(String, String, String, String), LeanReason> {
    let name = r
        .path()
        .and_then(|p| p.teile.last())
        .map(|i| i.text.clone())
        .ok_or(LeanReason::CallStatement)?;
    if !c.allow_calls {
        return Err(LeanReason::CallInExpression);
    }
    let (key, params, pre): (String, Vec<String>, String) = match resolve_callee(r, c.unit)? {
        Callee::Routine(f) => (
            f.decl.name.text.clone(),
            f.params.iter().map(|(n, _)| n.clone()).collect(),
            match c.unit.pre_of.get(&f.decl.name.text) {
                Some(Ok(p)) => p.clone(),
                _ => return Err(LeanReason::CalleeContract),
            },
        ),
        Callee::Foreign(f) => (
            f.name.clone(),
            f.params.iter().map(|(n, _)| n.clone()).collect(),
            f.pre.clone().ok_or(LeanReason::CalleeContract)?,
        ),
        Callee::Op(op) => (
            op.key.clone(),
            op.params.clone(),
            op.pre.clone().ok_or(LeanReason::GeneratedOp)?,
        ),
        // A transition is called with the device handle -- `anschalten(d)` -- and that one
        // argument is what its C form takes as well (`VirtioPci_ack(VirtioPci *d)`).
        Callee::Transition(t) => (
            t.name.clone(),
            vec!["d".to_string()],
            t.pre.clone().ok_or(LeanReason::Transition)?,
        ),
    };
    if params.len() != r.argumente.len() {
        return Err(LeanReason::CallStatement);
    }
    let mut args = Vec::new();
    for a in &r.argumente {
        args.push(expr_term(a, c)?.into_term());
    }
    let _ = name;
    c.callees.insert(key.clone());
    let names: Vec<String> = params.iter().map(|n| quoted(n)).collect();
    Ok((quoted(&key), names.join(", "), args.join(", "), pre))
}

/// The payload of a `publishes`, as a list of place names.
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

/// **The shape a `let` gives its name** -- from the declared type where there is one, else
/// from the initialiser, and only where the answer is certain. `None` costs a hypothesis
/// (the loop invariant will not carry the name), never a false one.
/// **A `let` that binds a record VALUE opens a ghost carrier for its fields** (2026-09-08).
///
/// The name is dropped from the map first, so a `let` that rebinds it with something that
/// is NOT a record leaves no stale carrier behind, and one that rebinds it with another
/// record gets a NEW carrier -- *the two values of one name are two places, which is the
/// whole point.*
fn note_record_binding(l: &LetStmt, c: &mut Ctx) {
    let name = l.name.text.clone();
    c.record_value.remove(&name);
    let Some(rec) = record_of_init(l, c) else { return };
    c.record_binds += 1;
    let ghost = format!("{name}#r{}", c.record_binds);
    c.record_value.insert(name, (rec, ghost));
}

/// The RECORD a `let` binds a value of -- from the annotation where there is one, else from
/// the callee's declared result type. **A POINTER to a record is not one**: it is a place
/// the record already has a carrier for, and giving it a ghost would make a caller's
/// promise about `s.len` unreadable to it.
fn record_of_init(l: &LetStmt, c: &Ctx) -> Option<String> {
    if let Some(t) = &l.typ {
        if matches!(t, TypExpr::Zeiger(_)) {
            return None;
        }
        return points_at_record(t, &c.unit.records);
    }
    let ExprArt::Ruf(r) = &crate::ohne_klammern(&l.wert).art else {
        return None;
    };
    match resolve_callee(r, c.unit).ok()? {
        Callee::Routine(f) => {
            let t = f.decl.ergebnis.as_ref()?;
            if matches!(t, TypExpr::Zeiger(_)) {
                return None;
            }
            points_at_record(t, &c.unit.records)
        }
        _ => None,
    }
}

fn shape_of_init(l: &LetStmt, c: &Ctx) -> Option<Shape> {
    if let Some(t) = &l.typ {
        return shape_of(t, &c.unit.u, &c.module);
    }
    shape_of_expr(&l.wert, c)
}

fn shape_of_expr(e: &Expr, c: &Ctx) -> Option<Shape> {
    match &e.art {
        ExprArt::Zahl(_) => Some(Shape::Int),
        ExprArt::Wahr | ExprArt::Falsch => Some(Shape::Bool),
        ExprArt::Klammer(x) => shape_of_expr(x, c),
        ExprArt::Unaer(UnOp::Nicht, _) => Some(Shape::Bool),
        ExprArt::Unaer(UnOp::Negativ, _) => Some(Shape::Int),
        ExprArt::Unaer(UnOp::BitNicht, _) => None,
        ExprArt::Binaer(op, _, _) => match op {
            BinOp::Plus
            | BinOp::Minus
            | BinOp::Mal
            | BinOp::Geteilt
            | BinOp::Rest
            |             BinOp::BitUnd
            | BinOp::BitOder
            | BinOp::BitXor
            | BinOp::SchiebLinks
            | BinOp::SchiebRechts => Some(Shape::Int),
            // PLAN-BITS section 4 (lane 88): no shape, like `~` -- the value
            // is an integer, but no term of this channel can name the
            // operation, so no proof about it can be built here either.
            BinOp::PlusWrap
            | BinOp::MinusWrap
            | BinOp::MalWrap
            | BinOp::SchiebLinksWrap
            | BinOp::PlusSat => None,
            BinOp::Gleich
            | BinOp::Ungleich
            | BinOp::Kleiner
            | BinOp::KleinerGleich
            | BinOp::Groesser
            | BinOp::GroesserGleich
            | BinOp::Und
            | BinOp::Oder => Some(Shape::Bool),
        },
        ExprArt::Ruf(r) => shape_of_call(r, c),
        // **«SG-24»** -- a count IS an integer; its shape is one, and the TERM is
        // what the model refuses (`Counted` in `expr_term` above, never here).
        ExprArt::Zaehle { .. } => Some(Shape::Int),
        ExprArt::Ort(o) => {
            if o.suffixe.is_empty() {
                return c.locals.iter().rev().find(|(n, _)| *n == o.basis.text).and_then(|(_, s)| *s);
            }
            if let [OrtSuffix::Feld(f)] = &o.suffixe[..] {
                let rec = c
                    .record_value
                    .get(&o.basis.text)
                    .map(|(r, _)| r)
                    .or_else(|| c.record_carrier.get(&o.basis.text))?;
                return c.unit.records.get(rec)?.iter().find(|(n, _)| n == &f.text).and_then(|(_, s)| *s);
            }
            if let Some((tab, _)) = array_place(o, c) {
                return array_elem_shape(&tab, c).ok();
            }
            let [OrtSuffix::Feld(_), OrtSuffix::Index(_), OrtSuffix::Feld(f)] = &o.suffixe[..] else {
                return None;
            };
            let tab = c.table_of(&o.basis.text)?;
            c.unit.tables.get(tab)?.fields.iter().find(|(n, _)| n == &f.text).and_then(|(_, s)| *s)
        }
        ExprArt::Alt(_)
        | ExprArt::Ergebnis
        | ExprArt::Gleitkomma { .. }
        | ExprArt::Eingebaut(_)
        | ExprArt::FnWert(_)
        // **Lane E1:** a library call yields a value of no known shape.
        // **Lane 111:** a table literal yields one the channel cannot name
        // either -- the shape vocabulary has no array form.
        | ExprArt::LibraryCall(_)
        | ExprArt::ArrayLit(_)
        | ExprArt::Grund { .. } => None,
    }
}

/// The shape of what a `Ruf` yields -- a value constructor's, or the callee's result.
fn shape_of_call(r: &Ruf, c: &Ctx) -> Option<Shape> {
    if is_option_value(r) {
        return Some(Shape::Opt);
    }
    if let Some(n) = r.path().and_then(|p| p.teile.last()) {
        if let Some(sh) = c.unit.variant_sum.get(&n.text) {
            return Some(*sh);
        }
    }
    match resolve_callee(r, c.unit).ok()? {
        Callee::Routine(f) => c.unit.result_shape.get(&f.decl.name.text).copied().flatten(),
        Callee::Foreign(f) => f.result,
        Callee::Op(_) | Callee::Transition(_) => None,
    }
}

/// **What a routine's answer looks like**, as a clause over `r : Option Value`: a value of
/// the declared shape -- or, where the signature has an error channel (`-> T or R`), that
/// or a reason. A routine WITHOUT a result promises nothing about `r`. The clause is what
/// lets a caller's proof read the answer at all: `let x = f(a)` binds `x` to it.
fn result_clause(sh: Option<Shape>, range: Option<(i128, i128)>, fehler: bool, answers: bool, r: &str) -> Option<String> {
    let range = range.or(sh.and_then(Shape::range));
    let value = match sh {
        Some(Shape::Int) | Some(Shape::IntIn(..)) => match range {
            // the declared range of the answer -- what the checker holds at every use
            Some((lo, hi)) => format!("(∃ x, {r} = some (.int x) ∧ {} ≤ x ∧ x ≤ {})", int_lit(lo), int_lit(hi)),
            None => format!("(∃ x, {r} = some (.int x))"),
        },
        Some(Shape::Bool) => format!("(∃ b, {r} = some (.bool b))"),
        // one of the declared cases, with its payload
        Some(sh @ Shape::Sum(_)) => format!("(∃ t p, {r} = some (.tagged t p) ∧ Shape.caseOk {} t p = true)", sum_cases_lean(sh)),
        Some(Shape::Opt) => format!("({r} = some .absent ∨ ∃ x, {r} = some (.present x))"),
        // **an answer of a shape the model does not carry** (a token type, an opaque
        // handle): the routine still ANSWERS, and a caller that binds the answer needs
        // exactly that -- `let p1 = mmu_an(p)` is a `match` on `some v`, and without this
        // clause it stays stuck on the callee's word (2026-09-08, `22-bootstrecke`)
        None if answers => format!("(∃ v, {r} = some v)"),
        // no answer -- and with an error channel, no answer OR a reason
        None => {
            if fehler {
                return Some(format!("({r} = none ∨ ∃ e, {r} = some (.reason e))"));
            }
            return None;
        }
    };
    Some(if fehler {
        format!("({value} ∨ ∃ e, {r} = some (.reason e))")
    } else {
        value
    })
}

/// A payload as the model's term: `none`, `(some none)`, `(some (some (lo, hi)))`.
fn payload_lean(p: Payload) -> String {
    match p {
        None => "none".into(),
        Some(None) => "(some none)".into(),
        Some(Some((lo, hi))) => format!("(some (some ({}, {})))", int_lit(lo), int_lit(hi)),
    }
}

/// The case list of a sum shape, as a Lean list literal.
fn sum_cases_lean(sh: Shape) -> String {
    match sh {
        Shape::Sum(i) => {
            let all = sum_cases().lock().unwrap();
            let cases: Vec<String> = all[i as usize]
                .iter()
                .map(|(n, p)| format!("({}, {})", quoted(n), payload_lean(*p)))
                .collect();
            format!("[{}]", cases.join(", "))
        }
        _ => "[]".into(),
    }
}

/// A block as a `Gabbro.Body.Stmt` list term.
fn block_term(b: &Block, c: &mut Ctx) -> Result<Carried, LeanReason> {
    let depth = c.locals.len();
    let mut teile = Vec::new();
    for s in &b.anweisungen {
        teile.push(stmt_term(s, c)?.into_term());
    }
    // A `let` name leaves scope with its block -- the model binds by name, so a name that
    // outlived its block would silently shadow one further out.
    c.locals.truncate(depth);
    Ok(LeanCarried::StmtSequence.term(format!("[{}]", teile.join(", "))))
}

/// **Does this block, or one under it, `return`?** A loop body that may leave the ROUTINE is
/// refused (`ReturnInLoop`) -- see the reason.
fn returns(b: &Block) -> bool {
    b.anweisungen.iter().any(|s| {
        matches!(s.art, StmtArt::Return(_))
            || crate::unterbloecke(s).into_iter().any(returns)
    })
}

/// **The shapes of the locals in scope, as `hasShape` conjuncts.** This is what a loop
/// invariant is strengthened by: without it a local the body counts in would come out of
/// the pass unconstrained, and the next statement reading it would be stuck.
fn shaped_locals(locals: &[(String, Option<Shape>)]) -> Vec<(String, Shape)> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for (n, sh) in locals.iter().rev() {
        if !seen.insert(n.clone()) {
            continue;
        }
        if let Some(sh) = sh {
            out.push((n.clone(), *sh));
        }
    }
    out.reverse();
    out
}

/// **The shape of one local, as an expression** -- and for an integer with a declared
/// range, the range with it: `hasShape n int ∧ (lo ≤ n ∧ n ≤ hi)`, one conjunct.
fn shape_conjunct(n: &str, sh: Shape, ranges: &HashMap<String, (i128, i128)>) -> String {
    // **A ranged local is typed by `.intIn lo hi`** -- a parameter by the range the
    // emitter names for it, a `let` by the range of its declared type. The invariant of a
    // loop then carries the range of every local in scope, and the pass owes it back:
    // that is the arithmetic the checker decided (`M1`) and the model decides again,
    // over the ranges of the operands it now has (fields, payloads, answers). Without it
    // an answer computed in a loop could not meet its own declared range (2026-09-08).
    let sh = match (sh, ranges.get(n)) {
        (Shape::Int | Shape::IntIn(..), Some((lo, hi))) => Shape::IntIn(*lo, *hi),
        _ => sh,
    };
    format!("(.hasShape {} {})", quoted(n), sh.lean())
}

/// An integer literal as a Lean term -- a negative one in parentheses, because `.int -1`
/// does not parse.
fn int_lit(v: i128) -> String {
    if v < 0 {
        format!("({v})")
    } else {
        v.to_string()
    }
}

fn shape_conjuncts(locals: &[(String, Option<Shape>)], ranges: &HashMap<String, (i128, i128)>) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    // The LAST binding of a name is the one in scope.
    for (n, sh) in locals.iter().rev() {
        if !seen.insert(n.clone()) {
            continue;
        }
        if let Some(sh) = sh {
            out.push(shape_conjunct(n, *sh, ranges));
        }
    }
    out.reverse();
    out
}

fn conj(terms: &[String]) -> String {
    match terms.len() {
        0 => "(.lit (.bool true))".to_string(),
        1 => terms[0].clone(),
        _ => {
            let mut acc = terms[terms.len() - 1].clone();
            for t in terms[..terms.len() - 1].iter().rev() {
                acc = format!("(.bin .and {t} {acc})");
            }
            acc
        }
    }
}

fn stmt_term(s: &Stmt, c: &mut Ctx) -> Result<Carried, LeanReason> {
    match &s.art {
        StmtArt::Let(l) => {
            // **`let n = f(a);` is a CALL, not an expression.** A callee may write, so an
            // expression carrying one would no longer be pure. `Some(e)` is a VALUE.
            if let ExprArt::Ruf(r) = &crate::ohne_klammern(&l.wert).art {
                if !is_value_constructor(r, c) {
                    let (hoist, (n, ps, args, pre)) = hoisted_call(r, c)?;
                    let sh = shape_of_init(l, c);
                    c.push_local(&l.name.text, sh);
                    note_record_binding(l, c);
                    return Ok(LeanCarried::StmtBindCall.term(format!(
                        "{hoist}(.bindCall {} {n} [{ps}] [{args}] {pre})",
                        quoted(&l.name.text)
                    )));
                }
            }
            let (hoist, w) = hoisted_expr(&l.wert, c)?;
            let sh = shape_of_init(l, c);
            c.push_local(&l.name.text, sh);
            note_record_binding(l, c);
            Ok(LeanCarried::StmtBindName.term(format!(
                "{hoist}(.bindName {} {})",
                quoted(&l.name.text),
                w
            )))
        }
        StmtArt::Zuweisung(z) => {
            let mischung = |op: ZuwOp, shape: Shape| -> Option<&'static str> {
                match (op, shape) {
                    (ZuwOp::Plus, Shape::Int | Shape::IntIn(..)) => Some("add"),
                    (ZuwOp::Minus, Shape::Int | Shape::IntIn(..)) => Some("sub"),
                    (ZuwOp::Und, Shape::Bool) => Some("and"),
                    (ZuwOp::Oder, Shape::Bool) => Some("or"),
                    (ZuwOp::Und, Shape::Int | Shape::IntIn(..)) => Some("band"),
                    (ZuwOp::Oder, Shape::Int | Shape::IntIn(..)) => Some("bor"),
                    _ => None,
                }
            };
            let (hoist, w) = hoisted_expr(&z.wert, c)?;
            if z.ziel.suffixe.is_empty() {
                // **`n = e;` at a LOCAL rebinds the name; it does not store into the world.**
                let ist_lokal = c.is_local(&z.ziel.basis.text);
                let ziel = quoted(&z.ziel.basis.text);
                if z.op == ZuwOp::Setzt {
                    return Ok(if ist_lokal {
                        LeanCarried::StmtAssignLocal.term(format!("{hoist}(.bindName {ziel} {w})"))
                    } else {
                        LeanCarried::StmtAssignGlobal
                            .term(format!("{hoist}(.assignGlobal {ziel} {w})"))
                    });
                }
                if !ist_lokal {
                    return Err(LeanReason::CompoundAssign);
                }
                let op = match z.op {
                    ZuwOp::Plus => "add",
                    ZuwOp::Minus => "sub",
                    _ => return Err(LeanReason::CompoundAssign),
                };
                return Ok(LeanCarried::StmtCompoundAssignLocal.term(format!(
                    "{hoist}(.bindName {ziel} (.bin .{op} (.name {ziel}) {w}))"
                )));
            }
            // a store into a register is the device's business (see `place_term`)
            if c.device_carrier.contains(&z.ziel.basis.text) {
                return Err(LeanReason::DevicePromise);
            }
            if let [OrtSuffix::Feld(f)] = &z.ziel.suffixe[..] {
                let (base, shape) = record_field(&z.ziel.basis.text, &f.text, c)?;
                c.note_record(&base, &f.text, shape);
                if z.op != ZuwOp::Setzt {
                    let Some(op) = mischung(z.op, shape) else {
                        return Err(LeanReason::CompoundAssign);
                    };
                    return Ok(LeanCarried::StmtStoreRecordField.term(format!(
                        "{hoist}(.assignField {} {} (.bin .{op} (.fieldOf {} {}) {}))",
                        quoted(&base),
                        quoted(&f.text),
                        quoted(&base),
                        quoted(&f.text),
                        w
                    )));
                }
                return Ok(LeanCarried::StmtStoreRecordField.term(format!(
                    "{hoist}(.assignField {} {} {})",
                    quoted(&base),
                    quoted(&f.text),
                    w
                )));
            }
            if let Some((tab, i)) = array_place(&z.ziel, c) {
                let shape = array_elem_shape(&tab, c)?;
                let idx = expr_term(i, c)?;
                let w = if z.op == ZuwOp::Setzt {
                    w
                } else {
                    let Some(op) = mischung(z.op, shape) else {
                        return Err(LeanReason::CompoundAssign);
                    };
                    format!("(.bin .{op} (.place {} {idx} \"elem\") {w})", quoted(&tab))
                };
                c.note(&tab, "elem", shape, &format!("element of `{tab}`"));
                return Ok(LeanCarried::StmtStoreArrayElement.term(format!(
                    "{hoist}(.assign {} {idx} \"elem\" {w})",
                    quoted(&tab)
                )));
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
            let carrier = place_carrier(&base, &tab);
            let idx = expr_term(i, c)?;
            let w = if z.op == ZuwOp::Setzt {
                w
            } else {
                let Some(op) = mischung(z.op, shape) else {
                    return Err(LeanReason::CompoundAssign);
                };
                format!(
                    "(.bin .{op} (.place {} {} {}) {})",
                    quoted(&carrier),
                    idx,
                    quoted(&f.text),
                    w
                )
            };
            // **A store into a `wrapping` field is reduced to the field's width.**
            let w = match c.unit.tables.get(&tab).and_then(|t| t.wraps.get(&f.text)) {
                Some((bits, signed)) => format!("(.wrapTo {bits} {signed} {w})"),
                None => w,
            };
            c.note(&carrier, &f.text, shape, &format!("`{}` in `{}`", f.text, tab));
            Ok(LeanCarried::StmtStoreSlotField.term(format!(
                "{hoist}(.assign {} {} {} {})",
                quoted(&carrier),
                idx,
                quoted(&f.text),
                w
            )))
        }
        StmtArt::Wenn(w) => {
            let mut otherwise = match &w.sonst {
                Some(b) => block_term(b, c)?.into_term(),
                None => "[]".to_string(),
            };
            for (bed, blk) in w.zweige.iter().rev() {
                // a call in the condition is hoisted in front of ITS `ite` -- inside the
                // `else` of the branch before it, so that it runs exactly when the
                // condition would have been evaluated
                let (hoist, b) = hoisted_expr(bed, c)?;
                let d = block_term(blk, c)?.into_term();
                otherwise = format!("[{hoist}(.ite {b} {d} {otherwise})]");
            }
            Ok(LeanCarried::StmtConditional.term(
                otherwise
                    .strip_prefix('[')
                    .and_then(|s| s.strip_suffix(']'))
                    .unwrap_or(&otherwise)
                    .to_string(),
            ))
        }
        StmtArt::Match(m) => {
            // **`match f(a) { … }` is a CALL followed by a `match`** -- the result goes into
            // a local of its own (`#m1`), and the arms read that local. A call is a
            // statement in the model, never an expression; the hoist is what a person
            // would write by hand, and it changes nothing the arms can observe.
            let (hoist, g) = hoisted_expr(&m.gegenstand, c)?;
            // **A `match` whose arms are bare case names is a `match` over a REASON.** The
            // enumeration is closed (`M123`), so the datum needs no catch-all: a reason no
            // arm names gets the model stuck.
            if m.zweige.iter().all(|z| c.unit.variants.contains_key(&z.variante.text)) {
                // **A `match` over a `tagged` value**: the arm by the case's name, the
                // payload bound to the binder where the arm names one.
                let mut arms = Vec::new();
                for z in &m.zweige {
                    let depth = c.locals.len();
                    let binder = match &z.binder {
                        Some(b) => {
                            c.push_local(&b.text, Some(Shape::Int));
                            format!("some {}", quoted(&b.text))
                        }
                        None => "none".to_string(),
                    };
                    let blk = block_term(&z.rumpf, c);
                    c.locals.truncate(depth);
                    arms.push(format!("({}, {binder}, {})", quoted(&z.variante.text), blk?));
                }
                return Ok(LeanCarried::StmtTaggedMatch
                    .term(format!("{hoist}(.onTag {g} [{}])", arms.join(", "))));
            }
            if m.zweige.iter().all(|z| z.binder.is_none() && z.variante.text != "None") {
                let mut arms = Vec::new();
                for z in &m.zweige {
                    arms.push(format!("({}, {})", quoted(&z.variante.text), block_term(&z.rumpf, c)?));
                }
                return Ok(LeanCarried::StmtReasonMatch
                    .term(format!("{hoist}(.onReason {g} [{}])", arms.join(", "))));
            }
            let mut onp = None;
            let mut ona = None;
            for z in &m.zweige {
                match (z.variante.text.as_str(), &z.binder) {
                    ("Some", Some(b)) => {
                        let depth = c.locals.len();
                        c.push_local(&b.text, Some(Shape::Int));
                        let blk = block_term(&z.rumpf, c)?;
                        c.locals.truncate(depth);
                        onp = Some((b.text.clone(), blk));
                    }
                    ("None", None) => ona = Some(block_term(&z.rumpf, c)?),
                    _ => return Err(LeanReason::MatchNotOption),
                }
            }
            match (onp, ona) {
                (Some((b, present)), Some(absent)) => Ok(LeanCarried::StmtOptionMatch.term(format!(
                    "{hoist}(.onOption {g} {} {present} {absent})",
                    quoted(&b)
                ))),
                _ => Err(LeanReason::MatchNotOption),
            }
        }
        // **`return` inside a loop is DESUGARED** (2026-09-07): the value goes into the
        // local `#ret`, the flag `#returned` is raised, and the pass ends (`.exit`). After
        // the loop the flag is tested and the routine returns -- or, one loop further out,
        // exits again. The loop's invariant carries the routine's `ensures` on the flagged
        // path (`ret_post`), so the theorem after the loop has what it needs. *A `return`
        // the loop's environment cannot carry becomes two locals it can.*
        StmtArt::Return(None) => {
            if !c.loop_stack.is_empty() {
                if c.ret_post.is_none() {
                    return Err(LeanReason::ReturnInLoop);
                }
                return Ok(LeanCarried::StmtReturnInLoop.term(
                    "(.bindName \"#ret\" (.lit .absent)), (.bindName \"#returned\" (.lit (.bool true))), .leave",
                ));
            }
            Ok(LeanCarried::StmtReturnNothing.term("(.ret none)"))
        }
        StmtArt::Return(Some(e)) => {
            if !c.loop_stack.is_empty() {
                if c.ret_post.is_none() {
                    return Err(LeanReason::ReturnInLoop);
                }
                if let ExprArt::Ruf(r) = &crate::ohne_klammern(e).art {
                    if !is_value_constructor(r, c) {
                        let (hoist, (n, ps, args, pre)) = hoisted_call(r, c)?;
                        return Ok(LeanCarried::StmtReturnInLoop.term(format!(
                            "{hoist}(.bindCall \"#ret\" {n} [{ps}] [{args}] {pre}), (.bindName \"#returned\" (.lit (.bool true))), .leave"
                        )));
                    }
                }
                let (hoist, v) = hoisted_expr(e, c)?;
                return Ok(LeanCarried::StmtReturnInLoop.term(format!(
                    "{hoist}(.bindName \"#ret\" {v}), (.bindName \"#returned\" (.lit (.bool true))), .leave"
                )));
            }
            if let ExprArt::Ruf(r) = &crate::ohne_klammern(e).art {
                if !is_value_constructor(r, c) {
                    let (hoist, (n, ps, args, pre)) = hoisted_call(r, c)?;
                    return Ok(LeanCarried::StmtReturnCall
                        .term(format!("{hoist}(.retCall {n} [{ps}] [{args}] {pre})")));
                }
            }
            let (hoist, v) = hoisted_expr(e, c)?;
            Ok(LeanCarried::StmtReturnValue.term(format!("{hoist}(.ret (some {v}))")))
        }
        StmtArt::Ruf(r) => {
            let (hoist, (n, ps, args, pre)) = hoisted_call(r, c)?;
            Ok(LeanCarried::StmtCall.term(format!("{hoist}(.call {n} [{ps}] [{args}] {pre})")))
        }
        // **Lane E2:** a library call lowers to no term -- refused like
        // any call the unit does not declare (checker: `N057`/`N069`).
        StmtArt::LibraryCall(_) => Err(LeanReason::CallStatement),
        // **«E4»:** the monotone arena has no term in this channel -- the
        // generations live in `grammatik/Grammatik/Arena.lean`, not in the
        // program-logic body model, so both statements lower to no term.
        StmtArt::Alloc(_) | StmtArt::ResetArena(_) => Err(LeanReason::Expression),
        // **`let n = f(a) else (e) { … }` is the error propagation** (2026-09-07): the
        // callee answers with a reason instead of a value, the `else` block runs with it
        // bound to `e`, and ends. The `place` form (`let n = A else …`, unpacking an atomic)
        // stays refused.
        StmtArt::LetSonst(l) => {
            let Some(r) = l.als_ruf() else {
                return Err(LeanReason::ErrorPropagation);
            };
            let (hoist, (n, ps, args, pre)) = hoisted_call(r, c)?;
            let depth = c.locals.len();
            c.push_local(&l.fehlername.text, None);
            let sonst = block_term(&l.sonst, c);
            c.locals.truncate(depth);
            let sonst = sonst?;
            c.push_local(&l.name.text, None);
            Ok(LeanCarried::StmtCallWithErrorExit.term(format!(
                "{hoist}(.bindCallElse {} {n} [{ps}] [{args}] {pre} {} {sonst})",
                quoted(&l.name.text),
                quoted(&l.fehlername.text)
            )))
        }
        StmtArt::Schleife(sch) => {
            let (inv, rumpf, marke, var) = match sch.as_ref() {
                Schleife::Traverse(x) => {
                    (&x.invariante, &x.rumpf, None, Some(x.variable.text.clone()))
                }
                Schleife::Retry(x) => (&x.invariante, &x.rumpf, x.marke.clone(), None),
                Schleife::Forever(x) => (&x.invariante, &x.rumpf, x.marke.clone(), None),
            };
            // **The number of passes** -- the domain's `count`, for a `traverse` over a
            // domain inside one table. It bounds how OFTEN the body runs (`by unvisited`
            // visits each slot at most once), where `range` bounds only the INDEX.
            let passes_bound = match sch.as_ref() {
                Schleife::Traverse(x) => domain_of(&x.domaene, &x.variable.text, c)
                    .ok()
                    .and_then(|(tab, _)| c.unit.tables.get(&tab)?.count),
                _ => None,
            };
            // the range of the index: every domain inside a table visits its slots
            let range = match sch.as_ref() {
                Schleife::Traverse(x) => domain_of(&x.domaene, &x.variable.text, c).ok().and_then(|(tab, _)| {
                    let info = c.unit.tables.get(&tab)?;
                    let count = info.count?;
                    // **over an array (`elems of`, `queue`) the binder may be read as the
                    // element**, and the element's declared range is then its range too:
                    // the bound that covers both readings (2026-09-08)
                    let elem = matches!(x.domaene, Domaene::ElementeVon(_) | Domaene::Schlange(_))
                        .then(|| info.fields.iter().find(|(n, _)| n == "elem").and_then(|(_, sh)| sh.and_then(Shape::range)))
                        .flatten();
                    Some(match elem {
                        Some((lo, hi)) => (lo.min(0), (hi + 1).max(count)),
                        None => (0i128, count),
                    })
                }),
                _ => None,
            };
            let may_return = returns(rumpf);
            if may_return && c.ret_post.is_none() {
                return Err(LeanReason::ReturnInLoop);
            }
            // The flag and the slot for a `return` inside: bound BEFORE the loop, so that
            // the invariant's shape conjuncts carry them and the test after the loop reads
            // a bound name.
            // **The pass counter is emitted only where the invariant NAMES it** (agent b,
            // 2026-09-08). Every other loop keeps the datum it had -- a convenience nobody
            // asked for should not move a single generated line.
            let counts_passes = inv.as_ref().is_some_and(|p| pred_names_passes(p))
                && passes_is_free(c)
                && range.is_some()
                && passes_bound.is_some();
            let mut prefix = String::new();
            if may_return {
                // **F2 (S4): `#ret` is bound ONCE, with the routine's declared answer
                // shape (`ret_init`) -- not `absent`/`None`.** A `return` inside rebinds
                // `#ret` to the answer further down, and `binde` keeps a name only under
                // the SAME shape (`Anweisung.lean:102`, U3) -- entry-absent against an
                // answer-valued rebinding was a refusal by construction. The per-return
                // rebindings are untouched (they carry the value); only this one binding
                // moves, and with it the invariant's `hasShape` conjunct for `#ret`.
                let (ret_term, ret_shape) = ret_init(c);
                prefix.push_str(&format!(
                    "(.bindName \"#returned\" (.lit (.bool false))), (.bindName \"#ret\" {ret_term}), "
                ));
                c.push_local("#returned", Some(Shape::Bool));
                c.push_local("#ret", ret_shape);
            }
            // **A loop without an `invariant` has the invariant `true`** (2026-09-07). Until
            // today it was refused -- *"a loop datum with no statement about it would let a
            // proof conclude from a loop exactly nothing"* -- and that sentence is right
            // about what follows the loop and wrong about the refusal: concluding NOTHING
            // from a loop is the sound reading of a loop nobody wrote a statement for, and
            // it is what the rest of the body then has to live with. What is still carried
            // are the shapes of the locals in scope, so the statement after the loop can
            // read them at all.
            //
            // **The invariant is read in the scope OUTSIDE the loop**, and strengthened by
            // the shapes of every local in that scope: those are the names the body may read
            // and rebind, and the rule has to carry their shapes across the pass.
            //
            // The loop variable shadows a parameter of the same name -- and a parameter's
            // declared range does not hold of an index the loop binds to that name.
            if let Some(v) = &var {
                c.ranges.remove(v);
            }
            // **The counter, bound to zero right before the loop.** It is a local of the
            // scope the invariant is read in, so the shape conjuncts carry it and the
            // rule's third premise (`LoopRuleP`) reads it off this very `bindName`.
            if counts_passes {
                prefix.push_str(&format!(
                    "(.bindName {} (.lit (.int 0))), ",
                    quoted(crate::PASSZAEHLER_LEAN)
                ));
                c.push_local(crate::PASSZAEHLER_LEAN, Some(Shape::Int));
            }
            let shapes = shaped_locals(&c.locals);
            // S4: the scope at this loop's entry, for the seam witness (see the field).
            let entry_locals = c.locals.clone();
            let mut parts = shape_conjuncts(&c.locals, &c.ranges);
            // The invariants the routine keeps hold at every pass: a call inside the loop
            // asks for them, and the routine's promise asks for them at the end.
            parts.extend(c.kept.iter().cloned());
            let core = match inv {
                Some(inv) => Some(pred_term(inv, c)?.into_term()),
                None => None,
            };
            // On the flagged path the routine's promise holds instead of the invariant.
            if may_return {
                let inv_only = core.clone().unwrap_or_else(|| "(.lit (.bool true))".into());
                let ret_post = c.ret_post.clone().unwrap_or_else(|| "(.lit (.bool true))".into());
                parts.push(format!(
                    "(.bin .or (.bin .and (.name \"#returned\") {ret_post}) (.bin .and (.un .not (.name \"#returned\")) {inv_only}))"
                ));
            } else if let Some(core) = core {
                parts.push(core);
            }
            let inv_term = conj(&parts);
            c.loops += 1;
            let id = format!("{}#{}", c.routine, c.loops);
            let depth = c.locals.len();
            let var_name = match &var {
                Some(v) => {
                    c.push_local(v, Some(Shape::Int));
                    v.clone()
                }
                None => "#pass".to_string(),
            };
            // The body's own callees and nested loops are collected apart from the
            // routine's, because the loop's theorem carries them as its own hypotheses.
            let outer_callees = std::mem::take(&mut c.callees);
            let outer_loops = std::mem::take(&mut c.loop_infos);
            let reads_before = c.option_reads.len();
            c.loop_stack.push(marke.map(|m| m.text));
            let body = block_term(rumpf, c);
            c.loop_stack.pop();
            c.locals.truncate(depth);
            let inner_callees = std::mem::replace(&mut c.callees, outer_callees);
            let inner_loops = std::mem::replace(&mut c.loop_infos, outer_loops);
            let body = body?.into_term();
            // **A pass that starts with the return flag set leaves at once** (agent b,
            // 2026-09-08). `return e` inside a loop is `#returned = true; #ret = e; leave`,
            // so in the RUN no pass follows one that returned -- but `LoopRule` quantifies
            // over every state the invariant admits, including one with the flag set, and
            // there the invariant is only the routine's promise: the person's own conjunct
            // is gone and a store in the body cannot meet its range. The guard makes that
            // pass do what the run does, which is nothing.
            //
            // **It is written only where the loop COUNTS its passes**, and that restriction
            // is measured and not tidiness: the guard is one more `ite` for `gabbro_cases`
            // to split, and over the whole corpus it closed `probe-elems` and opened
            // `beispiele/39-auftragsdienst` (net zero, run of 2026-09-08). Where nobody
            // writes `passes`, no conjunct of the person's is dropped by this branch in the
            // first place, so the guard buys nothing there and costs a split.
            let body = if may_return && counts_passes {
                format!(
                    "[(.ite (.name \"#returned\") [.leave] []){}{}",
                    if body == "[]" { "" } else { ", " },
                    &body[1..]
                )
            } else {
                body
            };
            // **The increment is the pass's FIRST statement**, so that a `next` or a
            // `leave` in the middle of the body cannot skip it.
            let body = if counts_passes {
                format!(
                    "[(.bindName {p} (.bin .add (.name {p}) (.lit (.int 1)))){}{}",
                    if body == "[]" { "" } else { ", " },
                    &body[1..],
                    p = quoted(crate::PASSZAEHLER_LEAN)
                )
            } else {
                body
            };
            c.callees.extend(inner_callees.iter().cloned());
            let nested: Vec<String> = inner_loops.iter().map(|l| l.id.clone()).collect();
            c.loop_infos.extend(inner_loops);
            let reads: Vec<(String, String, String, Shape)> = c.option_reads[reads_before..].to_vec();
            c.loop_infos.push(LoopInfo {
                id: id.clone(),
                inv: inv_term.clone(),
                var: var_name,
                body: body.clone(),
                callees: inner_callees,
                nested,
                shapes,
                parts: parts.len(),
                reads,
                ranges: c.ranges.clone(),
                records: c.seen_records.clone(),
                range,
                passes: if counts_passes { passes_bound } else { None },
                entry_locals,
            });
            let after = if !may_return {
                String::new()
            } else if !c.loop_stack.is_empty() {
                ", (.ite (.name \"#returned\") [.leave] [])".to_string()
            } else if c.has_result {
                ", (.ite (.name \"#returned\") [(.ret (some (.name \"#ret\")))] [])".to_string()
            } else {
                ", (.ite (.name \"#returned\") [(.ret none)] [])".to_string()
            };
            Ok(LeanCarried::StmtLoop
                .term(format!("{prefix}(.loop {} {inv_term} {body}){after}", quoted(&id))))
        }
        // **`narrow x to lo .. hi else { … }` is a conditional** (2026-09-07): the value stays
        // what it is, the type of the name gets narrower (`M1`'s business), and the `else`
        // block runs where the value is outside the range -- and ends, because `M1` demands
        // it. So the datum is an `ite` with an empty then-branch.
        StmtArt::Narrow(n) => {
            let NarrowZiel::Bereich(b) = &n.ziel else {
                return Err(LeanReason::Narrowing);
            };
            let x = place_term(&n.ort, c)?;
            let lo = expr_term(&b.von, c)?;
            let hi = expr_term(&b.bis, c)?;
            let upper = if b.exklusiv { "lt" } else { "le" };
            let sonst = block_term(&n.sonst, c)?;
            Ok(LeanCarried::StmtNarrowRange.term(format!(
                "(.ite (.bin .and (.bin .ge {x} {lo}) (.bin .{upper} {x} {hi})) [] {sonst})"
            )))
        }
        StmtArt::Bricht(b) => {
            let namen: Vec<String> = b.invarianten.iter().map(|i| quoted(&i.text)).collect();
            Ok(LeanCarried::StmtInvariantSuspension.term(format!(
                "(.breaking [{}] {})",
                namen.join(", "),
                block_term(&b.rumpf, c)?
            )))
        }
        // **`leave m;`/`next m;` end the pass of the INNERMOST loop** -- `Stmt.exit`. A mark
        // that names an outer one is refused: it would have to travel through a `.loop`
        // step that does not run the body.
        StmtArt::Leave(m) | StmtArt::Next(m) => {
            let word = if matches!(s.art, StmtArt::Leave(_)) { ".leave" } else { ".exit" };
            match c.loop_stack.last() {
                Some(Some(inner)) if *inner == m.text => Ok(LeanCarried::StmtLoopExit.term(word)),
                Some(None) => Ok(LeanCarried::StmtLoopExit.term(word)),
                _ => Err(LeanReason::NonLocalExit),
            }
        }
        StmtArt::Publish(pb) => {
            if !pb.ziel.suffixe.is_empty() {
                return Err(LeanReason::Publish);
            }
            let w = expr_term(&pb.wert, c)?;
            Ok(LeanCarried::StmtPublish.term(format!(
                "(.publish {} {w} [{}])",
                quoted(&pb.ziel.basis.text),
                nutzlast(&pb.nutzlast)
            )))
        }
        StmtArt::AwaitLoad(a) => {
            if !a.quelle.suffixe.is_empty() {
                return Err(LeanReason::Await);
            }
            let payload: Vec<String> = a.erwartet.iter().map(|o| quoted(&o.text())).collect();
            c.push_local(&a.name.text, None);
            Ok(LeanCarried::StmtAwait.term(format!(
                "(.awaitLoad {} {} [{}])",
                quoted(&a.name.text),
                quoted(&a.quelle.basis.text),
                payload.join(", ")
            )))
        }
        StmtArt::Exchange(_) => Err(LeanReason::Exchange),
        StmtArt::Observiert(_) => Err(LeanReason::Observe),
        StmtArt::Sperrt(l) => Ok(LeanCarried::StmtCriticalSection.term(format!(
            "(.locked {} {})",
            quoted(&l.sperre.basis.text),
            block_term(&l.rumpf, c)?
        ))),
    }
}

// ===========================================================================================
// THE UNIT -- everything read from DECLARATIONS, once per program.
// ===========================================================================================

/// A generated table operation, as a callee.
#[derive(Clone)]
pub struct OpInfo {
    pub key: String,
    pub table: String,
    pub params: Vec<String>,
    /// The premises `opsruf::koepfe` cuts, as one expression -- or `None` where one of them
    /// names a root the table's invariants do not name.
    pub pre: Option<String>,
}

/// A device transition, as a callee: a register write behind a frame.
#[derive(Clone)]
pub struct TransitionInfo {
    pub name: String,
    pub device: String,
    /// The `requires` as an expression -- `None` where it has no term (a register name is a
    /// place this model does not have), and then the call is refused.
    pub pre: Option<String>,
}

/// A routine without a body -- `extern fn`, or a declaration whose body is elsewhere.
#[derive(Clone)]
pub struct ForeignInfo {
    pub name: String,
    pub params: Vec<(String, Option<Shape>)>,
    pub result: Option<Shape>,
    /// `-> T or R`: the answer may be a reason.
    pub fehler: bool,
    /// The declared range of an integer answer.
    pub result_range: Option<(i128, i128)>,
    /// `-> never`: the routine does not return.
    pub never: bool,
    /// The routine declares an answer (of whatever shape).
    pub has_result: bool,
    pub pre: Option<String>,
    /// The `ensures` this channel can say, as the `post` of an ASSUMED contract.
    pub post: Vec<String>,
    pub writes: Vec<String>,
}

/// A `table`/`group` invariant, as this channel reads it.
#[derive(Clone)]
pub struct InvariantInfo {
    pub name: String,
    /// The carriers it speaks about -- one for a table, several for a group.
    pub carriers: Vec<String>,
    /// The `Expr` term, or the reason there is none.
    pub term: Result<String, LeanReason>,
    /// Whether some `maintains` names it; if not, every writer of a carrier owes it.
    pub maintained_by_name: bool,
    /// Whether the carrier is a `table … ops` -- then the template carries it.
    pub under_ops: bool,
}

pub struct Unit {
    pub u: crate::umgebung::Umgebung,
    pub tables: HashMap<String, TableInfo>,
    pub records: HashMap<String, Vec<(String, Option<Shape>)>>,
    /// **An array field is a table of its own** -- `plaetze : [AuftragNr; N]` inside
    /// `Ring` is the pseudo-table `Ring.plaetze` with the one field `elem` and `count N`,
    /// so that `r.plaetze[j]` is the place `.slot "Ring.plaetze" j "elem"` and `forall j in
    /// elems of r.plaetze` a `forallSlots` over it. Record name -> `(field, pseudo-table)`.
    /// A static array `buf : [u8; N]` is the pseudo-table `buf` the same way.
    pub record_arrays: HashMap<String, Vec<(String, String)>>,
    /// `(table, slot field) -> record`: a slot field of a record type -- `wartende :
    /// TidQueue` -- so that `queue T.slots[i].f` finds the record's array (2026-09-08).
    pub field_records: HashMap<(String, String), String>,
    statics_tables: HashMap<String, String>,
    statics_records: HashMap<String, String>,
    /// The scalar statics with a shape -- `static mut summe : u32` -- as `Place.global`s
    /// of `shapeOf`, so that a store into one is checked and a read from one is shaped.
    statics_scalars: Vec<(String, Shape)>,
    routines: BTreeMap<String, RoutineInfo>,
    result_shape: HashMap<String, Option<Shape>>,
    /// The declared range of an integer answer.
    result_range: HashMap<String, Option<(i128, i128)>>,
    /// The precondition expression of every routine of the unit -- shapes, `requires` and
    /// the invariants it maintains -- or the reason a clause has no term.
    pre_of: HashMap<String, Result<String, LeanReason>>,
    /// The layout of each routine's precondition: how many shape conjuncts, how many
    /// `requires`, how many kept invariants -- in that order.
    pre_parts: HashMap<String, (usize, usize, usize)>,
    foreign: BTreeMap<String, ForeignInfo>,
    ops: BTreeMap<String, OpInfo>,
    transitions: BTreeMap<String, TransitionInfo>,
    devices: BTreeSet<String>,
    invariants: Vec<InvariantInfo>,
    /// The `spec fn`s with a predicate body, for `refines`.
    specs: HashMap<String, FnDecl>,
    /// Every case of every `tagged type`: case name to whether it carries a payload this
    /// channel can take as a number.
    variants: HashMap<String, Option<bool>>,
    /// Case name -> the shape of the `tagged` type it belongs to.
    variant_sum: HashMap<String, Shape>,
}

fn carriers_written(
    w: &Option<Wirkungen>,
    map: &HashMap<String, String>,
    record_arrays: &HashMap<String, Vec<(String, String)>>,
) -> Vec<String> {
    let mut out = Vec::new();
    if let Some(w) = w {
        for x in &w.liste {
            match &x.art {
                WirkungArt::Schreibt(o)
                | WirkungArt::Verbraucht(o)
                | WirkungArt::Veroeffentlicht(o) => {
                    // `writes c.slots` at `c : ptr<…> Kappenraum` writes the TABLE -- the
                    // parameter name is the routine's, the carrier is the program's.
                    let name = map.get(&o.basis.text).cloned().unwrap_or_else(|| o.basis.text.clone());
                    // a record written is its arrays written -- they are tables of their own
                    if let Some(arrays) = record_arrays.get(&name) {
                        for (_, tab) in arrays {
                            if !out.contains(tab) {
                                out.push(tab.clone());
                            }
                        }
                    }
                    if !out.contains(&name) {
                        out.push(name);
                    }
                }
                WirkungArt::Liest(_)
                | WirkungArt::Sperrt(_)
                | WirkungArt::SperrtGeteilt(_)
                | WirkungArt::Maskiert(_)
                | WirkungArt::Belegt(_)
                | WirkungArt::Divergiert
                | WirkungArt::Rein => {}
            }
        }
    }
    out
}

fn points_at(typ: &TypExpr, decls: &HashMap<String, TableInfo>) -> Option<String> {
    let target = match typ {
        TypExpr::Zeiger(z) => &z.ziel,
        t => t,
    };
    let TypExpr::Pfad(pf) = target else { return None };
    let last = pf.teile.last()?;
    decls.contains_key(&last.text).then(|| last.text.clone())
}

fn points_at_record(typ: &TypExpr, decls: &HashMap<String, Vec<(String, Option<Shape>)>>) -> Option<String> {
    let target = match typ {
        TypExpr::Zeiger(z) => &z.ziel,
        t => t,
    };
    let TypExpr::Pfad(pf) = target else { return None };
    let last = pf.teile.last()?;
    decls.contains_key(&last.text).then(|| last.text.clone())
}

/// **The translation context of a routine** -- its parameters as locals, its carriers.
fn ctx_for<'a>(unit: &'a Unit, f: &FnDecl, routine: &str, module: &str, site: ResultSite) -> Ctx<'a> {
    let mut carrier = HashMap::new();
    for name in unit.tables.keys() {
        carrier.insert(name.clone(), name.clone());
    }
    for (n, t) in &unit.statics_tables {
        carrier.insert(n.clone(), t.clone());
    }
    let mut record_carrier = HashMap::new();
    for (n, r) in &unit.statics_records {
        record_carrier.insert(n.clone(), r.clone());
    }
    let mut locals = Vec::new();
    for p in &f.parameter {
        if let Some(t) = points_at(&p.typ, &unit.tables) {
            carrier.insert(p.name.text.clone(), t);
        }
        if let Some(r) = points_at_record(&p.typ, &unit.records) {
            record_carrier.insert(p.name.text.clone(), r);
        }
        let sh = unit
            .routines
            .get(&f.name.text)
            .and_then(|r| r.params.iter().find(|(n, _)| n == &p.name.text))
            .and_then(|(_, s)| *s);
        locals.push((p.name.text.clone(), sh));
    }
    let ranges = unit.routines.get(&f.name.text).map(|r| r.ranges.clone()).unwrap_or_default();
    let mut device_carrier = BTreeSet::new();
    for p in &f.parameter {
        let target = match &p.typ {
            TypExpr::Zeiger(z) => &z.ziel,
            t => t,
        };
        if let TypExpr::Pfad(pf) = target {
            if pf.teile.last().is_some_and(|l| unit.devices.contains(&l.text)) {
                device_carrier.insert(p.name.text.clone());
            }
        }
    }
    Ctx {
        unit,
        carrier,
        record_carrier,
        record_value: HashMap::new(),
        record_binds: 0,
        locals,
        ranges,
        device_carrier,
        self_carrier: None,
        module: module.to_string(),
        allow_calls: true,
        result_site: site,
        uses_result: false,
        olds: Vec::new(),
        seen: Vec::new(),
        seen_records: Vec::new(),
        routine: routine.to_string(),
        hoists: 0,
        hoisted: HashMap::new(),
        loops: 0,
        loop_infos: Vec::new(),
        loop_stack: Vec::new(),
        callees: BTreeSet::new(),
        option_reads: Vec::new(),
        ret_post: None,
        has_result: f.ergebnis.is_some(),
        kept: Vec::new(),
    }
}

/// The context of a `table`/`group` invariant: no parameters, `Self` is the carrier.
fn ctx_for_invariant<'a>(unit: &'a Unit, self_carrier: Option<String>, module: &str) -> Ctx<'a> {
    let mut carrier = HashMap::new();
    for name in unit.tables.keys() {
        carrier.insert(name.clone(), name.clone());
    }
    for (n, t) in &unit.statics_tables {
        carrier.insert(n.clone(), t.clone());
    }
    Ctx {
        unit,
        carrier,
        record_carrier: unit.statics_records.clone(),
        record_value: HashMap::new(),
        record_binds: 0,
        locals: Vec::new(),
        ranges: HashMap::new(),
        device_carrier: BTreeSet::new(),
        self_carrier,
        module: module.to_string(),
        allow_calls: false,
        result_site: ResultSite::Contract,
        uses_result: false,
        olds: Vec::new(),
        seen: Vec::new(),
        seen_records: Vec::new(),
        routine: String::new(),
        hoists: 0,
        hoisted: HashMap::new(),
        loops: 0,
        loop_infos: Vec::new(),
        loop_stack: Vec::new(),
        callees: BTreeSet::new(),
        option_reads: Vec::new(),
        ret_post: None,
        has_result: false,
        kept: Vec::new(),
    }
}

/// **The precondition of a routine as ONE expression**: the declared shape of every
/// parameter and every `requires`. `None` where a clause has no term.
fn pre_expr(unit: &Unit, f: &FnDecl, module: &str, params: &[(String, Option<Shape>)], ranges: &HashMap<String, (i128, i128)>, maintained: &[String]) -> Result<(String, (usize, usize, usize)), LeanReason> {
    let mut parts: Vec<String> = params
        .iter()
        .filter_map(|(n, sh)| sh.map(|sh| shape_conjunct(n, sh, ranges)))
        .collect();
    let mut c = ctx_for(unit, f, &f.name.text, module, ResultSite::Contract);
    c.allow_calls = false;
    for q in &f.requires {
        parts.push(pred_term(q, &mut c)?.into_term());
    }
    // **`maintains I` is an assumption of `I` on entry**, and so is every global invariant
    // of a carrier the routine writes: the invariant stands in the precondition, so a
    // caller has to hand it in -- and gets it back from the promise.
    let shapes = parts.len() - f.requires.len();
    let mut invs = 0;
    for m in maintained {
        if let Ok(t) = kept_invariant(unit, f, module, m) {
            parts.push(t);
            invs += 1;
        } else {
            kept_invariant(unit, f, module, m)?;
        }
    }
    Ok((conj(&parts), (shapes, f.requires.len(), invs)))
}

/// **An invariant a routine keeps, as an expression in the routine's own names.** A
/// `table`/`group` invariant has one term for the unit; a `spec fn` named by `maintains`
/// is inlined with its parameters mapped onto the routine's parameters OF THE SAME NAME --
/// `maintains baum_wohlgeformt` at `f(c : ptr<…> Kappenraum, …)` reads `baum_wohlgeformt(c)`.
fn kept_invariant(unit: &Unit, f: &FnDecl, module: &str, name: &str) -> Result<String, LeanReason> {
    if let Some(inv) = unit.invariants.iter().find(|i| i.name == name) {
        return inv.term.clone();
    }
    let spec = unit.specs.get(name).ok_or(LeanReason::Invariant)?;
    let FnRumpf::Pred(body) = &spec.rumpf else {
        return Err(LeanReason::SpecShape);
    };
    for p in &spec.parameter {
        if !f.parameter.iter().any(|q| q.name.text == p.name.text) {
            return Err(LeanReason::Invariant);
        }
    }
    let mut c = ctx_for(unit, f, &f.name.text, module, ResultSite::Contract);
    c.allow_calls = false;
    pred_term(body, &mut c).map(Carried::into_term)
}

/// **The root of a table's `reaches`-invariant**, for the `insert` premise of its ops.
fn reaches_root(t: &Tabelle) -> Option<Expr> {
    fn suche(p: &Pred) -> Option<Expr> {
        match &p.art {
            PredArt::Erreicht { nach, .. } => {
                if let [OrtSuffix::Feld(_), OrtSuffix::Index(i)] = &nach.suffixe[..] {
                    return Some(i.clone());
                }
                None
            }
            PredArt::Quantor(q) => suche(&q.rumpf),
            PredArt::Klammer(x) | PredArt::Nicht(x) => suche(x),
            PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
                suche(a).or_else(|| suche(b))
            }
            PredArt::Vergleich(_) | PredArt::Element(_, _) | PredArt::Held { .. } => None,
        }
    }
    t.invarianten.iter().find_map(|i| suche(&i.pred))
}

impl Unit {
    pub fn sammle(baum: &Programm) -> Unit {
        let u = crate::umgebung::Umgebung::sammle(baum);
        let mut tables = HashMap::new();
        let mut records = HashMap::new();
        let mut array_fields: Vec<(String, String, ArrayTy, String)> = Vec::new();
        let mut static_arrays: Vec<(String, ArrayTy, String)> = Vec::new();
        let mut devices = BTreeSet::new();
        let mut table_decls: Vec<(String, Tabelle)> = Vec::new();
        let mut group_decls: Vec<(String, GruppeDecl)> = Vec::new();
        let mut specs = HashMap::new();
        let mut variants: HashMap<String, Option<bool>> = HashMap::new();
        let mut variant_sum: HashMap<String, Shape> = HashMap::new();
        let mut fn_decls: Vec<(String, FnDecl)> = Vec::new();
        let mut transitions_raw: Vec<(String, Uebergang)> = Vec::new();
        crate::fuer_jedes_item_im_modul(baum, &mut |item, module| match &item.art {
            ItemArt::Tabelle(tb) => {
                let mut fields = Vec::new();
                let mut wraps = HashMap::new();
                if let Some(s) = &tb.slot {
                    for f in &s.felder {
                        let form = match &f.typ {
                            SlotTyp::Typ(te) => shape_of(te, &u, module),
                            // **A `wrapping` field is a NUMBER**, and a store into it is
                            // reduced to its width (`Expr.wrapTo`).
                            SlotTyp::Wrapping(it) => {
                                if let crate::typen::Typ::Ganzzahl(b) | crate::typen::Typ::Umlaufend(b) =
                                    u.typ_von_ausdruck_decl(module, &TypExpr::Int(it.clone()))
                                {
                                    wraps.insert(f.name.text.clone(), (b.breite, b.vorzeichen));
                                }
                                Some(Shape::Int)
                            }
                        };
                        fields.push((f.name.text.clone(), form));
                    }
                }
                let count = tb
                    .kapazitaet
                    .as_ref()
                    .and_then(|e| u.konst_wert(module, e));
                tables.insert(
                    tb.name.text.clone(),
                    TableInfo {
                        fields,
                        wraps,
                        count,
                        belegt: tb.belegt.as_ref().map(|b| b.text.clone()),
                        elter: tb.baum.as_ref().and_then(|b| b.elter.as_ref().map(|e| e.text.clone())),
                        root: reaches_root(tb),
                    },
                );
                table_decls.push((module.to_string(), tb.clone()));
            }
            ItemArt::Gruppe(g) => group_decls.push((module.to_string(), g.clone())),
            ItemArt::Format(fo) => {
                let fields = fo
                    .felder
                    .iter()
                    .map(|f| {
                        (
                            f.name.text.clone(),
                            if f.reserviert { None } else { shape_of(&f.typ.typ, &u, module) },
                        )
                    })
                    .collect();
                records.insert(fo.name.text.clone(), fields);
            }
            ItemArt::Typ(td) => {
                // **The cases of a `tagged type`**, with whether the payload is a number
                // here: an integer, an index, or a named type over one (an opaque handle
                // taken as its representation -- the model may see what `D1` hides from the
                // program, because nothing in the model can compute with it).
                if let Some(TypExpr::Varianten(vs, _)) = &td.rumpf {
                    for v in vs {
                        let payload = match &v.nutzlast {
                            None => Some(false),
                            Some(t) => {
                                use crate::typen::Typ;
                                match u.typ_von_ausdruck_decl(module, t) {
                                    Typ::Ganzzahl(_) | Typ::Umlaufend(_) | Typ::Tabelle(_) | Typ::Benannt { .. } => Some(true),
                                    _ => match t {
                                        TypExpr::Index { .. } => Some(true),
                                        _ => None,
                                    },
                                }
                            }
                        };
                        variants.insert(v.name.text.clone(), payload);
                    }
                    // the type's shape, for every case name
                    if let Some(sh) = shape_of_typ(&u.typ_von_ausdruck_decl(module, &TypExpr::Pfad(Pfad {
                        teile: vec![td.name.clone()],
                        span: td.name.span,
                    }))) {
                        for v in vs {
                            variant_sum.insert(v.name.text.clone(), sh);
                        }
                    }
                }
                if let Some(TypExpr::Verbund(fs, _)) = &td.rumpf {
                    if td.opaque {
                        return;
                    }
                    let fields = fs
                        .iter()
                        .map(|f| (f.name.text.clone(), shape_of(&f.typ.typ, &u, module)))
                        .collect();
                    for f in fs {
                        if let TypExpr::Feld(arr) = &f.typ.typ {
                            array_fields.push((td.name.text.clone(), f.name.text.clone(), arr.as_ref().clone(), module.to_string()));
                        }
                    }
                    records.insert(td.name.text.clone(), fields);
                }
            }
            ItemArt::Device(d) => {
                devices.insert(d.name.text.clone());
                for ue in &d.uebergaenge {
                    transitions_raw.push((d.name.text.clone(), ue.clone()));
                }
            }
            ItemArt::Funktion(f) => {
                if f.klasse == Some(FnKlasse::Spec) {
                    if let FnRumpf::Pred(_) = &f.rumpf {
                        specs.insert(f.name.text.clone(), f.clone());
                    }
                    return;
                }
                fn_decls.push((module.to_string(), f.clone()));
            }
            _ => {}
        });
        let mut statics_tables = HashMap::new();
        let mut statics_records = HashMap::new();
        let mut statics_scalars = Vec::new();
        crate::fuer_jedes_item_im_modul(baum, &mut |item, module| {
            // **An `atomic` and an `accumulates` are globals too** -- one place each, of
            // the declared type; what makes them atomic or per-core is the emitter's, and
            // the model reads and writes the one place.
            match &item.art {
                // **A constant without a value the checker folded** (`~x`, an expression
                // over another) is read as a place of the constant's shape -- `place_term`
                // writes `.global` for it, and the world has to type that place.
                ItemArt::Konst(k) => {
                    if u.konst_wert_von_namen(module, &k.name.text).is_none() {
                        if let Some(sh) = shape_of(&k.typ, &u, module) {
                            statics_scalars.push((k.name.text.clone(), sh));
                        }
                    }
                    return;
                }
                ItemArt::Atomic(a) => {
                    if let Some(sh) = shape_of(&a.typ, &u, module) {
                        statics_scalars.push((a.name.text.clone(), sh));
                    }
                    return;
                }
                ItemArt::Accumulates(a) => {
                    if let Some(sh) = shape_of(&a.typ, &u, module) {
                        statics_scalars.push((a.name.text.clone(), sh));
                    }
                    return;
                }
                _ => {}
            }
            let ItemArt::Statisch(st) = &item.art else { return };
            if let TypExpr::Feld(arr) = &st.typ {
                static_arrays.push((st.name.text.clone(), arr.as_ref().clone(), module.to_string()));
                return;
            }
            if let Some(t) = points_at(&st.typ, &tables) {
                statics_tables.insert(st.name.text.clone(), t);
            } else if let Some(r) = points_at_record(&st.typ, &records) {
                statics_records.insert(st.name.text.clone(), r);
            } else if let Some(sh) = shape_of(&st.typ, &u, module) {
                statics_scalars.push((st.name.text.clone(), sh));
            }
        });
        // **The arrays, as pseudo-tables.** One field `elem`, the element's shape; `count`
        // the declared length where it is a constant. An array whose element has no shape
        // or whose length is not a constant gets no table -- and its places stay refused.
        let mut record_arrays: HashMap<String, Vec<(String, String)>> = HashMap::new();
        let pseudo = |arr: &ArrayTy, module: &str| -> Option<TableInfo> {
            let sh = shape_of(&arr.element, &u, module)?;
            let count = u.konst_wert(module, &arr.laenge)?;
            Some(TableInfo {
                fields: vec![("elem".to_string(), Some(sh))],
                wraps: HashMap::new(),
                count: Some(count),
                belegt: None,
                elter: None,
                root: None,
            })
        };
        for (rec, field, arr, module) in &array_fields {
            if let Some(info) = pseudo(arr, module) {
                let name = format!("{rec}.{field}");
                tables.insert(name.clone(), info);
                record_arrays.entry(rec.clone()).or_default().push((field.clone(), name));
            }
        }
        for (name, arr, module) in &static_arrays {
            if let Some(info) = pseudo(arr, module) {
                tables.insert(name.clone(), info);
                statics_tables.insert(name.clone(), name.clone());
            }
        }
        // Which invariants a `maintains` names, unit-wide.
        let mut named = BTreeSet::new();
        for (_, f) in &fn_decls {
            for i in &f.maintains {
                named.insert(i.text.clone());
            }
        }
        // the slot fields of record type, by name: `queue T.slots[i].f` reads through them
        let mut field_records: HashMap<(String, String), String> = HashMap::new();
        for (_, tb) in &table_decls {
            if let Some(sl) = &tb.slot {
                for f in &sl.felder {
                    if let SlotTyp::Typ(te) = &f.typ {
                        if let Some(r) = points_at_record(te, &records) {
                            field_records.insert((tb.name.text.clone(), f.name.text.clone()), r);
                        }
                    }
                }
            }
        }
        let mut unit = Unit {
            u,
            tables,
            records,
            field_records,
            statics_tables,
            statics_records,
            statics_scalars,
            record_arrays,
            routines: BTreeMap::new(),
            result_shape: HashMap::new(),
            result_range: HashMap::new(),
            pre_of: HashMap::new(),
            pre_parts: HashMap::new(),
            foreign: BTreeMap::new(),
            ops: BTreeMap::new(),
            transitions: BTreeMap::new(),
            devices,
            invariants: Vec::new(),
            specs,
            variants,
            variant_sum,
        };
        // The invariants first: a routine's `maintained` list reads them.
        for (module, tb) in &table_decls {
            for inv in &tb.invarianten {
                let mut c = ctx_for_invariant(&unit, Some(tb.name.text.clone()), module);
                let term = pred_term(&inv.pred, &mut c).map(Carried::into_term);
                unit.invariants.push(InvariantInfo {
                    name: inv.name.text.clone(),
                    carriers: vec![tb.name.text.clone()],
                    term,
                    maintained_by_name: named.contains(&inv.name.text),
                    under_ops: !tb.ops.is_empty(),
                });
            }
        }
        for (module, g) in &group_decls {
            for inv in &g.invarianten {
                let mut c = ctx_for_invariant(&unit, None, module);
                let term = pred_term(&inv.pred, &mut c).map(Carried::into_term);
                unit.invariants.push(InvariantInfo {
                    name: inv.name.text.clone(),
                    carriers: g.traeger.iter().map(|t| t.text.clone()).collect(),
                    term,
                    maintained_by_name: named.contains(&inv.name.text),
                    under_ops: false,
                });
            }
        }
        // The routines, with parameters and results shaped from their declarations.
        for (module, f) in &fn_decls {
            let params: Vec<(String, Option<Shape>)> = f
                .parameter
                .iter()
                .map(|p| (p.name.text.clone(), shape_of(&p.typ, &unit.u, module)))
                .collect();
            let result = f.ergebnis.as_ref().and_then(|t| shape_of(t, &unit.u, module));
            unit.result_shape.insert(f.name.text.clone(), result);
            unit.result_range.insert(
                f.name.text.clone(),
                f.ergebnis.as_ref().and_then(|t| result_range_of(t, &unit.u, module)),
            );
            let mut map = unit.statics_tables.clone();
            for p in &f.parameter {
                if let Some(t) = points_at(&p.typ, &unit.tables) {
                    map.insert(p.name.text.clone(), t);
                }
                if let Some(r) = points_at_record(&p.typ, &unit.records) {
                    map.insert(p.name.text.clone(), r);
                }
            }
            // a static record written writes its arrays too
            for (n, r) in &unit.statics_records {
                map.entry(n.clone()).or_insert_with(|| r.clone());
            }
            let writes = carriers_written(&f.effects, &map, &unit.record_arrays);
            if let FnRumpf::Block(_) = &f.rumpf {
                let mut maintained: Vec<String> = f.maintains.iter().map(|i| i.text.clone()).collect();
                for inv in &unit.invariants {
                    if inv.maintained_by_name || inv.under_ops {
                        continue;
                    }
                    if inv.carriers.iter().any(|ca| writes.contains(ca)) && !maintained.contains(&inv.name) {
                        maintained.push(inv.name.clone());
                    }
                }
                unit.routines.insert(
                    f.name.text.clone(),
                    RoutineInfo {
                        module: module.clone(),
                        decl: f.clone(),
                        ranges: param_ranges(f, &unit.u, module),
                        params,
                        writes,
                        maintained,
                    },
                );
            } else {
                unit.foreign.insert(
                    f.name.text.clone(),
                    ForeignInfo {
                        name: f.name.text.clone(),
                        params,
                        result,
                        result_range: f.ergebnis.as_ref().and_then(|t| result_range_of(t, &unit.u, module)),
                        fehler: f.fehler.is_some(),
                        never: matches!(f.ergebnis, Some(TypExpr::Never(_))),
                        has_result: f.ergebnis.is_some() && !matches!(f.ergebnis, Some(TypExpr::Never(_))),
                        pre: None,
                        post: Vec::new(),
                        writes,
                    },
                );
            }
        }
        // **A name declared twice -- `pub impl fn` and `extern fn` in one unit** (`beispiele/29`)
        // is ONE routine here, and the body wins: a foreign contract beside a body of the
        // same name would be two declarations of one callee.
        let doubled: Vec<String> = unit.foreign.keys().filter(|n| unit.routines.contains_key(*n)).cloned().collect();
        for n in doubled {
            unit.foreign.remove(&n);
        }
        // The preconditions -- after every routine is known, because a `requires` may name a
        // table through a parameter and the context reads the routine's parameters.
        let names: Vec<String> = unit.routines.keys().cloned().collect();
        for n in names {
            let (decl, module, params, ranges, maintained) = {
                let r = &unit.routines[&n];
                (r.decl.clone(), r.module.clone(), r.params.clone(), r.ranges.clone(), r.maintained.clone())
            };
            match pre_expr(&unit, &decl, &module, &params, &ranges, &maintained) {
                Ok((p, k)) => {
                    unit.pre_of.insert(n.clone(), Ok(p));
                    unit.pre_parts.insert(n, k);
                }
                Err(e) => {
                    unit.pre_of.insert(n, Err(e));
                }
            }
        }
        let fnames: Vec<String> = unit.foreign.keys().cloned().collect();
        for n in fnames {
            let (decl, params) = {
                let module_decl = fn_decls.iter().find(|(_, f)| f.name.text == n).cloned();
                (module_decl, unit.foreign[&n].params.clone())
            };
            let Some((module, decl)) = decl else { continue };
            let ranges = param_ranges(&decl, &unit.u, &module);
            let pre = pre_expr(&unit, &decl, &module, &params, &ranges, &[]).ok().map(|(p, _)| p);
            let mut post = Vec::new();
            {
                let mut c = ctx_for(&unit, &decl, &n, &module, ResultSite::Bound);
                c.allow_calls = false;
                for q in &decl.ensures {
                    let olds_before = c.olds.len();
                    c.uses_result = false;
                    if let Ok(t) = pred_term(q, &mut c) {
                        post.push(clause_prop(t.as_str(), &c.olds[olds_before..], c.uses_result, "t", "t'", "r"));
                    }
                }
            }
            let f = unit.foreign.get_mut(&n).unwrap();
            f.pre = pre;
            f.post = post;
        }
        // The generated operations.
        for (_, tb) in &table_decls {
            for k in crate::opsruf::koepfe(tb) {
                let info = &unit.tables[&tb.name.text];
                let params: Vec<String> = k.parameter.iter().map(|(n, _)| n.clone()).collect();
                let pre = op_pre(&k, info, &tb.name.text);
                unit.ops.insert(
                    k.pfad(),
                    OpInfo {
                        key: k.pfad(),
                        table: tb.name.text.clone(),
                        params,
                        pre,
                    },
                );
            }
        }
        // The transitions: a `requires` over register names has no place here, so the
        // precondition is `true` only where there is no clause at all.
        for (dev, ue) in &transitions_raw {
            let pre = if ue.requires.is_none() {
                Some("(.lit (.bool true))".to_string())
            } else {
                None
            };
            unit.transitions.insert(
                ue.name.text.clone(),
                TransitionInfo {
                    name: ue.name.text.clone(),
                    device: dev.clone(),
                    pre,
                },
            );
        }
        unit
    }
}

/// **The premises of a generated operation, as one expression over its parameters.**
fn op_pre(k: &crate::opsruf::Kopf, info: &TableInfo, table: &str) -> Option<String> {
    use crate::opsruf::Forderung;
    let count = info.count?;
    let mut parts = Vec::new();
    let pname = |i: usize| k.parameter.get(i).map(|(n, _)| format!("(.name {})", quoted(n)));
    // The index parameters carry a shape; the carrier parameter is the table itself.
    for (i, (n, _)) in k.parameter.iter().enumerate() {
        if i > 0 {
            parts.push(format!("(.hasShape {} .int)", quoted(n)));
        }
    }
    for f in &k.forderungen {
        match f {
            Forderung::Frei { index, feld, .. } => {
                parts.push(format!(
                    "(.un .not (.place {} {} {}))",
                    quoted(table),
                    pname(*index)?,
                    quoted(feld)
                ));
            }
            Forderung::Erreichbar { index, via, .. } => {
                let root = info.root.as_ref()?;
                let root = match &root.art {
                    ExprArt::Zahl(n) => format!("(.lit (.int {n}))"),
                    ExprArt::Ort(o) if o.suffixe.is_empty() => format!("(.global {})", quoted(&o.basis.text)),
                    _ => return None,
                };
                parts.push(format!(
                    "(.reaches {} {} {root} {} {count})",
                    quoted(table),
                    pname(*index)?,
                    quoted(via)
                ));
            }
            Forderung::Blatt { index, via, .. } => {
                parts.push(format!(
                    "(.forallSlots \"x\" {count} (.bin .ne (.place {} (.name \"x\") {}) (.someOf {})))",
                    quoted(table),
                    quoted(via),
                    pname(*index)?
                ));
            }
            Forderung::NichtUeber { elter, platz, via, .. } => {
                parts.push(format!(
                    "(.un .not (.reaches {} {} {} {} {count}))",
                    quoted(table),
                    pname(*elter)?,
                    pname(*platz)?,
                    quoted(via)
                ));
            }
        }
    }
    Some(conj(&parts))
}

/// **One clause of a postcondition, as a `Prop` over the entry state, the exit state and
/// the result.** The locals are the ENTRY's -- a parameter the body rebinds still names its
/// argument in the contract -- with `old#i` and `result` bound on top.
fn clause_prop(term: &str, olds: &[String], uses_result: bool, s: &str, s2: &str, r: &str) -> String {
    let mut out = String::new();
    let mut binding = format!("{s}.local'");
    for (i, o) in olds.iter().enumerate() {
        out.push_str(&format!("∀ o{n}, eval {s} {o} = some o{n} → ", n = i + 1));
        binding = format!("(bindLocal {binding} \"old#{}\" o{})", i + 1, i + 1);
    }
    if uses_result {
        out.push_str(&format!("∃ v, {r} = some v ∧ "));
        binding = format!("(bindLocal {binding} \"result\" v)");
    }
    out.push_str(&format!(
        "eval {{ world := {s2}.world, local' := {binding} }} {term} = some (.bool true)"
    ));
    format!("({out})")
}

// ===========================================================================================
// THE THEOREMS OF A UNIT -- one per routine, one per loop, and the wiring.
// ===========================================================================================

/// A routine's translation, or the reason there is none.
pub struct RoutineGoal {
    pub name: String,
    pub body: Result<String, LeanReason>,
    /// The postcondition clauses -- `(origin, prop)` -- and the reason a clause has none.
    pub post: Vec<(String, Result<String, LeanReason>)>,
    /// The invariants this routine preserves -- `(name, term)`.
    pub keeps: Vec<(String, String)>,
    pub callees: BTreeSet<String>,
    pub loops: Vec<LoopInfo>,
    pub seen: Vec<(String, String, Shape, String)>,
    pub seen_records: Vec<(String, String, Shape)>,
    pub writes: Vec<String>,
    /// The parameters with a shape -- the `obtain` lines the proof opens with.
    pub shaped_params: Vec<(String, Shape)>,
    pub option_reads: Vec<(String, String, String, Shape)>,
    /// The declared ranges of the integer parameters (`RoutineInfo::ranges`).
    pub ranges: HashMap<String, (i128, i128)>,
    /// The `decreases` measure as a term, where the routine calls ITSELF directly and
    /// declares one -- the bounded self-contract in its statement, and the induction in
    /// `unit_closed` (`contract_of_duty_rec`), rest on it.
    pub decreases: Option<String>,
}

/// **Does the routine call itself directly -- and only there, not inside one of its loops?**
/// The direct case is what `contract_of_duty_rec` wires; a recursive call inside a loop
/// would need the bounded contract in the loop's statement, which is not written.
fn self_recursive(g: &RoutineGoal) -> bool {
    g.callees.contains(&g.name) && !g.loops.iter().any(|l| l.callees.contains(&g.name))
}

/// **Which loop does the routine call itself from -- if exactly one does?** (2026-09-08.)
///
/// The composition is `contract_of_duty_rec_loop_in` in the model (`contract_of_duty_rec_loop`
/// where the loop has no index range): the induction over the `decreases` runs OUTSIDE the
/// loop rule, so the pass may assume the bounded self-contract at the ROUTINE's entry state
/// -- and owes in return that the measure is still the one the routine entered with. Without
/// that second half the bound would be vacuous: a pass that lowered the measure could call
/// itself "below" a bound that no longer holds.
///
/// **What has to hold, and what does NOT.**
///
/// * Exactly ONE loop of the routine may hold the recursive call. Two would need the rule of
///   each inside the same induction, and the model composes one.
/// * That loop carries no loop inside it and stands inside no loop of the routine: every loop
///   on the way to the call would have to carry the measure too, and the composition is
///   written once, not for a stack (`nested`).
/// * That loop does not count its passes: its rule would be a `LoopRuleP`, and the
///   composition takes a `LoopRule`.
/// * **The routine's OTHER loops are none of this step's business** (2026-09-08). Their rules
///   are built before the contract, exactly as any loop's is, and handed to the routine's
///   duty beside the one the induction builds. Refusing them was an over-refusal: the earlier
///   `g.loops.len() == 1` refused a routine for a second loop that has nothing to do with the
///   recursion.
/// * **An index range is NOT required** (2026-09-08). The induction is over the `decreases`,
///   never over the index; the range is an assumption the pass gets, not a premise of the
///   composition. `looprule_of_body` builds the rule of a `retry`/`forever` loop without one.
fn rec_loop_of(g: &RoutineGoal) -> Option<usize> {
    if !g.callees.contains(&g.name) || g.decreases.is_none() {
        return None;
    }
    let mut found = None;
    for (i, l) in g.loops.iter().enumerate() {
        if l.callees.contains(&g.name) {
            if found.is_some() {
                return None; // several loops hold the call
            }
            found = Some(i);
        }
    }
    let i = found?;
    // Every loop of the routine carries the measure now, so every one of them has to be a
    // loop this step can build: flat (no stack of rules to compose) and not counting passes
    // (a `LoopRuleP` is not what the composition takes).
    if g.loops.iter().any(|l| !l.nested.is_empty() || l.passes.is_some()) {
        return None;
    }
    Some(i)
}

/// `rec_loop_of`, as a yes/no.
fn rec_in_loop(g: &RoutineGoal) -> bool {
    rec_loop_of(g).is_some()
}

/// **The whole unit, judged.** Every routine with a body, in declaration order.
pub fn routine_goals(unit: &Unit) -> Vec<RoutineGoal> {
    let mut out = Vec::new();
    for (name, r) in &unit.routines {
        let FnRumpf::Block(b) = &r.decl.rumpf else { continue };
        let mut keeps = Vec::new();
        for m in &r.maintained {
            if let Ok(t) = kept_invariant(unit, &r.decl, &r.module, m) {
                keeps.push((m.clone(), t));
            }
        }
        let mut c = ctx_for(unit, &r.decl, name, &r.module, ResultSite::Body);
        c.ret_post = ret_post_of(unit, &r.decl, &r.module, &r.maintained);
        c.kept = keeps.iter().map(|(_, t)| t.clone()).collect();
        let body = match unit.pre_of.get(name) {
            Some(Err(e)) => Err(*e),
            _ => block_term(b, &mut c).map(Carried::into_term),
        };
        let (callees, loops) = (std::mem::take(&mut c.callees), std::mem::take(&mut c.loop_infos));
        // The clauses: `ensures`, then `refines`.
        c.result_site = ResultSite::Bound;
        c.locals = r.decl.parameter.iter().map(|p| (p.name.text.clone(), None)).collect();
        let mut post = Vec::new();
        for (i, q) in r.decl.ensures.iter().enumerate() {
            c.olds.clear();
            c.uses_result = false;
            let t = pred_term(q, &mut c);
            post.push((
                format!("ensures #{}", i + 1),
                t.map(|t| clause_prop(t.as_str(), &c.olds, c.uses_result, "s", "s'", "r")),
            ));
        }
        if let Some(g) = &r.decl.verfeinert {
            let ziel = g.teile.last().map(|i| i.text.clone()).unwrap_or_default();
            let t = match specification(&r.decl, &ziel, unit) {
                Ok(p) => {
                    c.olds.clear();
                    c.uses_result = false;
                    pred_term(&p, &mut c)
                        .map(|t| clause_prop(t.as_str(), &c.olds, c.uses_result, "s", "s'", "r"))
                }
                Err(e) => Err(e),
            };
            post.push((format!("refines {ziel}"), t));
        }
        let shaped_params = r
            .params
            .iter()
            .filter_map(|(n, s)| s.map(|s| (n.clone(), s)))
            .collect();
        // The measure, wherever the routine declares one -- the self-recursion and the
        // cycle (`wiring_order`) rest on it; a recursive call inside a loop stays unwired.
        let decreases = r.decl.decreases.as_ref().and_then(|m| {
            let mut mc = ctx_for(unit, &r.decl, name, &r.module, ResultSite::Body);
            mc.allow_calls = false;
            expr_term(m, &mut mc).ok().map(Carried::into_term)
        });
        out.push(RoutineGoal {
            name: name.clone(),
            body,
            post,
            keeps,
            callees,
            loops,
            seen: c.seen.clone(),
            seen_records: c.seen_records.clone(),
            writes: r.writes.clone(),
            shaped_params,
            option_reads: c.option_reads.clone(),
            ranges: r.ranges.clone(),
            decreases,
        });
    }
    out
}

/// **What a `return` inside a loop has to establish**: every `ensures` with `result` read
/// as `#ret`, every `refines`, and every invariant the routine keeps -- as one expression.
/// `None` where a clause has no such reading.
fn ret_post_of(unit: &Unit, f: &FnDecl, module: &str, maintained: &[String]) -> Option<String> {
    let mut c = ctx_for(unit, f, &f.name.text, module, ResultSite::LoopRet);
    c.allow_calls = false;
    let mut parts = Vec::new();
    // the answer's shape travels with the flag -- the `return` after the loop hands `#ret`
    // to the promise, which says the answer has the declared shape (`result_clause`)
    if f.fehler.is_none() {
        if let Some(sh) = unit.result_shape.get(&f.name.text).copied().flatten() {
            parts.push(format!("(.hasShape \"#ret\" {})", sh.lean()));
        }
    }
    for q in &f.ensures {
        parts.push(pred_term(q, &mut c).ok()?.into_term());
    }
    if let Some(g) = &f.verfeinert {
        let ziel = g.teile.last().map(|i| i.text.clone()).unwrap_or_default();
        let p = specification(f, &ziel, unit).ok()?;
        parts.push(pred_term(&p, &mut c).ok()?.into_term());
    }
    for m in maintained {
        parts.push(kept_invariant(unit, f, module, m).ok()?);
    }
    Some(conj(&parts))
}

/// **The single pre-loop binding of `#ret` (F2).**
///
/// Returns the term and the shape the binding carries: the routine's declared answer
/// shape with a value of that shape -- `0`, the range's `lo`, `false`, `absent` -- so
/// that the invariant's `hasShape` conjunct holds on entry and every `return` inside
/// rebinds the SAME shape (`binde` keeps on equal, `Anweisung.lean:102`).
///
/// Where no `return` can hand the slot a value of the declared shape, the binding stays
/// `absent`/`None`, as before: no result at all, an unshaped one, a `tagged` one (a
/// `tagged` value is no literal here, and `schluss` gives `.tagOf` no shape either, so
/// carrying one would trade today's refusal for an unprovable conjunct), or `-> T or R`
/// (the slot may hold a reason, and `ret_post_of` above says no shape for it either).
fn ret_init(c: &Ctx) -> (String, Option<Shape>) {
    let shape = c
        .unit
        .routines
        .get(&c.routine)
        .filter(|r| r.decl.fehler.is_none())
        .and_then(|_| c.unit.result_shape.get(&c.routine).copied().flatten());
    match shape {
        Some(Shape::Int) => ("(.lit (.int 0))".into(), shape),
        Some(Shape::IntIn(lo, _)) => (format!("(.lit (.int {}))", int_lit(lo)), shape),
        Some(Shape::Bool) => ("(.lit (.bool false))".into(), shape),
        Some(Shape::Opt) => ("(.lit .absent)".into(), shape),
        Some(Shape::Sum(_)) | None => ("(.lit .absent)".into(), None),
    }
}

/// **`refines g` -- the head form.** The postcondition IS the `spec fn`'s expression body,
/// with its own parameter names replaced by the implementation's.
fn specification(f: &FnDecl, name: &str, unit: &Unit) -> Result<Pred, LeanReason> {
    let spec = unit.specs.get(name).ok_or(LeanReason::SpecShape)?;
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
        PredArt::Quantor(q) => PredArt::Quantor(Box::new(Quantor {
            art: q.art,
            variable: q.variable.clone(),
            domaene: renamed_domain(&q.domaene, pairs),
            rumpf: renamed_pred(&q.rumpf, pairs),
        })),
        PredArt::Erreicht { von, nach, via } => PredArt::Erreicht {
            von: renamed_ort(von, pairs),
            nach: renamed_ort(nach, pairs),
            via: via.clone(),
        },
        other => other.clone(),
    };
    Pred { art, ..p.clone() }
}

fn renamed_domain(d: &Domaene, pairs: &[(String, String)]) -> Domaene {
    match d {
        Domaene::SlotsVon(o) => Domaene::SlotsVon(renamed_ort(o, pairs)),
        other => other.clone(),
    }
}

fn renamed_ort(o: &Ort, pairs: &[(String, String)]) -> Ort {
    let mut o = o.clone();
    if let Some((_, fresh)) = pairs.iter().find(|(old, _)| *old == o.basis.text) {
        o.basis.text = fresh.clone();
    }
    for s in &mut o.suffixe {
        if let OrtSuffix::Index(i) = s {
            *i = renamed_expr(i, pairs);
        }
    }
    o
}

fn renamed_expr(e: &Expr, pairs: &[(String, String)]) -> Expr {
    let art = match &e.art {
        ExprArt::Ort(o) => ExprArt::Ort(renamed_ort(o, pairs)),
        ExprArt::Alt(o) => ExprArt::Alt(renamed_ort(o, pairs)),
        ExprArt::Klammer(x) => ExprArt::Klammer(Box::new(renamed_expr(x, pairs))),
        ExprArt::Unaer(op, x) => ExprArt::Unaer(*op, Box::new(renamed_expr(x, pairs))),
        ExprArt::Binaer(op, a, b) => ExprArt::Binaer(
            *op,
            Box::new(renamed_expr(a, pairs)),
            Box::new(renamed_expr(b, pairs)),
        ),
        ExprArt::Ruf(r) => {
            let mut r = r.clone();
            for a in &mut r.argumente {
                *a = renamed_expr(a, pairs);
            }
            ExprArt::Ruf(r)
        }
        // **Lane E1:** the arguments rename like any call's; the region is
        // raw tokens and carries no names.
        ExprArt::LibraryCall(r) => {
            let mut r = r.clone();
            for a in &mut r.args {
                *a = renamed_expr(a, pairs);
            }
            ExprArt::LibraryCall(r)
        }
        other => other.clone(),
    };
    Expr { art, ..e.clone() }
}

/// **The whole register, judged for the Lean channel.** One entry per obligation of
/// `pflichten::sammle`, in the same order -- so the two channels can be held against each
/// other, obligation by obligation.
pub fn verdicts(baum: &Programm) -> Vec<(crate::pflichten::Pflicht, LeanVerdict)> {
    let unit = Unit::sammle(baum);
    let goals = routine_goals(&unit);
    verdicts_over(baum, &unit, &goals)
}

fn verdicts_over(
    baum: &Programm,
    unit: &Unit,
    goals: &[RoutineGoal],
) -> Vec<(crate::pflichten::Pflicht, LeanVerdict)> {
    use crate::pflichten::Art;
    let by_name: HashMap<&str, &RoutineGoal> = goals.iter().map(|g| (g.name.as_str(), g)).collect();
    let meets = |f: &str| format!("{f}_meets");
    crate::pflichten::sammle(baum)
        .into_iter()
        .map(|p| {
            let v = match p.art {
                Art::Geraetezusage => LeanVerdict::Assumed(LeanReason::DevicePromise),
                Art::Fremdpflicht => LeanVerdict::Assumed(LeanReason::ForeignBody),
                Art::Vorbedingung => match by_name.get(p.funktion.as_str()) {
                    Some(g) => match &g.body {
                        Ok(_) => LeanVerdict::Carried(meets(&g.name)),
                        Err(r) => LeanVerdict::Refused(*r),
                    },
                    None => LeanVerdict::Refused(LeanReason::CallSite),
                },
                Art::Nachbedingung | Art::Verfeinerung => match by_name.get(p.funktion.as_str()) {
                    Some(g) => match &g.body {
                        Err(r) => LeanVerdict::Refused(*r),
                        Ok(_) => {
                            let key = if p.art == Art::Nachbedingung {
                                p.gegenstand.clone()
                            } else {
                                p.gegenstand.clone()
                            };
                            match g.post.iter().find(|(o, _)| *o == key) {
                                Some((_, Ok(_))) => LeanVerdict::Carried(meets(&g.name)),
                                Some((_, Err(r))) => LeanVerdict::Refused(*r),
                                None => LeanVerdict::Refused(LeanReason::Expression),
                            }
                        }
                    },
                    None => LeanVerdict::Refused(LeanReason::Expression),
                },
                Art::Erhaltung => match by_name.get(p.funktion.as_str()) {
                    Some(g) => match &g.body {
                        Err(r) => LeanVerdict::Refused(*r),
                        Ok(_) => {
                            if g.keeps.iter().any(|(n, _)| *n == p.gegenstand) {
                                LeanVerdict::Carried(meets(&g.name))
                            } else {
                                match unit.invariants.iter().find(|i| i.name == p.gegenstand) {
                                    Some(inv) => match &inv.term {
                                        Err(r) => LeanVerdict::Refused(*r),
                                        Ok(_) => LeanVerdict::Refused(LeanReason::Invariant),
                                    },
                                    None => LeanVerdict::Refused(LeanReason::Invariant),
                                }
                            }
                        }
                    },
                    None => LeanVerdict::Refused(LeanReason::Invariant),
                },
                Art::Schleifeninvariante => match by_name.get(p.funktion.as_str()) {
                    Some(g) => match &g.body {
                        Err(r) => LeanVerdict::Refused(*r),
                        Ok(_) => {
                            // `loop invariant #n` -- the n-th loop in source order, and the
                            // loops are numbered in that order.
                            let n = p
                                .gegenstand
                                .rsplit('#')
                                .next()
                                .and_then(|s| s.parse::<usize>().ok())
                                .unwrap_or(0);
                            let id = format!("{}#{n}", g.name);
                            if g.loops.iter().any(|l| l.id == id) {
                                LeanVerdict::Carried(loop_theorem(&id))
                            } else {
                                LeanVerdict::Refused(LeanReason::Loop)
                            }
                        }
                    },
                    None => LeanVerdict::Refused(LeanReason::Loop),
                },
                Art::Walkinvariante => {
                    // A `table`/`group` invariant nobody maintains is owed by its WRITERS; a
                    // `walk` clause is a statement about hardware.
                    let name = p.gegenstand.strip_prefix("invariant ").unwrap_or("");
                    match unit.invariants.iter().find(|i| i.name == name && i.carriers.contains(&p.funktion) || i.name == name && !name.is_empty() && p.gegenstand.starts_with("invariant ")) {
                        Some(inv) => match &inv.term {
                            Err(r) => LeanVerdict::Refused(*r),
                            Ok(_) => {
                                let writers: Vec<String> = goals
                                    .iter()
                                    .filter(|g| g.body.is_ok() && g.keeps.iter().any(|(n, _)| n == name))
                                    .map(|g| meets(&g.name))
                                    .collect();
                                let refused = goals
                                    .iter()
                                    .find(|g| g.body.is_err() && g.writes.iter().any(|w| inv.carriers.contains(w)));
                                match refused {
                                    Some(g) => LeanVerdict::Refused(*g.body.as_ref().err().unwrap()),
                                    None => LeanVerdict::CarriedBy(writers),
                                }
                            }
                        },
                        None => LeanVerdict::Assumed(LeanReason::WalkInvariant),
                    }
                }
            };
            // **A refusal whose reason is an assumption IS an assumption** -- a promise
            // over a device register is the device's, whatever duty it stands in.
            let v = match v {
                LeanVerdict::Refused(r) if r.kind() == Kind::Assumption => LeanVerdict::Assumed(r),
                v => v,
            };
            (p, v)
        })
        .collect()
}

/// **The path to the i-th of n conjuncts** of a right-nested conjunction, from a hypothesis
/// `h` that the whole holds.
fn conj_path(h: &str, i: usize, n: usize) -> String {
    let mut t = h.to_string();
    for _ in 0..i {
        t = format!("(and_right _ _ _ {t})");
    }
    if i + 1 < n {
        t = format!("(and_left _ _ _ {t})");
    }
    t
}

/// **The lines a proof opens with**: a witness for every shaped local (out of the
/// precondition or the invariant), and a witness for every slot field read at such an index
/// (out of the well-typed world). Returns the plain `obtain` lines, the `rcases` splits
/// (chained, because each splits the goal), and the equation names for the simp set.
fn openings(
    state: &str,
    hyp: &str,
    hyp_def: &str,
    shapes: &[(String, Shape)],
    parts: usize,
    reads: &[(String, String, String, Shape)],
    extra_index: Option<(&str, &str)>,
    invariants: &[(usize, String, String)],
    ranges: &HashMap<String, (i128, i128)>,
    record_reads: &[(String, String, Shape)],
) -> (Vec<String>, Vec<String>, Vec<String>) {
    let mut lines = Vec::new();
    let mut splits = Vec::new();
    let mut eqs = Vec::new();
    // **The invariants in the precondition, opened into rewrites.** They are what the
    // person's argument about a store at another index rests on -- and what the model
    // can only use once it is a `∀ k < N, …` and not an `eval`.
    for (i, name, def) in invariants {
        let path = conj_path(hyp, *i, parts);
        lines.push(format!("  have hi_{name} := {path}"));
        // the hypothesis's own definition is in the set too: where the invariant is the
        // whole precondition, the path is the hypothesis itself, still under its name
        lines.push(format!("  gabbro_simp_at hi_{name} [{def}, {hyp_def}]"));
    }
    // which locals have a witness, and under which name
    let mut witness: BTreeMap<String, String> = BTreeMap::new();
    for (i, (n, sh)) in shapes.iter().enumerate() {
        let path = conj_path(hyp, i, parts);
        let q = quoted(n);
        let id = n.replace('#', "_");
        match sh {
            Shape::IntIn(..) => {
                lines.push(format!("  obtain ⟨w_{id}, e_{id}, lo_{id}, hi_{id}⟩ := shape_intIn {state} {q} _ _ {path}"));
                witness.insert(n.clone(), format!("w_{id}"));
                eqs.push(format!("e_{id}"));
            }
            Shape::Int if ranges.contains_key(n) => {
                // the ranged shape: witness, lower and upper bound -- the bounds stay as
                // hypotheses `lo_x`/`hi_x` for the arithmetic (`omega`)
                lines.push(format!("  obtain ⟨w_{id}, e_{id}, lo_{id}, hi_{id}⟩ := shape_intIn {state} {q} _ _ {path}"));
                witness.insert(n.clone(), format!("w_{id}"));
                eqs.push(format!("e_{id}"));
            }
            Shape::Int => {
                lines.push(format!("  obtain ⟨w_{id}, e_{id}⟩ := shape_int {state} {q} {path}"));
                witness.insert(n.clone(), format!("w_{id}"));
                eqs.push(format!("e_{id}"));
            }
            Shape::Bool => {
                lines.push(format!("  obtain ⟨w_{id}, e_{id}⟩ := shape_bool {state} {q} {path}"));
                eqs.push(format!("e_{id}"));
            }
            Shape::Opt => {
                splits.push(format!("rcases shape_opt {state} {q} {path} with e_{id} | ⟨w_{id}, e_{id}⟩"));
                eqs.push(format!("e_{id}"));
            }
            Shape::Sum(_) => {
                lines.push(format!("  obtain ⟨w_{id}, p_{id}, e_{id}, c_{id}⟩ := shape_sum {state} {q} _ {path}"));
                eqs.push(format!("e_{id}"));
                eqs.push(format!("c_{id}"));
            }
        }
    }
    if let Some((v, k)) = extra_index {
        witness.insert(v.to_string(), k.to_string());
    }
    for (carrier, field, index, sh) in reads {
        let Some(w) = witness.get(index) else { continue };
        let place = format!("(.slot {} {w} {})", quoted(carrier), quoted(field));
        let id = format!("{carrier}_{field}_{}", index.replace('#', "_"));
        match sh {
            Shape::Int => lines.push(format!("  obtain ⟨n_{id}, h_{id}⟩ := WF_int shapeOf {state}.world {place} hwf rfl")),
            Shape::IntIn(..) => lines.push(format!("  obtain ⟨n_{id}, h_{id}, lo_{id}, hi_{id}⟩ := WF_intIn shapeOf {state}.world {place} _ _ hwf rfl")),
            Shape::Bool => lines.push(format!("  obtain ⟨n_{id}, h_{id}⟩ := WF_bool shapeOf {state}.world {place} hwf rfl")),
            Shape::Sum(_) => lines.push(format!("  obtain ⟨n_{id}, q_{id}, h_{id}, c_{id}⟩ := WF_sum shapeOf {state}.world {place} _ hwf rfl")),
            Shape::Opt => splits.push(format!("rcases WF_opt shapeOf {state}.world {place} hwf rfl with h_{id} | ⟨n_{id}, h_{id}⟩")),
        }
        eqs.push(format!("h_{id}"));
    }
    // **A record field read has a witness too** -- `.field "Text" "len"` is one place, and
    // the well-typed world gives it its shape without any index.
    for (carrier, field, sh) in record_reads {
        let place = format!("(.field {} {})", quoted(carrier), quoted(field));
        let id = format!("{}_{field}", carrier.replace(['.', ':', '#'], "_"));
        match sh {
            Shape::Int => lines.push(format!("  obtain ⟨n_{id}, h_{id}⟩ := WF_int shapeOf {state}.world {place} hwf rfl")),
            Shape::IntIn(..) => lines.push(format!("  obtain ⟨n_{id}, h_{id}, lo_{id}, hi_{id}⟩ := WF_intIn shapeOf {state}.world {place} _ _ hwf rfl")),
            Shape::Bool => lines.push(format!("  obtain ⟨n_{id}, h_{id}⟩ := WF_bool shapeOf {state}.world {place} hwf rfl")),
            Shape::Sum(_) => lines.push(format!("  obtain ⟨n_{id}, q_{id}, h_{id}, c_{id}⟩ := WF_sum shapeOf {state}.world {place} _ hwf rfl")),
            Shape::Opt => splits.push(format!("rcases WF_opt shapeOf {state}.world {place} hwf rfl with h_{id} | ⟨n_{id}, h_{id}⟩")),
        }
        eqs.push(format!("h_{id}"));
    }
    // **The hypothesis itself, as rewrites** -- a copy, so that the paths above (and the
    // case splits after them) still read the original. What the precondition or the
    // invariant says beyond the shapes -- the `requires`, the flag of a `return` inside
    // a loop -- becomes what `simp` and `simp_all` can use, instead of standing folded
    // under a name.
    let known: Vec<String> = eqs.iter().filter(|e| e.starts_with("e_") || e.starts_with("h_")).cloned().collect();
    let line_eqs: Vec<String> = known
        .iter()
        .filter(|e| !splits.iter().any(|sp| sp.contains(&format!(" {e} |")) || sp.contains(&format!("⟨n_{}, {e}⟩", &e[2..])) || sp.contains(&format!("⟨w_{}, {e}⟩", &e[2..]))))
        .cloned()
        .collect();
    let mut set = vec![hyp_def.to_string()];
    set.extend(line_eqs);
    lines.push(format!("  have hall := {hyp}"));
    lines.push(format!("  gabbro_simp_at hall [{}]", set.join(", ")));
    eqs.push("hall".to_string());
    (lines, splits, eqs)
}

fn loop_theorem(id: &str) -> String {
    format!("{}_keeps", lean_ident(id))
}

/// `f#1` -> `f_loop_1`.
fn lean_ident(id: &str) -> String {
    id.replace('#', "_loop_")
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

/// **The dependency order of the unit's theorems**: loops before their routine, callees
/// before callers. Returns the order, the CYCLES (a mutual recursion whose every member
/// declares a `decreases` and calls the cycle only outside its loops -- wired by one
/// induction, `contracts_of_duties_rec`), and, for every routine that cannot be wired,
/// the reason.
fn wiring_order(goals: &[RoutineGoal], all_routines: &BTreeSet<String>) -> (Vec<String>, Vec<Vec<String>>, BTreeMap<String, String>) {
    let names: BTreeSet<String> = goals.iter().filter(|g| g.body.is_ok()).map(|g| g.name.clone()).collect();
    let by_name: HashMap<&str, &RoutineGoal> = goals.iter().map(|g| (g.name.as_str(), g)).collect();
    // the edges among the routines with a body
    let edges = |n: &str| -> BTreeSet<String> {
        let g = by_name[n];
        g.callees
            .iter()
            .chain(g.loops.iter().flat_map(|l| l.callees.iter()))
            .filter(|c| names.contains(*c))
            .cloned()
            .collect()
    };
    // reachability, for the strongly connected components (the unit is small)
    let reach = |n: &str| -> BTreeSet<String> {
        let mut seen: BTreeSet<String> = BTreeSet::new();
        let mut stack: Vec<String> = edges(n).into_iter().collect();
        while let Some(x) = stack.pop() {
            if seen.insert(x.clone()) {
                stack.extend(edges(&x));
            }
        }
        seen
    };
    let reaches: HashMap<String, BTreeSet<String>> = names.iter().map(|n| (n.clone(), reach(n))).collect();
    let mut cycles: Vec<Vec<String>> = Vec::new();
    let mut in_cycle: HashMap<String, usize> = HashMap::new();
    for n in &names {
        if in_cycle.contains_key(n) {
            continue;
        }
        let mut members: Vec<String> = names
            .iter()
            .filter(|m| *m != n && reaches[n].contains(*m) && reaches[*m].contains(n))
            .cloned()
            .collect();
        if members.is_empty() {
            continue;
        }
        members.push(n.clone());
        members.sort();
        let idx = cycles.len();
        for m in &members {
            in_cycle.insert(m.clone(), idx);
        }
        cycles.push(members);
    }
    let mut unwired: BTreeMap<String, String> = BTreeMap::new();
    // a cycle is wired only where every member has a measure and calls the cycle outside
    // its loops
    let mut wired_cycles: Vec<Vec<String>> = Vec::new();
    let mut cycle_of: HashMap<String, usize> = HashMap::new();
    for members in &cycles {
        let ok = members.iter().all(|m| {
            let g = by_name[m.as_str()];
            g.decreases.is_some() && !g.loops.iter().any(|l| l.callees.iter().any(|c| members.contains(c)))
        });
        if ok {
            let idx = wired_cycles.len();
            for m in members {
                cycle_of.insert(m.clone(), idx);
            }
            wired_cycles.push(members.clone());
        } else {
            for m in members {
                let g = by_name[m.as_str()];
                let why = if g.decreases.is_none() {
                    "mutual recursion -- its `decreases` has no term"
                } else if g.loops.iter().any(|l| l.callees.iter().any(|c| members.contains(c))) {
                    "mutual recursion -- a call into the cycle stands inside a loop"
                } else {
                    "mutual recursion -- another member of the cycle cannot be wired"
                };
                unwired.insert(m.clone(), why.into());
            }
        }
    }
    let mut deps: HashMap<String, BTreeSet<String>> = HashMap::new();
    for g in goals {
        if g.body.is_err() {
            continue;
        }
        let mut d: BTreeSet<String> = BTreeSet::new();
        for c in g.callees.iter().chain(g.loops.iter().flat_map(|l| l.callees.iter())) {
            if !all_routines.contains(c) {
                continue;
            }
            if *c == g.name {
                // A direct self-recursion with a `decreases` is wired by induction over the
                // measure (`contract_of_duty_rec`); without one, or inside a loop, it is not.
                if cycle_of.contains_key(&g.name) {
                    continue;
                }
                if self_recursive(g) && g.decreases.is_some() {
                    continue;
                }
                // **A recursive call inside ONE loop of a flat routine is wired since
                // 2026-09-08** (`contract_of_duty_rec_loop_in`, `contract_of_duty_rec_loop`
                // where the loop has no index range): the induction over the `decreases` runs
                // outside the loop rule, and EVERY loop of the routine carries the measure.
                if rec_in_loop(g) {
                    continue;
                }
                let held: Vec<&LoopInfo> = g.loops.iter().filter(|l| l.callees.contains(&g.name)).collect();
                let why = if g.decreases.is_none() {
                    "recursion -- its `decreases` has no term; add one, and the induction \
                     over it is written for you"
                // **Nesting is asked FIRST, and the order is the diagnosis** (2026-09-08): a
                // loop's callee set includes the callees of the loops inside it, so a call in
                // an inner loop makes BOTH loops hold it -- and "several loops" would then be
                // the true sentence that sends a reader to the wrong place.
                } else if g.loops.iter().any(|l| !l.nested.is_empty()) {
                    "recursion -- a loop of the routine holds another loop, and the recursive \
                     call needs the measure carried across EVERY loop; the composition is \
                     written for a flat routine, not for a stack of rules"
                } else if held.len() > 1 {
                    "recursion -- the recursive call stands in SEVERAL loops of the routine; \
                     the induction composes the rule of one loop, not of two"
                } else if g.loops.iter().any(|l| l.passes.is_some()) {
                    "recursion -- a loop of the routine counts its passes, and its rule is a \
                     `LoopRuleP`; the composition takes a `LoopRule`"
                } else {
                    "recursion -- the recursive call stands in no loop this step can name"
                };
                unwired.insert(g.name.clone(), why.into());
            } else if !names.contains(c) {
                unwired.insert(g.name.clone(), format!("callee `{c}` refused"));
            } else if cycle_of.get(&g.name).is_some() && cycle_of.get(&g.name) == cycle_of.get(c) {
                // inside a wired cycle: not a dependency, the induction carries it
                continue;
            } else {
                d.insert(c.clone());
            }
        }
        deps.insert(g.name.clone(), d);
    }
    let mut order = Vec::new();
    let mut done: BTreeSet<String> = BTreeSet::new();
    loop {
        let mut progress = false;
        for n in &names {
            if done.contains(n) || unwired.contains_key(n) {
                continue;
            }
            // a cycle moves as one: every member's outside dependencies first
            let group: Vec<String> = match cycle_of.get(n) {
                Some(i) => wired_cycles[*i].clone(),
                None => vec![n.clone()],
            };
            let all_deps: BTreeSet<String> = group.iter().flat_map(|m| deps[m].iter().cloned()).collect();
            if all_deps.iter().all(|x| done.contains(x)) {
                for m in &group {
                    if !done.contains(m) {
                        order.push(m.clone());
                        done.insert(m.clone());
                    }
                }
                progress = true;
            } else if let Some(x) = all_deps.iter().find(|x| unwired.contains_key(*x)) {
                for m in &group {
                    unwired.insert(m.clone(), format!("callee `{x}` not wired"));
                }
                progress = true;
            }
        }
        if !progress {
            break;
        }
    }
    for n in &names {
        if !done.contains(n) && !unwired.contains_key(n) {
            unwired.insert(n.clone(), "mutual recursion -- a cycle over more than one name".into());
        }
    }
    (order, wired_cycles, unwired)
}

/// **Where a refusal really sits** (2026-09-08) -- and it is often not the clause the duty
/// names. `ensures result == puffer.e_eintritt` has a perfectly good term; what has none is
/// the `requires lenof(puffer) >= sizeof(Elf64Kopf)` of the same routine, and the whole
/// routine is refused with it. A reader who sees only `layout-buffer-length` next to the
/// `ensures` goes looking for a built-in in a clause that has none.
///
/// The same for a `table` invariant: it is owed by every routine that WRITES its carrier,
/// so one untranslatable writer refuses the invariant -- and the invariant's own term may
/// be right there in the file.
fn inherited_note(
    p: &crate::pflichten::Pflicht,
    r: LeanReason,
    goals: &[RoutineGoal],
    unit: &Unit,
) -> String {
    if let Some(g) = goals.iter().find(|g| g.name == p.funktion) {
        if g.body.as_ref().err().copied() == Some(r) {
            return format!(
                "\n      (inherited: this clause HAS a term; {} has none)",
                why_routine_refused(&p.funktion, r, unit)
            );
        }
    }
    let name = p.gegenstand.strip_prefix("invariant ").unwrap_or(&p.gegenstand);
    if let Some(inv) = unit.invariants.iter().find(|i| i.name == name) {
        if inv.term.is_ok() {
            if let Some(g) = goals
                .iter()
                .find(|g| g.body.as_ref().err().copied() == Some(r) && g.writes.iter().any(|w| inv.carriers.contains(w)))
            {
                return format!(
                    "\n      (inherited: this invariant HAS a term; `{}` writes its carrier and {} has none)",
                    g.name,
                    why_routine_refused(&g.name, r, unit)
                );
            }
        }
    }
    String::new()
}

/// **What in a routine has no term** -- so that the note above says the construct and not
/// only the routine. An invariant a routine must keep BECAUSE IT WRITES THE CARRIER is the
/// case that surprises: nothing in the routine's own text mentions it.
fn why_routine_refused(f: &str, r: LeanReason, unit: &Unit) -> String {
    if let Some(info) = unit.routines.get(f) {
        for m in &info.maintained {
            if let Some(inv) = unit.invariants.iter().find(|i| i.name == *m) {
                if inv.term.as_ref().err().copied() == Some(r) {
                    return format!(
                        "`{}` -- the invariant `{f}` must keep because it writes `{}`",
                        inv.name,
                        inv.carriers.join("`, `")
                    );
                }
            }
        }
    }
    format!("the body or the `requires` of `{f}`")
}

/// **The unit's obligation register, as a Lean 4 module.**
pub fn module(baum: &Programm, datei: &str) -> String {
    let unit = Unit::sammle(baum);
    let goals = routine_goals(&unit);
    let entries = verdicts_over(baum, &unit, &goals);
    let carried = entries.iter().filter(|(_, v)| v.is_goal()).count();
    let assumed = entries.iter().filter(|(_, v)| matches!(v, LeanVerdict::Assumed(_))).count();
    let refused = entries.len() - carried - assumed;
    let name = module_name(datei);
    let all_routines: BTreeSet<String> = unit.routines.keys().cloned().collect();
    let (order, cycles, unwired) = wiring_order(&goals, &all_routines);
    let cycle_of: HashMap<String, usize> = cycles
        .iter()
        .enumerate()
        .flat_map(|(i, ms)| ms.iter().map(move |m| (m.clone(), i)))
        .collect();
    let mut s = String::new();
    s.push_str("/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the\n");
    s.push_str("    `.gab`, and a second register over the same thing is the very class this\n");
    s.push_str("    folder is written against.\n\n");
    s.push_str("    Every obligation of the register appears below: CARRIED by a theorem of\n");
    s.push_str("    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or\n");
    s.push_str("    REFUSED by name. The line that has to add up:\n\n");
    // **The balance line keeps its shape** -- `goals + refused = total` -- and the assumptions
    // are counted INSIDE `refused`, then named on the line below: every reader of the header
    // (`zaehle-lean.py`, `zaehle-p6.py`, the probes) holds that one equation, and a third
    // column would have moved the equation under them.
    s.push_str(&format!(
        "        @duty 1  {datei}  total {}  goals {carried}  refused {}\n",
        entries.len(),
        refused + assumed
    ));
    s.push_str(&format!(
        "        @assumed {assumed}  of the refused are ASSUMPTIONS -- hardware, foreign code -- and {refused} are refused forms\n"
    ));
    s.push_str("\n    The meaning of a body is `Gabbro.Body`, written by hand and read by a\n");
    s.push_str("    person. What stands here is a DATUM of it -- this file defines nothing.\n\n");
    s.push_str("    WHAT A PERSON OWES: the `_statement` of every `_meets` and every `_keeps`\n");
    s.push_str("    theorem below. Each is proved by `gabbro_auto`, which closes what the\n");
    s.push_str("    model closes by computation and leaves a `sorry` on the rest -- and the\n");
    s.push_str("    rest is, by construction, the program's own logic: every hypothesis the\n");
    s.push_str("    proof can need stands in front of the turnstile. A person proves the\n");
    s.push_str("    statement in a file of their own and hands it to `unit_closed`.\n\n");
    s.push_str("    WHAT THE GENERATOR OWES, AND PAYS: the composition over every call\n");
    s.push_str("    (`Contract`, `Frame`), the rule of every loop (`LoopRule`), the\n");
    s.push_str("    precondition at every call site (the call gets stuck without it), and\n");
    s.push_str("    the wiring from the duties to the contracts (`unit_closed`).\n\n");
    s.push_str("    ASSUMED, and visible because it is written down: two different carrier\n");
    s.push_str("    names are two different objects (the alias passes carry it), and two\n");
    s.push_str("    objects of one record type are ONE object of the model (a record's\n");
    s.push_str("    places are named by its type, as a table's are); the\n");
    s.push_str("    declared `effects` list is complete (`E008`/`E010`, `Frame` in `Program`);\n");
    s.push_str("    the initial world satisfies every invariant (a statement about `boot`,\n");
    s.push_str("    booked by no register); and everything `Assumed` names.\n-/\n\n");
    s.push_str("import Gabbro.Body\n\n");
    // **The heartbeat budget is raised, and the reason is the automation.** `gabbro_auto`
    // runs a case split per undecided read and a `simp_all` per goal; a routine over a
    // `count 4096` table with three option reads spends the default budget before the
    // person's goal is even visible. Each step of the pipeline runs under its own budget
    // (`gabbro_try`, in the model), and the declaration's budget here is the sum of them --
    // a step that runs out leaves its goal, and the theorem does not go red.
    s.push_str("set_option autoImplicit false\nset_option maxHeartbeats 11300000\n\nopen Gabbro.Body\n\n");
    s.push_str(&format!("namespace GabbroDuty.{name}\n\n"));

    // ---- what is not here ---------------------------------------------------------------
    s.push_str("/-! ## What is NOT carried, and why -/\n\n");
    if refused == 0 && assumed == 0 {
        s.push_str("-- Every obligation of this unit is carried by a theorem below.\n\n");
    } else {
        s.push_str("/-\n  A duty that vanishes is noticed; one that gets weaker is not -- so each\n");
        s.push_str("  stands here with its reason.\n\n");
        for r in LeanReason::ALL {
            let mine: Vec<(usize, &crate::pflichten::Pflicht)> = entries
                .iter()
                .enumerate()
                .filter(|(_, (_, v))| matches!(v, LeanVerdict::Refused(x) | LeanVerdict::Assumed(x) if *x == r))
                .map(|(i, (p, _))| (i, p))
                .collect();
            if mine.is_empty() {
                continue;
            }
            let word = match r.kind() {
                Kind::Assumption => "ASSUMED",
                Kind::NoTerm => "refused",
                Kind::NoWiring => "not wired",
            };
            s.push_str(&format!("  {} ({}): {word} -- {}\n", r.tag(), mine.len(), r.sentence()));
            for (i, p) in mine {
                s.push_str(&format!(
                    "    duty_{}  {}  {} :: {}{}\n",
                    i + 1,
                    p.art.marke(),
                    p.funktion,
                    p.gegenstand,
                    inherited_note(p, r, &goals, &unit)
                ));
            }
            s.push('\n');
        }
        s.push_str("-/\n\n");
    }

    // ---- the register, obligation by obligation ---------------------------------------
    s.push_str("/-! ## The register, and which theorem carries each line -/\n\n");
    s.push_str("/-\n");
    for (i, (p, v)) in entries.iter().enumerate() {
        let by = match v {
            LeanVerdict::Carried(t) => format!("carried by `{t}`"),
            LeanVerdict::CarriedBy(ts) if ts.is_empty() => {
                "carried by no routine -- nothing in this unit writes the carrier".to_string()
            }
            LeanVerdict::CarriedBy(ts) => format!("carried by `{}`", ts.join("`, `")),
            LeanVerdict::Assumed(r) => format!("ASSUMED ({})", r.tag()),
            LeanVerdict::Refused(r) => format!("refused ({})", r.tag()),
        };
        s.push_str(&format!(
            "  duty_{}  {}  {} :: {}  --  {by}\n",
            i + 1,
            p.art.marke(),
            p.funktion,
            p.gegenstand
        ));
    }
    s.push_str("-/\n\n");

    // ---- the declared places ------------------------------------------------------------
    let mut dict: Vec<(String, String, Shape)> = Vec::new();
    let mut tnames: Vec<&String> = unit.tables.keys().collect();
    tnames.sort();
    for t in tnames {
        for (f, sh) in &unit.tables[t].fields {
            if let Some(sh) = sh {
                dict.push((t.clone(), f.clone(), *sh));
            }
        }
    }
    let mut rdict: Vec<(String, String, Shape)> = Vec::new();
    let mut rnames: Vec<&String> = unit.records.keys().collect();
    rnames.sort();
    for t in rnames {
        for (f, sh) in &unit.records[t] {
            if let Some(sh) = sh {
                rdict.push((t.clone(), f.clone(), *sh));
            }
        }
    }
    // **The ghost carriers of `let`-bound record VALUES** (2026-09-08) -- see
    // `Ctx::record_value`. A binding is not the one object of its type, so its fields are
    // named under a carrier of their own; the SHAPE is still the declared one, and
    // `wellFormed` is what carries it into a proof. **Nothing stores into these places**,
    // so a proof can read a `u32` off `c.len` and never a VALUE -- which is the whole of
    // what the checker knows about a record a call handed back.
    //
    // *They are read off the translated bodies (`routine_goals` ran above), not walked for
    // a second time*: a second walk would be a second register over one thing, and the
    // numbering of the carriers would have to agree with this one by hand.
    for g in &goals {
        for (carrier, field, sh) in &g.seen_records {
            if unit.records.contains_key(carrier) {
                continue;
            }
            if !rdict.iter().any(|(t, f, _)| t == carrier && f == field) {
                rdict.push((carrier.clone(), field.clone(), *sh));
            }
        }
    }
    s.push_str("/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/\n\n");
    s.push_str("/-- The shape every declared place carries, read from the declarations. -/\n");
    s.push_str("def shapeOf : Typing := fun p =>\n  match p with\n");
    for (t, f, sh) in &dict {
        s.push_str(&format!("  | .slot {} _ {} => some {}\n", quoted(t), quoted(f), sh.lean()));
    }
    for (t, f, sh) in &rdict {
        s.push_str(&format!("  | .field {} {} => some {}\n", quoted(t), quoted(f), sh.lean()));
    }
    for (n, sh) in &unit.statics_scalars {
        s.push_str(&format!("  | .global {} => some {}\n", quoted(n), sh.lean()));
    }
    s.push_str("  | _ => none\n\n");
    s.push_str("def wellFormed (s : State) : Prop := WF shapeOf s.world\n\n");

    // ---- the invariants ---------------------------------------------------------------
    let any_inv = unit.invariants.iter().any(|i| i.term.is_ok());
    if any_inv {
        s.push_str("/-! ## The invariants of the unit, as expressions -/\n\n");
        for inv in &unit.invariants {
            if let Ok(t) = &inv.term {
                s.push_str(&format!("/-- `{}` over `{}`. -/\n", inv.name, inv.carriers.join("`, `")));
                s.push_str(&format!("def inv_{} : Expr :=\n  {t}\n\n", inv.name));
            }
        }
    }

    // ---- the foreign contracts --------------------------------------------------------
    let mut assumed_parts: Vec<String> = Vec::new();
    let used_foreign: BTreeSet<String> = goals
        .iter()
        .flat_map(|g| g.callees.iter().chain(g.loops.iter().flat_map(|l| l.callees.iter())))
        .filter(|c| unit.foreign.contains_key(*c) || unit.transitions.contains_key(*c) || unit.ops.contains_key(*c))
        .cloned()
        .collect();
    if !used_foreign.is_empty() {
        s.push_str("/-! ## What is ASSUMED about callees no body of this unit defines -/\n\n");
        for c in &used_foreign {
            if let Some(f) = unit.foreign.get(c) {
                s.push_str(&format!("/-- `{c}` -- a foreign body: its contract is an assumption. -/\n"));
                s.push_str(&format!("def {c}_pre : Expr :=\n  {}\n\n", f.pre.clone().unwrap_or_else(|| "(.lit (.bool true))".into())));
                s.push_str(&format!("def {c}_post (t t' : State) (r : Option Value) : Prop :=\n"));
                // **`-> never` never returns**: what follows a call to it is unreachable,
                // and the promise says so -- `False`. The model's `ρ f` still answers a
                // state; the contract makes every statement after the call vacuous.
                let mut ps = if f.never { vec!["False".to_string()] } else { vec!["wellFormed t'".to_string()] };
                if let Some(cl) = result_clause(f.result, f.result_range, f.fehler, f.has_result, "r") {
                    ps.push(cl);
                }
                ps.extend(f.post.iter().cloned());
                s.push_str(&format!("  {}\n\n", ps.join("\n  ∧ ")));
                s.push_str(&format!("def {c}_writes : List String := [{}]\n\n", f.writes.iter().map(|w| quoted(w)).collect::<Vec<_>>().join(", ")));
                s.push_str(&format!("def {c}_requires (t : State) : Prop := wellFormed t ∧ eval t {c}_pre = some (.bool true)\n\n"));
                assumed_parts.push(format!("Contract ρ {} {c}_requires {c}_post", quoted(c)));
                assumed_parts.push(format!("Frame ρ {} {c}_writes", quoted(c)));
            } else if let Some(t) = unit.transitions.get(c) {
                s.push_str(&format!("/-- `{c}` -- a `transition` of `{}`: a register write behind a frame. -/\n", t.device));
                s.push_str(&format!("def {c}_pre : Expr :=\n  {}\n\n", t.pre.clone().unwrap_or_else(|| "(.lit (.bool true))".into())));
                s.push_str(&format!("def {c}_post (_t t' : State) (_r : Option Value) : Prop :=\n  wellFormed t'\n\n"));
                s.push_str(&format!("def {c}_writes : List String := [{}]\n\n", quoted(&t.device)));
                s.push_str(&format!("def {c}_requires (t : State) : Prop := wellFormed t ∧ eval t {c}_pre = some (.bool true)\n\n"));
                assumed_parts.push(format!("Contract ρ {} {c}_requires {c}_post", quoted(c)));
                assumed_parts.push(format!("Frame ρ {} {c}_writes", quoted(c)));
            } else if let Some(op) = unit.ops.get(c) {
                let id = c.replace("::", "_");
                s.push_str(&format!("/-- `{c}` -- a generated operation: its premises are the schema `opsruf` cuts,\n    and that it preserves the table's invariants is `table.ops.erhaltung`. -/\n"));
                s.push_str(&format!("def {id}_pre : Expr :=\n  {}\n\n", op.pre.clone().unwrap_or_else(|| "(.lit (.bool true))".into())));
                s.push_str(&format!("def {id}_post (t t' : State) (_r : Option Value) : Prop :=\n"));
                let mut ps = vec!["wellFormed t'".to_string()];
                for inv in &unit.invariants {
                    if inv.term.is_ok() && inv.carriers.contains(&op.table) {
                        ps.push(format!("(eval t inv_{n} = some (.bool true) → eval t' inv_{n} = some (.bool true))", n = inv.name));
                    }
                }
                s.push_str(&format!("  {}\n\n", ps.join("\n  ∧ ")));
                s.push_str(&format!("def {id}_writes : List String := [{}]\n\n", quoted(&op.table)));
                s.push_str(&format!("def {id}_requires (t : State) : Prop := wellFormed t ∧ eval t {id}_pre = some (.bool true)\n\n"));
                assumed_parts.push(format!("Contract ρ {} {id}_requires {id}_post", quoted(c)));
                assumed_parts.push(format!("Frame ρ {} {id}_writes", quoted(c)));
            }
        }
    }
    // **The initial state** -- what `boot` owes and no register books: that the world is
    // well-typed and every invariant of the unit holds before the first routine runs. It is
    // stated here as a definition so that a specification can name it, and it stands in the
    // header as an assumption -- a proof of it is a statement about the initialisers, and
    // this channel sees none.
    s.push_str("/-- **The initial state** -- what `boot` owes: a well-typed world in which every\n    invariant of the unit holds. No register books it; it is named here so that it can\n    be assumed BY NAME and not by omission. -/\n");
    s.push_str("def Initially (s0 : State) : Prop :=\n  wellFormed s0");
    for inv in &unit.invariants {
        if inv.term.is_ok() {
            s.push_str(&format!("\n  ∧ eval s0 inv_{} = some (.bool true)", inv.name));
        }
    }
    s.push_str("\n\n");
    s.push_str("/-- **What is assumed of the environment beyond the bodies of this unit.** -/\n");
    s.push_str("def Assumed (ρ : Env) : Prop :=\n");
    if assumed_parts.is_empty() {
        s.push_str("  True\n\n");
    } else {
        s.push_str(&format!("  {}\n\n", assumed_parts.join("\n  ∧ ")));
    }

    // ---- the routines -------------------------------------------------------------------
    let pre_name = |f: &str| format!("{f}_pre");
    let post_name = |f: &str| format!("{f}_post");
    let writes_name = |f: &str| format!("{f}_writes");
    let callee_id = |c: &str| c.replace("::", "_");
    // **Every contract first, every duty after** -- a caller's statement names its callee's
    // contract, and a mutual recursion names it in both directions; declaration order
    // would put one of the two before its definition.
    s.push_str("/-! ## The routines: body and contract -/\n\n");
    for g in &goals {
        s.push_str(&format!("/-! ### `{}` -/\n\n", g.name));
        let refused = g.body.as_ref().err().copied();
        if let Some(reason) = refused {
            s.push_str(&format!("-- REFUSED  {}  ({}): {}\n--   Its contract stands below all the same, so that a caller's theorem can name it;\n--   what is missing is the theorem that discharges it.\n\n", g.name, reason.tag(), reason.sentence()));
        }
        if let Ok(body) = &g.body {
            s.push_str(&format!("def {}_body : List Stmt :=\n  {body}\n\n", g.name));
        }
        s.push_str(&format!("/-- The precondition: the declared shapes and the `requires`. -/\n"));
        s.push_str(&format!(
            "def {} : Expr :=\n  {}\n\n",
            pre_name(&g.name),
            unit.pre_of.get(&g.name).and_then(|p| p.clone().ok()).unwrap_or_else(|| "(.lit (.bool true))".into())
        ));
        for (n, t) in &g.keeps {
            s.push_str(&format!("/-- `{n}`, as `{}` keeps it. -/\ndef {}_inv_{n} : Expr :=\n  {t}\n\n", g.name, g.name));
        }
        s.push_str(&format!("def {} : List String := [{}]\n\n", writes_name(&g.name), g.writes.iter().map(|w| quoted(w)).collect::<Vec<_>>().join(", ")));
        s.push_str(&format!("/-- What a caller of `{}` has to bring: a well-typed world and the precondition. -/\n", g.name));
        s.push_str(&format!("def {n}_requires (t : State) : Prop := wellFormed t ∧ eval t {n}_pre = some (.bool true)\n\n", n = g.name));
        s.push_str(&format!("/-- What `{}` PROMISES: the world stays well-typed, every invariant it maintains\n    survives, and its `ensures` hold -- over the entry state (`old`), the exit state\n    and the result. -/\n", g.name));
        s.push_str(&format!("def {} (s s' : State) (r : Option Value) : Prop :=\n", post_name(&g.name)));
        let mut ps = vec!["wellFormed s'".to_string()];
        {
            let r = &unit.routines[&g.name];
            if let Some(cl) = result_clause(
                unit.result_shape.get(&g.name).copied().flatten(),
                unit.result_range.get(&g.name).copied().flatten(),
                r.decl.fehler.is_some(),
                r.decl.ergebnis.is_some() && !matches!(r.decl.ergebnis, Some(TypExpr::Never(_))),
                "r",
            ) {
                ps.push(format!("-- the answer: a value of the declared shape\n  {cl}"));
            }
        }
        for (n, _) in &g.keeps {
            ps.push(format!("eval s' {}_inv_{n} = some (.bool true)", g.name));
        }
        for (origin, p) in &g.post {
            if let Ok(p) = p {
                ps.push(format!("-- {origin}\n  {p}"));
            } else {
                ps.push(format!("-- {origin}: NOT SAID ({}) -- a promise fewer makes a caller's goal harder, never wrong\n  True", p.as_ref().err().unwrap().tag()));
            }
        }
        s.push_str(&format!("  {}\n\n", ps.join("\n  ∧ ")));
        if refused.is_some() {
            continue;
        }
        if let Some(m) = &g.decreases {
            s.push_str(&format!("/-- The measure of `{}` -- what its `decreases` names; a recursive call is\n    below the current state in it. -/\n", g.name));
            s.push_str(&format!("def {}_decreases : Expr :=\n  {m}\n\n", g.name));
        }
    }

    s.push_str("/-! ## The duties: one statement per routine and per loop -/\n\n");
    for g in &goals {
        if g.body.is_err() {
            continue;
        }
        s.push_str(&format!("/-! ### `{}` -/\n\n", g.name));

        // **A routine whose recursive call stands inside its loop** (2026-09-08): the loop's
        // pass gets the bounded self-contract at the ROUTINE's entry state `s0`, and owes
        // that the measure at the end of the pass is still the one at `s0`. See `rec_in_loop`.
        let ril = rec_in_loop(g) && cycle_of.get(&g.name).is_none();

        // The loops, innermost first (they are pushed as they close).
        for l in &g.loops {
            let lid = lean_ident(&l.id);
            s.push_str(&format!("/-- Loop `{}` of `{}`: its body and its invariant (with the shapes of the locals in scope). -/\n", l.id, g.name));
            s.push_str(&format!("def {lid}_inv : Expr :=\n  {}\n\n", l.inv));
            s.push_str(&format!("def {lid}_body : List Stmt :=\n  {}\n\n", l.body));
            // The loop's theorem.
            let mut hyps: Vec<(String, String, String)> = Vec::new();
            if let Some((lo, hi)) = l.range {
                hyps.push(("hlo".into(), format!("{} ≤ k", int_lit(lo)), "the index is in the loop's range".into()));
                hyps.push(("hhi".into(), format!("k < {}", int_lit(hi)), "the index is in the loop's range".into()));
            }
            // **The pass counter** (agent b, 2026-09-08): this is the `i`-th pass of at most
            // `np`, and the ghost local says so.
            if let Some(np) = l.passes {
                hyps.push(("hplo".into(), "0 ≤ i".into(), "this is the `i`-th pass".into()));
                hyps.push(("hphi".into(), format!("i < {}", int_lit(np)), "the loop runs at most `count` passes".into()));
                hyps.push((
                    "hpass".into(),
                    format!("t.local' {} = .int i", quoted(crate::PASSZAEHLER_LEAN)),
                    "the counter stands at the number of passes already done".into(),
                ));
            }
            hyps.push(("hwf".into(), "wellFormed t".into(), "the well-formed world".into()));
            // **EVERY loop of the routine carries the measure, not only the one that holds
            // the call** (2026-09-08). Measured on `probe-rekursion-zwei-schleifen`: with the
            // measure carried only by the recursive loop, one goal stood in `faerben_meets`
            // -- `x = w_n`, the value of `n` AFTER the first loop against its value at entry.
            // A `LoopRule` says nothing about the locals, so as far as the model knew, a loop
            // in front of the recursive one could have moved the measure. It cannot: its
            // body does not touch `n`, and that is a fact its own pass proves.
            let ril_here = ril;
            if ril_here {
                hyps.push((
                    "s0".into(),
                    "State".into(),
                    "the ROUTINE's entry state -- what the induction over `decreases` bounds by".into(),
                ));
                hyps.push((
                    "hmeas".into(),
                    format!("eval t {}_decreases = eval s0 {}_decreases", g.name, g.name),
                    "the measure is still the one the routine entered with".into(),
                ));
            }
            hyps.push(("hinv".into(), format!("eval t {lid}_inv = some (.bool true)"), "the invariant at the start of the pass".into()));
            for c in &l.callees {
                let cid = callee_id(c);
                if ril_here && *c == g.name {
                    // **The bounded self-contract, at the routine's entry state** -- the pass
                    // runs inside the induction over the measure, so what it may assume about
                    // its own recursive call is the contract on states strictly below `s0`.
                    hyps.push((
                        format!("c_{cid}"),
                        format!("ContractBelow ρ {} {cid}_decreases s0 {cid}_requires {cid}_post", quoted(c)),
                        format!("the contract of `{c}` itself, below the routine's entry state in its `decreases`"),
                    ));
                } else {
                    hyps.push((format!("c_{cid}"), format!("Contract ρ {} {cid}_requires {cid}_post", quoted(c)), format!("the contract of `{c}`")));
                }
                hyps.push((format!("fr_{cid}"), format!("Frame ρ {} {cid}_writes", quoted(c)), format!("the frame of `{c}`")));
            }
            for n in &l.nested {
                let nid = lean_ident(n);
                let ty = g
                    .loops
                    .iter()
                    .find(|x| x.id == *n)
                    .map_or_else(|| format!("LoopRule ρ {} wellFormed {nid}_inv", quoted(n)), |x| loop_rule_type(x, "wellFormed"));
                hyps.push((format!("l_{nid}"), ty, format!("the rule of loop `{n}`")));
            }
            let after = if ril_here {
                format!(
                    "(wellFormed t' ∧ eval t' {}_decreases = eval s0 {}_decreases)",
                    g.name, g.name
                )
            } else {
                "wellFormed t'".to_string()
            };
            let concl = format!(
                "∃ t', finalState (exec ρ {lid}_body {{ t with local' := bindLocal t.local' {} (.int k) }}) = some t'\n        ∧ {after} ∧ eval t' {lid}_inv = some (.bool true){}",
                quoted(&l.var),
                match l.passes {
                    Some(_) => format!(
                        "\n        ∧ t'.local' {} = .int (i + 1)",
                        quoted(crate::PASSZAEHLER_LEAN)
                    ),
                    None => String::new(),
                }
            );
            s.push_str(&format!("/-- **The loop rule of `{}`, as a statement over one pass.** -/\n", l.id));
            let pass_binder = if l.passes.is_some() { " (i : Int)" } else { "" };
            s.push_str(&format!("def {lid}_keeps_statement : Prop :=\n  ∀ (ρ : Env) (t : State) (k : Int){pass_binder}"));
            for (lbl, term, _) in &hyps {
                s.push_str(&format!("\n    ({lbl} : {term})"));
            }
            s.push_str(&format!(",\n    {concl}\n\n"));
            s.push_str(&format!("theorem {lid}_keeps : {lid}_keeps_statement := by\n  unfold {lid}_keeps_statement\n  intro ρ t k{}", if l.passes.is_some() { " i" } else { "" }));
            for (lbl, _, _) in &hyps {
                s.push_str(&format!(" {lbl}"));
            }
            s.push_str("\n  simp only [wellFormed] at hwf ⊢\n");
            let invs: Vec<(usize, String, String)> = g
                .keeps
                .iter()
                .enumerate()
                .map(|(j, (n, _))| (l.shapes.len() + j, n.clone(), format!("{}_inv_{n}", g.name)))
                .collect();
            let (lines, splits, eqs) = openings("t", "hinv", &format!("{lid}_inv"), &l.shapes, l.parts, &l.reads, Some((&l.var, "k")), &invs, &l.ranges, &l.records);
            for z in &lines {
                s.push_str(z);
                s.push('\n');
            }
            let mut set = format!("{lid}_body, {lid}_inv, wellFormed");
            if ril_here {
                // **The measure equation, opened like the invariant is.** Measured
                // 2026-09-08: without this line the pass left exactly one goal --
                // `Value.int w_n = s0.local' "n"` -- which IS `hmeas` with the measure
                // unfolded and the parameter's witness applied. A hypothesis the pipeline
                // cannot see through is a hypothesis the person is asked for.
                let mut me = format!("{}_decreases", g.name);
                for e in &eqs {
                    me.push_str(&format!(", {e}"));
                }
                // **`.symm`, and the direction is the whole point** (measured 2026-09-08):
                // as `eval t e = eval s0 e` the rewrite runs the WRONG way -- `s0.local' "n"`
                // replaces the witness in every other hypothesis, and the pass stops
                // computing. Turned round, `s0` is what disappears.
                s.push_str(&format!("  have hmeas' := hmeas.symm\n  gabbro_simp_at hmeas' [{me}]\n"));
                set.push_str(&format!(", {}_decreases, hmeas'", g.name));
            }
            for c in &l.callees {
                let cid = callee_id(c);
                set.push_str(&format!(", {cid}_pre, {cid}_requires, {cid}_post, {cid}_writes, Frame_read _ _ _ fr_{cid}"));
            }
            for n in &l.nested {
                let nid = lean_ident(n);
                set.push_str(&format!(", {nid}_inv"));
            }
            for e in &eqs {
                set.push_str(&format!(", {e}"));
            }
            if l.passes.is_some() {
                set.push_str(", hpass");
            }
            let tactic = format!("gabbro_auto [{set}] using shapeOf");
            if splits.is_empty() {
                s.push_str(&format!("  {tactic}\n\n"));
            } else {
                s.push_str(&format!("  {}\n    <;> {tactic}\n\n", splits.join(" <;>\n    ")));
            }
        }

        // The routine's theorem.
        let in_cycle = cycle_of.get(&g.name).copied();
        let rec_measure = if (self_recursive(g) || ril) && in_cycle.is_none() { g.decreases.as_deref() } else { None };
        let mut hyps: Vec<(String, String, String)> = Vec::new();
        hyps.push(("hwf".into(), "wellFormed s".into(), "the well-formed world (`U2`)".into()));
        hyps.push(("hpre".into(), format!("eval s {} = some (.bool true)", pre_name(&g.name)), "the declared shapes, the `requires`, the invariants it maintains".into()));
        for c in &g.callees {
            let cid = callee_id(c);
            if in_cycle.is_some() && cycle_of.get(c).copied() == in_cycle {
                // **A member of the same cycle**: its contract, bounded by this routine's
                // measure -- what the induction over the cycle (`contracts_of_duties_rec`)
                // hands down.
                hyps.push((
                    format!("c_{cid}"),
                    format!(
                        "ContractBelowM ρ ⟨{}, {cid}_body, {cid}_requires, {cid}_post, {cid}_decreases⟩ {}_decreases s",
                        quoted(c),
                        g.name
                    ),
                    format!("the contract of `{c}` (the same cycle), below `s` in this routine's `decreases`"),
                ));
            } else if *c == g.name && rec_measure.is_some() {
                // **The bounded self-contract**: the routine's own contract, for every state
                // strictly below the current one in the measure. The induction that turns it
                // into the full contract is `contract_of_duty_rec`, in `unit_closed`.
                hyps.push((
                    format!("c_{cid}"),
                    format!("ContractBelow ρ {} {cid}_decreases s {cid}_requires {cid}_post", quoted(c)),
                    format!("the contract of `{c}` itself, below `s` in its `decreases`"),
                ));
            } else {
                hyps.push((format!("c_{cid}"), format!("Contract ρ {} {cid}_requires {cid}_post", quoted(c)), format!("the contract of `{c}`")));
            }
            hyps.push((format!("fr_{cid}"), format!("Frame ρ {} {cid}_writes", quoted(c)), format!("the frame of `{c}`")));
        }
        for l in &g.loops {
            let lid = lean_ident(&l.id);
            // **The loop of a routine that recurses inside it carries the measure** -- its
            // rule holds for states that agree with `s` in the `decreases`, and that is what
            // lets the pass use the bounded self-contract at `s` (`rec_in_loop`).
            let wf = if ril {
                format!("(fun u => wellFormed u ∧ eval u {n}_decreases = eval s {n}_decreases)", n = g.name)
            } else {
                "wellFormed".to_string()
            };
            hyps.push((format!("l_{lid}"), loop_rule_type(l, &wf), format!("the rule of loop `{}`", l.id)));
        }
        let concl = format!(
            "∃ s', finalState (exec ρ {n}_body s) = some s'\n        ∧ {n}_post s s' (finalValue (exec ρ {n}_body s))",
            n = g.name
        );
        s.push_str(&format!("/-- **The duty of `{}`**: under its precondition, the body runs to an end and\n    keeps its promise. Every `ensures`, every `V` at its call sites and every\n    invariant it maintains is this one theorem. -/\n", g.name));
        s.push_str(&format!("def {}_meets_statement : Prop :=\n  ∀ (ρ : Env) (s : State)", g.name));
        for (lbl, term, origin) in &hyps {
            s.push_str(&format!("\n    -- {origin}\n    ({lbl} : {term})"));
        }
        s.push_str(&format!(",\n    {concl}\n\n"));
        s.push_str(&format!("theorem {n}_meets : {n}_meets_statement := by\n  unfold {n}_meets_statement\n  intro ρ s", n = g.name));
        for (lbl, _, _) in &hyps {
            s.push_str(&format!(" {lbl}"));
        }
        s.push_str("\n  simp only [wellFormed] at hwf ⊢\n");
        let (nshapes, nreq, ninv) = unit.pre_parts.get(&g.name).copied().unwrap_or((0, 0, 0));
        let parts = nshapes + nreq + ninv;
        let invs: Vec<(usize, String, String)> = g
            .keeps
            .iter()
            .enumerate()
            .map(|(j, (n, _))| (nshapes + nreq + j, n.clone(), format!("{}_inv_{n}", g.name)))
            .collect();
        let (lines, splits, eqs) = openings("s", "hpre", &pre_name(&g.name), &g.shaped_params, parts, &g.option_reads, None, &invs, &g.ranges, &g.seen_records);
        for z in &lines {
            s.push_str(z);
            s.push('\n');
        }
        let mut set = format!("{n}_body, {n}_pre, {n}_post, wellFormed", n = g.name);
        for (n, _) in &g.keeps {
            set.push_str(&format!(", {}_inv_{n}", g.name));
        }
        for c in &g.callees {
            let cid = callee_id(c);
            set.push_str(&format!(", {cid}_pre, {cid}_requires, {cid}_post, {cid}_writes, Frame_read _ _ _ fr_{cid}"));
            if (*c == g.name && rec_measure.is_some()) || (in_cycle.is_some() && cycle_of.get(c).copied() == in_cycle) {
                set.push_str(&format!(", {cid}_decreases, {}_decreases", g.name));
            }
        }
        for l in &g.loops {
            set.push_str(&format!(", {}_inv", lean_ident(&l.id)));
        }
        for e in &eqs {
            set.push_str(&format!(", {e}"));
        }
        let tactic = format!("gabbro_auto [{set}] using shapeOf");
        if splits.is_empty() {
            s.push_str(&format!("  {tactic}\n\n"));
        } else {
            s.push_str(&format!("  {}\n    <;> {tactic}\n\n", splits.join(" <;>\n    ")));
        }
    }

    // ---- the wiring ---------------------------------------------------------------------
    s.push_str("/-! ## The wiring -- what the generator owes, and pays\n\n");
    s.push_str("    `Program ρ` says the environment runs the bodies of this unit. From it and\n");
    s.push_str("    the duty statements, `unit_closed` yields every contract and every loop rule\n");
    s.push_str("    -- in dependency order, so that no person writes the induction over the\n");
    s.push_str("    call graph or over the passes of a loop. -/\n\n");
    let mut prog_parts: Vec<(String, String)> = Vec::new();
    for g in &goals {
        if g.body.is_err() {
            continue;
        }
        prog_parts.push((format!("r_{}", g.name), format!("Runs ρ {} {}_body", quoted(&g.name), g.name)));
        prog_parts.push((format!("fr_{}", g.name), format!("Frame ρ {} {}_writes", quoted(&g.name), g.name)));
        for l in &g.loops {
            let lid = lean_ident(&l.id);
            match l.range {
                Some((lo, hi)) => prog_parts.push((
                    format!("rl_{lid}"),
                    match l.passes {
                        Some(np) => format!(
                            "RunsLoopN ρ {} {lid}_body {} {} {} {}",
                            quoted(&l.id), quoted(&l.var), int_lit(lo), int_lit(hi), int_lit(np)
                        ),
                        None => format!("RunsLoopIn ρ {} {lid}_body {} {} {}", quoted(&l.id), quoted(&l.var), int_lit(lo), int_lit(hi)),
                    },
                )),
                None => prog_parts.push((format!("rl_{lid}"), format!("RunsLoop ρ {} {lid}_body {}", quoted(&l.id), quoted(&l.var)))),
            }
        }
    }
    s.push_str("def Program (ρ : Env) : Prop :=\n");
    if prog_parts.is_empty() {
        s.push_str("  True\n\n");
    } else {
        s.push_str(&format!("  {}\n\n", prog_parts.iter().map(|(_, t)| t.clone()).collect::<Vec<_>>().join("\n  ∧ ")));
    }
    // The statements the wiring takes, and what it yields.
    let wired: Vec<&RoutineGoal> = order.iter().filter_map(|n| goals.iter().find(|g| g.name == *n)).collect();
    if !unwired.is_empty() {
        s.push_str("/-  NOT WIRED -- the duty is stated above; the step from it to the contract is not:\n");
        for (n, why) in &unwired {
            s.push_str(&format!("      {n}: {why}\n"));
        }
        s.push_str("    Each line above names the construct and the way out. What IS wired: a\n");
        s.push_str("    self-recursion, by induction over its `decreases` (`contract_of_duty_rec`);\n");
        s.push_str("    a cycle of routines, over their shared measure (`contracts_of_duties_rec`);\n");
        s.push_str("    a recursive call inside ONE loop of a flat routine, by the induction\n");
        s.push_str("    outside the loop rule, with the measure carried across every loop\n");
        s.push_str("    (`contract_of_duty_rec_loop_in`, `contract_of_duty_rec_loop` for a loop\n");
        s.push_str("    with no index range, 2026-09-08). A caller of a REFUSED\n");
        s.push_str("    callee has no contract to compose with: the callee's refusal above is the\n");
        s.push_str("    line to read, and fixing it wires the caller too. -/\n\n");
    }
    let mut yields: Vec<String> = Vec::new();
    for g in &wired {
        for l in &g.loops {
            yields.push(loop_rule_type(l, "wellFormed"));
        }
        yields.push(format!("Contract ρ {} {}_requires {}_post", quoted(&g.name), g.name, g.name));
    }
    s.push_str("theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)");
    for g in &wired {
        for l in &g.loops {
            let lid = lean_ident(&l.id);
            s.push_str(&format!("\n    (d_{lid} : {lid}_keeps_statement)"));
        }
        s.push_str(&format!("\n    (d_{n} : {n}_meets_statement)", n = g.name));
    }
    if yields.is_empty() {
        s.push_str(" :\n    True := by\n  trivial\n\n");
    } else {
        s.push_str(&format!(" :\n    {} := by\n", yields.join("\n    ∧ ")));
        // open the bundles
        if !prog_parts.is_empty() {
            s.push_str(&format!("  obtain ⟨{}⟩ := hp\n", prog_parts.iter().map(|(l, _)| l.clone()).collect::<Vec<_>>().join(", ")));
        }
        if !assumed_parts.is_empty() {
            let labels: Vec<String> = used_foreign
                .iter()
                .flat_map(|c| {
                    let cid = callee_id(c);
                    vec![format!("c_{cid}"), format!("fr_{cid}")]
                })
                .collect();
            s.push_str(&format!("  obtain ⟨{}⟩ := ha\n", labels.join(", ")));
        }
        for g in &wired {
            let ril = rec_in_loop(g) && cycle_of.get(&g.name).is_none();
            // innermost loops first: `loop_infos` is pushed as loops close, so the order is
            // already innermost-first for nesting.
            for l in &g.loops {
                if ril {
                    // **No rule of THIS routine can be built before the contract.** The loop
                    // that holds the recursive call needs the bounded self-contract, which
                    // only the induction hands down; and every other loop of the routine now
                    // carries the measure against the routine's ENTRY state, which is not in
                    // scope here either. Both are built below.
                    continue;
                }
                let lid = lean_ident(&l.id);
                let mut args = Vec::new();
                for c in &l.callees {
                    let cid = callee_id(c);
                    args.push(format!("c_{cid}"));
                    args.push(format!("fr_{cid}"));
                }
                for n in &l.nested {
                    args.push(format!("l_{}", lean_ident(n)));
                }
                match l.range {
                    Some((lo, hi)) if l.passes.is_some() => s.push_str(&format!(
                        "  have l_{lid} : {} :=\n    looprule_of_body_p ρ {} wellFormed {lid}_inv {lid}_body {} {} {} {} {} rl_{lid}\n      (fun t k i hlo hhi hplo hphi hpass hw hin => d_{lid} ρ t k i hlo hhi hplo hphi hpass hw hin{})\n",
                        loop_rule_type(l, "wellFormed"),
                        quoted(&l.id),
                        quoted(&l.var),
                        quoted(crate::PASSZAEHLER_LEAN),
                        int_lit(lo),
                        int_lit(hi),
                        int_lit(l.passes.unwrap()),
                        args.iter().map(|a| format!(" {a}")).collect::<String>()
                    )),
                    Some((lo, hi)) => s.push_str(&format!(
                        "  have l_{lid} : LoopRule ρ {} wellFormed {lid}_inv :=\n    looprule_of_body_in ρ {} wellFormed {lid}_inv {lid}_body {} {} {} rl_{lid}\n      (fun t k hlo hhi hw hi => d_{lid} ρ t k hlo hhi hw hi{})\n",
                        quoted(&l.id),
                        quoted(&l.id),
                        quoted(&l.var),
                        int_lit(lo),
                        int_lit(hi),
                        args.iter().map(|a| format!(" {a}")).collect::<String>()
                    )),
                    None => s.push_str(&format!(
                        "  have l_{lid} : LoopRule ρ {} wellFormed {lid}_inv :=\n    looprule_of_body ρ {} wellFormed {lid}_inv {lid}_body {} rl_{lid}\n      (fun t k hw hi => d_{lid} ρ t k hw hi{})\n",
                        quoted(&l.id),
                        quoted(&l.id),
                        quoted(&l.var),
                        args.iter().map(|a| format!(" {a}")).collect::<String>()
                    )),
                }
            }
            let in_cycle = cycle_of.get(&g.name).copied();
            let recursive = self_recursive(g) && g.decreases.is_some() && in_cycle.is_none();
            let member = |m: &str| {
                format!("⟨{}, {m}_body, {m}_requires, {m}_post, {m}_decreases⟩", quoted(m))
            };
            let mut args = Vec::new();
            for c in &g.callees {
                let cid = callee_id(c);
                // the self-contract is what the induction hands down, not a hypothesis --
                // and so is the contract of a cycle member, from the cycle's induction
                if in_cycle.is_some() && cycle_of.get(c).copied() == in_cycle {
                    args.push(format!("(hrec {} (by simp))", member(c)));
                } else if *c == g.name && recursive {
                    args.push("hrec".to_string());
                } else {
                    args.push(format!("c_{cid}"));
                }
                args.push(format!("fr_{cid}"));
            }
            for l in &g.loops {
                args.push(format!("l_{}", lean_ident(&l.id)));
            }
            if let Some(ci) = in_cycle {
                // **The cycle, once**: on its first member the induction over all of them,
                // and every member's contract is one instance of it.
                let members = &cycles[ci];
                if members.first() == Some(&g.name) {
                    let list: Vec<String> = members.iter().map(|m| member(m)).collect();
                    s.push_str(&format!("  have cyc_{ci} := contracts_of_duties_rec ρ [{}]\n", list.join(", ")));
                    s.push_str("    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr\n");
                    let runs: Vec<String> = members.iter().map(|m| format!("r_{m}")).collect();
                    s.push_str(&format!("        rcases hr with {} <;> assumption)\n", members.iter().map(|_| "rfl").collect::<Vec<_>>().join(" | ")));
                    let _ = runs;
                    s.push_str("    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr\n");
                    s.push_str(&format!("        rcases hr with {}\n", members.iter().map(|_| "rfl").collect::<Vec<_>>().join(" | ")));
                    for m in members {
                        let gm = goals.iter().find(|x| x.name == *m).unwrap();
                        let mut margs = Vec::new();
                        for c in &gm.callees {
                            let cid = callee_id(c);
                            if cycle_of.get(c) == Some(&ci) {
                                margs.push(format!("(hrec {} (by simp))", member(c)));
                            } else {
                                margs.push(format!("c_{cid}"));
                            }
                            margs.push(format!("fr_{cid}"));
                        }
                        for l in &gm.loops {
                            margs.push(format!("l_{}", lean_ident(&l.id)));
                        }
                        s.push_str(&format!(
                            "        · intro t ht hrec; exact d_{m} ρ t ht.1 ht.2{}\n",
                            margs.iter().map(|a| format!(" {a}")).collect::<String>()
                        ));
                    }
                    s.push_str("    )\n");
                }
                s.push_str(&format!(
                    "  have c_{n} : Contract ρ {} {n}_requires {n}_post := cyc_{ci} {} (by simp)\n",
                    quoted(&g.name),
                    member(&g.name),
                    n = g.name
                ));
            } else if ril {
                // **The recursive call stands inside the loop** (2026-09-08). One step:
                // `contract_of_duty_rec_loop_in` runs the induction over the `decreases`
                // OUTSIDE the loop rule, hands the pass the bounded self-contract at the
                // routine's entry state, and takes back from it that the measure did not
                // move. Afterwards the loop's own rule follows from the finished contract.
                let li = rec_loop_of(g).expect("`ril` is `rec_loop_of(..).is_some()`");
                let n = &g.name;
                // **A `retry`/`forever` loop takes the same composition without the range**
                // (2026-09-08): `contract_of_duty_rec_loop` and `looprule_of_body`. The
                // induction is over the `decreases`, never over the index -- the range is an
                // assumption the pass RECEIVES, not a premise of the composition. The earlier
                // refusal named the range as the obstacle, and the range was never it.
                let shape = |l: &LoopInfo| -> (&'static str, &'static str, String, &'static str) {
                    match l.range {
                        Some((lo, hi)) => (
                            "contract_of_duty_rec_loop_in",
                            "looprule_of_body_in",
                            format!(" {} {}", int_lit(lo), int_lit(hi)),
                            " hlo hhi",
                        ),
                        None => ("contract_of_duty_rec_loop", "looprule_of_body", String::new(), ""),
                    }
                };
                // the arguments of a pass's duty, in the order its statement declares them
                let pass_args = |l: &LoopInfo, below: bool, at: &str| -> String {
                    let mut a = Vec::new();
                    for c in &l.callees {
                        let cid = callee_id(c);
                        a.push(if c != n {
                            format!("c_{cid}")
                        } else if below {
                            format!("(contractBelow_of_contract ρ {} {n}_decreases {at} {n}_requires {n}_post c_{n})", quoted(n))
                        } else {
                            "hrec".to_string()
                        });
                        a.push(format!("fr_{cid}"));
                    }
                    a.iter().map(|x| format!(" {x}")).collect()
                };

                // **Every loop of the routine BUT the recursive one, as a rule that carries
                // the measure against an arbitrary entry state** -- the form the routine's
                // duty asks for once `ril` is on. It is built here because its pass needs
                // nothing the induction has; it is quantified over `s0` because the routine's
                // entry state is only named inside the induction.
                for (j, l) in g.loops.iter().enumerate() {
                    if j == li {
                        continue;
                    }
                    let lid = lean_ident(&l.id);
                    let (_, builder, bounds, hbnd) = shape(l);
                    let wfp = format!("(fun u => wellFormed u ∧ eval u {n}_decreases = eval s0 {n}_decreases)");
                    s.push_str(&format!(
                        "  have lp_{lid} : ∀ (s0 : State), LoopRule ρ {qid} {wfp} {lid}_inv :=\n    \
                         fun s0 => {builder} ρ {qid} {wfp} {lid}_inv {lid}_body {qv}{bounds} rl_{lid}\n      \
                         (fun t k{hbnd} hu hin => d_{lid} ρ t k{hbnd} hu.1 s0 hu.2 hin{la})\n",
                        qid = quoted(&l.id),
                        qv = quoted(&l.var),
                        la = pass_args(l, false, "t"),
                    ));
                }

                let l = &g.loops[li];
                let lid = lean_ident(&l.id);
                let (thm, _, bounds, hbnd) = shape(l);
                // the arguments of the routine's duty: the self-contract is `hrec`, the rule
                // of the loop that HOLDS the call is `hlr`, and every other loop hands in the
                // measure-carrying rule at the routine's entry state `t`.
                let mut margs = Vec::new();
                for c in &g.callees {
                    let cid = callee_id(c);
                    margs.push(if c == n { "hrec".to_string() } else { format!("c_{cid}") });
                    margs.push(format!("fr_{cid}"));
                }
                for (j, l2) in g.loops.iter().enumerate() {
                    margs.push(if j == li {
                        "hlr".to_string()
                    } else {
                        format!("(lp_{} t)", lean_ident(&l2.id))
                    });
                }
                s.push_str(&format!(
                    "  have c_{n} : Contract ρ {q} {n}_requires {n}_post :=\n    \
                     {thm} ρ {q} {n}_body {n}_requires {n}_post {n}_decreases wellFormed\n      \
                     {qid} {lid}_body {qv}{bounds} {lid}_inv r_{n} rl_{lid}\n      \
                     (fun s0 _h0 hrec t k{hbnd} hw hm hin => d_{lid} ρ t k{hbnd} hw s0 hm hin{la})\n      \
                     (fun t ht hrec hlr => d_{n} ρ t ht.1 ht.2{ma})\n",
                    q = quoted(n),
                    qid = quoted(&l.id),
                    qv = quoted(&l.var),
                    la = pass_args(l, false, "t"),
                    ma = margs.iter().map(|a| format!(" {a}")).collect::<String>(),
                ));
                // **And every loop's own rule, under the plain well-typed world** -- what
                // `unit_closed` hands out. The measure equation is `rfl` here: the pass is
                // read at the state it starts from.
                for (j, l) in g.loops.iter().enumerate() {
                    let lid = lean_ident(&l.id);
                    let (_, builder, bounds, hbnd) = shape(l);
                    s.push_str(&format!(
                        "  have l_{lid} : LoopRule ρ {qid} wellFormed {lid}_inv :=\n    \
                         {builder} ρ {qid} wellFormed {lid}_inv {lid}_body {qv}{bounds} rl_{lid}\n      \
                         (by intro t k{hbnd} hw hin\n          \
                         obtain ⟨t', h1, ⟨h2, _⟩, h3⟩ := d_{lid} ρ t k{hbnd} hw t rfl hin{la}\n          \
                         exact ⟨t', h1, h2, h3⟩)\n",
                        qid = quoted(&l.id),
                        qv = quoted(&l.var),
                        la = pass_args(l, j == li, "t"),
                    ));
                }
            } else if recursive {
                s.push_str(&format!(
                    "  have c_{n} : Contract ρ {} {n}_requires {n}_post :=\n    contract_of_duty_rec ρ {} {n}_body {n}_requires {n}_post {n}_decreases r_{n}\n      (fun t ht hrec => d_{n} ρ t ht.1 ht.2{})\n",
                    quoted(&g.name),
                    quoted(&g.name),
                    args.iter().map(|a| format!(" {a}")).collect::<String>(),
                    n = g.name
                ));
            } else {
                s.push_str(&format!(
                    "  have c_{n} : Contract ρ {} {n}_requires {n}_post :=\n    contract_of_duty ρ {} {n}_body {n}_requires {n}_post r_{n}\n      (fun t ht => d_{n} ρ t ht.1 ht.2{})\n",
                    quoted(&g.name),
                    quoted(&g.name),
                    args.iter().map(|a| format!(" {a}")).collect::<String>(),
                    n = g.name
                ));
            }
        }
        let mut have_names = Vec::new();
        for g in &wired {
            for l in &g.loops {
                have_names.push(format!("l_{}", lean_ident(&l.id)));
            }
            have_names.push(format!("c_{}", g.name));
        }
        if have_names.len() == 1 {
            s.push_str(&format!("  exact {}\n\n", have_names[0]));
        } else {
            s.push_str(&format!("  exact ⟨{}⟩\n\n", have_names.join(", ")));
        }
    }
    s.push_str(&format!("end GabbroDuty.{name}\n"));
    s
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
// ===========================================================================================

/// One routine of the program, as a datum -- or a named refusal.
pub struct Routine {
    pub name: String,
    pub body: Option<String>,
    pub refused: Option<LeanReason>,
    pub params: Vec<(String, Option<Shape>)>,
    pub pre: Vec<String>,
    pub dropped: Vec<String>,
    pub post: Vec<String>,
    pub post_dropped: Vec<String>,
}

/// Every routine of the program, in declaration order.
pub fn routines(baum: &Programm) -> Vec<Routine> {
    let unit = Unit::sammle(baum);
    let mut out = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, module| {
        let ItemArt::Funktion(f) = &item.art else { return };
        if f.klasse == Some(FnKlasse::Spec) {
            return;
        }
        let params: Vec<(String, Option<Shape>)> = unit
            .routines
            .get(&f.name.text)
            .map(|r| r.params.clone())
            .or_else(|| unit.foreign.get(&f.name.text).map(|r| r.params.clone()))
            .unwrap_or_default();
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
        let mut c = ctx_for(&unit, f, &f.name.text, module, ResultSite::Body);
        let maintained = unit.routines.get(&f.name.text).map(|r| r.maintained.clone()).unwrap_or_default();
        c.ret_post = ret_post_of(&unit, f, module, &maintained);
        c.kept = maintained.iter().filter_map(|m| kept_invariant(&unit, f, module, m).ok()).collect();
        let body = block_term(b, &mut c);
        c.result_site = ResultSite::Contract;
        let mut pre = Vec::new();
        let mut dropped = Vec::new();
        for (i, q) in f.requires.iter().enumerate() {
            match pred_term(q, &mut c) {
                Ok(t) => pre.push(t.into_term()),
                Err(r) => dropped.push(format!("requires #{} ({})", i + 1, r.tag())),
            }
        }
        let mut post = Vec::new();
        let mut post_dropped = Vec::new();
        for (i, q) in f.ensures.iter().enumerate() {
            match pred_term(q, &mut c) {
                Ok(t) => post.push(t.into_term()),
                Err(r) => post_dropped.push(format!("ensures #{} ({})", i + 1, r.tag())),
            }
        }
        match body {
            Ok(t) => out.push(Routine {
                name: f.name.text.clone(),
                body: Some(t.into_term()),
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
    let unit = Unit::sammle(baum);
    let mut dict: Vec<(String, String, Shape)> = Vec::new();
    let mut tnames: Vec<&String> = unit.tables.keys().collect();
    tnames.sort();
    for t in tnames {
        for (f, sh) in &unit.tables[t].fields {
            if let Some(sh) = sh {
                dict.push((t.clone(), f.clone(), *sh));
            }
        }
    }
    let mut rdict: Vec<(String, String, Shape)> = Vec::new();
    let mut rnames: Vec<&String> = unit.records.keys().collect();
    rnames.sort();
    for t in rnames {
        for (f, sh) in &unit.records[t] {
            if let Some(sh) = sh {
                rdict.push((t.clone(), f.clone(), *sh));
            }
        }
    }
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

    s.push_str("/-! ## The declared places\n\n");
    s.push_str("    **A specification names a place by STRING, and a typo in that string is a\n");
    s.push_str("    specification about a place that does not exist** -- vacuous rather than\n");
    s.push_str("    false, and vacuous reads like proved. This list is what a specification is\n");
    s.push_str("    held against; `instrumente/pruefe-lean-programm.sh` does the holding.\n-/\n\n");
    s.push_str("/-- `(carrier, field, shape)` for every declared slot field. -/\n");
    s.push_str("def places : List (String × String × String) :=\n");
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
    s.push_str("/-- `(carrier, field, shape)` for every declared RECORD or `format` field. -/\n");
    s.push_str("def fields : List (String × String × String) :=\n");
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
        .map(|(t, f, sh)| format!("(∀ k, {} (s.world (.slot {} k {})))", sh.predicate(), quoted(t), quoted(f)))
        .collect();
    parts.extend(rdict.iter().map(|(t, f, sh)| format!("({} (s.world (.field {} {})))", sh.predicate(), quoted(t), quoted(f))));
    if parts.is_empty() {
        s.push_str("  True\n\n");
    } else {
        s.push_str(&format!("  {}\n\n", parts.join("\n  ∧ ")));
    }

    s.push_str("/-! ## The routines -/\n\n");
    for r in &rs {
        if let Some(reason) = r.refused {
            s.push_str(&format!("-- REFUSED  {}  ({}): {}\n\n", r.name, reason.tag(), reason.sentence()));
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
            .filter_map(|(n, sh)| sh.map(|sh| format!("{} (s.local' {})", sh.predicate(), quoted(n))))
            .collect();
        for t in &r.pre {
            parts.push(format!("eval s {t} = some (.bool true)"));
        }
        if parts.is_empty() {
            s.push_str("  True\n\n");
        } else {
            s.push_str(&format!("  {}\n\n", parts.join("\n  ∧ ")));
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
            s.push_str(&format!("  {}\n\n", ps.join("\n  ∧ ")));
        }
    }

    s.push_str("/-! ## Proving something about this program\n\n");
    s.push_str("    A specification is a Lean predicate over `State`; the obligation is that a\n");
    s.push_str("    body establishes it. The tactic that unfolds the model is `gabbro_simp`,\n");
    s.push_str("    and it lives in `Gabbro.Body` -- not here, so that a change to the model\n");
    s.push_str("    reaches every proof through one place.\n\n");
    s.push_str("        theorem meets_spec (ρ : Env) (s : State) (k : Int)\n");
    s.push_str("            (wf : wellFormed s) (hk : s.local' \"k\" = .int k)\n");
    s.push_str("            : ∃ s', finalState (exec ρ f_body s) = some s'\n");
    s.push_str("                ∧ mySpec k s' := by\n");
    s.push_str("          gabbro_simp [mySpec, hk]\n-/\n\n");
    s.push_str("end GabbroProgram\n");
    s
}

// ===========================================================================================
// THE CARRIED HALF -- the register the refusals always had and the carries never did.
// ===========================================================================================

/// **Where a carried decision stands in `Coverage.lean`'s enumeration.**
///
/// A term-writing site either carries a form of the grammar -- and then it names the
/// `Form` constructors whose discharge lemma covers it -- or it writes a SUB-TERM of the
/// form around it and carries nothing of its own. *A literal `3` generates no obligation;
/// the clause it stands in does.*
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CarriedForm {
    /// The `Form` constructors of `programmlogik/Gabbro/Coverage.lean` that discharge this
    /// decision, in their spelling there. Never empty.
    Forms(&'static [&'static str]),
    /// A sub-term of the surrounding form. It states no obligation; the form around it does.
    Subterm,
}

/// **Every place the emitter CARRIES a form by writing a term names itself here.**
///
/// `LeanReason` made the refusals enumerable; the carries had no such list, and
/// `pruefe-deckung.py`'s own header said so: *"a form the grammar admits, the emitter
/// carries, and `Form` never names would pass every check."* Two registers over one thing
/// and only one of them read -- the `W7` class.
///
/// **A new carrying site cannot bypass this enum**, and that is a fact about the TYPE and
/// not about anybody's discipline: `place_term`, `expr_term`, `pred_term`, `domain_of`,
/// `stmt_term` and `block_term` return a `Carried`, `Carried` has a private field in a
/// module of its own, and the only way to build one is `LeanCarried::term`. *An `Ok(s)`
/// with a bare `String` does not compile.*
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LeanCarried {
    // ------------------------------------------------------------------ places
    /// A bare local name -- `(.name n)`.
    PlaceLocal,
    /// The pass counter's ghost local, read in a loop invariant (`passes`).
    PlacePassCounter,
    /// A constant folded to its value -- `WURZEL` is `0`, not a place of the world.
    PlaceConstant,
    /// A `static` -- `(.global n)`.
    PlaceGlobal,
    /// `r.f` at a record or a `format` -- `(.fieldOf ...)`.
    PlaceRecordField,
    /// `buf[i]`, `r.f[i]` -- a slot of the array's pseudo-table.
    PlaceArrayElement,
    /// `c.slots[i].f` -- the slot field, the commonest place of the corpus.
    PlaceSlotField,
    // ------------------------------------------------------------- expressions
    /// A number, `true`, `false`, a reason case -- a literal.
    ExprLiteral,
    /// `not e`, `-e`.
    ExprUnary,
    /// The binary operators, arithmetic and bit alike.
    ExprBinary,
    /// A call inside an expression, after the emitter has hoisted it into a `let`.
    ExprHoistedCall,
    /// `None`, `Some(e)`.
    ExprOption,
    /// `Case`, `Case(e)` of a `tagged type`.
    ExprTagged,
    /// `aligned(e, n)` -- `e % n == 0`.
    ExprAligned,
    /// `lenof a` at a fixed-length array -- the declared count.
    ExprArrayLength,
    /// `old(e)` in an `ensures` -- a name bound to the entry state's value.
    ExprOldState,
    /// `result` in an `ensures`, `#ret` after a desugared `return` in a loop.
    ExprResultName,
    // ------------------------------------------------------------- predicates
    /// `not P`, `P and Q`, `P or Q`, `P implies Q`.
    PredConnective,
    /// `Held(L)` in a contract -- `true`, and the lock passes decide it.
    PredLockHeld,
    /// `forall f in fields of F : P` where the body does not read the binder: the
    /// quantifier collapses over the declared, finite field list.
    PredQuantFields,
    /// `forall x in D : P` / `exists x in D : P` over an index domain.
    PredQuantIndexDomain,
    /// `a reaches b via f` -- the chain with the table's count as fuel.
    PredReaches,
    /// `e in D` -- the membership, as an expression over the index.
    PredMembership,
    // ----------------------------------------------------------------- domains
    /// `slots of T`.
    DomainSlots,
    /// `descendants of T.slots[p]`, `ancestors of T.slots[p]` -- the index domain cut by a
    /// reach along the table's `tree` edge.
    DomainReach,
    /// `chain(h, n) in T.slots[p]`.
    DomainChain,
    /// `elems of r.f`, `elems of buf`.
    DomainElems,
    /// `queue r`, `queue T.slots[i].f`.
    DomainQueue,
    // -------------------------------------------------------------- statements
    /// `let x = f(a);` -- a call whose answer is bound.
    StmtBindCall,
    /// `let x = e;` -- a plain binding.
    StmtBindName,
    /// `n = e;` at a LOCAL -- a rebinding, not a store into the world.
    StmtAssignLocal,
    /// `n += e;` at a local.
    StmtCompoundAssignLocal,
    /// `g = e;` at a `static`.
    StmtAssignGlobal,
    /// `r.f = e;` at a record or a `format`.
    StmtStoreRecordField,
    /// `buf[i] = e;`, `r.f[i] = e;`.
    StmtStoreArrayElement,
    /// `c.slots[i].f = e;` -- the commonest store of the corpus.
    StmtStoreSlotField,
    /// `if ... { ... } else { ... }`.
    StmtConditional,
    /// `match v { Case(p) => ... }` over a `tagged` value.
    StmtTaggedMatch,
    /// `match e { Case => ... }` over a REASON -- the closed enumeration of `M123`.
    StmtReasonMatch,
    /// `match e { Some(b) => ..., None => ... }`.
    StmtOptionMatch,
    /// `return;` / `return e;` inside a loop -- desugared into `#ret`, `#returned` and an
    /// exit of the pass.
    StmtReturnInLoop,
    /// `return;` -- the answerless return.
    StmtReturnNothing,
    /// `return e;` -- the value return.
    StmtReturnValue,
    /// `return f(a);` -- a call whose answer is returned straight on.
    StmtReturnCall,
    /// `f(a);` -- a call taken over the callee's contract.
    StmtCall,
    /// `let n = f(a) else (e) { ... };` -- the error propagation, carried since 2026-09-07
    /// and named by no `Form` until 2026-09-08.
    StmtCallWithErrorExit,
    /// `traverse` / `retry` / `forever` -- the loop, with its range and its pass counter
    /// where the domain gives them.
    StmtLoop,
    /// `narrow x to lo .. hi else { ... }` -- a conditional with an empty then-branch.
    StmtNarrowRange,
    /// `breaking I { ... }` -- the SUSPENSION of a table invariant.
    StmtInvariantSuspension,
    /// `leave m;` / `next m;` at the innermost loop.
    StmtLoopExit,
    /// `publishes a = e;` at a bare atomic.
    StmtPublish,
    /// `awaits n = a;` at a bare atomic.
    StmtAwait,
    /// `locks S { ... }` -- the critical section.
    StmtCriticalSection,
    /// Two statements in a row -- the block.
    StmtSequence,
}

impl LeanCarried {
    /// The stable name of the decision, the way `LeanReason::tag` names a refusal.
    pub fn tag(self) -> &'static str {
        match self {
            LeanCarried::PlaceLocal => "place-local",
            LeanCarried::PlacePassCounter => "place-pass-counter",
            LeanCarried::PlaceConstant => "place-constant",
            LeanCarried::PlaceGlobal => "place-global",
            LeanCarried::PlaceRecordField => "place-record-field",
            LeanCarried::PlaceArrayElement => "place-array-element",
            LeanCarried::PlaceSlotField => "place-slot-field",
            LeanCarried::ExprLiteral => "expr-literal",
            LeanCarried::ExprUnary => "expr-unary",
            LeanCarried::ExprBinary => "expr-binary",
            LeanCarried::ExprHoistedCall => "expr-hoisted-call",
            LeanCarried::ExprOption => "expr-option",
            LeanCarried::ExprTagged => "expr-tagged",
            LeanCarried::ExprAligned => "expr-aligned",
            LeanCarried::ExprArrayLength => "expr-array-length",
            LeanCarried::ExprOldState => "expr-old-state",
            LeanCarried::ExprResultName => "expr-result-name",
            LeanCarried::PredConnective => "pred-connective",
            LeanCarried::PredLockHeld => "pred-lock-held",
            LeanCarried::PredQuantFields => "pred-quant-fields",
            LeanCarried::PredQuantIndexDomain => "pred-quant-index-domain",
            LeanCarried::PredReaches => "pred-reaches",
            LeanCarried::PredMembership => "pred-membership",
            LeanCarried::DomainSlots => "domain-slots",
            LeanCarried::DomainReach => "domain-reach",
            LeanCarried::DomainChain => "domain-chain",
            LeanCarried::DomainElems => "domain-elems",
            LeanCarried::DomainQueue => "domain-queue",
            LeanCarried::StmtBindCall => "stmt-bind-call",
            LeanCarried::StmtBindName => "stmt-bind-name",
            LeanCarried::StmtAssignLocal => "stmt-assign-local",
            LeanCarried::StmtCompoundAssignLocal => "stmt-compound-assign-local",
            LeanCarried::StmtAssignGlobal => "stmt-assign-global",
            LeanCarried::StmtStoreRecordField => "stmt-store-record-field",
            LeanCarried::StmtStoreArrayElement => "stmt-store-array-element",
            LeanCarried::StmtStoreSlotField => "stmt-store-slot-field",
            LeanCarried::StmtConditional => "stmt-conditional",
            LeanCarried::StmtTaggedMatch => "stmt-tagged-match",
            LeanCarried::StmtReasonMatch => "stmt-reason-match",
            LeanCarried::StmtOptionMatch => "stmt-option-match",
            LeanCarried::StmtReturnInLoop => "stmt-return-in-loop",
            LeanCarried::StmtReturnNothing => "stmt-return-nothing",
            LeanCarried::StmtReturnValue => "stmt-return-value",
            LeanCarried::StmtReturnCall => "stmt-return-call",
            LeanCarried::StmtCall => "stmt-call",
            LeanCarried::StmtCallWithErrorExit => "stmt-call-with-error-exit",
            LeanCarried::StmtLoop => "stmt-loop",
            LeanCarried::StmtNarrowRange => "stmt-narrow-range",
            LeanCarried::StmtInvariantSuspension => "stmt-invariant-suspension",
            LeanCarried::StmtLoopExit => "stmt-loop-exit",
            LeanCarried::StmtPublish => "stmt-publish",
            LeanCarried::StmtAwait => "stmt-await",
            LeanCarried::StmtCriticalSection => "stmt-critical-section",
            LeanCarried::StmtSequence => "stmt-sequence",
        }
    }

    /// **What the decision carries, in `Coverage.lean`'s spelling.** The names here are
    /// checked against the Lean file in both directions -- by `pruefe-deckung.py` and, so
    /// that a run of the test suite is enough, by `carried_forms_are_named`.
    pub fn forms(self) -> CarriedForm {
        match self {
            LeanCarried::PlaceLocal => CarriedForm::Subterm,
            LeanCarried::PlacePassCounter => CarriedForm::Forms(&["loopPassCounted"]),
            LeanCarried::PlaceConstant => CarriedForm::Subterm,
            LeanCarried::PlaceGlobal => CarriedForm::Forms(&["read"]),
            LeanCarried::PlaceRecordField => CarriedForm::Forms(&["read"]),
            LeanCarried::PlaceArrayElement => CarriedForm::Forms(&["read"]),
            LeanCarried::PlaceSlotField => CarriedForm::Forms(&["read", "storeBesideRead"]),
            LeanCarried::ExprLiteral => CarriedForm::Subterm,
            LeanCarried::ExprUnary => CarriedForm::Forms(&["arithmeticSemantics"]),
            LeanCarried::ExprBinary => CarriedForm::Forms(&["arithmeticSemantics"]),
            LeanCarried::ExprHoistedCall => CarriedForm::Forms(&["callInExpressionHoisted"]),
            LeanCarried::ExprOption => CarriedForm::Subterm,
            LeanCarried::ExprTagged => CarriedForm::Subterm,
            LeanCarried::ExprAligned => CarriedForm::Subterm,
            LeanCarried::ExprArrayLength => CarriedForm::Subterm,
            LeanCarried::ExprOldState => CarriedForm::Subterm,
            LeanCarried::ExprResultName => CarriedForm::Forms(&["answerWithShape"]),
            LeanCarried::PredConnective => CarriedForm::Subterm,
            LeanCarried::PredLockHeld => CarriedForm::Subterm,
            LeanCarried::PredQuantFields => CarriedForm::Forms(&["quantFields"]),
            LeanCarried::PredQuantIndexDomain => CarriedForm::Forms(&["quantifiedPremise"]),
            LeanCarried::PredReaches => CarriedForm::Forms(&["storeBesideChain"]),
            LeanCarried::PredMembership => CarriedForm::Subterm,
            LeanCarried::DomainSlots => CarriedForm::Forms(&["quantSlots"]),
            LeanCarried::DomainReach => CarriedForm::Forms(&["quantReach"]),
            LeanCarried::DomainChain => CarriedForm::Forms(&["quantChain"]),
            LeanCarried::DomainElems => CarriedForm::Forms(&["quantElems"]),
            LeanCarried::DomainQueue => CarriedForm::Forms(&["quantQueue"]),
            LeanCarried::StmtBindCall => {
                CarriedForm::Forms(&["callResultBound", "answerWithoutShape"])
            }
            LeanCarried::StmtBindName => CarriedForm::Forms(&["localBinding"]),
            LeanCarried::StmtAssignLocal => CarriedForm::Forms(&["localBinding"]),
            LeanCarried::StmtCompoundAssignLocal => CarriedForm::Forms(&["localBinding"]),
            LeanCarried::StmtAssignGlobal => CarriedForm::Forms(&["store"]),
            LeanCarried::StmtStoreRecordField => CarriedForm::Forms(&["store"]),
            LeanCarried::StmtStoreArrayElement => CarriedForm::Forms(&["store"]),
            LeanCarried::StmtStoreSlotField => CarriedForm::Forms(&["store"]),
            LeanCarried::StmtConditional => CarriedForm::Forms(&["controlFlow"]),
            LeanCarried::StmtTaggedMatch => CarriedForm::Forms(&["taggedMatch"]),
            LeanCarried::StmtReasonMatch => CarriedForm::Forms(&["reasonMatch"]),
            LeanCarried::StmtOptionMatch => CarriedForm::Forms(&["optionMatch"]),
            LeanCarried::StmtReturnInLoop => CarriedForm::Forms(&["loopExit"]),
            LeanCarried::StmtReturnNothing => CarriedForm::Forms(&["answerWithoutShape"]),
            LeanCarried::StmtReturnValue => CarriedForm::Forms(&["answerWithShape"]),
            LeanCarried::StmtReturnCall => CarriedForm::Forms(&["callResultReturned"]),
            LeanCarried::StmtCall => CarriedForm::Forms(&["callStatement"]),
            LeanCarried::StmtCallWithErrorExit => CarriedForm::Forms(&["callWithErrorExit"]),
            LeanCarried::StmtLoop => {
                CarriedForm::Forms(&["loopPass", "loopPassInRange", "loopPassCounted"])
            }
            LeanCarried::StmtNarrowRange => CarriedForm::Forms(&["controlFlow"]),
            LeanCarried::StmtInvariantSuspension => CarriedForm::Forms(&["invariantSuspension"]),
            LeanCarried::StmtLoopExit => CarriedForm::Forms(&["loopExit"]),
            LeanCarried::StmtPublish => CarriedForm::Forms(&["publishAtomic"]),
            LeanCarried::StmtAwait => CarriedForm::Forms(&["awaitAtomic"]),
            LeanCarried::StmtCriticalSection => CarriedForm::Forms(&["criticalSection"]),
            LeanCarried::StmtSequence => CarriedForm::Forms(&["sequencing"]),
        }
    }

    /// The function of this file that decides it -- so a reader can go and look.
    pub fn site(self) -> &'static str {
        match self {
            LeanCarried::PlaceLocal
            | LeanCarried::PlacePassCounter
            | LeanCarried::PlaceConstant
            | LeanCarried::PlaceGlobal
            | LeanCarried::PlaceRecordField
            | LeanCarried::PlaceArrayElement
            | LeanCarried::PlaceSlotField => "place_term",
            LeanCarried::ExprLiteral
            | LeanCarried::ExprUnary
            | LeanCarried::ExprBinary
            | LeanCarried::ExprHoistedCall
            | LeanCarried::ExprOption
            | LeanCarried::ExprTagged
            | LeanCarried::ExprAligned
            | LeanCarried::ExprArrayLength
            | LeanCarried::ExprOldState
            | LeanCarried::ExprResultName => "expr_term",
            LeanCarried::PredConnective
            | LeanCarried::PredLockHeld
            | LeanCarried::PredQuantFields
            | LeanCarried::PredQuantIndexDomain
            | LeanCarried::PredReaches
            | LeanCarried::PredMembership => "pred_term",
            LeanCarried::DomainSlots
            | LeanCarried::DomainReach
            | LeanCarried::DomainChain
            | LeanCarried::DomainElems
            | LeanCarried::DomainQueue => "domain_of",
            LeanCarried::StmtSequence => "block_term",
            _ => "stmt_term",
        }
    }

    /// The position in `ALL`. **The match is exhaustive on purpose**: a new variant does
    /// not compile until it has one, and `all_is_the_whole_population` then fails until it
    /// stands in `ALL` too. *The population cannot be added to in silence.*
    #[allow(dead_code)]
    fn index(self) -> usize {
        match self {
            LeanCarried::PlaceLocal => 0,
            LeanCarried::PlacePassCounter => 1,
            LeanCarried::PlaceConstant => 2,
            LeanCarried::PlaceGlobal => 3,
            LeanCarried::PlaceRecordField => 4,
            LeanCarried::PlaceArrayElement => 5,
            LeanCarried::PlaceSlotField => 6,
            LeanCarried::ExprLiteral => 7,
            LeanCarried::ExprUnary => 8,
            LeanCarried::ExprBinary => 9,
            LeanCarried::ExprHoistedCall => 10,
            LeanCarried::ExprOption => 11,
            LeanCarried::ExprTagged => 12,
            LeanCarried::ExprAligned => 13,
            LeanCarried::ExprArrayLength => 14,
            LeanCarried::ExprOldState => 15,
            LeanCarried::ExprResultName => 16,
            LeanCarried::PredConnective => 17,
            LeanCarried::PredLockHeld => 18,
            LeanCarried::PredQuantFields => 19,
            LeanCarried::PredQuantIndexDomain => 20,
            LeanCarried::PredReaches => 21,
            LeanCarried::PredMembership => 22,
            LeanCarried::DomainSlots => 23,
            LeanCarried::DomainReach => 24,
            LeanCarried::DomainChain => 25,
            LeanCarried::DomainElems => 26,
            LeanCarried::DomainQueue => 27,
            LeanCarried::StmtBindCall => 28,
            LeanCarried::StmtBindName => 29,
            LeanCarried::StmtAssignLocal => 30,
            LeanCarried::StmtCompoundAssignLocal => 31,
            LeanCarried::StmtAssignGlobal => 32,
            LeanCarried::StmtStoreRecordField => 33,
            LeanCarried::StmtStoreArrayElement => 34,
            LeanCarried::StmtStoreSlotField => 35,
            LeanCarried::StmtConditional => 36,
            LeanCarried::StmtTaggedMatch => 37,
            LeanCarried::StmtReasonMatch => 38,
            LeanCarried::StmtOptionMatch => 39,
            LeanCarried::StmtReturnInLoop => 40,
            LeanCarried::StmtReturnNothing => 41,
            LeanCarried::StmtReturnValue => 42,
            LeanCarried::StmtReturnCall => 43,
            LeanCarried::StmtCall => 44,
            LeanCarried::StmtCallWithErrorExit => 45,
            LeanCarried::StmtLoop => 46,
            LeanCarried::StmtNarrowRange => 47,
            LeanCarried::StmtInvariantSuspension => 48,
            LeanCarried::StmtLoopExit => 49,
            LeanCarried::StmtPublish => 50,
            LeanCarried::StmtAwait => 51,
            LeanCarried::StmtCriticalSection => 52,
            LeanCarried::StmtSequence => 53,
        }
    }

    /// **The term this decision writes.** The only way to build a `Carried`, and therefore
    /// the only way for a term-writing function to return one.
    pub fn term(self, term: impl Into<String>) -> Carried {
        Carried::neu(self, term.into())
    }

    /// The whole population, in the order of `index`.
    pub const ALL: [LeanCarried; 54] = [
        LeanCarried::PlaceLocal,
        LeanCarried::PlacePassCounter,
        LeanCarried::PlaceConstant,
        LeanCarried::PlaceGlobal,
        LeanCarried::PlaceRecordField,
        LeanCarried::PlaceArrayElement,
        LeanCarried::PlaceSlotField,
        LeanCarried::ExprLiteral,
        LeanCarried::ExprUnary,
        LeanCarried::ExprBinary,
        LeanCarried::ExprHoistedCall,
        LeanCarried::ExprOption,
        LeanCarried::ExprTagged,
        LeanCarried::ExprAligned,
        LeanCarried::ExprArrayLength,
        LeanCarried::ExprOldState,
        LeanCarried::ExprResultName,
        LeanCarried::PredConnective,
        LeanCarried::PredLockHeld,
        LeanCarried::PredQuantFields,
        LeanCarried::PredQuantIndexDomain,
        LeanCarried::PredReaches,
        LeanCarried::PredMembership,
        LeanCarried::DomainSlots,
        LeanCarried::DomainReach,
        LeanCarried::DomainChain,
        LeanCarried::DomainElems,
        LeanCarried::DomainQueue,
        LeanCarried::StmtBindCall,
        LeanCarried::StmtBindName,
        LeanCarried::StmtAssignLocal,
        LeanCarried::StmtCompoundAssignLocal,
        LeanCarried::StmtAssignGlobal,
        LeanCarried::StmtStoreRecordField,
        LeanCarried::StmtStoreArrayElement,
        LeanCarried::StmtStoreSlotField,
        LeanCarried::StmtConditional,
        LeanCarried::StmtTaggedMatch,
        LeanCarried::StmtReasonMatch,
        LeanCarried::StmtOptionMatch,
        LeanCarried::StmtReturnInLoop,
        LeanCarried::StmtReturnNothing,
        LeanCarried::StmtReturnValue,
        LeanCarried::StmtReturnCall,
        LeanCarried::StmtCall,
        LeanCarried::StmtCallWithErrorExit,
        LeanCarried::StmtLoop,
        LeanCarried::StmtNarrowRange,
        LeanCarried::StmtInvariantSuspension,
        LeanCarried::StmtLoopExit,
        LeanCarried::StmtPublish,
        LeanCarried::StmtAwait,
        LeanCarried::StmtCriticalSection,
        LeanCarried::StmtSequence,
    ];
}

/// **The carried forms that NO term-writing site names, with the reason and the site.**
///
/// A form of `Coverage.lean` is carried either because the emitter writes a term for it --
/// then a `LeanCarried` variant names it -- or because the emitter decides it in the
/// WIRING: which theorem stands over which body, which hypothesis it takes, which conjunct
/// a shape contributes. *There is no term for "the callee's contract IS the duty proved
/// over its body"; there is a wiring order.*
///
/// The list is here rather than in the guard because it is a statement about the emitter,
/// and `carried_forms_are_named` demands that every carried form of the Lean file stand in
/// exactly one of the two lists. **A new carried form must be classified; it cannot arrive
/// unnoticed.**
pub const CARRIED_BY_WIRING: [(&str, &str, &str); 7] = [
    (
        "callChain",
        "wiring_order",
        "the outer call's contract fires at the state the inner one left -- an ORDER of hypotheses, not a term",
    ),
    (
        "callFrame",
        "openings",
        "the callee's `writes` list becomes the frame hypothesis of the caller's theorem",
    ),
    (
        "contractFromDuty",
        "routine_goals",
        "a duty proved over a body IS the callee's contract -- the wiring itself",
    ),
    (
        "recursionSelf",
        "self_recursive",
        "the induction over `decreases`; the emitter decides it from the call graph",
    ),
    (
        "recursionCycle",
        "wiring_order",
        "a CYCLE of the call graph gets one induction over the shared measure",
    ),
    (
        "recursionInLoop",
        "rec_in_loop",
        "a recursive call from inside the routine's own ranged loop",
    ),
    (
        "declaredRange",
        "shape_conjunct",
        "a declared range becomes a conjunct of the well-typedness, in both directions",
    ),
];

/// The `Carried` type and its private field. **A module of its own so that the field is out
/// of reach of the rest of this file**: inside one module a private field is private to
/// nobody, and the whole point is that `Carried { term }` cannot be written at a new
/// carrying site.
mod getragen {
    use super::LeanCarried;

    /// **A term the emitter WROTE, and the decision that wrote it.** Built only by
    /// `LeanCarried::term`.
    #[derive(Clone, Debug)]
    pub struct Carried {
        term: String,
        site: LeanCarried,
    }

    impl Carried {
        pub(super) fn neu(site: LeanCarried, term: String) -> Carried {
            Carried { term, site }
        }
        /// The decision that wrote this term.
        #[allow(dead_code)]
        pub fn site(&self) -> LeanCarried {
            self.site
        }
        pub fn as_str(&self) -> &str {
            &self.term
        }
        pub fn into_term(self) -> String {
            self.term
        }
    }

    impl std::fmt::Display for Carried {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str(&self.term)
        }
    }

    impl From<Carried> for String {
        fn from(c: Carried) -> String {
            c.term
        }
    }
}

pub use getragen::Carried;

// ===========================================================================================
// THE CORRESPONDENCE, ON THE RUST SIDE -- so a `cargo test` decides it and not a script.
// ===========================================================================================

/// `Coverage.lean`, read at COMPILE time. A file that moves away takes the build down; a
/// guard that reads it at run time would report a missing file as a green run.
#[cfg(test)]
const COVERAGE_LEAN: &str = include_str!("../../../programmlogik/Gabbro/Coverage.lean");

#[cfg(test)]
mod deckung_tests {
    use super::*;
    use std::collections::BTreeSet;

    /// The constructors of `Form` that `classify` sends to `.carried`.
    fn carried_forms() -> BTreeSet<String> {
        let start = COVERAGE_LEAN
            .find("def classify : Form -> Verdict")
            .or_else(|| COVERAGE_LEAN.find("def classify : Form \u{2192} Verdict"))
            .expect("`classify` not found in Coverage.lean");
        let rest = &COVERAGE_LEAN[start..];
        let end = rest.find("\n\n").expect("`classify` has no end");
        let body = &rest[..end];
        // Every constructor listed before the arm `=> .carried`.
        let mut out = BTreeSet::new();
        let mut pending: Vec<String> = Vec::new();
        for line in body.lines().skip(1) {
            let line = line.trim();
            if !line.starts_with('|') {
                continue;
            }
            for stueck in line.trim_start_matches('|').split('|') {
                let stueck = stueck.trim();
                let (namen, arm) = match stueck.split_once("=>") {
                    Some((n, a)) => (n.trim(), Some(a.trim())),
                    None => (stueck, None),
                };
                if let Some(n) = namen.strip_prefix('.') {
                    if !n.is_empty() {
                        pending.push(n.trim().to_string());
                    }
                }
                if let Some(arm) = arm {
                    if arm == ".carried" {
                        out.extend(pending.iter().cloned());
                    }
                    pending.clear();
                }
            }
        }
        out
    }

    /// **`ALL` is the whole population, once each.** `index` is exhaustive, so a new
    /// variant does not compile without a number; this makes the number decide `ALL`.
    #[test]
    fn all_is_the_whole_population() {
        for (i, c) in LeanCarried::ALL.iter().enumerate() {
            assert_eq!(c.index(), i, "{:?} stands at the wrong place in ALL", c);
        }
        let tags: BTreeSet<&str> = LeanCarried::ALL.iter().map(|c| c.tag()).collect();
        assert_eq!(tags.len(), LeanCarried::ALL.len(), "two decisions share a tag");
        for c in LeanCarried::ALL {
            assert!(!c.tag().is_empty(), "{:?} has an empty tag", c);
            assert!(!c.site().is_empty(), "{:?} names no site", c);
            if let CarriedForm::Forms(fs) = c.forms() {
                assert!(!fs.is_empty(), "{:?} names an EMPTY form list", c);
            }
        }
    }

    /// **The Lean file has carried forms at all** -- the reader must not read nothing and
    /// call it agreement. `W16`: a guard that measures an empty set is green for free.
    #[test]
    fn the_lean_file_is_readable() {
        let f = carried_forms();
        assert!(
            f.len() >= 30,
            "read only {} carried forms out of Coverage.lean -- the reader broke, \
             not the correspondence",
            f.len()
        );
        assert!(f.contains("store") && f.contains("read") && f.contains("callStatement"));
    }

    /// **Forward: every form a carrying site names is a form `classify` calls carried.**
    /// A name that drifts would make the register point at nothing.
    #[test]
    fn every_named_form_is_carried_in_lean() {
        let carried = carried_forms();
        let mut fehlend = Vec::new();
        for c in LeanCarried::ALL {
            if let CarriedForm::Forms(fs) = c.forms() {
                for f in fs {
                    if !carried.contains(*f) {
                        fehlend.push(format!("{} names `{}`", c.tag(), f));
                    }
                }
            }
        }
        assert!(
            fehlend.is_empty(),
            "carrying sites name forms that `classify` does not call carried: {:?}",
            fehlend
        );
    }

    /// **Backward: every carried form of the Lean file is named** -- by a carrying site, or
    /// by `CARRIED_BY_WIRING` with its reason. *This is the half that was blind: a form the
    /// emitter carries and `Form` never names, and a form `Form` names and nothing carries,
    /// both slip through a check that runs one way.*
    #[test]
    fn carried_forms_are_named() {
        let carried = carried_forms();
        let mut benannt: BTreeSet<String> = BTreeSet::new();
        for c in LeanCarried::ALL {
            if let CarriedForm::Forms(fs) = c.forms() {
                benannt.extend(fs.iter().map(|f| f.to_string()));
            }
        }
        let verdrahtet: BTreeSet<String> =
            CARRIED_BY_WIRING.iter().map(|(f, _, _)| f.to_string()).collect();
        let ungedeckt: Vec<&String> = carried
            .iter()
            .filter(|f| !benannt.contains(*f) && !verdrahtet.contains(*f))
            .collect();
        assert!(
            ungedeckt.is_empty(),
            "carried forms of Coverage.lean that no carrying site and no wiring entry \
             names: {:?}",
            ungedeckt
        );
        let doppelt: Vec<&String> = verdrahtet.iter().filter(|f| benannt.contains(*f)).collect();
        assert!(
            doppelt.is_empty(),
            "forms in BOTH lists -- a register with two entries over one thing: {:?}",
            doppelt
        );
        let unbekannt: Vec<&String> =
            verdrahtet.iter().filter(|f| !carried.contains(*f)).collect();
        assert!(
            unbekannt.is_empty(),
            "wiring entries for forms `classify` does not call carried: {:?}",
            unbekannt
        );
    }

    /// **The refusal half, on the Rust side too.** `pruefe-deckung.py` checks it against the
    /// text; a test that only a script performs is a check somebody has to remember.
    #[test]
    fn every_refusal_has_a_lean_constructor() {
        let start = COVERAGE_LEAN
            .find("inductive Reason where")
            .expect("`Reason` not found");
        let rest = &COVERAGE_LEAN[start..];
        let end = rest.find("\n\n").expect("`Reason` has no end");
        let body = &rest[..end];
        let namen: BTreeSet<&str> = body
            .lines()
            .skip(1)
            .flat_map(|l| l.split('|'))
            .map(|s| s.trim())
            .filter(|s| !s.is_empty() && s.chars().all(|c| c.is_ascii_alphanumeric()))
            .collect();
        assert_eq!(
            namen.len(),
            LeanReason::ALL.len(),
            "`Reason` has {} constructors, `LeanReason::ALL` {}",
            namen.len(),
            LeanReason::ALL.len()
        );
        for r in LeanReason::ALL {
            let s = format!("{:?}", r);
            let lean = format!("{}{}", s[..1].to_lowercase(), &s[1..]);
            assert!(
                namen.contains(lean.as_str()),
                "`LeanReason::{}` has no constructor `{}` in Coverage.lean",
                s,
                lean
            );
        }
    }
}

// ===========================================================================================
// S4 -- THE SEAM WITNESSES (`dokumente/PLAN-SICHERHEIT.md` §4).
//
// `gabbro lean` writes `Duty*.lean` per unit against `Gabbro.Body`; this function writes a
// SECOND module per unit against `Gabbro.Sicherheit.Anweisung`: for every routine whose
// body the duty channel carries, one theorem
//
//   theorem checker_agrees_<routine> :
//       (pruefeBlock seamP_<routine> <erg> <entry> <body>).isSome = true := by decide
//
// A unit the Rust checker accepts and `pruefe` refuses (or the reverse) then fails LOUDLY
// at `lake build` -- per routine, per run. What it measures is that the two checkers
// agree on the corpus, not that they are the same function.
//
// ## What the witness is, exactly -- and what it is not
//
// * The BODY is the duty channel's term (`RoutineGoal::body`), unchanged. The witness
//   therefore checks the duty datum against `pruefe`, not the source text against it:
//   a transformation the duty channel applies (hoisted calls, the `narrow`-as-`ite`
//   reading, the return-in-loop desugar) is checked WITH it, not held against it.
// * `P` is read from the DECLARATIONS: `D` from tables/records/statics, `sig` from
//   routine/foreign/op/transition declarations, `schleife` replayed from the walk (below).
// * The proposition is `.isSome = true`, not `= some _`: the latter leaves a
//   metavariable `decide` cannot evaluate (the scope is an existential over an infinite
//   type), while `.isSome` is a closed `Bool` equation. Same seam, decidable form.
// * `<entry>` is the parameter scope, NOT `[]`: `pruefeBlock P erg [] body` starts with
//   no names bound, and every routine that reads a parameter would refuse. The plan's
//   `[]` checks only closed bodies; routines with parameters start from `paramUmgebung`.
// * `decide` must TERMINATE: one theorem per routine keeps each decision small (a body
//   is tens of statements; every function `P` unfolds is a finite match). A `decide`
//   that hangs is a red witness, not a slow one -- run each file under `timeout`.
// * The file is a SEPARATE module, not a section of the `Duty` file: the duty watchers
//   (`zaehle-lean.py`, `beweis.rs`' single-`lean` flow) read `Duty` files, and a second
//   import there would move their subject.
//
// ## The two adapters -- places where the duty datum is not `pruefe`-shaped
//
// A1. Loop variables. The duty term binds no loop variable (the proof side carries it
//     in `LoopRule` hypotheses instead), but `pruefe` reads the body under the entry
//     scope, so an unbound variable refuses. The witness prepends
//     `(.bindName "v" (.lit (.int 0)))` per loop variable -- shape `IntIn(0,0)`, a POINT:
//     it satisfies every index bound (`0 < count`) while claiming no upper range the
//     model never gave. A body that needs the variable's true range may go red (or,
//     rarely, green) for the adapter's sake, never silently: each such case is triaged
//     as an adapter case, and the convention gap itself is an S4 finding to the lane
//     that owns `Anweisung.lean` (a `.loop` that bound its variable would need no this).
// A2. `#ret`. Bound in-term to `(.lit .absent)` (shape `.opt`) but recorded `None` by
//     the walk; the replay below reads it as `.opt`. Any OTHER unshaped residue in a
//     loop-entry snapshot (`let … else` names, `await` names -- both bound in-term with
//     a shape the walk does not record) skips the routine with a named reason instead
//     of guessing: a guessed shape would make the goal easier, the one direction a
//     refusal exists against.
//
// ## The scope replay -- exact by construction
//
// `LoopInfo::entry_locals` is the walk's push sequence before the loop (branch bindings
// truncated away by `block_term`, later bindings not yet pushed). Replaying `binde`
// over `entry ++ synthetics ++ snapshot` rebuilds Lean's list EXACTLY: cons on absent,
// keep on equal, and Lean refuses on different (the theorem is dead there anyway, and
// red is then the CORRECT cell -- a U3-class finding when Rust accepts). Youngest entry
// stays head; the parameter tail keeps declaration order, which is `paramUmgebung`'s.
//
/// A Lean identifier from a routine name -- Gabbro names are words, this fires on nothing.
fn seam_ident(s: &str) -> String {
    let mut o = String::new();
    for ch in s.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            o.push(ch);
        } else {
            o.push('_');
        }
    }
    if o.is_empty() || o.starts_with(|c: char| c.is_ascii_digit()) {
        o = format!("n{o}");
    }
    o
}

fn opt_shape_term(sh: Option<Shape>) -> String {
    match sh {
        Some(s) => format!("(some {})", s.lean()),
        None => "none".to_string(),
    }
}

/// One `binde` step over the replayed scope (youngest head): cons on absent, keep on
/// equal. Different means Lean's `binde` gave `none` -- the theorem is dead there; the
/// old entry is kept so the output stays valid Lean, and the red witness names the cell.
fn seam_bind(scope: &mut Vec<(String, Shape)>, n: &str, sh: Shape) {
    if scope.iter().any(|(m, _)| m == n) {
        // Present: Lean keeps the entry on equal and refuses on different (the theorem
        // is dead there either way) -- so keep, never duplicate.
    } else {
        scope.insert(0, (n.to_string(), sh));
    }
}

/// Rebuild the `Umgebung` at a loop's entry, youngest first. `None` (a NON-`#ret`
/// unshaped residue -- A2) refuses the routine instead of guessing.
fn replay_scope(
    entry: &[(String, Shape)],
    synth: &[(String, Shape)],
    pushes: &[(String, Option<Shape>)],
) -> Option<Vec<(String, Shape)>> {
    let mut scope: Vec<(String, Shape)> = entry.to_vec();
    for (n, sh) in synth {
        seam_bind(&mut scope, n, *sh);
    }
    for (n, sh) in pushes {
        match sh {
            Some(s) => seam_bind(&mut scope, n, *s),
            // A2: bound in-term to `(.lit .absent)`.
            None if n == "#ret" => seam_bind(&mut scope, n, Shape::Opt),
            None => return None,
        }
    }
    Some(scope)
}

fn umgebung_term(scope: &[(String, Shape)]) -> String {
    if scope.is_empty() {
        return "[]".to_string();
    }
    let parts: Vec<String> = scope
        .iter()
        .map(|(n, sh)| format!("({}, .form {})", quoted(n), sh.lean()))
        .collect();
    format!("[{}]", parts.join(", "))
}

/// `reason R { … }` items: the error-channel cases per reason type, unit-wide.
fn reason_cases(baum: &Programm) -> BTreeMap<String, Vec<String>> {
    let mut out: BTreeMap<String, Vec<String>> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _| {
        if let ItemArt::Reason(r) = &item.art {
            out.insert(
                r.name.text.clone(),
                r.faelle.iter().map(|f| f.name.text.clone()).collect(),
            );
        }
    });
    out
}

/// The `or R` of every FOREIGN callee (their declarations are not in `Unit`).
fn foreign_fehler(baum: &Programm) -> BTreeMap<String, String> {
    let mut out: BTreeMap<String, String> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _| {
        if let ItemArt::Funktion(f) = &item.art {
            if !matches!(&f.rumpf, FnRumpf::Block(_)) {
                if let Some(r) = &f.fehler {
                    out.insert(f.name.text.clone(), r.text.clone());
                }
            }
        }
    });
    out
}

fn sig_entry(params: &[(String, Option<Shape>)], erg: Option<Shape>, gruende: &[String]) -> String {
    let ps: Vec<String> = params
        .iter()
        .map(|(n, s)| format!("({}, {})", quoted(n), opt_shape_term(*s)))
        .collect();
    let gs: Vec<String> = gruende.iter().map(|g| quoted(g)).collect();
    format!(
        "{{ params := [{}], ergebnis := {}, gruende := [{}] }}",
        ps.join(", "),
        opt_shape_term(erg),
        gs.join(", ")
    )
}

/// The `Deklaration`, read from the declarations -- plus the routine's ghost carriers
/// (per routine, so two routines' `c#r1` never meet).
fn seam_decl(unit: &Unit, ghosts: &[(String, String, Shape)]) -> String {
    let mut tnames: Vec<&String> = unit.tables.keys().collect();
    tnames.sort();
    let mut slot_arms = Vec::new();
    for t in &tnames {
        let mut fs: Vec<&(String, Option<Shape>)> = unit.tables[*t].fields.iter().collect();
        fs.sort_by(|a, b| a.0.cmp(&b.0));
        for (f, sh) in fs {
            if let Some(sh) = sh {
                slot_arms.push(format!("    | {}, {} => some {}", quoted(t), quoted(f), sh.lean()));
            }
        }
    }
    let slot = if slot_arms.is_empty() {
        "fun _ _ => none".to_string()
    } else {
        format!("fun c f => match c, f with\n{}\n    | _, _ => none", slot_arms.join("\n"))
    };
    let mut count_arms = Vec::new();
    for t in &tnames {
        if let Some(n) = unit.tables[*t].count {
            count_arms.push(format!("    | {} => {}", quoted(t), int_lit(n)));
        }
    }
    let count = if count_arms.is_empty() {
        "fun _ => 0".to_string()
    } else {
        format!("fun c => match c with\n{}\n    | _ => 0", count_arms.join("\n"))
    };
    let mut rnames: Vec<&String> = unit.records.keys().collect();
    rnames.sort();
    let mut feld_arms = Vec::new();
    for t in &rnames {
        let mut fs: Vec<&(String, Option<Shape>)> = unit.records[*t].iter().collect();
        fs.sort_by(|a, b| a.0.cmp(&b.0));
        for (f, sh) in fs {
            if let Some(sh) = sh {
                feld_arms.push(format!("    | {}, {} => some {}", quoted(t), quoted(f), sh.lean()));
            }
        }
    }
    let mut seen_ghost: BTreeSet<(&str, &str)> = BTreeSet::new();
    for (carrier, field, sh) in ghosts {
        if unit.records.contains_key(carrier) {
            continue;
        }
        if seen_ghost.insert((carrier.as_str(), field.as_str())) {
            feld_arms.push(format!("    | {}, {} => some {}", quoted(carrier), quoted(field), sh.lean()));
        }
    }
    let feld = if feld_arms.is_empty() {
        "fun _ _ => none".to_string()
    } else {
        format!("fun c f => match c, f with\n{}\n    | _, _ => none", feld_arms.join("\n"))
    };
    let mut global_arms = Vec::new();
    let mut globals: Vec<(String, Shape)> = unit.statics_scalars.clone();
    globals.sort_by(|a, b| a.0.cmp(&b.0));
    for (n, sh) in &globals {
        global_arms.push(format!("    | {} => some {}", quoted(n), sh.lean()));
    }
    let global = if global_arms.is_empty() {
        "fun _ => none".to_string()
    } else {
        format!("fun g => match g with\n{}\n    | _ => none", global_arms.join("\n"))
    };
    format!("{{ slot := {slot}, count := {count}, feld := {feld}, global := {global} }}")
}

/// **The unit's seam module: one `checker_agrees` witness per carried routine.**
/// Routines the duty channel refuses get a comment with the reason, not a theorem --
/// a missing witness is counted, never silent (the `@seam` line adds up).
pub fn witness(baum: &Programm, datei: &str) -> String {
    let unit = Unit::sammle(baum);
    let goals = routine_goals(&unit);
    let name = module_name(datei);
    let reasons = reason_cases(baum);
    let ffehlers = foreign_fehler(baum);
    let gruende_of: &dyn Fn(Option<&str>) -> Vec<String> = &|r| {
        r.and_then(|n| reasons.get(n)).cloned().unwrap_or_default()
    };

    let mut s = String::new();
    s.push_str("/-  Written by `gabbro_check::lean::witness` (S4). Do not edit -- the source is\n");
    s.push_str("    the `.gab`, and this module is the seam measurement, not the duty register.\n\n");
    s.push_str("    One `checker_agrees` theorem per routine the duty channel carries: the duty\n");
    s.push_str("    datum, held against `pruefe` (`Gabbro.Sicherheit.Anweisung`). Both checkers\n");
    s.push_str("    accept, or the file goes red at `lake build` -- per routine, per run.\n\n");
    s.push_str("    Adapters (see the function docs): loop variables are bound to `0` at the\n");
    s.push_str("    routine's entry (A1), `#ret` replays as its recorded shape (`.opt` where\n");
    s.push_str("    unshaped, A2), routines with a loop\n");
    s.push_str("    over an unshaped residue (`let … else`/`await` names) get NO witness by name.\n");
    s.push_str("    The proposition is `.isSome = true`: `= some _` leaves a metavariable that\n");
    s.push_str("    `decide` cannot evaluate. Entry is the parameter scope: `[]` would refuse\n");
    s.push_str("    every routine that reads a parameter.\n-/\n\n");
    s.push_str("import Gabbro.Sicherheit.Anweisung\n\n");
    s.push_str("set_option autoImplicit false\n\nopen Gabbro.Body Gabbro.Sicherheit\n\n");
    s.push_str(&format!("namespace GabbroSeam.{name}\n\n"));

    // ---- the signatures, once for the unit -----------------------------------------
    s.push_str("/-! ## The callee signatures, from the declarations -/\n\n");
    s.push_str("def seamSig : String → Option Signatur := fun f => match f with\n");
    let mut signames: Vec<&String> = unit.routines.keys().collect();
    signames.sort();
    for r in &signames {
        let info = &unit.routines[*r];
        let gruende = gruende_of(info.decl.fehler.as_ref().map(|i| i.text.as_str()));
        s.push_str(&format!(
            "  | {} => some {}\n",
            quoted(r),
            sig_entry(&info.params, unit.result_shape.get(*r).copied().flatten(), &gruende)
        ));
    }
    let mut fnames: Vec<&String> = unit.foreign.keys().collect();
    fnames.sort();
    for f in &fnames {
        let info = &unit.foreign[*f];
        // A foreign `or R` names its cases through the declaration (`foreign_fehler`);
        // without the declaration the channel is unstatable here -- `[]`, and a `let …
        // else` over it goes red at `decide`, by name.
        let gruende = if info.fehler {
            gruende_of(ffehlers.get(f.as_str()).map(String::as_str))
        } else {
            Vec::new()
        };
        s.push_str(&format!(
            "  | {} => some {}\n",
            quoted(&info.name),
            sig_entry(&info.params, info.result, &gruende)
        ));
    }
    // Generated ops take unshaped premises (`OpInfo` names no shapes): every parameter
    // is untyped, and an untyped target accepts every value (`passtIn … none`). Their
    // answer has no declared shape either -- a `bindCall` on one goes red, triaged.
    let mut onames: Vec<&String> = unit.ops.keys().collect();
    onames.sort();
    for o in &onames {
        let info = &unit.ops[*o];
        let ps: Vec<(String, Option<Shape>)> =
            info.params.iter().map(|n| (n.clone(), None)).collect();
        s.push_str(&format!("  | {} => some {}\n", quoted(&info.key), sig_entry(&ps, None, &[])));
    }
    // A transition is called with the device handle (`call_parts`); untyped, like above.
    let mut tnames2: Vec<&String> = unit.transitions.keys().collect();
    tnames2.sort();
    for t in &tnames2 {
        let info = &unit.transitions[*t];
        s.push_str(&format!(
            "  | {} => some {}\n",
            quoted(&info.name),
            sig_entry(&[("d".to_string(), None)], None, &[])
        ));
    }
    s.push_str("  | _ => none\n\n");

    // ---- one witness per carried routine --------------------------------------------
    s.push_str("/-! ## The witnesses -- one theorem per carried routine -/\n\n");
    let mut getragen = 0usize;
    let mut ausgelassen: Vec<(String, String)> = Vec::new();
    for g in &goals {
        let r = seam_ident(&g.name);
        let body = match &g.body {
            Ok(b) => b.clone(),
            Err(e) => {
                ausgelassen.push((g.name.clone(), format!("duty-refused ({})", e.tag())));
                continue;
            }
        };
        let info = &unit.routines[&g.name];
        // A1: every loop variable bound to `0` at the routine's entry.
        let mut vars: Vec<String> = Vec::new();
        for l in &g.loops {
            if l.var != "#pass" && !vars.contains(&l.var) {
                vars.push(l.var.clone());
            }
        }
        let synth: Vec<(String, Shape)> =
            vars.iter().map(|v| (v.clone(), Shape::IntIn(0, 0))).collect();
        // The entry scope: the shaped parameters, in declaration order (`paramUmgebung`).
        let entry: Vec<(String, Shape)> = info
            .params
            .iter()
            .filter_map(|(n, sh)| sh.map(|v| (n.clone(), v)))
            .collect();
        // The loop scopes, replayed (`#ret` reads as its recorded shape -- `.opt`
        // for the unshaped residue via A2; any other unshaped residue skips the
        // routine instead of guessing).
        let mut schleifen: Vec<(String, Vec<(String, Shape)>)> = Vec::new();
        let mut rueckstand: Vec<String> = Vec::new();
        for l in &g.loops {
            match replay_scope(&entry, &synth, &l.entry_locals) {
                Some(scope) => schleifen.push((l.id.clone(), scope)),
                None => {
                    let mut res: Vec<String> = l
                        .entry_locals
                        .iter()
                        .filter(|(n, sh)| sh.is_none() && n != "#ret")
                        .map(|(n, _)| n.clone())
                        .collect();
                    res.sort();
                    res.dedup();
                    rueckstand = res;
                    break;
                }
            }
        }
        if !rueckstand.is_empty() {
            ausgelassen.push((g.name.clone(), format!("unshaped-scope ({})", rueckstand.join(", "))));
            continue;
        }
        // The ghosts this routine's bindings opened (per routine: two routines' `c#r1`
        // never meet).
        let ghosts: Vec<(String, String, Shape)> = g
            .seen_records
            .iter()
            .filter(|(carrier, _, _)| !unit.records.contains_key(carrier))
            .cloned()
            .collect();
        s.push_str(&format!("def seamD_{r} : Deklaration :=\n  {}\n\n", seam_decl(&unit, &ghosts)));
        if schleifen.is_empty() {
            s.push_str(&format!("def seamLoops_{r} : String → Option Umgebung := fun _ => none\n\n"));
        } else {
            s.push_str(&format!("def seamLoops_{r} : String → Option Umgebung := fun id => match id with\n"));
            for (id, scope) in &schleifen {
                s.push_str(&format!("  | {} => some {}\n", quoted(id), umgebung_term(scope)));
            }
            s.push_str("  | _ => none\n\n");
        }
        s.push_str(&format!(
            "def seamP_{r} : Programm := {{ D := seamD_{r}, sig := seamSig, schleife := seamLoops_{r} }}\n\n"
        ));
        // The adapted body: A1's bindings first, then the duty datum unchanged.
        let inner = body
            .strip_prefix('[')
            .and_then(|b| b.strip_suffix(']'))
            .unwrap_or("");
        let binds: Vec<String> = vars
            .iter()
            .map(|v| format!("(.bindName {} (.lit (.int 0)))", quoted(v)))
            .collect();
        let adapted = if inner.trim().is_empty() {
            format!("[{}]", binds.join(", "))
        } else if binds.is_empty() {
            body.clone()
        } else {
            format!("[{}, {}]", binds.join(", "), inner)
        };
        let erg = if info.decl.ergebnis.is_none() {
            "none".to_string()
        } else {
            opt_shape_term(unit.result_shape.get(&g.name).copied().flatten())
        };
        s.push_str(&format!(
            "theorem checker_agrees_{r} : (pruefeBlock seamP_{r} {erg} {} {adapted}).isSome = true := by decide\n\n",
            umgebung_term(&entry)
        ));
        getragen += 1;
    }
    for (n, w) in &ausgelassen {
        s.push_str(&format!("-- no witness for `{n}`: {w}\n"));
    }
    if !ausgelassen.is_empty() {
        s.push('\n');
    }
    s.push_str(&format!(
        "-- @seam {} routines {} witnesses {} skipped\n\nend GabbroSeam.{name}\n",
        goals.len(),
        getragen,
        ausgelassen.len()
    ));
    s
}
