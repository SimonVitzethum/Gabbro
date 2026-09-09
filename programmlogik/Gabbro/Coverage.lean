/-
  Gabbro -- **what this grammar covers, and what it hands to the person.**

  `Body.lean` says what a Gabbro program MEANS. This file says something else, about the
  channel that sits on top of it: *for every form of the language that can put an obligation
  in front of a person, who answers for it.*

  The sentence `PLAN.md` serves is

  > a person who wants to verify a Gabbro program formally proves their own logic, and
  > nothing else.

  Read as a slogan that is unfalsifiable. Read as a proposition it is section 6 of this
  file: `Form` enumerates the obligation-generating forms the grammar admits, `classify`
  gives each of them exactly one verdict, and `the_sentence` says that every form which is
  NOT the person's own logic is carried, carried by the automation, assumed by a name, or
  refused with a tag.

  ## What is proved here, and what is NOT

  **NOT proved: "the tactic closes it".** Tactic success is a property of a RUN, not a
  theorem, and a file that claimed otherwise would be worse than no file. The verdict
  `Verdict.carriedByTactic` exists for exactly the forms whose obligations `gabbro_auto`
  closes on the corpus and for which no general theorem stands here; `Discharges` is
  `False` for them, on purpose, so that moving a form into `carried` without a lemma
  breaks `carried_discharges` instead of passing quietly.

  **Proved: the plumbing rows of `PLAN.md` section 1, as general lemmas.** Every form the
  classifier calls `carried` has a proposition below it that is quantified over an
  ARBITRARY program of that shape -- an arbitrary environment, an arbitrary typing, an
  arbitrary body -- and a proof. Where the general form is false without a side condition,
  the side condition is a PREMISE and there is a theorem saying the premise cannot be
  dropped (section 5.9).

  ## The trap this file is inside

  `Form` and `Reason` are HAND-WRITTEN mirrors of `crates/gabbro-check/src/parse.rs` and
  `crates/gabbro-check/src/lean.rs`. A mirror that drifts still typechecks, and then the
  theorem is about a language that is not Gabbro. That is the `W7`/`W16` class: two
  registers over one thing, one of them read by a guard. The guard is
  `instrumente/pruefe-deckung.py`, and what it does NOT check is written in its own header.
-/
import Gabbro.Body

namespace Gabbro.Coverage

open Gabbro.Body

/-! ## 1. The refusal register, mirrored

    One constructor per variant of `LeanReason` (`crates/gabbro-check/src/lean.rs`), one
    string per `LeanReason::tag`, one kind per `LeanReason::kind`. **The order is the order
    of `LeanReason::ALL`**, so that a reader can hold the two lists side by side and
    `pruefe-deckung.py` can compare them line for line. -/

/-- Why a form gets no goal -- `lean.rs`'s `Kind`. -/
inductive Kind where
  /-- Not a gap: an assumption, stated in `Assumed rho` and visible. -/
  | assumption
  /-- This channel has no Lean term for the form. -/
  | noTerm
  /-- The term exists; the wiring from the duty to the contract does not. -/
  | noWiring
  deriving DecidableEq, Repr

/-- The 42 variants of `LeanReason`, in the order of `LeanReason::ALL`. -/
inductive Reason where
  | passCounter | quantifiedThreads | quantifiedMappings | bufferLength | recordValue
  | slotRecordArray | foreignBody | invariant | callSite | devicePromise | walkInvariant
  | callStatement | loop | concurrent | publish | await | exchange | observe
  | errorPropagation | narrowing | nonLocalExit | compoundAssign | matchNotOption | float
  | oldState | quantified | callInExpression | builtin | lockWitness | result
  | resultInBody | otherValue | expression | carrier | fieldShape | specShape
  | generatedOp | transition | constructedValue | calleeContract | returnInLoop | recursion
  | counted
  deriving DecidableEq, Repr

/-! ### `quantifiedThreads` -- a refusal whose ground is measured, not merely stated

    It is the largest single class in the register: **six duties over the corpus** on
    2026-09-08, and of those six only TWO are clauses -- `probe-neun-domaenen`'s
    `d8_threads` and `probe-stellungen`'s `s8_threads`. The other four are the INHERITED
    refusals of section 9.2: one untranslatable invariant on `Knoten` refuses every duty
    that writes it. *A class counted in duties is four fifths one clause.*

        for f in $(git ls-files 'beispiele/*.gab' 'messung/proben/*.gab' | grep -v gift); do
          ./target/debug/gabbro pflichten --lean "$f"; done | grep -c 'refused (quantified-threads)'

    **Why it does not become a goal, and why no surface closes it cheaply.** Every other
    domain hands the model a number: `slots of T` emits `.forallSlots "t" 128 …`, and `128`
    is `T`'s `count`. A `threads over T` -- or a mark at the table saying "this is the
    thread set" -- would have to emit that same `.forallSlots "t" 128 …`: the same
    constructor, the same index set, the same proposition, and byte-identical C. **That is
    a synonym of `slots of T`**, and a synonym is exactly the "form that means nothing" of
    `messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md` section 1.

    The surface that would carry more has to say which slots are LIVE -- a predicate at the
    declaration, and a second constructor beside `forallSlots`. Gabbro has no such
    declaration and has never decided what liveness is. **So the refusal stands, with a
    measured ground rather than an asserted one** (`PLAN.md` section 15), and the checker
    closed the last form of `threads` that stated nothing (`D024`) instead.
-/

/-- `LeanReason::tag` -- the string the register prints beside the duty. -/
def Reason.tag : Reason → String
  | .foreignBody => "foreign-body"
  | .invariant => "table-invariant"
  | .callSite => "call-site"
  | .devicePromise => "device-promise"
  | .walkInvariant => "walk-invariant"
  | .callStatement => "call-not-compositional"
  | .loop => "loop"
  | .concurrent => "concurrent-statement"
  | .publish => "publish"
  | .await => "await"
  | .exchange => "exchange"
  | .observe => "observe"
  | .errorPropagation => "let-else"
  | .narrowing => "narrow"
  | .passCounter => "pass-counter"
  | .nonLocalExit => "non-local-exit"
  | .compoundAssign => "compound-assignment"
  | .matchNotOption => "match-not-option"
  | .float => "float"
  | .oldState => "old-state"
  | .quantified => "quantified"
  | .quantifiedThreads => "quantified-threads"
  | .quantifiedMappings => "quantified-mappings"
  | .bufferLength => "layout-buffer-length"
  | .recordValue => "record-value"
  | .slotRecordArray => "slot-record-array"
  | .callInExpression => "call-in-expression"
  | .builtin => "builtin"
  | .lockWitness => "lock-witness"
  | .result => "result-in-ensures"
  | .resultInBody => "result-in-body"
  | .otherValue => "other-value"
  | .expression => "no-term"
  | .carrier => "carrier-not-a-table"
  | .fieldShape => "no-shape-for-field"
  | .specShape => "spec-not-an-expression"
  | .generatedOp => "generated-op"
  | .transition => "device-transition"
  | .constructedValue => "constructed-value"
  | .calleeContract => "callee-requires-no-term"
  | .returnInLoop => "return-in-loop"
  | .recursion => "recursion"
  | .counted => "counted"

/-- `LeanReason::kind`. -/
def Reason.kind : Reason → Kind
  | .foreignBody | .devicePromise | .walkInvariant => .assumption
  | .recursion => .noWiring
  | _ => .noTerm

/-! ## 2. The forms the grammar admits that can put an obligation in front of a person

    **One constructor per form**, mirroring the emitter's decision points (`lean.rs`) and
    `PLAN.md` section 1's table. `refusedOrAssumed` carries the 42 of section 1, so the
    enumeration is 45 constructors and 44 + 42 = 86 forms when it is expanded. -/

inductive Form where
  -- ### the sequential core
  /-- `f(a, b);` -- a call taken over the callee's contract. -/
  | callStatement
  /-- `let x = f(a, b);` -- a call whose answer is bound. -/
  | callResultBound
  /-- `g(f(a))`, `if f(a)`, `return f(a) + 1` -- a call INSIDE an expression, which the
      emitter hoists into a `let` before it writes anything (`hoisted_call`). -/
  | callInExpressionHoisted
  /-- A chain of calls: the outer one's contract fires at the state the inner one left. -/
  | callChain
  /-- A place outside the callee's `writes` list is untouched. -/
  | callFrame
  /-- The wiring itself: a duty proved over a body IS the callee's contract. -/
  | contractFromDuty
  /-- One pass of a loop, carrying the `invariant`. -/
  | loopPass
  /-- One pass of a loop over a domain with an index range -- the pass may use `lo <= k < hi`. -/
  | loopPassInRange
  /-- One pass of a loop that counts its passes -- the pass may use `passes`. -/
  | loopPassCounted
  /-- A routine that calls itself: the induction over `decreases`. -/
  | recursionSelf
  /-- A CYCLE of the call graph: one induction over the shared measure. -/
  | recursionCycle
  /-- A recursive call from inside the routine's own ranged loop. -/
  | recursionInLoop
  /-- `c.slots[i].f = e;`, `r.f = e;`, `g = e;` -- a store keeps the world well typed. -/
  | store
  /-- A read of the world produces a witness of the declared shape. -/
  | read
  /-- A declared range (`u8 in 0 .. 15`) as a shape, in both directions. -/
  | declaredRange
  /-- `match v { Case(p) => ... }` over a `tagged` value: no arm of the model gets stuck on
      a case the type admits. -/
  | taggedMatch
  /-- `match e { Some(b) => ..., None => ... }` -- the option match. -/
  | optionMatch
  /-- An answer with a declared shape and range, at the caller's binding. -/
  | answerWithShape
  /-- An answer without a shape (a token, a record): it exists, and the binding is filled. -/
  | answerWithoutShape
  /-- `if` -- the two branches AND the third outcome, which is stuck and not silent. -/
  | controlFlow
  /-- `let x = e;` -- a plain binding. -/
  | localBinding
  /-- Two statements in a row. -/
  | sequencing
  /-- `next` ends the pass, `leave` ends the loop. -/
  | loopExit
  /-- A read beside a store: the same place, or another one. -/
  | storeBesideRead
  /-- A store beside a `reaches` chain: the chain is unchanged. -/
  | storeBesideChain
  /-- The arithmetic the model carries: C's truncation, the sign of `%`, a zero
      denominator, a negative operand at a bit operation, a mask, a shift. -/
  | arithmeticSemantics
  /-- The BOUNDS the checker decided (`x & 251 <= 255`, `a*b <= A*B`, `0 <= a/b <= a`),
      closed by `gabbro_bits`/`gabbro_mul`/`gabbro_divmod`/`omega`. -/
  | arithmeticBounds
  /-- The heartbeat budget: a step that runs away takes the theorem down (`gabbro_try`). -/
  | budget
  /-- A quantified premise, instantiated at the index in play. -/
  | quantifiedPremise
  -- ### the quantifier domains that are NOT refused
  /-- `forall k in slots of T : ...` -/
  | quantSlots
  /-- `forall x in elems of a : ...` -/
  | quantElems
  /-- `forall x in queue R : ...` -/
  | quantQueue
  /-- `forall x in chain(a, b) in c : ...` -/
  | quantChain
  /-- `forall f in fields of F : ...` where the body does not read the binder. -/
  | quantFields
  /-- `forall x in descendants of T.slots[p] : ...`, `... in ancestors of ...` -- the index
      domain CUT by a reach along the table's `tree` edge. -/
  | quantReach
  -- ### the seven statements the emitter carried and this enumeration did not name
  --     (2026-09-08, agent h). Found by the register `LeanCarried` of `lean.rs`: each of
  --     these is a form the grammar admits, the emitter writes a term for, and `Form` was
  --     silent about. Six of the seven are the CARRIED half of a form whose REFUSED half
  --     was named all along -- `let ... else` at a place is refused and at a call carried,
  --     `publishes`/`awaits` at a suffix refused and bare carried, `locks` refused only as
  --     a fallback, `narrow` refused off a range and carried on one. *The refusal was in
  --     the register because refusals have an enum; the carry was not because carries had
  --     none.*
  /-- `match e { Case => ... }` over a REASON -- the third `match`, beside the tagged one
      and the option one. `M123` closes the enumeration, so an arm-less reason is stuck. -/
  | reasonMatch
  /-- `return f(a);` -- a call whose answer is returned straight on (`Stmt.retCall`). -/
  | callResultReturned
  /-- `let n = f(a) else (e) { ... };` -- the error propagation. The `place` shape of the
      same syntax is refused (`let-else`); THIS shape is carried. -/
  | callWithErrorExit
  /-- `breaking I { ... }` -- the suspension of a table invariant. Its meaning is the
      body's, and the duty stands beside it. -/
  | invariantSuspension
  /-- `publishes a = e;` at a bare atomic -- a store into the world at a `.global` place.
      At a place with a suffix it is refused (`publish`). -/
  | publishAtomic
  /-- `awaits n = a;` at a bare atomic -- a read of the world into a binding. At a place
      with a suffix it is refused (`await`). -/
  | awaitAtomic
  /-- `locks S { ... }` -- the critical section. Its meaning is the body's, and what makes
      the sequential reading sound is that the lock is held (`H005`/`H006`). -/
  | criticalSection
  -- ### the named assumptions (`PLAN.md` section 6)
  /-- The initial state: a well-typed world in which every invariant holds. -/
  | initialState
  /-- `Runs rho f body` -- that the environment IS the program. -/
  | environmentRunsBody
  /-- `RunsLoop` / `RunsLoopIn` -- that the environment runs the loop over its domain. -/
  | environmentRunsLoop
  /-- `RunsLoopN` -- that a traversal of a table of `count N` runs at most `N` passes; the
      sentence `by unvisited` makes. -/
  | environmentBoundsPasses
  /-- Two carrier names are two places; a record type is one object. -/
  | distinctCarriers
  /-- The checker and the emitter are trusted, not verified (`PLAN.md` section 1). -/
  | checkerAndEmitterTrusted
  -- ### the person's own logic
  /-- An `ensures` that follows from what the body does. -/
  | ownEnsures
  /-- An `invariant` that survives a pass because of what the pass changes. -/
  | ownInvariant
  /-- A `requires` strong enough for the body. -/
  | ownRequires
  /-- A `reaches` chain still intact after a relink. -/
  | ownReaches
  -- ### every form the emitter refuses or assumes BY NAME
  | refusedOrAssumed (r : Reason)
  deriving DecidableEq, Repr

/-! ## 3. The verdict -- one per form, total by construction -/

inductive Verdict where
  /-- Carried, and a general lemma of section 5 proves it. -/
  | carried
  /-- Closed by the automation on the corpus; **no general theorem stands here**. -/
  | carriedByTactic
  /-- Assumed, under the name given. -/
  | assumed (name : String)
  /-- Refused, under the tag the emitter prints. -/
  | refused (tag : String)
  /-- The person's own logic. -/
  | ownLogic
  /-- **Never returned.** It exists so that "the classifier answers for every form" is a
      proposition (`classify_total`) and not a property of the reader's attention. -/
  | unhandled
  deriving DecidableEq, Repr

def classify : Form → Verdict
  | .callStatement | .callResultBound | .callInExpressionHoisted | .callChain
  | .callFrame | .contractFromDuty
  | .loopPass | .loopPassInRange | .loopPassCounted
  | .recursionSelf | .recursionCycle | .recursionInLoop
  | .store | .read | .declaredRange | .taggedMatch | .optionMatch
  | .answerWithShape | .answerWithoutShape | .controlFlow | .localBinding | .sequencing
  | .loopExit | .storeBesideRead | .storeBesideChain | .arithmeticSemantics
  | .quantifiedPremise | .quantSlots | .quantElems | .quantQueue | .quantChain
  | .quantFields | .quantReach
  | .reasonMatch | .callResultReturned | .callWithErrorExit | .invariantSuspension
  | .publishAtomic | .awaitAtomic | .criticalSection => .carried
  | .arithmeticBounds => .carriedByTactic
  | .budget => .carriedByTactic
  | .initialState => .assumed "Initially s0"
  | .environmentRunsBody => .assumed "Runs rho f body"
  | .environmentRunsLoop => .assumed "RunsLoop / RunsLoopIn"
  | .environmentBoundsPasses => .assumed "RunsLoopN -- by unvisited"
  | .distinctCarriers => .assumed "two carrier names are two places"
  | .checkerAndEmitterTrusted => .assumed "the checker and the emitter are trusted"
  | .ownEnsures | .ownInvariant | .ownRequires | .ownReaches => .ownLogic
  | .refusedOrAssumed r =>
      match r.kind with
      | .assumption => .assumed r.tag
      | _ => .refused r.tag

/-! ## 4. What "own logic" IS -- a definition, not a slogan

    Written without ever mentioning `classify`: otherwise `ownLogic_is_the_persons` would
    be true by saying so, and would say nothing. -/

/-- Where the TEXT of the obligation comes from. -/
inductive Origin where
  /-- The grammar and the model fix the statement; no clause of the program says it. -/
  | language
  /-- The statement is a clause the person wrote. -/
  | person
  /-- Neither: hardware, foreign code, the environment, the toolchain. -/
  | outside
  deriving DecidableEq, Repr

def origin : Form → Origin
  | .initialState | .environmentRunsBody | .environmentRunsLoop | .environmentBoundsPasses
  | .distinctCarriers | .checkerAndEmitterTrusted => .outside
  | .ownEnsures | .ownInvariant | .ownRequires | .ownReaches => .person
  | .refusedOrAssumed r => match r.kind with | .assumption => .outside | _ => .language
  | _ => .language

/-- The four clauses a person writes. An obligation whose text is one of them is theirs;
    an obligation that names none of them is the language's. -/
def personalClauses : List String := ["ensures", "invariant", "requires", "reaches"]

def personalClause : Form → Option String
  | .ownEnsures => some "ensures"
  | .ownInvariant => some "invariant"
  | .ownRequires => some "requires"
  | .ownReaches => some "reaches"
  | _ => none

/-- **The obligation is the person's**: its text comes from a clause they wrote, and that
    clause is one of the four. Nothing here mentions `classify`. -/
def IsOwnLogic (f : Form) : Prop :=
  origin f = .person ∧ ∃ c, personalClause f = some c ∧ c ∈ personalClauses

/-! ## 5. The discharges -- one general lemma per carried form

    Every proposition below quantifies over an ARBITRARY environment, an arbitrary typing
    and an arbitrary program of the shape in question. None of them is about a unit of the
    corpus. Where a premise had to be added, the comment says what the premise is about --
    and section 5.9 proves that dropping it would make the statement false. -/

/-! ### 5.1 Calls -- `Contract`, `Frame`, and the precondition that is not decoration -/

/-- **A call: the callee's contract fires, the caller's locals survive, and every place
    outside the frame is what it was.**

    The ONLY premise beyond the contract and the frame is `WF Gamma s.world` at the call
    site. The callee's precondition is NOT a premise: `step` gets stuck unless
    `eval t pre = some (.bool true)` holds at the callee's entry state, so a caller that
    got past the call has established it by that very fact -- which is what the `V` duty
    of the register means and why it is carried by the caller's theorem. -/
def CallCarried : Prop :=
  ∀ (ρ : Env) (Γ : Typing) (f : String) (ps : List String) (as : List Expr) (pre : Expr)
    (Q : State → State → Option Value → Prop) (w : List String) (s s' : State),
    Contract ρ f (fun t => WF Γ t.world ∧ eval t pre = some (.bool true)) Q →
    Frame ρ f w →
    WF Γ s.world →
    step ρ (.call f ps as pre) s = .running s' →
    ∃ vs, evalAll s as = some vs ∧
      Q ⟨s.world, bindAll ps vs (fun _ => .absent)⟩
        (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).1
        (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).2 ∧
      s'.world = (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).1.world ∧
      s'.local' = s.local' ∧
      ∀ p, p.carrier ∉ w → s'.world p = s.world p

theorem call_carried : CallCarried := by
  intro ρ Γ f ps as pre Q w s s' hc hfr hwf hstep
  simp only [step] at hstep
  split at hstep
  · rename_i vs hvs
    split at hstep
    · rename_i hpre
      refine ⟨vs, hvs, ?_, ?_, ?_, ?_⟩
      · exact hc _ ⟨hwf, hpre⟩
      · cases hstep; rfl
      · cases hstep; rfl
      · intro p hp
        cases hstep
        exact hfr _ p hp
    · exact absurd hstep (by simp)
  · exact absurd hstep (by simp)

/-- **A call whose answer is bound** -- the commonest call shape, and the shape a call
    inside an expression becomes after the emitter hoists it. Same premises; in addition
    the binding holds the callee's answer and no other name moves. -/
def CallResultCarried : Prop :=
  ∀ (ρ : Env) (Γ : Typing) (f n : String) (ps : List String) (as : List Expr) (pre : Expr)
    (Q : State → State → Option Value → Prop) (w : List String) (s s' : State),
    Contract ρ f (fun t => WF Γ t.world ∧ eval t pre = some (.bool true)) Q →
    Frame ρ f w →
    WF Γ s.world →
    step ρ (.bindCall n f ps as pre) s = .running s' →
    ∃ vs v, evalAll s as = some vs ∧
      Q ⟨s.world, bindAll ps vs (fun _ => .absent)⟩
        (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).1
        (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).2 ∧
      (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).2 = some v ∧
      s'.world = (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).1.world ∧
      s'.local' n = v ∧
      (∀ m, m ≠ n → s'.local' m = s.local' m) ∧
      ∀ p, p.carrier ∉ w → s'.world p = s.world p

/-- The frame-free core of `CallResultCarried`, so that the chain lemma can use it without
    inventing a `writes` list for the callee. -/
theorem bindCall_core (ρ : Env) (Γ : Typing) (f n : String) (ps : List String)
    (as : List Expr) (pre : Expr) (Q : State → State → Option Value → Prop) (s s' : State)
    (hc : Contract ρ f (fun t => WF Γ t.world ∧ eval t pre = some (.bool true)) Q)
    (hwf : WF Γ s.world)
    (hstep : step ρ (.bindCall n f ps as pre) s = .running s') :
    ∃ vs v, evalAll s as = some vs ∧
      Q ⟨s.world, bindAll ps vs (fun _ => .absent)⟩
        (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).1
        (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).2 ∧
      (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).2 = some v ∧
      s'.world = (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).1.world ∧
      s'.local' n = v ∧
      (∀ m, m ≠ n → s'.local' m = s.local' m) := by
  simp only [step] at hstep
  split at hstep
  · rename_i vs hvs
    split at hstep
    · rename_i hpre
      split at hstep
      · rename_i v hv
        refine ⟨vs, v, hvs, hc _ ⟨hwf, hpre⟩, hv, ?_, ?_, ?_⟩
        · cases hstep; rfl
        · cases hstep; simp [bindLocal]
        · intro m hm; cases hstep; simp [bindLocal, hm]
      · exact absurd hstep (by simp)
    · exact absurd hstep (by simp)
  · exact absurd hstep (by simp)

theorem call_result_carried : CallResultCarried := by
  intro ρ Γ f n ps as pre Q w s s' hc hfr hwf hstep
  obtain ⟨vs, v, hvs, hq, hv, hw, hn, hm⟩ :=
    bindCall_core ρ Γ f n ps as pre Q s s' hc hwf hstep
  refine ⟨vs, v, hvs, hq, hv, hw, hn, hm, ?_⟩
  intro p hp
  rw [hw]
  exact hfr _ p hp

/-- **A chain of calls, innermost first.** The outer call's contract fires at the state the
    inner one left -- and the world is still well typed there because every `_post` the
    emitter writes carries `WF` back. That conjunct is the premise; without it the outer
    contract has nothing to stand on. -/
def CallChainCarried : Prop :=
  ∀ (ρ : Env) (Γ : Typing) (f g n m : String) (ps qs : List String) (as bs : List Expr)
    (pf pg : Expr) (Qg : State → State → Option Value → Prop) (s u u' : State),
    Contract ρ f (fun t => WF Γ t.world ∧ eval t pf = some (.bool true))
      (fun _ t' _ => WF Γ t'.world) →
    Contract ρ g (fun t => WF Γ t.world ∧ eval t pg = some (.bool true)) Qg →
    WF Γ s.world →
    step ρ (.bindCall n f ps as pf) s = .running u →
    step ρ (.bindCall m g qs bs pg) u = .running u' →
    exec ρ [Stmt.bindCall n f ps as pf, Stmt.bindCall m g qs bs pg] s = .running u' ∧
      ∃ ws, evalAll u bs = some ws ∧
        Qg ⟨u.world, bindAll qs ws (fun _ => .absent)⟩
           (ρ g ⟨u.world, bindAll qs ws (fun _ => .absent)⟩).1
           (ρ g ⟨u.world, bindAll qs ws (fun _ => .absent)⟩).2

theorem call_chain_carried : CallChainCarried := by
  intro ρ Γ f g n m ps qs as bs pf pg Qg s u u' hcf hcg hwf h1 h2
  constructor
  · simp only [exec, h1, h2]
  · obtain ⟨vs, _, _, hq, _, hw, _, _⟩ :=
      bindCall_core ρ Γ f n ps as pf (fun _ t' _ => WF Γ t'.world) s u hcf hwf h1
    have hwfu : WF Γ u.world := by rw [hw]; exact hq
    obtain ⟨ws, _, hws, hq2, _, _, _, _⟩ :=
      bindCall_core ρ Γ g m qs bs pg Qg u u' hcg hwfu h2
    exact ⟨ws, hws, hq2⟩

/-- **The frame, as a rewrite.** A place whose carrier the callee does not name reads the
    caller's world. -/
def CallFrameCarried : Prop :=
  ∀ (ρ : Env) (f : String) (w : List String), Frame ρ f w →
    ∀ (t : State) (p : Place), p.carrier ∉ w → (ρ f t).1.world p = t.world p

theorem call_frame_carried : CallFrameCarried := fun ρ f w fr t p h => Frame_read ρ f w fr t p h

/-- **The wiring: a duty proved over the body IS the callee's contract**, for any
    environment that runs the body. This is the row of `PLAN.md` section 1 that turns a
    person's theorem into something a caller may use. -/
def ContractFromDutyCarried : Prop :=
  ∀ (ρ : Env) (f : String) (body : List Stmt) (pre : State → Prop)
    (post : State → State → Option Value → Prop),
    Runs ρ f body →
    (∀ t, pre t → ∃ s', finalState (exec ρ body t) = some s' ∧
        post t s' (finalValue (exec ρ body t))) →
    Contract ρ f pre post

theorem contract_from_duty_carried : ContractFromDutyCarried :=
  fun ρ f body pre post hr hd => contract_of_duty ρ f body pre post hr hd

/-! ### 5.2 The answer -- with a shape and without one -/

/-- **An answer with a declared shape and range lands in the caller's binding with its
    bounds.** `result_clause` in the callee's `_post` is the premise; the conclusion is
    what the caller reads, and it is an integer in the declared range. -/
def AnswerWithShapeCarried : Prop :=
  ∀ (ρ : Env) (Γ : Typing) (f n : String) (ps : List String) (as : List Expr) (pre : Expr)
    (lo hi : Int) (s s' : State),
    Contract ρ f (fun t => WF Γ t.world ∧ eval t pre = some (.bool true))
      (fun _ _ r => ∃ x : Int, r = some (.int x) ∧ lo ≤ x ∧ x ≤ hi) →
    WF Γ s.world →
    step ρ (.bindCall n f ps as pre) s = .running s' →
    ∃ x : Int, s'.local' n = .int x ∧ lo ≤ x ∧ x ≤ hi

theorem answer_with_shape_carried : AnswerWithShapeCarried := by
  intro ρ Γ f n ps as pre lo hi s s' hc hwf hstep
  obtain ⟨vs, v, _, hq, hv, _, hn, _⟩ :=
    bindCall_core ρ Γ f n ps as pre _ s s' hc hwf hstep
  obtain ⟨x, hx, hlo, hhi⟩ := hq
  rw [hv] at hx
  injection hx with hvx
  exact ⟨x, by rw [hn, hvx], hlo, hhi⟩

/-- **An answer without a shape still fills the binding** -- `∃ v, r = some v` is exactly
    what keeps `bindCall` from getting stuck, and that is the whole of what the clause is
    for. -/
def AnswerWithoutShapeCarried : Prop :=
  ∀ (ρ : Env) (Γ : Typing) (f n : String) (ps : List String) (as : List Expr) (pre : Expr)
    (s : State) (vs : List Value),
    Contract ρ f (fun t => WF Γ t.world ∧ eval t pre = some (.bool true))
      (fun _ _ r => ∃ v, r = some v) →
    WF Γ s.world →
    evalAll s as = some vs →
    eval ⟨s.world, bindAll ps vs (fun _ => .absent)⟩ pre = some (.bool true) →
    step ρ (.bindCall n f ps as pre) s ≠ .stuck

theorem answer_without_shape_carried : AnswerWithoutShapeCarried := by
  intro ρ Γ f n ps as pre s vs hc hwf hvs hpre
  obtain ⟨v, hv⟩ := hc ⟨s.world, bindAll ps vs (fun _ => .absent)⟩ ⟨hwf, hpre⟩
  simp only [step, hvs, hpre, hv]
  simp

/-! ### 5.3 The world -- a store keeps it well typed, a read draws a witness from it -/

/-- **Every store keeps `WF`, given the shape obligation the emitter emits.** All three
    store statements, in one proposition; the premise is exactly `gabbro_wf`'s goal, and
    section 5.9 shows the statement is FALSE without it. The locals do not move. -/
def StoreCarried : Prop :=
  ∀ (ρ : Env) (Γ : Typing) (s s' : State), WF Γ s.world →
    (∀ (c fld : String) (i e : Expr), Stmt.assign c i fld e = Stmt.assign c i fld e →
      (∀ (k : Int) (v : Value), eval s i = some (.int k) → eval s e = some v →
        ∀ sh, Γ (.slot c k fld) = some sh → v.hasShape sh = true) →
      step ρ (.assign c i fld e) s = .running s' → WF Γ s'.world ∧ s'.local' = s.local') ∧
    (∀ (c fld : String) (e : Expr),
      (∀ (v : Value), eval s e = some v →
        ∀ sh, Γ (.field c fld) = some sh → v.hasShape sh = true) →
      step ρ (.assignField c fld e) s = .running s' → WF Γ s'.world ∧ s'.local' = s.local') ∧
    (∀ (g : String) (e : Expr),
      (∀ (v : Value), eval s e = some v →
        ∀ sh, Γ (.global g) = some sh → v.hasShape sh = true) →
      step ρ (.assignGlobal g e) s = .running s' → WF Γ s'.world ∧ s'.local' = s.local')

theorem store_carried : StoreCarried := by
  intro ρ Γ s s' hwf
  refine ⟨?_, ?_, ?_⟩
  · intro c fld i e _ hsh hstep
    simp only [step] at hstep
    split at hstep
    · rename_i k v hi he
      cases hstep
      exact ⟨WF_store Γ s.world _ v hwf (hsh k v hi he), rfl⟩
    · exact absurd hstep (by simp)
  · intro c fld e hsh hstep
    simp only [step] at hstep
    split at hstep
    · rename_i v he
      cases hstep
      exact ⟨WF_store Γ s.world _ v hwf (hsh v he), rfl⟩
    · exact absurd hstep (by simp)
  · intro g e hsh hstep
    simp only [step] at hstep
    split at hstep
    · rename_i v he
      cases hstep
      exact ⟨WF_store Γ s.world _ v hwf (hsh v he), rfl⟩
    · exact absurd hstep (by simp)

/-- **Every read of a declared place has a witness** -- one per shape of the model, and
    the ranged one comes with its bounds. -/
def ReadCarried : Prop :=
  ∀ (Γ : Typing) (σ : World) (p : Place), WF Γ σ →
    (Γ p = some .int → ∃ n, σ p = .int n) ∧
    (∀ lo hi, Γ p = some (.intIn lo hi) → ∃ n, σ p = .int n ∧ lo ≤ n ∧ n ≤ hi) ∧
    (Γ p = some .bool → ∃ b, σ p = .bool b) ∧
    (Γ p = some .opt → σ p = .absent ∨ ∃ n, σ p = .present n) ∧
    (∀ cs, Γ p = some (.sum cs) →
      ∃ t q, σ p = .tagged t q ∧ Shape.caseOk cs t q = true)

theorem read_carried : ReadCarried := by
  intro Γ σ p h
  exact ⟨fun hp => WF_int Γ σ p h hp,
         fun lo hi hp => WF_intIn Γ σ p lo hi h hp,
         fun hp => WF_bool Γ σ p h hp,
         fun hp => WF_opt Γ σ p h hp,
         fun cs hp => WF_sum Γ σ p cs h hp⟩

/-- **A declared range IS its bounds, in both directions.** `Shape.intIn lo hi` is what a
    `u8 in lo .. hi` means: a read from such a place is an integer between the bounds, and
    an integer between the bounds may be stored into it. -/
def DeclaredRangeCarried : Prop :=
  ∀ (v : Value) (lo hi : Int),
    v.hasShape (.intIn lo hi) = true ↔ ∃ n, v = .int n ∧ lo ≤ n ∧ n ≤ hi

theorem declared_range_carried : DeclaredRangeCarried := by
  intro v lo hi
  cases v <;> simp [Value.hasShape]

/-! ### 5.4 Control flow -- and the third outcome, which is stuck and never silent -/

/-- **An `if` takes one of its two branches, or gets stuck.** The third conjunct is the
    load-bearing one: a condition that is not a truth value does NOT silently take a
    branch. -/
def ControlFlowCarried : Prop :=
  ∀ (ρ : Env) (c : Expr) (a b : List Stmt) (s : State),
    (eval s c = some (.bool true) → step ρ (.ite c a b) s = exec ρ a s) ∧
    (eval s c = some (.bool false) → step ρ (.ite c a b) s = exec ρ b s) ∧
    ((∀ x : Bool, eval s c ≠ some (.bool x)) → step ρ (.ite c a b) s = .stuck)

theorem control_flow_carried : ControlFlowCarried := by
  intro ρ c a b s
  refine ⟨fun h => by simp [step, h], fun h => by simp [step, h], fun h => ?_⟩
  simp only [step]
  split
  · rename_i ht; exact absurd ht (h true)
  · rename_i hf; exact absurd hf (h false)
  · rfl

/-- **The option match**: the arm by the constructor, the payload bound, or stuck. -/
def OptionMatchCarried : Prop :=
  ∀ (ρ : Env) (g : Expr) (bn : String) (onP onA : List Stmt) (s : State),
    (∀ k : Int, eval s g = some (.present k) →
      step ρ (.onOption g bn onP onA) s
        = exec ρ onP { s with local' := bindLocal s.local' bn (.int k) }) ∧
    (eval s g = some .absent → step ρ (.onOption g bn onP onA) s = exec ρ onA s)

theorem option_match_carried : OptionMatchCarried := by
  intro ρ g bn onP onA s
  exact ⟨fun k h => by simp [step, h], fun h => by simp [step, h]⟩

/-- **A `let` binds one name and touches nothing else** -- not the world, not another
    local. -/
def LocalBindingCarried : Prop :=
  ∀ (ρ : Env) (n : String) (e : Expr) (s s' : State),
    step ρ (.bindName n e) s = .running s' →
    ∃ v, eval s e = some v ∧ s'.local' n = v ∧ s'.world = s.world ∧
      ∀ m, m ≠ n → s'.local' m = s.local' m

theorem local_binding_carried : LocalBindingCarried := by
  intro ρ n e s s' hstep
  simp only [step] at hstep
  split at hstep
  · rename_i v he
    cases hstep
    exact ⟨v, he, by simp [bindLocal], rfl, fun m hm => by simp [bindLocal, hm]⟩
  · exact absurd hstep (by simp)

/-- **Two statements in a row.** The second runs at the state the first left, and where
    the first does not leave a running state, the sequence ends there -- a `return` in the
    middle is not stepped over. -/
def SequencingCarried : Prop :=
  ∀ (ρ : Env) (a : Stmt) (rest : List Stmt) (s : State),
    (∀ u, step ρ a s = .running u → exec ρ (a :: rest) s = exec ρ rest u) ∧
    ((∀ u, step ρ a s ≠ .running u) → exec ρ (a :: rest) s = step ρ a s)

theorem sequencing_carried : SequencingCarried := by
  intro ρ a rest s
  constructor
  · intro u h; simp [exec, h]
  · intro hno
    cases hst : step ρ a s with
    | running u => exact absurd hst (hno u)
    | returned u v => simp [exec, hst]
    | exited u => simp [exec, hst]
    | left u => simp [exec, hst]
    | stuck => simp [exec, hst]

/-- **`next` ends the pass and `leave` ends the loop** -- and `iterate` does the right
    thing with each: after `next` the remaining indices are visited, after `leave` they are
    not. -/
def LoopExitCarried : Prop :=
  ∀ (ρ : Env) (s t t' : State) (body : List Stmt) (v : String) (k : Int) (ks : List Int),
    step ρ .exit s = .exited s ∧ step ρ .leave s = .left s ∧
    (exec ρ body { t with local' := bindLocal t.local' v (.int k) } = .left t' →
      iterate ρ body v (k :: ks) t = some t') ∧
    (exec ρ body { t with local' := bindLocal t.local' v (.int k) } = .exited t' →
      iterate ρ body v (k :: ks) t = iterate ρ body v ks t')

theorem loop_exit_carried : LoopExitCarried := by
  intro ρ s t t' body v k ks
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro h; simp [iterate, h]
  · intro h; simp [iterate, h]

/-- **The arms fit the value**: some arm carries this case's name, and every arm that
    carries it binds a payload exactly when the value has one. Both halves are decided by
    the emitter from the declared case list -- `D005` demands the match be exhaustive, and
    `Shape.sum` carries which cases have payloads. -/
def ArmsFit (arms : List (String × Option String × List Stmt)) (t : String)
    (q : Option Int) : Prop :=
  (∃ a ∈ arms, a.1 = t) ∧ (∀ a ∈ arms, a.1 = t → a.2.1.isSome = q.isSome)

/-- **A `match` over a `tagged` value never gets stuck on a case the type admits.** The
    first conjunct is the shape half: from the declared case list of a well-typed place,
    the arms fit whatever the world can hold there. The second is the step half: where the
    arms fit, the model does not get stuck. -/
def TaggedMatchCarried : Prop :=
  (∀ (cs : List (String × Option (Option (Int × Int))))
     (arms : List (String × Option String × List Stmt)) (t : String) (q : Option Int),
     Shape.caseOk cs t q = true →
     (∀ c ∈ cs, ∃ a ∈ arms, a.1 = c.1) →
     (∀ a ∈ arms, ∀ c ∈ cs, a.1 = c.1 → a.2.1.isSome = c.2.isSome) →
     ArmsFit arms t q) ∧
  (∀ (ρ : Env) (arms : List (String × Option String × List Stmt)) (g : Expr) (s : State)
     (t : String) (q : Option Int),
     eval s g = some (.tagged t q) → ArmsFit arms t q →
     ∃ (b : List Stmt) (u : State), step ρ (.onTag g arms) s = exec ρ b u)

theorem tagged_match_carried : TaggedMatchCarried := by
  constructor
  · intro cs arms t q hok hcov hpay
    have hex : ∃ c ∈ cs, c.1 = t ∧ Shape.payloadOk c.2 q = true := by
      simp only [Shape.caseOk, List.any_eq_true] at hok
      obtain ⟨c, hc, h⟩ := hok
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨c, hc, h.1, h.2⟩
    obtain ⟨c, hc, hct, hcp⟩ := hex
    refine ⟨?_, ?_⟩
    · obtain ⟨a, ha, hat⟩ := hcov c hc
      exact ⟨a, ha, by rw [hat, hct]⟩
    · intro a ha hat
      have hq : q.isSome = c.2.isSome := by
        cases hc2 : c.2 with
        | none => cases q with
          | none => simp
          | some n => rw [hc2] at hcp; simp [Shape.payloadOk] at hcp
        | some p => cases q with
          | none => rw [hc2] at hcp; cases p <;> simp [Shape.payloadOk] at hcp
          | some n => simp
      rw [hq]
      exact hpay a ha c hc (by rw [hat, hct])
  · intro ρ arms g s t q hg hfit
    simp only [step, hg]
    obtain ⟨⟨a, ha, hat⟩, hpay⟩ := hfit
    clear hg
    induction arms with
    | nil => exact absurd ha (by simp)
    | cons b rest ih =>
      obtain ⟨bn, bd, bb⟩ := b
      simp only [pickTag]
      by_cases hb : bn = t
      · subst hb
        have hfit := hpay (bn, bd, bb) (by simp) rfl
        simp only
        cases bd with
        | none => exact ⟨bb, s, rfl⟩
        | some vn =>
          simp only [Option.isSome] at hfit
          cases q with
          | none => simp at hfit
          | some k =>
            exact ⟨bb, { s with local' := bindLocal s.local' vn (.int k) }, rfl⟩
      · simp only [if_neg hb]
        refine ih ?_ ?_
        · intro c hc; exact hpay c (List.mem_cons_of_mem _ hc)
        · rcases List.mem_cons.mp ha with h | h
          · subst h; exact absurd hat hb
          · exact h

/-! ### 5.5 A store beside a read, and a store beside a chain -/

/-- **A read against a store**: the same place gives the stored value, another place gives
    what it had -- including two slots of one carrier at different indices, which is the
    case `gabbro_split` decides. -/
def StoreBesideReadCarried : Prop :=
  ∀ (σ : World) (p q : Place) (v : Value),
    store σ p v p = v ∧ (q ≠ p → store σ p v q = σ q) ∧
    ∀ (c fld : String) (k j : Int), k ≠ j →
      store σ (.slot c k fld) v (.slot c j fld) = σ (.slot c j fld)

theorem store_beside_read_carried : StoreBesideReadCarried := by
  intro σ p q v
  refine ⟨store_here σ p v, fun h => store_elsewhere σ p q v h, ?_⟩
  intro c fld k j h
  exact store_elsewhere σ _ _ v (by simp [h.symm])

/-- **A store beside a chain leaves the chain as it was.** The premise is a SYNTACTIC side
    condition the emitter decides -- the place written is not a link of this chain -- and
    it cannot be dropped: a store into the chain field is precisely what a relink is, and
    that is the person's own logic (`PLAN.md` section 5.1). -/
def StoreBesideChainCarried : Prop :=
  ∀ (σ : World) (c via : String) (to : Int) (p : Place) (v : Value),
    (∀ m, p ≠ .slot c m via) → ∀ (k : Int) (n : Nat),
      chase (store σ p v) c via to k n = chase σ c via to k n

theorem store_beside_chain_carried : StoreBesideChainCarried :=
  fun σ c via to p v h k n => chase_store_ne σ c via to p v h k n

/-! ### 5.6 The arithmetic the model carries -/

/-- **What the model says about the checker's arithmetic** -- and it is the MEANING, not
    the bounds: C's truncation toward zero, the sign of `%`, a zero denominator that gets
    stuck, a negative operand that stops a bit operation, a mask that stays non-negative,
    and a shift that is a multiplication and a division. The BOUNDS the checker decided are
    a different form (`Form.arithmeticBounds`), and they are not carried by a theorem. -/
def ArithmeticSemanticsCarried : Prop :=
  -- C truncates toward zero where Lean's own `/` rounds down, and `%` follows the dividend
  (binop .div (.int (-7)) (.int 2) = some (.int (-3)) ∧ ((-7 : Int) / 2) = -4) ∧
  (binop .rem (.int (-7)) (.int 2) = some (.int (-1))
   ∧ binop .rem (.int 7) (.int (-2)) = some (.int 1) ∧ ((-7 : Int) % 2) = 1) ∧
  -- a zero denominator answers nothing, in both operators
  (∀ a : Int, binop .div (.int a) (.int 0) = none ∧ binop .rem (.int a) (.int 0) = none) ∧
  -- a negative operand stops a bit operation instead of guessing a width
  (∀ a : Int, a < 0 →
     binop .band (.int a) (.int 1) = none ∧ binop .band (.int 1) (.int a) = none
     ∧ binop .bor (.int a) (.int 1) = none ∧ binop .bxor (.int a) (.int 1) = none
     ∧ binop .shl (.int a) (.int 1) = none ∧ binop .shr (.int a) (.int 1) = none
     ∧ binop .shl (.int 1) (.int a) = none ∧ binop .shr (.int 1) (.int a) = none) ∧
  -- a shift IS a multiplication and a division
  (∀ a b : Int, 0 ≤ a → 0 ≤ b →
     binop .shl (.int a) (.int b) = some (.int (a * 2 ^ b.toNat))
     ∧ binop .shr (.int a) (.int b) = some (.int (a.tdiv (2 ^ b.toNat)))) ∧
  -- and a mask, where it answers at all, answers with a non-negative number
  (∀ a b : Int, 0 ≤ a → 0 ≤ b →
     ∃ n : Nat, binop .band (.int a) (.int b) = some (.int (n : Int)))

theorem arithmetic_semantics_carried : ArithmeticSemanticsCarried :=
  ⟨div_truncates_where_lean_rounds_down, rem_follows_the_dividend,
   division_by_zero_is_stuck, a_negative_operand_stops_the_bits,
   a_shift_is_arithmetic, a_mask_stays_non_negative⟩

/-! ### 5.7 Quantifiers -- the premise, and the domains that are not refused -/

/-- **A quantified premise, instantiated at the index in play** -- and the other direction,
    which is how a quantified GOAL over an index range is proved. `gabbro_instantiate` and
    `gabbro_forall` are the tactics; this is the theorem under them. -/
def QuantifiedPremiseCarried : Prop :=
  ∀ (f : Nat → Option Value) (n : Nat),
    (allBelow f n = some (.bool true) → ∀ k, k < n → f k = some (.bool true)) ∧
    ((∀ k, k < n → f k = some (.bool true)) → allBelow f n = some (.bool true))

theorem quantified_premise_carried : QuantifiedPremiseCarried :=
  fun f n => ⟨(allBelow_true_iff f n).mp, (allBelow_true_iff f n).mpr⟩

/-- **A quantifier whose domain is an index range.** `slots of T`, `elems of a` and
    `queue R` are three surfaces of ONE discharge: each hangs on a declaration that gives a
    count, and each becomes `allBelow` over `0 ..< count`. *They share this proposition,
    and that sharing is the finding, not a shortcut.* -/
def IndexDomainCarried : Prop := QuantifiedPremiseCarried

theorem index_domain_carried : IndexDomainCarried := quantified_premise_carried

/-- **A quantifier over a chain** -- `forall x in chain(a, b) in c`. The chain the model
    follows with fuel and the chain as a relation are the same chain, in both directions;
    and a chain reaches where it starts. -/
def ChainDomainCarried : Prop :=
  (∀ (σ : World) (c via : String) (to k : Int) (n : Nat),
     chase σ c via to k n = some (.bool true) → Reaches σ c via k to) ∧
  (∀ (σ : World) (c via : String) (k to : Int), Reaches σ c via k to →
     ∃ n : Nat, chase σ c via to k n = some (.bool true)) ∧
  (∀ (σ : World) (c via : String) (to : Int) (n : Nat),
     chase σ c via to to n = some (.bool true))

theorem chain_domain_carried : ChainDomainCarried :=
  ⟨fun σ c via to k n h => reaches_of_chase σ c via to n k h,
   fun σ c via k to h => chase_of_reaches σ c via k to h,
   fun σ c via to n => chase_refl σ c via to n⟩

/-- **A quantifier over `fields of`** where the body does not read the binder: the field
    list is declared and finite, so the quantifier is a finite conjunction, and it
    collapses to the body. -/
def FieldsDomainCarried : Prop :=
  ∀ (f : Nat → Option Value), (∀ k, f k = some (.bool true)) →
    ∀ n : Nat, allBelow f n = some (.bool true)

theorem fields_domain_carried : FieldsDomainCarried :=
  fun f h n => (allBelow_true_iff f n).mpr (fun k _ => h k)

/-! ### 5.8 Loops and recursion -- the inductions, stated once for every program -/

def LoopPassCarried : Prop :=
  ∀ (ρ : Env) (id : String) (wf : State → Prop) (inv : Expr) (body : List Stmt) (v : String),
    RunsLoop ρ id body v →
    (∀ t (k : Int), wf t → eval t inv = some (.bool true) →
      ∃ t', finalState (exec ρ body { t with local' := bindLocal t.local' v (.int k) })
        = some t' ∧ wf t' ∧ eval t' inv = some (.bool true)) →
    LoopRule ρ id wf inv

theorem loop_pass_carried : LoopPassCarried :=
  fun ρ id wf inv body v hr hb => looprule_of_body ρ id wf inv body v hr hb

def LoopPassInRangeCarried : Prop :=
  ∀ (ρ : Env) (id : String) (wf : State → Prop) (inv : Expr) (body : List Stmt) (v : String)
    (lo hi : Int), RunsLoopIn ρ id body v lo hi →
    (∀ t (k : Int), lo ≤ k → k < hi → wf t → eval t inv = some (.bool true) →
      ∃ t', finalState (exec ρ body { t with local' := bindLocal t.local' v (.int k) })
        = some t' ∧ wf t' ∧ eval t' inv = some (.bool true)) →
    LoopRule ρ id wf inv

theorem loop_pass_in_range_carried : LoopPassInRangeCarried :=
  fun ρ id wf inv body v lo hi hr hb => looprule_of_body_in ρ id wf inv body v lo hi hr hb

def LoopPassCountedCarried : Prop :=
  ∀ (ρ : Env) (id : String) (wf : State → Prop) (inv : Expr) (body : List Stmt)
    (v pv : String) (lo hi np : Int), RunsLoopN ρ id body v lo hi np →
    (∀ t (k i : Int), lo ≤ k → k < hi → 0 ≤ i → i < np →
      t.local' pv = .int i → wf t → eval t inv = some (.bool true) →
      ∃ t', finalState (exec ρ body { t with local' := bindLocal t.local' v (.int k) })
        = some t' ∧ wf t' ∧ eval t' inv = some (.bool true) ∧ t'.local' pv = .int (i + 1)) →
    LoopRuleP ρ id wf inv pv

theorem loop_pass_counted_carried : LoopPassCountedCarried :=
  fun ρ id wf inv body v pv lo hi np hr hb =>
    looprule_of_body_p ρ id wf inv body v pv lo hi np hr hb

def RecursionSelfCarried : Prop :=
  ∀ (ρ : Env) (f : String) (body : List Stmt) (pre : State → Prop)
    (post : State → State → Option Value → Prop) (e : Expr), Runs ρ f body →
    (∀ t, pre t → ContractBelow ρ f e t pre post →
      ∃ s', finalState (exec ρ body t) = some s' ∧ post t s' (finalValue (exec ρ body t))) →
    Contract ρ f pre post

theorem recursion_self_carried : RecursionSelfCarried :=
  fun ρ f body pre post e hr hd => contract_of_duty_rec ρ f body pre post e hr hd

def RecursionCycleCarried : Prop :=
  ∀ (ρ : Env) (rs : List Member), (∀ r ∈ rs, Runs ρ r.name r.body) →
    (∀ r ∈ rs, ∀ t, r.pre t → (∀ r' ∈ rs, ContractBelowM ρ r' r.measure t) →
      ∃ s', finalState (exec ρ r.body t) = some s' ∧
        r.post t s' (finalValue (exec ρ r.body t))) →
    ∀ r ∈ rs, Contract ρ r.name r.pre r.post

theorem recursion_cycle_carried : RecursionCycleCarried :=
  fun ρ rs hr hd => contracts_of_duties_rec ρ rs hr hd

def RecursionInLoopCarried : Prop :=
  ∀ (ρ : Env) (f : String) (body : List Stmt) (pre : State → Prop)
    (post : State → State → Option Value → Prop) (e : Expr) (wf : State → Prop)
    (id : String) (lbody : List Stmt) (v : String) (lo hi : Int) (inv : Expr),
    Runs ρ f body → RunsLoopIn ρ id lbody v lo hi →
    (∀ (s0 : State), pre s0 → ContractBelow ρ f e s0 pre post →
      ∀ (t : State) (k : Int), lo ≤ k → k < hi → wf t → eval t e = eval s0 e →
        eval t inv = some (.bool true) →
        ∃ t', finalState (exec ρ lbody { t with local' := bindLocal t.local' v (.int k) })
                = some t' ∧ (wf t' ∧ eval t' e = eval s0 e)
              ∧ eval t' inv = some (.bool true)) →
    (∀ t, pre t → ContractBelow ρ f e t pre post →
        LoopRule ρ id (fun u => wf u ∧ eval u e = eval t e) inv →
      ∃ s', finalState (exec ρ body t) = some s' ∧
        post t s' (finalValue (exec ρ body t))) →
    Contract ρ f pre post

theorem recursion_in_loop_carried : RecursionInLoopCarried :=
  fun ρ f body pre post e wf id lbody v lo hi inv hr hl hb hd =>
    contract_of_duty_rec_loop_in ρ f body pre post e wf id lbody v lo hi inv hr hl hb hd

/-! ### 5.8b The seven statements the register found (2026-09-08, agent h)

    Every proposition here answers for a form the emitter has carried since the day it was
    written and this enumeration did not name. They are not new behaviour of the emitter;
    they are the half of it that had no register. -/

/-- **A quantifier over a reach domain** -- `descendants of`, `ancestors of`. The domain is
    the table's index range CUT by a chain along the `tree` edge, so the discharge is both
    halves at once: the index range as `allBelow`, and the chain the model follows with fuel
    against the chain as a relation. -/
def ReachDomainCarried : Prop := IndexDomainCarried ∧ ChainDomainCarried

theorem reach_domain_carried : ReachDomainCarried :=
  ⟨index_domain_carried, chain_domain_carried⟩

/-- **A `match` over a reason.** Where some arm carries the case's name the model runs that
    arm; where the subject is not a reason at all it is STUCK, which is the honest outcome
    and not a silent fall-through. -/
def ReasonMatchCarried : Prop :=
  (∀ (ρ : Env) (arms : List (String × List Stmt)) (g : Expr) (s : State) (x : String),
     eval s g = some (.reason x) → (∃ a ∈ arms, a.1 = x) →
     ∃ b : List Stmt, step ρ (.onReason g arms) s = exec ρ b s) ∧
  (∀ (ρ : Env) (arms : List (String × List Stmt)) (g : Expr) (s : State),
     (∀ x, eval s g ≠ some (.reason x)) → step ρ (.onReason g arms) s = .stuck)

theorem reason_match_carried : ReasonMatchCarried := by
  constructor
  · intro ρ arms g s x hg ⟨a, ha, hax⟩
    simp only [step, hg]
    clear hg
    induction arms with
    | nil => exact absurd ha (by simp)
    | cons b rest ih =>
      obtain ⟨bn, bb⟩ := b
      simp only [pickArm]
      by_cases hb : bn = x
      · simp only [if_pos hb]
        exact ⟨bb, rfl⟩
      · simp only [if_neg hb]
        rcases List.mem_cons.mp ha with h | h
        · subst h; exact absurd hax hb
        · exact ih h
  · intro ρ arms g s hno
    cases hg : eval s g with
    | none => simp [step, hg]
    | some v =>
      cases v with
      | reason x => exact absurd hg (hno x)
      | int _ => simp [step, hg]
      | bool _ => simp [step, hg]
      | absent => simp [step, hg]
      | present _ => simp [step, hg]
      | tagged _ _ => simp [step, hg]

/-- **`return f(a);`** -- the callee's contract fires, the answer returned is the callee's,
    the world is the one the callee left and the caller's locals are untouched. Same
    premises as every other call: the world is well typed, and the precondition is not a
    premise because `step` is stuck without it. -/
def CallResultReturnedCarried : Prop :=
  ∀ (ρ : Env) (Γ : Typing) (f : String) (ps : List String) (as : List Expr) (pre : Expr)
    (Q : State → State → Option Value → Prop) (s s' : State) (r : Option Value),
    Contract ρ f (fun t => WF Γ t.world ∧ eval t pre = some (.bool true)) Q →
    WF Γ s.world →
    step ρ (.retCall f ps as pre) s = .returned s' r →
    ∃ vs, evalAll s as = some vs ∧
      Q ⟨s.world, bindAll ps vs (fun _ => .absent)⟩
        (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).1
        (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).2 ∧
      r = (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).2 ∧
      s'.world = (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).1.world ∧
      s'.local' = s.local'

theorem call_result_returned_carried : CallResultReturnedCarried := by
  intro ρ Γ f ps as pre Q s s' r hc hwf hstep
  simp only [step] at hstep
  split at hstep
  · rename_i vs hvs
    split at hstep
    · rename_i hpre
      refine ⟨vs, hvs, hc _ ⟨hwf, hpre⟩, ?_, ?_, ?_⟩
      · cases hstep; rfl
      · cases hstep; rfl
      · cases hstep; rfl
    · exact absurd hstep (by simp)
  · exact absurd hstep (by simp)

/-- **`let n = f(a) else (e) { ... };`** -- the one error propagation. The callee's contract
    fires exactly as at any other call; what the answer IS then decides the continuation: a
    `reason` runs the `else` block with the reason bound, any other value fills the binding
    and the body goes on. *Two exits out of one call, and both of them named.* -/
def CallWithErrorExitCarried : Prop :=
  ∀ (ρ : Env) (Γ : Typing) (f n : String) (ps : List String) (as : List Expr) (pre : Expr)
    (err : String) (onErr : List Stmt)
    (Q : State → State → Option Value → Prop) (s : State) (vs : List Value),
    Contract ρ f (fun t => WF Γ t.world ∧ eval t pre = some (.bool true)) Q →
    WF Γ s.world →
    evalAll s as = some vs →
    eval ⟨s.world, bindAll ps vs (fun _ => .absent)⟩ pre = some (.bool true) →
    Q ⟨s.world, bindAll ps vs (fun _ => .absent)⟩
      (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).1
      (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).2 ∧
    (∀ x, (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).2 = some (.reason x) →
      step ρ (.bindCallElse n f ps as pre err onErr) s =
        exec ρ onErr ⟨(ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).1.world,
                     bindLocal s.local' err (.reason x)⟩) ∧
    (∀ v, (ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).2 = some v →
      (∀ x, v ≠ .reason x) →
      step ρ (.bindCallElse n f ps as pre err onErr) s =
        .running ⟨(ρ f ⟨s.world, bindAll ps vs (fun _ => .absent)⟩).1.world,
                  bindLocal s.local' n v⟩)

theorem call_with_error_exit_carried : CallWithErrorExitCarried := by
  intro ρ Γ f n ps as pre err onErr Q s vs hc hwf hvs hpre
  refine ⟨hc _ ⟨hwf, hpre⟩, ?_, ?_⟩
  · intro x hx
    simp only [step, hvs, hpre, hx]
  · intro v hv hnr
    cases v with
    | reason x => exact absurd rfl (hnr x)
    | int _ => simp only [step, hvs, hpre, hv]
    | bool _ => simp only [step, hvs, hpre, hv]
    | absent => simp only [step, hvs, hpre, hv]
    | present _ => simp only [step, hvs, hpre, hv]
    | tagged _ _ => simp only [step, hvs, hpre, hv]

/-- **`breaking I { ... }` and `locks S { ... }` change no state of their own.** Both are
    the body's meaning, and both are read as such for a REASON that stands elsewhere: at a
    `breaking` the duty to restore `I` stands beside the block, at a `locks` the sequential
    reading is what the lock passes buy. *A model that added state here would be a second
    register over a statement a pass already decides.* -/
def InvariantSuspensionCarried : Prop :=
  ∀ (ρ : Env) (invs : List String) (b : List Stmt) (s : State),
    step ρ (.breaking invs b) s = exec ρ b s

theorem invariant_suspension_carried : InvariantSuspensionCarried := fun _ _ _ _ => rfl

def CriticalSectionCarried : Prop :=
  ∀ (ρ : Env) (l : String) (b : List Stmt) (s : State),
    step ρ (.locked l b) s = exec ρ b s

theorem critical_section_carried : CriticalSectionCarried := fun _ _ _ _ => rfl

/-- **`publishes a = e;`** -- a store into the world at a `.global` place, and nothing else
    moves. The payload list is what the pass checked; the datum carries the bare atomic. -/
def PublishAtomicCarried : Prop :=
  ∀ (ρ : Env) (a : String) (e : Expr) (pl : List String) (s s' : State),
    step ρ (.publish a e pl) s = .running s' →
    ∃ v, eval s e = some v ∧ s'.world = store s.world (.global a) v ∧ s'.local' = s.local'

theorem publish_atomic_carried : PublishAtomicCarried := by
  intro ρ a e pl s s' hstep
  simp only [step] at hstep
  split at hstep
  · rename_i v hv
    cases hstep
    exact ⟨v, hv, rfl, rfl⟩
  · exact absurd hstep (by simp)

/-- **`awaits n = a;`** -- a read of the world into a binding; the world is untouched and no
    other name moves. -/
def AwaitAtomicCarried : Prop :=
  ∀ (ρ : Env) (n a : String) (pl : List String) (s s' : State),
    step ρ (.awaitLoad n a pl) s = .running s' →
    s'.local' n = s.world (.global a) ∧ s'.world = s.world ∧
      ∀ m, m ≠ n → s'.local' m = s.local' m

theorem await_atomic_carried : AwaitAtomicCarried := by
  intro ρ n a pl s s' hstep
  simp only [step] at hstep
  cases hstep
  exact ⟨by simp [bindLocal], rfl, fun m hm => by simp [bindLocal, hm]⟩

/-! ### 5.9 The premises are not decoration -- two theorems that say so

    Both statements below are the general lemmas of section 5 with a premise REMOVED, and
    both are false. That is what makes the premise a finding about the emitter and not a
    convenience of the proof. -/

/-- **A store without the shape obligation can break the well-typed world.** The premise of
    `StoreCarried` is exactly the goal `gabbro_wf` is pointed at, and it is load-bearing:
    the emitter's side condition does real work. -/
theorem store_without_the_shape_can_break_WF :
    ¬ ∀ (Γ : Typing) (σ : World) (p : Place) (v : Value), WF Γ σ → WF Γ (store σ p v) := by
  intro h
  have hbad := h (fun _ => some .int) (fun _ => .int 0) (.global "g") (.bool true)
    (by intro p sh hp; cases hp; rfl)
  have := hbad (.global "g") .int rfl
  simp [store, Value.hasShape] at this

/-- **A contract says nothing where its precondition fails.** So the `V` duty at a call
    site -- that the caller established the callee's `requires` -- cannot be dropped, and
    the model is right to get STUCK at a call whose precondition does not hold: a model
    that carried on would let the caller conclude the callee's `post` from nothing. -/
theorem a_contract_says_nothing_where_its_precondition_fails :
    ¬ ∀ (ρ : Env) (f : String) (P : State → Prop)
        (Q : State → State → Option Value → Prop) (t : State),
      Contract ρ f P Q → Q t (ρ f t).1 (ρ f t).2 := by
  intro h
  exact h (fun _ t => (t, none)) "f" (fun _ => False) (fun _ _ _ => False)
    ⟨fun _ => .absent, fun _ => .absent⟩ (fun _ hf => hf.elim)

/-! ## 6. The top theorems

    `Discharges` is the general lemma that answers for a form. **It is `False` for every
    form the classifier does not call `carried`** -- on purpose: moving a form into
    `carried` without writing its lemma then breaks `carried_discharges` instead of
    passing quietly. -/

def Discharges : Form → Prop
  | .callStatement => CallCarried
  | .callResultBound => CallResultCarried
  | .callInExpressionHoisted => CallResultCarried
  | .callChain => CallChainCarried
  | .callFrame => CallFrameCarried
  | .contractFromDuty => ContractFromDutyCarried
  | .loopPass => LoopPassCarried
  | .loopPassInRange => LoopPassInRangeCarried
  | .loopPassCounted => LoopPassCountedCarried
  | .recursionSelf => RecursionSelfCarried
  | .recursionCycle => RecursionCycleCarried
  | .recursionInLoop => RecursionInLoopCarried
  | .store => StoreCarried
  | .read => ReadCarried
  | .declaredRange => DeclaredRangeCarried
  | .taggedMatch => TaggedMatchCarried
  | .optionMatch => OptionMatchCarried
  | .answerWithShape => AnswerWithShapeCarried
  | .answerWithoutShape => AnswerWithoutShapeCarried
  | .controlFlow => ControlFlowCarried
  | .localBinding => LocalBindingCarried
  | .sequencing => SequencingCarried
  | .loopExit => LoopExitCarried
  | .storeBesideRead => StoreBesideReadCarried
  | .storeBesideChain => StoreBesideChainCarried
  | .arithmeticSemantics => ArithmeticSemanticsCarried
  | .quantifiedPremise => QuantifiedPremiseCarried
  | .quantSlots => IndexDomainCarried
  | .quantElems => IndexDomainCarried
  | .quantQueue => IndexDomainCarried
  | .quantChain => ChainDomainCarried
  | .quantFields => FieldsDomainCarried
  | .quantReach => ReachDomainCarried
  | .reasonMatch => ReasonMatchCarried
  | .callResultReturned => CallResultReturnedCarried
  | .callWithErrorExit => CallWithErrorExitCarried
  | .invariantSuspension => InvariantSuspensionCarried
  | .publishAtomic => PublishAtomicCarried
  | .awaitAtomic => AwaitAtomicCarried
  | .criticalSection => CriticalSectionCarried
  | _ => False

/-- **Every form the classifier calls `carried` has a general lemma that discharges it.**
    This is the sentence "the plumbing is carried", as a proposition over the whole
    enumeration. -/
theorem carried_discharges : ∀ f : Form, classify f = .carried → Discharges f := by
  intro f h
  cases f <;> simp only [classify] at h <;>
    first
      | exact call_carried
      | exact call_result_carried
      | exact call_chain_carried
      | exact call_frame_carried
      | exact contract_from_duty_carried
      | exact loop_pass_carried
      | exact loop_pass_in_range_carried
      | exact loop_pass_counted_carried
      | exact recursion_self_carried
      | exact recursion_cycle_carried
      | exact recursion_in_loop_carried
      | exact store_carried
      | exact read_carried
      | exact declared_range_carried
      | exact tagged_match_carried
      | exact option_match_carried
      | exact answer_with_shape_carried
      | exact answer_without_shape_carried
      | exact control_flow_carried
      | exact local_binding_carried
      | exact sequencing_carried
      | exact loop_exit_carried
      | exact store_beside_read_carried
      | exact store_beside_chain_carried
      | exact arithmetic_semantics_carried
      | exact quantified_premise_carried
      | exact index_domain_carried
      | exact chain_domain_carried
      | exact fields_domain_carried
      | exact reach_domain_carried
      | exact reason_match_carried
      | exact call_result_returned_carried
      | exact call_with_error_exit_carried
      | exact invariant_suspension_carried
      | exact publish_atomic_carried
      | exact await_atomic_carried
      | exact critical_section_carried
      | (rename_i r; cases r <;> simp [Reason.kind] at h)
      | exact absurd h (by simp)

/-- **The classifier answers for every form.** Not "for every form I remembered to look
    at" -- `Verdict.unhandled` exists for exactly this proposition to have content. -/
theorem classify_total : ∀ f : Form, classify f ≠ .unhandled := by
  intro f
  cases f
  case refusedOrAssumed r => cases r <;> simp [classify, Reason.kind]
  all_goals simp [classify]

/-- **Everything the classifier hands back to the person is a clause the person wrote.**
    `IsOwnLogic` is defined in section 4 without mentioning `classify`, so this is a claim
    about two independent case analyses agreeing -- which is what makes it falsifiable. -/
theorem ownLogic_is_the_persons : ∀ f : Form, classify f = .ownLogic → IsOwnLogic f := by
  intro f h
  cases f
  case refusedOrAssumed r => cases r <;> simp [classify, Reason.kind] at h
  case ownEnsures => exact ⟨rfl, "ensures", rfl, by simp [personalClauses]⟩
  case ownInvariant => exact ⟨rfl, "invariant", rfl, by simp [personalClauses]⟩
  case ownRequires => exact ⟨rfl, "requires", rfl, by simp [personalClauses]⟩
  case ownReaches => exact ⟨rfl, "reaches", rfl, by simp [personalClauses]⟩
  all_goals simp [classify] at h

/-- **And nothing whose statement the language fixes is left in the person's lap.** This is
    the other half of the owner's sentence, and the half a coverage claim usually skips. -/
theorem nothing_of_the_language_is_left_to_the_person :
    ∀ f : Form, origin f = .language → classify f ≠ .ownLogic := by
  intro f h
  cases f
  case refusedOrAssumed r => cases r <;> simp [classify, Reason.kind]
  case ownEnsures => simp [origin] at h
  case ownInvariant => simp [origin] at h
  case ownRequires => simp [origin] at h
  case ownReaches => simp [origin] at h
  all_goals simp [classify]

/-- **A form with no personal clause is not the person's.** -/
theorem no_clause_no_own_logic : ∀ f : Form, personalClause f = none → ¬ IsOwnLogic f := by
  intro f h hown
  obtain ⟨_, c, hc, _⟩ := hown
  rw [h] at hc
  exact absurd hc (by simp)

/-- **Every refusal carries a tag the emitter actually prints**, and no tag is empty. -/
theorem every_refusal_has_an_emitter_tag :
    ∀ (f : Form) (t : String), classify f = .refused t → ∃ r : Reason, r.tag = t ∧ t ≠ "" := by
  intro f t h
  cases f
  case refusedOrAssumed r =>
    have ht : r.tag = t := by cases r <;> simp_all [classify, Reason.kind, Reason.tag]
    refine ⟨r, ht, ?_⟩
    subst ht
    cases r <;> simp [Reason.tag]
  all_goals simp [classify] at h

/-- **Every assumption carries a name**, and no name is empty. -/
theorem every_assumption_has_a_name :
    ∀ (f : Form) (n : String), classify f = .assumed n → n ≠ "" := by
  intro f n h
  cases f
  case refusedOrAssumed r =>
    cases r <;> simp_all [classify, Reason.kind, Reason.tag] <;> simp [← h]
  case initialState => simp only [classify] at h; cases h; simp
  case environmentRunsBody => simp only [classify] at h; cases h; simp
  case environmentRunsLoop => simp only [classify] at h; cases h; simp
  case environmentBoundsPasses => simp only [classify] at h; cases h; simp
  case distinctCarriers => simp only [classify] at h; cases h; simp
  case checkerAndEmitterTrusted => simp only [classify] at h; cases h; simp
  all_goals simp [classify] at h

/-- ## The sentence the plan serves, as a proposition

    **For every form of this grammar that is not the person's own logic, the channel
    answers**: a general lemma carries it, the automation closes it on the corpus, it is
    assumed under a name, or it is refused under a tag. Nothing falls through, and nothing
    that the language fixes is handed over in silence. -/
theorem the_sentence : ∀ f : Form, ¬ IsOwnLogic f →
    classify f = .carried ∨ classify f = .carriedByTactic ∨
    (∃ n, classify f = .assumed n) ∨ (∃ t, classify f = .refused t) := by
  intro f h
  cases hv : classify f with
  | carried => exact Or.inl rfl
  | carriedByTactic => exact Or.inr (Or.inl rfl)
  | assumed n => exact Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))
  | refused t => exact Or.inr (Or.inr (Or.inr ⟨t, rfl⟩))
  | ownLogic => exact absurd (ownLogic_is_the_persons f hv) h
  | unhandled => exact absurd hv (classify_total f)

/-! ## 7. What this file does NOT prove -- read this beside section 6

    1. **That `gabbro_auto` closes anything.** `Form.arithmeticBounds` and `Form.budget`
       are `carriedByTactic`, `Discharges` is `False` for both, and the corpus is the only
       evidence there is for them.
    2. **That `Form` is the whole grammar.** It is a hand-written mirror; the guard
       `instrumente/pruefe-deckung.py` holds the `Reason` half against `lean.rs` line for
       line, and the rest of the enumeration against the emitter's carried decision points
       only as far as the code names them. What it cannot check is written in its header.
    3. **That the emitter writes the statements these lemmas assume.** Every proposition
       above is about the MODEL. That the emitter's `_pre`/`_post`/`_inv` say what the
       person's `.gab` file says is the emitter's correctness, and `PLAN.md` section 1 puts
       it explicitly out of scope: the checker and the emitter are trusted, not verified
       (`Form.checkerAndEmitterTrusted`).
    4. **That a form which MEANS NOTHING is caught.**
       `messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md` section 1 measures four forms the
       checker admits and that have no effect. This file answers that document's point 2
       (the proof channel answers for every form) and says nothing about its points 1 and 3.

       *Its section 1.1 -- the quantifier domain as decoration -- has since been closed on
       the CHECKER's side and not on this one*: `D022` refuses a binder used against its
       domain, `D023` hints where the body never mentions it, and `D024` refuses the last
       green form of `threads` (`PLAN.md` section 15). **That is a change to what the
       grammar admits, and it makes no verdict of this file different** -- a form the
       checker now rejects raises no obligation, and a refusal that stands cannot become
       weaker for it.
-/

end Gabbro.Coverage
