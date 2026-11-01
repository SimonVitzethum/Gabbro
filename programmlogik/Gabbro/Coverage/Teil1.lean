module

public import Gabbro.Body

@[expose] public section



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
    · exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])
  · exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

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
        · cases hstep; simp only [bindLocal, ↓reduceIte]
        · intro m hm; cases hstep; simp only [bindLocal, hm, ↓reduceIte]
      · exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])
    · exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])
  · exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

end Gabbro.Coverage
