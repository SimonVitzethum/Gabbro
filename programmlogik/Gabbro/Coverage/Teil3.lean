module

public import Gabbro.Body
public import Gabbro.Coverage.Teil2

@[expose] public section

namespace Gabbro.Coverage
open Gabbro.Body

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
    | nil => exact absurd ha (by simp only [List.not_mem_nil, not_false_eq_true])
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
    | none => simp only [step, hg]
    | some v =>
      cases v with
      | reason x => exact absurd hg (hno x)
      | int _ => simp only [step, hg]
      | bool _ => simp only [step, hg]
      | absent => simp only [step, hg]
      | present _ => simp only [step, hg]
      | tagged _ _ => simp only [step, hg]

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
    · exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])
  · exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

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
  · exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

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
  exact ⟨by simp only [bindLocal, ↓reduceIte], rfl, fun m hm => by simp only [bindLocal, hm, ↓reduceIte]⟩

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
  simp only [Value.hasShape, store, ↓reduceIte, Bool.false_eq_true] at this

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
      | (rename_i r; cases r <;> simp only [Reason.kind, reduceCtorEq] at h)
      | exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-- **The classifier answers for every form.** Not "for every form I remembered to look
    at" -- `Verdict.unhandled` exists for exactly this proposition to have content. -/
theorem classify_total : ∀ f : Form, classify f ≠ .unhandled := by
  intro f
  cases f
  case refusedOrAssumed r => cases r <;> simp only [classify, Reason.kind, ne_eq, reduceCtorEq, not_false_eq_true]
  all_goals simp only [classify, ne_eq, reduceCtorEq, not_false_eq_true]

/-- **Everything the classifier hands back to the person is a clause the person wrote.**
    `IsOwnLogic` is defined in section 4 without mentioning `classify`, so this is a claim
    about two independent case analyses agreeing -- which is what makes it falsifiable. -/
theorem ownLogic_is_the_persons : ∀ f : Form, classify f = .ownLogic → IsOwnLogic f := by
  intro f h
  cases f
  case refusedOrAssumed r => cases r <;> simp only [classify, Reason.kind, reduceCtorEq] at h
  case ownEnsures => exact ⟨rfl, "ensures", rfl, by simp only [personalClauses, List.mem_cons, String.reduceEq, List.not_mem_nil, or_self, or_false]⟩
  case ownInvariant => exact ⟨rfl, "invariant", rfl, by simp only [personalClauses, List.mem_cons, String.reduceEq, List.not_mem_nil, or_self, or_false, or_true]⟩
  case ownRequires => exact ⟨rfl, "requires", rfl, by simp only [personalClauses, List.mem_cons, String.reduceEq, List.not_mem_nil, or_self, or_false, or_true]⟩
  case ownReaches => exact ⟨rfl, "reaches", rfl, by simp only [personalClauses, List.mem_cons, String.reduceEq, List.not_mem_nil, or_false, or_true]⟩
  all_goals simp only [classify, reduceCtorEq] at h

/-- **And nothing whose statement the language fixes is left in the person's lap.** This is
    the other half of Simon's sentence, and the half a coverage claim usually skips. -/
theorem nothing_of_the_language_is_left_to_the_person :
    ∀ f : Form, origin f = .language → classify f ≠ .ownLogic := by
  intro f h
  cases f
  case refusedOrAssumed r => cases r <;> simp only [classify, Reason.kind, ne_eq, reduceCtorEq, not_false_eq_true]
  case ownEnsures => simp only [origin, reduceCtorEq] at h
  case ownInvariant => simp only [origin, reduceCtorEq] at h
  case ownRequires => simp only [origin, reduceCtorEq] at h
  case ownReaches => simp only [origin, reduceCtorEq] at h
  all_goals simp only [classify, ne_eq, reduceCtorEq, not_false_eq_true]

/-- **A form with no personal clause is not the person's.** -/
theorem no_clause_no_own_logic : ∀ f : Form, personalClause f = none → ¬ IsOwnLogic f := by
  intro f h hown
  obtain ⟨_, c, hc, _⟩ := hown
  rw [h] at hc
  exact absurd hc (by simp only [reduceCtorEq, not_false_eq_true])

/-- **Every refusal carries a tag the emitter actually prints**, and no tag is empty. -/
theorem every_refusal_has_an_emitter_tag :
    ∀ (f : Form) (t : String), classify f = .refused t → ∃ r : Reason, r.tag = t ∧ t ≠ "" := by
  intro f t h
  cases f
  case refusedOrAssumed r =>
    have ht : r.tag = t := by cases r <;> simp_all [classify, Reason.kind, Reason.tag]
    refine ⟨r, ht, ?_⟩
    subst ht
    cases r <;> simp only [Reason.tag, ne_eq, String.reduceEq, not_false_eq_true]
  all_goals simp only [classify, reduceCtorEq] at h

end Gabbro.Coverage
