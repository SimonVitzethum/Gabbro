module

public import Gabbro.Body
public import Gabbro.Coverage.Teil1

@[expose] public section

namespace Gabbro.Coverage
open Gabbro.Body

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
  simp only [ne_eq, reduceCtorEq, not_false_eq_true]

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
    · exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])
  · intro c fld e hsh hstep
    simp only [step] at hstep
    split at hstep
    · rename_i v he
      cases hstep
      exact ⟨WF_store Γ s.world _ v hwf (hsh v he), rfl⟩
    · exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])
  · intro g e hsh hstep
    simp only [step] at hstep
    split at hstep
    · rename_i v he
      cases hstep
      exact ⟨WF_store Γ s.world _ v hwf (hsh v he), rfl⟩
    · exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

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
  cases v <;> simp only [Value.hasShape, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, Value.int.injEq, exists_eq_left', Bool.false_eq_true, reduceCtorEq, false_and, exists_const]

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
  refine ⟨fun h => by simp only [step, h], fun h => by simp only [step, h], fun h => ?_⟩
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
  exact ⟨fun k h => by simp only [step, h], fun h => by simp only [step, h]⟩

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
    exact ⟨v, he, by simp only [bindLocal, ↓reduceIte], rfl, fun m hm => by simp only [bindLocal, hm, ↓reduceIte]⟩
  · exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

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
  · intro u h; simp only [exec, h]
  · intro hno
    cases hst : step ρ a s with
    | running u => exact absurd hst (hno u)
    | returned u v => simp only [exec, hst]
    | exited u => simp only [exec, hst]
    | left u => simp only [exec, hst]
    | stuck => simp only [exec, hst]

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
  · intro h; simp only [iterate, h]
  · intro h; simp only [iterate, h]

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
          | none => simp only [Option.isSome_none]
          | some n => rw [hc2] at hcp; simp only [Shape.payloadOk, Bool.false_eq_true] at hcp
        | some p => cases q with
          | none => rw [hc2] at hcp; cases p <;> simp only [Shape.payloadOk, Bool.false_eq_true] at hcp
          | some n => simp only [Option.isSome_some]
      rw [hq]
      exact hpay a ha c hc (by rw [hat, hct])
  · intro ρ arms g s t q hg hfit
    simp only [step, hg]
    obtain ⟨⟨a, ha, hat⟩, hpay⟩ := hfit
    clear hg
    induction arms with
    | nil => exact absurd ha (by simp only [List.not_mem_nil, not_false_eq_true])
    | cons b rest ih =>
      obtain ⟨bn, bd, bb⟩ := b
      simp only [pickTag]
      by_cases hb : bn = t
      · subst hb
        have hfit := hpay (bn, bd, bb) (by simp only [List.mem_cons, true_or]) rfl
        simp only
        cases bd with
        | none => exact ⟨bb, s, rfl⟩
        | some vn =>
          simp only [Option.isSome] at hfit
          cases q with
          | none => simp only [Bool.true_eq_false] at hfit
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
  exact store_elsewhere σ _ _ v (by simp only [ne_eq, Place.slot.injEq, h.symm, and_true, and_false, not_false_eq_true])

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

end Gabbro.Coverage
