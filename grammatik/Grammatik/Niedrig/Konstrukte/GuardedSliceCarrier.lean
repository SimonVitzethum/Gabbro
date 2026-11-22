module

public import Grammatik.Niedrig.Konstrukte.SliceCarrier
public import Grammatik.Niedrig.Konstrukte.SliceCheck
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ out : List (Res D)}
  {firstLo firstHi lastLo lastHi : Int} {capacity : Nat} {backing : Ty}

/-- The descriptor's fields have the static capacity bound. The
    enclosing guard proves that both bounded projections take their
    exact-value branch. -/
def guardedCarrierExpr (identity : Nat) (source : Var Γ backing)
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi)) :
    Expr D Γ Λ (sliceCarrierType identity capacity backing) :=
  let zero : Expr D Γ Λ (.int 0 capacity) :=
    .widen (Int.le_refl 0) (Int.natCast_nonneg _) (.lit 0)
  sliceCarrierExpr identity (.eng (.var first) 0 capacity zero)
    (.eng (.sub (.var last) (.var first)) 0 capacity zero) (.var source)

theorem guardedCarrierExpr_reads (identity : Nat) (source : Var Γ backing)
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi)) :
    (guardedCarrierExpr (D := D) (Λ := Λ) (capacity := capacity) identity source first last).orte = [] := rfl

private theorem eval_eng_exact {lo hi : Int} (source : Expr D Γ Λ (.int lo hi))
    (fallback : Expr D Γ Λ (.int 0 capacity)) (entry world : World D) (env : Env D Γ)
    (valid : 0 ≤ (eval entry source world env).n ∧ (eval entry source world env).n ≤ (capacity : Int)) :
    eval entry (.eng source 0 capacity fallback) world env = ⟨(eval entry source world env).n, valid.1, valid.2⟩ := by
  rw [eval]
  exact dite_eq_left valid

theorem guardedCarrierExpr_exact (identity : Nat) (source : Var Γ backing)
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (entry world : World D) (env : Env D Γ)
    {view : ArraySliceView capacity} (checked : ArraySliceView.check capacity (env.get first).n (env.get last).n = some view) :
    eval entry (guardedCarrierExpr (Λ := Λ) identity source first last) world env =
      packSliceCarrier identity view (env.get source) := by
  obtain ⟨_, valid, _, offset, length⟩ := ArraySliceView.check_result checked
  have inside := valid.2.2
  have ordered := valid.2.1
  have firstFits : 0 ≤ (env.get first).n ∧ (env.get first).n ≤ (capacity : Int) := ⟨valid.1, by omega⟩
  have lengthFits : 0 ≤ (env.get last).n - (env.get first).n ∧
      (env.get last).n - (env.get first).n ≤ (capacity : Int) := ⟨by omega, by omega⟩
  have startChecked (fallback : Expr D Γ Λ (.int 0 capacity)) :
      eval entry (.eng (.var first) 0 capacity fallback) world env =
        ⟨(env.get first).n, firstFits.1, firstFits.2⟩ :=
    eval_eng_exact (.var first) fallback entry world env firstFits
  have lengthChecked (fallback : Expr D Γ Λ (.int 0 capacity)) :
      eval entry (.eng (.sub (.var last) (.var first)) 0 capacity fallback) world env =
        ⟨(env.get last).n - (env.get first).n, lengthFits.1, lengthFits.2⟩ :=
    eval_eng_exact (.sub (.var last) (.var first)) fallback entry world env lengthFits
  rw [guardedCarrierExpr, sliceCarrierExpr_eval]
  rw [startChecked, lengthChecked]
  exact Prod.ext (zahl_ext offset.symm) (Prod.ext (zahl_ext length.symm) rfl)

/-- Both endpoint checks run before the ordinary binding of a slice
    descriptor. Invalid signed endpoints take the supplied refusal. -/
def withGuardedSlice (identity : Nat) (source : Var Γ backing) (length : Expr D Γ Λ (.int 0 capacity))
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (refused : Endblock D V l Γ Λ)
    (accepted : Block D V l (sliceCarrierType identity capacity backing :: Γ) Λ out) :
    Block D V l Γ Λ out :=
  guardSlice length first last refused (.bind (guardedCarrierExpr identity source first last) accepted)

theorem withGuardedSlice_exec (identity : Nat) (source : Var Γ backing) (length : Expr D Γ Λ (.int 0 capacity))
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (refused : Endblock D V l Γ Λ)
    (accepted : Block D V l (sliceCarrierType identity capacity backing :: Γ) Λ out)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) :
    let observed := world.lese Λ length.orte
    let available := (eval observed length observed env).n.toNat
    let outcome := execBlock oracle passes calls
      (withGuardedSlice identity source length first last refused accepted) world env
    (SignedSliceOk available (env.get first).n (env.get last).n →
      ∃ view, ArraySliceView.check capacity (env.get first).n (env.get last).n = some view ∧
        view.offset + view.length ≤ available ∧
        outcome = (execBlock oracle passes calls accepted observed
          (.cons (packSliceCarrier identity view (env.get source)) env)).schrumpf) ∧
    (¬ SignedSliceOk available (env.get first).n (env.get last).n →
      outcome = (execEnd oracle passes calls refused observed env).zuAusgang) := by
  intro observed available outcome
  have run := guardSlice_exec length first last refused
    (.bind (guardedCarrierExpr identity source first last) accepted) oracle passes calls world env
  change outcome = _ at run
  refine ⟨?_, fun refused => run.trans (ite_eq_right refused)⟩
  intro valid
  have typed := (eval observed length observed env).le_hi
  have capacityBound : available ≤ capacity := by change (eval observed length observed env).n.toNat ≤ _; omega
  have inCapacity : SignedSliceOk capacity (env.get first).n (env.get last).n :=
    ⟨valid.1, valid.2.1, Int.le_trans valid.2.2 (Int.ofNat_le.mpr capacityBound)⟩
  have decision := (ArraySliceView.check_exact capacity (env.get first).n (env.get last).n).mpr inCapacity
  cases checked : ArraySliceView.check capacity (env.get first).n (env.get last).n with
  | none => simp only [checked, Option.isSome_none, Bool.false_eq_true] at decision
  | some view =>
    obtain ⟨_, _, _, offset, exactLength⟩ := ArraySliceView.check_result checked
    refine ⟨view, rfl, ?_, ?_⟩
    · have high := valid.2.2
      omega
    · rw [run, ite_eq_left valid, execBlock, guardedCarrierExpr_reads]
      change (execBlock oracle passes calls accepted observed
        (.cons (eval observed (guardedCarrierExpr identity source first last) observed env) env)).schrumpf = _
      rw [guardedCarrierExpr_exact identity source first last observed observed env checked]

/-- Runtime text slicing checks the actual byte length. The success
    continuation receives a carrier whose ordinary decoder returns
    exactly the substring selected by the model. The refusal takes
    the original environment and never evaluates that continuation. -/
theorem withGuardedTextSlice_exec (identity : Nat) (source : Var Γ (.str capacity))
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (refused : Endblock D V l Γ Λ)
    (accepted : Block D V l (sliceCarrierType identity capacity (.str capacity) :: Γ) Λ out)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) :
    let selected := checkStringSlice (env.get source) (env.get first).n (env.get last).n
    let outcome := execBlock oracle passes calls
      (withGuardedSlice identity source (.strLen (.var source)) first last refused accepted) world env
    (∀ text, selected = some text → ∃ stored,
      decodeStringCarrier (D := D) (identity := identity) (capacity := capacity) stored = some text ∧
      outcome = (execBlock oracle passes calls accepted world (.cons stored env)).schrumpf) ∧
    (selected = none → outcome = (execEnd oracle passes calls refused world env).zuAusgang) := by
  intro selected outcome
  let length : Expr D Γ Λ (.int 0 capacity) := .strLen (.var source)
  obtain ⟨run, refuse⟩ :=
    withGuardedSlice_exec identity source length first last refused accepted oracle passes calls world env
  have quiet : world.lese Λ length.orte = world := rfl
  rw [quiet] at run refuse
  have available : (eval world length world env).n.toNat = (env.get source).1.length := rfl
  rw [available] at run refuse
  refine ⟨?_, ?_⟩
  · intro text chosen
    by_cases valid : SignedSliceOk (env.get source).1.length (env.get first).n (env.get last).n
    · obtain ⟨view, checked, present, executed⟩ := run valid
      let stored := packSliceCarrier identity view (env.get source)
      refine ⟨stored, ?_, executed⟩
      have decoded := decodeStringCarrier_pack identity view (env.get source) present
      obtain ⟨_, _, _, exactOffset, exactLength⟩ := ArraySliceView.check_result checked
      have start : view.offset = (env.get first).n.toNat := by omega
      have lastByte : view.offset + view.length = (env.get last).n.toNat := by
        have low := valid.1
        have order := valid.2.1
        omega
      rw [← chosen]
      change decodeStringCarrier (D := D) (identity := identity) stored =
        checkStringSlice (env.get source) (env.get first).n (env.get last).n
      rw [decoded, checkStringSlice, dite_eq_left valid]
      apply congrArg some
      apply Subtype.ext
      simp only [strBoundedSliceValue, strSliceValue, start, lastByte]
    · simp only [selected, checkStringSlice, dite_eq_right valid] at chosen
      cases chosen
  · intro rejected
    apply refuse
    intro valid
    simp only [selected, checkStringSlice, dite_eq_left valid] at rejected
    cases rejected

end Gabbro.Grammatik.LowLevel.Construct
