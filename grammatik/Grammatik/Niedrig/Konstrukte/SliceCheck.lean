module

public import Grammatik.Niedrig.Konstrukte.Schnitt
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ out : List (Res D)}
  {firstLo firstHi lastLo lastHi : Int} {capacity : Nat}

/-- Compare already evaluated endpoints while they still have their
    signed source type. The bound is the backing value's actual length. -/
def sliceBoundsExpr (length : Expr D Γ Λ (.int 0 capacity))
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi)) :
    Expr D Γ Λ .bool :=
  .and (.le (.lit 0) (.var first)) (.and (.le (.var first) (.var last)) (.le (.var last) length))

theorem sliceBoundsExpr_reads (length : Expr D Γ Λ (.int 0 capacity))
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi)) :
    (sliceBoundsExpr length first last).orte = length.orte := rfl

theorem sliceBoundsExpr_exact (length : Expr D Γ Λ (.int 0 capacity))
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (entry world : World D) (env : Env D Γ) :
    eval entry (sliceBoundsExpr length first last) world env = true ↔
      SignedSliceOk (eval entry length world env).n.toNat (env.get first).n (env.get last).n := by
  change (decide (0 ≤ (env.get first).n) &&
      (decide ((env.get first).n ≤ (env.get last).n) &&
        decide ((env.get last).n ≤ (eval entry length world env).n))) = true ↔ _
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq, SignedSliceOk]
  have nonnegative := (eval entry length world env).lo_le
  constructor <;> rintro ⟨lower, ordered, upper⟩ <;> exact ⟨lower, ordered, by omega⟩

/-- Share the same ordinary branch for an array capacity and the actual
    byte length of a string. Only the accepted arm constructs a view. -/
def guardSlice (length : Expr D Γ Λ (.int 0 capacity))
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (rejected : Endblock D V l Γ Λ) (accepted : Block D V l Γ Λ out) :
    Block D V l Γ Λ out :=
  .check (sliceBoundsExpr length first last) rejected accepted

theorem guardSlice_exec (length : Expr D Γ Λ (.int 0 capacity))
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (rejected : Endblock D V l Γ Λ) (accepted : Block D V l Γ Λ out)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) :
    let read := world.lese Λ length.orte
    execBlock oracle passes calls (guardSlice length first last rejected accepted) world env =
      if SignedSliceOk (eval read length read env).n.toNat (env.get first).n (env.get last).n then
        execBlock oracle passes calls accepted read env
      else (execEnd oracle passes calls rejected read env).zuAusgang := by
  intro read
  rw [guardSlice, execBlock, sliceBoundsExpr_reads]
  have exact := sliceBoundsExpr_exact length first last read read env
  change (if eval read (sliceBoundsExpr length first last) read env = true then _ else _) = _
  by_cases valid : SignedSliceOk (eval read length read env).n.toNat (env.get first).n (env.get last).n
  · rw [if_pos (exact.mpr valid), if_pos valid]
  · rw [if_neg (fun taken => valid (exact.mp taken)), if_neg valid]

/-- The generated guard uses the string's length word. A successful
    guard is equivalent to obtaining a well-typed model substring. -/
theorem stringSliceBounds_exact (source : Var Γ (.str capacity))
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (entry world : World D) (env : Env D Γ) :
    eval entry (sliceBoundsExpr (.strLen (.var source)) first last : Expr D Γ Λ .bool) world env = true ↔
      (checkStringSlice (env.get source) (env.get first).n (env.get last).n).isSome = true := by
  rw [checkStringSlice_exact]
  simpa only [eval, strLenW, Int.toNat_natCast] using
    sliceBoundsExpr_exact (Λ := Λ) (.strLen (.var source)) first last entry world env

/-- Both endpoint slots can hold the zero endpoints for every backing
    string. The accepted guard realizes the model's exact empty value. -/
theorem stringSliceBounds_erfuellbar {maximum : Nat} (source : Wert D (.str maximum)) :
    let first : Var [.int 0 0, .str maximum] (.int 0 0) := .here
    let saved : Var [.int 0 0, .str maximum] (.str maximum) := .there .here
    let env : Env D [.int 0 0, .str maximum] := .cons ⟨0, Int.le_refl 0, Int.le_refl 0⟩ (.cons source .nil)
    (∀ (world : World D), eval world
      (sliceBoundsExpr (Λ := Λ) (.strLen (.var saved)) first first) world env = true) ∧
      ∃ sliced, checkStringSlice source 0 0 = some sliced ∧ sliced.1 = [] := by
  have accepted : SignedSliceOk source.1.length 0 0 := ⟨Int.le_refl 0, Int.le_refl 0, Int.natCast_nonneg _⟩
  have observed := (checkStringSlice_exact source 0 0).mpr accepted
  refine ⟨?_, ?_⟩
  · intro world
    exact (stringSliceBounds_exact (.there .here) .here .here world world _).mpr observed
  · unfold checkStringSlice
    rw [dite_eq_left accepted]
    exact ⟨_, rfl, rfl⟩

end Gabbro.Grammatik.LowLevel.Construct
