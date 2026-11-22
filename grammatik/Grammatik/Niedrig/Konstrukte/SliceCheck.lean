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
  change (if wahr? (eval read (sliceBoundsExpr length first last) read env) = true then _ else _) = _
  by_cases valid : SignedSliceOk (eval read length read env).n.toNat (env.get first).n (env.get last).n
  · have inRange : wahr? (eval read (sliceBoundsExpr length first last) read env) = true := exact.mpr valid
    rw [if_pos inRange, if_pos valid]
  · have refuses : wahr? (eval read (sliceBoundsExpr length first last) read env) ≠ true :=
      fun taken => valid (exact.mp taken)
    rw [if_neg refuses, if_neg valid]

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

/-- Check the requested index against the saved runtime length. The
    signed check runs before converting the offset to an address. -/
def sliceIndexBoundsExpr {lo hi : Int} (length : Var Γ (.int 0 capacity)) (index : Var Γ (.int lo hi)) :
    Expr D Γ Λ .bool :=
  .and (.le (.lit 0) (.var index)) (.lt (.var index) (.var length))

theorem sliceIndexBounds_exact {lo hi : Int} (length : Var Γ (.int 0 capacity))
    (index : Var Γ (.int lo hi)) (entry world : World D) (env : Env D Γ) :
    eval entry (sliceIndexBoundsExpr (Λ := Λ) length index) world env = true ↔
      0 ≤ (env.get index).n ∧ (env.get index).n.toNat < (env.get length).n.toNat := by
  change (decide (0 ≤ (env.get index).n) && decide ((env.get index).n < (env.get length).n)) = true ↔ _
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq]
  have validLength := (env.get length).lo_le
  constructor <;> rintro ⟨lower, upper⟩ <;> exact ⟨lower, by omega⟩

/-- The index guard establishes the exact valid index of the runtime
    slice value, for every descriptor whose saved length is correct. -/
theorem sliceIndexBounds_view {lo hi : Int} {view : ArraySliceView capacity}
    (length : Var Γ (.int 0 capacity)) (index : Var Γ (.int lo hi))
    (entry world : World D) (env : Env D Γ)
    (saved : (env.get length).n = (view.length : Int)) :
    eval entry (sliceIndexBoundsExpr (Λ := Λ) length index) world env = true ↔
      0 ≤ (env.get index).n ∧ (env.get index).n.toNat < view.length := by
  rw [sliceIndexBounds_exact, saved, Int.toNat_natCast]

/-- The ordinary conditional runs the selection arm only at an index
    within the saved view. The guard observes no carrier. -/
theorem sliceIndexGuard_exec {lo hi : Int} {view : ArraySliceView capacity}
    (length : Var Γ (.int 0 capacity)) (index : Var Γ (.int lo hi))
    (rejected : Endblock D V l Γ Λ) (accepted : Block D V l Γ Λ out)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (saved : (env.get length).n = (view.length : Int)) :
    execBlock oracle passes calls (.check (sliceIndexBoundsExpr length index) rejected accepted) world env =
      if 0 ≤ (env.get index).n ∧ (env.get index).n.toNat < view.length then
        execBlock oracle passes calls accepted world env
      else (execEnd oracle passes calls rejected world env).zuAusgang := by
  have noReads : (sliceIndexBoundsExpr (D := D) (Λ := Λ) length index).orte = [] := rfl
  rw [execBlock, noReads, show world.lese Λ [] = world from rfl]
  have branch := sliceIndexBounds_view (Λ := Λ) length index world world env saved
  change (if wahr? (eval world (sliceIndexBoundsExpr (Λ := Λ) length index) world env) = true then _ else _) = _
  by_cases inside : 0 ≤ (env.get index).n ∧ (env.get index).n.toNat < view.length
  · rw [if_pos (branch.mpr inside), if_pos inside]
  · rw [if_neg (fun accepted => inside (branch.mp accepted)), if_neg inside]

/-- A slice with a positive length admits its first element and rejects
    its length as an index. Both outcomes follow from the same bound. -/
theorem sliceIndexBounds_erfuellbar {view : ArraySliceView capacity}
    (nonempty : 0 < view.length) (entry world : World D) :
    let size : Var [.int 0 capacity, .int 0 capacity] (.int 0 capacity) := .here
    let position : Var [.int 0 capacity, .int 0 capacity] (.int 0 capacity) := .there .here
    let length : Zahl 0 capacity := ⟨view.length, by omega, by have := view.fits; omega⟩
    let env : Env D [.int 0 capacity, .int 0 capacity] :=
      .cons length (.cons ⟨0, by omega, by omega⟩ .nil)
    eval entry (sliceIndexBoundsExpr (Λ := Λ) size position) world env = true ∧
      eval entry (sliceIndexBoundsExpr (Λ := Λ) size size) world env = false := by
  intro size position length env
  refine ⟨(sliceIndexBounds_view size position entry world env rfl).mpr ⟨Int.le_refl _, nonempty⟩, ?_⟩
  cases outcome : eval entry (sliceIndexBoundsExpr (Λ := Λ) size size) world env with
  | false => rfl
  | true =>
    have inside := ((sliceIndexBounds_view size size entry world env rfl).mp outcome).2
    have cast : (env.get size).n.toNat = view.length := Int.toNat_natCast _
    rw [cast] at inside
    exact (Nat.lt_irrefl _ inside).elim

end Gabbro.Grammatik.LowLevel.Construct
