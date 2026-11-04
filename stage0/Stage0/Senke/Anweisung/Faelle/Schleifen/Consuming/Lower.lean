/- Source operand lowering and checked frame placement for consuming traversal. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Allocation
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Code
@[expose] public section

namespace Gabbro.Stage0.Senke.Consuming
open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

/-- Lower every current-world operand at the same scratch origin. This uses
    ordinary lowE, including its checked loads and refusal behavior. Selection
    never mutates the represented world; the source body alone consumes cells.

    `remaining` is the body's simultaneous counter demand. The consuming loop
    needs one additional pair, holding fuel and the saved pre-body measure.
    counterDepthS includes that pair in the source-derived frame demand.
    The enclosing function must reserve that pair before relocating parameters
    and locals. The selected candidate uses the canonical binder slot frei Γ reserved;
    the predecessor, live flag and backup occupy the next three words. They
    are dead at body entry and may be reused by the body. The body producer
    receives the three persistent protected words and its
    actual leave/next targets. -/
def lower {Γ : Ctx} {Λ : List (Res D)} (L : Lay D) (layout : FrameLayout)
    (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (invariant : Expr D Γ Λ .bool) (bound : Int)
    (measure : Expr D Γ Λ (.int 0 bound))
    (reserved remaining : Nat) (kept : List Nat)
    (body : List Nat → Int × Int → Option (List II × Nat)) :
    Option (List II × Nat) := do
  let pair := counterPair reserved remaining
  let s := frei Γ reserved
  if layout.internalResult ≤ pair.1 ∧ pair.2 < FB + reserved ∧
      pair.1 ∉ kept ∧ pair.2 ∉ kept then
    let invCode ← lowE (reserved := reserved) L invariant (s + 4)
    let memberCode ← lowE (reserved := reserved) L member (s + 4)
    let edgeCode ← lowE (reserved := reserved) L edge (s + 4)
    let measureCode ← lowE (reserved := reserved) L measure (s + 4)
    emit s pair.1 pair.2 ((D.count t).toNat + bound.toNat + 1)
      (logikCode (D := D) .schleife) (D.count t) bound
      invCode memberCode edgeCode measureCode
      (body (s :: pair.1 :: pair.2 :: kept))
  else none

/-- Successful operand lowering exposes the actual four lowE results. The
    same reserved parameter is used by expressions, binders and the body. -/
theorem lower_actual {Γ : Ctx} {Λ : List (Res D)}
    {L : Lay D} {layout : FrameLayout} {t : D.Tab}
    {member : Expr D (.index (D.count t) :: Γ) Λ .bool}
    {edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool}
    {invariant : Expr D Γ Λ .bool} {bound : Int}
    {measure : Expr D Γ Λ (.int 0 bound)} {reserved remaining : Nat}
    {kept : List Nat}
    {body : List Nat → Int × Int → Option (List II × Nat)}
    {code : List II} {top : Nat}
    (h : lower L layout t member edge invariant bound measure
      reserved remaining kept body = some (code, top)) :
    let pair := counterPair reserved remaining
    let s := frei Γ reserved
    layout.internalResult ≤ pair.1 ∧ pair.2 < FB + reserved ∧
      pair.1 ∉ kept ∧ pair.2 ∉ kept ∧
    ∃ invCode memberCode edgeCode measureCode : List II × Nat,
      lowE (reserved := reserved) L invariant (s + 4) = some invCode ∧
      lowE (reserved := reserved) L member (s + 4) = some memberCode ∧
      lowE (reserved := reserved) L edge (s + 4) = some edgeCode ∧
      lowE (reserved := reserved) L measure (s + 4) = some measureCode ∧
      emit s pair.1 pair.2 ((D.count t).toNat + bound.toNat + 1)
        (logikCode (D := D) .schleife) (D.count t) bound
        invCode memberCode edgeCode measureCode
        (body (s :: pair.1 :: pair.2 :: kept)) = some (code, top) := by
  unfold lower at h
  dsimp only at h
  dsimp only
  split at h
  · next allocated =>
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨invCode, hi, memberCode, hm, edgeCode, he, measureCode, hmass, emitted⟩ := h
    exact ⟨allocated.1, allocated.2.1, allocated.2.2.1, allocated.2.2.2,
      invCode, memberCode, edgeCode, measureCode, hi, hm, he, hmass, emitted⟩
  · cases h

/-- The adapter cannot silently borrow a local or a caller's protected word
    when the required reserved pair has not been allocated. -/
theorem lower_refuses_pair {Γ : Ctx} {Λ : List (Res D)}
    (L : Lay D) (layout : FrameLayout) (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (invariant : Expr D Γ Λ .bool) (bound : Int)
    (measure : Expr D Γ Λ (.int 0 bound)) (reserved remaining : Nat)
    (kept : List Nat)
    (body : List Nat → Int × Int → Option (List II × Nat))
    (h : ¬ (layout.internalResult ≤ (counterPair reserved remaining).1 ∧
      (counterPair reserved remaining).2 < FB + reserved ∧
      (counterPair reserved remaining).1 ∉ kept ∧
      (counterPair reserved remaining).2 ∉ kept)) :
    lower L layout t member edge invariant bound measure reserved remaining kept body = none := by
  simp only [lower, h, ↓reduceIte]

/-- The selected and predecessor binders are distinct frame words whenever
    Stage 0 admits the represented index as one word. -/
theorem binder_positions (Γ : Ctx) (count : Int) (reserved : Nat)
    (h : valueWords (.index count) = 1) :
    frei (.index count :: Γ) reserved = frei Γ reserved + 1 ∧
    frei (.index count :: .index count :: Γ) reserved = frei Γ reserved + 2 := by
  simp only [frei, contextWords_cons, h]
  omega

/-- A pair assigned to a child is strictly above the parent's saved measure.
    This is the same reservation discipline used by `forever`. -/
theorem saved_measure_before_child (abi depth parent child : Nat)
    (hp : parent < depth) (hc : child < parent) :
    (counterPair (abi + 2 * depth) parent).2 <
      (counterPair (abi + 2 * depth) child).1 :=
  counterPair_nested abi depth parent child hp hc

/-- Saving the pre-body measure never overwrites the remaining fuel. -/
theorem control_pair_distinct (reserved remaining : Nat) :
    (counterPair reserved remaining).1 ≠ (counterPair reserved remaining).2 := by
  simp only [counterPair]
  omega

/-- Every selector operand starts beyond both live index words, the domain
    flag and the candidate backup used by the predecessor membership test. -/
theorem scratch_above_binders (Γ : Ctx) (count : Int) (reserved : Nat)
    (h : valueWords (.index count) = 1) :
    frei (.index count :: .index count :: Γ) reserved + 2 =
      frei Γ reserved + 4 := by
  have positions := binder_positions Γ count reserved h
  omega

/-- Copying a predecessor into the membership binder preserves its own
    binder, the current-domain flag and the candidate backup. Restoring the
    candidate subsequently does not overwrite the membership result. -/
theorem selector_slots_disjoint (s : Nat) :
    s ≠ s + 1 ∧ s ≠ s + 2 ∧ s ≠ s + 3 ∧
    s + 1 ≠ s + 2 ∧ s + 1 ≠ s + 3 ∧
    s + 2 ≠ s + 3 ∧ s + 3 < s + 4 := by
  omega

end Gabbro.Stage0.Senke.Consuming
