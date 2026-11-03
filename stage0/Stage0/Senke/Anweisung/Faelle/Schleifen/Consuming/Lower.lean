/- Source operand lowering for the consuming loop candidate. The statement
   admission gate remains closed until the concrete loop simulation is proved. -/
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
    The enclosing function must reserve that pair before relocating parameters
    and locals. The body producer receives all three protected words and its
    actual leave/next targets. -/
def lower {Γ : Ctx} {Λ : List (Res D)} (L : Lay D) (layout : FrameLayout)
    (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (invariant : Expr D Γ Λ .bool) (bound : Int)
    (measure : Expr D Γ Λ (.int 0 bound))
    (reserved remaining : Nat) (protected : List Nat)
    (body : List Nat → Int × Int → Option (List II × Nat)) :
    Option (List II × Nat) := do
  let pair := counterPair reserved remaining
  let s := frei Γ reserved
  if layout.internalResult ≤ pair.1 ∧ pair.2 < FB + reserved ∧
      pair.1 ∉ protected ∧ pair.2 ∉ protected then
    let invCode ← lowE (reserved := reserved) L invariant (s + 4)
    let memberCode ← lowE (reserved := reserved) L member (s + 4)
    let edgeCode ← lowE (reserved := reserved) L edge (s + 4)
    let measureCode ← lowE (reserved := reserved) L measure (s + 4)
    emit s pair.1 pair.2 ((D.count t).toNat + bound.toNat + 1)
      (logikCode (D := D) .schleife) (D.count t) bound
      invCode memberCode edgeCode measureCode
      (body (s :: pair.1 :: pair.2 :: protected))
  else none

/-- The adapter cannot silently borrow a local or a caller's protected word
    when the required reserved pair has not been allocated. -/
theorem lower_refuses_pair {Γ : Ctx} {Λ : List (Res D)}
    (L : Lay D) (layout : FrameLayout) (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (invariant : Expr D Γ Λ .bool) (bound : Int)
    (measure : Expr D Γ Λ (.int 0 bound)) (reserved remaining : Nat)
    (protected : List Nat)
    (body : List Nat → Int × Int → Option (List II × Nat))
    (h : ¬ (layout.internalResult ≤ (counterPair reserved remaining).1 ∧
      (counterPair reserved remaining).2 < FB + reserved ∧
      (counterPair reserved remaining).1 ∉ protected ∧
      (counterPair reserved remaining).2 ∉ protected)) :
    lower L layout t member edge invariant bound measure reserved remaining protected body = none := by
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
