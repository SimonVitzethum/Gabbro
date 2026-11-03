/- Source operand lowering for the consuming loop candidate. The statement
   admission gate remains closed until the concrete loop simulation is proved. -/
module
public import Grammatik.Kern.Syntax.Zucker
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Allocation
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Code
@[expose] public section

namespace Gabbro.Stage0.Senke.Consuming
open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

/-- Insert the candidate binder below the predecessor binder. In particular,
    the predecessor remains `here`, while every outer variable moves past
    both indices. A captured outer index is never confused with either one. -/
def predecessorMember {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool) :
    Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool :=
  member.ren (Var.hoch Var.there)

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
    let invCode ← lowE (reserved := reserved) L invariant (s + 3)
    let memberCode ← lowE (reserved := reserved) L member (s + 3)
    let predecessorCode ← lowE (reserved := reserved) L
      (predecessorMember t member) (s + 3)
    let edgeCode ← lowE (reserved := reserved) L edge (s + 3)
    let measureCode ← lowE (reserved := reserved) L measure (s + 3)
    emit s pair.1 pair.2 ((D.count t).toNat + bound.toNat + 1)
      (logikCode (D := D) .schleife) (D.count t) bound
      invCode memberCode predecessorCode edgeCode measureCode
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

/-- Every selector operand starts beyond both live index words. The extra
    word between those binders and scratch holds the nonempty-domain flag. -/
theorem scratch_above_binders (Γ : Ctx) (count : Int) (reserved : Nat)
    (h : valueWords (.index count) = 1) :
    frei (.index count :: .index count :: Γ) reserved + 1 =
      frei Γ reserved + 3 := by
  have positions := binder_positions Γ count reserved h
  omega

end Gabbro.Stage0.Senke.Consuming
