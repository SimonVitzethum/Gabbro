/-
  File:      stage0/Stage0/Senke/Welt/Rahmen.lean
  Subject:   The frame of a function in `S0IR`: the first slots (`FB`), the variable slots of a context (`vslot`,
             `frei`) and their disjointness. Split out of `Ausdruck.lean` unchanged.
-/
module
public import Grammatik.Kern.Semantik.Semantik
public import Runner.IR.Rahmen
public import Stage0.Senke.Ausdruck.Aggregat.Layout
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR


/-- The position of a variable, counted from the head of the context. -/
def Var.idx : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Nat
  | _, _, .here => 0
  | _, _, .there x => Var.idx x + 1

/-- The first slots of every frame: 0 the return `pc` and 1 the caller's `fp` (both written by `call`), 2 the
    remaining call depth (G's `fuel`; a call with depth 0 stops with `abstieg`),
    and 3 is reserved for an entry snapshot. The variables follow. -/
def FB : Nat := 4

/-- The first free slot of a frame whose variables are `Γ`. -/
def frei (Γ : Ctx) (reserved : Nat := 0) : Nat := FB + reserved + contextWords Γ

@[simp] theorem frei_cons (Γ : Ctx) (τ : Ty) (reserved : Nat) :
    frei (τ :: Γ) reserved = frei Γ reserved + valueWords τ := by
  simp [frei, Nat.add_assoc]

/-- Offset from the variable area's base; extension never moves existing values. -/
def variableOffset : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Nat
  | _ :: Γ, _, .here => contextWords Γ
  | _, _, .there x => variableOffset x

/-- The complete value span fits below the context's first free word. -/
theorem variableOffset_bound {Γ : Ctx} {τ : Ty} (x : Var Γ τ) :
    variableOffset x + valueWords τ ≤ contextWords Γ := by
  induction x with
  | here => exact Nat.le_refl _
  | there x ih => simp only [variableOffset, contextWords_cons]; omega

/-- Distinct variables have disjoint complete spans, including nested shapes. -/
theorem variableOffset_disjoint {Γ : Ctx} {τ τ' : Ty} (x : Var Γ τ) (y : Var Γ τ')
    (hne : Var.idx y ≠ Var.idx x) :
    variableOffset x + valueWords τ ≤ variableOffset y ∨
      variableOffset y + valueWords τ' ≤ variableOffset x := by
  induction x generalizing τ' with
  | here =>
    cases y with
    | here => exact False.elim (hne rfl)
    | there y => exact Or.inr (variableOffset_bound y)
  | there x ih =>
    cases y with
    | here => exact Or.inl (variableOffset_bound x)
    | there y => exact ih y (by intro h; apply hne; simp only [Var.idx, h])

/-- The frame slot of the first word of a variable. -/
def vslot {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (reserved : Nat := 0) : Nat :=
  FB + reserved + variableOffset x

theorem vslot_span_ne {Γ : Ctx} {τ τ' : Ty} (x : Var Γ τ) (y : Var Γ τ')
    (hne : Var.idx y ≠ Var.idx x) {i j : Nat} (hi : i < valueWords τ) (hj : j < valueWords τ') :
    vslot x reserved + i ≠ vslot y reserved + j := by
  have separation := variableOffset_disjoint x y hne
  unfold vslot
  omega

/-- Reserve a prefix after the ABI header consistently for bindings and scratch. -/
theorem frei_reserved (Γ : Ctx) (reserved : Nat) :
    FB + reserved ≤ frei Γ reserved := by simp [frei]

theorem vslot_reserved {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (reserved : Nat) :
    FB + reserved ≤ vslot x reserved := by simp [vslot]

/-- Extending the context allocates exactly its first free unreserved word. -/
theorem vslot_here_reserved (Γ : Ctx) (τ : Ty) (reserved : Nat) :
    vslot (Var.here : Var (τ :: Γ) τ) reserved = frei Γ reserved := by
  simp [vslot, frei, variableOffset]

end Gabbro.Stage0.Senke
