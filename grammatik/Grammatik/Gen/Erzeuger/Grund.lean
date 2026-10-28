/-
  File:      Grammatik/Gen/Erzeuger/Grund.lean
  Subject:   The GENERATOR OF VALID PROGRAMS, the common ground: complete enumerations of what a declaration
             names (`Aufz`), the typed-element filter `ofTy` over lists of dependent pairs, the bounded integers,
             the decision of the model's proof arguments (`darf`, `gdarf`), and the generator of variables with its
             completeness.

  THE FRAME OF THE WHOLE GENERATOR (this folder). The model's terms (`Expr`, `Stmt`, `Block`, `Endblock`,
  `Arms`, `GrundArms`, `Args`, `ErgExpr`, `Programm`) are INTRINSICALLY TYPED: a term carries its typing
  indices, the range of its result, the held-resource list before and after, the proof arguments of every
  rule. A generator over them returns LISTS OF DEPENDENT PAIRS, `(τ, e)` with `e : Expr Γ Λ τ`, and a
  subterm of a required type is picked with `ofTy`. Every generator is by FUEL: `gen (n + 1)` is built from
  `gen n`, and `gen 0 = []`. The size of a term (`Groesse.lean` of each family) counts every node and every
  free number or enumeration index once, so a free number is bounded by the size, and so is the list it is
  drawn from. Completeness is then a single induction on `n` per family: a term of size at most `n + 1` is
  built by one rule from subterms of size at most `n`, which the induction hypothesis puts into `gen n`.
-/
import Grammatik.Kern.Syntax.Syntax

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

set_option warn.classDefReducibility false

/-- **Complete enumerations** of what a declaration names: every table, field, static, lock, mark, function,
    invariant, axiom, register and assumption of `D` is in the list. (The goal statement's `Aufzaehlung`s are
    the same for functions, locks and carriers; here the generator needs every kind.) -/
class Aufz (D : Deklaration) where
  tab : List D.Tab
  tab_mem : ∀ t, t ∈ tab
  feld : ∀ t, List (D.Feld t)
  feld_mem : ∀ t f, f ∈ feld t
  glob : List D.Glob
  glob_mem : ∀ g, g ∈ glob
  lock : List D.Lock
  lock_mem : ∀ l, l ∈ lock
  marke : List D.Marke
  marke_mem : ∀ m, m ∈ marke
  fn : List D.Fn
  fn_mem : ∀ f, f ∈ fn
  inv : List D.Inv
  inv_mem : ∀ i, i ∈ inv
  ax : List D.Ax
  ax_mem : ∀ a, a ∈ ax
  reg : List D.Reg
  reg_mem : ∀ r, r ∈ reg
  annahme : List D.Annahme
  annahme_mem : ∀ a, a ∈ annahme
  /-- The pointer types a function conforms to (`Deklaration.passt`, 2026-10-21): a finite list that
      holds every one. -/
  sigs : List Nat
  sigs_mem : ∀ f n, D.passt f n = true → n ∈ sigs
  /-- decidable equality on functions and the other enumerated types the generator compares -/
  decFn : DecidableEq D.Fn
  decInv : DecidableEq D.Inv
  decAx : DecidableEq D.Ax
  decReg : DecidableEq D.Reg
  decAnnahme : DecidableEq D.Annahme

attribute [instance] Aufz.decFn Aufz.decInv Aufz.decAx Aufz.decReg Aufz.decAnnahme

/-- The integers `-n .. n`. -/
def ints (n : Nat) : List Int := (List.range (2 * n + 1)).map fun k => ((k : Nat) : Int) - (n : Int)

theorem mem_ints {n : Nat} {k : Int} (h : k.natAbs ≤ n) : k ∈ ints n := by
  unfold ints
  rw [List.mem_map]
  refine ⟨(k + n).toNat, List.mem_range.mpr (by omega), ?_⟩
  omega

/-- The elements of a list of dependent pairs at index `a` (the typed-element filter). -/
def ofTy {α : Type} {F : α → Type} [DecidableEq α] (xs : List (Σ a, F a)) (a : α) : List (F a) :=
  xs.filterMap fun p => if h : p.1 = a then some (h ▸ p.2) else none

theorem mem_ofTy {α : Type} {F : α → Type} [DecidableEq α] {xs : List (Σ a, F a)} {a : α} {x : F a}
    (h : (⟨a, x⟩ : Σ a, F a) ∈ xs) : x ∈ ofTy xs a := by
  unfold ofTy
  rw [List.mem_filterMap]
  exact ⟨⟨a, x⟩, h, by simp only [↓reduceDIte]⟩

section Entscheidung

variable {D : Deklaration}

instance (t : D.Tab) (Λ : List (Res D)) : Decidable (darf D t Λ) := by
  unfold darf; infer_instance

instance (g : D.Glob) (Λ : List (Res D)) : Decidable (gdarf D g Λ) := by
  unfold gdarf; infer_instance

end Entscheidung

/-! ## Variables -/

/-- Every variable of a context, with its type (the context is finite). -/
def genVar : (Γ : Ctx) → List (Σ τ, Var Γ τ)
  | [] => []
  | σ :: Γ => ⟨σ, .here⟩ :: (genVar Γ).map fun p => ⟨p.1, .there p.2⟩

/-- Completeness: every variable is generated. -/
theorem genVar_vollst : ∀ (Γ : Ctx) (τ : Ty) (x : Var Γ τ), (⟨τ, x⟩ : Σ τ, Var Γ τ) ∈ genVar Γ := by
  intro Γ τ x
  induction x with
  | here => simp only [genVar, List.mem_cons, List.mem_map, Sigma.mk.injEq, true_or]
  | there x ih => simp only [genVar, List.mem_cons, List.mem_map]; exact Or.inr ⟨⟨_, x⟩, ih, rfl⟩

/-- The size of a variable: its depth in the context, plus the node. -/
def groesseVar : ∀ {Γ : Ctx} {τ : Ty}, Var Γ τ → Nat
  | _, _, .here => 1
  | _, _, .there x => 1 + groesseVar x

end Gabbro.Grammatik.Gen
