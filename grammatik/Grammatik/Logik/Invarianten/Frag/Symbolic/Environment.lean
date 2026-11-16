module

public import Grammatik.Logik.Invarianten.Frag.Observation
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Rename

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic

open Elim Elim.Korrekt

/-- Memory and immutable observations occupy disjoint namespaces. Extending the
    immutable namespace with `Option` makes the new `none` key fresh by type. -/
abbrev Key (D : Deklaration) (α : Type) := Observation D ⊕ α

def values (valuation : Assignment α) (world : World D) : Assignment (Key D α)
  | .inl key => assignment world key
  | .inr key => valuation key

def extend (valuation : Assignment α) (value : Int) : Assignment (Option α)
  | none => value
  | some key => valuation key

def embed : Key D α → Key D (Option α)
  | .inl key => .inl key
  | .inr key => .inr (some key)

theorem embed_injective : Function.Injective (embed (D := D) (α := α)) := by
  intro left right same
  cases left <;> cases right <;> cases same <;> rfl

theorem embed_fresh (key : Key D α) : embed key ≠ .inr none := by
  cases key <;> intro impossible <;> cases impossible

theorem values_extend (valuation : Assignment α) (world : World D) (value : Int) :
    values (extend valuation value) world ∘ embed = values valuation world := by
  funext key
  cases key <;> rfl

/-- Integers are terms, including unknown parameters and call answers. Known
    values retain exact Boolean/capability and finite non-integer selection. -/
inductive SymValue (D : Deklaration) (α : Type) : Ty → Type where
  | known (value : Wert D τ) : SymValue D α τ
  | integer (term : LTerm α) : SymValue D α (.int lo hi)

def SymValue.Realizes (valuation : Assignment α) (world : World D) :
    SymValue D α τ → Wert D τ → Prop
  | .known expected, actual => expected = actual
  | .integer term, actual => term.denote valuation = actual.n

def SymValue.lift : SymValue D α τ → SymValue D (Option α) τ
  | .known value => .known value
  | .integer term => .integer (renameTerm some term)

theorem SymValue.realizes_lift (symbol : SymValue D α τ) (valuation : Assignment α)
    (world : World D) (fresh : Int) (actual : Wert D τ) :
    symbol.lift.Realizes (extend valuation fresh) world actual ↔
      symbol.Realizes valuation world actual := by
  cases symbol with
  | known value => rfl
  | integer term =>
      simp only [SymValue.lift, SymValue.Realizes, renameTerm_denote]
      rfl

/-- An environment contains expressions, never an enumeration of a scalar
    range. Its relation is deliberately about the actual typed runtime Env. -/
inductive SymEnv (D : Deklaration) (α : Type) : Ctx → Type where
  | nil : SymEnv D α []
  | cons (value : SymValue D α τ) (tail : SymEnv D α Γ) : SymEnv D α (τ :: Γ)

def SymEnv.ofEnv : Env D Γ → SymEnv D α Γ
  | .nil => .nil
  | .cons value tail => .cons (.known value) (ofEnv tail)

def SymEnv.get : SymEnv D α Γ → Var Γ τ → SymValue D α τ
  | .cons value _, .here => value
  | .cons _ tail, .there name => tail.get name

def SymEnv.set : SymEnv D α Γ → Var Γ τ → SymValue D α τ → SymEnv D α Γ
  | .cons _ tail, .here, value => .cons value tail
  | .cons head tail, .there name, value => .cons head (tail.set name value)

def SymEnv.tail : SymEnv D α (τ :: Γ) → SymEnv D α Γ
  | .cons _ tail => tail

def SymEnv.Realizes (valuation : Assignment α) (world : World D) :
    SymEnv D α Γ → Env D Γ → Prop
  | .nil, .nil => True
  | .cons symbol tail, .cons actual rest =>
      symbol.Realizes valuation world actual ∧ tail.Realizes valuation world rest

/-- Immutable locals retain their values when memory or the event trace changes.
    A memory-dependent initializer must first introduce a fresh immutable key. -/
theorem SymEnv.realizes_world (symbols : SymEnv D α Γ) (actual : Env D Γ)
    (valuation : Assignment α) (world after : World D) :
    symbols.Realizes valuation world actual ↔ symbols.Realizes valuation after actual := by
  induction symbols with
  | nil => cases actual; rfl
  | cons value rest ih =>
      cases actual
      cases value <;> exact and_congr Iff.rfl (ih _)

theorem SymEnv.realizes_ofEnv (actual : Env D Γ) (valuation : Assignment α) (world : World D) :
    (SymEnv.ofEnv actual).Realizes valuation world actual := by
  induction actual with
  | nil => trivial
  | cons value tail ih => exact ⟨rfl, ih⟩

theorem SymEnv.realizes_get (symbols : SymEnv D α Γ) (actual : Env D Γ)
    (valuation : Assignment α) (world : World D) (name : Var Γ τ)
    (realized : symbols.Realizes valuation world actual) :
    (symbols.get name).Realizes valuation world (actual.get name) := by
  induction name with
  | here => cases symbols; cases actual; exact realized.1
  | there name ih => cases symbols; cases actual; exact ih _ _ realized.2

theorem SymEnv.realizes_set (symbols : SymEnv D α Γ) (actual : Env D Γ)
    (valuation : Assignment α) (world : World D) (name : Var Γ τ)
    (symbol : SymValue D α τ) (value : Wert D τ)
    (realized : symbols.Realizes valuation world actual)
    (selected : symbol.Realizes valuation world value) :
    (symbols.set name symbol).Realizes valuation world (actual.set name value) := by
  induction name with
  | here => cases symbols; cases actual; exact ⟨selected, realized.2⟩
  | there name ih => cases symbols; cases actual; exact ⟨realized.1, ih _ _ _ _ realized.2 selected⟩

def SymEnv.lift : SymEnv D α Γ → SymEnv D (Option α) Γ
  | .nil => .nil
  | .cons symbol tail => .cons symbol.lift tail.lift

theorem SymEnv.realizes_lift (symbols : SymEnv D α Γ) (actual : Env D Γ)
    (valuation : Assignment α) (world : World D) (fresh : Int) :
    symbols.lift.Realizes (extend valuation fresh) world actual ↔
      symbols.Realizes valuation world actual := by
  induction symbols with
  | nil => cases actual; rfl
  | cons symbol tail ih =>
      cases actual
      exact and_congr (symbol.realizes_lift valuation world fresh _) (ih _)

/-- Coverage uses the actual evaluation/answer, not a chosen inhabitant. Every
    typed integer extends a realizing valuation without changing an old key. -/
theorem SymEnv.extend_integer (symbols : SymEnv D α Γ) (actual : Env D Γ)
    (valuation : Assignment α) (world : World D) (value : Zahl lo hi)
    (realized : symbols.Realizes valuation world actual) :
    (SymEnv.cons (.integer (.var none)) symbols.lift).Realizes
      (extend valuation value.n) world (.cons value actual) :=
  ⟨rfl, (symbols.realizes_lift actual valuation world value.n).mpr realized⟩

/-- Exact finite environments remain a specialization of the symbolic one.
    Recovering one requires a certificate covering every realizing valuation. -/
def SymEnv.concrete? : (symbols : SymEnv D α Γ) → Option
    { actual : Env D Γ // ∀ valuation world runtime,
      symbols.Realizes valuation world runtime → runtime = actual }
  | .nil => some ⟨.nil, fun _ _ runtime _ => by cases runtime; rfl⟩
  | .cons (.integer _) _ => none
  | .cons (.known value) rest => do
      let tail ← rest.concrete?
      return ⟨.cons value tail.val, fun valuation world runtime realized => by
        cases runtime with
        | cons head rest =>
            change value = head ∧ _ at realized
            rw [← realized.1, tail.property valuation world rest realized.2]⟩

end Gabbro.Grammatik.Invarianten.Frag.Symbolic
