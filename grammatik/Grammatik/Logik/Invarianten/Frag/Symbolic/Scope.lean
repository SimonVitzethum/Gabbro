module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Environment
public import Grammatik.Logik.Invarianten.VC.Control

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic

open Elim Elim.Korrekt VC

/-- Immutable observations of an input environment precede the next fresh key.
    Bound keys of the generated formula need not satisfy this restriction. -/
def SymValue.Bounded (next : Nat) : SymValue D Nat τ → Prop
  | .known _ => True
  | .integer term => ∀ key ∈ termKeys term, key < next

def SymEnv.Bounded (next : Nat) : SymEnv D Nat Γ → Prop
  | .nil => True
  | .cons value rest => value.Bounded next ∧ rest.Bounded next

theorem SymValue.realizes_congr (symbol : SymValue D Nat τ) (next : Nat)
    (bounded : symbol.Bounded next) (valuation other : Assignment Nat)
    (agree : ∀ key, key < next → valuation key = other key)
    (world after : World D) (actual : Wert D τ) :
    symbol.Realizes valuation world actual ↔ symbol.Realizes other after actual := by
  cases symbol with
  | known value => rfl
  | integer term =>
      change term.denote valuation = actual.n ↔ term.denote other = actual.n
      have same := termKeys_congr term valuation other (fun key member => agree key (bounded key member))
      rw [same]

theorem SymEnv.realizes_congr (symbols : SymEnv D Nat Γ) (next : Nat)
    (bounded : symbols.Bounded next) (valuation other : Assignment Nat)
    (agree : ∀ key, key < next → valuation key = other key)
    (world after : World D) (actual : Env D Γ) :
    symbols.Realizes valuation world actual ↔ symbols.Realizes other after actual := by
  induction symbols with
  | nil => cases actual; rfl
  | cons value rest ih =>
      cases actual
      exact and_congr (value.realizes_congr next bounded.1 valuation other agree world after _)
        (ih bounded.2 _)

theorem SymValue.bounded_mono (symbol : SymValue D Nat τ) {next more : Nat}
    (bounded : symbol.Bounded next) (larger : next ≤ more) : symbol.Bounded more := by
  cases symbol with
  | known value => trivial
  | integer term => exact fun key member => Nat.lt_of_lt_of_le (bounded key member) larger

theorem SymEnv.bounded_mono (symbols : SymEnv D Nat Γ) {next more : Nat}
    (bounded : symbols.Bounded next) (larger : next ≤ more) : symbols.Bounded more := by
  induction symbols with
  | nil => trivial
  | cons value rest ih => exact ⟨value.bounded_mono bounded.1 larger, ih bounded.2⟩

/-- The frozen entry data may depend on existing immutable keys only. The
    condition's meaning quantifies those data; they are never executable input. -/
structure Context (A : Type) (next : Nat) where
  holds : Assignment Nat → A → Prop
  stable : ∀ valuation other item,
    (∀ key, key < next → valuation key = other key) →
    (holds valuation item ↔ holds other item)

def Context.weaken (context : Context A next) (larger : next ≤ more) : Context A more where
  holds := context.holds
  stable := fun valuation other item agree => context.stable valuation other item
    (fun key inside => agree key (Nat.lt_of_lt_of_le inside larger))

def Context.empty : Context Unit 0 where
  holds := fun _ _ => True
  stable := fun _ _ _ _ => Iff.rfl

/-- The formula remains quantified syntax until the arithmetic decision gate.
    Soundness covers every valuation, actual runtime and frozen entry datum. -/
structure Certificate {program : Programm D} {checked : D.Fn → List D.Inv} {S : SperrInv D}
    (context : Context A next) (target : A → Runtime program checked S → World D → Prop) where
  formula : LProp (Key D Nat)
  sound : ∀ valuation item, context.holds valuation item → ∀ runtime world,
    formula.denote (values valuation world) → target item runtime world

def Certificate.map {program : Programm D} {checked : D.Fn → List D.Inv} {S : SperrInv D}
    {context : Context A next} {target other : A → Runtime program checked S → World D → Prop}
    (pre : Certificate context target)
    (implies : ∀ item runtime world, target item runtime world → other item runtime world) :
    Certificate context other where
  formula := pre.formula
  sound := fun valuation item present runtime world valid =>
    implies item runtime world (pre.sound valuation item present runtime world valid)

end Gabbro.Grammatik.Invarianten.Frag.Symbolic
