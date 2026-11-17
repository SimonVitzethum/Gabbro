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
  | .product components => ∀ {kind} (field : FieldAt _ kind), (components field).Bounded next

def SymEnv.Bounded (next : Nat) : SymEnv D Nat Γ → Prop
  | .nil => True
  | .cons value rest => value.Bounded next ∧ rest.Bounded next

theorem SymEnv.bounded_get (symbols : SymEnv D Nat Γ) (next : Nat)
    (bounded : symbols.Bounded next) (name : Var Γ τ) : (symbols.get name).Bounded next := by
  induction name with
  | here => cases symbols; exact bounded.1
  | there name ih => cases symbols; exact ih _ bounded.2

theorem SymEnv.bounded_set (symbols : SymEnv D Nat Γ) (next : Nat) (bounded : symbols.Bounded next)
    (name : Var Γ τ) (value : SymValue D Nat τ) (selected : value.Bounded next) :
    (symbols.set name value).Bounded next := by
  induction name with
  | here => cases symbols; exact ⟨selected, bounded.2⟩
  | there name ih => cases symbols; exact ⟨bounded.1, ih _ bounded.2 _ selected⟩

theorem values_bind (valuation : Assignment Nat) (world : World D) (key : Nat) (value : Int) :
    values (valuation.bind key value) world = (values valuation world).bind (.inr key) value := by
  funext name
  cases name <;> simp only [values, Assignment.bind, Sum.inr.injEq, reduceCtorEq, ↓reduceIte]

theorem values_read (valuation : Assignment Nat) (world : World D)
    (resources : List (Res D)) (carriers : List (D.Tab ⊕ D.Glob)) :
    values valuation (world.lese resources carriers) = values valuation world := by
  funext key
  cases key with
  | inl key => exact congrFun (assignment_lese world resources carriers) key
  | inr key => rfl

theorem SymValue.realizes_congr (symbol : SymValue D Nat τ) (next : Nat)
    (bounded : symbol.Bounded next) (valuation other : Assignment Nat)
    (agree : ∀ key, key < next → valuation key = other key)
    (world after : World D) (actual : Wert D τ) :
    symbol.Realizes valuation world actual ↔ symbol.Realizes other after actual := by
  induction symbol with
  | known value => rfl
  | integer term =>
      change term.denote valuation = actual.n ↔ term.denote other = actual.n
      have same := termKeys_congr term valuation other (fun key member => agree key (bounded key member))
      rw [same]
  | product components ih =>
      constructor <;> intro ready kind field
      · exact (ih field (bounded field) _).mp (ready field)
      · exact (ih field (bounded field) _).mpr (ready field)

theorem SymValue.bounded_field (symbol : SymValue D Nat (.prod name fields))
    (next : Nat) (bounded : symbol.Bounded next) (position : FieldAt fields kind) :
    (symbol.field position).Bounded next := by
  cases symbol with
  | known value => trivial
  | product components => exact bounded position

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
  induction symbol with
  | known value => trivial
  | integer term => exact fun key member => Nat.lt_of_lt_of_le (bounded key member) larger
  | product components ih => exact fun field => ih field (bounded field)

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

abbrev Context.weaken (context : Context A next) (larger : next ≤ more) : Context A more where
  holds := context.holds
  stable := fun valuation other item agree => context.stable valuation other item
    (fun key inside => agree key (Nat.lt_of_lt_of_le inside larger))

def Context.empty : Context Unit 0 where
  holds := fun _ _ => True
  stable := fun _ _ _ _ => Iff.rfl

/-- The formula remains quantified syntax until the arithmetic decision gate.
    Soundness covers every valuation, actual runtime and frozen entry datum. -/
structure Certificate {program : Programm D} {checked : D.Fn → List D.Inv} {S : SperrInv D}
    (context : Context A next)
    (target : Assignment Nat → A → Runtime program checked S → World D → Prop) where
  formula : LProp (Key D Nat)
  sound : ∀ valuation item, context.holds valuation item → ∀ runtime world,
    formula.denote (values valuation world) → target valuation item runtime world

def Certificate.map {program : Programm D} {checked : D.Fn → List D.Inv} {S : SperrInv D}
    {context : Context A next}
    {target other : Assignment Nat → A → Runtime program checked S → World D → Prop}
    (pre : Certificate context target)
    (implies : ∀ valuation item runtime world,
      target valuation item runtime world → other valuation item runtime world) :
    Certificate context other where
  formula := pre.formula
  sound := fun valuation item present runtime world valid =>
    implies valuation item runtime world (pre.sound valuation item present runtime world valid)

def Certificate.weaken {program : Programm D} {checked : D.Fn → List D.Inv} {S : SperrInv D}
    {context : Context A next}
    {target : Assignment Nat → A → Runtime program checked S → World D → Prop}
    (pre : Certificate context target) (larger : next ≤ more) : Certificate (context.weaken larger) target where
  formula := pre.formula
  sound := pre.sound

def Certificate.read {program : Programm D} {checked : D.Fn → List D.Inv} {S : SperrInv D}
    {context : Context A next}
    {target : Assignment Nat → A → Runtime program checked S → World D → Prop}
    (pre : Certificate context target) (resources : List (Res D)) (carriers : List (D.Tab ⊕ D.Glob)) :
    Certificate context (fun valuation item runtime world =>
      target valuation item runtime (world.lese resources carriers)) where
  formula := pre.formula
  sound := fun valuation item present runtime world valid => pre.sound valuation item present runtime _ (by
    rw [values_read]
    exact valid)

/-- Conjunction is reserved for genuinely finite choices, such as Boolean
    values and reason constructors. Unknown integer ranges use binders. -/
def allCertificates {program : Programm D} {checked : D.Fn → List D.Inv} {S : SperrInv D}
    (context : Context A next) (items : List I)
    (target : I → Assignment Nat → A → Runtime program checked S → World D → Prop)
    (compile : ∀ candidate, Except Refusal (Certificate context (target candidate))) :
    Except Refusal (Certificate context (fun valuation entry runtime world =>
      ∀ candidate ∈ items, target candidate valuation entry runtime world)) :=
  match items with
  | [] => .ok {
      formula := .tru
      sound := fun _ _ _ _ _ _ _ impossible => False.elim (List.not_mem_nil impossible) }
  | candidate :: rest => do
      let head ← compile candidate
      let tail ← allCertificates context rest target compile
      return {
        formula := .and head.formula tail.formula
        sound := fun valuation entry present runtime world valid value member => by
          rcases List.mem_cons.mp member with same | inside
          · subst value
            exact head.sound valuation entry present runtime world valid.1
          · exact tail.sound valuation entry present runtime world valid.2 value inside }

end Gabbro.Grammatik.Invarianten.Frag.Symbolic
