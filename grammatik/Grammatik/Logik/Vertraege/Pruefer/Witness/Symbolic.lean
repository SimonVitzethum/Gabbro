module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Selection
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Parameters
public import Grammatik.Logik.Vertraege.Pruefer.Witness.Control

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.SymbolicWitness

open Invarianten Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.Frag.Symbolic
open Pruefer.Symbolic

abbrev declaration := Witness.u32Declaration
abbrev program := Witness.u32Program
abbrev u32 : Ty := .int 0 (2 ^ 32 - 1)
abbrev sumType : Ty := .int 0 (2 ^ 32 - 1 + 10)

def world : World declaration where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun _ => ⟨0, by decide, by decide⟩
  spur := []

def seven : Wert declaration u32 := ⟨7, by decide, by decide⟩
def actual : Env declaration [u32] := .cons seven .nil
def symbols : SymEnv declaration Nat [u32] := .cons (.integer (.var 0)) .nil
def valuation : Frag.Assignment Nat := fun _ => 7

theorem bounded_zeuge : symbols.Bounded 1 :=
  ⟨fun key member => by have same := List.mem_singleton.mp member; subst key; decide, trivial⟩

theorem realizes_zeuge : symbols.Realizes valuation world actual := ⟨rfl, trivial⟩

def context : Context Unit 1 := Context.empty.weaken (by decide)

def initializer : Expr declaration [u32] [] sumType :=
  let argument : Expr declaration [u32] [] u32 := .var .here
  let memory : Expr declaration [u32] [] (.int 0 10) :=
    .glob false (fun _ member => (List.not_mem_nil member).elim)
  .add argument memory

def target (actual : Env declaration [u32]) (value : Wert declaration sumType)
    (_ : Unit) (_ : VC.Runtime program (fun _ => []) (SperrInv.leer declaration)) (world : World declaration) : Prop :=
  value.n = (actual.get .here).n + (world.globs false).n

def compiler : SelectCompiler context symbols sumType target :=
  fun _ _ symbol _ => do
    let encoded ← encodeValue symbol
    return {
      formula := .eq encoded.val (.add (.var (.inr 0)) (.var (.inl (.glob false))))
      sound := fun valuation _ _ _ world valid actual realized value selected => by
        have head : valuation 0 = (actual.get .here).n := by
          cases actual
          exact realized.1
        have number := encoded.property valuation world value selected
        change encoded.val.denote (values valuation world) = value.n at number
        change encoded.val.denote (values valuation world) = valuation 0 + (world.globs false).n at valid
        change value.n = _
        exact number.symm.trans (valid.trans (congrArg (· + (world.globs false).n) head)) }

def selected := Pruefer.Symbolic.selectValue symbols bounded_zeuge initializer target compiler

/-- A full-width parameter and a memory-dependent defining relation exercise
    the scalar continuation. No integer-domain budget is present in this API. -/
theorem selection_present_zeuge : selected.toOption.isSome = true := by rfl

def selection := selected.toOption.get selection_present_zeuge

/-- The real Cooper decision accepts the quantified relation, independently
    of both the u32 range cardinality and the actual memory observation. -/
theorem selection_decides_zeuge :
    decideB (VC.close (VC.lower selection.formula)) (VC.close_closed _) = true := by
  apply (VC.close_decide_true_iff _).mpr
  intro values
  apply (VC.lower_denote _ values).mpr
  change ∀ value : Int,
    ((0 ≤ value ∧ value ≤ 2 ^ 32 - 1 + 10) ∧
      value = values (.inr 0) + values (.inl (.glob false))) →
    value = values (.inr 0) + values (.inl (.glob false))
  exact fun _ guarded => guarded.2

def parameterDomain : Parameters declaration 0 [u32] :=
  (parameters 0 0 [u32]).toOption.get (by rfl)

theorem parameter_u32_no_enumeration_zeuge :
    parameterDomain.next = 1 ∧ parameterDomain.templates.length = 1 := by constructor <;> rfl

theorem parameter_coverage_zeuge (actual : Env declaration [u32]) (incoming : Frag.Assignment Nat) :
    ∃ symbols ∈ parameterDomain.templates, ∃ valuation,
      symbols.Realizes valuation world actual ∧ ∀ key, key < 0 → valuation key = incoming key :=
  parameterDomain.cover world actual incoming

theorem known_environment_zeuge :
    (SymEnv.ofEnv actual : SymEnv declaration Nat [u32]).concrete?.isSome = true := by rfl

theorem world_correspondence_zeuge :
    symbols.Realizes valuation world actual ↔
      symbols.Realizes valuation (world.schreibGlob false [] ⟨9, by decide, by decide⟩) actual :=
  symbols.realizes_world actual valuation _ _

theorem bounded_get_zeuge : (symbols.get .here).Bounded 1 :=
  symbols.bounded_get 1 bounded_zeuge .here

theorem value_bounded_mono_zeuge : (symbols.get .here).Bounded 2 :=
  (symbols.get .here).bounded_mono bounded_get_zeuge (by decide)

theorem environment_bounded_mono_zeuge : symbols.Bounded 2 :=
  symbols.bounded_mono bounded_zeuge (by decide)

theorem value_realizes_congr_zeuge :
    (symbols.get .here).Realizes valuation world seven ↔
      (symbols.get .here).Realizes (valuation.bind 1 9) world seven :=
  (symbols.get .here).realizes_congr 1 bounded_get_zeuge valuation (valuation.bind 1 9)
    (by
      intro key inside
      have same : key = 0 := by omega
      subst key
      rfl) world world seven

theorem environment_realizes_congr_zeuge :
    symbols.Realizes valuation world actual ↔ symbols.Realizes (valuation.bind 1 9) world actual :=
  symbols.realizes_congr 1 bounded_zeuge valuation (valuation.bind 1 9)
    (by
      intro key inside
      have same : key = 0 := by omega
      subst key
      rfl) world world actual

theorem values_bind_zeuge :
    values (valuation.bind 1 9) world = (values valuation world).bind (.inr 1) 9 :=
  values_bind valuation world 1 9

theorem values_read_zeuge : values valuation (world.lese [] [.inr false]) = values valuation world :=
  values_read valuation world [] [.inr false]

end Gabbro.Grammatik.Vertraege.Pruefer.SymbolicWitness
