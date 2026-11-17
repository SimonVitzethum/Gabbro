module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Parameters
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Projection
public import Grammatik.Logik.Invarianten.Frag.Witness

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic.ProductWitness

open Elim Elim.Korrekt

abbrev declaration := Frag.Witness.declaration
abbrev u32 : Ty := .int 0 (2 ^ 32 - 1)
abbrev pair : Ty := .prod 0 [u32, u32]

def domain : Parameters declaration 0 [pair] :=
  (parameters 0 0 [pair]).toOption.get (by with_unfolding_all rfl)

/-- Two independent full-width fields use two keys and one template, at zero
    integer enumeration budget. The actual parameter space has 2^64 values. -/
theorem parameter_components_zeuge : domain.next = 2 ∧ domain.templates.length = 1 := by
  constructor <;> with_unfolding_all rfl

def seven : Wert declaration u32 := ⟨7, by decide, by decide⟩
def nine : Wert declaration u32 := ⟨9, by decide, by decide⟩
def actual : Env declaration [pair] := .cons (ProdVal.pcons seven (ProdVal.pcons nine ())) .nil

theorem actual_coverage_zeuge (world : World declaration) :
    ∃ symbols ∈ domain.templates, ∃ valuation,
      symbols.Realizes valuation world actual ∧ ∀ key, key < 0 → valuation key = 0 :=
  domain.cover world actual (fun _ => 0)

end Gabbro.Grammatik.Invarianten.Frag.Symbolic.ProductWitness
