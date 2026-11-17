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

def components : SymEnv declaration Nat [u32, u32] :=
  .cons (.integer (.var 0)) (.cons (.integer (.var 1)) .nil)

def symbols : SymEnv declaration Nat [pair] := components.packProduct 0 [u32, u32]
def valuation : Assignment Nat := fun key => if key = 0 then 7 else 9

theorem components_bounded_zeuge : components.Bounded 2 := by
  refine ⟨?_, ?_, trivial⟩
  · intro key member; have same := List.mem_singleton.mp member; subst key; decide
  · intro key member; have same := List.mem_singleton.mp member; subst key; decide

theorem flatten_get_zeuge :
    (flattenProduct [u32, u32] (actual.get .here) (Env.nil : Env declaration [])).get
      (fieldVariable (.tail .head)) = nine :=
  flattenProduct_get (.tail .head) (actual.get .here) .nil

theorem pack_realizes_zeuge (world : World declaration) : symbols.Realizes valuation world actual :=
  components.realizes_packProduct 0 [u32, u32] (actual.get .here) .nil valuation world
    ⟨rfl, rfl, trivial⟩

theorem pack_bounded_zeuge : symbols.Bounded 2 :=
  components.bounded_packProduct 0 [u32, u32] components_bounded_zeuge

theorem drop_bounded_zeuge : (components.dropPrefix [u32, u32]).Bounded 2 :=
  components.bounded_dropPrefix [u32, u32] components_bounded_zeuge

theorem drop_realizes_zeuge (world : World declaration) :
    (components.dropPrefix [u32, u32]).Realizes valuation world .nil :=
  components.realizes_dropPrefix [u32, u32] (actual.get .here) .nil valuation world ⟨rfl, rfl, trivial⟩

def firstField : Expr declaration [pair] [] u32 := .prodGet (.var .here) .head

def view : ValueView symbols firstField := (valueView? firstField symbols).get (by rfl)

theorem view_zeuge (world old : World declaration) :
    view.symbol.Realizes valuation world (eval old firstField world actual) ∧ view.symbol.Bounded 2 :=
  ⟨view.realizes valuation old world actual (pack_realizes_zeuge world),
    view.bounded 2 pack_bounded_zeuge⟩

theorem product_lift_zeuge (world : World declaration) (fresh : Int) :
    (symbols.get .here).lift.Realizes (extend valuation fresh) world (actual.get .here) :=
  ((symbols.get .here).realizes_lift valuation world fresh _).mpr (pack_realizes_zeuge world).1

theorem product_world_zeuge (world after : World declaration) :
    (symbols.get .here).Realizes valuation after (actual.get .here) :=
  ((symbols.get .here).realizes_world valuation world after _).mp (pack_realizes_zeuge world).1

theorem product_congr_zeuge (world after : World declaration) :
    (symbols.get .here).Realizes valuation after (actual.get .here) :=
  ((symbols.get .here).realizes_congr 2 pack_bounded_zeuge.1 valuation valuation
    (fun _ _ => rfl) world after _).mp (pack_realizes_zeuge world).1

theorem product_bounded_mono_zeuge : (symbols.get .here).Bounded 3 :=
  (symbols.get .here).bounded_mono pack_bounded_zeuge.1 (by decide)

theorem product_projection_zeuge (world : World declaration) :
    ((symbols.get .here).field .head).Realizes valuation world seven ∧
      ((symbols.get .here).field .head).Bounded 2 :=
  ⟨(symbols.get .here).realizes_field .head valuation world _ (pack_realizes_zeuge world).1,
    (symbols.get .here).bounded_field 2 pack_bounded_zeuge.1 .head⟩

theorem context_size_zeuge : sizeOf ([u32, u32] ++ [pair]) ≤ sizeOf [u32, u32] + sizeOf [pair] :=
  context_size_append [u32, u32] [pair]

end Gabbro.Grammatik.Invarianten.Frag.Symbolic.ProductWitness
