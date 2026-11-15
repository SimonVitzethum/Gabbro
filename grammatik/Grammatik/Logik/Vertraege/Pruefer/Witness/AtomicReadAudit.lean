module

public import Grammatik.Gen.Zeugen.M.M49_50
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.AtomicReadAudit

open Gabbro.Grammatik Gen Zielsatz

abbrev original := Gen.Zeugen.M49_50.e
abbrev declaration := original.D

local instance : DecidableEq declaration.Fn := original.aufz.decFn
local instance : DecidableEq declaration.Ax := original.aufz.decAx

/-- Both existing gates accept the unchanged generated candidate. -/
theorem gates_zeuge :
    Invarianten.Pruefer.programInvariantsB original.P original.S original.fs original.lockSources
      {} original.ls = true ∧
    KontrakteGeprueftB original.P original.S original.fs original.lockSources = true := by
  constructor <;> decide +kernel

/-- This is the generator's actual model Bool, not a substitute checker. -/
theorem accepted_zeuge : original.gueltig = true :=
  Gen.Zeugen.M49_50.e_gueltig_iff_gates.mpr gates_zeuge

/-- The normal soundness theorem supplies the entire model specification;
    only its standing named native-hardware class is in scope. -/
theorem model_spec_zeuge [RootNativeFloat.Hardware] :
    AkzeptiertSpecX original.P original.S original.fs original.ws [] [] :=
  akzeptiertSpecX_of original.hvoll original.hls original.hcs [] accepted_zeuge

/-- Semantic invariant duties are outputs of the actual gate. -/
theorem invariant_duties_zeuge : ∀ f,
    Invarianten.Pruefer.InvariantDuties original.P original.S f :=
  Invarianten.Pruefer.programInvariantsB_sound original.P original.S original.fs
    original.lockSources {} original.hvoll gates_zeuge.1

/-- Semantic contract duties are outputs too, without per-program assumptions. -/
theorem contract_duties_zeuge : ∀ f, ContractDuties original.P original.S f :=
  KontrakteGeprueftB_sound original.hvoll gates_zeuge.2

#print axioms accepted_zeuge
#print axioms model_spec_zeuge
#print axioms invariant_duties_zeuge
#print axioms contract_duties_zeuge

/-- One planted fault: only the second function's postcondition changes. -/
def falseProgram : Programm declaration :=
  { original.P with ensures := fun f => if f.val = 1 then .fls else original.P.ensures f }

def negative : Einsatz :=
  { original with P := falseProgram, hBoden := original.hBoden }

theorem same_body_zeuge : negative.P.rumpf = original.P.rumpf := rfl

theorem false_contract_refused_zeuge : negative.gueltig = false := by decide +kernel

abbrev returnedFunction : declaration.Fn := ⟨1, by decide⟩

/-- Every stored cell has Boolean type in this generated declaration. -/
def world : World declaration where
  slots
    | ⟨0, _⟩, _, ⟨0, _⟩ => false
    | ⟨1, _⟩, _, ⟨0, _⟩ => false
    | ⟨0, _⟩, _, ⟨n + 1, h⟩ => by have : n + 1 < 1 := h; omega
    | ⟨1, _⟩, _, ⟨n + 1, h⟩ => by have : n + 1 < 1 := h; omega
    | ⟨n + 2, h⟩, _, _ => by have : n + 2 < 2 := h; omega
  globs
    | ⟨0, _⟩ => false
    | ⟨1, _⟩ => false
    | ⟨2, _⟩ => false
    | ⟨3, _⟩ => false
    | ⟨n + 4, h⟩ => by have : n + 4 < 4 := h; omega
  spur := []

def calls (f : declaration.Fn) (_ : World declaration)
    (_ : Env declaration (declaration.params f)) : RufAusgang f := .logik .schleife

/-- The changed post is false on a concrete entry/return pair. -/
theorem false_contract_counterexample_zeuge :
    ReqAmEintritt negative.P returnedFunction world .nil ∧
      ¬ EnsAmRueck negative.P returnedFunction world world .nil () :=
  ⟨rfl, Bool.false_ne_true⟩

/-- The original return body really returns; the negative is not vacuous. -/
theorem concrete_return_zeuge (O : Orakel declaration) :
    execEnd O 0 calls (negative.P.rumpf returnedFunction) world .nil =
      .zurueck world () := by rfl

#print axioms false_contract_refused_zeuge
#print axioms false_contract_counterexample_zeuge
#print axioms concrete_return_zeuge

end Gabbro.Grammatik.Vertraege.Pruefer.AtomicReadAudit
