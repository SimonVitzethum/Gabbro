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

#eval repr Gen.Zeugen.M49_50.z

end Gabbro.Grammatik.Vertraege.Pruefer.AtomicReadAudit
