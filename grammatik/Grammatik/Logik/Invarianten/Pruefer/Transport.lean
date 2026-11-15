module

public import Grammatik.Logik.Invarianten.Pruefer.Program
public import Grammatik.Zielsatz.Atomar.AtomarRuheNutzer

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer

variable {D : Deklaration} {P : Programm D} {S : SperrInv D}

/-- The idle-root transformation transports semantic checker facts rather
    than rerunning VC generation on generated code. -/
theorem invariantDuties_mitRuhe (checked : ∀ f, InvariantDuties P S f) :
    ∀ f, InvariantDuties P.mitRuhe S.mitRuhe f := by
  intro f passes Q shared subset
  cases f with
  | none => exact ⟨invGutSA_ruhe P passes Q S.mitRuhe shared, invGutGrundA_ruhe⟩
  | some f =>
      have facts := checked f passes (axWahr D) shared subset
      have normal := invGutSA_mitRuhe facts.1
      have reason := invGutGrundA_mitRuhe facts.2
      constructor
      · intro O frame locality contract U havoc A atomic R respects noPre
        exact normal O frame locality (axVertragOP_of_O _ (axVertragO_wahr O)) U havoc A atomic R respects noPre
      · intro O frame locality contract U havoc A atomic R respects noPre
        exact reason O frame locality (axVertragOP_of_O _ (axVertragO_wahr O)) U havoc A atomic R respects noPre

end Gabbro.Grammatik.Invarianten.Pruefer
