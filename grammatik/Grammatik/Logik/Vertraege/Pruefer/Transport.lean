module

public import Grammatik.Logik.Vertraege.Pruefer.Program
public import Grammatik.Zielsatz.Atomar.AtomarRuheNutzer

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

variable {D : Deklaration} {P : Programm D} {S : SperrInv D}

/-- Transport checked semantic facts through the existing idle-root proof. -/
theorem contractDuties_mitRuhe (checked : ∀ f, ContractDuties P S f) :
    ∀ f, ContractDuties P.mitRuhe S.mitRuhe f := by
  intro f passes Q shared subset
  cases f with
  | none => exact ⟨koerperGutSA_ruhe, invGutSA_ruhe, invGutGrundA_ruhe⟩
  | some f =>
      have facts := checked f passes (axWahr D) shared subset
      have body := koerperGutSA_mitRuhe facts.1
      have normal := invGutSA_mitRuhe facts.2.1
      have reason := invGutGrundA_mitRuhe facts.2.2
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · intro O frame local contract U havoc A atomic R respects noPre
        exact body.1 O frame local (axVertragOP_of_O _ (axVertragO_wahr O)) U havoc A atomic R respects noPre
      · intro O frame local contract U havoc A atomic R respects noLogic
        exact body.2 O frame local (axVertragOP_of_O _ (axVertragO_wahr O)) U havoc A atomic R respects noLogic
      · intro O frame local contract U havoc A atomic R respects noPre
        exact normal O frame local (axVertragOP_of_O _ (axVertragO_wahr O)) U havoc A atomic R respects noPre
      · intro O frame local contract U havoc A atomic R respects noPre
        exact reason O frame local (axVertragOP_of_O _ (axVertragO_wahr O)) U havoc A atomic R respects noPre

end Gabbro.Grammatik.Vertraege.Pruefer
