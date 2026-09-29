import Bruecke.Pflichten
import Grammatik.Kette104
import Grammatik.Kette104Satz
import Bruecke.Start
import Duty.Duty104Referenz

/-! BRIDGE-INSTANCE beispiele/104-referenz.gab Bruecke.Instanz104

    S1+S2 instance: `beispiele/104-referenz.gab`.
    The parse is anchored at the source text by `Kette104.uebersetzt4`
    (`uebersetzeAllg src104real = .ok ⟨uExp104, …⟩`); every printed definition of
    `Duty104Referenz.lean` is checked against the Lean computation from `uExp104`. -/

namespace Gabbro.Bruecke.I104

open Gabbro.Body Gabbro.Grammatik.Parser.Uebersetze
open GabbroDuty.Duty104Referenz

def u := uExp104

/-- The anchor: the SOURCE TEXT (`src104real`, byte for byte, pinned in `Kette104`) elaborates to
    `u`, in Lean. Every check below is about the program of that text. -/
theorem verankert : ∃ P fs, Gabbro.Grammatik.uebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2.src104real = .ok ⟨u, P, fs⟩ :=
  ⟨_, _, Gabbro.Grammatik.Kette104.uebersetzt4⟩

def ein : UFn := u.fns[0]'(by decide)
def lies : UFn := u.fns[1]'(by decide)

theorem shape_eq : shapeOf = shapeOfU u := by
  funext p
  rcases p with ⟨c, i, f⟩ | ⟨c, n⟩ | n
  · by_cases hc : c = "Konto" <;> by_cases hf : f = "stand" <;>
      simp [shapeOf, shapeOfU, slotShape, u, uExp104, hc, hf, @eq_comm _ "stand"]
  · simp [shapeOf, shapeOfU]
  · simp [shapeOf, shapeOfU]

theorem wf_eq : wellFormed = fun s => WF (shapeOfU u) s.world := by
  funext s; unfold wellFormed; rw [shape_eq]


example : zuBody u ein = some einzahlen_body := rfl
example : zuBody u lies = some lies_body := rfl
example : preExpr ein = einzahlen_pre := rfl
example : preExpr lies = lies_pre := rfl
example : ein.schreibt = einzahlen_writes := rfl
example : lies.schreibt = lies_writes := rfl

example : (fun s s' r => (postU u wellFormed ein s s' r).getD False) = einzahlen_post := rfl
example : (fun s s' r => (postU u wellFormed lies s s' r).getD False) = lies_post := rfl
example : preProp wellFormed ein = einzahlen_requires := rfl
example : preProp wellFormed lies = lies_requires := rfl

example : meetsU u wellFormed ein ((zuBody u ein).getD []) = einzahlen_meets_statement := rfl
example : meetsU u wellFormed lies ((zuBody u lies).getD []) = lies_meets_statement := rfl

/-- S4 (start part): the start obligation of the chain's unit holds by the shape of the lowering. -/
theorem start : Gabbro.Grammatik.Zielsatz.StartPflicht Gabbro.Grammatik.Kette104.E4 :=
  startPflicht_wahr _ (fun _ => rfl) (lowerAllg_requires _ _ _ Gabbro.Grammatik.Kette104.low4)

end Gabbro.Bruecke.I104
