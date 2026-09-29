import Bruecke.Pflichten
import Grammatik.Kette108
import Duty.Duty108DisjointStartLocks

/-! S1+S2 instance: `beispiele/108-disjoint-start-locks.gab` (see `Instanz104.lean`). -/

namespace Gabbro.Bruecke.I108

open Gabbro.Body Gabbro.Grammatik.Parser.Uebersetze
open GabbroDuty.Duty108DisjointStartLocks

def u := Gabbro.Grammatik.Parser.UebersetzeAllg2.uExp108

theorem verankert : ∃ P fs, Gabbro.Grammatik.uebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2.src108 = .ok ⟨u, P, fs⟩ :=
  ⟨_, _, Gabbro.Grammatik.Kette108.uebersetzt8⟩

def ra : UFn := u.fns[0]'(by decide)
def rc : UFn := u.fns[1]'(by decide)

theorem shape_eq : shapeOf = shapeOfU u := by
  funext p
  rcases p with ⟨c, i, f⟩ | ⟨c, n⟩ | n
  · by_cases hc : c = "T" <;> by_cases hf : f = "v" <;>
      simp [shapeOf, shapeOfU, slotShape, u, Gabbro.Grammatik.Parser.UebersetzeAllg2.uExp108, hc, hf, @eq_comm _ "v"]
  · simp [shapeOf, shapeOfU]
  · simp [shapeOf, shapeOfU]

example : zuBody u ra = some read_a_body := rfl
example : zuBody u rc = some read_c_body := rfl
example : preExpr ra = read_a_pre := rfl
example : preExpr rc = read_c_pre := rfl
example : ra.schreibt = read_a_writes := rfl
example : rc.schreibt = read_c_writes := rfl
example : (fun s s' r => (postU u wellFormed ra s s' r).getD False) = read_a_post := rfl
example : (fun s s' r => (postU u wellFormed rc s s' r).getD False) = read_c_post := rfl
example : preProp wellFormed ra = read_a_requires := rfl
example : preProp wellFormed rc = read_c_requires := rfl
example : meetsU u wellFormed ra ((zuBody u ra).getD []) = read_a_meets_statement := rfl
example : meetsU u wellFormed rc ((zuBody u rc).getD []) = read_c_meets_statement := rfl

end Gabbro.Bruecke.I108
