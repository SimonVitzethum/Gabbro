import Bruecke.Pflichten
import Bruecke.Pruefung
import Grammatik.Kette108
import Bruecke.Start
import Bruecke.Atomar
import Duty.Duty108DisjointStartLocks

/-! BRIDGE-INSTANCE beispiele/108-disjoint-start-locks.gab Bruecke.Instanz108

    S1+S2 instance: `beispiele/108-disjoint-start-locks.gab` (see `Instanz104.lean`). -/

namespace Gabbro.Bruecke.I108

open Gabbro.Body Gabbro.Grammatik.Parser.Uebersetze
open GabbroDuty.Duty108DisjointStartLocks
open Gabbro.Grammatik.Parser.UebersetzeAllg (fnAt)

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

/-- S4 (start part): the start obligation of the chain's unit holds by the shape of the lowering. -/
theorem start : Gabbro.Grammatik.Zielsatz.StartPflicht Gabbro.Grammatik.Kette108.E8 :=
  startPflicht_wahr _ (fun _ => rfl) (lowerAllg_requires _ _ _ Gabbro.Grammatik.Kette108.low8)

/-! BRIDGE-CLOSED beispiele/108-disjoint-start-locks.gab nutzer_bruecke

    S3 instance: the simulation theorem applied to the parser's program of 108 (see
    `Instanz104.lean`); the duties are GabbroV's `read_a_meets` and `read_c_meets`. -/

theorem wf_eq : wellFormed = fun s => Gabbro.Body.WF (shapeOfU u) s.world := by
  funext s; unfold wellFormed; rw [shape_eq]

theorem wfU_eq : wfU u = wellFormed := by rw [wf_eq]; rfl

/-- Every duty of the unit, as the bridge states it: GabbroV's proofs. -/
theorem meets_alle : ∀ c : Fin u.fns.length, ∃ body, zuBody u (fnAt u c) = some body ∧
    meetsU u (wfU u) (fnAt u c) body := by
  intro c
  rw [wfU_eq]
  match c with
  | ⟨0, _⟩ => exact ⟨read_a_body, rfl, read_a_meets⟩
  | ⟨1, _⟩ => exact ⟨read_c_body, rfl, read_c_meets⟩

theorem stimmig : Stimmig u := stimmig_of (by decide)

theorem rang : Rang u (rangAuto u) := rang_of (by decide)

/-- **THE CLOSED BRIDGE OF 108**: premise (b) of the goal theorem, from GabbroV's duty proofs. -/
theorem nutzer_bruecke : Gabbro.Grammatik.Zielsatz.NutzerPflicht Gabbro.Grammatik.Kette108.E8 :=
  bruecke_nutzer Gabbro.Grammatik.Kette108.low8 stimmig (rangAuto u) rang meets_alle
    Gabbro.Grammatik.Kette108.E8 rfl rfl rfl

/-- The closed chain of 108 with its premise (b) taken from the bridge. -/
def kette_108_bruecke : Gabbro.Grammatik.Kette Gabbro.Grammatik.Parser.UebersetzeAllg2.src108 :=
  { Gabbro.Grammatik.Kette108.kette_108 with nutzer := nutzer_bruecke }

/-! BRIDGE-ATOMIC beispiele/108-disjoint-start-locks.gab nutzerA_bruecke -/

/-- The same premise WITH THE ATOMIC RELY (`NutzerPflichtA`): the parser's unit has no shared atomic. -/
theorem nutzerA_bruecke : Gabbro.Grammatik.Zielsatz.NutzerPflichtA Gabbro.Grammatik.Kette108.E8 :=
  bruecke_nutzerA Gabbro.Grammatik.Kette108.low8 stimmig (rangAuto u) rang meets_alle
    Gabbro.Grammatik.Kette108.E8 rfl rfl rfl

#print axioms nutzerA_bruecke


/-! BRIDGE-CHAIN beispiele/108-disjoint-start-locks.gab kette_108_bruecke -/

#print axioms kette_108_bruecke

#print axioms nutzer_bruecke

end Gabbro.Bruecke.I108
