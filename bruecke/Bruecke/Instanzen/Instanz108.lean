module
import Grammatik.Kern.Taktik.KernelRfl
public import Bruecke.Pflichten
public import Bruecke.Pruefung
public import Grammatik.Korpus.Programme.Einheit108
public import Bruecke.Start
public import Bruecke.Quelle
public import Bruecke.Kette.Quelle
public import Duty.Duty0108DisjointStartLocks
import all Init.Data.String.Length
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.Repr
import all Init.Data.String.Decode
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


/-! BRIDGE-INSTANCE beispiele/0108-disjoint-start-locks.gab Bruecke.Instanzen.Instanz108

    S1+S2 instance: `beispiele/0108-disjoint-start-locks.gab` (see `Instanz104.lean`). -/

namespace Gabbro.Bruecke.I108

open Gabbro.Body Gabbro.Grammatik.Parser.Uebersetze
open GabbroDuty.Duty0108DisjointStartLocks
open Gabbro.Grammatik.Parser.UebersetzeAllg (fnAt)

def u := Gabbro.Grammatik.Parser.UebersetzeAllg2.uExp108

theorem verankert : ∃ P fs, Gabbro.Grammatik.uebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2.src108 = .ok ⟨u, P, fs⟩ :=
  ⟨_, _, Gabbro.Grammatik.Einheit108.uebersetzt8⟩

def ra : UFn := u.fns[0]'(by decide)
def rc : UFn := u.fns[1]'(by decide)

theorem shape_eq : shapeOf = shapeOfUG u := by
  funext p
  rcases p with ⟨c, i, f⟩ | ⟨c, n⟩ | n
  · by_cases hc : c = "T" <;> by_cases hf : f = "v" <;>
      simp [shapeOf, shapeOfUG, shapeOfU, globShape, Gabbro.Grammatik.Parser.UebersetzeAllg.globIdx, slotShape, u, Gabbro.Grammatik.Parser.UebersetzeAllg2.uExp108, hc, hf, @eq_comm _ "v"]
  · simp only [shapeOf, shapeOfUG, shapeOfU, globShape, Gabbro.Grammatik.Parser.UebersetzeAllg.globIdx, u, Gabbro.Grammatik.Parser.UebersetzeAllg2.uExp108]
  · simp only [shapeOf, shapeOfUG, shapeOfU, globShape, Gabbro.Grammatik.Parser.UebersetzeAllg.globIdx, u, Gabbro.Grammatik.Parser.UebersetzeAllg2.uExp108]

example : zuBody u ra = some read_a_body := rfl
example : zuBody u rc = some read_c_body := rfl
example : preExpr ra = read_a_pre := rfl
example : preExpr rc = read_c_pre := rfl
example : ra.puts = read_a_writes := rfl
example : rc.puts = read_c_writes := rfl
example : (fun s s' r => (postU u wellFormed ra s s' r).getD False) = read_a_post := rfl
example : (fun s s' r => (postU u wellFormed rc s s' r).getD False) = read_c_post := rfl
example : preProp wellFormed ra = read_a_requires := rfl
example : preProp wellFormed rc = read_c_requires := rfl
example : meetsU u wellFormed ra ((zuBody u ra).getD []) = read_a_meets_statement := rfl
example : meetsU u wellFormed rc ((zuBody u rc).getD []) = read_c_meets_statement := rfl

/-- S4 (start part): the start obligation of the chain's unit holds by the shape of the lowering. -/
theorem start : Gabbro.Grammatik.Zielsatz.StartPflicht Gabbro.Grammatik.Einheit108.E8 :=
  startPflicht_wahr _ (fun _ => rfl) (lowerAllg_requires _ _ _ (by decide) Gabbro.Grammatik.Einheit108.low8)

/-! BRIDGE-CLOSED beispiele/0108-disjoint-start-locks.gab nutzer_bruecke

    S3 instance: the simulation theorem applied to the parser's program of 108 (see
    `Instanz104.lean`); the duties are GabbroV's `read_a_meets` and `read_c_meets`. -/

theorem wf_eq : wellFormed = fun s => Gabbro.Body.WF (shapeOfUG u) s.world := by
  funext s; unfold wellFormed; rw [shape_eq]

theorem wfU_eq : wfU u = wellFormed := by rw [wf_eq]; rfl

/-- Every duty of the unit, as the bridge states it: GabbroV's proofs. -/
theorem meets_alle : ∀ c : Fin u.fns.length, ∃ body, zuBodyZ u (fnAt u c) = some body ∧
    meetsU u (wfU u) (fnAt u c) body := by
  intro c
  rw [wfU_eq]
  match c with
  | ⟨0, _⟩ => exact ⟨read_a_body, (by kernel_rfl), read_a_meets⟩
  | ⟨1, _⟩ => exact ⟨read_c_body, (by kernel_rfl), read_c_meets⟩

/-! GENERIC-WITNESS beispiele/0108-disjoint-start-locks.gab pflichten_108

    P6: the computed statement `PflichtenAlle src108` (`Quelle.lean`), witnessed by the front end's own
    output and GabbroV's duty proofs. -/

theorem pflichten_108 (hPtr : SchnittstellenPflicht u) :
    PflichtenAlle Gabbro.Grammatik.Parser.UebersetzeAllg2.src108 :=
  ⟨u, uOf_eq Gabbro.Grammatik.Einheit108.uebersetzt8, by decide, by decide, by decide, by decide,
    by decide, hPtr, fun c => by
      obtain ⟨body, hb, hm⟩ := meets_alle c
      exact ⟨body, hb, hm⟩⟩

/-- Premise (b) from the Body duties and the separately owed O43 refinement. -/
theorem nutzer_bruecke (hPtr : SchnittstellenPflicht u) :
    Gabbro.Grammatik.Zielsatz.NutzerPflicht Gabbro.Grammatik.Einheit108.E8 := by
  obtain ⟨hn, hp⟩ := nutzer_aus_quelleG_alle (pflichten_108 hPtr)
    Gabbro.Grammatik.Einheit108.uebersetzt8
  exact ⟨hp.logik, start⟩

/-! BRIDGE-ATOMIC beispiele/0108-disjoint-start-locks.gab nutzerA_bruecke -/

/-- The same premise WITH THE ATOMIC RELY (`NutzerPflichtA`): the parser's unit has no shared atomic. -/
theorem nutzerA_bruecke (hPtr : SchnittstellenPflicht u) :
    Gabbro.Grammatik.Zielsatz.NutzerPflichtA Gabbro.Grammatik.Einheit108.E8 :=
  Gabbro.Grammatik.Zielsatz.nutzerPflichtA_ohne_atomar
    (declOf_kein_atomar u rfl) (nutzer_bruecke hPtr)

#print axioms nutzerA_bruecke




#print axioms nutzer_bruecke

end Gabbro.Bruecke.I108
