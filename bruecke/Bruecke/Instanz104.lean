import Bruecke.Pflichten
import Bruecke.Pruefung
import Grammatik.Kette104
import Grammatik.Kette104Satz
import Bruecke.Start
import Bruecke.Atomar
import Bruecke.Quelle
import Duty.Duty104Referenz

/-! BRIDGE-INSTANCE beispiele/104-referenz.gab Bruecke.Instanz104

    S1+S2 instance: `beispiele/104-referenz.gab`.
    The parse is anchored at the source text by `Kette104.uebersetzt4`
    (`uebersetzeAllg src104real = .ok ⟨uExp104, …⟩`); every printed definition of
    `Duty104Referenz.lean` is checked against the Lean computation from `uExp104`. -/

namespace Gabbro.Bruecke.I104

open Gabbro.Body Gabbro.Grammatik.Parser.Uebersetze
open GabbroDuty.Duty104Referenz
open Gabbro.Grammatik.Parser.UebersetzeAllg (fnAt)

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

/-! BRIDGE-CLOSED beispiele/104-referenz.gab nutzer_bruecke

    S3 instance: the simulation theorem (`Bruecke/Simulation.lean`, `bruecke_nutzer`) applied to the
    parser's program of 104. Its premises, each checked here: the lowering (`Kette104.low4`), the
    name conditions and the rank of the call graph (decided), and the DUTIES -- GabbroV's own
    proofs `einzahlen_meets` and `lies_meets` from `Duty104Referenz.lean`, the statements the
    per-unit `rfl` checks above tie to the Lean computation. The conclusion is premise (b) of the
    goal theorem for the chain's unit `E4`. -/

theorem wfU_eq : wfU u = wellFormed := by rw [wf_eq]; rfl

/-- Every duty of the unit, as the bridge states it: GabbroV's proofs. -/
theorem meets_alle : ∀ c : Fin u.fns.length, ∃ body, zuBody u (fnAt u c) = some body ∧
    meetsU u (wfU u) (fnAt u c) body := by
  intro c
  rw [wfU_eq]
  match c with
  | ⟨0, _⟩ => exact ⟨einzahlen_body, rfl, einzahlen_meets⟩
  | ⟨1, _⟩ => exact ⟨lies_body, rfl, lies_meets⟩

theorem stimmig : Stimmig u := stimmig_of (by decide)

theorem rang : Rang u (rangAuto u) := rang_of (by decide)

/-! GENERIC-WITNESS beispiele/104-referenz.gab pflichten_104

    P6: the same bridge through the GENERIC theorem over every source (`Quelle.lean`). The
    statement `Pflichten src104real` is COMPUTED from the pinned text; this file only supplies a
    witness (the elaborated program, checked against the text by `verankert`'s theorem) and the
    duty proofs of GabbroV. -/

theorem pflichten_104 : Pflichten Gabbro.Grammatik.Parser.UebersetzeAllg2.src104real :=
  ⟨u, uOf_eq Gabbro.Grammatik.Kette104.uebersetzt4, by decide, by decide, by decide, meets_alle⟩

/-- Premise (b) for the unit the GENERIC construction builds from the text. -/
theorem nutzer_generisch : ∃ hn : nullB u = true,
    Gabbro.Grammatik.Zielsatz.NutzerPflicht (einheitAllg u Gabbro.Grammatik.Kette104.P4 hn) :=
  nutzer_aus_quelle pflichten_104 Gabbro.Grammatik.Kette104.uebersetzt4

/-- **THE CLOSED BRIDGE OF 104**: premise (b) of the goal theorem, from GabbroV's duty proofs. -/
theorem nutzer_bruecke : Gabbro.Grammatik.Zielsatz.NutzerPflicht Gabbro.Grammatik.Kette104.E4 :=
  bruecke_nutzer Gabbro.Grammatik.Kette104.low4 stimmig (rangAuto u) rang meets_alle
    Gabbro.Grammatik.Kette104.E4 rfl rfl rfl

/-- The closed chain of 104 with its premise (b) taken from the bridge instead of the hand proof
    `nutzer4`: source text, checker, GabbroV's duties, the correspondence to the C. -/
def kette_104_bruecke : Gabbro.Grammatik.Kette Gabbro.Grammatik.Parser.UebersetzeAllg2.src104real :=
  { Gabbro.Grammatik.Kette104.kette_104 with nutzer := nutzer_bruecke }

/-- **WITNESS of the simulation theorem** (`bruecke_nutzer`): its premises hold jointly on a real
    program with a call -- the parser's lowering of 104, the name conditions, a rank, and every
    duty proved by GabbroV. -/
theorem bruecke_zeuge : ∃ (u : UProg) (P : Gabbro.Grammatik.Programm (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf u))
    (fs : List (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf u).Fn),
    Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerAllg u = .ok (P, fs) ∧ Stimmig u ∧ Rang u (rangAuto u) ∧
    (∀ c : Fin u.fns.length, ∃ body, zuBody u (fnAt u c) = some body ∧ meetsU u (wfU u) (fnAt u c) body) ∧
    ∃ c : Fin u.fns.length, ∃ g args, UStmt.call g args ∈ (fnAt u c).saetze :=
  ⟨u, _, _, Gabbro.Grammatik.Kette104.low4, stimmig, rang, meets_alle,
    ⟨⟨0, by decide⟩, "lies", [.freshPtr "Konto" false, .wert (.param "i")], by decide⟩⟩

/-! BRIDGE-ATOMIC beispiele/104-referenz.gab nutzerA_bruecke -/

/-- The same premise WITH THE ATOMIC RELY (`NutzerPflichtA`): the parser's unit has no shared atomic. -/
theorem nutzerA_bruecke : Gabbro.Grammatik.Zielsatz.NutzerPflichtA Gabbro.Grammatik.Kette104.E4 :=
  bruecke_nutzerA Gabbro.Grammatik.Kette104.low4 stimmig (rangAuto u) rang meets_alle
    Gabbro.Grammatik.Kette104.E4 rfl rfl rfl

#print axioms nutzerA_bruecke


/-! BRIDGE-CHAIN beispiele/104-referenz.gab kette_104_bruecke -/

#print axioms kette_104_bruecke

#print axioms nutzer_bruecke
#print axioms bruecke_zeuge

end Gabbro.Bruecke.I104
