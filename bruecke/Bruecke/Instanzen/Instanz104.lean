module
public import Bruecke.Pflichten
public import Bruecke.Pruefung
public import Grammatik.Korpus.Programme.Einheit104
public import Bruecke.Start
public import Bruecke.Quelle
public import Bruecke.Kette.Quelle
public import Duty.Duty0104Referenz
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


/-! BRIDGE-INSTANCE beispiele/0104-referenz.gab Bruecke.Instanzen.Instanz104

    S1+S2 instance: `beispiele/0104-referenz.gab`.
    The parse is anchored at the source text by `Einheit104.uebersetzt4`
    (`uebersetzeAllg src104real = .ok ⟨uExp104, …⟩`); every printed definition of
    `Duty0104Referenz.lean` is checked against the Lean computation from `uExp104`. -/

namespace Gabbro.Bruecke.I104

open Gabbro.Body Gabbro.Grammatik.Parser.Uebersetze
open GabbroDuty.Duty0104Referenz
open Gabbro.Grammatik.Parser.UebersetzeAllg (fnAt)

def u := uExp104

/-- The anchor: the SOURCE TEXT (`src104real`, byte for byte, pinned in `Einheit104`) elaborates to
    `u`, in Lean. Every check below is about the program of that text. -/
theorem verankert : ∃ P fs, Gabbro.Grammatik.uebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2.src104real = .ok ⟨u, P, fs⟩ :=
  ⟨_, _, Gabbro.Grammatik.Einheit104.uebersetzt4⟩

def ein : UFn := u.fns[0]'(by decide)
def lies : UFn := u.fns[1]'(by decide)

theorem shape_eq : shapeOf = shapeOfUG u := by
  funext p
  rcases p with ⟨c, i, f⟩ | ⟨c, n⟩ | n
  · by_cases hc : c = "Konto" <;> by_cases hf : f = "stand" <;>
      simp [shapeOf, shapeOfUG, shapeOfU, globShape, Gabbro.Grammatik.Parser.UebersetzeAllg.globIdx, slotShape, u, uExp104, hc, hf, @eq_comm _ "stand"]
  · simp only [shapeOf, shapeOfUG, shapeOfU, globShape, Gabbro.Grammatik.Parser.UebersetzeAllg.globIdx, u, uExp104]
  · simp only [shapeOf, shapeOfUG, shapeOfU, globShape, Gabbro.Grammatik.Parser.UebersetzeAllg.globIdx, u, uExp104]

theorem wf_eq : wellFormed = fun s => WF (shapeOfUG u) s.world := by
  funext s; unfold wellFormed; rw [shape_eq]

/-- The bridge permits the private call clock to advance in a read-only callee. -/
def einzahlen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State) (hwf : wellFormed s)
    (hpre : eval s einzahlen_pre = some (.bool true))
    (c_lies : Contract ρ "lies" lies_requires lies_post)
    (fr_lies : Frame ρ "lies" [callClock]),
    ∃ s', finalState (exec ρ einzahlen_body s) = some s'
        ∧ einzahlen_post s s' (finalValue (exec ρ einzahlen_body s))

theorem einzahlen_meets : einzahlen_meets_statement := by
  intro ρ s hwf hpre c_lies fr_lies
  obtain ⟨i, ei, ilo, ihi⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  obtain ⟨n, en, _, nhi⟩ :=
    WF_intIn shapeOf s.world (.slot "Konto" i "stand") 0 100 hwf rfl
  let σ := store s.world (.slot "Konto" i "stand") (.int 100)
  let t : State := ⟨σ, bindAll ["k", "i"] [s.local' "k", .int i] (fun _ => .absent)⟩
  have hσ : WF shapeOf σ := by
    apply WF_store _ _ _ _ hwf
    intro sh hsh
    have hs : some (.intIn 0 100) = some sh := hsh
    cases hs
    decide
  have ht : lies_requires t := by
    refine ⟨hσ, ?_⟩
    simp [t, lies_pre, eval, bindAll, bindLocal, Value.hasShape, andBool, ilo, ihi]
  have hc := c_lies t ht
  let s' : State := { s with world := (ρ "lies" t).1.world }
  have he : exec ρ einzahlen_body s = .running s' := by
    simp [einzahlen_body, exec, step, eval, evalAll, ei, t, σ, s',
      bindAll, bindLocal, Value.hasShape, andBool, ilo, ihi]
  have hr : (ρ "lies" t).1.world (.slot "Konto" i "stand") = .int 100 := by
    rw [Frame_read ρ "lies" [callClock] fr_lies t (.slot "Konto" i "stand")
      (by simp [Place.carrier, callClock])]
    exact store_here _ _ _
  refine ⟨s', ?_, ?_⟩
  · rw [he]
    rfl
  · change wellFormed s' ∧ _
    refine ⟨hc.1, ?_⟩
    intro ov hov
    have ho : .int n = ov := Option.some.inj (by simpa [eval, ei, en] using hov)
    subst ov
    simp [eval, s', ei, bindLocal, hr, binop, nhi]

theorem einzahlen_body_eq : zuBodyZ u ein = some einzahlen_body := by cbv
theorem lies_body_eq : zuBodyZ u lies = some lies_body := by cbv
example : preExpr ein = einzahlen_pre := rfl
example : preExpr lies = lies_pre := rfl
example : ein.puts = einzahlen_writes := rfl
example : lies.puts = lies_writes := rfl

example : (fun s s' r => (postU u wellFormed ein s s' r).getD False) = einzahlen_post := rfl
example : (fun s s' r => (postU u wellFormed lies s s' r).getD False) = lies_post := rfl
example : preProp wellFormed ein = einzahlen_requires := rfl
example : preProp wellFormed lies = lies_requires := rfl

example : meetsU u wellFormed ein ((zuBodyZ u ein).getD []) = einzahlen_meets_statement := by
  rw [einzahlen_body_eq]
  rfl
example : meetsU u wellFormed lies ((zuBodyZ u lies).getD []) = lies_meets_statement := by
  rw [lies_body_eq]
  rfl

/-- S4 (start part): the start obligation of the chain's unit holds by the shape of the lowering. -/
theorem start : Gabbro.Grammatik.Zielsatz.StartPflicht Gabbro.Grammatik.Einheit104.E4 :=
  startPflicht_wahr _ (fun _ => rfl) (lowerAllg_requires _ _ _ (by decide) Gabbro.Grammatik.Einheit104.low4)

/-! BRIDGE-CLOSED beispiele/0104-referenz.gab nutzer_bruecke

    S3 instance: the consolidated source theorem (`Kette/Quelle.lean`) applied to the
    parser's program of 104. Its premises, each checked here: the lowering (`Einheit104.low4`), the
    name conditions and the rank of the call graph (decided), and the DUTIES -- the frame-aware
    `einzahlen_meets` above and GabbroV's `lies_meets` from `Duty0104Referenz.lean`, tied to the
    canonical reader by the body equalities above. The conclusion is premise (b) of the
    goal theorem for the chain's unit `E4`. -/

theorem wfU_eq : wfU u = wellFormed := by rw [wf_eq] <;> rfl

/-- Every duty of the unit, as the bridge states it: GabbroV's proofs. -/
theorem meets_alle : ∀ c : Fin u.fns.length, ∃ body, zuBodyZ u (fnAt u c) = some body ∧
    meetsU u (wfU u) (fnAt u c) body := by
  intro c
  rw [wfU_eq]
  match c with
  | ⟨0, _⟩ => exact ⟨einzahlen_body, einzahlen_body_eq, einzahlen_meets⟩
  | ⟨1, _⟩ => exact ⟨lies_body, lies_body_eq, lies_meets⟩

/-! GENERIC-WITNESS beispiele/0104-referenz.gab pflichten_104

    P6: the same bridge through the GENERIC theorem over every source (`Quelle.lean`). The
    statement `PflichtenAlle src104real` is COMPUTED from the pinned text; this file only supplies a
    witness (the elaborated program, checked against the text by `verankert`'s theorem) and the
    duty proofs of GabbroV. -/

theorem pflichten_104 (hPtr : SchnittstellenPflicht u) :
    PflichtenAlle Gabbro.Grammatik.Parser.UebersetzeAllg2.src104real :=
  ⟨u, uOf_eq Gabbro.Grammatik.Einheit104.uebersetzt4, by decide, by decide, by decide, by decide,
    by decide, hPtr, fun c => by
      obtain ⟨body, hb, hm⟩ := meets_alle c
      exact ⟨body, hb, hm⟩⟩

/-- Premise (b) for the unit the GENERIC construction builds from the text. -/
theorem nutzer_generisch (hPtr : SchnittstellenPflicht u) : ∃ hn : nullB u = true,
    Gabbro.Grammatik.Zielsatz.NutzerPflicht (einheitAllg u Gabbro.Grammatik.Einheit104.P4 hn) :=
  nutzer_aus_quelleG_alle (pflichten_104 hPtr) Gabbro.Grammatik.Einheit104.uebersetzt4

/-- Premise (b) from the Body duties and the separately owed O43 refinement. -/
theorem nutzer_bruecke (hPtr : SchnittstellenPflicht u) :
    Gabbro.Grammatik.Zielsatz.NutzerPflicht Gabbro.Grammatik.Einheit104.E4 := by
  obtain ⟨hn, hp⟩ := nutzer_aus_quelleG_alle (pflichten_104 hPtr)
    Gabbro.Grammatik.Einheit104.uebersetzt4
  exact ⟨hp.logik, start⟩

/-! BRIDGE-ATOMIC beispiele/0104-referenz.gab nutzerA_bruecke -/

/-- The same premise WITH THE ATOMIC RELY (`NutzerPflichtA`): the parser's unit has no shared atomic. -/
theorem nutzerA_bruecke (hPtr : SchnittstellenPflicht u) :
    Gabbro.Grammatik.Zielsatz.NutzerPflichtA Gabbro.Grammatik.Einheit104.E4 :=
  Gabbro.Grammatik.Zielsatz.nutzerPflichtA_ohne_atomar
    (declOf_kein_atomar u rfl) (nutzer_bruecke hPtr)

#print axioms nutzerA_bruecke




#print axioms nutzer_bruecke

end Gabbro.Bruecke.I104
