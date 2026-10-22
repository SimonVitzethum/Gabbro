/-
  File:      Grammatik/Zielsatz/Atomar/TerminierungZeuge.lean
  Subject:   WITNESS OF `GabbroZielTerminierung` (2026-10-22): every premise group discharged on the two-thread
             program `mE` (SpecProben.lean, MehrfadenZeuge.lean) -- the concrete checker `akzeptiertX_pruefer`
             accepts it (`decide`), its user logic holds with the rely (no atomic global), the empty measure meets
             the duty (no function lies on a cycle), the hardware and runtime premises hold -- on a run whose first
             step changes the memory; both starts are of class `endet`.
-/
import Grammatik.Zielsatz.Atomar.BeweisTerminierung
import Grammatik.Zielsatz.Kern.Proben

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

theorem mX_akzeptiert : akzeptiertX_pruefer.akzeptiert mE mFs [()] mCs = true := by decide

theorem mE_nutzerA : NutzerPflichtA mE := nutzerPflichtA_ohne_atomar (fun g => nomatch g) mE_nutzerPflicht

/-- No function of `mP` lies on a cycle. -/
theorem mZykS : ∀ f g : mD.Fn, zykS mP mFs f g = false := by
  intro f g
  cases f <;> cases g <;> decide

/-- Both starts are of class `endet`. -/
theorem mKlasse_A : klasse mP mFs (Mass.leer (D := mD)).hat mHauptA = .endet := by decide
theorem mKlasse_B : klasse mP mFs (Mass.leer (D := mD)).hat mHauptB = .endet := by decide

/-- Every declared start is of class `endet`. -/
theorem mStart_endet (t : Faden) (w : mD.Fn) (hw : (initRuhe mE.starts t).1 = some w) :
    klasse mE.P mFs (Mass.leer (D := mD)).hat w = .endet := by
  match t, hw with
  | 0, hw =>
      have : w = mHauptA := (Option.some.inj hw).symm
      subst this; exact mKlasse_A
  | 1, hw =>
      have : w = mHauptB := (Option.some.inj hw).symm
      subst this; exact mKlasse_B
  | _ + 2, hw => exact absurd hw (by simp [initRuhe, mE])

/-- The run: thread 0's first step (a write to `privA`), then nothing. -/
theorem terminierung_zeuge : ∃ (R : LaufGX mE.P.mitRuhe mO.mitRuhe 0 (GeteiltV (D := mD) mE.P mE.ws)),
    R.M 0 = RufStartG mE.P.mitRuhe (speicherR mSp) (initRuhe mE.starts) ∧ R.akt 0 = some 0 ∧
    (R.M 1).speicher ≠ speicherR mSp ∧
    ∀ t, (∃ N, ∀ j, N ≤ j → R.akt j ≠ some t) ∧ ∀ j, ¬ HaltBenannt mO.mitRuhe 0 (R.M j) .budget t := by
  obtain ⟨M1, s1, hZ1⟩ := w_blatt (P := mP.mitRuhe) (O := mO.mitRuhe) (passes := 0)
    (M := RufStartG mP.mitRuhe (speicherR mSp) (initRuhe [⟨mHauptA, .nil⟩, ⟨mHauptB, .nil⟩]))
    (f := 0) rfl _ _ _ rfl rfl (fun _ h => nomatch h) _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _) ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  let R : LaufGX mE.P.mitRuhe mO.mitRuhe 0 (GeteiltV (D := mD) mE.P mE.ws) :=
    { M := fun n => if n = 0 then RufStartG mP.mitRuhe (speicherR mSp) (initRuhe [⟨mHauptA, .nil⟩, ⟨mHauptB, .nil⟩])
        else M1
      akt := fun n => if n = 0 then some 0 else none
      schritt := fun n u h => by
        by_cases hn : n = 0
        · subst hn
          simp only [if_true, Option.some.injEq] at h
          subst h
          simp only [if_true, Nat.zero_add, Nat.one_ne_zero, if_false]
          exact gx_aus_g s1
        · simp only [hn, if_false] at h
          cases h
      stotter := fun n h => by
        by_cases hn : n = 0
        · subst hn; simp at h
        · simp only [hn, if_false, Nat.add_one_ne_zero] }
  have hL : Laufzeit mE (speicherR mSp) (initRuhe mE.starts) := laufzeit_initRuhe mE
  have hT := gabbro_ziel_terminierung akzeptiertX_pruefer mD mE ⟨mFs, mFs_voll⟩ ⟨[()], mLocks_voll⟩
    ⟨mCs, mCs_voll⟩ mX_akzeptiert mE_nutzerA 0 Mass.leer
    (fun f => massPflicht_ohne_zyklus mP mFs 0 _ _ _ _ f (mZykS f))
    (fun f g h => absurd (h.symm.trans (mZykS f g)) (by decide))
    mO ⟨mO_gut, mO_lokal, axVertragO_wahr mO⟩ _ _ hL R rfl
  refine ⟨R, rfl, rfl, ?_, fun t => ⟨(hT t).1, (hT t).2 fun w hw => ?_⟩⟩
  · intro h
    have e := congrArg (fun s : Speicher mD.mitRuhe => (s.slots MTab.privA 0 () : Zahl 0 100).n) h
    simp only [R, Nat.one_ne_zero, if_false] at e
    rw [hZ1.2] at e
    revert e
    decide
  · exact mStart_endet t w hw

#print axioms terminierung_zeuge

end Gabbro.Grammatik.Zielsatz
