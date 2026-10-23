/-
  File:      Grammatik/Zielsatz/Atomar/BeweisTerminierung.lean
  Subject:   THE PROOF OF `GabbroZielTerminierung` (2026-10-22): the premise groups (a)-(d) with the measure duty give
             the premises of `endet_satz` (Logik/Terminierung/Entscheidung.lean), as they give the replay in
             `zielX_aus`.
-/
import Grammatik.Zielsatz.Atomar.BeweisAtomar
import Grammatik.Logik.Terminierung.Entscheidung
import Grammatik.Zielsatz.Atomar.MassRuhe

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration}

section Aus

variable [DecidableEq D.Fn]

/-- **Termination from (a), (b) with the rely, the measure duty, (c) and an admissible start**: finitely many steps
    per thread on every infinite GX run, and for a start of class `endet` never a spent budget. -/
theorem terminierung_aus (P : Programm D) (S : SperrInv D) (Q : AxEns D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (ws : List D.Fn)
    (hA : AkzeptiertSpecX P S fs ws) (hN : LogikPflichtA P S Q (GeteiltA P ws)) (O : Orakel D)
    (hH : HardwareAnnahmen O Q) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hZ : StartZulaessig P S fs ws sp init)
    (m : Mass D) (hM : ∀ f, MassPflicht P passes Q S (GeteiltV P ws) m (zykS P fs) f)
    (hLm : ∀ f g, zykS P fs f g = true → (m f).length = (m g).length)
    (R : LaufGX P O passes (GeteiltV P ws)) (h0 : R.M 0 = RufStartG P sp init) (t : Faden) :
    (∃ N, ∀ j, N ≤ j → R.akt j ≠ some t) ∧
      (ewigFrei P fs (init t).1 = true → ∀ j, ¬ HaltBenannt O passes (R.M j) .budget t) := by
  have hW : ∀ t, D.haelt (init t).1 = [] ∧ D.gruende (init t).1 = 0 := fun t => by
    rcases hZ.wurzel t with h | h
    · exact hA.wurzeln _ h
    · exact ⟨h.1, h.2.1⟩
  have hLeer : ∀ t, D.haelt (init t).1 = [] := fun t => (hW t).1
  have hS : SperrInvOk S := ⟨hA.sperrOrte, hN.2.1⟩
  have hT : ∀ c, GeteiltV P ws c → GeteiltA P ws c := fun c h => h.1
  have hTA : ∀ c, GeteiltV P ws c → AtomarAusgenommen c := fun c h => h.1.1
  have hTV : ∀ c, GeteiltV P ws c → VertragsFrei P c := fun c h => h.2
  have hTS : ∀ c, GeteiltV P ws c → ∀ f Λ, c ∉ stabilS P S (lokW P fs ws) f Λ :=
    fun c h f Λ => geteiltV_nicht_stabil hvoll hA h f Λ
  have hTO : ∀ c, GeteiltV P ws c → ∀ L, c ∉ S.orte L :=
    fun c h L hL => h.1.2.1 L (hA.sperrOrte L c hL)
  have hlokK : ∀ c, lokW P fs ws c = true → GetrenntK P (kVon P fs init) c := fun c hc =>
    getrenntK_of hZ (by
      unfold lokW at hc
      exact @of_decide_eq_true _ (Classical.propDecidable _) hc)
  have hK := fun f => koerperGutSA_mono hT ((hN.1 passes f).1)
  have hex := startExklusiv_ohne_haelt init hLeer
  refine ⟨terminierung m Q S (kVon P fs init) (lokW P fs ws) sp init hH.1 hH.2.1 hH.2.2 hN.2.2 hS hvoll
      (fun t => hA.abg _) (fun t => reachB_wurzel P fs _) hTA hTV hTS hTO (fragX_ok hvoll hA.frag hA.fuss) hA.fuss
      hlokK hK hM hZ.req hZ.sperren hex hLm R h0 t, fun hk j ⟨l, Γ, Λ, ρ, r, hrest, hh⟩ => ?_⟩
  have h1 := ewigFrei_ohne_budget hvoll sp init R h0 t hk j
  rw [sigmaRest_lies (fun g => g.istEwig) hrest, restHalt_budget_ewig hh] at h1
  exact absurd h1 (by decide)

end Aus

/-- **GABBRO_ZIEL_TERMINIERUNG, proved.** -/
theorem gabbro_ziel_terminierung : GabbroZielTerminierung := by
  intro C D _ E fs ls cs hC hN passes m hM hLm O hH sp init hL lebt0 R0 hK0 t
  have hR0 : R0.alsGX.M 0 = RufStartG E.P.mitRuhe sp init := congrArg FadenMaschine.m hK0
  change (∃ N, ∀ j, N ≤ j → R0.alsGX.akt j ≠ some t) ∧
    ((∀ w, (init t).1 = some w → klasse E.P fs.1 m.hat w = .endet) →
      ∀ j, ¬ HaltBenannt O.mitRuhe passes (R0.alsGX.M j) .budget t)
  generalize R0.alsGX = R at hR0 ⊢
  have hA0 := C.korrekt E fs ls cs hC
  have hA := akzeptiertSpecX_mitRuhe E.P fs.2 hA0
  have hN' : LogikPflichtA E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q)
      (GeteiltA E.P.mitRuhe (wsRuhe E.ws)) := by
    have h := logikPflichtA_mitRuhe hN.logik
    exact ⟨fun passes f => ⟨koerperGutSA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA0.abg hc)
        (h.1 passes f).1,
      invGutSA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA0.abg hc) (h.1 passes f).2.1,
      invGutGrundA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA0.abg hc) (h.1 passes f).2.2⟩,
      h.2⟩
  have hH' := hardware_mitRuhe hH
  have hZ := startZulaessig_aus E fs.1 hN.start hL
  have heq := geteiltV_mitRuhe_eq E.P (ws := E.ws) fs.2 hA0.abg
  have hM' := massPflicht_mitRuhe fs.2 hA0.abg hM
  have hLm' : ∀ f' g', zykS E.P.mitRuhe (fsRuhe fs.1) f' g' = true →
      (m.mitRuhe f').length = (m.mitRuhe g').length := by
    intro f' g' hz
    cases f' with
    | none => rw [zykS_mitRuhe_ruhe] at hz; cases hz
    | some f =>
      cases g' with
      | none => rw [zykS_mitRuhe_zur_ruhe] at hz; cases hz
      | some g =>
        rw [zykS_mitRuhe E.P fs.2 hA0.abg] at hz
        rw [Mass.laenge_mitRuhe, Mass.laenge_mitRuhe]
        exact hLm f g hz
  revert hM' R
  rw [← heq]
  intro R hR0 hM'
  refine ⟨(terminierung_aus E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q) (fsRuhe_voll fs.2) (wsRuhe E.ws) hA hN'
    O.mitRuhe hH' passes sp init hZ m.mitRuhe hM' hLm' R hR0 t).1, fun hk => ?_⟩
  refine (terminierung_aus E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q) (fsRuhe_voll fs.2) (wsRuhe E.ws) hA hN'
    O.mitRuhe hH' passes sp init hZ m.mitRuhe hM' hLm' R hR0 t).2 ?_
  cases hi : (init t).1 with
  | none => exact ewigFrei_mitRuhe_ruhe E.P
  | some w => exact ewigFrei_mitRuhe E.P fs.2 hA0.abg (ewigFrei_klasse E.P fs.1 m.hat fs.2 (hk w hi))

end Gabbro.Grammatik.Zielsatz
