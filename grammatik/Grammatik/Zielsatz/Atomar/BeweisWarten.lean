/-
  File:      Grammatik/Zielsatz/Atomar/BeweisWarten.lean
  Subject:   THE PROOF OF `GabbroZielWarten` (2026-10-23): the waiting bound `wartezeit_schranke`
             (Logik/Fortschritt/Lebendigkeit.lean) from the four premise groups -- the goal theorem supplies its
             machine facts (no logic stop, every float range check passes, the lock ranks, exclusivity), the ticket
             lock its FIFO order (`fifoSperre_aus`); fairness window, hold time, no stop inside a section and the
             contenders are the statement's named premises.
-/
import Grammatik.Zielsatz.Atomar.BeweisAtomar
import Grammatik.Logik.Fortschritt.Lebendigkeit

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration}

section Aus

variable [DecidableEq D.Fn]

/-- **Every float range check passes at every machine GX reaches**, from the premise groups (as `zielX_aus`). -/
theorem bereich_aus (P : Programm D) (S : SperrInv D) (Q : AxEns D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (ws : List D.Fn)
    {B : List (ArenaOwnership.Body.ArenaIface D)} (hA : AkzeptiertSpecX P S fs ws B) (hN : LogikPflichtA P S Q (GeteiltA P ws)) (O : Orakel D)
    (hH : HardwareAnnahmen O Q) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hZ : StartZulaessig P S fs ws sp init)
    (M : RufMaschineG D) (hX : RufErreichbarGX P O passes (GeteiltV P ws) (RufStartG P sp init) M) :
    ∀ t, BereichG M t := by
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
  have hZI := zielInvSA_erreichbarGX P O passes Q S (kVon P fs init) (GeteiltV P ws) (lokW P fs ws)
    sp init hH.1 hH.2.1 hH.2.2 hN.2.2 hS hvoll (fun t => hA.abg _)
    (fun t => reachB_wurzel P fs _) hTA hTV hTS hTO (fragX_ok hvoll hA.frag hA.fuss) hA.fuss
    hlokK hK (fun f => massPflicht_aus P passes Q S (GeteiltV P ws) Mass.leer f) hZ.req hZ.sperren hex M hX
  exact fun t => fadenSA_bereich hH.1 hH.2.1 hH.2.2 hS hZ.sperren hK hA.fuss t (hZI.1.1 t)

end Aus

/-- **GABBRO_ZIEL_WARTEN, PROVED.** -/
theorem gabbro_ziel_warten : GabbroZielWarten := by
  intro C D _ E fs ls cs hC hN O hH passes sp init hL R F h k Ts hR0 hFair hHz hHw hAnw L t n0 hSp
  have hA0 := (C.korrekt E fs ls cs hC).1
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
  have hLeer : ∀ t, D.mitRuhe.haelt (init t).1 = [] := fun t => by
    rcases hZ.wurzel t with h | h
    · exact (hA.wurzeln _ h).1
    · exact h.1
  have hr : ∀ n, RufErreichbarG E.P.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) (R.M n) :=
    R.toPlanLauf.erreichbar (hR0 ▸ RufErreichbarG.start)
  exact wartezeit_schranke R.toPlanLauf hH'.1 hA.stufen sp init hLeer ls.2 (hR0 ▸ RufErreichbarG.start)
    (fun n => (zielX_aus E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q) (fsRuhe_voll fs.2) ls.2 (wsRuhe E.ws) hA hN'
      O.mitRuhe hH' passes sp init hZ (R.M n) (gx_aus_g_lauf (hr n))).keinLogikHalt)
    (fun n => bereich_aus E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q) (fsRuhe_voll fs.2) (wsRuhe E.ws) hA hN'
      O.mitRuhe hH' passes sp init hZ (R.M n) (gx_aus_g_lauf (hr n)))
    hA.antworten ⟨fifoSperre_aus R, hFair⟩ hHz hHw hAnw L t n0 hSp

end Gabbro.Grammatik.Zielsatz
