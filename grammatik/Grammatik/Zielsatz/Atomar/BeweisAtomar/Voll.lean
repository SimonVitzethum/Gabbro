/- The goal theorems under the full summary premise (every foreign answer meets its
   declared summary at every question): `gabbro_ziel_voll` and `gabbro_ziel_leben`.
   The headline `gabbro_ziel` (call-site duties) is in `BeweisAtomar/Fremd.lean`. -/
module

public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration}

/-! ## The statements under the full summary premise -/

/-- **GABBRO_ZIEL_VOLL, PROVED**: the goal under the full summary premise (c). -/
theorem gabbro_ziel_voll : GabbroZielVoll := by
  intro C D _ E fs ls cs hC hN O hH passes sp init hL lebt0 K hK
  obtain ⟨hA0, hBS, _⟩ := C.korrekt E fs ls cs hH.2.2.2 hC
  have hA := akzeptiertSpecX_mitRuhe E.P fs.2 hA0
  have heq := geteiltV_mitRuhe_eq E.P (ws := E.ws) fs.2 hA0.abg
  have hN' : LogikPflichtA E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q)
      (GeteiltA E.P.mitRuhe (wsRuhe E.ws)) := by
    have h := logikPflichtA_mitRuhe hN.logik
    exact ⟨fun passes f => ⟨koerperGutSA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA0.abg hc)
        (h.1 passes f).1,
      invGutSA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA0.abg hc) (h.1 passes f).2.1,
      invGutGrundA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA0.abg hc) (h.1 passes f).2.2⟩,
      h.2⟩
  have h := zielFX_aus E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q) (fsRuhe_voll fs.2) ls.2
    (wsRuhe E.ws) hA hN' O.mitRuhe (hardware_mitRuhe hH) passes sp init
    (startZulaessig_aus E fs.1 hN.start hL) (ArenaOwnership.Ruhe.startOwn_arenen hL hBS) lebt0 K (heq ▸ hK)
  exact heq ▸ h

/-- **GABBRO_ZIEL_LEBEN, PROVED.** The reduction to `P.mitRuhe` as for `gabbro_ziel_voll`; every machine of the run is
    reached, so the goal theorem's facts hold at each of them (progress, lock exclusivity, the rank invariant), and
    `hungerfrei` applies. -/
theorem gabbro_ziel_leben : GabbroZielLeben := by
  intro C D _ E fs ls cs hC hN O hH passes sp init hL R hR0 hFair n t L hSp
  have hA0 := (C.korrekt E fs ls cs hH.2.2.2 hC).1
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
  have hND := startSpur_nodup_leer init hLeer
  have hr : ∀ n, RufErreichbarG E.P.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) (R.M n) :=
    R.toPlanLauf.erreichbar (hR0 ▸ RufErreichbarG.start)
  exact hungerfrei R hH'.1
    (fun n t => ⟨_, rangInvG_erreichbar hH'.1 hA.stufen sp init hND (hr n) t⟩)
    (fun n => exklusivG hH'.1 sp init (startExklusiv_ohne_haelt init hLeer) (hr n))
    (fun n => (zielX_aus E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q) (fsRuhe_voll fs.2) ls.2 (wsRuhe E.ws) hA hN'
      O.mitRuhe hH' passes sp init hZ (R.M n) (gx_aus_g_lauf (hr n))).fortschritt)
    hFair hSp


end Gabbro.Grammatik.Zielsatz
