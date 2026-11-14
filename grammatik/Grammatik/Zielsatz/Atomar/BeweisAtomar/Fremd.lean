/- GABBRO_ZIEL WITH THE CALL-SITE DUTIES, PROVED (C08 R3b). The actual binding inhabits the body
   duties' conditional class (`axVertragOP_of_binding`), the call-site duty makes every question a
   run asks a question whose pre held (`antwortQLauf_of_callSite`), and the replay of `zielFX_rely`
   records exactly those answers. -/
module

public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Voll
public import Grammatik.Zielsatz.Kern.Spec.Fremd

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration}

/-- **GABBRO_ZIEL, PROVED.** -/
theorem gabbro_ziel : GabbroZiel := by
  intro C D _ E fs ls cs hC hN hCS hPD O hFV hH passes sp init hL lebt0 K hK
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
  have hQ0 : AxVertragOP (PreQ E.P) E.Q O := axVertragOP_of_binding hFV hPD hH.2.2.1
  have hQ1 : AxVertragOP (PreQ E.P.mitRuhe) (axEnsRuhe E.Q) O.mitRuhe := axVertragOP_mitRuhe hQ0
  have hR : ∀ n, RelyQ E.P.mitRuhe O.mitRuhe n (axEnsRuhe E.Q)
      (GeteiltV E.P.mitRuhe (wsRuhe E.ws)) (RufStartG E.P.mitRuhe sp init) := by
    intro n
    rw [heq]
    exact relyQ_of_callSite hQ1 (hCS O [] hH (foreignPflicht_nil_of_vertrag hFV) n sp init hL)
  have h := zielFX_rely E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q) (fsRuhe_voll fs.2) ls.2
    (wsRuhe E.ws) hA hN' O.mitRuhe (gutO_mitRuhe hH.1) (regLokal_mitRuhe hH.2.1) passes sp init hR
    (startZulaessig_aus E fs.1 hN.start hL) (ArenaOwnership.Ruhe.startOwn_arenen hL hBS) lebt0 K
    (heq ▸ hK)
  exact heq ▸ h

end Gabbro.Grammatik.Zielsatz

#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel
