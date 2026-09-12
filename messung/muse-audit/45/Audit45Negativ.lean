-- Audit 45 probe E: negative controls on QLeer and BlattGegenbeispiel.
-- These are NOT findings: they confirm the wave-1 BUILD claims check out.
-- (E1) `qRequires_nowhere`/`qEnsures_nowhere` genuinely consume their
-- witnesses (no vacuity): instantiating the negated Q at the falsifying
-- values and computing by `rfl` reproduces the proofs.
-- (E2) `qensures_ist_slot` genuinely observes memory: flipping the slot
-- flips the Q, so the predicate is not constant on ordinary programs.
import Grammatik.QLeer
import Grammatik.BlattGegenbeispiel

namespace GabbroAudit45E

open Gabbro.Grammatik

-- E1: the requires witness computes to `false` by `rfl`, as the proof uses.
example : wahr? (eval (sig : World qD) (qP.requires qfn) sig rhoK0) = false :=
  rfl

-- E1: the ensures witness computes to `false` by `rfl`, as the proof uses.
example (sig : World qD) :
    wahr? (eval sig (qP.ensures qfn) sig
      (ergEnv (qD.erg qfn) vK6 rhoK0)) = false :=
  rfl

-- E2: the slot contract distinguishes `true`-slot from `false`-slot worlds.
example : Extraktion.QEnsures (D := BG.D1) BG.P1 ()
    (BG.weltB true []) :=
  (BG.qensures_ist_slot _).mpr rfl

example : ¬ Extraktion.QEnsures (D := BG.D1) BG.P1 ()
    (BG.weltB false []) := by
  intro hq
  have hs := (BG.qensures_ist_slot _).mp hq
  have hb : (BG.weltB false []).slots () 0 () = false := rfl
  rw [hb] at hs
  exact Bool.false_ne_true hs

#print axioms Gabbro.Grammatik.qRequires_nowhere
#print axioms Gabbro.Grammatik.BG.qensures_ist_slot

/-
CUTS:
- Pass-only probe: confirms the Q-falsity witnesses compute and the slot
  contract is memory-sensitive. No finding attached.
-/
