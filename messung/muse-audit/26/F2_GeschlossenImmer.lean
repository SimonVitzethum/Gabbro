/-
  Audit 26, finding F2 -- Erhaltung.lean: `geschlossen_immer` (line 555)
  derives `corrClosed` for EVERY certificate, but only over the NAMED-form
  closure predicate (`exists s, .benannt f s in tafel`). The moment a
  certificate row carries a form outside the 19 named shapes -- which any
  real image after `tafelNeu` admits (e.g. `logUndOder` content) -- the
  predicate is not even statable. The demo: `geschlossen_immer` fires on an
  arbitrary cert BECAUSE `ruledB_voll` proves every CForm is named-tabled;
  the closedness is over a predicate that ranges over the named fragment
  only, so it cannot see a 30-slot census form.
-/
import Grammatik.Erhaltung

open Gabbro.Grammatik

/-- F2: closure holds for a cert whose rows are all `.literal` -- trivially. -/
example : corrClosed ⟨[{gabbroSite := 0, cSite := 99, form := .literal}]
    ⟩ (fun f => ∃ s : RulingStatus, .benannt f s ∈ tafel ∧ entschieden (.benannt f s)) :=
  geschlossen_immer _

/-- F2: `ruledB_voll` -- every CForm passes the NAMED check, so the check
    cannot distinguish census forms from named ones; there is no census
    arm in `ruledB` at all (its `.luecke` arm is `false`). -/
theorem audit26_ruledB_luecke_arm (f : CForm) : ruledB f = true :=
  ruledB_voll f

/-- F2: the `.luecke` arm of the recomputation is constantly `false`. -/
example : (fun e => match e with
    | EntscheidZiel.benannt g _ => decide (g = CForm.literal)
    | EntscheidZiel.luecke _ _ => false)
    (EntscheidZiel.luecke .bedingt .offen) = false := rfl

#print axioms audit26_ruledB_luecke_arm

/-
CUTS:
  (C1) Whether closure SHOULD range over census slots is a contract
       question; this demo only shows the current predicate cannot.
-/
