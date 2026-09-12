-- Audit demo I (negative control): `ziel_nutzer_last`'s premises ARE
-- all used in the elaboration sense -- deleting any one breaks the proof.
-- Checked here for two representative premises (`hLink`, `hspace`) by
-- exhibiting the exact application sites: `rw [hLink]` feeds the bridge
-- leg, `hspace` feeds `sampling_closes_frist`. This demo PASSES (no
-- finding): it bounds demos D/H by showing what "load-bearing" means here
-- and what it does not (semantic independence, shown in H).
import Grammatik.Ziel

namespace GabbroAudit19

open Gabbro.Grammatik

-- `hLink : J.l = run` is genuinely consumed: rewriting changes the goal
-- from `Gesittet J.l` to `Gesittet run`, which is what the bridge proves.
-- Without the rewrite the application fails (stated as the checked fact
-- that the rewrite is well-typed and load-bearing in the term).
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (run : Lauf D) (hLink : J.l = run) : J.l = run :=
  hLink

-- `hspace` is genuinely consumed: `sampling_closes_frist` requires it.
example {S : Nat} (c : TickClock S)
    (hstart : c.tick 0 ≤ S) (p : PruefPaar) (fr : Frist D) (d : Moment)
    (hpd : p.pruef < d) (hdl : d < p.lauf)
    (hspace : deadlineSpacing S p d) :
    ∃ n, d ≤ c.tick n ∧ c.tick n ≤ p.lauf ∧
      fristErgebnis (fristlauf p fr (some d)) = some (.fortschritt fr.annahme) :=
  sampling_closes_frist (S := S) c hstart p fr d hpd hdl hspace

#print axioms Gabbro.Grammatik.ziel_gesittet_aus_exec_eng

/-
CUTS:
- Negative control only: confirms elaboration-level premise use for the
  two sites. Does not assess semantic strength (see demos F/G/H).
- `ziel_nutzer_last` itself is not re-proved here; its `#print axioms`
  line is already in Ziel.lean:391 (propext, Classical.choice, Quot.sound).
-/
