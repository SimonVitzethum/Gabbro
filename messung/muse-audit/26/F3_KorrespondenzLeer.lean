/-
  Audit 26, finding F3 -- Erhaltung.lean: `korrespondenz_leer` (line 615)
  proves `satz_korrespondenz [] ⟨[]⟩` vacuously: all four conjuncts quantify
  over empty lists. The demo restates it minimally: every leg holds because
  there is nothing to check. The header calls it "vacuously"; the finding
  is that the correspondence sentence is satisfiable by the EMPTY
  certificate for the EMPTY run, so it cannot distinguish "checked" from
  "nothing happened".
-/
import Grammatik.Erhaltung

open Gabbro.Grammatik

/-- F3: the empty certificate satisfies completeness (nothing owed). -/
example : corrComplete ([] : List Nat) ⟨[]⟩ := by
  intro g hg
  exact False.elim (List.not_mem_nil hg)

/-- F3: the empty certificate satisfies no-extra (nothing claimed). -/
example : corrNoExtra ([] : List Nat) ⟨[]⟩ := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)

/-- F3: the full vacuous correspondence, as stated. -/
theorem audit26_korrespondenz_leer_vacuous :
    satz_korrespondenz [] ⟨[]⟩ :=
  korrespondenz_leer

#print axioms audit26_korrespondenz_leer_vacuous

/-
CUTS:
  (C1) Whether the sentence SHOULD exclude the empty cert is a contract
       question; this demo only shows the vacuity.
-/
