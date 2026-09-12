/-
  Audit 26, finding F9 -- Terminierung.lean: `traverse_fallend_terminiert`,
  `traverse_verbrauchend_terminiert`, `rekursion_mass_terminiert`
  (lines 155-175) are the SAME theorem as `mass_faellt_schranke`
  (line 128) with renamed binders (`mass`/`umfang`, `hfall`/`hschwund`).
  Pattern (a): conclusion equal to a premise theorem modulo renaming.
  The file header is honest ("honestly the same argument, which is the
  point"), so severity is low -- but the three names look like three
  results (traverse/by-consuming/recursion) while the falling premise
  (the writer's logic, C2) is assumed in each. This demo shows the
  definitional identity.
-/
import Grammatik.Terminierung

open Gabbro.Grammatik

/-- F9: `traverse_fallend_terminiert` IS `mass_faellt_schranke`. -/
theorem audit26_fallend_is_schranke {S : Type} (step : S → Option S)
    (mass : S → Nat)
    (hfall : ∀ s s', step s = some s' → mass s' < mass s) (s : S) :
    ∃ s', laufMitTreibstoff step (mass s + 1) s = some s' :=
  traverse_fallend_terminiert step mass hfall s

/-- F9: `traverse_verbrauchend_terminiert` IS `mass_faellt_schranke`. -/
theorem audit26_verbrauchend_is_schranke {S : Type} (step : S → Option S)
    (umfang : S → Nat)
    (hschwund : ∀ s s', step s = some s' → umfang s' < umfang s) (s : S) :
    ∃ s', laufMitTreibstoff step (umfang s + 1) s = some s' :=
  traverse_verbrauchend_terminiert step umfang hschwund s

/-- F9: `rekursion_mass_terminiert` IS `mass_faellt_schranke`. -/
theorem audit26_rekursion_is_schranke {S : Type} (step : S → Option S)
    (mass : S → Nat)
    (hfall : ∀ s s', step s = some s' → mass s' < mass s) (s : S) :
    ∃ s', laufMitTreibstoff step (mass s + 1) s = some s' :=
  rekursion_mass_terminiert step mass hfall s

#print axioms audit26_fallend_is_schranke
#print axioms audit26_verbrauchend_is_schranke
#print axioms audit26_rekursion_is_schranke

/-
CUTS:
  (C1) The file books the falling premise as the writer's logic (C2), so
       this is counted as honest duplication, not hidden vacuity.
-/
