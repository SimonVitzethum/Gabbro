/-
  Audit 26, finding F8 -- Terminierung.lean: `retry_beschraenkt_antwortet`
  (line 180) proves `∃ o, laufMitTreibstoff step n s = o` by `⟨_, rfl⟩`.
  Pattern (a/c): the conclusion is reflexivity -- ANY function answers
  "something"; done vs out-of-fuel are not distinguished, so "bounded
  retry cannot hang" reads more than the Lean states (pattern (d) too:
  totality of a total function). This demo shows the degeneracy: the
  witness can be `none` (out of fuel) and the theorem still holds.
-/
import Grammatik.Terminierung

open Gabbro.Grammatik

/-- F8: the "answer" may be `none` -- out of fuel counts as answering. -/
example : ∃ o, laufMitTreibstoff (fun _ : Unit => some ()) 0 () = o :=
  retry_beschraenkt_antwortet _ _ _

/-- F8: pinpoint -- the fuel-0 run answers `none`, and that satisfies it. -/
example : laufMitTreibstoff (fun _ : Unit => some ()) 0 () = none := rfl

/-- F8: the same reflexivity for an ARBITRARY unrelated function. -/
theorem audit26_retry_answers_trivial {S : Type} (step : S → Option S)
    (n : Nat) (s : S) : ∃ o, laufMitTreibstoff step n s = o :=
  ⟨_, rfl⟩

#print axioms audit26_retry_answers_trivial

/-
CUTS:
  (C1) A real boundedness claim would say the loop answers DONE or names
       the exhaustion branch; this demo only shows the filed claim is `rfl`.
-/
