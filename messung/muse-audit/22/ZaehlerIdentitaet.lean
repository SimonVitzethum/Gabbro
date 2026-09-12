import Grammatik.Maschine

open Gabbro.Grammatik

-- Finding 1 (pattern a): zaehler_zeigt_atom concludes its own premise.
-- Its conclusion `(prog f)[pc f]? = some (PCAtom.leaf Λ cs₀)` is `hpc` with
-- `hΛa : Λa = Λ` and `hcs : cs = cs₀` substituted -- the proof is just the rewrite.
-- Demonstration: the theorem is interchangeable with a bare substitution instance.
example (prog : PCProg D) (f : Faden) (pc : PCStand)
    (Λ : List (Res D)) (cs₀ : List (D.Tab ⊕ D.Glob))
    (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hpc : (prog f)[pc f]? = some (PCAtom.leaf Λa cs))
    (hΛa : Λa = Λ) (hcs : cs = cs₀) :
    (prog f)[pc f]? = some (PCAtom.leaf Λ cs₀) :=
  -- No use of PCSchritt, PCReach, execStmt, or any machine fact: pure substitution.
  zaehler_zeigt_atom prog f pc Λ cs₀ Λa cs hpc hΛa hcs

-- Companion: the "discharge corollary" is the constructor direction of the same
-- substitution, i.e. packing the conclusion back into an existential. The two
-- together form a rewrite round-trip, not scheduler content.
example (prog : PCProg D) (f : Faden) (pc : PCStand)
    (Λ : List (Res D)) (cs₀ : List (D.Tab ⊕ D.Glob))
    (hident : (prog f)[pc f]? = some (PCAtom.leaf Λ cs₀)) :
    ∃ Λa : List (Res D), ∃ cs : List (D.Tab ⊕ D.Glob),
      (prog f)[pc f]? = some (PCAtom.leaf Λa cs) ∧ Λa = Λ ∧ cs = cs₀ :=
  hpc_hΛa_hcs_aus_zaehler prog f pc Λ cs₀ hident

-- Round-trip witness: composing the two recovers the input, showing that
-- §15 states one propositional identity twice (unpack then repack).
example (prog : PCProg D) (f : Faden) (pc : PCStand)
    (Λ : List (Res D)) (cs₀ : List (D.Tab ⊕ D.Glob))
    (hident : (prog f)[pc f]? = some (PCAtom.leaf Λ cs₀)) :
    (prog f)[pc f]? = some (PCAtom.leaf Λ cs₀) := by
  obtain ⟨Λa, cs, hpc, hΛa, hcs⟩ :=
    hpc_hΛa_hcs_aus_zaehler prog f pc Λ cs₀ hident
  exact zaehler_zeigt_atom prog f pc Λ cs₀ Λa cs hpc hΛa hcs

#print axioms zaehler_zeigt_atom
#print axioms hpc_hΛa_hcs_aus_zaehler

/-!
CUTS:
- No claim about which atom the counter SHOULD point at is checked here;
  that is the S12 remainder booked in the section header.
-/
