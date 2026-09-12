-- Audit 45 probe C: `rueck_ohne_nachbedingung` conclusion restates a premise.
-- Pattern (a): the first conjunct of the conclusion is `RufEnsCheck ...`,
-- which is exactly the premise `hens_pos` (same arguments). The proof is
-- `refine <hens_pos, ?_>`; the second conjunct is `.ok != .logik`
-- discrimination from `hruf` alone. `hens_pos` is used only to re-emit it.
-- Demonstration: the same conclusion shape follows with the ensures check
-- supplied ONLY as the conclusion's own first conjunct source, and the
-- no-`nachbedingung` half needs no ensures premise at all.
import Grammatik.VertragOrtB

namespace GabbroAudit45C

open Gabbro.Grammatik

-- The ensures half of the conclusion needs no `rufAt` reasoning: it is
-- the premise handed back. Isolate that step.
example (P : Programm D) (f : D.Fn) (s0 s1 : World D)
    (rho : Env D (D.params f)) (v : ErgVal D (D.erg f))
    (hens_pos : RufEnsCheck P f s0 s1 rho v) :
    RufEnsCheck P f s0 s1 rho v :=
  hens_pos

-- The discrimination half needs only the `.ok` equation, no ensures check:
-- an `.ok` outcome is never `.logik`, for ANY ensures-side whatever.
example (P : Programm D) (O : Orakel D) (passes : Nat)
    (fuel : Nat) (f : D.Fn) (sigma : World D) (rho : Env D (D.params f))
    (sinv : World D) (v : ErgVal D (D.erg f))
    (hruf : rufAt P O passes (fuel + 1) f sigma rho =
      RufAusgang.ok (D := D) (f := f) sinv v) :
    (∀ e : Logik D, e = .nachbedingung f →
      rufAt P O passes (fuel + 1) f sigma rho ≠ .logik e) := by
  intro e he hcon
  rw [hruf] at hcon
  exact absurd hcon (by cases he <;> simp)

#print axioms Gabbro.Grammatik.rueck_ohne_nachbedingung

/-
CUTS:
- No claim the theorem is false; both conjuncts are true. The audit point
  is pattern (a): the ensures conjunct is `hens_pos` restated, so the
  "bridge" between return event and `rufAt` carries no ensures content
  beyond echoing its own premise (the `rufAt` equation `hruf` is what
  excludes `.logik`, and it already presupposes the ensures check via
  `rufAt_ok_of_gates`).
-/
