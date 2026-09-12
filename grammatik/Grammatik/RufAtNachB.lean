/-
  File:      Grammatik/RufAtNachB.lean
  Subject:   THE rufAt POSTCONDITION EQUIVALENCE (attempt B of 2).

  `VertragOrtB.lean` proves one direction (`rufAt_ok_of_gates`): ensures
  check true for the actual value ==> `rufAt` answers `.ok`. This file
  proves the equivalence: with the body OUTCOME as an equation
  (`execEnd ... = EndAusgang.zurueck σ1 v`), the requires gate open, and
  the invariant tail passing (all shapes shared with `rufAt_ok_of_gates`),
  `rufAt` answers `.logik (.nachbedingung f)` iff the ensures check for
  the actual `v` is false. A corollary: `rufAt` never answers
  `.logik (.nachbedingung f)` iff the ensures check holds.
-/
import Grammatik.VertragOrtB

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The unfolded call: one equation feeding both directions -/

/-- `rufAt` at a returned call is the ensures gate: with the requires gate
    open, the body returned, and the invariant tail passing, the outcome is
    the ensures `if` over the ACTUAL `v` (the value kept by the `hbody`
    equation -- never recovered from a bare `some` world). -/
theorem rufAt_fall_nach (P : Programm D) (O : Orakel D)
    (passes : Nat)
    (fuel : Nat) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f))
    (sread : World D)
    (hread : sread = σ.lese (Signatur.anfang D (D.signatur f))
      (P.requires f).orte)
    (hreq : wahr? (eval sread (P.requires f) sread ρ) = true)
    (σ1 : World D) (v : ErgVal D (D.erg f))
    (hbody : execEnd (V := vertragVon D f) O passes (rufAt P O passes fuel)
      (P.rumpf f) sread ρ = EndAusgang.zurueck σ1 v)
    (sret : World D)
    (hret : sret = σ1.lese (vertragVon D f).ende (P.ensures f).orte)
    (sinv : World D)
    (hsinv : sinv = (D.invs.filter (schuldet f)).foldl
      (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) sret)
    (hinv : D.invs.find? (fun i => schuldet f i &&
      !wahr? (eval sinv (P.invariante i) sinv .nil)) = none) :
    rufAt P O passes (fuel + 1) f σ ρ =
      (if wahr? (eval sread (P.ensures f) sret (ergEnv (D.erg f) v ρ)) = false
        then RufAusgang.logik (D := D) (.nachbedingung f)
        else RufAusgang.ok (D := D) (f := f) sinv v) := by
  have hgate : ¬ (wahr? (eval sread (P.requires f) sread ρ) = false) := by
    rw [hreq]; decide
  simp only [rufAt, ← hread, ← hret, ← hsinv, hbody, hinv, if_neg hgate]

/-! ## CUTS
  - Skeleton: only the unfolded equation so far; the iff and the
    never-corollary are not yet stated.
-/

#print axioms Gabbro.Grammatik.rufAt_fall_nach

end Gabbro.Grammatik
