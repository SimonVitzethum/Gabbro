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

/-! ## 2. The postcondition equivalence -/

/-- THE `rufAt` POSTCONDITION EQUIVALENCE: with the body outcome given as an
    equation (`hbody` keeps the actual value `v` -- a bare `some` world
    would lose it, which was attempt A's failure), the requires gate open,
    and the invariant tail passing, `rufAt` answers
    `.logik (.nachbedingung f)` iff the ensures check for the ACTUAL `v`
    is false. Both directions unfold `rufAt` through `rufAt_fall_nach`
    (which unfolds exactly as `rufAt_ok_of_gates` does); every gate
    premise feeds that rewrite, and the discrimination between the `.logik`
    and `.ok` constructors closes the false branches. -/
theorem rufAt_nachbedingung_iff_ensFalsch (P : Programm D) (O : Orakel D)
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
        RufAusgang.logik (D := D) (.nachbedingung f) ↔
      wahr? (eval sread (P.ensures f) sret (ergEnv (D.erg f) v ρ)) = false := by
  have hfall := rufAt_fall_nach P O passes fuel f σ ρ sread hread hreq
    σ1 v hbody sret hret sinv hsinv hinv
  rw [hfall]
  constructor
  · intro h
    by_cases hc : wahr? (eval sread (P.ensures f) sret
        (ergEnv (D.erg f) v ρ)) = false
    · exact hc
    · rw [if_neg hc] at h
      cases h
  · intro h
    rw [if_pos h]

/-! ## 3. The never-corollary -/

/-- `rufAt` never answers `.logik (.nachbedingung f)` iff the ensures check
    holds for the actual `v` (same gate/body/tail shapes as the iff). The
    check is named through `RufEnsCheck` from `VertragOrtB` (imported, not
    duplicated); the `≠`-side is the negation of the iff's left side and
    the `RufEnsCheck`-side the negation of its right side, closed by the
    same unfolding. -/
theorem rufAt_nie_nachbedingung_iff_ens (P : Programm D) (O : Orakel D)
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
    rufAt P O passes (fuel + 1) f σ ρ ≠
        RufAusgang.logik (D := D) (.nachbedingung f) ↔
      RufEnsCheck P f sread sret ρ v := by
  have hiff := rufAt_nachbedingung_iff_ensFalsch P O passes fuel f σ ρ sread
    hread hreq σ1 v hbody sret hret sinv hsinv hinv
  unfold RufEnsCheck
  constructor
  · intro hne
    by_cases hc : wahr? (eval sread (P.ensures f) sret
        (ergEnv (D.erg f) v ρ)) = false
    · exact absurd (hiff.mpr hc) hne
    · cases heq : wahr? (eval sread (P.ensures f) sret
        (ergEnv (D.erg f) v ρ)) with
      | true => rfl
      | false => exact absurd heq hc
  · intro htrue hlogik
    have hfalse := hiff.mp hlogik
    rw [htrue] at hfalse
    cases hfalse

/-! ## CUTS
  - Scope: the returned-body case only (`hbody` pins the `.zurueck` outcome).
    Non-returning bodies (`.grund`, `.logik`, `.hardware`) are excluded by
    the `hbody` equation, not by a premise left unused: `rufAt` forwards
    those outcomes unchanged (no postcondition gate), so no equivalence of
    this shape holds for them.
  - Worlds change: the body outcome world comes from `execEnd` (which can
    change memory via `execStmt`), and the read worlds `sread`/`sret`/`sinv`
    come from `World.lese`; no world here is invented.
-/

#print axioms Gabbro.Grammatik.rufAt_fall_nach
#print axioms Gabbro.Grammatik.rufAt_nachbedingung_iff_ensFalsch
#print axioms Gabbro.Grammatik.rufAt_nie_nachbedingung_iff_ens

end Gabbro.Grammatik
