/-
  File:      Grammatik/Berechenbarkeit/AdmissionBoundary.lean
  Subject:   Preserve the existing termination admission while developing universality.

  The result is generic over actual Gabbro programs and their finite function lists.
  An unmeasured non-tail cycle anywhere in a start's call hull is rejected, not merely
  marked conditional. A universal stack implementation must discharge this obstruction
  rather than changing the classifier to accept it.
-/
import Grammatik.Berechenbarkeit.RecursionBoundary

namespace Gabbro.Grammatik.Berechenbarkeit.AdmissionBoundary

open Gabbro.Grammatik

/-- Every reachable unmeasured non-tail cycle makes the start's class `abgelehnt`. -/
theorem unmeasured_non_tail_rejected {D : Deklaration} [DecidableEq D.Fn]
    (P : Programm D) (fs : List D.Fn) (mass : D.Fn → Bool) (w f : D.Fn)
    (member : f ∈ fs) (reachable : reachB P fs w f = true)
    (cycle : imZyklus P fs f = true) (unmeasured : mass f = false)
    (nonTail : zyklusEndstaendig P fs f = false) :
    klasse P fs mass w = .abgelehnt := by
  have localRejected : lokal P fs mass f = .abgelehnt := by
    unfold lokal
    cases passOk P fs mass f <;> simp [cycle, unmeasured, nonTail]
  have lower := (klasse_foldl P fs mass w fs .endet).2 f member reachable
  change (lokal P fs mass f).rang ≤ (klasse P fs mass w).rang at lower
  rw [localRejected] at lower
  cases h : klasse P fs mass w <;> simp_all [TermKlasse.rang]

/-- Accepted conditional cycles must be tail cycles unless a measure is supplied. This
    is a necessary condition, not a claim that a measure-present flag proves descent. -/
theorem admitted_cycle_has_measure_or_tail {D : Deklaration} [DecidableEq D.Fn]
    (P : Programm D) (fs : List D.Fn) (mass : D.Fn → Bool) (w f : D.Fn)
    (member : f ∈ fs) (reachable : reachB P fs w f = true)
    (cycle : imZyklus P fs f = true) (admitted : klasse P fs mass w ≠ .abgelehnt) :
    mass f = true ∨ zyklusEndstaendig P fs f = true := by
  cases hm : mass f with
  | true => exact .inl rfl
  | false =>
      cases ht : zyklusEndstaendig P fs f with
      | true => exact .inr rfl
      | false => exact False.elim (admitted
          (unmeasured_non_tail_rejected P fs mass w f member reachable cycle hm ht))

open Gabbro.Grammatik.Zielsatz.BudgetZeuge Gabbro.Grammatik.Terminierung.KlasseZeuge

/-- The generic rejection theorem applies to the existing finite growing-stack program. -/
theorem rejection_zeuge : klasse RecursionBoundary.program [()] ohne () = .abgelehnt :=
  unmeasured_non_tail_rejected RecursionBoundary.program [()] ohne () ()
    (by simp) (by decide) (by decide) rfl (by decide)

/-- A real conditional tail cycle remains allowed; the rejection theorem does not ban
    conditional execution or strengthen the existing classifier. -/
theorem conditional_tail_zeuge :
    klasse (prog rEnd) [()] ohne () = .bedingt ∧
      zyklusEndstaendig (prog rEnd) [()] () = true := by decide

end Gabbro.Grammatik.Berechenbarkeit.AdmissionBoundary
