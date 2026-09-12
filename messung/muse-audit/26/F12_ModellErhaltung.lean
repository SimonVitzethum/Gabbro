/-
  Audit 26, finding F12 -- Budget.lean: `modell_erhaltung` (line 681)
  concludes `(∃ _ : Expr D Γ Λ (.int lo hi), True) ∧
  senkKosten c ≤ absenkung.proPrimitiv`. Pattern (a): the first conjunct
  is `zeugnis_sound c lo hi hval` verbatim (meaning leg reused, honestly
  labelled), and the second is `senkKosten_unter_schranke` (count leg:
  `senkKosten c = 1 ≤ 17` by the two filed lemmas). The "preservation"
  header therefore conjoins two facts that share only the hypothesis
  `hmod`; no interaction between meaning and count is proved (the count
  does not depend on validity). This demo shows the count leg needs no
  validity at all.
-/
import Grammatik.Budget

open Gabbro.Grammatik

/-- F12: the count leg holds without any certificate validity. -/
theorem audit26_count_needs_no_validity {D : Deklaration} (c : CertExpr D)
    (hmod : modellKopf c = true) :
    senkKosten c ≤ absenkung.proPrimitiv :=
  senkKosten_unter_schranke c hmod

/-- F12: the meaning leg is exactly `zeugnis_sound`. -/
theorem audit26_meaning_is_zeugnis {D : Deklaration} {Γ : Ctx}
    {Λ : List (Res D)} (c : CertExpr D) (lo hi : Int)
    (hval : GueltigAbleitung D Γ Λ c lo hi) :
    (∃ _ : Expr D Γ Λ (.int lo hi), True) :=
  zeugnis_sound c lo hi hval

#print axioms audit26_count_needs_no_validity
#print axioms audit26_meaning_is_zeugnis

/-
CUTS:
  (C1) Whether preservation SHOULD link meaning and count (e.g. the
       lowered op computes the same value) is the booked follow-up in
       the section header; this demo only shows the filed conjunction
       proves no such link.
-/
