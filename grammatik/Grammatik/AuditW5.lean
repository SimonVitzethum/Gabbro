/-
  File:      Grammatik/AuditW5.lean
  Subject:   Wave 4-5 audit: vacuity probes and counter-lemmas (lane 122).

  Read-and-probe lane. For each wave 4-5 main theorem the full premise
  table lives in MUSE-REPORT-122.md; this file carries only the proved
  counter-lemmas backing the "no" rows.
-/
import Grammatik.VertragsFuss
import Grammatik.Profil

namespace Gabbro.Grammatik

/-- Counter-lemma A (VertragsFuss): the joint checker premise of the four
    `hReqTAll_aus_B` / `hReqGAll_aus_B` / `hEnsTAll_aus_B` / `hEnsGAll_aus_B`
    theorems is false on the reference fixture itself. `lies` ensures
    `result = konto[0]` (footprint `[.inl ()]`) while its write signature
    is empty, so `vertragFussB refP refLies = false` by computation. -/
theorem fussB_all_falsch :
    (∀ f : refD.Fn, vertragFussB refP f = true) → False := by
  intro h
  have hL := h refLies
  rw [vertragFussB_refLies_falsch] at hL
  exact absurd hL Bool.false_ne_true

/-- Counter-lemma B (Profil): the `hkey` premise of `profil_modell`
    (`∀ a ∈ P, ∃ k v, istModus a k v`) is unsatisfiable for any profile
    containing a free-prose (`frei`) entry -- no `frei` entry is a `modus`
    entry. Profiles with free assumptions cannot use `profil_modell`;
    the `_zeuge` companion covers keyed-only profiles. -/
theorem hkey_schliesst_frei_aus {D : Deklaration} (P : Profil D)
    (n c : String) (p : World D → Prop)
    (hmem : AnnahmeEintrag.frei (D := D) n c p ∈ P)
    (hkey : ∀ a ∈ P, ∃ k v, istModus (D := D) a k v) : False := by
  obtain ⟨k, v, hn, hc, heq⟩ := hkey _ hmem
  cases heq

/-
CUTS:
  - The audit table (MUSE-REPORT-122.md) classifies every wave 4-5 main
    theorem; only the rows backed by proved lemmas above are claimed here.
  - No witness for the audited theorems is (re-)proved here; existing
    `_zeuge` companions are reviewed in the report, not re-derived.
-/

#print axioms Gabbro.Grammatik.fussB_all_falsch
#print axioms Gabbro.Grammatik.hkey_schliesst_frei_aus
