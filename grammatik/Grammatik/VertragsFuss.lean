/-
  File:      Grammatik/VertragsFuss.lean
  Subject:   D7 -- contract footprint containment by computation.

  The goal theorem owes four footprint premises (`Ziel.lean`: `hReqTAll`,
  `hReqGAll`, `hEnsTAll`, `hEnsGAll`): every carrier read by `requires` /
  `ensures` lies in the function's write signature. This file turns them
  into checker facts: `vertragFussB` decides the containment from the
  contract syntax, and the four `aus_B` theorems recover the exact
  `Ziel.lean` shapes from a positive check.
-/
import Grammatik.InterferenzAllgemein
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- One carrier covered by the write signature of `f`. -/
def fussDeckt (f : D.Fn) (o : D.Tab ⊕ D.Glob) : Bool :=
  match o with
  | .inl t => D.schreibt f t
  | .inr x => D.gschreibt f x

/-- Checker predicate: every carrier read by `requires` / `ensures` of `f`
    lies in the write signature of `f`. -/
def vertragFussB (P : Programm D) (f : D.Fn) : Bool :=
  ((P.requires f).orte.all (fussDeckt f)) &&
    ((P.ensures f).orte.all (fussDeckt f))

/-- The `requires` leg of a positive check, tables and globals jointly. -/
theorem vertragFussB_req (P : Programm D) (f : D.Fn)
    (h : vertragFussB P f = true) :
    (∀ t : D.Tab, .inl t ∈ (P.requires f).orte → D.schreibt f t = true) ∧
      (∀ x : D.Glob, .inr x ∈ (P.requires f).orte → D.gschreibt f x = true) := by
  have hReq : ((P.requires f).orte.all (fussDeckt f)) = true := by
    simp only [vertragFussB] at h
    rw [Bool.and_eq_true] at h
    exact h.1
  have hall := List.all_eq_true.mp hReq
  constructor
  · intro t hmem
    have hp := hall _ hmem
    simp only [fussDeckt] at hp
    simpa using hp
  · intro x hmem
    have hp := hall _ hmem
    simp only [fussDeckt] at hp
    simpa using hp

/-- The `ensures` leg of a positive check, tables and globals jointly. -/
theorem vertragFussB_ens (P : Programm D) (f : D.Fn)
    (h : vertragFussB P f = true) :
    (∀ t : D.Tab, .inl t ∈ (P.ensures f).orte → D.schreibt f t = true) ∧
      (∀ x : D.Glob, .inr x ∈ (P.ensures f).orte → D.gschreibt f x = true) := by
  have hEns : ((P.ensures f).orte.all (fussDeckt f)) = true := by
    simp only [vertragFussB] at h
    rw [Bool.and_eq_true] at h
    exact h.2
  have hall := List.all_eq_true.mp hEns
  constructor
  · intro t hmem
    have hp := hall _ hmem
    simp only [fussDeckt] at hp
    simpa using hp
  · intro x hmem
    have hp := hall _ hmem
    simp only [fussDeckt] at hp
    simpa using hp

/-- `hReqTAll` (`Ziel.lean`) from a positive check on every function. -/
theorem hReqTAll_aus_B (P : Programm D) (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (hB : ∀ f, vertragFussB P f = true) :
    ∀ (g : Faden), g ∈ J.faeden → ∀ t : D.Tab,
      .inl t ∈ (P.requires (J.code g)).orte →
        D.schreibt (J.code g) t = true := by
  intro g _ t hmem
  exact (vertragFussB_req P (J.code g) (hB (J.code g))).1 t hmem

/-- `hReqGAll` (`Ziel.lean`) from a positive check on every function. -/
theorem hReqGAll_aus_B (P : Programm D) (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (hB : ∀ f, vertragFussB P f = true) :
    ∀ (g : Faden), g ∈ J.faeden → ∀ x : D.Glob,
      .inr x ∈ (P.requires (J.code g)).orte →
        D.gschreibt (J.code g) x = true := by
  intro g _ x hmem
  exact (vertragFussB_req P (J.code g) (hB (J.code g))).2 x hmem

/-- `hEnsTAll` (`Ziel.lean`) from a positive check on every function. -/
theorem hEnsTAll_aus_B (P : Programm D) (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (hB : ∀ f, vertragFussB P f = true) :
    ∀ (g : Faden), g ∈ J.faeden → ∀ t : D.Tab,
      .inl t ∈ (P.ensures (J.code g)).orte →
        D.schreibt (J.code g) t = true := by
  intro g _ t hmem
  exact (vertragFussB_ens P (J.code g) (hB (J.code g))).1 t hmem

/-- `hEnsGAll` (`Ziel.lean`) from a positive check on every function. -/
theorem hEnsGAll_aus_B (P : Programm D) (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (hB : ∀ f, vertragFussB P f = true) :
    ∀ (g : Faden), g ∈ J.faeden → ∀ x : D.Glob,
      .inr x ∈ (P.ensures (J.code g)).orte →
        D.gschreibt (J.code g) x = true := by
  intro g _ x hmem
  exact (vertragFussB_ens P (J.code g) (hB (J.code g))).2 x hmem

/-- Positive evidence: `einzahlen` passes the check (`requires` is `true`,
    `ensures` reads only the written table). -/
theorem vertragFussB_refEin : vertragFussB refP refEin = true := by
  decide

/-- The rule-13 witness for `hReqTAll_aus_B` fails on `refP`, by computation:
    `lies` ensures `result = konto[0]` but writes nothing, so the joint premise
    `∀ f, vertragFussB refP f = true` is false. This is booked in CUTS. -/
theorem vertragFussB_refLies_falsch : vertragFussB refP refLies = false := by
  decide

end Gabbro.Grammatik

/-! ## CUTS:
  - No `hReqTAll_aus_B_zeuge` on `refP`: the joint premise
    `∀ f, vertragFussB refP f = true` is unprovable because
    `vertragFussB refP refLies = false` (`vertragFussB_refLies_falsch`, by
    `decide`). The read-only function `lies` ensures `result = konto[0]`
    (`refEnsLies`, footprint `[.inl ()]`) while its write signature is empty
    (`refSigLies.schreibt = fun _ => false`). So write-signature containment
    as stated excludes ordinary read contracts; the checker rule that would
    enforce it would reject the reference fixture itself. Per rule 13 this is
    a finding, not a weakened witness: no `_zeuge` companion is claimed.
  - The Rust checker does not enforce the containment either: `wirkungen.rs`
    collects expression reads (`liest`) but never mentions `requires` /
    `ensures` (zero hits), and footprints (`bau.rs`: `fussAus`) come from the
    declared `writes` effects only. Smallest rule that would: refuse a
    function whose `requires` / `ensures` reads a carrier outside its
    declared write effects (no number assigned; this lane adds none).
-/

#print axioms Gabbro.Grammatik.fussDeckt
#print axioms Gabbro.Grammatik.vertragFussB
#print axioms Gabbro.Grammatik.vertragFussB_req
#print axioms Gabbro.Grammatik.vertragFussB_ens
#print axioms Gabbro.Grammatik.hReqTAll_aus_B
#print axioms Gabbro.Grammatik.hReqGAll_aus_B
#print axioms Gabbro.Grammatik.hEnsTAll_aus_B
#print axioms Gabbro.Grammatik.hEnsGAll_aus_B
#print axioms Gabbro.Grammatik.vertragFussB_refEin
#print axioms Gabbro.Grammatik.vertragFussB_refLies_falsch
