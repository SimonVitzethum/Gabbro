/-
  Audit 25 / Geteilt.lean: demonstrations for read-only findings.

  This file imports only the audited slice plus its real dependency
  (Koernung reads Semantik). No existing file is modified.
-/
import Grammatik.Geteilt
import Grammatik.Marken

open Gabbro.Grammatik.Geteilt

namespace Audit25.Geteilt

/-! ## G1 (pattern b): owner mark premise of `eigner_ungeteilt_ein_faden` is never used.

    The proof is `geteilt_treu B fuel h c hmem hu f g hf hg`: the owner
    hypothesis `_hm : m \in W.eignerVon c` never appears. The theorem with the
    premise dropped is definitionally the old theorem. -/

theorem g1_owner_premise_unused (B : Bau) (W : OwnerAnfang) (fuel : Nat)
    (h : pruefeUngeteilt B fuel = true)
    (c : Carrier) (hmem : c ∈ B.traeger) (hu : B.geteilt c = false)
    (m : OwnerMarke) (_hm : m ∈ W.eignerVon c)
    (f g : Nat) (hf : ErreichtBau B fuel f c) (hg : ErreichtBau B fuel g c) :
    f = g :=
  -- The owner hypothesis `hm` is never named: this is `geteilt_treu`.
  geteilt_treu B fuel h c hmem hu f g hf hg

/-- Direct form: the conclusion follows without any owner premise. -/
theorem g1_direct (B : Bau) (fuel : Nat)
    (h : pruefeUngeteilt B fuel = true)
    (c : Carrier) (hmem : c ∈ B.traeger) (hu : B.geteilt c = false)
    (f g : Nat) (hf : ErreichtBau B fuel f c) (hg : ErreichtBau B fuel g c) :
    f = g :=
  geteilt_treu B fuel h c hmem hu f g hf hg

#check @eigner_ungeteilt_ein_faden
#check @g1_direct

/-! ## G2 (pattern b): existence premise of `eigner_erster_aus_anfang` is used
    only to discharge an impossible branch.

    `_hmE : \exists c, m \in W.eignerVon c` is consumed solely by
    `absurd _hmE (eigner_nie_in_welt ...)` on the produced-half branch.
    Consequence demonstrated: whenever the witness list's second half is
    empty, the conclusion holds with NO existence premise at all. -/

theorem g2_no_existence_needed (W : OwnerAnfang) (ruft : Fn → List Fn)
    (fuel : Nat) (e : Fn)
    (m : OwnerMarke)
    (hmem : m ∈ W.anfang e ++ weltErzeugt W ruft fuel e)
    (hempty : weltErzeugt W ruft fuel e = []) :
    m ∈ W.anfang e := by
  rw [hempty, List.append_nil] at hmem
  exact hmem

/-! ## G3 (pattern c): `carrierVonTab` / `carrierVonGlob` / `tabVonCarrier` /
    `globVonCarrier` are the identity, so `tabRundweg` and `globRundweg`
    are `rfl`-lemmas about `Nat = Nat`, and the "round-trip" says nothing
    about table/global separation (the header itself notes separation fails
    under these codes; `halvesDisjointForm` is stated, not proved). -/

/-- The fold is the identity function. -/
theorem g3_fold_is_id (t : TabCarrier) : carrierVonTab t = t := rfl

/-- The mirror is the identity function. -/
theorem g3_mirror_is_id (c : Carrier) : tabVonCarrier c = c := rfl

/-- Hence the "round-trip" is `t = t`. -/
theorem g3_roundtrip_is_refl (t : TabCarrier) :
    tabVonCarrier (carrierVonTab t) = t := rfl

/-- Separation is in general false under the identity codes:
    `[0]` as tables meets `[0]` as globals. -/
theorem g3_separation_fails :
    ¬ halvesDisjointForm [0] [0] := by
  intro h
  have := h 0 (by simp) 0 (by simp)
  exact this rfl

/-! ## G4 (pattern a/d): `lauf_hat_eintritt` and `nur_deklariert_teilt_lauf`
    restate the `BauLauf` hypothesis.

    `BauLauf B fuel l := coverage ∧ pairs`. `lauf_hat_eintritt` projects the
    first conjunct at `s`; `nur_deklariert_teilt_lauf` projects the second
    conjunct and discharges the same-thread case by contradiction. Both
    conclusions are the premise unfolded. Demonstrated: each follows from a
    direct projection with no extra content. -/

theorem g4_entry_is_projection (B : Bau) (fuel : Nat) (l : List SchrittC)
    (hl : BauLauf B fuel l) (s : SchrittC) (hs : s ∈ l) :
    ∃ e, B.eintritt[s.1]? = some e := by
  have hcov : ∀ s ∈ l, ErreichtBau B fuel s.1 s.2 := hl.1
  obtain ⟨e, _, he, _, _⟩ := hcov s hs
  exact ⟨e, he⟩

theorem g4_pairs_is_projection (B : Bau) (fuel : Nat) (l : List SchrittC)
    (hl : BauLauf B fuel l)
    (s₁ s₂ : SchrittC) (h₁ : s₁ ∈ l) (h₂ : s₂ ∈ l) (hfg : s₁.1 ≠ s₂.1) :
    (s₁.1, s₂.1) ∈ B.neben ∨ (s₂.1, s₁.1) ∈ B.neben := by
  have hpairs := hl.2
  rcases hpairs s₁ h₁ s₂ h₂ with h | h | h
  · exact absurd h hfg
  · exact Or.inl h
  · exact Or.inr h

/-! ## G5 (pattern a): `ungeteilt_aus_baulauf` / `ungeteilt_aus_lauf` /
    `ungeteilt_aus_bau` are `geteilt_treu` with the coverage premise
    pre-applied. The run hypotheses contribute only the two reachability
    witnesses; the "joint run" and "fold" layers add `congrArg` steps.
    Demonstrated: `ungeteilt_aus_baulauf` is `ungeteilt_aus_bau` on `hl.1`. -/

theorem g5_baulauf_is_bau (B : Bau) (fuel : Nat)
    (h : pruefeUngeteilt B fuel = true) (l : List SchrittC)
    (hl : BauLauf B fuel l)
    (c : Carrier) (hmem : c ∈ B.traeger) (hu : B.geteilt c = false)
    (s₁ s₂ : SchrittC) (h₁ : s₁ ∈ l) (h₂ : s₂ ∈ l)
    (hg : s₁.2 = s₂.2) (hc : s₁.2 = c) : s₁.1 = s₂.1 :=
  ungeteilt_aus_bau B fuel h l hl.1 c hmem hu s₁ s₂ h₁ h₂ hg hc

/-! ## G6 (pattern e, checked non-finding): the coverage premise
    `hdeck : ∀ s ∈ l, ErreichtBau B fuel s.1 s.2` is NOT vacuous for the
    speech-probe declaration: `miniB`'s own entry reaches its own carrier,
    so the premise is satisfiable. This records that §5's dynamic coverage
    is a genuine (stated) obligation, not a vacuity. -/

-- `ErreichtBau miniB 3 0 7` holds: entry 0 calls itself (refl) and writes 7.
theorem g6_coverage_satisfiable : ErreichtBau miniB 3 0 7 := by
  refine ⟨0, 0, rfl, ?_, by decide⟩
  exact RuftStarN.refl _ _

/-
CUTS:
- G1 VERIFIED below via #print axioms (proof uses only geteilt_treu; owner
  hypothesis unused). G2 demonstrated by g2 (branch-level use only).
- G3 VERIFIED by rfl-proofs plus the explicit separation counterexample.
- G4/G5 are structural restatements; demonstrated by projection proofs.
- G6 is a non-finding: coverage premise is satisfiable (checked above).
-/

#print axioms Audit25.Geteilt.g1_direct
#print axioms Audit25.Geteilt.g3_separation_fails
#print axioms Audit25.Geteilt.g6_coverage_satisfiable
