/-
  File:      Grammatik/X86/HwKapsteinTsoIsaAddr.lean
  Subject:   TSO projection of the isa, addr and muldiv union tags.

  Lane 1327: every classified union step of `HwKapsteinTso` (lane 1295)
  projects to the TSO store-buffer model; isa/addr/muldiv were left as
  FINDINGs there. This file classifies exactly those three tags over
  the reused projection `kapTso` (never redefined): isa register steps
  are silent, isa loads observe with forwarding, isa stores are single
  `issueByte` events; muldiv steps are silent (register-only); addr
  stores are folds of byte issues (`concIssue` over `entriesOf`) and
  addr loads are silent forwarding observations. Widths 1/2/4/8 bytes;
  a split across a group boundary stays the accepted tearing refusal.
  Every accepted definition is reused unchanged, never redefined.
-/
import Grammatik.X86.HwKapsteinTso

namespace Gabbro.Grammatik.X86

/-- Re-embedded ISA successors leave the TSO projection unchanged:
    only core data moves, never memory or buffers. -/
theorem kapTso_setKernVonZustand (m : HwMaschine) (c : Nat)
    (s' : Zustand) :
    kapTso (setKernVonZustand m c s') = kapTso m := by
  rfl

/-! ## 1. ISA tag: register steps are silent, loads observe,
    stores issue one byte. -/

/-- Every ISA adapter step classifies on the TSO projection with its
    footprint named: register steps are silent (only core data moves),
    loads observe with forwarding (`loadByte`, both the observed and
    the demanded value named), stores are single `issueByte` events. -/
theorem kap_isa_tso_klass (m m' : HwMaschine) (c : Nat)
    (e : IsaEreignis)
    (h : adapterIsa.schritt m c e = some m') :
    (∃ d s', e = .reg d ∧ stepI d (projZustand m c) = some s'
      ∧ m' = setKernVonZustand m c s' ∧ kapTso m' = kapTso m)
    ∨ (∃ a v w, e = .lade a v ∧ kapTso m' = kapTso m
      ∧ loadByte (kapTso m) c a = some w ∧ (w == v) = true)
    ∨ (∃ a v s', e = .gibAus a v
      ∧ issueByte (kapTso m) c a v = some s' ∧ kapTso m' = s') := by
  cases e with
  | reg d =>
    cases hstep : stepI d (projZustand m c) with
    | some s' =>
      cases hg : isaNurRegister d.instr with
      | true =>
        have he := adapterIsa_reg m c d s' hstep hg
        rw [he] at h
        cases h
        exact Or.inl ⟨d, s', rfl, hstep, rfl,
          kapTso_setKernVonZustand m c s'⟩
      | false =>
        have he := adapterIsa_reg_verweigert_speicher m c d s' hstep hg
        rw [he] at h
        cases h
    | none =>
      have he := adapterIsa_reg_verweigert_schritt m c d hstep
      rw [he] at h
      cases h
  | lade a v =>
    cases hload : loadByte (tsoAnsicht m) c a with
    | some w =>
      cases heq : (w == v) with
      | true =>
        have he := adapterIsa_lade m c a v w hload heq
        rw [he] at h
        cases h
        exact Or.inr (Or.inl ⟨a, v, w, rfl, rfl, hload, heq⟩)
      | false =>
        have he := adapterIsa_lade_verweigert_wert m c a v w hload heq
        rw [he] at h
        cases h
    | none =>
      have he := adapterIsa_lade_verweigert m c a v hload
      rw [he] at h
      cases h
  | gibAus a v =>
    cases hissue : issueByte (tsoAnsicht m) c a v with
    | some s' =>
      have he := adapterIsa_gibAus m c a v s' hissue
      rw [he] at h
      cases h
      exact Or.inr (Or.inr ⟨a, v, s', rfl, hissue,
        kapTso_setTso m s'⟩)
    | none =>
      have he := adapterIsa_gibAus_verweigert m c a v hissue
      rw [he] at h
      cases h
  | verweigert =>
    have he := adapterIsa_verweigert m c
    rw [he] at h
    cases h

/- CUTS:
    Proved here so far: `kapTso_setKernVonZustand` (ISA register
    re-embedding is silent on the TSO projection) and the exact ISA
    classification `kap_isa_tso_klass` (register steps silent, loads
    observe with forwarding, stores are single `issueByte` events).
    NOT proved here (next pieces): isa reachability, muldiv silence,
    addr `concIssue` fold lemmas, union lifts, joint witness.
-/

#print axioms kapTso_setKernVonZustand
#print axioms kap_isa_tso_klass

end Gabbro.Grammatik.X86
