/-
  Audit 25 / Koernung.lean: demonstrations for read-only findings.

  No existing file is modified.
-/
import Grammatik.Koernung

open Gabbro.Grammatik

namespace Audit25.Koernung

/-! ## K1 (pattern b): the verdict hypothesis of `refused_no_tear` is never used.

    `refused_no_tear (f) (g) (h : f.verdict = some g) ...` cases on `g`
    with two identical branches, both `boundary_no_tear old new hlen m hd`.
    Neither `f` nor `h` is named. Demonstrated: the same conclusion with the
    verdict hypothesis (and the form) deleted, no case split. -/

theorem k1_ohne_verdict
    (old new : List Byte)
    (hlen : old.length = new.length) (m : Nat) (hd : AtBoundary old new m) :
    interrupted old new m = old ∨ interrupted old new m = new :=
  boundary_no_tear old new hlen m hd

-- The guarantee value is forced by the form: two verdict witnesses agree.
theorem k1_verdict_funktional (f : InvForm) (g₁ g₂ : Guarantee)
    (h₁ : f.verdict = some g₁) (h₂ : f.verdict = some g₂) : g₁ = g₂ := by
  rw [h₁] at h₂
  exact Option.some_inj.mp h₂

/-! ## K2 (pattern b/c): `AtBoundary` ignores its `old` argument.

    `def AtBoundary (_old new : List Byte) (m : Nat) : Prop :=
      m = 0 ∨ new.length ≤ m`. The underscore binder marks it: the "no
    observer sees the middle" premise constrains only `new` and `m`, never
    the old bytes. Demonstrated: swapping `old` preserves the premise. -/

theorem k2_alte_bytes_irrelevant (old₁ old₂ new : List Byte) (m : Nat)
    (h : AtBoundary old₁ new m) : AtBoundary old₂ new m :=
  h

/-! ## K3 (pattern a): `shared_inventory_tearing_free` re-discharges the two
    pure list lemmas per disjunct; the volatile disjunct adds no tearing
    content (see K4). Demonstrated: the admitted case is `admitted_no_tear`
    and the refused case is `boundary_no_tear`, directly. -/

theorem k3_admitted_ist_liste (form : InvForm) (hadm : form.admitted)
    (old new : List Byte) (hlen : old.length = new.length)
    (holdw : old.length = form.width) (m : Nat) :
    interrupted old new m = old ∨ interrupted old new m = new :=
  admitted_no_tear form hadm old new hlen holdw m

theorem k3_refused_ist_grenze (old new : List Byte)
    (hlen : old.length = new.length) (m : Nat) (hd : AtBoundary old new m) :
    interrupted old new m = old ∨ interrupted old new m = new :=
  boundary_no_tear old new hlen m hd

/-! ## K4 (pattern d): the "tearing free" name covers the volatile row,
    for which the theorem concludes only the tag, not old-or-new.

    With `h := Or.inr (Or.inr rfl)` the conclusion is `Or.inl rfl` -- true
    even for the witnessed tear. Demonstrated on the witnessed mix: the
    theorem holds while the transfer tears. -/

/-- Volatile row carries no tearing content: the conclusion holds WITH the
    witnessed tear present (left disjunct is the tag, old-or-new fails). -/
theorem k4_volatil_trotz_riss :
    torn [⟨0, by omega, by omega⟩, ⟨0, by omega, by omega⟩]
         [⟨1, by omega, by omega⟩, ⟨1, by omega, by omega⟩]
         (interrupted [⟨0, by omega, by omega⟩, ⟨0, by omega, by omega⟩]
            [⟨1, by omega, by omega⟩, ⟨1, by omega, by omega⟩] 1) ∧
    (InvForm.volatileReg = .volatileReg ∨
      interrupted [⟨0, by omega, by omega⟩, ⟨0, by omega, by omega⟩]
        [⟨1, by omega, by omega⟩, ⟨1, by omega, by omega⟩] 1 =
        [⟨0, by omega, by omega⟩, ⟨0, by omega, by omega⟩] ∨
      interrupted [⟨0, by omega, by omega⟩, ⟨0, by omega, by omega⟩]
        [⟨1, by omega, by omega⟩, ⟨1, by omega, by omega⟩] 1 =
        [⟨1, by omega, by omega⟩, ⟨1, by omega, by omega⟩]) := by
  refine ⟨mid_interruption_tears, Or.inl rfl⟩

/-! ## K5 (checked non-findings): the atomicity premise is satisfiable
    (`ereignisAtomar_gilt`), and the negative cases are genuine
    (`schreibBytes_not_single`, `leseBytes_not_atomic` conclude
    disequalities, not implications with unused premises). No demo needed
    beyond citing: `ereignisAtomar_gilt` closes the premise for every event,
    so §3 is not vacuous; §4/§5 prove `≠`, so they are not trivially true. -/

theorem k5_praemisse_erfuellbar (D : Deklaration) (e : Ereignis D) :
    EreignisAtomar e :=
  ereignisAtomar_gilt e

/-
CUTS:
- K1 VERIFIED: k1_ohne_verdict drops form+verdict, no case split.
- K2 VERIFIED: k2 shows `old` is ignored by `AtBoundary`.
- K3 demonstrated by direct re-derivation from the list lemmas.
- K4 VERIFIED: k4_volatil_trotz_riss shows the volatile disjunct coexists
  with the witnessed tear.
- K5 non-findings: premise satisfiable, negative cases genuine disequalities.
-/

#print axioms Audit25.Koernung.k1_ohne_verdict
#print axioms Audit25.Koernung.k2_alte_bytes_irrelevant
#print axioms Audit25.Koernung.k4_volatil_trotz_riss
#print axioms Audit25.Koernung.k5_praemisse_erfuellbar
