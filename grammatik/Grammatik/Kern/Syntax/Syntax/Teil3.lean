module

public import Grammatik.Kern.Syntax.Syntax.Teil2
public import Grammatik.Kern.Syntax.Syntax.Teil2Programm

@[expose] public section

namespace Gabbro.Grammatik

/-! ## C11 current-state selector

    Deterministic selection for `Stmt.consumeTraverse`: the first remaining
    member in index order. The machine supplies the CURRENT membership test
    (evaluating `member` in the post-body world); this file owns only the
    order: first match in list order wins, so on the ascending `alleIndizes`
    order the least eligible index wins and ties break by position.

    Soundness (`waehleMinimal_istMitglied`) and completeness
    (`waehleMinimal_vollstaendig`) below are proved from the definition alone.
    The bridge from actual `World D` states and emitted mutations to
    `Isabelle.Consuming`'s `Tabelle`/`kante` relation, strict measure fall and
    selector completeness over the live domain are OPEN (design rows
    "Consuming proofs/admission" and "Consuming export/IR"). -/

/-- First member of `ks` in list order (`none` when no element passes). -/
def waehleMinimal : List Nat → (Nat → Bool) → Option Nat
  | [], _ => none
  | k :: ks, p => if p k then some k else waehleMinimal ks p

/-- A selected index passes the test and comes from the list. -/
theorem waehleMinimal_istMitglied {ks : List Nat} {p : Nat → Bool} {v : Nat}
    (h : waehleMinimal ks p = some v) : p v = true ∧ v ∈ ks := by
  induction ks with
  | nil => simp only [waehleMinimal, reduceCtorEq] at h
  | cons k ks ih =>
      simp only [waehleMinimal] at h
      by_cases hk : p k = true
      · simp only [hk, ↓reduceIte] at h
        cases h
        exact ⟨hk, by simp⟩
      · have hkf : p k = false := by
          cases hpk : p k with
          | false => rfl
          | true => exact absurd hpk hk
        simp only [hkf, ↓reduceIte] at h
        obtain ⟨hpv, hmem⟩ := ih h
        exact ⟨hpv, by simp [hmem]⟩

/-- No selection means no element passes. -/
theorem waehleMinimal_keinMitglied {ks : List Nat} {p : Nat → Bool}
    (h : waehleMinimal ks p = none) : ∀ v ∈ ks, p v = false := by
  induction ks with
  | nil => intro v hv; cases hv
  | cons k ks ih =>
      simp only [waehleMinimal] at h
      by_cases hk : p k = true
      · simp only [hk, ↓reduceIte, reduceCtorEq] at h
      · have hkf : p k = false := by
          cases hpk : p k with
          | false => rfl
          | true => exact absurd hpk hk
        simp only [hkf, ↓reduceIte] at h
        intro v hv
        simp only [List.mem_cons] at hv
        cases hv with
        | inl heq => subst heq; exact hkf
        | inr hmem => exact ih h v hmem

/-- Every all-false list selects nothing. -/
theorem waehleMinimal_alleFalsch {ks : List Nat} {p : Nat → Bool}
    (h : ∀ v ∈ ks, p v = false) : waehleMinimal ks p = none := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      have hk : p k = false := h k (by simp)
      simp only [waehleMinimal, hk, ↓reduceIte]
      apply ih
      intro v hv
      exact h v (by simp [hv])

/-- Completeness: empty selection exactly when the domain has no member. -/
theorem waehleMinimal_vollstaendig {ks : List Nat} {p : Nat → Bool} :
    waehleMinimal ks p = none ↔ ∀ v ∈ ks, p v = false :=
  ⟨waehleMinimal_keinMitglied, waehleMinimal_alleFalsch⟩

/-- Witness: two eligible indices select the first in list order. -/
theorem waehleMinimal_zeuge : waehleMinimal [1, 0] (fun _ => true) = some 1 := by
  rfl

#print axioms waehleMinimal_istMitglied
#print axioms waehleMinimal_keinMitglied
#print axioms waehleMinimal_alleFalsch
#print axioms waehleMinimal_vollstaendig
#print axioms waehleMinimal_zeuge

end Gabbro.Grammatik
