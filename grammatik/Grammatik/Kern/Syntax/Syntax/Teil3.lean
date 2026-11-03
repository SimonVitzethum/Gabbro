module

public import Grammatik.Kern.Syntax.Syntax.Teil2
public import Grammatik.Kern.Syntax.Syntax.Teil2Programm

@[expose] public section

namespace Gabbro.Grammatik

/-! ## C11 current-state selector

    Deterministic selection for `Stmt.consumeTraverse`: the least remaining
    member that is minimal w.r.t. the declared edge relation, in index order.
    The machine supplies the CURRENT membership test (evaluating `member` in
    the post-body world) and the CURRENT edge test (evaluating `edge` there);
    this file owns only the order: the first minimal candidate in list order
    wins, so on the ascending `alleIndizes` order the least minimal index wins
    and ties break by position.

    `waehleMinimal` is the plain first-match order. `verbrauchWahl` refines it
    with minimality: a candidate `k` is eligible when it is a member (`p k`)
    and no member `j` with a different code (`same j k = false`) strictly
    precedes it (`e j k`). The machine instantiates `same` with equality of
    the represented index values, so self-edges never block and duplicate
    codes never select twice.

    Soundness (`verbrauchWahl_istMitglied`, `verbrauchWahl_istMinimal`) and
    completeness (`verbrauchWahl_vollstaendig`) below are proved from the
    definition alone. The bridge from actual `World D` states and emitted
    mutations to `Isabelle.Consuming`'s `Tabelle`/`kante` relation, strict
    measure fall and selector completeness over the live domain lives with the
    sequential semantics (`verbrauchLauf`, `verbrauchSel_*`) and the G machine
    (`dannVerbrauch` …); the re-selection itself is no longer open. -/

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

/-! ## Edge-minimal selection (`verbrauchWahl`)

    The candidate order is list order; eligibility is membership plus
    minimality w.r.t. `e`. `same` names equal codes (the machine uses equality
    of the represented index values). -/

/-- No remaining member with a different code strictly precedes `k`. -/
def keinVorgaenger {α : Type} : List α → (α → Bool) → (α → α → Bool) →
    (α → α → Bool) → α → Bool
  | [], _, _, _, _ => true
  | j :: js, p, e, same, k =>
      (!(p j && e j k && !(same j k))) && keinVorgaenger js p e same k

/-- A candidate is eligible when it is a member with no predecessor. -/
def istMinimalVerbrauch {α : Type} (ks : List α) (p : α → Bool)
    (e : α → α → Bool) (same : α → α → Bool) (k : α) : Bool :=
  p k && keinVorgaenger ks p e same k

/-- First minimal candidate in list order (`none` when none is minimal). -/
def verbrauchWahlAux {α : Type} (ganz : List α) : List α → (α → Bool) →
    (α → α → Bool) → (α → α → Bool) → Option α
  | [], _, _, _ => none
  | k :: ks, p, e, same =>
      if istMinimalVerbrauch ganz p e same k then some k
      else verbrauchWahlAux ganz ks p e same

/-- Deterministic current-state selection over `ks`. -/
def verbrauchWahl {α : Type} (ks : List α) (p : α → Bool) (e : α → α → Bool)
    (same : α → α → Bool) : Option α :=
  verbrauchWahlAux ks ks p e same

/-- A selected index passes the minimality test. -/
theorem verbrauchWahlAux_minimal {α : Type} {ganz ks : List α} {p : α → Bool}
    {e : α → α → Bool} {same : α → α → Bool} {v : α}
    (h : verbrauchWahlAux ganz ks p e same = some v) :
    istMinimalVerbrauch ganz p e same v = true := by
  induction ks with
  | nil => simp only [verbrauchWahlAux, reduceCtorEq] at h
  | cons k ks ih =>
      simp only [verbrauchWahlAux] at h
      by_cases hk : istMinimalVerbrauch ganz p e same k = true
      · simp only [hk, ↓reduceIte] at h
        cases h
        exact hk
      · have hkf : istMinimalVerbrauch ganz p e same k = false := by
          cases hpk : istMinimalVerbrauch ganz p e same k with
          | false => rfl
          | true => exact absurd hpk hk
        simp only [hkf, ↓reduceIte] at h
        exact ih h

/-- A selected index is a member of the scanned list. -/
theorem verbrauchWahlAux_istMitglied {α : Type} {ganz ks : List α} {p : α → Bool}
    {e : α → α → Bool} {same : α → α → Bool} {v : α}
    (h : verbrauchWahlAux ganz ks p e same = some v) : v ∈ ks := by
  induction ks with
  | nil => simp only [verbrauchWahlAux, reduceCtorEq] at h
  | cons k ks ih =>
      simp only [verbrauchWahlAux] at h
      by_cases hk : istMinimalVerbrauch ganz p e same k = true
      · simp only [hk, ↓reduceIte] at h
        cases h
        exact List.mem_cons_self ..
      · have hkf : istMinimalVerbrauch ganz p e same k = false := by
          cases hpk : istMinimalVerbrauch ganz p e same k with
          | false => rfl
          | true => exact absurd hpk hk
        simp only [hkf, ↓reduceIte] at h
        exact List.mem_cons_of_mem _ (ih h)

/-- A selected index is a member of the list. -/
theorem verbrauchWahl_istMitglied {α : Type} {ks : List α} {p : α → Bool}
    {e : α → α → Bool} {same : α → α → Bool} {v : α}
    (h : verbrauchWahl ks p e same = some v) : p v = true ∧ v ∈ ks := by
  simp only [verbrauchWahl] at h
  have hmin := verbrauchWahlAux_minimal h
  simp only [istMinimalVerbrauch, Bool.and_eq_true] at hmin
  exact ⟨hmin.1, verbrauchWahlAux_istMitglied h⟩

/-- From a clean predecessor scan, a different member never strictly precedes. -/
theorem keinVorgaenger_falsch {α : Type} {ks : List α} {p : α → Bool}
    {e : α → α → Bool} {same : α → α → Bool} {v j : α}
    (hj : j ∈ ks) (hpj : p j = true) (hne : same j v = false)
    (h : keinVorgaenger ks p e same v = true) : e j v = false := by
  induction ks with
  | nil => cases hj
  | cons k ks ih =>
      simp only [keinVorgaenger, Bool.and_eq_true] at h
      obtain ⟨hk, hrest⟩ := h
      simp only [List.mem_cons] at hj
      cases hj with
      | inl heq =>
          subst heq
          by_cases he : e j v = true
          · have hkf : (p j && e j v && !(same j v)) = true := by
              simp only [hpj, he, hne, Bool.not_false, Bool.and_self]
            have : (!(p j && e j v && !(same j v))) = false := by
              simp only [hkf, Bool.not_true]
            simp only [this, Bool.false_eq_true] at hk
          · have hef : e j v = false := by
              cases hpk : e j v with
              | false => rfl
              | true => exact absurd hpk he
            exact hef
      | inr hmem => exact ih hmem hrest

/-- A selected index is minimal: no different member strictly precedes it. -/
theorem verbrauchWahl_istMinimal {α : Type} {ks : List α} {p : α → Bool}
    {e : α → α → Bool} {same : α → α → Bool} {v : α}
    (h : verbrauchWahl ks p e same = some v) {j : α} (hj : j ∈ ks)
    (hpj : p j = true) (hne : same j v = false) : e j v = false := by
  simp only [verbrauchWahl] at h
  have hmin := verbrauchWahlAux_minimal h
  simp only [istMinimalVerbrauch, Bool.and_eq_true] at hmin
  exact keinVorgaenger_falsch hj hpj hne hmin.2

/-- No selection means no candidate passes the minimality test. -/
theorem verbrauchWahl_keinMinimal {α : Type} {ganz ks : List α} {p : α → Bool}
    {e : α → α → Bool} {same : α → α → Bool}
    (h : verbrauchWahlAux ganz ks p e same = none) :
    ∀ v ∈ ks, istMinimalVerbrauch ganz p e same v = false := by
  induction ks with
  | nil => intro v hv; cases hv
  | cons k ks ih =>
      simp only [verbrauchWahlAux] at h
      by_cases hk : istMinimalVerbrauch ganz p e same k = true
      · simp only [hk, ↓reduceIte, reduceCtorEq] at h
      · have hkf : istMinimalVerbrauch ganz p e same k = false := by
          cases hpk : istMinimalVerbrauch ganz p e same k with
          | false => rfl
          | true => exact absurd hpk hk
        simp only [hkf, ↓reduceIte] at h
        intro v hv
        simp only [List.mem_cons] at hv
        cases hv with
        | inl heq => subst heq; exact hkf
        | inr hmem => exact ih h v hmem

/-- A list with no minimal candidate selects nothing. -/
theorem verbrauchWahlAux_alleUnminimal {α : Type} {ganz ks : List α} {p : α → Bool}
    {e : α → α → Bool} {same : α → α → Bool}
    (h : ∀ v ∈ ks, istMinimalVerbrauch ganz p e same v = false) :
    verbrauchWahlAux ganz ks p e same = none := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      have hk : istMinimalVerbrauch ganz p e same k = false :=
        h k (by simp)
      simp only [verbrauchWahlAux, hk, ↓reduceIte]
      apply ih
      intro v hv
      exact h v (List.mem_cons_of_mem _ hv)

/-- Completeness: empty selection exactly when no candidate is minimal. -/
theorem verbrauchWahl_vollstaendig {α : Type} {ks : List α} {p : α → Bool}
    {e : α → α → Bool} {same : α → α → Bool} :
    verbrauchWahl ks p e same = none ↔
      ∀ v ∈ ks, istMinimalVerbrauch ks p e same v = false :=
  ⟨verbrauchWahl_keinMinimal, fun h => verbrauchWahlAux_alleUnminimal h⟩

/-- Witness: with the edge `0 → 1`, `0` is selected first; once `0` is
    consumed, `1` is minimal and selected. -/
theorem verbrauchWahl_zeuge_zwei :
    verbrauchWahl [0, 1] (fun _ => true) (fun j k => (j == 0 && k == 1))
        (fun j k => j == k) = some 0 ∧
      verbrauchWahl [1] (fun _ => true) (fun j k => (j == 0 && k == 1))
        (fun j k => j == k) = some 1 := by
  constructor <;> rfl

/-! ## Selection transport along a value map

    The `ru` congruence (and every world transport) maps the index domain
    pointwise (`alleIndizes` through `valR`) with pointwise-equal tests.
    Selection follows the map. -/

/-- Predecessor scans follow a value map with pointwise-equal tests (the
    test point is fixed, so no membership travels into the scan). -/
theorem keinVorgaenger_map {α β : Type} (f : α → β) (ganz : List α)
    (p : α → Bool) (p' : β → Bool) (e : α → α → Bool) (e' : β → β → Bool)
    (same : α → α → Bool) (same' : β → β → Bool)
    (k : α)
    (hp : ∀ k ∈ ganz, p' (f k) = p k)
    (he : ∀ j ∈ ganz, e' (f j) (f k) = e j k)
    (hsame : ∀ j ∈ ganz, same' (f j) (f k) = same j k) :
    keinVorgaenger (ganz.map f) p' e' same' (f k) =
      keinVorgaenger ganz p e same k := by
  induction ganz with
  | nil => rfl
  | cons j js ih =>
      simp only [keinVorgaenger, List.map_cons]
      have hpj : p' (f j) = p j := hp j (by simp)
      have hej : e' (f j) (f k) = e j k := he j (by simp)
      have hsj : same' (f j) (f k) = same j k := hsame j (by simp)
      rw [hpj, hej, hsj,
        ih (fun k hk => hp k (List.mem_cons_of_mem _ hk))
          (fun j hj => he j (List.mem_cons_of_mem _ hj))
          (fun j hj => hsame j (List.mem_cons_of_mem _ hj))]

/-- Minimality tests follow a value map on the domain. -/
theorem istMinimalVerbrauch_map {α β : Type} (f : α → β) (ganz : List α)
    (p : α → Bool) (p' : β → Bool) (e : α → α → Bool) (e' : β → β → Bool)
    (same : α → α → Bool) (same' : β → β → Bool)
    (hp : ∀ k ∈ ganz, p' (f k) = p k)
    (he : ∀ j ∈ ganz, ∀ k ∈ ganz, e' (f j) (f k) = e j k)
    (hsame : ∀ j ∈ ganz, ∀ k ∈ ganz, same' (f j) (f k) = same j k)
    (k : α) (hk : k ∈ ganz) :
    istMinimalVerbrauch (ganz.map f) p' e' same' (f k) =
      istMinimalVerbrauch ganz p e same k := by
  simp only [istMinimalVerbrauch, hp k hk,
    keinVorgaenger_map f ganz p p' e e' same same' k hp
      (fun j hj => he j hj k hk) (fun j hj => hsame j hj k hk)]

/-- Selection follows a value map with pointwise-equal tests over the
    scanned sublist. -/
theorem verbrauchWahlAux_map {α β : Type} (f : α → β) (ganz ks : List α)
    (p : α → Bool) (p' : β → Bool) (e : α → α → Bool) (e' : β → β → Bool)
    (same : α → α → Bool) (same' : β → β → Bool)
    (hp : ∀ k ∈ ganz, p' (f k) = p k)
    (he : ∀ j ∈ ganz, ∀ k ∈ ganz, e' (f j) (f k) = e j k)
    (hsame : ∀ j ∈ ganz, ∀ k ∈ ganz, same' (f j) (f k) = same j k)
    (hsub : ∀ k ∈ ks, k ∈ ganz) :
    verbrauchWahlAux (ganz.map f) (ks.map f) p' e' same' =
      (verbrauchWahlAux ganz ks p e same).map f := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      have hk : k ∈ ganz := hsub k (by simp)
      have hm := istMinimalVerbrauch_map f ganz p p' e e' same same'
        hp he hsame k hk
      simp only [verbrauchWahlAux, List.map_cons, hm]
      by_cases ht : istMinimalVerbrauch ganz p e same k = true
      · simp only [ht, ↓reduceIte]; rfl
      · have htf : istMinimalVerbrauch ganz p e same k = false := by
          cases hpk : istMinimalVerbrauch ganz p e same k with
          | false => rfl
          | true => exact absurd hpk ht
        simp only [htf, ↓reduceIte]
        exact ih (fun k hk => hsub k (List.mem_cons_of_mem _ hk))

/-- Selection over a domain follows the domain map. -/
theorem verbrauchWahl_map {α β : Type} (f : α → β) (ks : List α)
    (p : α → Bool) (p' : β → Bool) (e : α → α → Bool) (e' : β → β → Bool)
    (same : α → α → Bool) (same' : β → β → Bool)
    (hp : ∀ k ∈ ks, p' (f k) = p k)
    (he : ∀ j ∈ ks, ∀ k ∈ ks, e' (f j) (f k) = e j k)
    (hsame : ∀ j ∈ ks, ∀ k ∈ ks, same' (f j) (f k) = same j k) :
    verbrauchWahl (ks.map f) p' e' same' =
      (verbrauchWahl ks p e same).map f :=
  verbrauchWahlAux_map f ks ks p p' e e' same same' hp he hsame (fun k hk => hk)

/-- Pointwise-equal predicates count alike across a value map (`all`). -/
theorem map_all_beibehalt {α β : Type} (f : α → β) (l : List α)
    (p : α → Bool) (p' : β → Bool)
    (h : ∀ x ∈ l, p' (f x) = p x) :
    ((l.map f).all p') = (l.all p) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx : p' (f x) = p x := h x List.mem_cons_self
      have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [List.map_cons, List.all_cons, hx, ih']

#print axioms waehleMinimal_istMitglied
#print axioms waehleMinimal_keinMitglied
#print axioms waehleMinimal_alleFalsch
#print axioms waehleMinimal_vollstaendig
#print axioms waehleMinimal_zeuge
#print axioms verbrauchWahlAux_minimal
#print axioms verbrauchWahlAux_istMitglied
#print axioms verbrauchWahl_istMitglied
#print axioms keinVorgaenger_falsch
#print axioms verbrauchWahl_istMinimal
#print axioms verbrauchWahl_keinMinimal
#print axioms verbrauchWahlAux_alleUnminimal
#print axioms verbrauchWahl_vollstaendig
#print axioms verbrauchWahl_zeuge_zwei
#print axioms keinVorgaenger_map
#print axioms istMinimalVerbrauch_map
#print axioms verbrauchWahlAux_map
#print axioms verbrauchWahl_map
#print axioms map_all_beibehalt

end Gabbro.Grammatik
