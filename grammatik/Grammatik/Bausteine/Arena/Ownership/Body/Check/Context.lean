import Grammatik.Bausteine.Arena.Ownership.Body.Judgment

/-! Decidable context relations for the executable admission check. On
bounded contexts the Bool tests decide `Weaker` and `ExitsTo`; joins of two
branch contexts and the head context of a loop are computed. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

/-- Rights agree below a bound. -/
def rightsAgree (a b : Context) (n : Nat) : Bool := (List.range n).all fun i => a.rights i == b.rights i

/-- Every name `k` ties to an origin is tied to it in `c`. -/
def refsWeaker : List (Option Nat) → List (Option Nat) → Bool
  | [], [] => true
  | x :: xs, y :: ys => (x.isNone || x == y) && refsWeaker xs ys
  | _, _ => false

/-- **`Weaker`, decided.** -/
def weakerB (k c : Context) : Bool :=
  rightsAgree k c (max k.next c.next) && refsWeaker k.references c.references

theorem rightsAgree_sound {a b : Context} {n : Nat} (h : rightsAgree a b n = true) {i : Nat} (hi : i < n) :
    a.rights i = b.rights i := by
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simpa using this

theorem refsWeaker_sound : ∀ {k c : List (Option Nat)}, refsWeaker k c = true →
    k.length = c.length ∧ ∀ (p o : Nat), k[p]? = some (some o) → c[p]? = some (some o)
  | [], [], _ => ⟨rfl, fun _ _ h => by cases h⟩
  | x :: xs, y :: ys, h => by
    simp only [refsWeaker, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at h
    obtain ⟨hxy, hr⟩ := h
    obtain ⟨hl, hs⟩ := refsWeaker_sound hr
    refine ⟨by simp only [List.length_cons, hl, Nat.add_left_cancel_iff], ?_⟩
    intro p o hp
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp ⊢
      rcases hxy with hn | he
      · subst hn; cases hp
      · rw [← he]; exact hp
    | succ p => simpa using hs p o (by simpa using hp)
  | [], _ :: _, h => by simp only [refsWeaker, Bool.false_eq_true] at h
  | _ :: _, [], h => by simp only [refsWeaker, Bool.false_eq_true] at h

theorem rights_eq_of_agree {a b : Context} (ha : a.bounded) (hb : b.bounded)
    (h : rightsAgree a b (max a.next b.next) = true) (i : Nat) : a.rights i = b.rights i := by
  by_cases hi : i < max a.next b.next
  · exact rightsAgree_sound h hi
  · rw [ha.1 i (by omega), hb.1 i (by omega)]

theorem weaker_of {k c : Context} (hk : k.bounded) (hr : ∀ i, k.rights i = c.rights i)
    (hrefs : refsWeaker k.references c.references = true) : Weaker k c := by
  obtain ⟨hl, hs⟩ := refsWeaker_sound hrefs
  exact ⟨hr, hk.1, hl, fun p o h => ⟨hs p o h, hk.2 _ (List.mem_of_getElem? h) o rfl⟩⟩

theorem weakerB_sound {k c : Context} (hk : k.bounded) (hc : c.bounded) (h : weakerB k c = true) :
    Weaker k c := by
  simp only [weakerB, Bool.and_eq_true] at h
  exact weaker_of hk (rights_eq_of_agree hk hc h.1) h.2

/-- The pointwise meet of two reference lists. -/
def refsMeet : List (Option Nat) → List (Option Nat) → List (Option Nat)
  | x :: xs, y :: ys => (if x == y then x else none) :: refsMeet xs ys
  | _, _ => []

/-- **The join of two branch contexts**, when they agree on every right. -/
def joinB (a b : Context) : Option Context :=
  if rightsAgree a b (max a.next b.next) && a.references.length == b.references.length then
    some ⟨refsMeet a.references b.references, a.rights, max a.next b.next⟩
  else none

theorem refsMeet_weaker : ∀ {a b : List (Option Nat)}, a.length = b.length →
    refsWeaker (refsMeet a b) a = true ∧ refsWeaker (refsMeet a b) b = true
  | [], [], _ => ⟨rfl, rfl⟩
  | x :: xs, y :: ys, h => by
    have ih := refsMeet_weaker (a := xs) (b := ys) (by simpa using h)
    by_cases he : x = y
    · subst he; simp only [refsMeet, BEq.rfl, ↓reduceIte, refsWeaker, Bool.or_true, ih.1, Bool.and_self, ih.2, and_self]
    · simp only [refsMeet, beq_iff_eq, he, ↓reduceIte, refsWeaker, Option.isNone_none, Bool.true_or, ih.1,
  Bool.and_self, ih.2, and_self]

theorem joinB_bounded {a b j : Context} (ha : a.bounded) (hb : b.bounded) (hj : joinB a b = some j) :
    j.bounded := by
  unfold joinB at hj
  split at hj
  · cases hj
    refine ⟨fun i hi => ha.1 i (by simp only at hi; omega), ?_⟩
    intro ref hm i he
    subst he
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hm
    have hl : a.references.length = b.references.length := by
      rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc.2
    have hw := (refsWeaker_sound (refsMeet_weaker hl).1).2 p i hp
    have := ha.2 _ (List.mem_of_getElem? hw) i rfl
    simp only [gt_iff_lt]; omega
  · cases hj

theorem joinB_weaker {a b j : Context} (ha : a.bounded) (hb : b.bounded) (hj : joinB a b = some j) :
    Weaker j a ∧ Weaker j b := by
  have hjb := joinB_bounded ha hb hj
  unfold joinB at hj
  split at hj
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    cases hj
    have hm := refsMeet_weaker hc.2
    exact ⟨weaker_of hjb (fun _ => rfl) hm.1, weaker_of hjb (fun i => rights_eq_of_agree (a := a) (b := b) ha hb hc.1 i) hm.2⟩
  · cases hj

end Gabbro.Grammatik.ArenaOwnership.Body
