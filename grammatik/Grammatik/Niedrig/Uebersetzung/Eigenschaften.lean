/-
  File:      Grammatik/Niedrig/Uebersetzung/Eigenschaften.lean
  Subject:   THEOREMS OF THE NEUTRAL WALK (L6a): locality, map/unmap frame,
    unmap fault, protect weakening, aliases surviving one unmap.

  * `walkAux_agree`: the walk depends only on the visited entries.
  * `map_untouched` / `unmap_untouched`: setting one entry changes nothing
    for addresses whose path avoids it (the frame half of map/unmap).
  * `unmap_fault`: an address whose path reaches the unmapped entry faults.
  * `protect_walk_le`: protect never yields more permissions (`WalkLe`).
  * `Alias` with `alias_survives_unmap`: two addresses naming the same frame
    are aliases; unmapping one path leaves the other translating, so
    revocation needs more than one unmap.
  * LEFT OUT: the general reconstruction of an address from indices and
    offset (see `Regime.lean`); a walk-level map-success rule for reaching
    addresses (witnessed by `rfl` instances in `Zeuge.lean` instead).
-/
module

public import Grammatik.Niedrig.Uebersetzung.Tabelle

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Uebersetzung

/-- The walk depends only on the entries it visits. -/
theorem walkAux_agree (T1 T2 : Tables) (is : List Nat) (cur : Nat)
    (h : ∀ p : Nat × Nat, p ∈ visitedAux T1 is cur →
      T1 p.1 p.2 = T2 p.1 p.2) :
    walkAux T1 is cur = walkAux T2 is cur := by
  cases is with
  | nil =>
    rfl
  | cons i rest =>
    have hmem : (cur, i) ∈ visitedAux T1 (i :: rest) cur := by
      unfold visitedAux
      exact List.mem_cons_self
    have heq := h (cur, i) hmem
    cases he : T1 cur i with
    | absent =>
      rw [he] at heq
      have he2 : T2 cur i = Entry.absent := by
        rw [← heq]
      unfold walkAux
      rw [he, he2]
    | table nxt1 =>
      rw [he] at heq
      have he2 : T2 cur i = Entry.table nxt1 := by
        rw [← heq]
      cases rest with
      | nil =>
        unfold walkAux
        rw [he, he2]
      | cons j js =>
        have htail : ∀ p : Nat × Nat, p ∈ visitedAux T1 (j :: js) nxt1 →
            T1 p.1 p.2 = T2 p.1 p.2 := by
          intro p hp
          apply h
          unfold visitedAux
          rw [he]
          show p ∈ (cur, i) :: visitedAux T1 (j :: js) nxt1
          exact List.mem_cons_of_mem _ hp
        unfold walkAux
        rw [he, he2]
        exact walkAux_agree T1 T2 (j :: js) nxt1 htail
    | leaf f p =>
      rw [he] at heq
      have he2 : T2 cur i = Entry.leaf f p := by
        rw [← heq]
      cases rest with
      | nil =>
        unfold walkAux
        rw [he, he2]
      | cons j js =>
        unfold walkAux
        rw [he, he2]

/-- The address walk depends only on its visited entries. -/
theorem walk_agree (R : Regime) (T1 T2 : Tables) (root a : Nat)
    (h : ∀ p : Nat × Nat, p ∈ visited R T1 root a →
      T1 p.1 p.2 = T2 p.1 p.2) :
    walk R T1 root a = walk R T2 root a :=
  walkAux_agree T1 T2 (R.indices a) root h

/-- One set entry keeps every visited entry off its address. -/
theorem setEntry_untouched (T : Tables) (is : List Nat) (cur tbl idx : Nat)
    (e : Entry) (hnot : (tbl, idx) ∉ visitedAux T is cur) (p : Nat × Nat)
    (hp : p ∈ visitedAux T is cur) :
    setEntry T tbl idx e p.1 p.2 = T p.1 p.2 := by
  cases p with
  | mk t i =>
    unfold setEntry
    split
    · rename_i h1
      split
      · rename_i h2
        have hmem : (tbl, idx) ∈ visitedAux T is cur := by
          rw [← h1, ← h2]
          exact hp
        cases hnot hmem
      · rfl
    · rfl

/-- `map` changes nothing off its entry. -/
theorem map_untouched (R : Regime) (T : Tables) (root a tbl idx frame : Nat)
    (p : Perm) (hnot : (tbl, idx) ∉ visited R T root a) :
    walk R (mapEntry T tbl idx frame p) root a =
      walk R T root a :=
  (walkAux_agree T (mapEntry T tbl idx frame p) (R.indices a) root
    (fun q hq =>
      (setEntry_untouched T (R.indices a) root tbl idx
        (Entry.leaf frame p) hnot q hq).symm)).symm

/-- `unmap` changes nothing off its entry. -/
theorem unmap_untouched (R : Regime) (T : Tables) (root a tbl idx : Nat)
    (hnot : (tbl, idx) ∉ visited R T root a) :
    walk R (unmapEntry T tbl idx) root a =
      walk R T root a :=
  (walkAux_agree T (unmapEntry T tbl idx) (R.indices a) root
    (fun q hq =>
      (setEntry_untouched T (R.indices a) root tbl idx
        Entry.absent hnot q hq).symm)).symm

/-- The unmapped head always faults, whatever it held. -/
theorem unmap_head_eq (T : Tables) (i : Nat) (rest : List Nat)
    (cur tbl idx : Nat) (hhead : (cur, i) = (tbl, idx)) :
    walkAux (unmapEntry T tbl idx) (i :: rest) cur = Option.none := by
  have hunmap : unmapEntry T tbl idx cur i = Entry.absent := by
    unfold unmapEntry
    cases hhead
    exact setEntry_hit _ _ _ _
  unfold walkAux
  rw [hunmap]

/-- Off its entry, unmap keeps the entry. -/
theorem unmap_head_ne (T : Tables) (cur i tbl idx : Nat)
    (hhead : (cur, i) ≠ (tbl, idx)) :
    unmapEntry T tbl idx cur i = T cur i := by
  unfold unmapEntry
  have hne : cur ≠ tbl ∨ i ≠ idx := by
    by_cases h1 : cur = tbl
    · exact Or.inr (fun e => hhead (by rw [h1, e]))
    · exact Or.inl h1
  cases hne with
  | inl h1 =>
    exact setEntry_miss_table _ _ _ _ _ _ h1
  | inr h2 =>
    by_cases h1 : cur = tbl
    · subst h1
      rw [setEntry_miss_index _ _ _ _ _ h2]
    · exact setEntry_miss_table _ _ _ _ _ _ h1

/-- `unmap` faults every address whose path reaches the entry. -/
theorem unmapAux_fault (T : Tables) (is : List Nat) (cur tbl idx : Nat)
    (hmem : (tbl, idx) ∈ visitedAux T is cur) :
    walkAux (unmapEntry T tbl idx) is cur = Option.none := by
  induction is generalizing cur with
  | nil =>
    simp only [visitedAux] at hmem
    cases hmem
  | cons i rest ih =>
    by_cases hhead : (cur, i) = (tbl, idx)
    · exact unmap_head_eq T i rest cur tbl idx hhead
    · have hunmap_eq := unmap_head_ne T cur i tbl idx hhead
      cases he : T cur i with
      | absent =>
        unfold walkAux
        rw [hunmap_eq, he]
      | table nxt1 =>
        cases rest with
        | nil =>
          unfold walkAux
          rw [hunmap_eq, he]
        | cons j js =>
          have htail : (tbl, idx) ∈ visitedAux T (j :: js) nxt1 := by
            unfold visitedAux at hmem
            rw [he] at hmem
            change (tbl, idx) ∈ (cur, i) :: visitedAux T (j :: js) nxt1
              at hmem
            have hOr := List.mem_cons.mp hmem
            cases hOr with
            | inl heq =>
              cases hhead heq.symm
            | inr htail =>
              exact htail
          have htail_walk := ih nxt1 htail
          unfold walkAux
          rw [hunmap_eq, he]
          exact htail_walk
      | leaf frame perms =>
        cases rest with
        | nil =>
          have himp : (cur, i) = (tbl, idx) := by
            unfold visitedAux at hmem
            rw [he] at hmem
            change (tbl, idx) ∈ (cur, i) :: ([] : List (Nat × Nat))
              at hmem
            have hOr := List.mem_cons.mp hmem
            cases hOr with
            | inl heq =>
              exact heq.symm
            | inr hcon =>
              cases hcon
          cases hhead himp
        | cons j js =>
          unfold walkAux
          rw [hunmap_eq, he]

/-- `unmap` faults every reaching address. -/
theorem unmap_fault (R : Regime) (T : Tables) (root a tbl idx : Nat)
    (hmem : (tbl, idx) ∈ visited R T root a) :
    walk R (unmapEntry T tbl idx) root a = Option.none :=
  unmapAux_fault T (R.indices a) root tbl idx hmem

/-- Walk results ordered by same frame and fewer permissions. -/
inductive WalkLe : Option (Nat × Perm) → Option (Nat × Perm) → Prop where
  | none : WalkLe Option.none Option.none
  | some : ∀ f p q, q.le p → WalkLe (Option.some (f, p)) (Option.some (f, q))

/-- `protect` never yields more permissions. -/
theorem protect_walkAux_le (T : Tables) (is : List Nat) (cur tbl idx : Nat)
    (q : Perm) :
    WalkLe (walkAux T is cur)
      (walkAux (protectEntry T tbl idx q) is cur) := by
  cases is with
  | nil =>
    exact WalkLe.none
  | cons i rest =>
    cases he : T cur i with
    | absent =>
      have he2 : protectEntry T tbl idx q cur i = Entry.absent := by
        unfold protectEntry
        split
        · rename_i h1
          split
          · rename_i h2
            rw [he]
          · exact he
        · exact he
      unfold walkAux
      rw [he, he2]
      exact WalkLe.none
    | table nxt1 =>
      have he2 : protectEntry T tbl idx q cur i = Entry.table nxt1 := by
        unfold protectEntry
        split
        · rename_i h1
          split
          · rename_i h2
            rw [he]
          · exact he
        · exact he
      cases rest with
      | nil =>
        unfold walkAux
        rw [he, he2]
        exact WalkLe.none
      | cons j js =>
        unfold walkAux
        rw [he, he2]
        exact protect_walkAux_le T (j :: js) nxt1 tbl idx q
    | leaf f p =>
      cases rest with
      | nil =>
        have he2 : protectEntry T tbl idx q cur i =
            Entry.leaf f (Perm.meet p q) ∨
            protectEntry T tbl idx q cur i = Entry.leaf f p := by
          unfold protectEntry
          split
          · rename_i h1
            split
            · rename_i h2
              rw [he]
              exact Or.inl rfl
            · exact Or.inr he
          · exact Or.inr he
        cases he2 with
        | inl hmeet =>
          unfold walkAux
          rw [he, hmeet]
          exact WalkLe.some f p (Perm.meet p q) (Perm.meet_le_left p q)
        | inr hsame =>
          unfold walkAux
          rw [he, hsame]
          exact WalkLe.some f p p (Perm.le_refl p)
      | cons j js =>
        have he2 : protectEntry T tbl idx q cur i =
            Entry.leaf f (Perm.meet p q) ∨
            protectEntry T tbl idx q cur i = Entry.leaf f p := by
          unfold protectEntry
          split
          · rename_i h1
            split
            · rename_i h2
              rw [he]
              exact Or.inl rfl
            · exact Or.inr he
          · exact Or.inr he
        cases he2 with
        | inl hmeet =>
          unfold walkAux
          rw [he, hmeet]
          exact WalkLe.none
        | inr hsame =>
          unfold walkAux
          rw [he, hsame]
          exact WalkLe.none

/-- `protect` never yields more permissions, on addresses. -/
theorem protect_walk_le (R : Regime) (T : Tables) (root a tbl idx : Nat)
    (q : Perm) :
    WalkLe (walk R T root a)
      (walk R (protectEntry T tbl idx q) root a) := by
  unfold walk
  exact protect_walkAux_le T (R.indices a) root tbl idx q

/-- Two addresses naming the same frame are aliases. -/
def Alias (R : Regime) (T : Tables) (root a1 a2 : Nat) : Prop :=
  ∃ f p1 p2,
    walk R T root a1 = Option.some (f, p1) ∧
    walk R T root a2 = Option.some (f, p2)

/-- After unmapping one path, the other alias still translates. -/
theorem alias_survives_unmap (R : Regime) (T : Tables) (root a1 a2 : Nat)
    (tbl idx : Nat)
    (hmem1 : (tbl, idx) ∈ visited R T root a1)
    (hnot2 : (tbl, idx) ∉ visited R T root a2)
    (f : Nat) (p2 : Perm)
    (h2 : walk R T root a2 = Option.some (f, p2)) :
    walk R (unmapEntry T tbl idx) root a2 = Option.some (f, p2) := by
  have hsame := unmap_untouched R T root a2 tbl idx hnot2
  rw [hsame]
  exact h2

#print axioms Gabbro.Grammatik.Niedrig.Uebersetzung.walkAux_agree
#print axioms Gabbro.Grammatik.Niedrig.Uebersetzung.unmap_fault
#print axioms Gabbro.Grammatik.Niedrig.Uebersetzung.protect_walk_le
#print axioms Gabbro.Grammatik.Niedrig.Uebersetzung.alias_survives_unmap

end Gabbro.Grammatik.Niedrig.Uebersetzung
