/-! Cumulative padding for ordered global storage. -/
module
public import Stage0.Senke.Welt.AlignUp

@[expose] public section
namespace Gabbro.Stage0.Senke

/-- Thread the padded end through the enumeration, rather than padding raw sums. -/
def globStarts {G : Type} : List G → Nat → (G → Nat) → (G → Nat) → List (G × Nat)
  | [], _, _, _ => []
  | g :: gs, o, sz, alignment =>
      let start := alignUp o (alignment g)
      (g, start) :: globStarts gs (start + sz g) sz alignment

/-- The first free byte after all globals, including cumulative padding. -/
def globEnd {G : Type} : List G → Nat → (G → Nat) → (G → Nat) → Nat
  | [], o, _, _ => o
  | g :: gs, o, sz, alignment =>
      globEnd gs (alignUp o (alignment g) + sz g) sz alignment

/-- Look up the first occurrence, threading the same padded cursor as the layout. -/
def globStartOf {G : Type} [DecidableEq G] : List G → Nat → (G → Nat) → (G → Nat) → G → Nat
  | [], o, _, _, _ => o
  | a :: gs, o, sz, alignment, g =>
      if g = a then alignUp o (alignment a)
      else globStartOf gs (alignUp o (alignment a) + sz a) sz alignment g

theorem globStartOf_mem {G : Type} [DecidableEq G] (gs : List G) (o : Nat)
    (sz alignment : G → Nat) (g : G) (hg : g ∈ gs) :
    (g, globStartOf gs o sz alignment g) ∈ globStarts gs o sz alignment := by
  induction gs generalizing o with
  | nil => simp at hg
  | cons a gs ih =>
      by_cases eq : g = a
      · subst g; simp [globStartOf, globStarts]
      · have tail : g ∈ gs := by simpa [eq] using hg
        simpa [globStartOf, globStarts, eq] using
          (List.mem_cons_of_mem (a, alignUp o (alignment a)) (ih _ tail))

theorem globEnd_ge {G : Type} (gs : List G) (o : Nat) (sz alignment : G → Nat) :
    o ≤ globEnd gs o sz alignment := by
  induction gs generalizing o with
  | nil => simp [globEnd]
  | cons g gs ih =>
      have := ih (alignUp o (alignment g) + sz g)
      have := le_alignUp o (alignment g)
      simp only [globEnd]
      omega

theorem globStarts_bounds {G : Type} (gs : List G) (o : Nat)
    (sz alignment : G → Nat) (g : G) (start : Nat)
    (h : (g, start) ∈ globStarts gs o sz alignment) :
    o ≤ start ∧ start + sz g ≤ globEnd gs o sz alignment := by
  induction gs generalizing o with
  | nil => simp [globStarts] at h
  | cons a gs ih =>
      simp only [globStarts, List.mem_cons] at h
      rcases h with h | h
      · cases h
        exact ⟨le_alignUp o (alignment g), globEnd_ge gs _ sz alignment⟩
      · have hb := ih _ h
        have ha := le_alignUp o (alignment a)
        simp only [globEnd]
        omega

/-- Every later start is at least the end of the preceding global. -/
theorem globStarts_step {G : Type} (g : G) (gs : List G) (o : Nat)
    (sz alignment : G → Nat) (h : G) (t : Nat)
    (ht : (h, t) ∈ globStarts gs
      (alignUp o (alignment g) + sz g) sz alignment) :
    alignUp o (alignment g) + sz g ≤ t :=
  (globStarts_bounds gs _ sz alignment h t ht).1

theorem globStarts_disjoint {G : Type} (gs : List G) (o : Nat)
    (sz alignment : G → Nat) (g h : G) (s t : Nat)
    (hg : (g, s) ∈ globStarts gs o sz alignment)
    (hh : (h, t) ∈ globStarts gs o sz alignment) (hne : g ≠ h) :
    s + sz g ≤ t ∨ t + sz h ≤ s := by
  induction gs generalizing o with
  | nil => simp [globStarts] at hg
  | cons a gs ih =>
      simp only [globStarts, List.mem_cons] at hg hh
      rcases hg with hg | hg <;> rcases hh with hh | hh
      · cases hg; cases hh; exact False.elim (hne rfl)
      · cases hg
        exact Or.inl (globStarts_bounds gs _ sz alignment h t hh).1
      · cases hh
        exact Or.inr (globStarts_bounds gs _ sz alignment g s hg).1
      · exact ih _ hg hh

/-- Unit alignment preserves the previous total size exactly. -/
@[simp] theorem globEnd_one {G : Type} (gs : List G) (o : Nat) (sz : G → Nat) :
    globEnd gs o sz (fun _ => 1) = o + (gs.map sz).sum := by
  induction gs generalizing o with
  | nil => simp [globEnd]
  | cons g gs ih => simp [globEnd, ih, Nat.add_assoc]

/-- Unit alignment recovers every previous prefix offset. -/
theorem globStarts_one {G : Type} (gs : List G) (o : Nat) (sz : G → Nat) :
    ∀ k : Nat, (globStarts gs o sz (fun _ => 1))[k]? =
      gs[k]?.map (fun g => (g, o + ((gs.map sz).take k).sum)) := by
  induction gs generalizing o with
  | nil => intro k; simp [globStarts]
  | cons g gs ih =>
      intro k
      cases k with
      | zero => simp [globStarts]
      | succ k => simpa [globStarts, Nat.add_assoc] using ih (o + sz g) k

/-- Relative padding preserves the storage grid, including zero alignment. -/
theorem glob_grid {G : Type} (gs : List G) (o : Nat) (sz alignment : G → Nat)
    (ho : 8 ∣ o) (hs : ∀ g, 8 ∣ sz g) :
    (∀ g start, (g, start) ∈ globStarts gs o sz (fun g => wordAlign (alignment g)) →
      8 ∣ start) ∧ 8 ∣ globEnd gs o sz (fun g => wordAlign (alignment g)) := by
  induction gs generalizing o with
  | nil => exact ⟨by simp [globStarts], ho⟩
  | cons g gs ih =>
      have ha := alignUp_word_grid o (alignment g) ho
      have tail := ih _ (Nat.dvd_add ha (hs g))
      constructor
      · intro h start hm
        simp only [globStarts, List.mem_cons] at hm
        rcases hm with hm | hm
        · cases hm; exact ha
        · exact tail.1 h start hm
      · exact tail.2

end Gabbro.Stage0.Senke
