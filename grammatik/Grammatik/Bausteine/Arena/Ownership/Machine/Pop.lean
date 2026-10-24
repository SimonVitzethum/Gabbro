import Grammatik.Bausteine.Arena.Ownership.Machine.View

/-! **The ledger when the running activation returns.** The returning
activation `cf` hands what it owns (at most its owning result) to its caller
`fr` under a new grant, and leaves every loan it holds. Seen from the
caller, nothing else changes: what it had lent to `cf` is again its own,
and no other activation's view moves. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

/-- One cell when `cf` returns to `fr`. -/
def popCell (next : Nat) (cf fr : Frame) (cell : Cell) : Cell :=
  if cell.owner = cf then ⟨cell.allocation, next, fr, []⟩
  else { cell with loans := cell.loans.filter (fun g => decide (g ≠ cf)) }

/-- **The ledger after `cf` returns to `fr`.** -/
def _root_.Gabbro.Grammatik.ArenaOwnership.State.pop (s : State) (cf fr : Frame) : State :=
  ⟨s.next + 1, fun j => (s.cells j).map (popCell s.next cf fr)⟩

namespace Pop

variable {s : State} {cf fr : Frame}

theorem cells (j : Int) : (s.pop cf fr).cells j = (s.cells j).map (popCell s.next cf fr) := rfl

theorem none_iff (j : Int) : (s.pop cf fr).cells j = none ↔ s.cells j = none := by
  rw [cells]; cases s.cells j <;> simp

theorem valid (hv : s.valid) : (s.pop cf fr).valid := by
  intro i c hc
  rw [cells] at hc
  cases hs : s.cells i with
  | none => rw [hs] at hc; cases hc
  | some old =>
    rw [hs] at hc
    simp only [Option.map_some, Option.some.injEq] at hc
    subst hc
    obtain ⟨h1, h2, h3, h4⟩ := hv i old hs
    unfold popCell
    split
    · exact ⟨by show old.allocation ≤ s.next; omega, by show s.next < s.next + 1; omega, List.nodup_nil, by simp⟩
    · refine ⟨h1, by show old.grant < s.next + 1; omega, h3.filter _, fun hm => h4 (List.mem_filter.mp hm).1⟩

theorem progress : s.progress (s.pop cf fr) := by
  refine ⟨Nat.le_succ _, ?_⟩
  intro slot cell hc hlt
  rw [cells] at hc
  cases hs : s.cells slot with
  | none => rw [hs] at hc; cases hc
  | some old =>
    rw [hs] at hc
    simp only [Option.map_some, Option.some.injEq] at hc
    subst hc
    unfold popCell at hlt ⊢
    split at hlt
    · simp at hlt
    · rename_i hne
      simp only [hne, if_false]
      exact ⟨old, rfl, rfl, rfl⟩

theorem agrees {D : Deklaration} {A : FreiForm D} {σ : World D} (ha : s.agrees A σ) :
    (s.pop cf fr).agrees A σ := by
  refine ⟨valid ha.1, fun i => (ha.2 i).trans ?_⟩
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨popCell s.next cf fr c, by rw [cells, hc]; rfl⟩
  · rintro ⟨c, hc⟩
    cases hs : s.cells i with
    | none => rw [cells, hs] at hc; cases hc
    | some old => exact ⟨old, rfl⟩

/-- The thread `t` returns from activation `a + 1` to `a`. -/
def lower (depth : Nat → Nat) (t a : Nat) : Nat → Nat := fun u => if u = t then a else depth u

theorem frame_eq {f g : Frame} (ht : f.thread = g.thread) (ha : f.activation = g.activation) : f = g := by
  cases f; cases g; simp_all

variable {depth : Nat → Nat} {t a : Nat}

/-- **The discipline survives the return.** -/
theorem disciplined (hd : s.Disciplined depth) (hdepth : depth t = a + 1) :
    (s.pop ⟨t, a + 1⟩ ⟨t, a⟩).Disciplined (lower depth t a) := by
  have below : ∀ g : Frame, g.activation ≤ depth g.thread → g ≠ ⟨t, a + 1⟩ →
      g.activation ≤ lower depth t a g.thread := by
    intro g hg hne
    unfold lower
    split
    · rename_i hgt
      rw [hgt, hdepth] at hg
      have : g.activation ≠ a + 1 := fun he => hne (frame_eq hgt he)
      omega
    · exact hg
  intro i c hc
  rw [cells] at hc
  cases hs : s.cells i with
  | none => rw [hs] at hc; cases hc
  | some old =>
    rw [hs] at hc
    simp only [Option.map_some, Option.some.injEq] at hc
    subst hc
    obtain ⟨⟨hdeep, hsort⟩, hown, hloans⟩ := hd i old hs
    unfold popCell
    split
    · refine ⟨⟨by simp, by simp⟩, ?_, by simp⟩
      simp [lower]
    · rename_i hne
      refine ⟨⟨fun g hg => hdeep g ((List.mem_filter.mp hg).1), hsort.filter _⟩, below _ hown hne, ?_⟩
      intro g hg
      have hgne : g ≠ ⟨t, a + 1⟩ := by simpa using (List.mem_filter.mp hg).2
      exact below g (hloans g ((List.mem_filter.mp hg).1)) hgne

/-- **No other activation's view moves.** -/
theorem view_other (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {fr2 : Frame}
    (hne : fr2.thread ≠ t ∨ fr2.activation < a) :
    (s.pop ⟨t, a + 1⟩ ⟨t, a⟩).viewAt fr2 = s.viewAt fr2 := by
  apply View.viewAt_eq
  intro i
  rw [cells]
  cases hs : s.cells i with
  | none => rfl
  | some c =>
    simp only [Option.map_some, Option.bind_some]
    unfold popCell
    split
    · rename_i hcf
      have h1 : ¬ fr2.Sees ⟨c.allocation, s.next, ⟨t, a⟩, []⟩ := by
        rintro ⟨ht, hlt⟩
        simp at ht hlt
        rcases hne with h | h
        · exact h ht.symm
        · omega
      have h2 : ¬ fr2.Sees c := by
        rintro ⟨ht, hlt⟩
        rw [hcf] at ht hlt
        simp at ht hlt
        rcases hne with h | h
        · exact h ht.symm
        · omega
      simp [h1, h2]
    · rename_i hcf
      by_cases hsee : fr2.Sees c
      · have hsee' : fr2.Sees { c with loans := c.loans.filter (fun g => decide (g ≠ ⟨t, a + 1⟩)) } := hsee
        simp only [hsee, hsee', if_true, Option.some.injEq]
        simp only [Cell.at, Cell.mk.injEq, true_and]
        rw [List.filter_filter]
        apply List.filter_congr
        intro g hg
        have hdg := (hd i c hs).1.1 g hg
        by_cases hgcf : g = ⟨t, a + 1⟩
        · subst hgcf
          have hthr : (⟨t, a + 1⟩ : Frame).thread = fr2.thread := hdg.1.trans hsee.1
          have : fr2.Deeper ⟨t, a + 1⟩ := by
            refine ⟨hthr, ?_⟩
            rcases hne with h | h
            · exact absurd hthr.symm h
            · show fr2.activation < a + 1; omega
          simp [this]
        · simp [hgcf]
      · have hsee' : ¬ fr2.Sees { c with loans := c.loans.filter (fun g => decide (g ≠ ⟨t, a + 1⟩)) } := hsee
        rw [if_neg hsee, if_neg hsee']

end Pop

end Gabbro.Grammatik.ArenaOwnership.Machine
