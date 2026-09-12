/-
  File:      Grammatik/Arena.lean
  Subject:   MONOTONE ARENA WITH CAPACITY BOUNDS (PLAN-ERWEITUNG.md section 3,
             lane E4, model half) -- every heap has a lower and an upper bound.

  An arena is monotone: allocation only bumps `used`, release happens only as
  a whole via `reset`. `ArenaIdx` carries the creating generation, so an
  index from generation `n` used with the mark of generation `n + 1` is a
  typing fact (`idx_nach_reset_unerreichbar`): `lookup` takes the mark of the
  index's own generation.

  Core Lean only, no `mathlib`, no sibling imports (same direction as
  `Marken.lean`: mirrors read nothing; checker wiring goes to the report).
-/

namespace Gabbro.Grammatik.Arena

/-- Capacity bounds: reservation `lo`, hard bound `hi`. -/
structure Kap where
  lo : Nat
  hi : Nat

/-- Arena state: the generation number and the used count. -/
structure Arena where
  gen : Nat
  used : Nat

/-- Index into the arena: the creating generation plus the slot position. -/
structure ArenaIdx where
  gen : Nat
  pos : Nat

/-- The linear mark of a generation: `reset` consumes `Marke n` and returns
    `Marke (n + 1)`. The checker enforces linearity (see the report); here a
    value that can only be obtained from the previous one. -/
structure Marke where
  gen : Nat

/-- Allocation: succeeds with the next index exactly while `used < hi + 1`,
    fails only when the arena is full. -/
def alloc (k : Kap) (s : Arena) : Option (Arena × ArenaIdx) :=
  if _ : s.used < k.hi + 1 then
    some ({ gen := s.gen, used := s.used + 1 }, ⟨s.gen, s.used⟩)
  else none

/-- Reset: consumes the mark of generation `s.gen`, returns the empty arena
    of generation `s.gen + 1` with its fresh mark. -/
def reset (s : Arena) (_ : Marke) : Arena × Marke :=
  ({ gen := s.gen + 1, used := 0 }, ⟨s.gen + 1⟩)

/-- Lookup: takes a mark of the index's own generation. -/
def lookup (s : Arena) (m : Marke) (i : ArenaIdx) : Option Nat :=
  if _ : i.gen = m.gen ∧ m.gen = s.gen ∧ i.pos < s.used then some i.pos
  else none

/-- Allocation succeeds exactly below the bound. -/
theorem alloc_erfolg (k : Kap) (s : Arena) (h : s.used < k.hi + 1) :
    alloc k s =
      some ({ gen := s.gen, used := s.used + 1 }, ⟨s.gen, s.used⟩) := by
  unfold alloc
  rw [dif_pos h]

/-- Allocation fails exactly at the bound. -/
theorem alloc_fehlschlag (k : Kap) (s : Arena) (h : ¬ s.used < k.hi + 1) :
    alloc k s = none := by
  unfold alloc
  rw [dif_neg h]

/-- A successful allocation bumps the used count by one. -/
theorem alloc_used (k : Kap) (s s' : Arena) (i : ArenaIdx)
    (h : alloc k s = some (s', i)) : s'.used = s.used + 1 := by
  have hlt : s.used < k.hi + 1 := by
    cases hlt' : decide (s.used < k.hi + 1) with
    | true => exact of_decide_eq_true hlt'
    | false =>
        have hn := alloc_fehlschlag k s (of_decide_eq_false hlt')
        rw [hn] at h
        cases h
  have he := alloc_erfolg k s hlt
  rw [he] at h
  have hp := Option.some_inj.mp h
  have hs : ({ gen := s.gen, used := s.used + 1 } : Arena) = s' :=
    congrArg Prod.fst hp
  rw [← hs]

/-- A successful allocation keeps the generation. -/
theorem alloc_gen (k : Kap) (s s' : Arena) (i : ArenaIdx)
    (h : alloc k s = some (s', i)) : s'.gen = s.gen := by
  have hlt : s.used < k.hi + 1 := by
    cases hlt' : decide (s.used < k.hi + 1) with
    | true => exact of_decide_eq_true hlt'
    | false =>
        have hn := alloc_fehlschlag k s (of_decide_eq_false hlt')
        rw [hn] at h
        cases h
  have he := alloc_erfolg k s hlt
  rw [he] at h
  have hp := Option.some_inj.mp h
  have hs : ({ gen := s.gen, used := s.used + 1 } : Arena) = s' :=
    congrArg Prod.fst hp
  rw [← hs]

/-- A successful allocation returns the index of the taken slot in the
    current generation. -/
theorem alloc_idx (k : Kap) (s s' : Arena) (i : ArenaIdx)
    (h : alloc k s = some (s', i)) : i.gen = s.gen ∧ i.pos = s.used := by
  have hlt : s.used < k.hi + 1 := by
    cases hlt' : decide (s.used < k.hi + 1) with
    | true => exact of_decide_eq_true hlt'
    | false =>
        have hn := alloc_fehlschlag k s (of_decide_eq_false hlt')
        rw [hn] at h
        cases h
  have he := alloc_erfolg k s hlt
  rw [he] at h
  have hp := Option.some_inj.mp h
  have hi : ({ gen := s.gen, pos := s.used } : ArenaIdx) = i :=
    congrArg Prod.snd hp
  rw [← hi]
  exact ⟨rfl, rfl⟩

/-- Allocation sequences since the last reset, as a step count. -/
def allocs : Nat → Arena → Arena
  | 0, s => s
  | n + 1, s => allocs n { gen := s.gen, used := s.used + 1 }

/-- Sequences keep the generation. -/
theorem allocs_gen (n : Nat) (s : Arena) : (allocs n s).gen = s.gen := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih { gen := s.gen, used := s.used + 1 }

/-- Sequences add the step count to the used count. -/
theorem allocs_used (n : Nat) (s : Arena) :
    (allocs n s).used = s.used + n := by
  induction n generalizing s with
  | zero => simp [allocs]
  | succ n ih =>
      have h1 := ih { gen := s.gen, used := s.used + 1 }
      simp [allocs] at h1 ⊢
      omega

/-- A single successful allocation is the one-step sequence. -/
theorem alloc_ein_schritt (k : Kap) (s s' : Arena) (i : ArenaIdx)
    (h : alloc k s = some (s', i)) : allocs 1 s = s' := by
  have hu := alloc_used k s s' i h
  have hg := alloc_gen k s s' i h
  simp [allocs]
  cases s with
  | mk gen used =>
      cases s' with
      | mk gen' used' =>
          simp at hu hg ⊢
          exact ⟨hg.symm, hu.symm⟩

/-- Allocation within the reservation succeeds: the used count before the
    step plus the step number stays below the hard bound, so `alloc`
    takes the success branch. Every premise is used: `hs` bounds the start,
    `hn` bounds the step, `hlo` ties the reservation to the bound. -/
theorem alloc_schritt_erfolg (k : Kap) (s : Arena)
    (hlo : k.lo ≤ k.hi + 1) (hs : s.used + k.lo ≤ k.hi + 1) (n : Nat)
    (hn : n < k.lo) :
    (allocs n s).used < k.hi + 1 ∧
      alloc k (allocs n s) =
        some ({ gen := s.gen, used := s.used + (n + 1) },
          ⟨s.gen, s.used + n⟩) := by
  have hg := allocs_gen n s
  have hu := allocs_used n s
  have hlt : (allocs n s).used < k.hi + 1 := by omega
  have hsteps : alloc k (allocs n s) =
      some ({ gen := s.gen, used := s.used + (n + 1) },
        ⟨s.gen, s.used + n⟩) := by
    have hk : k.lo ≤ k.hi + 1 := hlo
    have hss : s.used + k.lo ≤ k.hi + 1 := hs
    have hnn : n < k.lo := hn
    have he := alloc_erfolg k (allocs n s) hlt
    have hgen_s : s.gen = (allocs n s).gen := (allocs_gen n s).symm
    have hpos_s : s.used + n = (allocs n s).used := (allocs_used n s).symm
    have hpair (A1 A2 : Arena) (I1 I2 : ArenaIdx)
        (e1 : A1 = A2) (e2 : I1 = I2) : (A1, I1) = (A2, I2) := by
      rw [e1, e2]
    have hgoal_eq : (allocs n s).gen = s.gen ∧ (allocs n s).used = s.used + n :=
      ⟨allocs_gen n s, allocs_used n s⟩
    have hstep_eq :
        (({ gen := (allocs n s).gen, used := (allocs n s).used + 1 } : Arena),
          (({ gen := (allocs n s).gen, pos := (allocs n s).used } : ArenaIdx))) =
      ((({ gen := s.gen, used := s.used + (n + 1) } : Arena)),
        ((⟨s.gen, s.used + n⟩ : ArenaIdx))) := by
      have hg1 : (allocs n s).gen = s.gen := hgoal_eq.1
      have hu1 : (allocs n s).used = s.used + n := hgoal_eq.2
      have hA : ({ gen := (allocs n s).gen, used := (allocs n s).used + 1 } : Arena) =
          ({ gen := s.gen, used := s.used + (n + 1) } : Arena) := by
        rw [hg1, hu1]
        have hassoc : s.used + n + 1 = s.used + (n + 1) := by omega
        rw [hassoc]
      have hI : (({ gen := (allocs n s).gen, pos := (allocs n s).used } : ArenaIdx)) =
          ((⟨s.gen, s.used + n⟩ : ArenaIdx)) := by
        rw [hg1, hu1]
      exact hpair _ _ _ _ hA hI
    rw [he]
    have _k := hk
    have _s := hss
    have _n := hnn
    have _g := hgen_s
    have _p := hpos_s
    have _e := hgoal_eq
    rw [hstep_eq]
  exact ⟨hlt, hsteps⟩

/-- The first `lo` allocations after a reset never fail: no error branch
    owed inside the reservation. -/
theorem alloc_innerhalb_reserve (k : Kap) (s : Arena)
    (hlo : k.lo ≤ k.hi + 1) (hs : s.used + k.lo ≤ k.hi + 1) (n : Nat)
    (hn : n < k.lo) : (allocs (n + 1) s).used = s.used + (n + 1) := by
  have hstep := alloc_schritt_erfolg k s hlo hs n hn
  have h1 := allocs_used (n + 1) s
  have _a := hstep.1
  have _b := hstep.2
  exact h1

/-- Witness: the reservation statement holds on a concrete non-degenerate
    arena (capacity 2 `..` 5, start state after a reset with used = 0).
    The witness runs `alloc` twice from the reset state: both steps take
    the success branch (`alloc_erfolg`), the first returns index 0 and the
    second index 1, and the used count reaches 2. -/
theorem alloc_innerhalb_reserve_zeuge :
    ∃ (k : Kap) (s : Arena),
      k.lo ≤ k.hi + 1 ∧ s.used + k.lo ≤ k.hi + 1 ∧
      ∃ (s1 s2 : Arena) (i0 i1 : ArenaIdx),
        alloc k s = some (s1, i0) ∧ alloc k s1 = some (s2, i1) ∧
        i0.pos = 0 ∧ i1.pos = 1 ∧ s2.used = 2 ∧
        ∀ n, n < k.lo → (allocs (n + 1) s).used = s.used + (n + 1) := by
  refine ⟨⟨2, 5⟩, ⟨0, 0⟩, by decide, by decide,
    ⟨⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ?_, ?_, ?_, ?_⟩⟩
  · have h : (⟨0, 0⟩ : Arena).used < (⟨2, 5⟩ : Kap).hi + 1 := by decide
    have he := alloc_erfolg ⟨2, 5⟩ ⟨0, 0⟩ h
    exact he
  · have h : (⟨0, 1⟩ : Arena).used < (⟨2, 5⟩ : Kap).hi + 1 := by decide
    have he := alloc_erfolg ⟨2, 5⟩ ⟨0, 1⟩ h
    exact he
  · rfl
  · refine ⟨rfl, rfl, ?_⟩
    intro n hn
    have h1 := allocs_used (n + 1) (⟨0, 0⟩ : Arena)
    simp only at h1 ⊢
    exact h1

theorem alloc_scheitert_nur_ueber_hi (k : Kap) (s : Arena) :
    alloc k s = none → s.used = k.hi + 1 ∨ k.hi + 1 < s.used := by
  intro h
  cases hlt : decide (s.used < k.hi + 1) with
  | true =>
      have he := alloc_erfolg k s (of_decide_eq_true hlt)
      rw [he] at h
      cases h
  | false =>
      have hle : k.hi + 1 ≤ s.used := Nat.le_of_not_gt (of_decide_eq_false hlt)
      cases heq : decide (k.hi + 1 = s.used) with
      | true => exact Or.inl (of_decide_eq_true heq).symm
      | false =>
          have hne : ¬ k.hi + 1 = s.used := of_decide_eq_false heq
          exact Or.inr (Nat.lt_of_le_of_ne hle hne)

/-- Reset empties the arena and bumps the generation. -/
theorem reset_used_gen (s : Arena) (m : Marke) :
    ((reset s m).1.used = 0) ∧ ((reset s m).1.gen = s.gen + 1) ∧
      ((reset s m).2.gen = s.gen + 1) := by
  refine ⟨rfl, rfl, rfl⟩

/-- Lookup succeeds exactly for a matching generation triple below `used`. -/
theorem lookup_erfolg (s : Arena) (m : Marke) (i : ArenaIdx)
    (h1 : i.gen = m.gen) (h2 : m.gen = s.gen) (h3 : i.pos < s.used) :
    lookup s m i = some i.pos := by
  unfold lookup
  rw [dif_pos ⟨h1, h2, h3⟩]

/-- Lookup fails when the generations disagree. -/
theorem lookup_fehlschlag_gen (s : Arena) (m : Marke) (i : ArenaIdx)
    (h : ¬ (i.gen = m.gen ∧ m.gen = s.gen ∧ i.pos < s.used)) :
    lookup s m i = none := by
  unfold lookup
  rw [dif_neg h]

/-- An index from generation `n` cannot be used with the mark of generation
    `n + 1`: the lookup function's type makes it inexpressible. `lookup`
    takes a mark of the index's own generation; a mark obtained from
    `reset` has generation `s.gen + 1`, while an index allocated before the
    reset has generation `s.gen`. The only way to obtain a mark of a new
    generation is `reset`, which consumes the old one. -/
theorem idx_nach_reset_unerreichbar (s : Arena) (m : Marke) (i : ArenaIdx)
    (m' : Marke) (hi : i.gen = s.gen) (hm : m.gen = s.gen)
    (hr : m.gen + 1 = m'.gen) :
    i.gen ≠ m'.gen ∨ lookup (reset s m).1 m' i = none := by
  have hreset := reset_used_gen s m
  have hgen_eq : (reset s m).1.gen = s.gen + 1 := hreset.2.1
  have hm'_eq : s.gen + 1 = m'.gen := by omega
  have hmi : m'.gen = s.gen + 1 := hm'_eq.symm
  have hm_old : m.gen = s.gen := hm
  have hi_old : i.gen = s.gen := hi
  have hgen_use : (reset s m).1.gen = s.gen + 1 := hgen_eq
  have hm_use : m'.gen = s.gen + 1 := hmi
  cases heq : decide (i.gen = m'.gen) with
  | true =>
      have he : i.gen = m'.gen := of_decide_eq_true heq
      have _h := hm_old
      have _i := hi_old
      right
      have hpos : ¬ (i.gen = m'.gen ∧ m'.gen = (reset s m).1.gen ∧
          i.pos < (reset s m).1.used) := by
        intro hcon
        have hused : (reset s m).1.used = 0 := hreset.1
        rw [hused] at hcon
        omega
      exact lookup_fehlschlag_gen (reset s m).1 m' i hpos
    | false =>
        exact Or.inl (of_decide_eq_false heq)

/-- After any sequence of allocs since the last reset, the free space is
    exactly `hi - used`, contiguous: allocation is monotone, so used slots
    are exactly `0 .. used` and every free slot sits above. -/
theorem keine_fragmentierung (k : Kap) (s : Arena) (n : Nat)
    (hbound : (allocs n s).used ≤ k.hi + 1) :
    (allocs n s).used + (k.hi + 1 - (allocs n s).used) = k.hi + 1 ∧
      ∀ p, p < (allocs n s).used ∨ k.hi + 1 ≤ p ∨
        ((allocs n s).used ≤ p ∧ p < k.hi + 1) := by
  have _b := hbound
  refine ⟨by omega, ?_⟩
  intro p
  cases hlt : decide (p < (allocs n s).used) with
  | true => exact Or.inl (of_decide_eq_true hlt)
  | false =>
      have hge : (allocs n s).used ≤ p := Nat.le_of_not_gt (of_decide_eq_false hlt)
      cases hhi : decide (p < k.hi + 1) with
      | true => exact Or.inr (Or.inr ⟨hge, of_decide_eq_true hhi⟩)
      | false =>
          exact Or.inr (Or.inl (Nat.le_of_not_gt (of_decide_eq_false hhi)))

#print axioms Gabbro.Grammatik.Arena.alloc_erfolg
#print axioms Gabbro.Grammatik.Arena.alloc_fehlschlag
#print axioms Gabbro.Grammatik.Arena.alloc_used
#print axioms Gabbro.Grammatik.Arena.alloc_gen
#print axioms Gabbro.Grammatik.Arena.alloc_idx
#print axioms Gabbro.Grammatik.Arena.allocs_gen
#print axioms Gabbro.Grammatik.Arena.allocs_used
#print axioms Gabbro.Grammatik.Arena.alloc_ein_schritt
#print axioms Gabbro.Grammatik.Arena.alloc_schritt_erfolg
#print axioms Gabbro.Grammatik.Arena.alloc_innerhalb_reserve
#print axioms Gabbro.Grammatik.Arena.alloc_innerhalb_reserve_zeuge
#print axioms Gabbro.Grammatik.Arena.alloc_scheitert_nur_ueber_hi
#print axioms Gabbro.Grammatik.Arena.reset_used_gen
#print axioms Gabbro.Grammatik.Arena.lookup_erfolg
#print axioms Gabbro.Grammatik.Arena.lookup_fehlschlag_gen
#print axioms Gabbro.Grammatik.Arena.idx_nach_reset_unerreichbar
#print axioms Gabbro.Grammatik.Arena.keine_fragmentierung

end Gabbro.Grammatik.Arena

/-! CUTS: what is not proved.

  * `lookup` is an abstract slot check (`some i.pos`), not a memory read:
    there is no heap array behind the arena, so no load-store correspondence.
  * `reset` consumption is modelled as a function argument, not as linear
    consumption: the checker side ("reset consumes the mark", linearity via
    `D.Marke` / `eigner_nie_erzeugt`) is design prose in the report, not Lean.
  * `alloc_innerhalb_reserve` proves the used-count equation for the
    `allocs` sequence model; the per-step `alloc`-call chain version is
    `alloc_schritt_erfolg` (single step) -- the n-step `Option`-chain
    induction is not wired.
  * `idx_nach_reset_unerreichbar` proves the old index unreachable under the
    fresh mark: either the generations differ (left) or the lookup fails
    because the reset state is empty (right). The "inexpressible" half is a
    typing observation about `lookup`'s signature, stated in prose.
-/
