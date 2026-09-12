/-
  File:      Grammatik/Arena.lean
  Subject:   MONOTONE ARENA WITH CAPACITY BOUNDS (PLAN-ERWEITUNG.md section 3,
             lane E4, model half) -- every heap has a lower and an upper bound.

  Typed model: the generation is a type index. `Arena k g` carries
  `used <= k.hi`; `ArenaIdx g n` is an index into the first `n` cells of
  generation `g`; `Marke g` is a token whose constructor is private, so only
  `start` and `reset` produce marks. `lookup` is total: a stale index
  (`ArenaIdx g n` against generation `g + 1`) does not typecheck.

  Core Lean only, no `mathlib`, no sibling imports (same direction as
  `Marken.lean`: mirrors read nothing; checker wiring goes to the report).
-/

namespace Gabbro.Grammatik.Arena

/-- Capacity bounds: reservation `lo`, hard bound `hi`. -/
structure Kap where
  lo : Nat
  hi : Nat

/-- Arena state of generation `g` under bound `k`: the used count never
    exceeds `hi` -- by construction, not by premise. -/
structure Arena (k : Kap) (g : Nat) where
  used : Nat
  hused : used ≤ k.hi

/-- Index into the first `n` cells of generation `g`. -/
structure ArenaIdx (g n : Nat) where
  i : Nat
  hi : i < n

/-- The linear mark of generation `g`: a token. The constructor is private
    to this module, so outside `start`/`reset` no mark can be made --
    see `reset_verbraucht`. -/
structure Marke (g : Nat) where
  private mk :: (dummy : Unit)

/-- The initial arena of generation 0 with its mark. -/
def start (k : Kap) : Arena k 0 × Marke 0 :=
  (⟨0, Nat.zero_le _⟩, Marke.mk ())

/-- Allocation: succeeds with the next index exactly while `used < hi`. -/
def alloc {k : Kap} {g : Nat} (a : Arena k g) :
    Option (Arena k g × ArenaIdx g (a.used + 1)) :=
  if h : a.used < k.hi then
    some (⟨a.used + 1, by omega⟩, ⟨a.used, by omega⟩)
  else none

/-- Reset: consumes the mark of generation `g`, returns the empty arena of
    generation `g + 1` with its fresh mark. -/
def reset {k : Kap} {g : Nat} (a : Arena k g) (m : Marke g) :
    Arena k (g + 1) × Marke (g + 1) :=
  (⟨0, Nat.zero_le _⟩, Marke.mk ())

/-- Lookup: total. Takes the mark of the index's own generation plus the
    proof that the index range is allocated; returns the slot. -/
def lookup {k : Kap} {g n : Nat} (a : Arena k g) (m : Marke g)
    (x : ArenaIdx g n) (h : n ≤ a.used) : Nat :=
  x.i

/-- Allocation succeeds exactly below the bound. -/
theorem alloc_erfolg {k : Kap} {g : Nat} (a : Arena k g)
    (h : a.used < k.hi) :
    alloc a = some (⟨a.used + 1, by omega⟩,
      (⟨a.used, by omega⟩ : ArenaIdx g (a.used + 1))) := by
  unfold alloc
  rw [dif_pos h]

/-- Allocation fails exactly at or above the bound. -/
theorem alloc_fehlschlag {k : Kap} {g : Nat} (a : Arena k g)
    (h : ¬ a.used < k.hi) : alloc a = none := by
  unfold alloc
  rw [dif_neg h]

/-- A successful allocation bumps the used count by one. -/
theorem alloc_used' {k : Kap} {g : Nat} (a : Arena k g)
    (p : Arena k g × ArenaIdx g (a.used + 1)) (h : alloc a = some p) :
    p.1.used = a.used + 1 := by
  have hlt : a.used < k.hi := by
    cases hlt' : decide (a.used < k.hi) with
    | true => exact of_decide_eq_true hlt'
    | false =>
        have hn := alloc_fehlschlag a (of_decide_eq_false hlt')
        rw [hn] at h
        cases h
  have he := alloc_erfolg a hlt
  rw [he] at h
  have hp := Option.some_inj.mp h
  have hs : (⟨a.used + 1, by omega⟩ : Arena k g) = p.1 :=
    congrArg Prod.fst hp
  rw [← hs]

/-- A successful allocation returns the taken slot. -/
theorem alloc_idx' {k : Kap} {g : Nat} (a : Arena k g)
    (p : Arena k g × ArenaIdx g (a.used + 1)) (h : alloc a = some p) :
    p.2.i = a.used := by
  have hlt : a.used < k.hi := by
    cases hlt' : decide (a.used < k.hi) with
    | true => exact of_decide_eq_true hlt'
    | false =>
        have hn := alloc_fehlschlag a (of_decide_eq_false hlt')
        rw [hn] at h
        cases h
  have he := alloc_erfolg a hlt
  rw [he] at h
  have hp := Option.some_inj.mp h
  have hs : (⟨a.used, by omega⟩ : ArenaIdx g (a.used + 1)) = p.2 :=
    congrArg Prod.snd hp
  rw [← hs]

/-- Allocation fails if and only if the arena is full. -/
theorem alloc_scheitert_gdw {k : Kap} {g : Nat} (a : Arena k g) :
    alloc a = none ↔ a.used = k.hi := by
  constructor
  · intro hnone
    cases hlt : decide (a.used < k.hi) with
    | true =>
        have he := alloc_erfolg a (of_decide_eq_true hlt)
        rw [he] at hnone
        cases hnone
    | false =>
        have hnge : ¬ a.used < k.hi := of_decide_eq_false hlt
        have hle : a.used ≤ k.hi := a.hused
        omega
  · intro heq
    have hnge : ¬ a.used < k.hi := by omega
    exact alloc_fehlschlag a hnge

/-- `n` successive allocations: iterates `alloc`, collecting the taken
    slot positions. Fails (`none`) at the first full arena. -/
def allocSeq {k : Kap} {g : Nat} (n : Nat) (a : Arena k g) :
    Option (Σ _ : Arena k g, List Nat) :=
  match n with
  | 0 => some ⟨a, []⟩
  | n + 1 =>
      match alloc a with
      | none => none
      | some p =>
          match allocSeq n p.1 with
          | none => none
          | some q => some ⟨q.1, p.2.i :: q.2⟩

/-- Successive allocations succeed whenever the arena holds them: the
    length is `n`, the used count grows by `n`, and the positions are
    exactly the contiguous block starting at the old used count. -/
theorem allocSeq_gelingt {k : Kap} {g : Nat} (b : Arena k g) (n : Nat)
    (h : b.used + n ≤ k.hi) :
    ∃ (b' : Arena k g) (l : List Nat),
      allocSeq n b = some ⟨b', l⟩ ∧ l.length = n ∧ b'.used = b.used + n ∧
        l = List.range' b.used n := by
  induction n generalizing b with
  | zero =>
      exact ⟨b, [], rfl, rfl, by omega, rfl⟩
  | succ n ih =>
      have hlt : b.used < k.hi := by omega
      have he := alloc_erfolg b hlt
      have hex : ∃ p : Arena k g × ArenaIdx g (b.used + 1),
          alloc b = some p := ⟨_, he⟩
      obtain ⟨p, hp⟩ := hex
      have hp1 : p.1.used = b.used + 1 := alloc_used' b p hp
      have hp2 : p.2.i = b.used := alloc_idx' b p hp
      have hu1 : p.1.used + n ≤ k.hi := by omega
      obtain ⟨b', l, hseq, hlen, hused', hrange⟩ := ih p.1 hu1
      have hstep : allocSeq (n + 1) b = some ⟨b', p.2.i :: l⟩ := by
        simp only [allocSeq, hp, hseq]
      refine ⟨b', p.2.i :: l, hstep, by simp [hlen], by omega, ?_⟩
      rw [hp2, hrange, hp1]
      rfl

/-- The first `lo` allocations after a reset never fail: iterating `alloc`
    from the reset state (used = 0) succeeds with `n` indices whenever
    `n ≤ lo ≤ hi`. -/
theorem alloc_innerhalb_reserve {k : Kap} {g : Nat} (a : Arena k g)
    (m : Marke g) (n : Nat) (hlo : k.lo ≤ k.hi) (hn : n ≤ k.lo) :
    ∃ (a' : Arena k (g + 1)) (l : List Nat),
      allocSeq n (reset a m).1 = some ⟨a', l⟩ ∧ l.length = n := by
  have h0 : (reset a m).1.used = 0 := rfl
  have hle : (reset a m).1.used + n ≤ k.hi := by omega
  obtain ⟨a', l, hseq, hlen, hused', hrange⟩ :=
    allocSeq_gelingt (reset a m).1 n hle
  exact ⟨a', l, hseq, hlen⟩

/-- No fragmentation: the `n` indices allocated after a reset are exactly
    `[0, 1, …, n-1]`. -/
theorem keine_fragmentierung {k : Kap} {g : Nat} (a : Arena k g)
    (m : Marke g) (n : Nat) (hlo : k.lo ≤ k.hi) (hn : n ≤ k.lo) :
    ∃ (a' : Arena k (g + 1)) (l : List Nat),
      allocSeq n (reset a m).1 = some ⟨a', l⟩ ∧ l = List.range n := by
  have h0 : (reset a m).1.used = 0 := rfl
  have hle : (reset a m).1.used + n ≤ k.hi := by omega
  obtain ⟨a', l, hseq, hlen, hused', hrange⟩ :=
    allocSeq_gelingt (reset a m).1 n hle
  have hrr : l = List.range n := by
    rw [hrange, h0]
    exact List.range_eq_range'.symm
  exact ⟨a', l, hseq, hrr⟩

/-- Witness: with `lo = 2`, `hi = 4`, two allocations after a reset succeed
    and return indices 0 and 1. -/
theorem alloc_innerhalb_reserve_zeuge :
    ∃ (a' : Arena (⟨2, 4⟩ : Kap) 1) (l : List Nat),
      allocSeq 2 (reset (start (⟨2, 4⟩ : Kap)).1
        (start (⟨2, 4⟩ : Kap)).2).1 = some ⟨a', l⟩ ∧ l = [0, 1] := by
  refine ⟨⟨2, by decide⟩, [0, 1], by rfl, rfl⟩

/-- Reset empties the arena. -/
theorem reset_used {k : Kap} {g : Nat} (a : Arena k g) (m : Marke g) :
    (reset a m).1.used = 0 := rfl

/-- Reset consumes the mark: the fresh mark of generation `g + 1` equals any
    mark of that generation -- marks carry no identity beyond their type
    index, and the constructor is private, so outside this module the only
    way to obtain a `Marke (g + 1)` is `start`/`reset`. -/
theorem reset_verbraucht {k : Kap} {g : Nat} (a : Arena k g) (m : Marke g)
    (m' : Marke (g + 1)) : (reset a m).2 = m' := by
  cases (reset a m).2
  cases m'
  rfl

/-- Lookup returns the slot, inside the allocated range. -/
theorem lookup_gilt {k : Kap} {g n : Nat} (a : Arena k g) (m : Marke g)
    (x : ArenaIdx g n) (h : n ≤ a.used) :
    lookup a m x h = x.i ∧ x.i < a.used + 1 := by
  have hx : x.i < n := x.hi
  refine ⟨rfl, ?_⟩
  show x.i < a.used + 1
  omega

#print axioms Gabbro.Grammatik.Arena.alloc_erfolg
#print axioms Gabbro.Grammatik.Arena.alloc_fehlschlag
#print axioms Gabbro.Grammatik.Arena.alloc_used'
#print axioms Gabbro.Grammatik.Arena.alloc_idx'
#print axioms Gabbro.Grammatik.Arena.alloc_scheitert_gdw
#print axioms Gabbro.Grammatik.Arena.allocSeq_gelingt
#print axioms Gabbro.Grammatik.Arena.alloc_innerhalb_reserve
#print axioms Gabbro.Grammatik.Arena.keine_fragmentierung
#print axioms Gabbro.Grammatik.Arena.alloc_innerhalb_reserve_zeuge
#print axioms Gabbro.Grammatik.Arena.reset_used
#print axioms Gabbro.Grammatik.Arena.reset_verbraucht
#print axioms Gabbro.Grammatik.Arena.lookup_gilt

end Gabbro.Grammatik.Arena

/-! CUTS: what is not proved.

  * "No index survives a reset" is a TYPE fact, not a theorem: `lookup`
    takes `Marke g` and `ArenaIdx g n` at the same `g`, so an
    `ArenaIdx g n` cannot be passed where `ArenaIdx (g + 1) n` is expected
    -- Lean rejects the application at typecheck. A theorem stating this
    would have to exhibit the ill-typed term, which is impossible; what is
    proved instead is `reset_verbraucht` (the fresh mark equals any mark of
    the new generation) with the constructor private, so no stale mark can
    be forged outside this module.
  * `lookup` returns the slot position (`x.i`), not a stored value: there is
    no heap array behind the arena, so no load-store correspondence.
  * Linearity ("reset consumes the mark") is carried by the types `Marke g`
    vs `Marke (g + 1)` plus the private constructor; the checker's `Λ`
    bookkeeping (`Stmt.retires`) is design prose in the report, not Lean.
-/

