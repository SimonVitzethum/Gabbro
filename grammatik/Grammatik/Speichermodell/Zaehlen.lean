/-
  File:      Grammatik/Speichermodell/Zaehlen.lean
  Subject:   Lean groundwork for COUNT AS A PREDICATE (agent 03,
             usability team).

  Finding G6 of `messung/SPRACHE-EFFIZIENZ.md`: `count k in slots
  of T : p` exists as a computation but not inside an `invariant` /
  `spec fn`, so a refcount invariant ("refcount equals the number of
  slots pointing at it") cannot be stated. This file proves, over any
  slot predicate and with no program named: bounds (`zaehle_le`),
  emptiness/fullness characterisations (`zaehle_null_iff`,
  `zaehle_voll_iff`), monotonicity (`zaehle_mono`), the windowed
  split (`zaehle_add`), the single-slot update laws
  (`zaehle_schreibe` and its equal/plus/minus-one corollaries), and
  the refcount transfer (`refcount_erhalten`). `zaehle` is defined by
  recursion (the task's blessed fallback: no `List.countP` API names
  needed). No Arm instruction facts (rule 7 N/A, recorded in CUTS).
-/
import Init

namespace Grammatik.Speichermodell.Zaehlen

/-- The number of indices `k < n` with `p k` (by recursion, not
    `List.countP`). -/
def zaehle (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => zaehle p n + (if p n then 1 else 0)

/-! ## 2. Bounds, emptiness, fullness, monotonicity. -/

/-- A count never exceeds the range. -/
theorem zaehle_le (p : Nat → Bool) (n : Nat) : zaehle p n ≤ n := by
  induction n with
  | zero => simp [zaehle]
  | succ n ih =>
      cases hn : p n with
      | true =>
          have e : zaehle p (n + 1) = zaehle p n + 1 := by simp [zaehle, hn]
          omega
      | false =>
          have e : zaehle p (n + 1) = zaehle p n := by simp [zaehle, hn]
          omega

/-- Zero count means no index satisfies `p`. -/
theorem zaehle_null_iff (p : Nat → Bool) (n : Nat) :
    zaehle p n = 0 ↔ ∀ k < n, p k = false := by
  induction n with
  | zero =>
      constructor
      · intro h k hk
        exact absurd hk (by omega)
      · intro h
        rfl
  | succ n ih =>
      constructor
      · intro h k hk
        cases hn : p n with
        | true =>
            have e : zaehle p (n + 1) = zaehle p n + 1 := by simp [zaehle, hn]
            exfalso
            omega
        | false =>
            have e : zaehle p (n + 1) = zaehle p n := by simp [zaehle, hn]
            have hz : zaehle p n = 0 := by rw [e] at h; exact h
            by_cases hks : k = n
            · rw [hks]
              exact hn
            · exact (ih.mp hz) k (by omega)
      · intro h
        have hn : p n = false := h n (by omega)
        have hz : zaehle p n = 0 := ih.mpr (fun k hk => h k (by omega))
        simp [zaehle, hn, hz]

/-- Full count means every index satisfies `p`. -/
theorem zaehle_voll_iff (p : Nat → Bool) (n : Nat) :
    zaehle p n = n ↔ ∀ k < n, p k = true := by
  induction n with
  | zero =>
      constructor
      · intro h k hk
        exact absurd hk (by omega)
      · intro h
        rfl
  | succ n ih =>
      constructor
      · intro h k hk
        cases hn : p n with
        | true =>
            have e : zaehle p (n + 1) = zaehle p n + 1 := by simp [zaehle, hn]
            by_cases hks : k = n
            · rw [hks]
              exact hn
            · have hz : zaehle p n = n := by omega
              exact (ih.mp hz) k (by omega)
        | false =>
            have e : zaehle p (n + 1) = zaehle p n := by simp [zaehle, hn]
            have hle := zaehle_le p n
            exfalso
            omega
      · intro h
        have hn : p n = true := h n (by omega)
        have hz : zaehle p n = n := ih.mpr (fun k hk => h k (by omega))
        simp [zaehle, hn, hz]

/-- Pointwise implication lifts to counts. -/
theorem zaehle_mono (p q : Nat → Bool) (n : Nat)
    (h : ∀ k < n, p k = true → q k = true) :
    zaehle p n ≤ zaehle q n := by
  induction n with
  | zero => simp [zaehle]
  | succ n ih =>
      cases hn : p n with
      | true =>
          have hqn : q n = true := h n (by omega) hn
          have e1 : zaehle p (n + 1) = zaehle p n + 1 := by simp [zaehle, hn]
          have e2 : zaehle q (n + 1) = zaehle q n + 1 := by simp [zaehle, hqn]
          have ih' := ih (fun k hk => h k (by omega))
          omega
      | false =>
          have e1 : zaehle p (n + 1) = zaehle p n := by simp [zaehle, hn]
          have e2 : zaehle q (n + 1) = zaehle q n + (if q n then 1 else 0) := by
            simp [zaehle]
          have ih' := ih (fun k hk => h k (by omega))
          omega

/-! ## 3. Splitting and agreement. -/

/-- Agreement on a range means equal counts. -/
theorem zaehle_gleich (p q : Nat → Bool) (n : Nat)
    (h : ∀ k < n, q k = p k) : zaehle q n = zaehle p n := by
  induction n with
  | zero => simp [zaehle]
  | succ n ih =>
      have hqn : q n = p n := h n (by omega)
      have e1 : zaehle q (n + 1) = zaehle q n + (if q n then 1 else 0) := by
        simp [zaehle]
      have e2 : zaehle p (n + 1) = zaehle p n + (if p n then 1 else 0) := by
        simp [zaehle]
      have ih' := ih (fun k hk => h k (by omega))
      rw [hqn] at e1
      omega

/-- **Windowed split**: counting `m + n` is the head count plus the
    shifted tail count (the hold-sized scan). -/
theorem zaehle_add (p : Nat → Bool) (m n : Nat) :
    zaehle p (m + n) = zaehle p m + zaehle (fun k => p (m + k)) n := by
  induction n generalizing m with
  | zero => simp [zaehle]
  | succ n ih =>
      have e : m + (n + 1) = (m + n) + 1 := by omega
      rw [e]
      simp only [zaehle]
      have ihr := ih m
      omega

/-! ## 4. Single-slot updates. -/

/-- **The update law**: if `q` agrees with `p` everywhere below `n`
    except possibly at `j`, the counts differ only by the two
    single-slot contributions. This is what makes a count invariant
    maintainable by one write. -/
theorem zaehle_schreibe (p q : Nat → Bool) (n j : Nat) (hjn : j < n)
    (h : ∀ k < n, k ≠ j → q k = p k) :
    zaehle q n + (if p j then 1 else 0) =
      zaehle p n + (if q j then 1 else 0) := by
  induction n with
  | zero => omega
  | succ n ih =>
      have h' : ∀ k < n, k ≠ j → q k = p k :=
        fun k hk hkj => h k (by omega) hkj
      by_cases hnj : n = j
      · rw [hnj]
        have e1 : zaehle q (j + 1) = zaehle q j + (if q j then 1 else 0) := by
          simp [zaehle]
        have e2 : zaehle p (j + 1) = zaehle p j + (if p j then 1 else 0) := by
          simp [zaehle]
        have heq : zaehle q j = zaehle p j :=
          zaehle_gleich p q j (fun k hk => h k (by omega) (by omega))
        omega
      · have hjn' : j < n := by omega
        have ih' := ih hjn' h'
        have hqn : q n = p n := h n (by omega) hnj
        have e1 : zaehle q (n + 1) = zaehle q n + (if q n then 1 else 0) := by
          simp [zaehle]
        have e2 : zaehle p (n + 1) = zaehle p n + (if p n then 1 else 0) := by
          simp [zaehle]
        rw [hqn] at e1
        omega

/-- Equal at the written slot: the count is unchanged. -/
theorem zaehle_schreibe_gleich (p q : Nat → Bool) (n j : Nat)
    (hjn : j < n) (h : ∀ k < n, k ≠ j → q k = p k)
    (heq : q j = p j) :
    zaehle q n = zaehle p n := by
  have h0 := zaehle_schreibe p q n j hjn h
  rw [heq] at h0
  omega

/-- `false → true`: the count grows by exactly one. -/
theorem zaehle_schreibe_plus_eins (p q : Nat → Bool) (n j : Nat)
    (hjn : j < n) (h : ∀ k < n, k ≠ j → q k = p k)
    (hpj : p j = false) (hqj : q j = true) :
    zaehle q n = zaehle p n + 1 := by
  have h0 := zaehle_schreibe p q n j hjn h
  have e0 : (if false then (1 : Nat) else 0) = 0 := rfl
  have e1 : (if true then (1 : Nat) else 0) = 1 := rfl
  rw [hpj, hqj, e0, e1] at h0
  omega

/-- `true → false`: the count shrinks by exactly one. -/
theorem zaehle_schreibe_minus_eins (p q : Nat → Bool) (n j : Nat)
    (hjn : j < n) (h : ∀ k < n, k ≠ j → q k = p k)
    (hpj : p j = true) (hqj : q j = false) :
    zaehle q n + 1 = zaehle p n := by
  have h0 := zaehle_schreibe p q n j hjn h
  have e0 : (if false then (1 : Nat) else 0) = 0 := rfl
  have e1 : (if true then (1 : Nat) else 0) = 1 := rfl
  rw [hpj, hqj, e0, e1] at h0
  omega

/-! ## 5. The refcount transfer. -/

/-- **Refcount preserved by one slot update**: changing only slot
    `j` from `a` to `b` moves the count by the two single-slot
    contributions — from `zaehle_schreibe`, stated without
    subtraction. -/
theorem refcount_erhalten (ziel ziel' : Nat → Nat) (t : Nat)
    (n j a b refcount : Nat) (hjn : j < n)
    (ha : ziel j = a) (hb : ziel' j = b)
    (hothers : ∀ k, k ≠ j → ziel' k = ziel k)
    (href : refcount = zaehle (fun k => decide (ziel k = t)) n) :
    zaehle (fun k => decide (ziel' k = t)) n +
        (if a = t then 1 else 0) =
      refcount + (if b = t then 1 else 0) := by
  have h := zaehle_schreibe (fun k => decide (ziel k = t))
    (fun k => decide (ziel' k = t)) n j hjn (by
      intro k _ hkj
      show decide (ziel' k = t) = decide (ziel k = t)
      rw [hothers k hkj])
  have e1 : (if ziel j = t then (1 : Nat) else 0) =
      (if a = t then 1 else 0) := by
    rw [ha]
  have e2 : (if ziel' j = t then (1 : Nat) else 0) =
      (if b = t then 1 else 0) := by
    rw [hb]
  simp at h
  rw [e1, e2] at h
  omega

/-! ## 6. Witnesses: parities, splits, single writes, refcounts. -/

/-- Three evens below 6. -/
theorem wit_zaehle_parity : zaehle (fun k => k % 2 == 0) 6 = 3 := by decide

/-- The windowed split at 2 + 4 on evens. -/
theorem wit_add : zaehle (fun k => k % 2 == 0) (2 + 4) =
    zaehle (fun k => k % 2 == 0) 2 + zaehle (fun k => (2 + k) % 2 == 0) 4 :=
  zaehle_add (fun k => k % 2 == 0) 2 4

/-- Flipping slot 1 off→on grows the even-count 3 → 4. -/
theorem wit_schreibe : zaehle (fun k => k % 2 == 0 || k == 1) 5 =
    zaehle (fun k => k % 2 == 0) 5 + 1 :=
  zaehle_schreibe_plus_eins (fun k => k % 2 == 0)
    (fun k => k % 2 == 0 || k == 1) 5 1 (by decide) (by decide) (by decide)
    (by decide)

/-- The full update law on the same flip. -/
theorem wit_schreibe_allg :
    zaehle (fun k => k % 2 == 0 || k == 1) 5 +
        (if (fun k => k % 2 == 0) 1 then 1 else 0) =
      zaehle (fun k => k % 2 == 0) 5 +
        (if (fun k => k % 2 == 0 || k == 1) 1 then 1 else 0) :=
  zaehle_schreibe (fun k => k % 2 == 0) (fun k => k % 2 == 0 || k == 1) 5 1
    (by decide) (by decide)

/-- Refcount 3 with one `7`, refcount 2 with two. -/
theorem wit_refcount :
    let ziel : Nat → Nat := fun k => if k = 1 then 7 else 0
    let ziel' : Nat → Nat := fun k => if k = 2 then 7 else ziel k
    zaehle (fun k => decide (ziel k = 0)) 4 = 3 ∧
      zaehle (fun k => decide (ziel' k = 0)) 4 = 2 := by
  decide

/-- The refcount fixture: one `7` at slot 1. -/
def zielWit : Nat → Nat := fun k => if k = 1 then 7 else 0

/-- The refcount fixture after writing `7` at slot 2. -/
def zielWit' : Nat → Nat := fun k => if k = 2 then 7 else zielWit k

/-- The transfer moves 3 → 2 across the slot-2 write. -/
theorem wit_refcount_transfer :
    zaehle (fun k => decide (zielWit' k = 0)) 4 +
        (if (0 : Nat) = 0 then 1 else 0) =
      3 + (if (7 : Nat) = 0 then 1 else 0) :=
  refcount_erhalten zielWit zielWit' 0 4 2 0 7 3 (by decide) rfl rfl
    (fun k hkj => by simp only [zielWit']; rw [if_neg hkj]) (by decide)

end Grammatik.Speichermodell.Zaehlen

/-
CUTS: what is not proved or not covered.
  - Proved: counting by recursion (`zaehle`), bounds and
    characterisations (`zaehle_le`, `zaehle_null_iff`,
    `zaehle_voll_iff`), monotonicity (`zaehle_mono`), agreement
    (`zaehle_gleich`), the windowed split (`zaehle_add`), the
    single-slot update laws (`zaehle_schreibe` with the equal/
    plus-one/minus-one corollaries), the refcount transfer
    (`refcount_erhalten`), and decide witnesses (parity 3, split
    at 2+4, the slot-1 flip 3→4, refcounts 3 and 2 with the
    transfer).
  - NOT proved: predicate syntax in the language (no `count`
    surface); the checker rule naming the counted domain; the
    exporter form (the language form is the next step and needs
    the invariant language to name the counted domain).
  - Rule 7 (Sail citations) is N/A: pure `Nat`/`Bool` counting
    logic, no Arm instruction semantics (confidence: definitional).
-/

#print axioms Grammatik.Speichermodell.Zaehlen.zaehle_le
#print axioms Grammatik.Speichermodell.Zaehlen.zaehle_null_iff
#print axioms Grammatik.Speichermodell.Zaehlen.zaehle_voll_iff
#print axioms Grammatik.Speichermodell.Zaehlen.zaehle_mono
#print axioms Grammatik.Speichermodell.Zaehlen.zaehle_gleich
#print axioms Grammatik.Speichermodell.Zaehlen.zaehle_add
#print axioms Grammatik.Speichermodell.Zaehlen.zaehle_schreibe
#print axioms Grammatik.Speichermodell.Zaehlen.zaehle_schreibe_gleich
#print axioms Grammatik.Speichermodell.Zaehlen.zaehle_schreibe_plus_eins
#print axioms Grammatik.Speichermodell.Zaehlen.zaehle_schreibe_minus_eins
#print axioms Grammatik.Speichermodell.Zaehlen.refcount_erhalten
#print axioms Grammatik.Speichermodell.Zaehlen.wit_zaehle_parity
#print axioms Grammatik.Speichermodell.Zaehlen.wit_add
#print axioms Grammatik.Speichermodell.Zaehlen.wit_schreibe
#print axioms Grammatik.Speichermodell.Zaehlen.wit_schreibe_allg
#print axioms Grammatik.Speichermodell.Zaehlen.wit_refcount
#print axioms Grammatik.Speichermodell.Zaehlen.wit_refcount_transfer
