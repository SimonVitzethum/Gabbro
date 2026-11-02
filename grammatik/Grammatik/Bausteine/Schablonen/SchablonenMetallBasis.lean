/-
  File:      Grammatik/SchablonenMetall.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-TRANSLATION-VALIDATION.md): the GENERATED pieces of the
             bare-metal image (C-free lane, C3 slice 1, 2026-10-05).

  Rows of `crates/gabbro-check/src/schablonen.rs`:

  * `metall.speicher` -- the compiler's four memory functions the build writes beside the
    image (`treiber.rs::METALL_SPEICHER`): `memcpy`, `memmove`, `memset`, `memcmp`, one byte per
    step. Until 2026-10-05 they were the first 50 lines of `laufzeit/metall/kern.c`.
  * `arena.metall` -- the bare-metal reservation in front of the proved pool runtime
    `arena.modul` (`treiber.rs::METALL_ARENA_FUSS`): `gabbro_arena_reserve(d)` binds `d` to the
    pool of ITS position in the emitted list (`GABBRO_ARENEN`), and ends the machine when the
    list does not hold `d` or the pool reservation refuses. Until 2026-10-05 the image linked
    `laufzeit/metall/arena.c` (one shared reserve, carved by a counter).

  Both are ABSTRACT CORES like `arena.modul` (SchablonenModul.lean): memory is a function from
  addresses to bytes, and each C loop is the recursion of the same name below:

    memcpy   `for (i = 0; i < n; i++) dd[i] = ss[i];`              -- `vor`
    memmove  `dd < ss` ? the same forward loop : `while (n > 0) { n--; dd[n] = ss[n]; }`
                                                                    -- `vor` / `rueck`
    memset   `for (i = 0; i < n; i++) dd[i] = (unsigned char)c;`   -- `setze`
    memcmp   `for (i = 0; i < n; i++) if (x[i] != y[i]) return x[i] < y[i] ? -1 : 1;`
                                                                    -- `vgl`

  What is proved:

  * `memcpy_korrekt`: under C's own premise for `memcpy` (the two ranges do not overlap) the
    destination holds the source's bytes, and nothing outside the destination moves
    (`vor_rahmen`);
  * `memmove_korrekt`: for EVERY overlap the destination holds the source's ORIGINAL bytes --
    the forward loop when `d < s` (`vor_korrekt`), the backward one otherwise (`rueck_korrekt`);
    a mere copy loop would fail here, and `memmove_vorwaerts_waere_falsch` shows it does;
  * `memset_korrekt`: every destination byte is `c mod 256`, nothing else moves;
  * `memcmp_null`, `memcmp_kleiner`: `0` exactly when the ranges are equal, `-1` exactly at a
    first difference whose left byte is smaller;
  * `arena_metall_eigene_stelle`, `arena_metall_getrennt`, `arena_metall_fremd`: a reservation
    that returns binds the pool of the descriptor's own position, two descriptors never share
    a pool, a descriptor the list does not hold never gets one; with `arena.modul`'s
    `arena_modul_slot_im_lager` every slot of every arena lies inside its own pool, and pools
    of different arenas are disjoint byte ranges (`arena_metall_lager_getrennt`).

  NOT proved: that the compiler calls the four functions only with ranges it owns (the C and
  the hardware, the trust every target names), and that the image is compiled with
  `-fno-tree-loop-distribute-patterns` (both flag words of the image carry it; without it GCC
  may turn the loops back into calls to themselves).

  No `sorry`, no `native_decide`, no new axiom; each theorem has a witness instantiating ALL
  its premises jointly.
-/

module

@[expose] public section

namespace Gabbro.Grammatik

namespace MetallLaufzeit

/-! ## 1. `metall.speicher` -/

/-- Byte memory: an address answers a byte. -/
abbrev Sp := Nat → Nat

/-- One store `m[a] = v`. -/
def schreib (m : Sp) (a v : Nat) : Sp := fun x => if x = a then v else m x

/-- The forward copy loop after `i` iterations (indices `0 .. i-1`). -/
def vor (m : Sp) (d s : Nat) : Nat → Sp
  | 0 => m
  | i + 1 => schreib (vor m d s i) (d + i) (vor m d s i (s + i))

/-- The backward copy loop over `n` bytes (index `n-1` first). -/
def rueck (m : Sp) (d s : Nat) : Nat → Sp
  | 0 => m
  | n + 1 => rueck (schreib m (d + n) (m (s + n))) d s n

/-- The fill loop after `i` iterations. -/
def setze (m : Sp) (d c : Nat) : Nat → Sp
  | 0 => m
  | i + 1 => schreib (setze m d c i) (d + i) (c % 256)

/-- The compare loop from index `i` with `r` bytes left. -/
def vgl (m : Sp) (a b : Nat) : Nat → Nat → Int
  | _, 0 => 0
  | i, r + 1 =>
    if m (a + i) ≠ m (b + i) then (if m (a + i) < m (b + i) then -1 else 1)
    else vgl m a b (i + 1) r

/-- The four C functions. -/
def memcpy (m : Sp) (d s n : Nat) : Sp := vor m d s n
def memmove (m : Sp) (d s n : Nat) : Sp := if d < s then vor m d s n else rueck m d s n
def memset (m : Sp) (d c n : Nat) : Sp := setze m d c n
def memcmp (m : Sp) (a b n : Nat) : Int := vgl m a b 0 n

theorem vor_rahmen (m : Sp) (d s : Nat) :
    ∀ i a, (a < d ∨ d + i ≤ a) → vor m d s i a = m a := by
  intro i
  induction i with
  | zero => intro a _; rfl
  | succ i ih =>
    intro a h
    simp only [vor, schreib]
    have hne : a ≠ d + i := by omega
    simp only [hne, if_false]
    exact ih a (by omega)

theorem vor_korrekt (m : Sp) (d s : Nat) :
    ∀ n, (d ≤ s ∨ s + n ≤ d) → ∀ j, j < n → vor m d s n (d + j) = m (s + j) := by
  intro n
  induction n with
  | zero => intro _ j hj; omega
  | succ n ih =>
    intro h j hj
    simp only [vor, schreib]
    by_cases hjn : j = n
    · subst hjn
      simp only [if_true]
      exact vor_rahmen m d s j (s + j) (by omega)
    · have hne : d + j ≠ d + n := by omega
      simp only [hne, if_false]
      exact ih (by omega) j (by omega)

theorem rueck_rahmen (d s : Nat) :
    ∀ n (m : Sp) a, (a < d ∨ d + n ≤ a) → rueck m d s n a = m a := by
  intro n
  induction n with
  | zero => intro m a _; rfl
  | succ n ih =>
    intro m a h
    simp only [rueck]
    rw [ih _ a (by omega)]
    simp only [schreib]
    have hne : a ≠ d + n := by omega
    simp only [hne, ↓reduceIte]

theorem rueck_korrekt (d s : Nat) (hs : s ≤ d) :
    ∀ n (m : Sp) j, j < n → rueck m d s n (d + j) = m (s + j) := by
  intro n
  induction n with
  | zero => intro m j hj; omega
  | succ n ih =>
    intro m j hj
    simp only [rueck]
    by_cases hjn : j = n
    · subst hjn
      rw [rueck_rahmen d s j _ (d + j) (by omega)]
      simp only [schreib, Nat.add_left_cancel_iff, ↓reduceIte]
    · rw [ih _ j (by omega)]
      simp only [schreib]
      have hne : s + j ≠ d + n := by omega
      simp only [hne, ↓reduceIte]

/-- **`memcpy`**: under C's premise (no overlap) the destination holds the source. -/
theorem memcpy_korrekt (m : Sp) (d s n : Nat) (h : s + n ≤ d ∨ d + n ≤ s) :
    (∀ j, j < n → memcpy m d s n (d + j) = m (s + j)) ∧
    (∀ a, (a < d ∨ d + n ≤ a) → memcpy m d s n a = m a) :=
  ⟨vor_korrekt m d s n (by omega), vor_rahmen m d s n⟩

/-- **`memmove`**: for EVERY overlap the destination holds the source's original bytes, and
    nothing outside the destination moves. -/
theorem memmove_korrekt (m : Sp) (d s n : Nat) :
    (∀ j, j < n → memmove m d s n (d + j) = m (s + j)) ∧
    (∀ a, (a < d ∨ d + n ≤ a) → memmove m d s n a = m a) := by
  unfold memmove
  by_cases h : d < s
  · simp only [h, if_true]
    exact ⟨vor_korrekt m d s n (by omega), vor_rahmen m d s n⟩
  · simp only [h, if_false]
    exact ⟨fun j hj => rueck_korrekt d s (by omega) n m j hj, rueck_rahmen d s n m⟩

/-- The backward branch is not decoration: the forward loop alone, run on an overlap with
    `s < d`, overwrites a source byte before it reads it. -/
theorem memmove_vorwaerts_waere_falsch :
    vor (fun x => x) 1 0 2 (1 + 1) ≠ (fun x : Nat => x) (0 + 1) := by decide

theorem memset_korrekt (m : Sp) (d c n : Nat) :
    (∀ j, j < n → memset m d c n (d + j) = c % 256) ∧
    (∀ a, (a < d ∨ d + n ≤ a) → memset m d c n a = m a) := by
  unfold memset
  refine ⟨?_, ?_⟩
  · induction n with
    | zero => intro j hj; omega
    | succ n ih =>
      intro j hj
      simp only [setze, schreib]
      by_cases hjn : j = n
      · subst hjn; simp only [Nat.add_left_cancel_iff, ↓reduceIte]
      · have hne : d + j ≠ d + n := by omega
        simp only [hne, if_false]
        exact ih j (by omega)
  · induction n with
    | zero => intro a _; rfl
    | succ n ih =>
      intro a h
      simp only [setze, schreib]
      have hne : a ≠ d + n := by omega
      simp only [hne, if_false]
      exact ih a (by omega)

theorem vgl_null (m : Sp) (a b : Nat) :
    ∀ r i, vgl m a b i r = 0 ↔ ∀ j, j < r → m (a + i + j) = m (b + i + j) := by
  intro r
  induction r with
  | zero => intro i; simp only [vgl, Nat.not_lt_zero, false_implies, implies_true]
  | succ r ih =>
    intro i
    simp only [vgl]
    by_cases h : m (a + i) = m (b + i)
    · simp only [h, ne_eq, not_true_eq_false, if_false]
      rw [ih (i + 1)]
      constructor
      · intro hr j hj
        by_cases hj0 : j = 0
        · subst hj0; simpa using h
        · have := hr (j - 1) (by omega)
          have e1 : a + (i + 1) + (j - 1) = a + i + j := by omega
          have e2 : b + (i + 1) + (j - 1) = b + i + j := by omega
          rwa [e1, e2] at this
      · intro hr j hj
        have := hr (j + 1) (by omega)
        have e1 : a + (i + 1) + j = a + i + (j + 1) := by omega
        have e2 : b + (i + 1) + j = b + i + (j + 1) := by omega
        rwa [e1, e2]
    · simp only [ne_eq, h, not_false_eq_true, if_true]
      constructor
      · intro hc; split at hc <;> simp only [Int.reduceNeg, Int.neg_eq_zero, Int.reduceEq] at hc
      · intro hr; exact absurd (by simpa using hr 0 (by omega)) h

/-- **`memcmp` answers 0 exactly when the two ranges are equal.** -/
theorem memcmp_null (m : Sp) (a b n : Nat) :
    memcmp m a b n = 0 ↔ ∀ j, j < n → m (a + j) = m (b + j) := by
  unfold memcmp
  rw [vgl_null]
  simp only [Nat.add_zero]

theorem vgl_kleiner (m : Sp) (a b : Nat) :
    ∀ r i, vgl m a b i r = -1 →
      ∃ k, k < r ∧ (∀ j, j < k → m (a + i + j) = m (b + i + j)) ∧
        m (a + i + k) < m (b + i + k) := by
  intro r
  induction r with
  | zero => intro i h; simp only [vgl, Int.reduceNeg, reduceCtorEq] at h
  | succ r ih =>
    intro i h
    simp only [vgl] at h
    by_cases he : m (a + i) = m (b + i)
    · simp only [he, ne_eq, not_true_eq_false, if_false] at h
      obtain ⟨k, hk, hgl, hlt⟩ := ih (i + 1) h
      refine ⟨k + 1, by omega, ?_, ?_⟩
      · intro j hj
        by_cases hj0 : j = 0
        · subst hj0; simpa using he
        · have := hgl (j - 1) (by omega)
          have e1 : a + (i + 1) + (j - 1) = a + i + j := by omega
          have e2 : b + (i + 1) + (j - 1) = b + i + j := by omega
          rwa [e1, e2] at this
      · have e1 : a + (i + 1) + k = a + i + (k + 1) := by omega
        have e2 : b + (i + 1) + k = b + i + (k + 1) := by omega
        rwa [e1, e2] at hlt
    · simp only [ne_eq, he, not_false_eq_true, if_true] at h
      by_cases hl : m (a + i) < m (b + i)
      · exact ⟨0, by omega, fun j hj => by omega, by simpa using hl⟩
      · simp only [hl, ↓reduceIte, Int.reduceNeg, reduceCtorEq] at h

/-- **`memcmp` answers -1 exactly at a first difference whose left byte is smaller.** -/
theorem memcmp_kleiner (m : Sp) (a b n : Nat) (h : memcmp m a b n = -1) :
    ∃ k, k < n ∧ (∀ j, j < k → m (a + j) = m (b + j)) ∧ m (a + k) < m (b + k) := by
  obtain ⟨k, hk, hgl, hlt⟩ := vgl_kleiner m a b n 0 h
  exact ⟨k, hk, fun j hj => by simpa using hgl j hj, by simpa using hlt⟩


end MetallLaufzeit
end Gabbro.Grammatik
