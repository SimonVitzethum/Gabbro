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
public import Grammatik.Bausteine.Schablonen.SchablonenMetallBasis

@[expose] public section

namespace Gabbro.Grammatik

namespace MetallLaufzeit
/-! ### Witnesses: every premise instantiated, on a memory where each address holds itself -/

def ident : Sp := fun x => x

/-- `memcpy` of 3 bytes from 10 to 0 (no overlap), `memmove` of 4 bytes from 0 to 2 (overlap,
    the backward branch) and from 2 to 0 (overlap, the forward branch), `memset` of 3 bytes
    with 300, and `memcmp` both ways. -/
theorem metall_speicher_zeuge :
    (10 + 3 ≤ 0 ∨ 0 + 3 ≤ 10) ∧
    memcpy ident 0 10 3 (0 + 2) = ident (10 + 2) ∧ memcpy ident 0 10 3 5 = 5 ∧
    memmove ident 2 0 4 (2 + 3) = ident (0 + 3) ∧
    memmove ident 0 2 4 (0 + 3) = ident (2 + 3) ∧
    memset ident 7 300 3 (7 + 1) = 44 ∧ memset ident 7 300 3 10 = 10 ∧
    memcmp ident 0 0 5 = 0 ∧ memcmp ident 0 1 3 = -1 ∧ memcmp ident 1 0 3 = 1 := by
  decide

/-! ## 2. `arena.metall` -/

/-- The first position of `d` in the emitted list (`gabbro_modul_arenen`). -/
def stelle : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: rest, d => if x = d then some 0 else (stelle rest d).map (· + 1)

/-- `gabbro_arena_reserve(d)` on the bare-metal image: the position of `d`, if the pool
    reservation of that position succeeds (`ok`, the `arena.modul` reservation); `none` ends
    the machine. -/
def reserviere (liste : List Nat) (ok : Nat → Bool) (d : Nat) : Option Nat :=
  match stelle liste d with
  | none => none
  | some i => if ok i then some i else none

theorem stelle_korrekt : ∀ (liste : List Nat) d i, stelle liste d = some i → liste[i]? = some d
  | [], _, _, h => by simp only [stelle, reduceCtorEq] at h
  | x :: rest, d, i, h => by
    simp only [stelle] at h
    by_cases hx : x = d
    · simp only [hx, if_true, Option.some.injEq] at h
      subst h; simp only [hx, List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero]
    · simp only [hx, if_false, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      simpa using stelle_korrekt rest d j hj

theorem stelle_fremd : ∀ (liste : List Nat) d, d ∉ liste → stelle liste d = none
  | [], _, _ => rfl
  | x :: rest, d, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [stelle]
    have hx : ¬ x = d := fun e => h.1 e.symm
    simp only [hx, ↓reduceIte, stelle_fremd rest d h.2, Option.map_none]

/-- A reservation that returns binds the pool of the descriptor's OWN position. -/
theorem arena_metall_eigene_stelle (liste : List Nat) (ok : Nat → Bool) (d i : Nat)
    (h : reserviere liste ok d = some i) : liste[i]? = some d ∧ ok i = true := by
  unfold reserviere at h
  split at h
  · simp only [reduceCtorEq] at h
  · rename_i j hj
    by_cases hok : ok j
    · simp only [hok, if_true, Option.some.injEq] at h
      subst h; exact ⟨stelle_korrekt liste d j hj, hok⟩
    · simp only [hok, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- **Two descriptors never share a pool.** -/
theorem arena_metall_getrennt (liste : List Nat) (ok : Nat → Bool) (d1 d2 i1 i2 : Nat)
    (hd : d1 ≠ d2) (h1 : reserviere liste ok d1 = some i1)
    (h2 : reserviere liste ok d2 = some i2) : i1 ≠ i2 := by
  intro e
  subst e
  have a := (arena_metall_eigene_stelle liste ok d1 i1 h1).1
  have b := (arena_metall_eigene_stelle liste ok d2 i1 h2).1
  rw [a] at b
  exact hd (Option.some.inj b)

/-- A descriptor the emitted list does not hold gets no pool: the machine ends. -/
theorem arena_metall_fremd (liste : List Nat) (ok : Nat → Bool) (d : Nat) (h : d ∉ liste) :
    reserviere liste ok d = none := by
  unfold reserviere; rw [stelle_fremd liste d h]

/-- The pools are the rows of `uint8_t lager[N][V]`: row `i` is `[i * V, (i+1) * V)`. Bytes
    of two different rows never coincide. -/
theorem arena_metall_lager_getrennt (V i1 i2 x y : Nat) (hi : i1 ≠ i2) (hx : x < V) (hy : y < V) :
    i1 * V + x ≠ i2 * V + y := by
  intro e
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · have : (i1 + 1) * V ≤ i2 * V := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this
    omega
  · have : (i2 + 1) * V ≤ i1 * V := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this
    omega

/-- Witness: the list `[10, 20, 30]` (three descriptors), every pool reservation succeeding
    but the third's; 10 and 20 get pools 0 and 1, 30 ends the machine, 40 is no arena. -/
theorem arena_metall_zeuge :
    let liste := [10, 20, 30]
    let ok : Nat → Bool := fun i => i < 2
    reserviere liste ok 10 = some 0 ∧ reserviere liste ok 20 = some 1 ∧
    reserviere liste ok 30 = none ∧ reserviere liste ok 40 = none ∧
    (10 : Nat) ≠ 20 ∧ (0 : Nat) ≠ 1 ∧ 40 ∉ liste ∧
    0 * 4096 + 4095 ≠ 1 * 4096 + 0 := by
  decide

end MetallLaufzeit

end Gabbro.Grammatik
