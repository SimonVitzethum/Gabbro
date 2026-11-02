module


@[expose] public section


namespace Gabbro.Grammatik

namespace ModulLaufzeit

/-! ## 1. `arena.modul` -/

/-- The descriptor fields the template reads (the emitter's `gabbro_arena_desc`). -/
structure Desk where
  elem : Nat
  max : Nat
  floor : Nat
  committed : Nat
  deriving DecidableEq

/-- `gabbro_modul_spanne`: the ceiling in bytes, cut at the provision `V`. -/
def spanne (d : Desk) (V : Nat) : Nat := min (d.max * d.elem) V

/-- `gabbro_modul_reserve`: `none` is a refused LOAD (a bad descriptor or a floor the span
    cannot hold); otherwise the descriptor with `committed = floor`. -/
def reserve (d : Desk) (V : Nat) : Option Desk :=
  if d.max = 0 ∨ d.elem = 0 ∨ d.max < d.floor then none
  else if spanne d V < d.floor * d.elem then none
  else some { d with committed := d.floor }

/-- The three answers of `gabbro_arena_grow`. -/
inductive Wachs where
  | stopp          -- past the ceiling: the fail-stop (`gabbro_modul_stopp` set)
  | nein           -- past the span: `false`, the program's `else` runs
  | ja (d : Desk)  -- committed moved
  deriving DecidableEq

/-- `gabbro_arena_grow(d, n)` for `n > 0` (the C answers `true` for `n = 0` and changes
    nothing). -/
def grow (d : Desk) (V n : Nat) : Wachs :=
  if d.max < d.committed + n then .stopp
  else if spanne d V < (d.committed + n) * d.elem then .nein
  else .ja { d with committed := d.committed + n }

/-- The invariant: every committed slot lies inside the span, the span inside the pool. -/
def Inv (d : Desk) (V : Nat) : Prop :=
  d.committed ≤ d.max ∧ d.committed * d.elem ≤ spanne d V ∧ spanne d V ≤ V

theorem spanne_le (d : Desk) (V : Nat) : spanne d V ≤ V := Nat.min_le_right _ _

theorem arena_modul_inv_reserve (d d' : Desk) (V : Nat) (h : reserve d V = some d') :
    Inv d' V ∧ d'.committed = d.floor ∧ d'.elem = d.elem ∧ d'.max = d.max := by
  unfold reserve at h
  split at h
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  · split at h
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    · rename_i h1 h2
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨⟨?_, ?_, spanne_le _ _⟩, rfl, rfl, rfl⟩
      · simp only; omega
      · simp only [spanne] at h2 ⊢; omega

theorem arena_modul_inv_grow (d d' : Desk) (V n : Nat) (_hI : Inv d V)
    (h : grow d V n = .ja d') : Inv d' V ∧ d'.committed = d.committed + n ∧
      d'.elem = d.elem ∧ d'.max = d.max := by
  unfold grow at h
  split at h
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  · split at h
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    · rename_i h1 h2
      simp only [Wachs.ja.injEq] at h
      subst h
      refine ⟨⟨?_, ?_, spanne_le _ _⟩, rfl, rfl, rfl⟩
      · simp only; omega
      · simp only [spanne] at h2 ⊢; omega

/-- A refused `grow` (either kind) leaves the descriptor as it was: the C returns before any
    store to `committed`. -/
theorem arena_modul_monoton (d d' : Desk) (V n : Nat) (h : grow d V n = .ja d') :
    d.committed ≤ d'.committed := by
  unfold grow at h
  split at h
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  · split at h
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    · simp only [Wachs.ja.injEq] at h; subst h; simp only [Nat.le_add_right]

/-- **Every slot the unit can reach lies inside its pool**: slot `i < committed` occupies the
    bytes `[i * elem, (i+1) * elem)`, all below `V` (the static `uint8_t [V]` row). -/
theorem arena_modul_slot_im_lager (d : Desk) (V i : Nat) (hI : Inv d V) (hi : i < d.committed) :
    (i + 1) * d.elem ≤ V := by
  obtain ⟨_, h2, h3⟩ := hI
  have : (i + 1) * d.elem ≤ d.committed * d.elem := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **No 64-bit product wraps**: with 32-bit `max` and `elem`, the ceiling product and the
    floor product are below `2^64`, and the span product `neu * elem` is formed only when
    `neu <= max` (the ceiling test comes first). -/
theorem arena_modul_kein_ueberlauf (d : Desk) (neu : Nat) (hm : d.max < 2 ^ 32)
    (he : d.elem < 2 ^ 32) (hf : d.floor ≤ d.max) (hn : neu ≤ d.max) :
    d.max * d.elem < 2 ^ 64 ∧ d.floor * d.elem < 2 ^ 64 ∧ neu * d.elem < 2 ^ 64 := by
  have hmax : d.max * d.elem < 2 ^ 32 * 2 ^ 32 := by
    calc d.max * d.elem ≤ d.max * (2 ^ 32 - 1) := Nat.mul_le_mul_left _ (by omega)
      _ < 2 ^ 32 * 2 ^ 32 := by
        have : d.max * (2 ^ 32 - 1) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
  have h64 : (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 := by rfl
  rw [h64] at hmax
  refine ⟨hmax, ?_, ?_⟩
  · exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hf) hmax
  · exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hn) hmax

/-- A grow past the ceiling is the fail-stop, never a commit. -/
theorem arena_modul_ueber_der_decke (d : Desk) (V n : Nat) (h : d.max < d.committed + n) :
    grow d V n = .stopp := by
  unfold grow; simp only [h, ↓reduceIte]

/-! ### Witness: the `halde` probe (`messung/proben/kmodul/halde-treiber.gab`) -/

/-- `arena Knoten capacity 2 .. 4 max 4096 of Wert` (8-byte slots) under `provision 24576`. -/
def haldeD : Desk := { elem := 8, max := 4096, floor := 4, committed := 0 }

theorem arena_modul_zeuge :
    ∃ d1 d2 d3,
      reserve haldeD 24576 = some d1 ∧ Inv d1 24576 ∧
      grow d1 24576 1024 = .ja d2 ∧ grow d2 24576 1024 = .ja d3 ∧
      d3.committed = 2052 ∧ Inv d3 24576 ∧
      grow d3 24576 1024 = .nein ∧          -- the third grow is refused below the ceiling
      grow d3 24576 3000 = .stopp ∧          -- and one past the ceiling is the fail-stop
      (2051 + 1) * d3.elem ≤ 24576 := by
  refine ⟨{ haldeD with committed := 4 }, { haldeD with committed := 1028 },
    { haldeD with committed := 2052 }, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := { decide := true }) [Inv]


end ModulLaufzeit
end Gabbro.Grammatik
