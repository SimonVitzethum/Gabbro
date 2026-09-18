/-
  File:      Grammatik/CFormMatch.lean
  Subject:   Integer-match semantics: exhaustiveness over ranges (lane 228).

  After lane 222 (integer arms `3 =>`, `0 .. 255 =>`, `0 ..< 256 =>` in
  `ast.rs`, not yet lowered: lane 227's `switch` lowering is unmerged)
  this file denotes the arms, states exhaustiveness (covered exactly
  or with an explicit default -- never asserted, a missing arm is a
  refusal downstream, TODO wave B rule), and shows the denotation
  sound against the emitted `switch` (`CS.sw` + default branch):
  one correspondence lemma per arm shape.

  The range of the exhaustiveness check is the scrutinee's TYPE range
  (`.int lo hi` admits exactly `lo .. hi`, G1 `einpassen_voll`):
  coverage is decided over constants, never over user logic.
-/
import Grammatik.CFormen
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

/-- One integer `match` arm pattern (lane 222 `IntPat`, mirrored):
    an exact value (`3 =>`) or a literal range (`0 .. 255 =>`
    inclusive, `0 ..< 256 =>` exclusive). Bounds are literals on
    purpose: a computed bound would move the coverage decision into
    user logic. -/
inductive IArm where
  | exact (v : Int) : IArm
  | range (lo hi : Int) (excl : Bool) : IArm
  deriving DecidableEq, Repr

/-! ## 1. Denotation: which values an arm matches -/

/-- Decidable match test of one arm against a value. -/
def trifftB : IArm → Int → Bool
  | .exact v, x => x == v
  | .range lo hi false, x => decide (lo ≤ x ∧ x ≤ hi)
  | .range lo hi true, x => decide (lo ≤ x ∧ x < hi)

/-- Denotation of one arm: the values it matches. -/
def trifft (a : IArm) (x : Int) : Prop := trifftB a x = true

/-- Exact arm: it matches exactly its value. -/
theorem exact_trifft (v x : Int) : trifft (.exact v) x ↔ x = v := by
  simp only [trifft, trifftB, beq_iff_eq]

/-- Inclusive range arm: it matches exactly `lo .. hi`. -/
theorem range_incl_trifft (lo hi x : Int) :
    trifft (.range lo hi false) x ↔ lo ≤ x ∧ x ≤ hi := by
  simp only [trifft, trifftB, decide_eq_true_eq]

/-- Exclusive range arm: it matches exactly `lo ..< hi`. -/
theorem range_excl_trifft (lo hi x : Int) :
    trifft (.range lo hi true) x ↔ lo ≤ x ∧ x < hi := by
  simp only [trifft, trifftB, decide_eq_true_eq]

/-! ## 2. Expansion: the `case` labels one arm writes -/

/-- `n` consecutive values from `s`: the finite enumeration behind
    every range expansion and every coverage check. -/
def aufzaehlung : Nat → Int → List Int
  | 0, _ => []
  | n + 1, s => s :: aufzaehlung n (s + 1)

/-- Membership in the enumeration is the interval. -/
theorem mem_aufzaehlung (n : Nat) (s x : Int) :
    x ∈ aufzaehlung n s ↔ s ≤ x ∧ x < s + n := by
  induction n generalizing s with
  | zero => simp [aufzaehlung]
  | succ n ih =>
    simp only [aufzaehlung, List.mem_cons]
    constructor
    · intro h
      rcases h with rfl | hm
      · constructor <;> omega
      · obtain ⟨h1, h2⟩ := (ih (s + 1)).mp hm
        constructor <;> omega
    · intro ⟨h1, h2⟩
      by_cases hx : x = s
      · exact Or.inl hx
      · exact Or.inr ((ih (s + 1)).mpr ⟨by omega, by omega⟩)

/-- The `case` labels one arm writes: the singleton for an exact arm,
    the full enumeration for a range (empty for an inverted range --
    an arm matching nothing, never a default). -/
def armKeys : IArm → List Int
  | .exact v => [v]
  | .range lo hi false =>
      if lo ≤ hi then aufzaehlung ((hi + 1 - lo).toNat) lo else []
  | .range lo hi true =>
      if lo < hi then aufzaehlung ((hi - lo).toNat) lo else []

/-- Exact arm: its label is its value. -/
theorem mem_armKeys_exact (v x : Int) :
    x ∈ armKeys (.exact v) ↔ x = v := by
  simp [armKeys]

/-- Inclusive range arm: its labels are exactly `lo .. hi`. -/
theorem mem_armKeys_incl (lo hi x : Int) :
    x ∈ armKeys (.range lo hi false) ↔ lo ≤ x ∧ x ≤ hi := by
  simp only [armKeys]
  by_cases h : lo ≤ hi
  · rw [if_pos h, mem_aufzaehlung]
    have e1 : ((((hi + 1 - lo).toNat : Nat)) : Int) = hi + 1 - lo :=
      Int.toNat_of_nonneg (by omega)
    rw [e1]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega⟩,
      fun ⟨h1, h2⟩ => ⟨h1, by omega⟩⟩
  · rw [if_neg h, List.mem_nil_iff, false_iff]
    intro ⟨h1, _⟩
    omega

/-- Exclusive range arm: its labels are exactly `lo ..< hi`. -/
theorem mem_armKeys_excl (lo hi x : Int) :
    x ∈ armKeys (.range lo hi true) ↔ lo ≤ x ∧ x < hi := by
  simp only [armKeys]
  by_cases h : lo < hi
  · rw [if_pos h, mem_aufzaehlung]
    have e1 : ((((hi - lo).toNat : Nat)) : Int) = hi - lo :=
      Int.toNat_of_nonneg (by omega)
    rw [e1]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega⟩,
      fun ⟨h1, h2⟩ => ⟨h1, by omega⟩⟩
  · rw [if_neg h, List.mem_nil_iff, false_iff]
    intro ⟨h1, _⟩
    omega

/-- Denotation and labels agree, for every arm shape. -/
theorem trifft_mem_armKeys (a : IArm) (x : Int) :
    trifft a x ↔ x ∈ armKeys a := by
  cases a with
  | exact v => exact (exact_trifft v x).trans (mem_armKeys_exact v x).symm
  | range lo hi excl =>
    cases excl with
    | false =>
      exact (range_incl_trifft lo hi x).trans (mem_armKeys_incl lo hi x).symm
    | true =>
      exact (range_excl_trifft lo hi x).trans (mem_armKeys_excl lo hi x).symm

/-- The emitted `case` table: every covered value with its FIRST arm
    index. `List.lookup` returns the first pair, so dispatch is first
    match -- exactly `CS.sw` with `break;` in every arm. -/
def fallListeAux : List IArm → Nat → List (Int × Nat)
  | [], _ => []
  | a :: as, i => (armKeys a).map (fun k => (k, i)) ++ fallListeAux as (i + 1)

def fallListe (arms : List IArm) : List (Int × Nat) := fallListeAux arms 0

/-- Dispatch: the chosen arm index for a value, `none` for a miss. -/
def wahl (arms : List IArm) (x : Int) : Option Nat :=
  (fallListe arms).lookup x

/-- A member pair makes the lookup succeed. -/
theorem lookup_mem_isSome {l : List (Int × Nat)} {x : Int} {i : Nat}
    (h : (x, i) ∈ l) : (l.lookup x).isSome = true := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    simp only [List.mem_cons] at h
    rcases h with hmem | hm
    · have hx : x = a := congrArg Prod.fst hmem
      have he : ((x == a) = true) := by rw [beq_iff_eq]; exact hx
      simp only [List.lookup, he, Option.isSome_some]
    · by_cases he : (((x == a)) = true)
      · simp only [List.lookup, he, Option.isSome_some]
      · cases hbx : (x == a) with
        | true => exact absurd hbx he
        | false =>
          simp only [List.lookup, hbx]
          exact ih hm

/-- Every value an arm of the list matches reaches the table with
    some index. -/
theorem mem_fallListeAux_of (arms : List IArm) (i : Nat) (a : IArm) (x : Int)
    (ha : a ∈ arms) (hx : x ∈ armKeys a) :
    ∃ j, (x, j) ∈ fallListeAux arms i := by
  induction arms generalizing i with
  | nil => simp at ha
  | cons hd tl ih =>
    simp only [fallListeAux, List.mem_append]
    simp only [List.mem_cons] at ha
    rcases ha with rfl | hm
    · exact ⟨i, Or.inl (List.mem_map.mpr ⟨x, hx, rfl⟩)⟩
    · obtain ⟨j, hj⟩ := ih (i + 1) hm
      exact ⟨j, Or.inr hj⟩

/-- A matched value dispatches to some arm. -/
theorem trifft_wahl_some {arms : List IArm} {x : Int}
    (h : ∃ a ∈ arms, trifft a x) : ∃ i, wahl arms x = some i := by
  obtain ⟨a, ha, ht⟩ := h
  rw [trifft_mem_armKeys] at ht
  obtain ⟨j, hj⟩ := mem_fallListeAux_of arms 0 a x ha ht
  have hs : ((fallListe arms).lookup x).isSome = true :=
    lookup_mem_isSome hj
  cases he : ((fallListe arms).lookup x) with
  | some i => exact ⟨i, he⟩
  | none => rw [he] at hs; simp at hs

/-- A miss refuses every arm: no arm matches the value. -/
theorem wahl_none_weigert {arms : List IArm} {x : Int}
    (hmiss : wahl arms x = none) (a : IArm) (ha : a ∈ arms) :
    ¬ trifft a x := by
  intro ht
  obtain ⟨i, hi⟩ := trifft_wahl_some ⟨a, ha, ht⟩
  rw [hmiss] at hi
  cases hi

end Gabbro.Grammatik
