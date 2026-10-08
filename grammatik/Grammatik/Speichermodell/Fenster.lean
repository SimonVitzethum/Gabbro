/-
  File:      Grammatik/Speichermodell/Fenster.lean
  Subject:   Lean groundwork for the windowed traverse (agent 03,
             usability team).

  Finding G4 of `messung/SPRACHE-EFFIZIENZ.md`: a hold-chunked scan of
  a big table has to walk the indices `s .. s+n-1`. This file models,
  over every index list and with no program named: the window
  (`indizes`, defined by recursion rather than `List.range'` so no
  range API is needed), the walk with early exit (`lauf`: `none`
  leaves NOW with the state as-is), and the ghost visited list
  (`besucht`). Standalone: nothing in the existing semantics is
  changed. No Arm instruction facts (rule 7 N/A, recorded in CUTS).
-/
import Init

namespace Grammatik.Speichermodell.Fenster

/-- The window `s .. s+n-1` (by recursion, not `List.range'`). -/
def indizes : Nat → Nat → List Nat
  | _, 0 => []
  | s, n + 1 => s :: indizes (s + 1) n

/-- A walk with early exit: `none` leaves NOW with the state as-is
    (a leaving step's own effect is the caller's business: return
    `none` after recording it in a pair state if needed), `some a'`
    continues with `a'`. -/
def lauf {α : Type} (schritt : α → Nat → Option α) : α → List Nat → α
  | a, [] => a
  | a, k :: ks =>
      match schritt a k with
      | none => a
      | some a' => lauf schritt a' ks

/-- The ghost visited list: the indices the walk actually executes,
    including the one that leaves. -/
def besucht {α : Type} (f : α → Nat → Option α) : α → List Nat → List Nat
  | _, [] => []
  | a, k :: ks =>
      match f a k with
      | none => [k]
      | some a' => k :: besucht f a' ks

/-! ## 2. The window: length, members, uniqueness, chunking. -/

/-- A window has exactly `n` indices. -/
theorem indizes_laenge (s n : Nat) : (indizes s n).length = n := by
  induction n generalizing s with
  | zero => simp [indizes]
  | succ n ih => simp [indizes, ih]

/-- Membership is the interval. -/
theorem indizes_mem (s n k : Nat) :
    k ∈ indizes s n ↔ s ≤ k ∧ k < s + n := by
  induction n generalizing s with
  | zero =>
      constructor
      · intro h
        simp only [indizes] at h
        simp at h
      · rintro ⟨h1, h2⟩
        exact False.elim (by omega)
  | succ n ih =>
      simp only [indizes, List.mem_cons]
      constructor
      · rintro (rfl | hm)
        · exact ⟨by omega, by omega⟩
        · have h2 := (ih (s + 1)).mp hm
          omega
      · rintro ⟨h1, h2⟩
        by_cases hks : k = s
        · exact Or.inl hks
        · exact Or.inr ((ih (s + 1)).mpr ⟨by omega, by omega⟩)

/-- A window holds no index twice. -/
theorem indizes_nodup (s n : Nat) : (indizes s n).Nodup := by
  induction n generalizing s with
  | zero => simp [indizes]
  | succ n ih =>
      simp only [indizes]
      refine List.Pairwise.cons ?_ (ih _)
      intro y hy hEq
      have h2 := (indizes_mem (s + 1) n y).mp hy
      omega

/-- **Chunking**: a window splits at `m` (the hold-sized scan). -/
theorem indizes_append (s m n : Nat) :
    indizes s (m + n) = indizes s m ++ indizes (s + m) n := by
  induction m generalizing s with
  | zero => simp [indizes]
  | succ m ih =>
      have e : m + 1 + n = (m + n) + 1 := by omega
      have e2 : s + 1 + m = s + (m + 1) := by omega
      simp only [indizes, e, e2, List.cons_append, ih]

/-! ## 3. The walk splits into chunks. -/

/-- **Chunked walking**: a walk over `xs ++ ys` continues from where
    the walk over `xs` ended — WHEN the first chunk never leaves.
    This is the soundness of walking a table in hold-sized chunks. -/
theorem lauf_append {α : Type} (f : α → Nat → Option α) (a : α)
    (xs ys : List Nat) (h : ∀ b k, k ∈ xs → f b k ≠ none) :
    lauf f a (xs ++ ys) = lauf f (lauf f a xs) ys := by
  induction xs generalizing a with
  | nil => simp [lauf]
  | cons x xs ih =>
      have hmem : ∀ b k, k ∈ xs → f b k ≠ none :=
        fun b k hk => h b k (List.mem_cons_of_mem _ hk)
      have hne : f a x ≠ none := h a x (List.mem_cons_self ..)
      cases hfx : f a x with
      | none => exact absurd hfx hne
      | some a' =>
          simp only [lauf, hfx, List.cons_append]
          exact ih a' hmem

/-- **Early exit**: a leaving first step stops the walk and ignores
    the rest, whatever follows. -/
theorem lauf_leave {α : Type} (f : α → Nat → Option α) (a : α)
    (k : Nat) (ks : List Nat) (h : f a k = none) :
    lauf f a (k :: ks) = a := by
  simp only [lauf, h]

/-! ## 4. The ghost visited list. -/

/-- The visited log is a prefix of the schedule. -/
theorem besucht_prefix {α : Type} (f : α → Nat → Option α) (a : α)
    (xs : List Nat) : List.IsPrefix (besucht f a xs) xs := by
  induction xs generalizing a with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
      cases hfx : f a x with
      | none =>
          exact ⟨xs, by simp only [besucht, hfx, List.cons_append, List.nil_append]⟩
      | some a' =>
          obtain ⟨t, ht⟩ := ih a'
          exact ⟨t, by simp only [besucht, hfx, List.cons_append, ht]⟩

/-- With no leaving step the visited log is the whole schedule. -/
theorem besucht_voll {α : Type} (f : α → Nat → Option α) (a : α)
    (xs : List Nat) (h : ∀ b k, k ∈ xs → f b k ≠ none) :
    besucht f a xs = xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      have hmem : ∀ b k, k ∈ xs → f b k ≠ none :=
        fun b k hk => h b k (List.mem_cons_of_mem _ hk)
      cases hfx : f a x with
      | none => exact absurd hfx (h a x (List.mem_cons_self ..))
      | some a' =>
          simp only [besucht, hfx]
          exact congrArg _ (ih a' hmem)

/-- **The visited log is a prefix, and the whole schedule when no
    step leaves.** -/
theorem besucht_praefix {α : Type} (f : α → Nat → Option α) (a : α)
    (xs : List Nat) :
    List.IsPrefix (besucht f a xs) xs ∧
      ((∀ b k, k ∈ xs → f b k ≠ none) → besucht f a xs = xs) :=
  ⟨besucht_prefix f a xs, fun h => besucht_voll f a xs h⟩

/-! ## 5. Witnesses: counting, chunked and early-exit walks. -/

/-- The window `3 .. 6`. -/
theorem wit_indizes : indizes 3 4 = [3, 4, 5, 6] := by decide

/-- A counting walk sums the window: 0+3+4+5+6 = 18. -/
theorem wit_summe : lauf (fun a k => some (a + k)) 0 (indizes 3 4) = 18 := by
  decide

/-- Chunked: two half-windows give the same 18. -/
theorem wit_stuecke :
    lauf (fun a k => some (a + k))
      (lauf (fun a k => some (a + k)) 0 (indizes 3 2)) (indizes 5 2) = 18 := by
  decide

/-- Early exit: 3 + 4, stops at 5. -/
theorem wit_abbruch :
    lauf (fun a k => if k = 5 then none else some (a + k)) 0
      (indizes 3 4) = 7 := by
  decide

/-- The ghost log of the early-exit walk. -/
theorem wit_besucht :
    besucht (fun a k => if k = 5 then none else some (a + k)) 0
      (indizes 3 4) = [3, 4, 5] := by
  decide

end Grammatik.Speichermodell.Fenster

/-
CUTS: what is not proved or not covered.
  - Proved: the window (`indizes` length/members/nodup/chunking),
    chunked walking (`lauf_append` under no-leave), early exit
    (`lauf_leave`), the ghost log (prefix always, full when no step
    leaves), and decide witnesses (window, sum 18, chunked 18,
    early exit 7, log [3,4,5]).
  - NOT proved: parser, checker or exporter forms (no `traverse`
    surface, no `from/count` items); bounds `s + n ≤ count` (the
    checker's later rule); lowering to loads/stores.
  - Rule 7 (Sail citations) is N/A: pure `Nat`/`List`/`Option`
    walk logic, no Arm instruction semantics (confidence:
    definitional — the file states no fact about any machine).
-/

#print axioms Grammatik.Speichermodell.Fenster.indizes_laenge
#print axioms Grammatik.Speichermodell.Fenster.indizes_mem
#print axioms Grammatik.Speichermodell.Fenster.indizes_nodup
#print axioms Grammatik.Speichermodell.Fenster.indizes_append
#print axioms Grammatik.Speichermodell.Fenster.lauf_append
#print axioms Grammatik.Speichermodell.Fenster.lauf_leave
#print axioms Grammatik.Speichermodell.Fenster.besucht_prefix
#print axioms Grammatik.Speichermodell.Fenster.besucht_voll
#print axioms Grammatik.Speichermodell.Fenster.besucht_praefix
#print axioms Grammatik.Speichermodell.Fenster.wit_indizes
#print axioms Grammatik.Speichermodell.Fenster.wit_summe
#print axioms Grammatik.Speichermodell.Fenster.wit_stuecke
#print axioms Grammatik.Speichermodell.Fenster.wit_abbruch
#print axioms Grammatik.Speichermodell.Fenster.wit_besucht
