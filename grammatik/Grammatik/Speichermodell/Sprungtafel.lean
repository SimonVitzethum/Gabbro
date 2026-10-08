/-
  File:      Grammatik/Speichermodell/Sprungtafel.lean
  Subject:   Dense dispatch as a jump table (agent 03, usability team).

  Finding G12/C2 of `messung/SPRACHE-EFFIZIENZ.md`: a `match` over
  integers elaborates to a comparison chain of up to 1797 operations;
  a native compiler wants a table lookup. This file proves, over
  every arm list and with no program named, that a table over a
  window covering every arm value answers exactly like the chain
  (`suche_gleich_kette`), plus the window choice (`fenster_deckt`).
  No code generation and no range-check emission here: the compiler
  chooses between chain and table. No Arm instruction facts (rule 7
  N/A, recorded in CUTS).
-/
import Init

namespace Grammatik.Speichermodell.Sprungtafel

/-- One dispatch arm: the matched value and the result id. -/
abbrev Arm := Nat × Nat

/-- The comparison chain: the result of the FIRST arm whose value
    equals the scrutinee (`none` if no arm matches). -/
def kette : List Arm → Nat → Option Nat
  | [], _ => none
  | (v, r) :: arms, x => if x == v then some r else kette arms x

/-- Distinct arm values (documents the dense-dispatch precondition;
    no theorem below needs it — duplicates are fine, the first arm
    wins in both chain and table). -/
def Eindeutig (arms : List Arm) : Prop := (arms.map Prod.fst).Nodup

/-- The table over the window `lo .. lo+n-1`: entry `k` runs the
    chain at `lo + k`. -/
def tafel (arms : List Arm) (lo n : Nat) : List (Option Nat) :=
  (List.range n).map fun k => kette arms (lo + k)

/-- Table lookup at `x`: the flattened in-window entry, `none`
    outside the window. -/
def suche (arms : List Arm) (lo n x : Nat) : Option Nat :=
  if lo ≤ x ∧ x < lo + n then ((tafel arms lo n)[x - lo]?).join else none

/-! ## 2. The table is faithful inside the window. -/

/-- The table has exactly `n` entries. -/
theorem tafel_laenge (arms : List Arm) (lo n : Nat) :
    (tafel arms lo n).length = n := by
  simp [tafel]

/-- Outside every arm's reach the chain answers `none`: an out-of-window
    scrutinee equals no in-window arm value. -/
theorem kette_none_aussen (arms : List Arm) (lo n x : Nat)
    (h : ∀ a ∈ arms, lo ≤ a.1 ∧ a.1 < lo + n)
    (hx : x < lo ∨ lo + n ≤ x) : kette arms x = none := by
  induction arms with
  | nil => rfl
  | cons a arms ih =>
      have hmem : a ∈ a :: arms := List.mem_cons_self ..
      have hw := h a hmem
      have hmem' : ∀ a_1 ∈ arms, lo ≤ a_1.1 ∧ a_1.1 < lo + n :=
        fun a_1 ha => h a_1 (List.mem_cons_of_mem _ ha)
      have hne : x ≠ a.1 := by omega
      simp only [kette]
      simp [hne]
      exact ih hmem'

/-- In the window the lookup runs the chain (no premises on `arms`). -/
theorem suche_im_fenster (arms : List Arm) (lo n x : Nat)
    (h : lo ≤ x ∧ x < lo + n) : suche arms lo n x = kette arms x := by
  unfold suche
  rw [if_pos h]
  have hmem : x - lo < n := by omega
  have e1 : (List.range n)[x - lo]? = some (x - lo) :=
    List.getElem?_range hmem
  have e2 : ((List.range n).map fun k => kette arms (lo + k))[x - lo]? =
      some (kette arms (lo + (x - lo))) := by
    rw [List.getElem?_map, e1, Option.map_some]
  have e3 : lo + (x - lo) = x := by omega
  rw [e3] at e2
  simp only [tafel]
  rw [e2]
  rfl

/-- Outside the window the lookup answers `none`. -/
theorem suche_ausserhalb (arms : List Arm) (lo n x : Nat)
    (h : x < lo ∨ lo + n ≤ x) : suche arms lo n x = none := by
  unfold suche
  rw [if_neg (by omega)]

/-! ## 3. The table replaces the chain exactly. -/

/-- **Soundness of the lowering**: covered arms make table and chain
    agree on every scrutinee — inside by `suche_im_fenster`, outside
    because an out-of-window value matches no in-window arm
    (`kette_none_aussen`). Duplicates need nothing: the first arm
    wins in both. -/
theorem suche_gleich_kette (arms : List Arm) (lo n : Nat)
    (h : ∀ a ∈ arms, lo ≤ a.1 ∧ a.1 < lo + n) (x : Nat) :
    suche arms lo n x = kette arms x := by
  by_cases hx : lo ≤ x ∧ x < lo + n
  · exact suche_im_fenster arms lo n x hx
  · have hx' : x < lo ∨ lo + n ≤ x := by omega
    rw [suche_ausserhalb arms lo n x hx']
    exact (kette_none_aussen arms lo n x h hx').symm

/-! ## 4. Choosing the window. -/

/-- Minimum arm value (`0` for no arms). -/
def armMin : List Arm → Nat
  | [] => 0
  | (v, _) :: arms => Nat.min v (armMin arms)

/-- Maximum arm value (`0` for no arms). -/
def armMax : List Arm → Nat
  | [] => 0
  | (v, _) :: arms => Nat.max v (armMax arms)

/-- The minimum is a lower bound. -/
theorem armMin_le (arms : List Arm) (a : Arm) (hm : a ∈ arms) :
    armMin arms ≤ a.1 := by
  revert a hm
  induction arms with
  | nil => intro a hm; simp at hm
  | cons c arms ih =>
      intro a hm
      simp only [List.mem_cons] at hm
      simp only [armMin]
      rcases hm with h | hm'
      · rw [h]
        exact Nat.min_le_left _ _
      · exact Nat.le_trans (Nat.min_le_right _ _) (ih _ hm')

/-- The maximum is an upper bound. -/
theorem armMax_ge (arms : List Arm) (a : Arm) (hm : a ∈ arms) :
    a.1 ≤ armMax arms := by
  revert a hm
  induction arms with
  | nil => intro a hm; simp at hm
  | cons c arms ih =>
      intro a hm
      simp only [List.mem_cons] at hm
      simp only [armMax]
      rcases hm with h | hm'
      · rw [h]
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih _ hm') (Nat.le_max_right _ _)

/-! ## 5. Choosing the window. -/

/-- The window covering the arms: `(minimum, span)`, `(0, 1)` when
    empty (vacuous for `fenster_deckt`, which quantifies members). -/
def fenster (arms : List Arm) : Nat × Nat :=
  (armMin arms, armMax arms - armMin arms + 1)

/-- **The chosen window covers every arm value**, so `suche_gleich_kette`
    applies to it. -/
theorem fenster_deckt (arms : List Arm) (a : Arm) (hm : a ∈ arms) :
    (fenster arms).1 ≤ a.1 ∧ a.1 < (fenster arms).1 + (fenster arms).2 := by
  have hmin := armMin_le arms a hm
  have hmax := armMax_ge arms a hm
  simp only [fenster]
  refine ⟨armMin_le _ _ hm, ?_⟩
  show a.1 < armMin arms + (armMax arms - armMin arms + 1)
  omega

/-! ## 6. Witnesses: the finding's table, decided. -/

/-- The table over `10 .. 13` for `[(10,1),(11,2),(13,3)]`. -/
theorem wit_tafel :
    tafel [(10, 1), (11, 2), (13, 3)] 10 4 =
      [some 1, some 2, none, some 3] := by decide

/-- Lookup of the gap reads `none`. -/
theorem wit_suche12 : suche [(10, 1), (11, 2), (13, 3)] 10 4 12 = none := by
  decide

/-- Lookup of an arm reads its result. -/
theorem wit_suche13 :
    suche [(10, 1), (11, 2), (13, 3)] 10 4 13 = some 3 := by decide

/-- Lookup below the window reads `none`. -/
theorem wit_suche9 : suche [(10, 1), (11, 2), (13, 3)] 10 4 9 = none := by
  decide

/-- Lookup above the window reads `none`. -/
theorem wit_suche14 : suche [(10, 1), (11, 2), (13, 3)] 10 4 14 = none := by
  decide

/-- Chain and table agree everywhere on the covered arms. -/
theorem wit_kette_agrees (x : Nat) :
    suche [(10, 1), (11, 2), (13, 3)] 10 4 x =
      kette [(10, 1), (11, 2), (13, 3)] x :=
  suche_gleich_kette _ _ _ (by decide) x

/-- Duplicates: the chain returns the first arm. -/
theorem wit_dup_kette : kette [(5, 1), (5, 2)] 5 = some 1 := by decide

/-- Duplicates: the table entry is the first arm too. -/
theorem wit_dup_suche : suche [(5, 1), (5, 2)] 5 2 5 = some 1 := by decide

end Grammatik.Speichermodell.Sprungtafel

/-
CUTS: what is not proved or not covered.
  - Proved: the comparison chain, the window table and the lookup;
    in-window fidelity (`suche_im_fenster`, no premises on `arms`),
    out-of-window `none` (`suche_ausserhalb`), exact replacement
    (`suche_gleich_kette`, duplicates fine — `Eindeutig` is defined
    but no theorem needs it), the covering window (`fenster`,
    `fenster_deckt`), and decide witnesses for the finding's table
    including the duplicate case.
  - NOT proved: code generation (table emission, range-check
    emission); the compiler's chain-vs-table choice (density
    heuristic); sparse tables with holes beyond the window span.
  - Rule 7 (Sail citations) is N/A: pure `Nat`/`List`/`Option`
    decision logic, no Arm instruction semantics (confidence:
    definitional — the file states no fact about any machine).
-/

#print axioms Grammatik.Speichermodell.Sprungtafel.suche_im_fenster
#print axioms Grammatik.Speichermodell.Sprungtafel.suche_ausserhalb
#print axioms Grammatik.Speichermodell.Sprungtafel.suche_gleich_kette
#print axioms Grammatik.Speichermodell.Sprungtafel.fenster_deckt

/-
CUTS (skeleton): definitions only. NOT yet present: `tafel_laenge`,
`suche_im_fenster`, `suche_ausserhalb`, `suche_gleich_kette`,
`fenster`/`fenster_deckt`, witnesses, `#print axioms`.
-/
