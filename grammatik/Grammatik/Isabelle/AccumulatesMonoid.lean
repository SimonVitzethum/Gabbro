/-
  File:      Grammatik/Isabelle/AccumulatesMonoid.lean
  Port of:   beweise/Accumulates_Monoid.thy (template `accumulates.monoid`, S9)

  The Isabelle theory models the closed vocabulary `max | min | add | or | and`
  as ONE structure -- a commutative monoid (`merge_monoid` locale) -- folds it
  over the per-core cells (`faltet`), shows the fold is independent of the core
  order (`faltung_ist_reihenfolgeunabhaengig`, via multisets), and shows it
  agrees with a sequential chain of atomic RMW steps AT THE QUIESCE POINT
  (`am_ruhepunkt_gleich_dem_atomaren_rmw`). It then discharges the structure
  for the four word operations and for `min` at a bounded type.

  Adaptations (same content, Lean core without mathlib):
  - The locale becomes a `structure MergeMonoid` over a carrier `α`.
  - `mset xs = mset ys` becomes `IsPerm xs ys` (own inductive: nil / cons /
    swap / trans). Over lists, permutation equality IS multiset equality; there
    is no `Multiset` in Lean core, so the equivalence cannot be stated, only
    documented here.
  - The four instance interpretations become four `MergeMonoid` terms
    (`maxMonoid`, `addMonoid`, `orMonoid`, `andMonoid`).
  - `min` at `{linorder, order_top}` becomes `min` on `Nat` with the top made
    EXPLICIT: `∀ T a, a ≤ T → min T a = a`. The Isabelle `top` carries
    `a ≤ top` as an instance property; here it is a premise. Same equation,
    same force (a generator starting `min` at `0` breaks it).
-/

namespace Gabbro.Grammatik.Isabelle.AccumulatesMonoid

/-- The shared structure of the closed `merge` vocabulary: associative,
    commutative, with a neutral element. (Isabelle: `locale merge_monoid`.) -/
structure MergeMonoid (α : Type) where
  op : α → α → α
  neutral : α
  assoz : ∀ a b c, op (op a b) c = op a (op b c)
  komm : ∀ a b, op a b = op b a
  links : ∀ a, op neutral a = a

variable {α : Type} (M : MergeMonoid α)

/-- Right neutrality follows from commutativity and left neutrality.
    (Isabelle: `rechts`.) -/
theorem rechts (a : α) : M.op a M.neutral = a := by
  rw [M.komm a M.neutral]
  exact M.links a

/-- The fold over the per-core cells. (Isabelle: `faltet`.) -/
def faltet : List α → α
  | [] => M.neutral
  | x :: xs => M.op x (faltet xs)

/-- Folding a concatenation splits at the joint.
    (Isabelle: `faltet_anhaengen`.) -/
theorem faltet_anhaengen (xs ys : List α) :
    faltet M (xs ++ ys) = M.op (faltet M xs) (faltet M ys) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, faltet]
    exact (M.links (faltet M ys)).symm
  | cons x xs ih =>
    simp only [List.cons_append, faltet]
    rw [ih]
    exact (M.assoz x (faltet M xs) (faltet M ys)).symm

/-- Swapping the first two cells changes nothing.
    (Isabelle: `faltet_vertauschen`.) -/
theorem faltet_vertauschen (x y : α) (xs : List α) :
    faltet M (x :: y :: xs) = faltet M (y :: x :: xs) := by
  simp only [faltet]
  have h1 : M.op x (M.op y (faltet M xs)) = M.op (M.op x y) (faltet M xs) :=
    (M.assoz x y (faltet M xs)).symm
  have h2 : M.op (M.op x y) (faltet M xs) = M.op (M.op y x) (faltet M xs) := by
    rw [M.komm x y]
  have h3 : M.op (M.op y x) (faltet M xs) = M.op y (M.op x (faltet M xs)) :=
    M.assoz y x (faltet M xs)
  rw [h1, h2, h3]

/-- Permutation equality of cell lists (Isabelle `mset` equality, which does
    not exist in Lean core). -/
inductive IsPerm : List α → List α → Prop where
  | nil : IsPerm [] []
  | cons (x : α) {l₁ l₂ : List α} (h : IsPerm l₁ l₂) : IsPerm (x :: l₁) (x :: l₂)
  | swap (x y : α) (l : List α) : IsPerm (x :: y :: l) (y :: x :: l)
  | trans {l₁ l₂ l₃ : List α} (h₁ : IsPerm l₁ l₂) (h₂ : IsPerm l₂ l₃) :
      IsPerm l₁ l₃

/-- THE theorem: the fold does not depend on the order of the cores.
    (Isabelle: `faltung_ist_reihenfolgeunabhaengig`; `mset` replaced by
    `IsPerm`, same mathematical content.) -/
theorem faltung_ist_reihenfolgeunabhaengig {xs ys : List α}
    (h : IsPerm xs ys) : faltet M xs = faltet M ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [faltet]; rw [ih]
  | swap x y l => exact faltet_vertauschen M x y l
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The sequential chain of atomic RMW steps on a single cell.
    (Isabelle: `rmw_kette`.) -/
def rmwKette : α → List α → α
  | z, [] => z
  | z, x :: xs => rmwKette (M.op z x) xs

/-- Pulling the start value out of the chain.
    (Isabelle: `rmw_kette_zieht_heraus`.) -/
theorem rmw_kette_zieht_heraus (z : α) (xs : List α) :
    rmwKette M z xs = M.op z (faltet M xs) := by
  induction xs generalizing z with
  | nil =>
    simp only [rmwKette, faltet]
    exact (rechts M z).symm
  | cons x xs ih =>
    simp only [rmwKette, faltet]
    rw [ih (M.op z x)]
    exact M.assoz z x (faltet M xs)

/-- AT THE QUIESCE POINT the fold agrees with the atomic chain.
    (Isabelle: `am_ruhepunkt_gleich_dem_atomaren_rmw`.) -/
theorem am_ruhepunkt_gleich_dem_atomaren_rmw (xs : List α) :
    rmwKette M M.neutral xs = faltet M xs := by
  rw [rmw_kette_zieht_heraus]
  exact M.links (faltet M xs)

/-! ## The vocabulary really is monoids -/

/-- `max` on `Nat` with neutral `0`. (Isabelle: `acc_max`.) -/
def maxMonoid : MergeMonoid Nat where
  op := Nat.max
  neutral := 0
  assoz := Nat.max_assoc
  komm := Nat.max_comm
  links := Nat.zero_max

/-- `(+)` on `Nat` with neutral `0`. (Isabelle: `acc_add`.) -/
def addMonoid : MergeMonoid Nat where
  op := Nat.add
  neutral := 0
  assoz := Nat.add_assoc
  komm := Nat.add_comm
  links := Nat.zero_add

/-- `(||)` on `Bool` with neutral `false`. (Isabelle: `acc_or`.) -/
def orMonoid : MergeMonoid Bool where
  op := (· || ·)
  neutral := false
  assoz := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  komm := fun a b => by cases a <;> cases b <;> rfl
  links := fun a => by cases a <;> rfl

/-- `(&&)` on `Bool` with neutral `true`. (Isabelle: `acc_and`.) -/
def andMonoid : MergeMonoid Bool where
  op := (· && ·)
  neutral := true
  assoz := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  komm := fun a b => by cases a <;> cases b <;> rfl
  links := fun a => by cases a <;> rfl

/-- `min` is associative. (Isabelle: `min_ist_monoid_mit_top`, first part.) -/
theorem min_ist_monoid_vereinigen (a b c : Nat) :
    min (min a b) c = min a (min b c) := by
  omega

/-- `min` is commutative. (Isabelle: `min_ist_monoid_mit_top`, second part.) -/
theorem min_ist_monoid_vertauschen (a b : Nat) : min a b = min b a := by
  omega

/-- `min` at an EXPLICIT top `T`: the premise `a ≤ T` is what the Isabelle
    `order_top` instance supplies silently. A generator starting `min` at `0`
    breaks exactly this equation. (Isabelle: `min_ist_monoid_mit_top`.) -/
theorem min_ist_monoid_mit_top (T a : Nat) (h : a ≤ T) : min T a = a := by
  omega

/-! ## Witness: the fold on a concrete instance -/

/-- Witness: folding `[1, 2, 3]` with `add` gives `6`, and the swapped list
    gives the same -- the order-independence on a concrete instance. No lemma
    above quantifies over syntax, so the inhabitation obligation is vacuous;
    this is a data-level witness for the main theorem. -/
theorem faltet_zeuge :
    faltet addMonoid [1, 2, 3] = 6 ∧
    faltet addMonoid [1, 2, 3] = faltet addMonoid [3, 1, 2] := by
  constructor
  · rfl
  · have h : IsPerm [1, 2, 3] [3, 1, 2] :=
      .trans (.cons 1 (.swap 2 3 [])) (.swap 1 3 [2])
    exact faltung_ist_reihenfolgeunabhaengig addMonoid h

/-! ## Bridge

  The Lean semantics ties `accumulates` to a global plus a generated store
  (`Syntax.lean`: "`accumulates` = `Glob` + erzeugte Zuweisung"). That half --
  that the EMITTER lays out one cell per core and starts each at the right
  neutral element (in particular `min` NOT at `0`) -- is the PL.3 bridge and is
  NOT shown here, exactly as the Isabelle theory does not show it (M-2 there).
  Named, not faked: `min_mit_null_start_zieht_auf_null (T) : min T 0 = 0`. -/

/-- The named trap: `min` started at `0` drags every result to `0`. -/
theorem min_mit_null_start_zieht_auf_null (T : Nat) : min T 0 = 0 := by
  omega

#print axioms Gabbro.Grammatik.Isabelle.AccumulatesMonoid.rechts
#print axioms Gabbro.Grammatik.Isabelle.AccumulatesMonoid.faltet_anhaengen
#print axioms Gabbro.Grammatik.Isabelle.AccumulatesMonoid.faltet_vertauschen
#print axioms Gabbro.Grammatik.Isabelle.AccumulatesMonoid.faltung_ist_reihenfolgeunabhaengig
#print axioms Gabbro.Grammatik.Isabelle.AccumulatesMonoid.rmw_kette_zieht_heraus
#print axioms Gabbro.Grammatik.Isabelle.AccumulatesMonoid.am_ruhepunkt_gleich_dem_atomaren_rmw
#print axioms Gabbro.Grammatik.Isabelle.AccumulatesMonoid.min_ist_monoid_mit_top
#print axioms Gabbro.Grammatik.Isabelle.AccumulatesMonoid.faltet_zeuge

end Gabbro.Grammatik.Isabelle.AccumulatesMonoid
