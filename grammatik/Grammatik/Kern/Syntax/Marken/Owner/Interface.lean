module

public import Grammatik.Kern.Syntax.Typen.Teil2

@[expose] public section

namespace Gabbro.Grammatik

/-- An explicit handoff of an existing nominal owner. `none` retires it;
    `some stage` returns that same owner at the indicated stage. Both returning
    channels use this inventory. Ordinary `produziert` never carries owners. -/
structure OwnerMove (Marke : Type) where
  mark : Marke
  before : Nat
  after : Option Nat
  deriving DecidableEq, Repr

/-- Resource-only call metadata, separate from copyable `Ty`/`Val` arguments.
    Loans return their exact input stage; stage-changing handoff is a move.
    Nonempty flows require the C09 machine/source simulation before admission. -/
structure OwnerFlow (Marke : Type) where
  moves : List (OwnerMove Marke) := []
  loans : List (Marke × Nat) := []
  deriving DecidableEq, Repr

namespace OwnerFlow

variable {Marke : Type}

/-- All owner inputs, including the exclusive loans. -/
def inputs (F : OwnerFlow Marke) : List (Marke × Nat) :=
  F.moves.map (fun x => (x.mark, x.before)) ++ F.loans

/-- The common normal/reason inventory: retired moves contribute no output. -/
def outputs (F : OwnerFlow Marke) : List (Marke × Nat) :=
  F.moves.filterMap (fun x => x.after.map (fun s => (x.mark, s))) ++ F.loans

/-- One input per nominal identity across all stages, disjoint moves/loans,
    owner-only entries, bounded stages and monotone stage-changing moves.
    A loan cannot change stage or disappear from either returning channel. -/
def Valid (isOwner : Marke → Bool) (stages : Marke → Nat) (F : OwnerFlow Marke) : Prop :=
  (F.inputs.map Prod.fst).Nodup ∧
  (∀ x ∈ F.moves, isOwner x.mark = true ∧ x.before < stages x.mark ∧
    x.after.all (fun s => decide (x.before ≤ s ∧ s < stages x.mark)) = true) ∧
  ∀ p ∈ F.loans, isOwner p.1 = true ∧ p.2 < stages p.1

instance [DecidableEq Marke] (isOwner : Marke → Bool) (stages : Marke → Nat)
    (F : OwnerFlow Marke) : Decidable (Valid isOwner stages F) := by
  unfold Valid
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Decidable static validation, with no permissive branch for unknown forms. -/
def validB [DecidableEq Marke] (isOwner : Marke → Bool) (stages : Marke → Nat)
    (F : OwnerFlow Marke) : Bool := decide (Valid isOwner stages F)

theorem validB_iff [DecidableEq Marke] (isOwner : Marke → Bool) (stages : Marke → Nat)
    (F : OwnerFlow Marke) : validB isOwner stages F = true ↔ Valid isOwner stages F := by
  simp only [validB, decide_eq_true_eq]

private theorem returned_moves_sublist (moves : List (OwnerMove Marke)) :
    ((moves.filterMap (fun x => x.after.map (fun s => (x.mark, s)))).map Prod.fst).Sublist
      ((moves.map (fun x => (x.mark, x.before))).map Prod.fst) := by
  induction moves with
  | nil => exact List.Sublist.refl []
  | cons x xs ih =>
      cases hs : x.after with
      | none => simpa [hs] using List.Sublist.cons x.mark ih
      | some s => simpa [hs] using List.Sublist.cons_cons x.mark ih

/-- Returning never duplicates an input identity, including across stages. -/
theorem outputs_nodup {isOwner : Marke → Bool} {stages : Marke → Nat}
    {F : OwnerFlow Marke} (hv : Valid isOwner stages F) : (F.outputs.map Prod.fst).Nodup := by
  have hs := (returned_moves_sublist F.moves).append (List.Sublist.refl (F.loans.map Prod.fst))
  have hs' : (F.outputs.map Prod.fst).Sublist (F.inputs.map Prod.fst) := by
    simpa only [outputs, inputs, List.map_append] using hs
  exact hs'.nodup hv.1

/-- Every returned identity has an explicit input; only its move stage may differ. -/
theorem output_from_input (F : OwnerFlow Marke) {m : Marke} {s : Nat}
    (h : (m, s) ∈ F.outputs) : ∃ before, (m, before) ∈ F.inputs := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨x, hx, he⟩ := List.mem_filterMap.mp h
    cases hs : x.after with
    | none => simp [hs] at he
    | some stage =>
      have e : (x.mark, stage) = (m, s) := by simpa [hs] using he
      have hm : x.mark = m := congrArg Prod.fst e
      refine ⟨x.before, List.mem_append_left _ ?_⟩
      exact List.mem_map.mpr ⟨x, hx, by simp only [hm]⟩
  · exact ⟨s, List.mem_append_right _ h⟩

/-- The stage of every returned owner is in the declaration's range. -/
theorem output_bounded {isOwner : Marke → Bool} {stages : Marke → Nat}
    {F : OwnerFlow Marke} (hv : Valid isOwner stages F) {m : Marke} {s : Nat}
    (h : (m, s) ∈ F.outputs) : isOwner m = true ∧ s < stages m := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨x, hx, he⟩ := List.mem_filterMap.mp h
    cases hs : x.after with
    | none => simp [hs] at he
    | some stage =>
      have e : (x.mark, stage) = (m, s) := by simpa [hs] using he
      cases e
      have hb : x.before ≤ stage ∧ stage < stages x.mark := by
        simpa only [hs, Option.all_some, decide_eq_true_eq] using (hv.2.1 x hx).2.2
      exact ⟨(hv.2.1 x hx).1, hb.2⟩
  · exact hv.2.2 (m, s) h

/-- The empty interface is valid for every owner declaration. -/
theorem empty_valid (isOwner : Marke → Bool) (stages : Marke → Nat) :
    Valid isOwner stages ({} : OwnerFlow Marke) := by
  simp [Valid, inputs]

end OwnerFlow

namespace OwnerFlow

/-- Rename nominal identities without changing stages or the transfer mode. -/
def map {α β : Type} (f : α → β) (F : OwnerFlow α) : OwnerFlow β :=
  { moves := F.moves.map (fun x => ⟨f x.mark, x.before, x.after⟩), loans := F.loans.map (Prod.map f id) }

theorem inputs_map {α β : Type} (f : α → β) (F : OwnerFlow α) :
    (F.map f).inputs = F.inputs.map (Prod.map f id) := by
  simp only [map, inputs, List.map_append, List.map_map]
  rfl

theorem outputs_map {α β : Type} (f : α → β) (F : OwnerFlow α) :
    (F.map f).outputs = F.outputs.map (Prod.map f id) := by
  unfold map outputs
  rw [List.map_append]
  congr 1
  induction F.moves with
  | nil => rfl
  | cons x xs ih => cases x.after <;> simp_all

/-- With no nominal identity in the source type, every owner interface is empty. -/
theorem empty_of_empty (F : OwnerFlow Empty) : F = {} := by
  rcases F with ⟨moves, loans⟩
  have hm : moves = [] := by
    cases moves with
    | nil => rfl
    | cons x _ => exact nomatch x.mark
  have hl : loans = [] := by
    cases loans with
    | nil => rfl
    | cons x _ => exact nomatch x.1
  cases hm
  cases hl
  rfl

end OwnerFlow

end Gabbro.Grammatik
