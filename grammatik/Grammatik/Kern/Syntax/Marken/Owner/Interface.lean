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
    A mint creates its fresh owner at the admitted root: the minter holds it
    from its start frame (`inputs`) and returns it (`outputs`); it is never
    ordinary production. Nonempty flows require the C09 machine/source
    simulation before admission. -/
structure OwnerFlow (Marke : Type) where
  moves : List (OwnerMove Marke) := []
  loans : List (Marke × Nat) := []
  /-- Checked mints (`mints m`, C09): the minter holds the fresh owner from
      its start frame and returns it. Last field: coverage numbers it by
      position. -/
  mints : List (Marke × Nat) := []
  deriving DecidableEq, Repr

namespace OwnerFlow

variable {Marke : Type}

/-- All owner inputs, including the exclusive loans and the checked mints
    the minter holds from its start frame. -/
def inputs (F : OwnerFlow Marke) : List (Marke × Nat) :=
  F.moves.map (fun x => (x.mark, x.before)) ++ F.loans ++ F.mints

/-- The common normal/reason inventory: retired moves contribute no output.
    Minted owners are returned, never ordinarily produced. -/
def outputs (F : OwnerFlow Marke) : List (Marke × Nat) :=
  F.moves.filterMap (fun x => x.after.map (fun s => (x.mark, s))) ++ F.loans ++ F.mints

/-- One input per nominal identity across all stages, disjoint moves/loans/mints,
    owner-only entries, bounded stages and monotone stage-changing moves.
    A loan cannot change stage or disappear from either returning channel.
    A mint is held from the start frame and returned. -/
def Valid (isOwner : Marke → Bool) (stages : Marke → Nat) (F : OwnerFlow Marke) : Prop :=
  (F.inputs.map Prod.fst).Nodup ∧
  (∀ x ∈ F.moves, isOwner x.mark = true ∧ x.before < stages x.mark ∧
    x.after.all (fun s => decide (x.before ≤ s ∧ s < stages x.mark)) = true) ∧
  (∀ p ∈ F.loans, isOwner p.1 = true ∧ p.2 < stages p.1) ∧
  ∀ p ∈ F.mints, isOwner p.1 = true ∧ p.2 < stages p.1

instance [DecidableEq Marke] (isOwner : Marke → Bool) (stages : Marke → Nat)
    (F : OwnerFlow Marke) : Decidable (Valid isOwner stages F) := by
  unfold Valid
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Decidable static validation, with no permissive branch for unknown forms. -/
def validB [DecidableEq Marke] (isOwner : Marke → Bool) (stages : Marke → Nat)
    (F : OwnerFlow Marke) : Bool := decide (Valid isOwner stages F)

theorem validB_iff [DecidableEq Marke] (isOwner : Marke → Bool) (stages : Marke → Nat)
    (F : OwnerFlow Marke) : validB isOwner stages F = true ↔ Valid isOwner stages F := by
  simp only [validB, decide_eq_true_eq]

private theorem returned_moves_sublist (moves : List (OwnerMove Marke))
    (loans mints : List (Marke × Nat)) :
    ((moves.filterMap (fun x => x.after.map (fun s => (x.mark, s))) ++ loans ++ mints).map Prod.fst).Sublist
      (((moves.map (fun x => (x.mark, x.before))) ++ loans ++ mints).map Prod.fst) := by
  have hmoves : ((moves.filterMap (fun x => x.after.map (fun s => (x.mark, s)))).map Prod.fst).Sublist
      ((moves.map (fun x => (x.mark, x.before))).map Prod.fst) := by
    induction moves with
    | nil => exact List.Sublist.refl []
    | cons x xs ih =>
        cases hs : x.after with
        | none => simpa [hs] using List.Sublist.cons x.mark ih
        | some s => simpa [hs] using List.Sublist.cons_cons x.mark ih
  have htail : (loans ++ mints).map Prod.fst |>.Sublist (loans ++ mints).map Prod.fst :=
    List.Sublist.refl _
  have h := hmoves.append htail
  simpa only [List.map_append] using h

/-- Returning never duplicates an input identity, including across stages
    and through checked mints. -/
theorem outputs_nodup {isOwner : Marke → Bool} {stages : Marke → Nat}
    {F : OwnerFlow Marke} (hv : Valid isOwner stages F) : (F.outputs.map Prod.fst).Nodup := by
  have hs := returned_moves_sublist F.moves F.loans F.mints
  have hs' : (F.outputs.map Prod.fst).Sublist (F.inputs.map Prod.fst) := by
    simpa only [outputs, inputs] using hs
  exact hs'.nodup hv.1

/-- Every returned identity has an explicit input; only its move stage may
    differ. Minted owners are held from the start frame. -/
theorem output_from_input (F : OwnerFlow Marke) {m : Marke} {s : Nat}
    (h : (m, s) ∈ F.outputs) : ∃ before, (m, before) ∈ F.inputs := by
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨x, hx, he⟩ := List.mem_filterMap.mp h
      cases hs : x.after with
      | none => simp [hs] at he
      | some stage =>
        have e : (x.mark, stage) = (m, s) := by simpa [hs] using he
        have hm : x.mark = m := congrArg Prod.fst e
        refine ⟨x.before, List.mem_append_left _ (List.mem_append_left _ ?_)⟩
        exact List.mem_map.mpr ⟨x, hx, by simp only [hm]⟩
    · exact ⟨s, List.mem_append_left _ (List.mem_append_right _ h)⟩
  · exact ⟨s, List.mem_append_right _ h⟩

/-- The stage of every returned owner is in the declaration's range. -/
theorem output_bounded {isOwner : Marke → Bool} {stages : Marke → Nat}
    {F : OwnerFlow Marke} (hv : Valid isOwner stages F) {m : Marke} {s : Nat}
    (h : (m, s) ∈ F.outputs) : isOwner m = true ∧ s < stages m := by
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨x, hx, he⟩ := List.mem_filterMap.mp h
      cases hs : x.after with
      | none => simp [hs] at he
      | some stage =>
        have e : (x.mark, stage) = (m, s) := by simpa [hs] using he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
        have hb : x.before ≤ stage ∧ stage < stages x.mark := by
          simpa only [hs, Option.all_some, decide_eq_true_eq] using (hv.2.1 x hx).2.2
        exact ⟨(hv.2.1 x hx).1, hb.2⟩
    · exact hv.2.2.1 (m, s) h
  · exact hv.2.2.2 (m, s) h

/-- The empty interface is valid for every owner declaration. -/
theorem empty_valid (isOwner : Marke → Bool) (stages : Marke → Nat) :
    Valid isOwner stages ({} : OwnerFlow Marke) := by
  simp [Valid, inputs]

/-- **Checked call-boundary escrow, static half (C09).** The callee's owner flow is
    valid over the mentioned identities (one input per nominal identity, bounded
    stages, monotone moves, loans exact), disjoint from ordinary consumption (one
    identity is never spent twice at a call), and every input is a declared
    eigner. At a call the caller's bindings named in these inputs move into a
    frame escrow; the return gives back exactly the outputs (`Owner/Escrow.lean`). -/
def EscrowReady {Marke : Type} (isOwner : Marke → Bool) (stages : Marke → Nat)
    (isEigner : Marke → Prop) (konsumiert : List (Marke × Nat)) (F : OwnerFlow Marke) : Prop :=
  F.Valid isOwner stages ∧
    (∀ p ∈ konsumiert, p.1 ∉ F.inputs.map Prod.fst) ∧
    (∀ m ∈ F.inputs.map Prod.fst, isEigner m)

/-- The empty flow is escrow-ready for every declaration. -/
theorem escrowReady_of_empty {Marke : Type} (isOwner : Marke → Bool) (stages : Marke → Nat)
    (isEigner : Marke → Prop) (konsumiert : List (Marke × Nat)) {F : OwnerFlow Marke}
    (h : F = {}) : F.EscrowReady isOwner stages isEigner konsumiert := by
  subst h
  refine ⟨OwnerFlow.empty_valid _ _, ?_, ?_⟩
  · intro p _
    simp [OwnerFlow.inputs]
  · intro m hm
    simp [OwnerFlow.inputs] at hm

/-- Escrow readiness follows equal flows. -/
theorem escrowReady_congr {Marke : Type} {isOwner : Marke → Bool} {stages : Marke → Nat}
    {isEigner : Marke → Prop} {konsumiert : List (Marke × Nat)} {F G : OwnerFlow Marke}
    (h : F = G) (hr : F.EscrowReady isOwner stages isEigner konsumiert) :
    G.EscrowReady isOwner stages isEigner konsumiert :=
  h ▸ hr

/-- Projections of the escrow condition. -/
theorem escrowReady_valid {Marke : Type} {isOwner : Marke → Bool} {stages : Marke → Nat}
    {isEigner : Marke → Prop} {konsumiert : List (Marke × Nat)} {F : OwnerFlow Marke}
    (h : F.EscrowReady isOwner stages isEigner konsumiert) : F.Valid isOwner stages :=
  h.1

theorem escrowReady_disjoint {Marke : Type} {isOwner : Marke → Bool} {stages : Marke → Nat}
    {isEigner : Marke → Prop} {konsumiert : List (Marke × Nat)} {F : OwnerFlow Marke}
    (h : F.EscrowReady isOwner stages isEigner konsumiert) :
    ∀ p ∈ konsumiert, p.1 ∉ F.inputs.map Prod.fst :=
  h.2.1

theorem escrowReady_resolved {Marke : Type} {isOwner : Marke → Bool} {stages : Marke → Nat}
    {isEigner : Marke → Prop} {konsumiert : List (Marke × Nat)} {F : OwnerFlow Marke}
    (h : F.EscrowReady isOwner stages isEigner konsumiert) :
    ∀ m ∈ F.inputs.map Prod.fst, isEigner m :=
  h.2.2

end OwnerFlow

namespace OwnerFlow

/-- Rename nominal identities without changing stages or the transfer mode. -/
def map {α β : Type} (f : α → β) (F : OwnerFlow α) : OwnerFlow β :=
  { moves := F.moves.map (fun x => ⟨f x.mark, x.before, x.after⟩),
    loans := F.loans.map (Prod.map f id), mints := F.mints.map (Prod.map f id) }

theorem inputs_map {α β : Type} (f : α → β) (F : OwnerFlow α) :
    (F.map f).inputs = F.inputs.map (Prod.map f id) := by
  simp only [map, inputs, List.map_append, List.map_map]
  rfl

theorem outputs_map {α β : Type} (f : α → β) (F : OwnerFlow α) :
    (F.map f).outputs = F.outputs.map (Prod.map f id) := by
  have hm : ((F.moves.map fun x => (⟨f x.mark, x.before, x.after⟩ : OwnerMove β)).filterMap
        fun x => x.after.map fun s => (x.mark, s)) =
        (F.moves.filterMap fun x => x.after.map fun s => (x.mark, s)).map (Prod.map f id) := by
    rw [List.filterMap_map, List.map_filterMap]
    congr 1
    funext x
    simp only [Function.comp_apply]
    cases x.after <;> rfl
  simp only [map, outputs, List.map_append, hm]

/-- With no nominal identity in the source type, every owner interface is empty. -/
theorem empty_of_empty (F : OwnerFlow Empty) : F = {} := by
  rcases F with ⟨moves, loans, mints⟩
  have hm : moves = [] := by
    cases moves with
    | nil => rfl
    | cons x _ => exact nomatch x.mark
  have hl : loans = [] := by
    cases loans with
    | nil => rfl
    | cons x _ => exact nomatch x.1
  have hmi : mints = [] := by
    cases mints with
    | nil => rfl
    | cons x _ => exact nomatch x.1
  cases hm
  cases hl
  cases hmi
  rfl

end OwnerFlow

end Gabbro.Grammatik
