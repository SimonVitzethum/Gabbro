import Grammatik.Bausteine.Arena.Ownership.Progress

namespace Gabbro.Grammatik.ArenaOwnership

def activationMax : List Nat → Nat
  | [] => 0
  | n :: ns => max n (activationMax ns)

theorem activation_le_max {n : Nat} {ns : List Nat} (hm : n ∈ ns) : n ≤ activationMax ns := by
  induction ns with
  | nil => cases hm
  | cons a rest ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst a; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hm) (Nat.le_max_right _ _)

def State.activations (s : State) (extent : Nat) : List Nat :=
  (List.range extent).flatMap (fun i => match s.cells (Int.ofNat i) with
    | none => []
    | some cell => cell.owner.activation :: cell.loans.map Frame.activation)

/-- The next activation is chosen from the actual finite ledger. Grant
freshness never relies on a caller-provided numeric activation identifier. -/
def State.freshFrame (s : State) (extent : Nat) (caller : Frame) : Frame :=
  ⟨caller.thread, 1 + max caller.activation (activationMax (s.activations extent))⟩

theorem State.freshFrame_thread (s : State) (extent : Nat) (caller : Frame) :
    (s.freshFrame extent caller).thread = caller.thread := rfl

theorem State.freshFrame_ne_caller (s : State) (extent : Nat) (caller : Frame) :
    s.freshFrame extent caller ≠ caller := by
  intro he
  have hh := congrArg Frame.activation he
  have hm := Nat.le_max_left caller.activation (activationMax (s.activations extent))
  change 1 + max caller.activation (activationMax (s.activations extent)) = caller.activation at hh
  omega

theorem State.cells_bounds {D : Deklaration} {s : State} {A : FreiForm D} {σ : World D}
    (ha : s.agrees A σ) {i : Int} {cell : Cell} (hc : s.cells i = some cell) :
    0 ≤ i ∧ i < D.count A.tab := by
  have hl := (ha.2 i).mpr ⟨cell, hc⟩
  exact ⟨hl.1, Int.lt_of_lt_of_le hl.2.1 (A.stand_le σ)⟩

theorem State.activation_member {s : State} {extent : Nat} {slot : Int} {cell : Cell}
    (hc : s.cells slot = some cell) (hb : 0 ≤ slot ∧ slot < extent) :
    cell.owner.activation ∈ s.activations extent ∧
      ∀ f ∈ cell.loans, f.activation ∈ s.activations extent := by
  have hcast : Int.ofNat slot.toNat = slot := Int.toNat_of_nonneg hb.1
  have hlt : slot.toNat < extent := (Int.toNat_lt hb.1).mpr hb.2
  have hlist : (cell.owner.activation :: cell.loans.map Frame.activation) ⊆ s.activations extent := by
    intro n hn
    apply List.mem_flatMap.mpr
    refine ⟨slot.toNat, List.mem_range.mpr hlt, ?_⟩
    simpa only [hcast, hc] using hn
  exact ⟨hlist (List.mem_cons_self), fun f hf => hlist (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f, hf, rfl⟩))⟩

/-- Freshness includes suspended loans in other stack frames. The bound is
derived from G's actual live-cell relation; no extra hardware or user-logic
assumption is introduced. -/
theorem State.freshFrame_fresh {D : Deklaration} {s : State} {A : FreiForm D} {σ : World D}
    (ha : s.agrees A σ) (caller : Frame) :
    ∀ slot cell, s.cells slot = some cell →
      cell.owner ≠ s.freshFrame (D.count A.tab).toNat caller ∧
        s.freshFrame (D.count A.tab).toNat caller ∉ cell.loans := by
  intro slot cell hc
  have hbound := State.cells_bounds ha hc
  have hcast : slot < Int.ofNat (D.count A.tab).toNat := by
    change slot < ((D.count A.tab).toNat : Int)
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ D.count A.tab)]
    exact hbound.2
  obtain ⟨howner, hloans⟩ := State.activation_member hc ⟨hbound.1, hcast⟩
  have hm := Nat.le_max_right caller.activation (activationMax (s.activations (D.count A.tab).toNat))
  constructor
  · intro he
    have hh := congrArg Frame.activation he
    have hl := activation_le_max howner
    change cell.owner.activation = 1 + max caller.activation (activationMax (s.activations (D.count A.tab).toNat)) at hh
    omega
  · intro hin
    have hl := activation_le_max (hloans _ hin)
    change 1 + max caller.activation (activationMax (s.activations (D.count A.tab).toNat)) ≤ _ at hl
    omega

#print axioms State.freshFrame_fresh

end Gabbro.Grammatik.ArenaOwnership
