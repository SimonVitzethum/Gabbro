module

public import Core.Verfeinerung.Schnitt

@[expose] public section

namespace Gabbro.Core.Maschine.Zeitlauf

variable {S Ev T Obs : Type}
variable {schritt : Nat → S → Ev → S → Prop} {pause : Nat → S → Prop}
variable {next : Nat → T → Obs → T → Prop} {idle : Nat → T → Prop}

/-- Local matching at a hardware tick. Each ideal transition must have a concrete
    transition at this tick. A concrete pause leaves the ideal machine both unchanged
    and without a transition at the same opportunity. -/
structure Taktbild (next : Nat → T → Obs → T → Prop) (idle : Nat → T → Prop)
    (t : Nat) (konkret : Option Ev) (i : T) (ideal : Option Obs) (i' : T) : Prop where
  takt : Takt next idle t i ideal i'
  pause : konkret = none → ideal = none ∧ KeinSchritt next t i

variable (ρ : Zeitlauf schritt pause) (bezug : S → T → Prop)
variable (lokal : Nat → T → Option Obs → T → Prop)

/-- A local extension returns only the next ideal state and label. Its proof concerns
    the current tick, with the current concrete step and the current state relation. -/
abbrev Fortsetzung (next : Nat → T → Obs → T → Prop) (idle : Nat → T → Prop) : Prop :=
  ∀ t i, bezug (ρ.zustand t) i →
    ∃ r : T × Option Obs, bezug (ρ.zustand (t + 1)) r.1 ∧ Taktbild next idle t (ρ.spur t) i r.2 r.1 ∧ lokal t i r.2 r.1

/-- Choose a chain of related ideal states and incoming labels, recursively from the
    fixed initial state. The relation holds by construction on every prefix. -/
noncomputable def bildFolge (start : T) (init : bezug (ρ.zustand 0) start)
    (folgt : Fortsetzung ρ bezug lokal next idle) : (t : Nat) → { r : T × Option Obs // bezug (ρ.zustand t) r.1 }
  | 0 => ⟨(start, none), init⟩
  | t + 1 =>
    let alt := bildFolge start init folgt t
    let wahl := folgt t alt.val.1 alt.property
    ⟨Classical.choose wahl, (Classical.choose_spec wahl).1⟩

theorem bildFolge_takt (start : T) (init : bezug (ρ.zustand 0) start)
    (folgt : Fortsetzung ρ bezug lokal next idle) (t : Nat) :
    Taktbild next idle t (ρ.spur t) (bildFolge ρ bezug lokal start init folgt t).val.1
      (bildFolge ρ bezug lokal start init folgt (t + 1)).val.2 (bildFolge ρ bezug lokal start init folgt (t + 1)).val.1 ∧
    lokal t (bildFolge ρ bezug lokal start init folgt t).val.1
      (bildFolge ρ bezug lokal start init folgt (t + 1)).val.2 (bildFolge ρ bezug lokal start init folgt (t + 1)).val.1 :=
  (Classical.choose_spec (folgt t _ (bildFolge ρ bezug lokal start init folgt t).property)).2

/-- The single ideal run obtained by iterating local matches, with the precise
    initial state and with a local match at every tick. -/
theorem laufbild (start : T) (init : bezug (ρ.zustand 0) start) (folgt : Fortsetzung ρ bezug lokal next idle) :
    ∃ η : Zeitlauf next idle, η.zustand 0 = start ∧
      (∀ t, bezug (ρ.zustand t) (η.zustand t)) ∧
      (∀ t, Taktbild next idle t (ρ.spur t) (η.zustand t) (η.spur t) (η.zustand (t + 1)) ∧
        lokal t (η.zustand t) (η.spur t) (η.zustand (t + 1))) := by
  let f := bildFolge ρ bezug lokal start init folgt
  exact ⟨⟨fun t => (f t).val.1, fun t => (f (t + 1)).val.2,
    fun t => (bildFolge_takt ρ bezug lokal start init folgt t).1.takt⟩, rfl, fun t => (f t).property,
    bildFolge_takt ρ bezug lokal start init folgt⟩

variable {ρ} {η : Zeitlauf next idle}

theorem endlich_ab (t : Nat) (tail : ∀ i, t ≤ i → ρ.spur i = none) : ρ.Endlich := by
  obtain ⟨k, _, noLater⟩ :
      ∃ k : ρ.Schnitt, k.val ≤ t ∧ ∀ i, k.val ≤ i → i < t → ρ.spur i = none := by
    clear tail
    induction t with
    | zero => exact ⟨⟨0, Or.inl rfl⟩, Nat.le_refl _, fun _ _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ t ih =>
      cases event : ρ.spur t with
      | none =>
        obtain ⟨k, before, empty⟩ := ih
        refine ⟨k, Nat.le_succ_of_le before, fun i after earlier => ?_⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ earlier) with lt | eq
        · exact empty i after lt
        · exact eq.symm ▸ event
      | some e =>
        exact ⟨⟨t + 1, Or.inr ⟨t, e, rfl, event⟩⟩, Nat.le_refl _,
          fun _ le lt => (Nat.not_lt_of_ge le lt).elim⟩
  exact ⟨k, fun i fromCut => (Nat.lt_or_ge i t).elim (noLater i fromCut) (tail i)⟩

/-- A private suffix cannot continue forever at a fixed ideal state when each
    concrete transition strictly decreases a natural-number measure. -/
theorem endlich_iff (gedeckt : ∀ t, ρ.spur t = none → η.spur t = none)
    (mass : Nat → Nat) (bleibt : ∀ t, ρ.spur t = none → mass (t + 1) = mass t)
    (sinkt : ∀ t event, η.spur t = none → ρ.spur t = some event → mass (t + 1) < mass t) :
    ρ.Endlich ↔ η.Endlich := by
  constructor
  · rintro ⟨k, tail⟩
    exact endlich_ab k.val fun t after => gedeckt t (tail t after)
  · rintro ⟨k, tail⟩
    classical
    let P (n : Nat) := ∃ t, k.val ≤ t ∧ mass t = n
    have existsMass : ∃ n, P n := ⟨mass k.val, k.val, Nat.le_refl _, rfl⟩
    obtain ⟨t₀, after₀, eq₀⟩ := Nat.find_spec existsMass
    have quiet (t : Nat) (after : t₀ ≤ t) (eq : mass t = mass t₀) : ρ.spur t = none := by
      cases event : ρ.spur t with
      | none => rfl
      | some step =>
        have after' := Nat.le_trans after₀ after
        have smaller := sinkt t step (tail t after') event
        have least := Nat.find_min' existsMass
          (show P (mass (t + 1)) from ⟨t + 1, Nat.le_succ_of_le after', rfl⟩)
        exact (Nat.not_lt_of_ge least (smaller.trans_le (eq.trans eq₀).le)).elim
    have constant (n : Nat) : mass (t₀ + n) = mass t₀ := by
      induction n with
      | zero => rfl
      | succ n ih =>
        exact (bleibt _ (quiet _ (Nat.le_add_right _ _) ih)).trans ih
    exact endlich_ab t₀ fun t after => quiet t after (by
      simpa only [Nat.add_sub_of_le after] using constant (t - t₀))

end Gabbro.Core.Maschine.Zeitlauf
