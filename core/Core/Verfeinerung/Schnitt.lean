module

public import Core.Maschine.Zeitlauf

@[expose] public section

namespace Gabbro.Core.Maschine.Zeitlauf

variable {S Ev : Type} {schritt : Nat → S → Ev → S → Prop} {pause : Nat → S → Prop}

/-- The last actual cut of a time-indexed run, including the initial cut. During a
    hardware pause the index stays fixed. -/
def letzterSchnitt (ρ : Zeitlauf schritt pause) : Nat → ρ.Schnitt
  | 0 => ⟨0, Or.inl rfl⟩
  | t + 1 => if h : (ρ.spur t).isSome then
      ⟨t + 1, Or.inr ((Option.isSome_iff_exists.mp h).elim fun e eq => ⟨t, e, rfl, eq⟩)⟩
    else ρ.letzterSchnitt t

theorem letzterSchnitt_wartet (ρ : Zeitlauf schritt pause) {t : Nat} (h : ρ.spur t = none) :
    ρ.letzterSchnitt (t + 1) = ρ.letzterSchnitt t := by
  rw [letzterSchnitt]
  exact dite_eq_right (fun present => Option.isSome_iff_ne_none.mp present h)

theorem letzterSchnitt_schritt (ρ : Zeitlauf schritt pause) {t : Nat} {e : Ev}
    (h : ρ.spur t = some e) :
    ρ.letzterSchnitt (t + 1) = ⟨t + 1, Or.inr ⟨t, e, rfl, h⟩⟩ := by
  rw [letzterSchnitt]
  exact dite_eq_left (Option.isSome_iff_exists.mpr ⟨e, h⟩)

theorem letzterSchnitt_vor (ρ : Zeitlauf schritt pause) (t : Nat) :
    (ρ.letzterSchnitt t).val ≤ t := by
  induction t with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    cases h : ρ.spur t with
    | none => simpa only [letzterSchnitt_wartet ρ h] using Nat.le_trans ih (Nat.le_succ t)
    | some e => simp only [letzterSchnitt_schritt ρ h, Nat.le_refl]

theorem letzterSchnitt_zustand (ρ : Zeitlauf schritt pause) (t : Nat) :
    ρ.zustand (ρ.letzterSchnitt t).val = ρ.zustand t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    cases h : ρ.spur t with
    | none => simpa only [letzterSchnitt_wartet ρ h] using ih.trans (ρ.wartet h).1.symm
    | some e => simp only [letzterSchnitt_schritt ρ h]

theorem letzterSchnitt_fix (ρ : Zeitlauf schritt pause) (k : ρ.Schnitt) :
    ρ.letzterSchnitt k.val = k := by
  obtain ⟨t, first | ⟨n, e, eq, event⟩⟩ := k
  · subst t
    rfl
  · subst t
    rw [letzterSchnitt_schritt ρ event]

theorem letzterSchnitt_monoton (ρ : Zeitlauf schritt pause) {a b : Nat} (le : a ≤ b) :
    (ρ.letzterSchnitt a).val ≤ (ρ.letzterSchnitt b).val := by
  induction le with
  | refl => exact Nat.le_refl _
  | @step b _ ih =>
    cases h : ρ.spur b with
    | none => simpa only [letzterSchnitt_wartet ρ h] using ih
    | some e => simpa only [letzterSchnitt_schritt ρ h] using
        Nat.le_succ_of_le (Nat.le_trans ih (letzterSchnitt_vor ρ b))

variable {T Obs : Type} {next : Nat → T → Obs → T → Prop} {idle : Nat → T → Prop}

/-- The ideal cut at the same hardware index, or the preceding one when the ideal
    machine pauses. The map covers the ideal run whenever every ideal transition
    has a concrete transition at its hardware tick. -/
def schnittBild (ρ : Zeitlauf schritt pause) (η : Zeitlauf next idle) (k : ρ.Schnitt) :
    η.Schnitt :=
  η.letzterSchnitt k.val

theorem schnittBild_deckt (ρ : Zeitlauf schritt pause) (η : Zeitlauf next idle)
    (gedeckt : ∀ n, ρ.spur n = none → η.spur n = none) :
    Function.Surjective (schnittBild ρ η) := by
  rintro ⟨t, first | ⟨n, e, eq, event⟩⟩
  · subst t
    exact ⟨⟨0, Or.inl rfl⟩, rfl⟩
  · subst t
    cases h : ρ.spur n with
    | none => cases (gedeckt n h).symm.trans event
    | some step => exact ⟨⟨n + 1, Or.inr ⟨n, step, rfl, h⟩⟩,
        letzterSchnitt_fix η ⟨n + 1, Or.inr ⟨n, e, rfl, event⟩⟩⟩

/-- Ordered observations of the transitions strictly before the given cut. -/
def praefix (spur : Nat → List Ev) : Nat → List Ev
  | 0 => []
  | t + 1 => praefix spur t ++ spur t

theorem praefix_letzterSchnitt (ρ : Zeitlauf schritt pause) (spur : Nat → List Obs)
    (leer : ∀ t, ρ.spur t = none → spur t = []) (t : Nat) :
    praefix spur (ρ.letzterSchnitt t).val = praefix spur t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    cases event : ρ.spur t with
    | none => simpa only [letzterSchnitt_wartet ρ event, praefix, leer t event, List.append_nil] using ih
    | some e => rw [letzterSchnitt_schritt ρ event]

end Gabbro.Core.Maschine.Zeitlauf
