module

public import Core.Beobachtung.Fluss.Beschriftung.Leck
public import Core.Beobachtung.Fluss.Beschriftung.Flussregel

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

/-- Copy the secret local into temporary 0, then compute a public constant in temporary 1. -/
def gutFragment : Fragment :=
  (Fragment.einzel (.lesen 0 0)).anhaengen (Fragment.einzel (.literal 1 7))

/-- Local 0 is secret throughout; temporary 0 is secret once it holds the copy. -/
def gutBeschriftung : Beschriftung :=
  { temp := fun pc s => if s = 0 ∧ 1 ≤ pc then geheim else ∅
    lokal := fun _ i => if i = 0 then geheim else ∅ }

theorem gut_temp (pc s : Nat) :
    oeffentlich (gutBeschriftung.temp pc s) = true ↔ ¬ (s = 0 ∧ 1 ≤ pc) := by
  simp only [gutBeschriftung]
  split
  · simp only [geheim_verborgen, Bool.false_eq_true, false_iff, not_not]
    assumption
  · rename_i h
    simp only [oeffentlich_leer, true_iff]
    exact h

theorem gut_lokal (pc i : Nat) :
    oeffentlich (gutBeschriftung.lokal pc i) = true ↔ i ≠ 0 := by
  simp only [gutBeschriftung]
  split
  · rename_i h
    simp only [geheim_verborgen, Bool.false_eq_true, false_iff, ne_eq, not_not]
    exact h
  · rename_i h
    simp only [oeffentlich_leer, true_iff]
    exact h

/-- The program is accepted: no secret reaches a public component. -/
theorem gut_akzeptiert : gutFragment.FlussAkzeptiert gutBeschriftung := by
  intro pc f hf
  have code : gutFragment.code = [.lesen 0 0, .literal 1 7] := rfl
  rw [code] at hf
  rcases pc with _ | _ | pc
  · have hf' : Befehl.lesen 0 0 = f := Option.some.inj hf
    subst hf'
    refine ⟨fun s hs h => ?_, fun i h => h, fun h => ?_⟩
    · simp only [gut_temp] at h ⊢
      omega
    · exact absurd (⟨rfl, Nat.le_refl 1⟩ : (0 : Nat) = 0 ∧ 1 ≤ 1) ((gut_temp 1 0).1 h)
  · have hf' : Befehl.literal 1 7 = f := Option.some.inj hf
    subst hf'
    refine ⟨fun s hs h => ?_, fun i h => h, fun h => ?_⟩
    · simp only [gut_temp] at h ⊢
      omega
    · intro k hk
      cases hk
  · simp at hf

/-- The labelled unit of the accepted program satisfies the labelled flow rule. -/
theorem gut_fluss_lokal (platform : Plattform) :
    FlussLokal (gutFragment.beschriftet platform gutBeschriftung) :=
  gutFragment.flussAkzeptiert_lokal platform gutBeschriftung gut_akzeptiert

/-- **Satisfiability of the labelled flow premise with different secrets.** Run the whole
    program from two frames that differ in the secret local: the frames differ, the public
    views are equal. -/
theorem gut_zwei_werte (x y : Bool) (live : Nat → Bool) :
    let lauf (z : Bool) := (Befehl.literal 1 7).auswerten
      ((Befehl.lesen 0 0).auswerten (rahmenGeheim z) live) live
    (lauf x).sicht gutBeschriftung = (lauf y).sicht gutBeschriftung ∧
      (x ≠ y → lauf x ≠ lauf y) := by
  intro lauf
  refine ⟨?_, fun hxy h => hxy ?_⟩
  · have anfang : (rahmenGeheim x).sicht gutBeschriftung = (rahmenGeheim y).sicht gutBeschriftung :=
      sicht_geheim gutBeschriftung (Bool.eq_false_iff.2 fun h => (gut_lokal 0 0).1 h rfl) x y
    have nach₀ := Befehl.sichtErhaltend (.lesen 0 0) (gut_akzeptiert 0 _ rfl) _ _ live rfl anfang
    exact Befehl.sichtErhaltend (.literal 1 7) (gut_akzeptiert 1 _ rfl) _ _ live rfl nach₀
  · have temp := congrFun (congrArg Rahmen.temp h) 0
    simp only [lauf, Befehl.auswerten, Rahmen.schreibe, rahmenGeheim, Rahmen.start,
      Function.update_apply] at temp
    cases temp
    rfl

end Gabbro.Core.Ast.Semantik
