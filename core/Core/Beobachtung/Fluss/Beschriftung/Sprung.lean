module

public import Core.Beobachtung.Fluss.Beschriftung.Skalar

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung

/-- `springe`: only the program counter moves. -/
def SpringeSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc abstand : Nat),
    (∀ s, oeffentlich (β.temp (pc + abstand) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + abstand) i) = true → oeffentlich (β.lokal pc i) = true) →
    (Befehl.springe abstand).SichtErhaltendBei β pc

/-- `springeWenn`: the tested temporary must be public (the branch is public control), and
    both successors keep the labels at least as secret. -/
def SpringeWennSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc quelle abstand : Nat) (bei : Bool),
    oeffentlich (β.temp pc quelle) = true →
    (∀ q, q = pc + 1 ∨ q = pc + abstand →
      (∀ s, oeffentlich (β.temp q s) = true → oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal q i) = true → oeffentlich (β.lokal pc i) = true)) →
    (Befehl.springeWenn quelle bei abstand).SichtErhaltendBei β pc

/-- The view after only the program counter moved, as a change of the view before. -/
theorem sicht_springe (β : Beschriftung) (r : Rahmen) (q : Nat) :
    ({ r with pc := q } : Rahmen).sicht β =
      { r.sicht β with
        pc := q
        temp := fun s => if oeffentlich (β.temp q s) = true then r.temp s else none
        lokale := maskiere (β.lokal q) 0 r.lokale } :=
  rfl

/-- Public equality at `pc` gives public equality of the temporaries and locals there. -/
theorem sicht_oeffentliche_teile {β : Beschriftung} {r₁ r₂ : Rahmen} (h : r₁.sicht β = r₂.sicht β) :
    r₂.pc = r₁.pc ∧ (∀ s, oeffentlich (β.temp r₁.pc s) = true → r₁.temp s = r₂.temp s) ∧
      maskiere (β.lokal r₁.pc) 0 r₁.lokale = maskiere (β.lokal r₁.pc) 0 r₂.lokale := by
  have pcEq : r₂.pc = r₁.pc := (sicht_pc h).symm
  refine ⟨pcEq, fun s hs => ?_, ?_⟩
  · have e : (if oeffentlich (β.temp r₁.pc s) = true then r₁.temp s else none) =
        (if oeffentlich (β.temp r₂.pc s) = true then r₂.temp s else none) :=
      congrFun (congrArg Rahmen.temp h) s
    rw [pcEq] at e
    simpa only [hs, if_true] using e
  · have e : maskiere (β.lokal r₁.pc) 0 r₁.lokale = maskiere (β.lokal r₂.pc) 0 r₂.lokale :=
      congrArg Rahmen.lokale h
    rw [pcEq] at e
    exact e

/-- Moving the program counter to `q` keeps public equality when the labels at `q` are at
    least as secret as at the current position. -/
theorem sicht_pcWechsel {β : Beschriftung} {q : Nat} {r₁ r₂ : Rahmen}
    (hT : ∀ s, oeffentlich (β.temp q s) = true → oeffentlich (β.temp r₁.pc s) = true)
    (hL : ∀ i, oeffentlich (β.lokal q i) = true → oeffentlich (β.lokal r₁.pc i) = true)
    (h : r₁.sicht β = r₂.sicht β) :
    ({ r₁ with pc := q } : Rahmen).sicht β = ({ r₂ with pc := q } : Rahmen).sicht β := by
  obtain ⟨_, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  rw [sicht_springe, sicht_springe, h]
  have hTe : (fun s => if oeffentlich (β.temp q s) = true then r₁.temp s else none) =
      (fun s => if oeffentlich (β.temp q s) = true then r₂.temp s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp q s) = true
    · simp only [hp, if_true]
      exact tempPub s (hT s hp)
    · simp only [if_neg hp]
  rw [hTe, maskiere_gleich_mono hL 0 _ _ lokEq]
  rfl

theorem springeSicht : SpringeSichtAussage := by
  intro β pc abstand hT hL r₁ r₂ live hpc h
  subst hpc
  have pcEq : r₂.pc = r₁.pc := (sicht_pc h).symm
  simp only [Befehl.auswerten, pcEq]
  exact sicht_pcWechsel hT hL h

theorem springeWennSicht : SpringeWennSichtAussage := by
  intro β pc quelle abstand bei hq hs r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, _⟩ := sicht_oeffentliche_teile h
  have gleich : r₁.temp quelle = r₂.temp quelle := tempPub quelle hq
  simp only [Befehl.auswerten, pcEq, gleich]
  by_cases t : (r₂.temp quelle).bind alsBoolean = some bei
  · simp only [t, if_true]
    have hs' := hs (r₁.pc + abstand) (Or.inr rfl)
    exact sicht_pcWechsel hs'.1 hs'.2 h
  · simp only [t, if_false]
    have hs' := hs (r₁.pc + 1) (Or.inl rfl)
    exact sicht_pcWechsel hs'.1 hs'.2 h


end Gabbro.Core.Ast.Semantik
