module

public import Core.Beobachtung.Fluss.Beschriftung.Regel

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung

/-- The view of a frame after `schreibe`, written as a change of the view before it. -/
theorem sicht_schreibe (β : Beschriftung) (r : Rahmen) (dst : Nat) (v : Option Dynamisch) :
    (r.schreibe dst v).sicht β =
      { r.sicht β with
        pc := r.pc + 1
        temp := fun s => if oeffentlich (β.temp (r.pc + 1) s) = true then
          Function.update r.temp dst v s else none
        lokale := maskiere (β.lokal (r.pc + 1)) 0 r.lokale } :=
  rfl

/-- **One write rule serves every instruction of that shape.** -/
theorem Befehl.sichtErhaltend_schreibform {β : Beschriftung} {pc dst : Nat} {liest : List Komp}
    {f : Befehl} (form : f.Schreibform dst liest) (regel : β.SchreibRegel pc dst liest) :
    f.SichtErhaltendBei β pc := by
  obtain ⟨g, hf, cong⟩ := form
  obtain ⟨hT, hL, hD⟩ := regel
  intro r₁ r₂ live hpc h
  subst hpc
  rw [hf, hf]
  have pcEq : r₂.pc = r₁.pc := (sicht_pc h).symm
  have tempEq : ∀ s, (if oeffentlich (β.temp r₁.pc s) = true then r₁.temp s else none) =
      (if oeffentlich (β.temp r₁.pc s) = true then r₂.temp s else none) := by
    intro s
    have e : (if oeffentlich (β.temp r₁.pc s) = true then r₁.temp s else none) =
        (if oeffentlich (β.temp r₂.pc s) = true then r₂.temp s else none) :=
      congrFun (congrArg Rahmen.temp h) s
    rw [pcEq] at e
    exact e
  have lokEq : maskiere (β.lokal r₁.pc) 0 r₁.lokale = maskiere (β.lokal r₁.pc) 0 r₂.lokale := by
    have e : maskiere (β.lokal r₁.pc) 0 r₁.lokale = maskiere (β.lokal r₂.pc) 0 r₂.lokale :=
      congrArg Rahmen.lokale h
    rw [pcEq] at e
    exact e
  have tempPub : ∀ s, oeffentlich (β.temp r₁.pc s) = true → r₁.temp s = r₂.temp s := by
    intro s hs
    simpa only [hs, if_true] using tempEq s
  have lokPub : ∀ i, oeffentlich (β.lokal r₁.pc i) = true →
      r₁.lokale[i]?.join = r₂.lokale[i]?.join := by
    intro i hi
    exact maskiere_eintrag 0 _ _ i lokEq (by simpa only [Nat.zero_add] using hi)
  have gleich : oeffentlich (β.temp (r₁.pc + 1) dst) = true → g r₁ = g r₂ := by
    intro hs
    refine cong r₁ r₂ fun k hk => ?_
    have pub := hD hs k hk
    cases k with
    | temp s => exact tempPub s pub
    | lokal i => exact lokPub i pub
  have hTe : (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then
        Function.update r₁.temp dst (g r₁) s else none) =
      (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then
        Function.update r₂.temp dst (g r₂) s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
    · simp only [hp, if_true]
      by_cases hs : s = dst
      · subst hs
        simp only [Function.update_self]
        exact gleich hp
      · simp only [Function.update_of_ne hs]
        exact tempPub s (hT s hs hp)
    · simp only [if_neg hp]
  have hLe : maskiere (β.lokal (r₁.pc + 1)) 0 r₁.lokale =
      maskiere (β.lokal (r₁.pc + 1)) 0 r₂.lokale :=
    maskiere_gleich_mono hL 0 _ _ lokEq
  rw [sicht_schreibe, sicht_schreibe, h, pcEq, hTe, hLe]

end Gabbro.Core.Ast.Semantik
