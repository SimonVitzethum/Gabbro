module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.RfindBlock

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The pinned divergence obligation is false as parsed. Because `→` binds more
    tightly than `↔`, its body reads `(premises → LHS) ↔ LaufStirbtNicht`; a
    frame past the program end makes the left side vacuously true and the right
    side false. -/
theorem rfindDivergenzAussageFalsch :
    ¬ rfindDivergenzAussage ([.springe 200] : List Befehl)
        (Nat.Partrec.Code.const 1) 0 0 10 30 20 := by
  intro hDiv
  let cfBlk : List Befehl := [.springe 200]
  let rBasis : Rahmen := Rahmen.start []
  let r : Rahmen := { rBasis with pc := 244 }
  have hEquiv := hDiv 0 r
  have hLeft : (r.pc = 0 →
      r.temp (10 + 0) = some (natVal 0) →
      r.temp (10 + 1) = some (natVal 0) →
      r.temp (10 + 2) = some (natVal 0) →
      ((∀ y, 0 ≤ y → ∃ v, Nat.Partrec.Code.eval (Nat.Partrec.Code.const 1)
          (Nat.pair 0 y) = Part.some v) ∧
        (∀ y, 0 ≤ y → Nat.Partrec.Code.eval (Nat.Partrec.Code.const 1)
          (Nat.pair 0 y) ≠ Part.some 0))) := by
    intro hpc
    change (244 : Nat) = 0 at hpc
    omega
  have hNotLive : ¬ LaufStirbtNicht (rfindSchleife cfBlk 0 10) r := by
    intro hlive
    obtain ⟨r', hr'⟩ := hlive 1
    have hnone : Schritt (rfindSchleife cfBlk 0 10) (some r) = none := by
      have hlen : (rfindSchleife cfBlk 0 10).length = 54 := by rfl
      have hget : (rfindSchleife cfBlk 0 10)[r.pc]? = none := by
        change (rfindSchleife cfBlk 0 10)[244]? = none
        exact getLenKein _ 244 (by rw [hlen]; omega)
      simp only [Schritt, hget]
    change Schritt (rfindSchleife cfBlk 0 10) (some r) = none at hr'
    rw [hnone] at hr'
    cases hr'
  exact hNotLive (hEquiv.mp hLeft)

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
