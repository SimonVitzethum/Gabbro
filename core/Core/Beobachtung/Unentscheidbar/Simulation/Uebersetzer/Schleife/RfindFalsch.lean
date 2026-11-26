module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.RfindBlock

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The pinned divergence obligation is false. Its statement quantifies over
    the translated block without any `BlockKorrekt` premise, so a block that
    leaves the loop early makes the run die although the code is total and never
    zero. -/
theorem rfindDivergenzAussageFalsch :
    ¬ rfindDivergenzAussage ([.springe 200] : List Befehl)
        (Nat.Partrec.Code.const 1) 0 0 10 30 20 := by
  intro hDiv
  let cfBlk : List Befehl := [.springe 200]
  let rBasis : Rahmen := Rahmen.start []
  let temp' : Nat → Option Dynamisch :=
    Function.update (Function.update (Function.update rBasis.temp 10 (some (natVal 0)))
      11 (some (natVal 0))) 12 (some (natVal 0))
  let r : Rahmen := { rBasis with temp := temp' }
  have hpc : r.pc = 0 := rfl
  have ha : r.temp (10 + 0) = some (natVal 0) := by
    simp only [r, Nat.add_zero, Function.update_self, Function.update_of_ne]
  have hm1 : r.temp (10 + 1) = some (natVal 0) := by
    simp only [r, Function.update_self, Function.update_of_ne]
  have hm2 : r.temp (10 + 2) = some (natVal 0) := by
    simp only [r, Function.update_self]
  have hEquiv := hDiv 0 r hpc ha hm1 hm2
  have hL : ((∀ y, 0 ≤ y → ∃ v, Nat.Partrec.Code.eval (Nat.Partrec.Code.const 1)
        (Nat.pair 0 y) = Part.some v) ∧
      (∀ y, 0 ≤ y → Nat.Partrec.Code.eval (Nat.Partrec.Code.const 1)
        (Nat.pair 0 y) ≠ Part.some 0)) := by
    constructor
    · intro y hy
      refine ⟨1, ?_⟩
      simpa only [Nat.Partrec.Code.eval_const]
    · intro y hy
      rw [Nat.Partrec.Code.eval_const]
      simp only [Part.some.injEq]
      omega
  have hRunDies : LaufStirbt (rfindSchleife cfBlk 0 10) r := by
    obtain ⟨k, rP, hrunP, hpcP, _, _, _, _, _⟩ :=
      paarVorwaerts 10 12 14 20 r 0 0 hpc ha hm2 (by omega) (by omega)
    have hbleib := laufBleibtVorEnde (paarBerechnung 10 12 14 20) r k rP hrunP hpcP
    have hrunLoop : (Schritt (rfindSchleife cfBlk 0 10))^[k] (some r) = some rP := by
      simpa only [rfindSchleife, cfBlk] using
        laufAnhang (paarBerechnung 10 12 14 20)
          (cfBlk ++ [.literal 15 0, .vergleichen .lt 15, .springeWenn 15 false 3] ++
            [.literal 17 1, .binaer .add 12, .zurueckSprung (49 + cfBlk.length)] ++
            kopie 0 12) r k hbleib
    have hstep1 : Schritt (rfindSchleife cfBlk 0 10) (some rP) =
        some { rP with pc := 244 } := by
      have hget : (rfindSchleife cfBlk 0 10)[rP.pc]? = some (.springe 200) := by
        rw [hpcP]
        rfl
      simpa only [Schritt, hget, Befehl.auswerten, hpcP]
    have hstep2 : Schritt (rfindSchleife cfBlk 0 10) (some { rP with pc := 244 }) = none := by
      have hlen : (rfindSchleife cfBlk 0 10).length = 54 := by rfl
      have hget : (rfindSchleife cfBlk 0 10)[244]? = none :=
        getLenKein _ 244 (by rw [hlen]; omega)
      simp only [Schritt, hget]
    refine ⟨k + 2, ?_⟩
    rw [show k + 2 = 2 + k by omega, Function.iterate_add_apply, hrunLoop]
    rw [show (2 : Nat) = 1 + 1 by omega, Function.iterate_add_apply, hstep1, hstep2]
  have hnotlive : ¬ LaufStirbtNicht (rfindSchleife cfBlk 0 10) r := by
    intro hlive
    exact (laufStirbtNicht_iff _ _).mp hlive hRunDies
  exact hnotlive (hEquiv.mp hL)

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
