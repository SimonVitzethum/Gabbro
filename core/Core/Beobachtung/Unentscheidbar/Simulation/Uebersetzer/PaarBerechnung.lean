module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.BleibtImBlock

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The machine product of two natural literals is the exact natural value. -/
theorem packMulNat (x y : Nat) :
    (Ganzzahl.pack ⟨_, _, Arith.auswerten .mul
      (Zahl.literal (x : Int)) (Zahl.literal (y : Int))⟩) = natVal (x * y) := by
  have e : (x : Int) * (y : Int) = (((x * y : Nat)) : Int) := (Nat.cast_mul x y).symm
  have hlo : (Arith.mul.bounds (x : Int) (x : Int) (y : Int) (y : Int)).1 =
      (((x * y : Nat)) : Int) := by
    simp only [Arith.bounds]
    omega
  have hhi : (Arith.mul.bounds (x : Int) (x : Int) (y : Int) (y : Int)).2 =
      (((x * y : Nat)) : Int) := by
    simp only [Arith.bounds]
    omega
  have hw : (Arith.auswerten .mul (Zahl.literal (x : Int)) (Zahl.literal (y : Int))).wert =
      (((x * y : Nat)) : Int) := e
  exact packEqOfBounds _ _ _ _ hlo hhi hw

/-- The machine sum of two natural literals is the exact natural value. -/
theorem packAddNat (x y : Nat) :
    (Ganzzahl.pack ⟨_, _, Arith.auswerten .add
      (Zahl.literal (x : Int)) (Zahl.literal (y : Int))⟩) = natVal (x + y) := by
  have e : (x : Int) + (y : Int) = (((x + y : Nat)) : Int) := by omega
  have hlo : (Arith.add.bounds (x : Int) (x : Int) (y : Int) (y : Int)).1 =
      (((x + y : Nat)) : Int) := by
    simp only [Arith.bounds]
    omega
  have hhi : (Arith.add.bounds (x : Int) (x : Int) (y : Int) (y : Int)).2 =
      (((x + y : Nat)) : Int) := by
    simp only [Arith.bounds]
    omega
  have hw : (Arith.auswerten .add (Zahl.literal (x : Int)) (Zahl.literal (y : Int))).wert =
      (((x + y : Nat)) : Int) := e
  exact packEqOfBounds _ _ _ _ hlo hhi hw

/-- The machine comparison of two naturals agrees with the natural one. -/
theorem vergleichLtNat (a b : Nat) :
    Compare.eval .lt ((a : Nat) : Int) ((b : Nat) : Int) = true ↔ a < b := by
  simp only [Compare.eval, decide_eq_true_eq, Int.ofNat_lt]

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
