module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBlock

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Exact machine multiplication on two natural-valued slots. -/
theorem schrittMulNat (blk : List Befehl) (r : Rahmen) (p links x y : Nat)
    (hpc : r.pc = p)
    (hx : r.temp links = some (natVal x))
    (hy : r.temp (links + 1) = some (natVal y))
    (h : blk[p]? = some (.binaer .mul links)) :
    Schritt blk (some r) = some { r with pc := p + 1, temp := Function.update r.temp links (some (natVal (x * y))) } := by
  let A : Ganzzahl := ⟨(x : Int), (x : Int), Zahl.literal (x : Int)⟩
  let B : Ganzzahl := ⟨(y : Int), (y : Int), Zahl.literal (y : Int)⟩
  have ha : r.zahl links = some A := by
    show ((r.temp links).bind alsGanzzahl) = _
    rw [hx]
    rfl
  have hb : r.zahl (links + 1) = some B := by
    show ((r.temp (links + 1)).bind alsGanzzahl) = _
    rw [hy]
    rfl
  have e := schrittBinaer blk r p links .mul A B hpc ha hb h
  have hp : (Ganzzahl.pack ⟨_, _, Arith.auswerten .mul A.zahl B.zahl⟩ : Dynamisch) = natVal (x * y) := by
    dsimp only [A, B]
    exact packMulNat x y
  rw [e, hpc, hp]

/-- Exact machine addition on two natural-valued slots. -/
theorem schrittAddNat (blk : List Befehl) (r : Rahmen) (p links x y : Nat)
    (hpc : r.pc = p)
    (hx : r.temp links = some (natVal x))
    (hy : r.temp (links + 1) = some (natVal y))
    (h : blk[p]? = some (.binaer .add links)) :
    Schritt blk (some r) = some { r with pc := p + 1, temp := Function.update r.temp links (some (natVal (x + y))) } := by
  let A : Ganzzahl := ⟨(x : Int), (x : Int), Zahl.literal (x : Int)⟩
  let B : Ganzzahl := ⟨(y : Int), (y : Int), Zahl.literal (y : Int)⟩
  have ha : r.zahl links = some A := by
    show ((r.temp links).bind alsGanzzahl) = _
    rw [hx]
    rfl
  have hb : r.zahl (links + 1) = some B := by
    show ((r.temp (links + 1)).bind alsGanzzahl) = _
    rw [hy]
    rfl
  have e := schrittBinaer blk r p links .add A B hpc ha hb h
  have hp : (Ganzzahl.pack ⟨_, _, Arith.auswerten .add A.zahl B.zahl⟩ : Dynamisch) = natVal (x + y) := by
    dsimp only [A, B]
    exact packAddNat x y
  rw [e, hpc, hp]

/-- Exact machine comparison on two natural-valued slots. -/
theorem schrittVergleichNat (blk : List Befehl) (r : Rahmen) (p links x y : Nat)
    (hpc : r.pc = p)
    (hx : r.temp links = some (natVal x))
    (hy : r.temp (links + 1) = some (natVal y))
    (h : blk[p]? = some (.vergleichen .lt links)) :
    Schritt blk (some r) = some { r with pc := p + 1, temp := Function.update r.temp links (some ⟨.bool, Compare.eval .lt (x : Int) (y : Int)⟩) } := by
  let A : Ganzzahl := ⟨(x : Int), (x : Int), Zahl.literal (x : Int)⟩
  let B : Ganzzahl := ⟨(y : Int), (y : Int), Zahl.literal (y : Int)⟩
  have ha : r.zahl links = some A := by
    show ((r.temp links).bind alsGanzzahl) = _
    rw [hx]
    rfl
  have hb : r.zahl (links + 1) = some B := by
    show ((r.temp (links + 1)).bind alsGanzzahl) = _
    rw [hy]
    rfl
  have e := schrittVergleichen blk r p links .lt A B hpc ha hb h
  rw [e, hpc]
  dsimp only [A, B]
  rfl

/-- One iteration is definitionally one machine step. -/
theorem schrittAlsIterate (blk : List Befehl) (r : Rahmen) :
    (Schritt blk)^[1] (some r) = Schritt blk (some r) := rfl

/-- Concatenate two iterated runs. -/
theorem kettenSchritt (blk : List Befehl) (r₀ r₁ r₂ : Rahmen) (m n : Nat)
    (h₁ : (Schritt blk)^[m] (some r₀) = some r₁)
    (h₂ : (Schritt blk)^[n] (some r₁) = some r₂) :
    (Schritt blk)^[n + m] (some r₀) = some r₂ := by
  rw [Function.iterate_add_apply, h₁, h₂]

/-- Append one plain machine step to an iterated run. -/
theorem kettenEinSchritt (blk : List Befehl) (r₀ r₁ r₂ : Rahmen) (m : Nat)
    (h₁ : (Schritt blk)^[m] (some r₀) = some r₁)
    (h₂ : Schritt blk (some r₁) = some r₂) :
    (Schritt blk)^[1 + m] (some r₀) = some r₂ := by
  rw [Function.iterate_add_apply, h₁, schrittAlsIterate, h₂]

/-- The shared prefix of the pairing computation, as explicit frames. -/
def pb1 (r : Rahmen) (a frei : Nat) : Rahmen :=
  { r with pc := 3, temp := Function.update r.temp frei (some (natVal a)) }
def pb2 (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb1 r a frei with pc := 6, temp := Function.update (pb1 r a frei).temp (frei + 1) (some (natVal b)) }
def pb3 (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb2 r a b frei with pc := 9, temp := Function.update (pb2 r a b frei).temp (frei + 2) (some (natVal a)) }
def pb4 (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb3 r a b frei with pc := 12, temp := Function.update (pb3 r a b frei).temp (frei + 3) (some (natVal b)) }
def pb5 (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb4 r a b frei with pc := 13, temp := Function.update (pb4 r a b frei).temp frei (some ⟨.bool, Compare.eval .lt (a : Int) (b : Int)⟩) }

/-- The true (`a < b`) branch frames. -/
def pb6w (r : Rahmen) (a b frei : Nat) : Rahmen := { pb5 r a b frei with pc := 30 }
def pb7w (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb6w r a b frei with pc := 33, temp := Function.update (pb6w r a b frei).temp (frei + 4) (some (natVal b)) }
def pb8w (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb7w r a b frei with pc := 36, temp := Function.update (pb7w r a b frei).temp (frei + 5) (some (natVal b)) }
def pb9w (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb8w r a b frei with pc := 37, temp := Function.update (pb8w r a b frei).temp (frei + 4) (some (natVal (b * b))) }
def pb10w (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb9w r a b frei with pc := 40, temp := Function.update (pb9w r a b frei).temp (frei + 5) (some (natVal a)) }
def pb11w (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb10w r a b frei with pc := 41, temp := Function.update (pb10w r a b frei).temp (frei + 4) (some (natVal (b * b + a))) }
def pb12w (r : Rahmen) (a b aus frei : Nat) : Rahmen :=
  { pb11w r a b frei with pc := 44, temp := Function.update (pb11w r a b frei).temp aus (some (natVal (b * b + a))) }

/-- The false (`¬ a < b`) branch frames. -/
def pb6f (r : Rahmen) (a b frei : Nat) : Rahmen := { pb5 r a b frei with pc := 14 }
def pb7f (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb6f r a b frei with pc := 17, temp := Function.update (pb6f r a b frei).temp (frei + 4) (some (natVal a)) }
def pb8f (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb7f r a b frei with pc := 20, temp := Function.update (pb7f r a b frei).temp (frei + 5) (some (natVal a)) }
def pb9f (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb8f r a b frei with pc := 21, temp := Function.update (pb8f r a b frei).temp (frei + 4) (some (natVal (a * a))) }
def pb10f (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb9f r a b frei with pc := 22, temp := Function.update (pb9f r a b frei).temp (frei + 4) (some (natVal (a * a + a))) }
def pb11f (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb10f r a b frei with pc := 25, temp := Function.update (pb10f r a b frei).temp (frei + 5) (some (natVal b)) }
def pb12f (r : Rahmen) (a b frei : Nat) : Rahmen :=
  { pb11f r a b frei with pc := 26, temp := Function.update (pb11f r a b frei).temp (frei + 4) (some (natVal (a * a + a + b))) }
def pb13f (r : Rahmen) (a b aus frei : Nat) : Rahmen :=
  { pb12f r a b frei with pc := 29, temp := Function.update (pb12f r a b frei).temp aus (some (natVal (a * a + a + b))) }
def pb14f (r : Rahmen) (a b aus frei : Nat) : Rahmen := { pb13f r a b aus frei with pc := 44 }

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
