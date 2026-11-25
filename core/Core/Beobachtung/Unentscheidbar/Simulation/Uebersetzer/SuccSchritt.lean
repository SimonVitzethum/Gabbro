module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Grundlagen

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The successor block: copy the input to a scratch slot, add one there,
    copy the result to the output slot. -/
def succBlk (ein aus frei : Nat) : List Befehl :=
  kopie frei ein ++ [.literal (frei + 1) 1, .binaer .add frei] ++ kopie aus frei

theorem succBlkLaenge (ein aus frei : Nat) : (succBlk ein aus frei).length = 8 := by
  rfl

def frameSucc1 (r : Rahmen) (ein frei : Nat) : Rahmen :=
  { r with pc := r.pc + 1, lokale := r.temp ein :: r.lokale }

def frameSucc2 (r : Rahmen) (ein frei : Nat) : Rahmen :=
  { frameSucc1 r ein frei with
    pc := r.pc + 2, temp := Function.update r.temp frei (r.temp ein) }

def frameSucc3 (r : Rahmen) (ein frei : Nat) : Rahmen :=
  { frameSucc2 r ein frei with pc := r.pc + 3, lokale := r.lokale }

def frameSucc4 (r : Rahmen) (ein frei : Nat) : Rahmen :=
  { frameSucc3 r ein frei with
    pc := r.pc + 4, temp := Function.update (frameSucc3 r ein frei).temp (frei + 1) (some (natVal 1)) }

def frameSucc5 (r : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameSucc4 r ein frei with
    pc := r.pc + 5,
    temp := Function.update (frameSucc4 r ein frei).temp frei
      (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .add (Zahl.literal (n : Int)) (Zahl.literal ((1 : Nat) : Int))⟩)) }

def frameSucc6 (r : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameSucc5 r ein aus frei n with
    pc := r.pc + 6, lokale := (frameSucc5 r ein aus frei n).temp frei :: r.lokale }

def frameSucc7 (r : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameSucc6 r ein aus frei n with
    pc := r.pc + 7,
    temp := Function.update (frameSucc6 r ein aus frei n).temp aus ((frameSucc6 r ein aus frei n).temp frei) }

def frameSucc8 (r : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameSucc7 r ein aus frei n with pc := r.pc + 8, lokale := r.lokale }

theorem natAusgabeAdd (n : Nat) : NatAusgabe
    (Ganzzahl.pack ⟨_, _, Arith.auswerten .add (Zahl.literal (n : Int)) (Zahl.literal ((1 : Nat) : Int))⟩) =
      some (n + 1) := by
  simp only [NatAusgabe, alsGanzzahl, Ganzzahl.pack, Arith.auswerten, Zahl.literal]
  rw [show (n : Int) + ((1 : Nat) : Int) = ((n + 1 : Nat) : Int) by omega]
  rw [if_pos (by omega : (0 : Int) ≤ ((n + 1 : Nat) : Int))]
  simp only [Int.toNat_natCast]

theorem succSchritt0 (ein aus frei : Nat) (r : Rahmen) (hpc : r.pc = 0) :
    Schritt (succBlk ein aus frei) (some r) = some (frameSucc1 r ein frei) := by
  have hget : (succBlk ein aus frei)[r.pc]? = some (.binden nameX ein) := by
    rw [hpc]
    rfl
  simp only [Schritt, hget]
  rfl

theorem succSchritt1 (ein aus frei : Nat) (r : Rahmen) (hpc : r.pc = 0) :
    Schritt (succBlk ein aus frei) (some (frameSucc1 r ein frei)) =
      some (frameSucc2 r ein frei) := by
  have hpc1 : (frameSucc1 r ein frei).pc = 1 := by
    show r.pc + 1 = 1
    omega
  have hget : (succBlk ein aus frei)[(frameSucc1 r ein frei).pc]? = some (.lesen frei 0) := by
    rw [hpc1]
    rfl
  simp only [Schritt, hget]
  rfl

theorem succSchritt2 (ein aus frei : Nat) (r : Rahmen) (hpc : r.pc = 0) :
    Schritt (succBlk ein aus frei) (some (frameSucc2 r ein frei)) =
      some (frameSucc3 r ein frei) := by
  have hpc2 : (frameSucc2 r ein frei).pc = 2 := by
    show r.pc + 2 = 2
    omega
  have hget : (succBlk ein aus frei)[(frameSucc2 r ein frei).pc]? = some (.blockEnde 1) := by
    rw [hpc2]
    rfl
  simp only [Schritt, hget]
  rfl

theorem succSchritt3 (ein aus frei : Nat) (r : Rahmen) (hpc : r.pc = 0) :
    Schritt (succBlk ein aus frei) (some (frameSucc3 r ein frei)) =
      some (frameSucc4 r ein frei) := by
  have hpc3 : (frameSucc3 r ein frei).pc = 3 := by
    show r.pc + 3 = 3
    omega
  have hget : (succBlk ein aus frei)[(frameSucc3 r ein frei).pc]? = some (.literal (frei + 1) 1) := by
    rw [hpc3]
    rfl
  simp only [Schritt, hget]
  rfl

theorem succSchritt4 (ein aus frei : Nat) (r : Rahmen) (hr : r.temp ein = some (natVal n))
    (hpc : r.pc = 0) (hein : ein < frei) :
    Schritt (succBlk ein aus frei) (some (frameSucc4 r ein frei)) =
      some (frameSucc5 r ein aus frei n) := by
  have hpc4 : (frameSucc4 r ein frei).pc = 4 := by
    show r.pc + 4 = 4
    omega
  have hget : (succBlk ein aus frei)[(frameSucc4 r ein frei).pc]? = some (.binaer .add frei) := by
    rw [hpc4]
    rfl
  have h1 : frei ≠ frei + 1 := by omega
  have hein1 : ein ≠ frei + 1 := by omega
  have heinf : ein ≠ frei := by omega
  have hF4t : (frameSucc4 r ein frei).temp =
      Function.update (frameSucc3 r ein frei).temp (frei + 1) (some (natVal 1)) := rfl
  have hF3t : (frameSucc3 r ein frei).temp = (frameSucc2 r ein frei).temp := rfl
  have hF2t : (frameSucc2 r ein frei).temp =
      Function.update (frameSucc1 r ein frei).temp frei (r.temp ein) := rfl
  have hF1t : (frameSucc1 r ein frei).temp = r.temp := rfl
  have hF4e : (frameSucc4 r ein frei).temp ein = some (natVal n) := by
    rw [hF4t, updateMiss _ _ _ _ hein1, hF3t, hF2t, updateMiss _ _ _ _ heinf, hF1t]
    exact hr
  have hz0 : (frameSucc4 r ein frei).zahl frei =
      some ⟨(n : Int), (n : Int), Zahl.literal (n : Int)⟩ := by
    show (((frameSucc4 r ein frei).temp frei).bind alsGanzzahl) = _
    rw [hF4t, updateMiss _ _ _ _ h1, hF3t, hF2t, updateHit, hr]
    rfl
  have hz1 : (frameSucc4 r ein frei).zahl (frei + 1) =
      some ⟨((1 : Nat) : Int), ((1 : Nat) : Int), Zahl.literal ((1 : Nat) : Int)⟩ := by
    show (((frameSucc4 r ein frei).temp (frei + 1)).bind alsGanzzahl) = _
    rw [hF4t, updateHit]
    rfl
  simp only [Schritt, hget, Befehl.auswerten, Rahmen.schreibe, hz0, hz1]
  rfl

theorem succSchritt5 (ein aus frei : Nat) (r : Rahmen) (n : Nat) (hpc : r.pc = 0) :
    Schritt (succBlk ein aus frei) (some (frameSucc5 r ein aus frei n)) =
      some (frameSucc6 r ein aus frei n) := by
  have hpc5 : (frameSucc5 r ein aus frei n).pc = 5 := by
    show r.pc + 5 = 5
    omega
  have hget : (succBlk ein aus frei)[(frameSucc5 r ein aus frei n).pc]? = some (.binden nameX frei) := by
    rw [hpc5]
    rfl
  simp only [Schritt, hget]
  rfl

theorem succSchritt6 (ein aus frei : Nat) (r : Rahmen) (n : Nat) (hpc : r.pc = 0) :
    Schritt (succBlk ein aus frei) (some (frameSucc6 r ein aus frei n)) =
      some (frameSucc7 r ein aus frei n) := by
  have hpc6 : (frameSucc6 r ein aus frei n).pc = 6 := by
    show r.pc + 6 = 6
    omega
  have hget : (succBlk ein aus frei)[(frameSucc6 r ein aus frei n).pc]? = some (.lesen aus 0) := by
    rw [hpc6]
    rfl
  simp only [Schritt, hget]
  rfl

theorem succSchritt7 (ein aus frei : Nat) (r : Rahmen) (n : Nat) (hpc : r.pc = 0) :
    Schritt (succBlk ein aus frei) (some (frameSucc7 r ein aus frei n)) =
      some (frameSucc8 r ein aus frei n) := by
  have hpc7 : (frameSucc7 r ein aus frei n).pc = 7 := by
    show r.pc + 7 = 7
    omega
  have hget : (succBlk ein aus frei)[(frameSucc7 r ein aus frei n).pc]? = some (.blockEnde 1) := by
    rw [hpc7]
    rfl
  simp only [Schritt, hget]
  rfl

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
