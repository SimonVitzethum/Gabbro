module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Sqrt

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Selection after the search: square the root, subtract from the input
    for the difference `d`, then output `d` or the root depending on
    whether `d` is smaller. Select offsets follow the search exit at 25. -/
def leftSel (ein aus frei : Nat) : List Befehl :=
  [.binden nameX (frei + 0), .lesen (frei + 1) 0, .blockEnde 1, .binden nameX (frei + 1), .lesen (frei + 3) 0, .blockEnde 1, .binden nameX (frei + 1), .lesen (frei + 4) 0, .blockEnde 1, .binaer .mul (frei + 3), .binden nameX ein, .lesen (frei + 1) 0, .blockEnde 1, .binden nameX (frei + 1), .lesen (frei + 5) 0, .blockEnde 1, .binden nameX (frei + 3), .lesen (frei + 6) 0, .blockEnde 1, .binaer .sub (frei + 5), .binden nameX (frei + 5), .lesen (frei + 3) 0, .blockEnde 1, .binden nameX (frei + 0), .lesen (frei + 4) 0, .blockEnde 1, .vergleichen .lt (frei + 3), .springeWenn (frei + 3) true 5, .binden nameX (frei + 0), .lesen aus 0, .blockEnde 1, .springe 4, .binden nameX (frei + 5), .lesen aus 0, .blockEnde 1]

/-- The relocatable block for `left`: search prefix followed by selection. -/
def leftBlk (ein aus frei : Nat) : List Befehl :=
  sqrtPrefix ein frei ++ leftSel ein aus frei

theorem leftSelLaenge (ein aus frei : Nat) : (leftSel ein aus frei).length = 35 := by
  rfl

theorem leftBlkLaenge (ein aus frei : Nat) : (leftBlk ein aus frei).length = 60 := by
  rfl

/-- Selection states from the search exit, with `s` the integer root. -/
def frameL1 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { e with pc := 25 + 3, temp := Function.update e.temp (frei + 1) (some (natVal (Nat.sqrt n))) }
def frameL2 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL1 e ein aus frei n with pc := 25 + 6, temp := Function.update (frameL1 e ein aus frei n).temp (frei + 3) (some (natVal (Nat.sqrt n))) }
def frameL3 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL2 e ein aus frei n with pc := 25 + 9, temp := Function.update (frameL2 e ein aus frei n).temp (frei + 4) (some (natVal (Nat.sqrt n))) }
def frameL4 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL3 e ein aus frei n with pc := 25 + 10, temp := Function.update (frameL3 e ein aus frei n).temp (frei + 3) (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int))⟩)) }
def frameL5 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL4 e ein aus frei n with pc := 25 + 13, temp := Function.update (frameL4 e ein aus frei n).temp (frei + 1) (some (natVal n)) }
def frameL6 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL5 e ein aus frei n with pc := 25 + 16, temp := Function.update (frameL5 e ein aus frei n).temp (frei + 5) (some (natVal n)) }
def frameL7 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL6 e ein aus frei n with pc := 25 + 19, temp := Function.update (frameL6 e ein aus frei n).temp (frei + 6) (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int))⟩)) }
def frameL8 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL7 e ein aus frei n with pc := 25 + 20, temp := Function.update (frameL7 e ein aus frei n).temp (frei + 5) (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩)) }
def frameL9 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL8 e ein aus frei n with pc := 25 + 23, temp := Function.update (frameL8 e ein aus frei n).temp (frei + 3) (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩)) }
def frameL10 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL9 e ein aus frei n with pc := 25 + 26, temp := Function.update (frameL9 e ein aus frei n).temp (frei + 4) (some (natVal (Nat.sqrt n))) }

/-- The difference `n - s * s` as a machine integer comparison. -/
def cmpBoolLeft (s n : Nat) : Bool := Compare.eval .lt ((n : Int) - (s : Int) * (s : Int)) (s : Int)
def frameL11 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL10 e ein aus frei n with pc := 25 + 27, temp := Function.update (frameL10 e ein aus frei n).temp (frei + 3) (some ⟨.bool, cmpBoolLeft (Nat.sqrt n) n⟩) }
def frameL12t (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL11 e ein aus frei n with pc := 25 + 32 }
def frameL12e (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL11 e ein aus frei n with pc := 25 + 28 }
def frameL13t (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL12t e ein aus frei n with pc := 25 + 35, temp := Function.update (frameL12t e ein aus frei n).temp aus (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩)) }
def frameL13e (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL12e e ein aus frei n with pc := 25 + 31, temp := Function.update (frameL12e e ein aus frei n).temp aus (some (natVal (Nat.sqrt n))) }
def frameL14e (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL13e e ein aus frei n with pc := 25 + 35 }

/-- The machine difference decides the same way as the natural one. -/
theorem decideDlt (s n : Nat) (h : s * s ≤ n) :
    decide (((n : Int) - (s : Int) * (s : Int)) < (s : Int)) =
      decide (n - s * s < s) := by
  simp only [intSubNat s n h, Nat.cast_lt]

/-- The unpairing splits on the difference against the root. -/
theorem hunLeft (n : Nat) : Nat.unpair n =
    (if n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n
      then (n - Nat.sqrt n * Nat.sqrt n, Nat.sqrt n)
      else (Nat.sqrt n, n - Nat.sqrt n * Nat.sqrt n - Nat.sqrt n)) := rfl

/-- The left projection selects the difference when it is smaller. -/
theorem hunLeftT (n : Nat) (h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n) :
    (Nat.unpair n).1 = n - Nat.sqrt n * Nat.sqrt n := by
  rw [hunLeft n, if_pos h]

theorem hunLeftE (n : Nat) (h : ¬ (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n)) :
    (Nat.unpair n).1 = Nat.sqrt n := by
  rw [hunLeft n, if_neg h]

/-- Selection links from the search exit; the exit state `e` carries
    the root in `frei + 0` and the input in `ein`. -/
theorem selLink1 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n))) :
    (Schritt (leftBlk ein aus frei))^[3] (some e) =
      some (frameL1 e ein aus frei n) := by
  have g0 : (leftBlk ein aus frei)[25]? = some (.binden nameX (frei + 0)) := by rfl
  have g1 : (leftBlk ein aus frei)[25 + 1]? = some (.lesen (frei + 1) 0) := by rfl
  have g2 : (leftBlk ein aus frei)[25 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 25 (frei + 1) (frei + 0) _ hepc hes g0 g1 g2
  simpa only [frameL1] using e0

theorem selLink2 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n))) :
    (Schritt (leftBlk ein aus frei))^[6] (some e) =
      some (frameL2 e ein aus frei n) := by
  have h11 := selLink1 ein aus frei n e hepc hes
  have hpc : (frameL1 e ein aus frei n).pc = 28 := rfl
  have hq : (frameL1 e ein aus frei n).temp (frei + 1) = some (natVal (Nat.sqrt n)) :=
    updateHit _ _ _
  have g0 : (leftBlk ein aus frei)[28]? = some (.binden nameX (frei + 1)) := by rfl
  have g1 : (leftBlk ein aus frei)[28 + 1]? = some (.lesen (frei + 3) 0) := by rfl
  have g2 : (leftBlk ein aus frei)[28 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 28 (frei + 3) (frei + 1) _ hpc hq g0 g1 g2
  have e1 : (Schritt (leftBlk ein aus frei))^[6] (some e) =
      (Schritt (leftBlk ein aus frei))^[3]
        ((Schritt (leftBlk ein aus frei))^[3] (some e)) := by
    rw [show (6 : Nat) = 3 + 3 from rfl, Function.iterate_add_apply]
  rw [e1, h11]
  simpa only [frameL2] using e0

theorem selLink3 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n))) :
    (Schritt (leftBlk ein aus frei))^[9] (some e) =
      some (frameL3 e ein aus frei n) := by
  have h22 := selLink2 ein aus frei n e hepc hes
  have hpc : (frameL2 e ein aus frei n).pc = 31 := rfl
  have hq : (frameL2 e ein aus frei n).temp (frei + 1) = some (natVal (Nat.sqrt n)) := by
    show Function.update _ (frei + 3) _ (frei + 1) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (3 : Nat) ≠ 1))]
    exact updateHit _ _ _
  have g0 : (leftBlk ein aus frei)[31]? = some (.binden nameX (frei + 1)) := by rfl
  have g1 : (leftBlk ein aus frei)[31 + 1]? = some (.lesen (frei + 4) 0) := by rfl
  have g2 : (leftBlk ein aus frei)[31 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 31 (frei + 4) (frei + 1) _ hpc hq g0 g1 g2
  have e1 : (Schritt (leftBlk ein aus frei))^[9] (some e) =
      (Schritt (leftBlk ein aus frei))^[3]
        ((Schritt (leftBlk ein aus frei))^[6] (some e)) := by
    rw [show (9 : Nat) = 3 + 6 from rfl, Function.iterate_add_apply]
  rw [e1, h22]
  simpa only [frameL3] using e0

theorem selLink4 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n))) :
    (Schritt (leftBlk ein aus frei))^[10] (some e) =
      some (frameL4 e ein aus frei n) := by
  have h33 := selLink3 ein aus frei n e hepc hes
  have hpc : (frameL3 e ein aus frei n).pc = 34 := rfl
  have ha : (frameL3 e ein aus frei n).zahl (frei + 3) =
      some ⟨((Nat.sqrt n : Nat) : Int), ((Nat.sqrt n : Nat) : Int), Zahl.literal ((Nat.sqrt n : Nat) : Int)⟩ := by
    have hA3t : (frameL3 e ein aus frei n).temp (frei + 3) = some (natVal (Nat.sqrt n)) := by
      show Function.update _ (frei + 4) _ (frei + 3) = _
      rw [updateMiss _ _ _ _ (addNeLinks (by decide : (4 : Nat) ≠ 3))]
      exact updateHit _ _ _
    show (((frameL3 e ein aus frei n).temp (frei + 3)).bind alsGanzzahl) = _
    rw [hA3t]
    rfl
  have hb : (frameL3 e ein aus frei n).zahl (frei + 4) =
      some ⟨((Nat.sqrt n : Nat) : Int), ((Nat.sqrt n : Nat) : Int), Zahl.literal (((Nat.sqrt n : Nat)) : Int)⟩ := by
    show (((frameL3 e ein aus frei n).temp (frei + 4)).bind alsGanzzahl) = _
    rw [show (frameL3 e ein aus frei n).temp (frei + 4) = some (natVal (Nat.sqrt n)) from updateHit _ _ _]
    rfl
  have g : (leftBlk ein aus frei)[34]? = some (.binaer .mul (frei + 3)) := by rfl
  have e0 : (Schritt (leftBlk ein aus frei))^[1] (some (frameL3 e ein aus frei n)) =
      some (frameL4 e ein aus frei n) :=
    schrittBinaer _ _ _ _ .mul _ _ hpc ha hb g
  have e1 : (Schritt (leftBlk ein aus frei))^[10] (some e) =
      (Schritt (leftBlk ein aus frei))^[1]
        ((Schritt (leftBlk ein aus frei))^[9] (some e)) := by
    rw [show (10 : Nat) = 1 + 9 from rfl, Function.iterate_add_apply]
  rw [e1, h33, e0]

theorem selLink5 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (leftBlk ein aus frei))^[13] (some e) =
      some (frameL5 e ein aus frei n) := by
  have h44 := selLink4 ein aus frei n e hepc hes
  have hpc : (frameL4 e ein aus frei n).pc = 35 := rfl
  have hq : (frameL4 e ein aus frei n).temp ein = some (natVal n) := by
    show Function.update _ (frei + 3) _ ein = _
    rw [updateMiss _ _ _ _ (ltNeAdd hein)]
    show Function.update _ (frei + 4) _ ein = _
    rw [updateMiss _ _ _ _ (ltNeAdd hein)]
    show Function.update _ (frei + 3) _ ein = _
    rw [updateMiss _ _ _ _ (ltNeAdd hein)]
    show Function.update _ (frei + 1) _ ein = _
    rw [updateMiss _ _ _ _ (ltNeAdd hein)]
    exact heq
  have g0 : (leftBlk ein aus frei)[35]? = some (.binden nameX ein) := by rfl
  have g1 : (leftBlk ein aus frei)[35 + 1]? = some (.lesen (frei + 1) 0) := by rfl
  have g2 : (leftBlk ein aus frei)[35 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 35 (frei + 1) ein _ hpc hq g0 g1 g2
  have e1 : (Schritt (leftBlk ein aus frei))^[13] (some e) =
      (Schritt (leftBlk ein aus frei))^[3]
        ((Schritt (leftBlk ein aus frei))^[10] (some e)) := by
    rw [show (13 : Nat) = 3 + 10 from rfl, Function.iterate_add_apply]
  rw [e1, h44]
  simpa only [frameL5] using e0

theorem selLink6 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (leftBlk ein aus frei))^[16] (some e) =
      some (frameL6 e ein aus frei n) := by
  have h55 := selLink5 ein aus frei n e hepc hes heq hein
  have hpc : (frameL5 e ein aus frei n).pc = 38 := rfl
  have hq : (frameL5 e ein aus frei n).temp (frei + 1) = some (natVal n) :=
    updateHit _ _ _
  have g0 : (leftBlk ein aus frei)[38]? = some (.binden nameX (frei + 1)) := by rfl
  have g1 : (leftBlk ein aus frei)[38 + 1]? = some (.lesen (frei + 5) 0) := by rfl
  have g2 : (leftBlk ein aus frei)[38 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 38 (frei + 5) (frei + 1) _ hpc hq g0 g1 g2
  have e1 : (Schritt (leftBlk ein aus frei))^[16] (some e) =
      (Schritt (leftBlk ein aus frei))^[3]
        ((Schritt (leftBlk ein aus frei))^[13] (some e)) := by
    rw [show (16 : Nat) = 3 + 13 from rfl, Function.iterate_add_apply]
  rw [e1, h55]
  simpa only [frameL6] using e0

theorem selLink7 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (leftBlk ein aus frei))^[19] (some e) =
      some (frameL7 e ein aus frei n) := by
  have h66 := selLink6 ein aus frei n e hepc hes heq hein
  have hpc : (frameL6 e ein aus frei n).pc = 41 := rfl
  have hq : (frameL6 e ein aus frei n).temp (frei + 3) = some (Ganzzahl.pack ⟨_, _, Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int))⟩) := by
    show Function.update _ (frei + 5) _ (frei + 3) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (5 : Nat) ≠ 3))]
    show Function.update _ (frei + 1) _ (frei + 3) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (1 : Nat) ≠ 3))]
    exact updateHit _ _ _
  have g0 : (leftBlk ein aus frei)[41]? = some (.binden nameX (frei + 3)) := by rfl
  have g1 : (leftBlk ein aus frei)[41 + 1]? = some (.lesen (frei + 6) 0) := by rfl
  have g2 : (leftBlk ein aus frei)[41 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 41 (frei + 6) (frei + 3) _ hpc hq g0 g1 g2
  have e1 : (Schritt (leftBlk ein aus frei))^[19] (some e) =
      (Schritt (leftBlk ein aus frei))^[3]
        ((Schritt (leftBlk ein aus frei))^[16] (some e)) := by
    rw [show (19 : Nat) = 3 + 16 from rfl, Function.iterate_add_apply]
  rw [e1, h66]
  simpa only [frameL7] using e0

theorem selLink8 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (leftBlk ein aus frei))^[20] (some e) =
      some (frameL8 e ein aus frei n) := by
  have h77 := selLink7 ein aus frei n e hepc hes heq hein
  have hpc : (frameL7 e ein aus frei n).pc = 44 := rfl
  have ha7 : (frameL7 e ein aus frei n).zahl (frei + 5) = some ⟨(n : Int), (n : Int), Zahl.literal (n : Int)⟩ := by
    have hA7t : (frameL7 e ein aus frei n).temp (frei + 5) = some (natVal n) := by
      show Function.update _ (frei + 6) _ (frei + 5) = _
      rw [updateMiss _ _ _ _ (addNeLinks (by decide : (6 : Nat) ≠ 5))]
      exact updateHit _ _ _
    show (((frameL7 e ein aus frei n).temp (frei + 5)).bind alsGanzzahl) = _
    rw [hA7t]
    rfl
  have hb7 : (frameL7 e ein aus frei n).zahl (frei + 6) = some ⟨_, _, Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int))⟩ := by
    show (((frameL7 e ein aus frei n).temp (frei + 6)).bind alsGanzzahl) = _
    rw [show (frameL7 e ein aus frei n).temp (frei + 6) = some (Ganzzahl.pack ⟨_, _, Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int))⟩) from updateHit _ _ _]
    rfl
  have g44 : (leftBlk ein aus frei)[44]? = some (.binaer .sub (frei + 5)) := by rfl
  have e0 : (Schritt (leftBlk ein aus frei))^[1] (some (frameL7 e ein aus frei n)) =
      some (frameL8 e ein aus frei n) :=
    schrittBinaer _ _ _ _ .sub _ _ hpc ha7 hb7 g44
  have e1 : (Schritt (leftBlk ein aus frei))^[20] (some e) =
      (Schritt (leftBlk ein aus frei))^[1]
        ((Schritt (leftBlk ein aus frei))^[19] (some e)) := by
    rw [show (20 : Nat) = 1 + 19 from rfl, Function.iterate_add_apply]
  rw [e1, h77, e0]

theorem selLink9 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (leftBlk ein aus frei))^[23] (some e) =
      some (frameL9 e ein aus frei n) := by
  have h88 := selLink8 ein aus frei n e hepc hes heq hein
  have hpc : (frameL8 e ein aus frei n).pc = 45 := rfl
  have hq : (frameL8 e ein aus frei n).temp (frei + 5) = some (Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩) :=
    updateHit _ _ _
  have g0 : (leftBlk ein aus frei)[45]? = some (.binden nameX (frei + 5)) := by rfl
  have g1 : (leftBlk ein aus frei)[45 + 1]? = some (.lesen (frei + 3) 0) := by rfl
  have g2 : (leftBlk ein aus frei)[45 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 45 (frei + 3) (frei + 5) _ hpc hq g0 g1 g2
  have e1 : (Schritt (leftBlk ein aus frei))^[23] (some e) =
      (Schritt (leftBlk ein aus frei))^[3]
        ((Schritt (leftBlk ein aus frei))^[20] (some e)) := by
    rw [show (23 : Nat) = 3 + 20 from rfl, Function.iterate_add_apply]
  rw [e1, h88]
  simpa only [frameL9] using e0

theorem selLink10 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (leftBlk ein aus frei))^[26] (some e) =
      some (frameL10 e ein aus frei n) := by
  have h99 := selLink9 ein aus frei n e hepc hes heq hein
  have hpc : (frameL9 e ein aus frei n).pc = 48 := rfl
  have hq : (frameL9 e ein aus frei n).temp (frei + 0) = some (natVal (Nat.sqrt n)) := by
    show Function.update _ (frei + 3) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (3 : Nat) ≠ 0))]
    show Function.update _ (frei + 5) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (5 : Nat) ≠ 0))]
    show Function.update _ (frei + 6) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (6 : Nat) ≠ 0))]
    show Function.update _ (frei + 5) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (5 : Nat) ≠ 0))]
    show Function.update _ (frei + 1) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (1 : Nat) ≠ 0))]
    show Function.update _ (frei + 3) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (3 : Nat) ≠ 0))]
    show Function.update _ (frei + 4) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (4 : Nat) ≠ 0))]
    show Function.update _ (frei + 3) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (3 : Nat) ≠ 0))]
    show Function.update _ (frei + 1) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (1 : Nat) ≠ 0))]
    exact hes
  have g0 : (leftBlk ein aus frei)[48]? = some (.binden nameX (frei + 0)) := by rfl
  have g1 : (leftBlk ein aus frei)[48 + 1]? = some (.lesen (frei + 4) 0) := by rfl
  have g2 : (leftBlk ein aus frei)[48 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 48 (frei + 4) (frei + 0) _ hpc hq g0 g1 g2
  have e1 : (Schritt (leftBlk ein aus frei))^[26] (some e) =
      (Schritt (leftBlk ein aus frei))^[3]
        ((Schritt (leftBlk ein aus frei))^[23] (some e)) := by
    rw [show (26 : Nat) = 3 + 23 from rfl, Function.iterate_add_apply]
  rw [e1, h99]
  simpa only [frameL10] using e0

theorem selLink11 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (leftBlk ein aus frei))^[27] (some e) =
      some (frameL11 e ein aus frei n) := by
  have h1010 := selLink10 ein aus frei n e hepc hes heq hein
  have hpc : (frameL10 e ein aus frei n).pc = 51 := rfl
  have ha10 : (frameL10 e ein aus frei n).zahl (frei + 3) = some ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩ := by
    have hA10t : (frameL10 e ein aus frei n).temp (frei + 3) = some (Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩) := by
      show Function.update _ (frei + 4) _ (frei + 3) = _
      rw [updateMiss _ _ _ _ (addNeLinks (by decide : (4 : Nat) ≠ 3))]
      exact updateHit _ _ _
    show (((frameL10 e ein aus frei n).temp (frei + 3)).bind alsGanzzahl) = _
    rw [hA10t]
    rfl
  have hb10 : (frameL10 e ein aus frei n).zahl (frei + 4) = some ⟨((Nat.sqrt n : Nat) : Int), ((Nat.sqrt n : Nat) : Int), Zahl.literal ((Nat.sqrt n : Nat) : Int)⟩ := by
    show (((frameL10 e ein aus frei n).temp (frei + 4)).bind alsGanzzahl) = _
    rw [show (frameL10 e ein aus frei n).temp (frei + 4) = some (natVal (Nat.sqrt n)) from updateHit _ _ _]
    rfl
  have g51 : (leftBlk ein aus frei)[51]? = some (.vergleichen .lt (frei + 3)) := by rfl
  have e0 : (Schritt (leftBlk ein aus frei))^[1] (some (frameL10 e ein aus frei n)) =
      some (frameL11 e ein aus frei n) :=
    schrittVergleichen _ _ _ _ .lt _ _ hpc ha10 hb10 g51
  have e1 : (Schritt (leftBlk ein aus frei))^[27] (some e) =
      (Schritt (leftBlk ein aus frei))^[1]
        ((Schritt (leftBlk ein aus frei))^[26] (some e)) := by
    rw [show (27 : Nat) = 1 + 26 from rfl, Function.iterate_add_apply]
  rw [e1, h1010, e0]

theorem selLink12t (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei)
    (h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n) :
    (Schritt (leftBlk ein aus frei))^[28] (some e) =
      some (frameL12t e ein aus frei n) := by
  have h1111 := selLink11 ein aus frei n e hepc hes heq hein
  have hpc : (frameL11 e ein aus frei n).pc = 52 := rfl
  have htemp : (frameL11 e ein aus frei n).temp (frei + 3) =
      some ⟨.bool, cmpBoolLeft (Nat.sqrt n) n⟩ :=
    updateHit _ _ _
  have hbool : cmpBoolLeft (Nat.sqrt n) n = true := by
    have e1 : cmpBoolLeft (Nat.sqrt n) n =
        decide (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n) := by
      simp only [cmpBoolLeft, Compare.eval, decideDlt _ _ (Nat.sqrt_le n)]
    rw [e1]
    exact decide_eq_true h
  have g52 : (leftBlk ein aus frei)[52]? = some (.springeWenn (frei + 3) true 5) := by
    rfl
  have e0 : (Schritt (leftBlk ein aus frei))^[1] (some (frameL11 e ein aus frei n)) =
      some (frameL12t e ein aus frei n) :=
    schrittSpringeWennWahr _ _ _ _ _ _ _ hpc htemp hbool g52
  have e1 : (Schritt (leftBlk ein aus frei))^[28] (some e) =
      (Schritt (leftBlk ein aus frei))^[1]
        ((Schritt (leftBlk ein aus frei))^[27] (some e)) := by
    rw [show (28 : Nat) = 1 + 27 from rfl, Function.iterate_add_apply]
  rw [e1, h1111, e0]

theorem selLink12e (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei)
    (h : ¬ (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n)) :
    (Schritt (leftBlk ein aus frei))^[28] (some e) =
      some (frameL12e e ein aus frei n) := by
  have h1111 := selLink11 ein aus frei n e hepc hes heq hein
  have hpc : (frameL11 e ein aus frei n).pc = 52 := rfl
  have htemp : (frameL11 e ein aus frei n).temp (frei + 3) =
      some ⟨.bool, cmpBoolLeft (Nat.sqrt n) n⟩ :=
    updateHit _ _ _
  have hbool : cmpBoolLeft (Nat.sqrt n) n ≠ true := by
    have e1 : cmpBoolLeft (Nat.sqrt n) n =
        decide (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n) := by
      simp only [cmpBoolLeft, Compare.eval, decideDlt _ _ (Nat.sqrt_le n)]
    have e2 : decide (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n) = false :=
      decide_eq_false h
    rw [e1, e2]
    exact Bool.false_ne_true
  have g52 : (leftBlk ein aus frei)[52]? = some (.springeWenn (frei + 3) true 5) := by
    rfl
  have e0 : (Schritt (leftBlk ein aus frei))^[1] (some (frameL11 e ein aus frei n)) =
      some (frameL12e e ein aus frei n) :=
    schrittSpringeWennFalsch _ _ _ _ _ _ _ hpc htemp hbool g52
  have e1 : (Schritt (leftBlk ein aus frei))^[28] (some e) =
      (Schritt (leftBlk ein aus frei))^[1]
        ((Schritt (leftBlk ein aus frei))^[27] (some e)) := by
    rw [show (28 : Nat) = 1 + 27 from rfl, Function.iterate_add_apply]
  rw [e1, h1111, e0]

theorem selLink13t (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei)
    (h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n) :
    (Schritt (leftBlk ein aus frei))^[31] (some e) =
      some (frameL13t e ein aus frei n) := by
  have h1212 := selLink12t ein aus frei n e hepc hes heq hein h
  have hpc : (frameL12t e ein aus frei n).pc = 57 := rfl
  have hq : (frameL12t e ein aus frei n).temp (frei + 5) = some (Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩) := by
    have h11 : (frameL12t e ein aus frei n).temp (frei + 5) =
        (frameL11 e ein aus frei n).temp (frei + 5) := rfl
    rw [h11]
    show Function.update _ (frei + 3) _ (frei + 5) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (3 : Nat) ≠ 5))]
    show Function.update _ (frei + 4) _ (frei + 5) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (4 : Nat) ≠ 5))]
    show Function.update _ (frei + 3) _ (frei + 5) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (3 : Nat) ≠ 5))]
    exact updateHit _ _ _
  have g0 : (leftBlk ein aus frei)[57]? = some (.binden nameX (frei + 5)) := by rfl
  have g1 : (leftBlk ein aus frei)[57 + 1]? = some (.lesen aus 0) := by rfl
  have g2 : (leftBlk ein aus frei)[57 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 57 aus (frei + 5) _ hpc hq g0 g1 g2
  have e1 : (Schritt (leftBlk ein aus frei))^[31] (some e) =
      (Schritt (leftBlk ein aus frei))^[3]
        ((Schritt (leftBlk ein aus frei))^[28] (some e)) := by
    rw [show (31 : Nat) = 3 + 28 from rfl, Function.iterate_add_apply]
  rw [e1, h1212]
  simpa only [frameL13t] using e0

theorem selLink13e (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei)
    (h : ¬ (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n)) :
    (Schritt (leftBlk ein aus frei))^[31] (some e) =
      some (frameL13e e ein aus frei n) := by
  have h1212 := selLink12e ein aus frei n e hepc hes heq hein h
  have hpc : (frameL12e e ein aus frei n).pc = 53 := rfl
  have hq : (frameL12e e ein aus frei n).temp (frei + 0) = some (natVal (Nat.sqrt n)) := by
    show Function.update _ (frei + 3) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (3 : Nat) ≠ 0))]
    show Function.update _ (frei + 4) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (4 : Nat) ≠ 0))]
    show Function.update _ (frei + 3) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (3 : Nat) ≠ 0))]
    show Function.update _ (frei + 5) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (5 : Nat) ≠ 0))]
    show Function.update _ (frei + 6) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (6 : Nat) ≠ 0))]
    show Function.update _ (frei + 5) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (5 : Nat) ≠ 0))]
    show Function.update _ (frei + 1) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (1 : Nat) ≠ 0))]
    show Function.update _ (frei + 3) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (3 : Nat) ≠ 0))]
    show Function.update _ (frei + 4) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (4 : Nat) ≠ 0))]
    show Function.update _ (frei + 3) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (3 : Nat) ≠ 0))]
    show Function.update _ (frei + 1) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (1 : Nat) ≠ 0))]
    exact hes
  have g0 : (leftBlk ein aus frei)[53]? = some (.binden nameX (frei + 0)) := by rfl
  have g1 : (leftBlk ein aus frei)[53 + 1]? = some (.lesen aus 0) := by rfl
  have g2 : (leftBlk ein aus frei)[53 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 53 aus (frei + 0) _ hpc hq g0 g1 g2
  have e1 : (Schritt (leftBlk ein aus frei))^[31] (some e) =
      (Schritt (leftBlk ein aus frei))^[3]
        ((Schritt (leftBlk ein aus frei))^[28] (some e)) := by
    rw [show (31 : Nat) = 3 + 28 from rfl, Function.iterate_add_apply]
  rw [e1, h1212]
  simpa only [frameL13e] using e0

theorem selLink14e (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei)
    (h : ¬ (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n)) :
    (Schritt (leftBlk ein aus frei))^[32] (some e) =
      some (frameL14e e ein aus frei n) := by
  have h1313 := selLink13e ein aus frei n e hepc hes heq hein h
  have hpc : (frameL13e e ein aus frei n).pc = 56 := rfl
  have g56 : (leftBlk ein aus frei)[56]? = some (.springe 4) := by rfl
  have e0 : (Schritt (leftBlk ein aus frei))^[1] (some (frameL13e e ein aus frei n)) =
      some (frameL14e e ein aus frei n) :=
    schrittSpringe _ _ _ _ hpc g56
  have e1 : (Schritt (leftBlk ein aus frei))^[32] (some e) =
      (Schritt (leftBlk ein aus frei))^[1]
        ((Schritt (leftBlk ein aus frei))^[31] (some e)) := by
    rw [show (32 : Nat) = 1 + 31 from rfl, Function.iterate_add_apply]
  rw [e1, h1313, e0]

/-- Preservation through the selection for the then-branch. -/
theorem presSelT (ein aus frei n : Nat) (e : Rahmen) (t : Nat)
    (ht : t < frei) (hne : t ≠ aus) :
    (frameL13t e ein aus frei n).temp t = e.temp t := by
  have e1 : (frameL13t e ein aus frei n).temp t = (frameL12t e ein aus frei n).temp t := by
    show Function.update _ aus _ t = _
    rw [updateMiss _ _ _ _ hne]
  have e2 : (frameL12t e ein aus frei n).temp t = (frameL11 e ein aus frei n).temp t := rfl
  have e3 : (frameL11 e ein aus frei n).temp t = (frameL10 e ein aus frei n).temp t := by
    show Function.update _ (frei + 3) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e4 : (frameL10 e ein aus frei n).temp t = (frameL9 e ein aus frei n).temp t := by
    show Function.update _ (frei + 4) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e5 : (frameL9 e ein aus frei n).temp t = (frameL8 e ein aus frei n).temp t := by
    show Function.update _ (frei + 3) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e6 : (frameL8 e ein aus frei n).temp t = (frameL7 e ein aus frei n).temp t := by
    show Function.update _ (frei + 5) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e7 : (frameL7 e ein aus frei n).temp t = (frameL6 e ein aus frei n).temp t := by
    show Function.update _ (frei + 6) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e8 : (frameL6 e ein aus frei n).temp t = (frameL5 e ein aus frei n).temp t := by
    show Function.update _ (frei + 5) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e9 : (frameL5 e ein aus frei n).temp t = (frameL4 e ein aus frei n).temp t := by
    show Function.update _ (frei + 1) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e10 : (frameL4 e ein aus frei n).temp t = (frameL3 e ein aus frei n).temp t := by
    show Function.update _ (frei + 3) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e11 : (frameL3 e ein aus frei n).temp t = (frameL2 e ein aus frei n).temp t := by
    show Function.update _ (frei + 4) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e12 : (frameL2 e ein aus frei n).temp t = (frameL1 e ein aus frei n).temp t := by
    show Function.update _ (frei + 3) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e13 : (frameL1 e ein aus frei n).temp t = e.temp t := by
    show Function.update _ (frei + 1) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13]

/-- Preservation through the selection for the else-branch. -/
theorem presSelE (ein aus frei n : Nat) (e : Rahmen) (t : Nat)
    (ht : t < frei) (hne : t ≠ aus) :
    (frameL14e e ein aus frei n).temp t = e.temp t := by
  have e1 : (frameL14e e ein aus frei n).temp t = (frameL13e e ein aus frei n).temp t := rfl
  have e2 : (frameL13e e ein aus frei n).temp t = (frameL12e e ein aus frei n).temp t := by
    show Function.update _ aus _ t = _
    rw [updateMiss _ _ _ _ hne]
  have e3 : (frameL12e e ein aus frei n).temp t = (frameL11 e ein aus frei n).temp t := rfl
  have e4 : (frameL11 e ein aus frei n).temp t = (frameL10 e ein aus frei n).temp t := by
    show Function.update _ (frei + 3) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e5 : (frameL10 e ein aus frei n).temp t = (frameL9 e ein aus frei n).temp t := by
    show Function.update _ (frei + 4) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e6 : (frameL9 e ein aus frei n).temp t = (frameL8 e ein aus frei n).temp t := by
    show Function.update _ (frei + 3) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e7 : (frameL8 e ein aus frei n).temp t = (frameL7 e ein aus frei n).temp t := by
    show Function.update _ (frei + 5) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e8 : (frameL7 e ein aus frei n).temp t = (frameL6 e ein aus frei n).temp t := by
    show Function.update _ (frei + 6) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e9 : (frameL6 e ein aus frei n).temp t = (frameL5 e ein aus frei n).temp t := by
    show Function.update _ (frei + 5) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e10 : (frameL5 e ein aus frei n).temp t = (frameL4 e ein aus frei n).temp t := by
    show Function.update _ (frei + 1) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e11 : (frameL4 e ein aus frei n).temp t = (frameL3 e ein aus frei n).temp t := by
    show Function.update _ (frei + 3) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e12 : (frameL3 e ein aus frei n).temp t = (frameL2 e ein aus frei n).temp t := by
    show Function.update _ (frei + 4) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e13 : (frameL2 e ein aus frei n).temp t = (frameL1 e ein aus frei n).temp t := by
    show Function.update _ (frei + 3) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e14 : (frameL1 e ein aus frei n).temp t = e.temp t := by
    show Function.update _ (frei + 1) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]

/-- Then-branch arrival: loop exit composed with the difference selection. -/
theorem leftArrivalThen (ein aus frei n : Nat) (r : Rahmen)
    (hpc : r.pc = 0) (hr : r.temp ein = some (natVal n))
    (hein : ein < frei) (haus : aus < frei) (hunters : ein ≠ aus)
    (hcond : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n) :
    ∃ k r', (Schritt (leftBlk ein aus frei))^[k] (some r) = some r' ∧
      r'.pc = 60 ∧ r'.temp aus = some (natVal ((Nat.unpair n).1)) ∧
      (∀ t, t < frei → t ≠ aus → r'.temp t = r.temp t) ∧
      r'.lokale = r.lokale ∧ r'.rueckgabe = r.rueckgabe ∧ r'.stopp = r.stopp := by
  obtain ⟨kL, rE, hrunL, hpcL, hsqrtL, hpresL, hlokL, hrueckL, hstoppL, hkL⟩ :=
    sqrtSchleife ein frei n r (leftSel ein aus frei) hpc hr hein
  have hrunL' : (Schritt (leftBlk ein aus frei))^[kL] (some r) = some rE := hrunL
  have heqE : rE.temp ein = some (natVal n) := by
    rw [hpresL _ hein]
    exact hr
  have hsqrt : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hrunT := selLink13t ein aus frei n rE hpcL hsqrtL heqE hein hcond
  have hausT : (frameL13t rE ein aus frei n).temp aus =
      some (natVal ((Nat.unpair n).1)) := by
    have hcast := packSubCast (Nat.sqrt n) n hsqrt
    have hun := hunLeftT n hcond
    have hget : (frameL13t rE ein aus frei n).temp aus =
        some (Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int))
          (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int))
            (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩) :=
      updateHit _ _ _
    rw [hget, hcast, hun]
  have hrun : (Schritt (leftBlk ein aus frei))^[kL + 31] (some r) =
      some (frameL13t rE ein aus frei n) := by
    rw [show kL + 31 = 31 + kL from Nat.add_comm kL 31, Function.iterate_add_apply, hrunL']
    exact hrunT
  have hpc' : (frameL13t rE ein aus frei n).pc = 60 := by
    show (frameL13t rE ein aus frei n).pc = (leftBlk ein aus frei).length
    rw [leftBlkLaenge]
    rfl
  refine ⟨kL + 31, _, hrun, hpc', hausT, ?_, ?_, ?_, ?_⟩
  · intro t ht hne
    rw [presSelT ein aus frei n rE t ht hne, hpresL t ht]
  · exact hlokL
  · exact hrueckL
  · exact hstoppL

/-- Else-branch arrival: loop exit composed with the root selection. -/
theorem leftArrivalElse (ein aus frei n : Nat) (r : Rahmen)
    (hpc : r.pc = 0) (hr : r.temp ein = some (natVal n))
    (hein : ein < frei) (haus : aus < frei) (hunters : ein ≠ aus)
    (hcond : ¬ (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n)) :
    ∃ k r', (Schritt (leftBlk ein aus frei))^[k] (some r) = some r' ∧
      r'.pc = 60 ∧ r'.temp aus = some (natVal ((Nat.unpair n).1)) ∧
      (∀ t, t < frei → t ≠ aus → r'.temp t = r.temp t) ∧
      r'.lokale = r.lokale ∧ r'.rueckgabe = r.rueckgabe ∧ r'.stopp = r.stopp := by
  obtain ⟨kL, rE, hrunL, hpcL, hsqrtL, hpresL, hlokL, hrueckL, hstoppL, hkL⟩ :=
    sqrtSchleife ein frei n r (leftSel ein aus frei) hpc hr hein
  have hrunL' : (Schritt (leftBlk ein aus frei))^[kL] (some r) = some rE := hrunL
  have heqE : rE.temp ein = some (natVal n) := by
    rw [hpresL _ hein]
    exact hr
  have hrunE := selLink14e ein aus frei n rE hpcL hsqrtL heqE hein hcond
  have hausE : (frameL14e rE ein aus frei n).temp aus =
      some (natVal ((Nat.unpair n).1)) := by
    have hun := hunLeftE n hcond
    have hget : (frameL14e rE ein aus frei n).temp aus = some (natVal (Nat.sqrt n)) :=
      updateHit _ _ _
    rw [hget, hun]
  have hrun : (Schritt (leftBlk ein aus frei))^[kL + 32] (some r) =
      some (frameL14e rE ein aus frei n) := by
    rw [show kL + 32 = 32 + kL from Nat.add_comm kL 32, Function.iterate_add_apply, hrunL']
    exact hrunE
  have hpc' : (frameL14e rE ein aus frei n).pc = 60 := by
    show (frameL14e rE ein aus frei n).pc = (leftBlk ein aus frei).length
    rw [leftBlkLaenge]
    rfl
  refine ⟨kL + 32, _, hrun, hpc', hausE, ?_, ?_, ?_, ?_⟩
  · intro t ht hne
    rw [presSelE ein aus frei n rE t ht hne, hpresL t ht]
  · exact hlokL
  · exact hrueckL
  · exact hstoppL

/-- The left-projection block is correct in the block-lemma sense. -/
theorem blockLeft (ein aus frei : Nat) (hein : ein < frei) (haus : aus < frei)
    (hunters : ein ≠ aus) :
    BlockKorrekt (leftBlk ein aus frei) .left ein aus frei := by
  unfold BlockKorrekt
  refine ⟨hein, haus, hunters, ?_, ?_⟩
  · intro n r hpc hr
    by_cases hcond : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n
    · intro a ha
      have ha0 : a = (Nat.unpair n).1 := by
        have h0 : Part.some ((Nat.unpair n).1) = Part.some a := by
          change Part.some ((Nat.unpair n).1) = Part.some a at ha
          exact ha
        exact (Part.some_injective h0).symm
      subst ha0
      obtain ⟨k, r', hrun, hpc', haus', hpres, hlok, hrueck, hstopp⟩ :=
        leftArrivalThen ein aus frei n r hpc hr hein haus hunters hcond
      exact ⟨k, r', hrun, hpc', haus', hpres, hlok, hrueck, hstopp⟩
    · intro a ha
      have ha0 : a = (Nat.unpair n).1 := by
        have h0 : Part.some ((Nat.unpair n).1) = Part.some a := by
          change Part.some ((Nat.unpair n).1) = Part.some a at ha
          exact ha
        exact (Part.some_injective h0).symm
      subst ha0
      obtain ⟨k, r', hrun, hpc', haus', hpres, hlok, hrueck, hstopp⟩ :=
        leftArrivalElse ein aus frei n r hpc hr hein haus hunters hcond
      exact ⟨k, r', hrun, hpc', haus', hpres, hlok, hrueck, hstopp⟩
  · intro k r' hk hpc'
    by_cases hcond : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n
    · obtain ⟨kT, rT, hrunT, hpcT, hausT, hpresT, hlokT, hrueckT, hstoppT⟩ :=
        leftArrivalThen ein aus frei n r hpc hr hein haus hunters hcond
      rcases lt_trichotomy k kT with h | h | h
      · exfalso
        exact laufStirbtNach _ _ _ _ _ _ hk hpc' hrunT h
      · subst h
        have heq : r' = rT := Option.some_inj (hk.symm.trans hrunT)
        subst heq
        have heval : Nat.Partrec.Code.eval .left n = Part.some ((Nat.unpair n).1) := rfl
        exact ⟨(Nat.unpair n).1, heval, hausT, hpresT, hlokT, hrueckT, hstoppT⟩
      · exfalso
        exact laufStirbtNach _ _ kT k _ _ hrunT hpcT hk h
    · obtain ⟨kE, rE, hrunE, hpcE, hausE, hpresE, hlokE, hrueckE, hstoppE⟩ :=
        leftArrivalElse ein aus frei n r hpc hr hein haus hunters hcond
      rcases lt_trichotomy k kE with h | h | h
      · exfalso
        exact laufStirbtNach _ _ _ _ _ _ hk hpc' hrunE h
      · subst h
        have heq : r' = rE := Option.some_inj (hk.symm.trans hrunE)
        subst heq
        have heval : Nat.Partrec.Code.eval .left n = Part.some ((Nat.unpair n).1) := rfl
        exact ⟨(Nat.unpair n).1, heval, hausE, hpresE, hlokE, hrueckE, hstoppE⟩
      · exfalso
        exact laufStirbtNach _ _ kE k _ _ hrunE hpcE hk h

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
