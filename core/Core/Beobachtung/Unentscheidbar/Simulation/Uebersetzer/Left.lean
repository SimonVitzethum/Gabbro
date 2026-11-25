module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Sqrt

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Selection after the search: square the root, subtract from the input
    for the difference `d`, write `d` to the output speculatively, then
    overwrite it with the root unless `d` is smaller. Select offsets follow
    the search exit at 25. Only the scratch slots `frei + 0/1/2` are used. -/
def leftSel (ein aus frei : Nat) : List Befehl :=
  [.binden nameX (frei + 0), .lesen (frei + 1) 0, .blockEnde 1, .binden nameX (frei + 1), .lesen (frei + 2) 0, .blockEnde 1, .binaer .mul (frei + 1), .binden nameX (frei + 1), .lesen (frei + 2) 0, .blockEnde 1, .binden nameX ein, .lesen (frei + 1) 0, .blockEnde 1, .binaer .sub (frei + 1), .binden nameX (frei + 1), .lesen aus 0, .blockEnde 1, .binden nameX (frei + 0), .lesen (frei + 2) 0, .blockEnde 1, .vergleichen .lt (frei + 1), .springeWenn (frei + 1) true 4, .binden nameX (frei + 0), .lesen aus 0, .blockEnde 1]

/-- The relocatable block for `left`: search prefix followed by selection. -/
def leftBlk (ein aus frei : Nat) : List Befehl :=
  sqrtPrefix ein frei ++ leftSel ein aus frei

theorem leftSelLaenge (ein aus frei : Nat) : (leftSel ein aus frei).length = 25 := by
  rfl

theorem leftBlkLaenge (ein aus frei : Nat) : (leftBlk ein aus frei).length = 50 := by
  rfl

/-- Selection states from the search exit, with `s` the integer root. -/
def frameL1 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { e with pc := 25 + 3, temp := Function.update e.temp (frei + 1) (some (natVal (Nat.sqrt n))) }
def frameL2 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL1 e ein aus frei n with pc := 25 + 6, temp := Function.update (frameL1 e ein aus frei n).temp (frei + 2) (some (natVal (Nat.sqrt n))) }
def frameL3 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL2 e ein aus frei n with pc := 25 + 7, temp := Function.update (frameL2 e ein aus frei n).temp (frei + 1) (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int))⟩)) }
def frameL4 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL3 e ein aus frei n with pc := 25 + 10, temp := Function.update (frameL3 e ein aus frei n).temp (frei + 2) (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int))⟩)) }
def frameL5 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL4 e ein aus frei n with pc := 25 + 13, temp := Function.update (frameL4 e ein aus frei n).temp (frei + 1) (some (natVal n)) }
def frameL6 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL5 e ein aus frei n with pc := 25 + 14, temp := Function.update (frameL5 e ein aus frei n).temp (frei + 1) (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩)) }
def frameL7 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL6 e ein aus frei n with pc := 25 + 17, temp := Function.update (frameL6 e ein aus frei n).temp aus (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩)) }
def frameL8 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL7 e ein aus frei n with pc := 25 + 20, temp := Function.update (frameL7 e ein aus frei n).temp (frei + 2) (some (natVal (Nat.sqrt n))) }
def frameL9 (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL8 e ein aus frei n with pc := 25 + 21, temp := Function.update (frameL8 e ein aus frei n).temp (frei + 1) (some ⟨.bool, cmpBoolLeft (Nat.sqrt n) n⟩) }

/-- The difference `n - s * s` as a machine integer comparison. -/
def cmpBoolLeft (s n : Nat) : Bool := Compare.eval .lt ((n : Int) - (s : Int) * (s : Int)) (s : Int)
def frameL10t (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL9 e ein aus frei n with pc := 25 + 25 }
def frameL10e (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL9 e ein aus frei n with pc := 25 + 22 }
def frameL11e (e : Rahmen) (ein aus frei n : Nat) : Rahmen := { frameL10e e ein aus frei n with pc := 25 + 25, temp := Function.update (frameL10e e ein aus frei n).temp aus (some (natVal (Nat.sqrt n))) }

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
  have g1 : (leftBlk ein aus frei)[28 + 1]? = some (.lesen (frei + 2) 0) := by rfl
  have g2 : (leftBlk ein aus frei)[28 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 28 (frei + 2) (frei + 1) _ hpc hq g0 g1 g2
  rw [show (6 : Nat) = 3 + 3 from rfl, Function.iterate_add_apply, h11]
  simpa only [frameL2] using e0

theorem selLink3 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n))) :
    (Schritt (leftBlk ein aus frei))^[7] (some e) =
      some (frameL3 e ein aus frei n) := by
  have h22 := selLink2 ein aus frei n e hepc hes
  have hpc : (frameL2 e ein aus frei n).pc = 31 := rfl
  have ha : (frameL2 e ein aus frei n).zahl (frei + 1) =
      some ⟨((Nat.sqrt n : Nat) : Int), ((Nat.sqrt n : Nat) : Int), Zahl.literal ((Nat.sqrt n : Nat) : Int)⟩ := by
    have hA : (frameL2 e ein aus frei n).temp (frei + 1) = some (natVal (Nat.sqrt n)) := by
      show Function.update _ (frei + 2) _ (frei + 1) = _
      rw [updateMiss _ _ _ _ (addNeLinks (by decide : (1 : Nat) ≠ 2))]
      exact updateHit _ _ _
    exact zahlOfNat _ _ _ hA
  have hb : (frameL2 e ein aus frei n).zahl (frei + 2) =
      some ⟨((Nat.sqrt n : Nat) : Int), ((Nat.sqrt n : Nat) : Int), Zahl.literal ((Nat.sqrt n : Nat) : Int)⟩ :=
    zahlOfNat _ _ _ (updateHit _ _ _)
  have g : (leftBlk ein aus frei)[31]? = some (.binaer .mul (frei + 1)) := by rfl
  have e0 : (Schritt (leftBlk ein aus frei))^[1] (some (frameL2 e ein aus frei n)) =
      some (frameL3 e ein aus frei n) :=
    schrittBinaer _ _ _ _ .mul _ _ hpc ha hb g
  rw [show (7 : Nat) = 1 + 6 from rfl, Function.iterate_add_apply, h22]
  exact e0

theorem selLink4 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n))) :
    (Schritt (leftBlk ein aus frei))^[10] (some e) =
      some (frameL4 e ein aus frei n) := by
  have h33 := selLink3 ein aus frei n e hepc hes
  have hpc : (frameL3 e ein aus frei n).pc = 32 := rfl
  have hq : (frameL3 e ein aus frei n).temp (frei + 1) = some (Ganzzahl.pack ⟨_, _, Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int))⟩) :=
    updateHit _ _ _
  have g0 : (leftBlk ein aus frei)[32]? = some (.binden nameX (frei + 1)) := by rfl
  have g1 : (leftBlk ein aus frei)[32 + 1]? = some (.lesen (frei + 2) 0) := by rfl
  have g2 : (leftBlk ein aus frei)[32 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 32 (frei + 2) (frei + 1) _ hpc hq g0 g1 g2
  rw [show (10 : Nat) = 3 + 7 from rfl, Function.iterate_add_apply, h33]
  simpa only [frameL4] using e0

theorem selLink5 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (leftBlk ein aus frei))^[13] (some e) =
      some (frameL5 e ein aus frei n) := by
  have h44 := selLink4 ein aus frei n e hepc hes
  have hpc : (frameL4 e ein aus frei n).pc = 35 := rfl
  have hq : (frameL4 e ein aus frei n).temp ein = some (natVal n) := by
    show Function.update _ (frei + 2) _ ein = _
    rw [updateMiss _ _ _ _ (ltNeAdd hein)]
    show Function.update _ (frei + 1) _ ein = _
    rw [updateMiss _ _ _ _ (ltNeAdd hein)]
    show Function.update _ (frei + 2) _ ein = _
    rw [updateMiss _ _ _ _ (ltNeAdd hein)]
    show Function.update _ (frei + 1) _ ein = _
    rw [updateMiss _ _ _ _ (ltNeAdd hein)]
    exact heq
  have g0 : (leftBlk ein aus frei)[35]? = some (.binden nameX ein) := by rfl
  have g1 : (leftBlk ein aus frei)[35 + 1]? = some (.lesen (frei + 1) 0) := by rfl
  have g2 : (leftBlk ein aus frei)[35 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 35 (frei + 1) ein _ hpc hq g0 g1 g2
  rw [show (13 : Nat) = 3 + 10 from rfl, Function.iterate_add_apply, h44]
  simpa only [frameL5] using e0

theorem selLink6 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (leftBlk ein aus frei))^[14] (some e) =
      some (frameL6 e ein aus frei n) := by
  have h55 := selLink5 ein aus frei n e hepc hes heq hein
  have hpc : (frameL5 e ein aus frei n).pc = 38 := rfl
  have ha : (frameL5 e ein aus frei n).zahl (frei + 1) = some ⟨(n : Int), (n : Int), Zahl.literal (n : Int)⟩ := by
    have hA : (frameL5 e ein aus frei n).temp (frei + 1) = some (natVal n) := updateHit _ _ _
    exact zahlOfNat _ _ _ hA
  have hb : (frameL5 e ein aus frei n).zahl (frei + 2) = some ⟨_, _, Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int))⟩ := by
    have hA : (frameL5 e ein aus frei n).temp (frei + 2) = some (Ganzzahl.pack ⟨_, _, Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int))⟩) := by
      show Function.update _ (frei + 1) _ (frei + 2) = _
      rw [updateMiss _ _ _ _ (addNeLinks (by decide : (2 : Nat) ≠ 1))]
      exact updateHit _ _ _
    show (((frameL5 e ein aus frei n).temp (frei + 2)).bind alsGanzzahl) = some ⟨_, _, Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int))⟩)
    rw [hA]
    rfl
  have g : (leftBlk ein aus frei)[38]? = some (.binaer .sub (frei + 1)) := by rfl
  have e0 : (Schritt (leftBlk ein aus frei))^[1] (some (frameL5 e ein aus frei n)) =
      some (frameL6 e ein aus frei n) :=
    schrittBinaer _ _ _ _ .sub _ _ hpc ha hb g
  rw [show (14 : Nat) = 1 + 13 from rfl, Function.iterate_add_apply, h55]
  exact e0

theorem selLink7 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (leftBlk ein aus frei))^[17] (some e) =
      some (frameL7 e ein aus frei n) := by
  have h66 := selLink6 ein aus frei n e hepc hes heq hein
  have hpc : (frameL6 e ein aus frei n).pc = 39 := rfl
  have hq : (frameL6 e ein aus frei n).temp (frei + 1) = some (Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩) :=
    updateHit _ _ _
  have g0 : (leftBlk ein aus frei)[39]? = some (.binden nameX (frei + 1)) := by rfl
  have g1 : (leftBlk ein aus frei)[39 + 1]? = some (.lesen aus 0) := by rfl
  have g2 : (leftBlk ein aus frei)[39 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 39 aus (frei + 1) _ hpc hq g0 g1 g2
  rw [show (17 : Nat) = 3 + 14 from rfl, Function.iterate_add_apply, h66]
  simpa only [frameL7] using e0

theorem selLink8 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) (haus : aus < frei) :
    (Schritt (leftBlk ein aus frei))^[20] (some e) =
      some (frameL8 e ein aus frei n) := by
  have h77 := selLink7 ein aus frei n e hepc hes heq hein
  have hpc : (frameL7 e ein aus frei n).pc = 42 := rfl
  have hne0 : (frei + 0) ≠ aus := Ne.symm (Nat.ne_of_lt (by simpa only [Nat.add_zero] using haus))
  have hq : (frameL7 e ein aus frei n).temp (frei + 0) = some (natVal (Nat.sqrt n)) := by
    show Function.update _ aus _ (frei + 0) = _
    rw [updateMiss _ _ _ _ hne0]
    show Function.update _ (frei + 1) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
    show Function.update _ (frei + 1) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
    show Function.update _ (frei + 2) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 2))]
    show Function.update _ (frei + 1) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
    show Function.update _ (frei + 2) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 2))]
    show Function.update _ (frei + 1) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
    exact hes
  have g0 : (leftBlk ein aus frei)[42]? = some (.binden nameX (frei + 0)) := by rfl
  have g1 : (leftBlk ein aus frei)[42 + 1]? = some (.lesen (frei + 2) 0) := by rfl
  have g2 : (leftBlk ein aus frei)[42 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 42 (frei + 2) (frei + 0) _ hpc hq g0 g1 g2
  rw [show (20 : Nat) = 3 + 17 from rfl, Function.iterate_add_apply, h77]
  simpa only [frameL8] using e0

theorem selLink9 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) (haus : aus < frei) :
    (Schritt (leftBlk ein aus frei))^[21] (some e) =
      some (frameL9 e ein aus frei n) := by
  have h88 := selLink8 ein aus frei n e hepc hes heq hein haus
  have hpc : (frameL8 e ein aus frei n).pc = 45 := rfl
  have ha : (frameL8 e ein aus frei n).zahl (frei + 1) = some ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩ := by
    have hA : (frameL8 e ein aus frei n).temp (frei + 1) = some (Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩) := by
      show Function.update _ (frei + 2) _ (frei + 1) = _
      rw [updateMiss _ _ _ _ (addNeLinks (by decide : (1 : Nat) ≠ 2))]
      show Function.update _ aus _ (frei + 1) = _
      rw [updateMiss _ _ _ _ (scratchNeAus (Nat.le_add_right frei 1) haus)]
      exact updateHit _ _ _
    show (((frameL8 e ein aus frei n).temp (frei + 1)).bind alsGanzzahl) = some ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩)
    rw [hA]
    rfl
  have hb : (frameL8 e ein aus frei n).zahl (frei + 2) = some ⟨((Nat.sqrt n : Nat) : Int), ((Nat.sqrt n : Nat) : Int), Zahl.literal ((Nat.sqrt n : Nat) : Int)⟩ :=
    zahlOfNat _ _ _ (updateHit _ _ _)
  have g : (leftBlk ein aus frei)[45]? = some (.vergleichen .lt (frei + 1)) := by rfl
  have e0 : (Schritt (leftBlk ein aus frei))^[1] (some (frameL8 e ein aus frei n)) =
      some (frameL9 e ein aus frei n) :=
    schrittVergleichen _ _ _ _ .lt _ _ hpc ha hb g
  rw [show (21 : Nat) = 1 + 20 from rfl, Function.iterate_add_apply, h88]
  exact e0

theorem selJumpT (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) (haus : aus < frei)
    (h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n) :
    (Schritt (leftBlk ein aus frei))^[22] (some e) =
      some (frameL10t e ein aus frei n) := by
  have hpre := selLink9 ein aus frei n e hepc hes heq hein haus
  have hpc : (frameL9 e ein aus frei n).pc = 46 := rfl
  have htemp : (frameL9 e ein aus frei n).temp (frei + 1) =
      some ⟨.bool, cmpBoolLeft (Nat.sqrt n) n⟩ :=
    updateHit _ _ _
  have hbool : cmpBoolLeft (Nat.sqrt n) n = true := by
    have e1 : cmpBoolLeft (Nat.sqrt n) n =
        decide (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n) := by
      simp only [cmpBoolLeft, Compare.eval, decideDlt _ _ (Nat.sqrt_le n)]
    rw [e1]
    exact decide_eq_true h
  have g : (leftBlk ein aus frei)[46]? = some (.springeWenn (frei + 1) true 4) := by rfl
  have e0 : (Schritt (leftBlk ein aus frei))^[1] (some (frameL9 e ein aus frei n)) =
      some (frameL10t e ein aus frei n) :=
    schrittSpringeWennWahr _ _ _ _ _ _ _ hpc htemp hbool g
  rw [show (22 : Nat) = 1 + 21 from rfl, Function.iterate_add_apply, hpre]
  exact e0

theorem selJumpE (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) (haus : aus < frei)
    (h : ¬ (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n)) :
    (Schritt (leftBlk ein aus frei))^[22] (some e) =
      some (frameL10e e ein aus frei n) := by
  have hpre := selLink9 ein aus frei n e hepc hes heq hein haus
  have hpc : (frameL9 e ein aus frei n).pc = 46 := rfl
  have htemp : (frameL9 e ein aus frei n).temp (frei + 1) =
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
  have g : (leftBlk ein aus frei)[46]? = some (.springeWenn (frei + 1) true 4) := by rfl
  have e0 : (Schritt (leftBlk ein aus frei))^[1] (some (frameL9 e ein aus frei n)) =
      some (frameL10e e ein aus frei n) :=
    schrittSpringeWennFalsch _ _ _ _ _ _ _ hpc htemp hbool g
  rw [show (22 : Nat) = 1 + 21 from rfl, Function.iterate_add_apply, hpre]
  exact e0

theorem selElseRun (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) (haus : aus < frei)
    (h : ¬ (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n)) :
    (Schritt (leftBlk ein aus frei))^[25] (some e) =
      some (frameL11e e ein aus frei n) := by
  have hpre := selJumpE ein aus frei n e hepc hes heq hein haus h
  have hpc : (frameL10e e ein aus frei n).pc = 47 := rfl
  have g0 : (leftBlk ein aus frei)[47]? = some (.binden nameX (frei + 0)) := by rfl
  have g1 : (leftBlk ein aus frei)[47 + 1]? = some (.lesen aus 0) := by rfl
  have g2 : (leftBlk ein aus frei)[47 + 2]? = some (.blockEnde 1) := by rfl
  have hq : (frameL10e e ein aus frei n).temp (frei + 0) = some (natVal (Nat.sqrt n)) := by
    have h01 : (frameL10e e ein aus frei n).temp (frei + 0) =
        (frameL9 e ein aus frei n).temp (frei + 0) := rfl
    rw [h01]
    have hne0 : (frei + 0) ≠ aus := Ne.symm (Nat.ne_of_lt (by simpa only [Nat.add_zero] using haus))
    show Function.update _ (frei + 1) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
    show Function.update _ (frei + 2) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 2))]
    show Function.update _ aus _ (frei + 0) = _
    rw [updateMiss _ _ _ _ hne0]
    show Function.update _ (frei + 1) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
    show Function.update _ (frei + 1) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
    show Function.update _ (frei + 2) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 2))]
    show Function.update _ (frei + 1) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
    show Function.update _ (frei + 2) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 2))]
    show Function.update _ (frei + 1) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
    exact hes
  have e0 := laufKopie _ _ 47 aus (frei + 0) _ hpc hq g0 g1 g2
  rw [show (25 : Nat) = 3 + 22 from rfl, Function.iterate_add_apply, hpre]
  simpa only [frameL11e] using e0

/-- Preservation through the shared selection prefix. -/
theorem presSelPrefix (ein aus frei n : Nat) (e : Rahmen) (t : Nat)
    (ht : t < frei) (hne : t ≠ aus) :
    (frameL9 e ein aus frei n).temp t = e.temp t := by
  have e1 : (frameL9 e ein aus frei n).temp t = (frameL8 e ein aus frei n).temp t := by
    show Function.update _ (frei + 1) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e2 : (frameL8 e ein aus frei n).temp t = (frameL7 e ein aus frei n).temp t := by
    show Function.update _ (frei + 2) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e3 : (frameL7 e ein aus frei n).temp t = (frameL6 e ein aus frei n).temp t := by
    show Function.update _ aus _ t = _
    rw [updateMiss _ _ _ _ hne]
  have e4 : (frameL6 e ein aus frei n).temp t = (frameL5 e ein aus frei n).temp t := by
    show Function.update _ (frei + 1) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e5 : (frameL5 e ein aus frei n).temp t = (frameL4 e ein aus frei n).temp t := by
    show Function.update _ (frei + 1) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e6 : (frameL4 e ein aus frei n).temp t = (frameL3 e ein aus frei n).temp t := by
    show Function.update _ (frei + 2) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e7 : (frameL3 e ein aus frei n).temp t = (frameL2 e ein aus frei n).temp t := by
    show Function.update _ (frei + 1) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e8 : (frameL2 e ein aus frei n).temp t = (frameL1 e ein aus frei n).temp t := by
    show Function.update _ (frei + 2) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  have e9 : (frameL1 e ein aus frei n).temp t = e.temp t := by
    show Function.update _ (frei + 1) _ t = _
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9]

/-- Preservation through the selection for the then-branch. -/
theorem presSelT (ein aus frei n : Nat) (e : Rahmen) (t : Nat)
    (ht : t < frei) (hne : t ≠ aus) :
    (frameL10t e ein aus frei n).temp t = e.temp t := by
  have e1 : (frameL10t e ein aus frei n).temp t = (frameL9 e ein aus frei n).temp t := rfl
  rw [e1, presSelPrefix ein aus frei n e t ht hne]

/-- Preservation through the selection for the else-branch. -/
theorem presSelE (ein aus frei n : Nat) (e : Rahmen) (t : Nat)
    (ht : t < frei) (hne : t ≠ aus) :
    (frameL11e e ein aus frei n).temp t = e.temp t := by
  have e1 : (frameL11e e ein aus frei n).temp t = (frameL10e e ein aus frei n).temp t := by
    show Function.update _ aus _ t = _
    rw [updateMiss _ _ _ _ hne]
  have e2 : (frameL10e e ein aus frei n).temp t = (frameL9 e ein aus frei n).temp t := rfl
  rw [e1, e2, presSelPrefix ein aus frei n e t ht hne]

/-- Then-branch arrival: loop exit composed with the difference selection. -/
theorem leftArrivalThen (ein aus frei n : Nat) (r : Rahmen)
    (hpc : r.pc = 0) (hr : r.temp ein = some (natVal n))
    (hein : ein < frei) (haus : aus < frei) (hunters : ein ≠ aus)
    (hcond : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n) :
    ∃ k r', (Schritt (leftBlk ein aus frei))^[k] (some r) = some r' ∧
      r'.pc = 50 ∧ r'.temp aus = some (natVal ((Nat.unpair n).1)) ∧
      (∀ t, t < frei → t ≠ aus → r'.temp t = r.temp t) ∧
      r'.lokale = r.lokale ∧ r'.rueckgabe = r.rueckgabe ∧ r'.stopp = r.stopp := by
  obtain ⟨kL, rE, hrunL, hpcL, hsqrtL, hpresL, hlokL, hrueckL, hstoppL, hkL⟩ :=
    sqrtSchleife ein frei n r (leftSel ein aus frei) hpc hr hein
  have hrunL' : (Schritt (leftBlk ein aus frei))^[kL] (some r) = some rE := hrunL
  have heqE : rE.temp ein = some (natVal n) := by
    rw [hpresL _ hein]
    exact hr
  have hsqrt : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hrunT := selJumpT ein aus frei n rE hpcL hsqrtL heqE hein haus hcond
  have hausT : (frameL10t rE ein aus frei n).temp aus =
      some (natVal ((Nat.unpair n).1)) := by
    have hcast := packSubCast (Nat.sqrt n) n hsqrt
    have htemp : (frameL10t rE ein aus frei n).temp aus =
        (frameL9 rE ein aus frei n).temp aus := rfl
    rw [htemp]
    have hget : (frameL9 rE ein aus frei n).temp aus =
        some (Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int))
          (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int))
            (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩) := by
      show Function.update _ (frei + 1) _ aus = _
      rw [updateMiss _ _ _ _ (ltNeAdd haus)]
      show Function.update _ (frei + 2) _ aus = _
      rw [updateMiss _ _ _ _ (ltNeAdd haus)]
      show Function.update _ aus _ aus = _
      exact updateHit _ _ _
    rw [hget, hcast, hunLeft n, if_pos hcond]
  have hrun : (Schritt (leftBlk ein aus frei))^[kL + 22] (some r) =
      some (frameL10t rE ein aus frei n) := by
    rw [show kL + 22 = 22 + kL from Nat.add_comm kL 22, Function.iterate_add_apply, hrunL']
    exact hrunT
  have hpc' : (frameL10t rE ein aus frei n).pc = 50 := by
    show (frameL10t rE ein aus frei n).pc = (leftBlk ein aus frei).length
    rw [leftBlkLaenge]
    rfl
  refine ⟨kL + 22, _, hrun, hpc', hausT, ?_, ?_, ?_, ?_⟩
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
      r'.pc = 50 ∧ r'.temp aus = some (natVal ((Nat.unpair n).1)) ∧
      (∀ t, t < frei → t ≠ aus → r'.temp t = r.temp t) ∧
      r'.lokale = r.lokale ∧ r'.rueckgabe = r.rueckgabe ∧ r'.stopp = r.stopp := by
  obtain ⟨kL, rE, hrunL, hpcL, hsqrtL, hpresL, hlokL, hrueckL, hstoppL, hkL⟩ :=
    sqrtSchleife ein frei n r (leftSel ein aus frei) hpc hr hein
  have hrunL' : (Schritt (leftBlk ein aus frei))^[kL] (some r) = some rE := hrunL
  have heqE : rE.temp ein = some (natVal n) := by
    rw [hpresL _ hein]
    exact hr
  have hrunE := selElseRun ein aus frei n rE hpcL hsqrtL heqE hein haus hcond
  have hausE : (frameL11e rE ein aus frei n).temp aus =
      some (natVal ((Nat.unpair n).1)) := by
    have hget : (frameL11e rE ein aus frei n).temp aus = some (natVal (Nat.sqrt n)) :=
      updateHit _ _ _
    rw [hget, hunLeft n, if_neg hcond]
  have hrun : (Schritt (leftBlk ein aus frei))^[kL + 25] (some r) =
      some (frameL11e rE ein aus frei n) := by
    rw [show kL + 25 = 25 + kL from Nat.add_comm kL 25, Function.iterate_add_apply, hrunL']
    exact hrunE
  have hpc' : (frameL11e rE ein aus frei n).pc = 50 := by
    show (frameL11e rE ein aus frei n).pc = (leftBlk ein aus frei).length
    rw [leftBlkLaenge]
    rfl
  refine ⟨kL + 25, _, hrun, hpc', hausE, ?_, ?_, ?_, ?_⟩
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
  apply And.intro hein
  apply And.intro haus
  apply And.intro hunters
  intro n r hpc hr
  refine ⟨?_, ?_⟩
  · intro a ha
    have ha0 : a = (Nat.unpair n).1 := by
      have h0 : Part.some ((Nat.unpair n).1) = Part.some a := by
        change Part.some ((Nat.unpair n).1) = Part.some a at ha
        exact ha
      exact (Part.some_injective h0).symm
    subst ha0
    by_cases hcond : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n
    · obtain ⟨k, r', hrun, hpc', haus', hpres, hlok, hrueck, hstopp⟩ :=
        leftArrivalThen ein aus frei n r hpc hr hein haus hunters hcond
      exact ⟨k, r', hrun, hpc', haus', hpres, hlok, hrueck, hstopp⟩
    · obtain ⟨k, r', hrun, hpc', haus', hpres, hlok, hrueck, hstopp⟩ :=
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
        have heq : r' = rT := Option.some.inj (hk.symm.trans hrunT)
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
        have heq : r' = rE := Option.some.inj (hk.symm.trans hrunE)
        subst heq
        have heval : Nat.Partrec.Code.eval .left n = Part.some ((Nat.unpair n).1) := rfl
        exact ⟨(Nat.unpair n).1, heval, hausE, hpresE, hlokE, hrueckE, hstoppE⟩
      · exfalso
        exact laufStirbtNach _ _ kE k _ _ hrunE hpcE hk h

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
