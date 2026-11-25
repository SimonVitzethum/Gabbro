module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Left

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Selection for the right projection: square the root, subtract from the input
    for the difference `d`, save `d`, subtract the root to form `d - s`
    speculatively, then overwrite with the root when `d` is smaller. Selection
    offsets follow the search exit at 25. Scratch slots `frei + 0/1/2/3` are used. -/
def rightSel (ein aus frei : Nat) : List Befehl :=
  [.binden nameX (frei + 0), .lesen (frei + 1) 0, .blockEnde 1, .binden nameX (frei + 1),
   .lesen (frei + 2) 0, .blockEnde 1, .binaer .mul (frei + 1), .binden nameX (frei + 1),
   .lesen (frei + 2) 0, .blockEnde 1, .binden nameX ein, .lesen (frei + 1) 0, .blockEnde 1,
   .binaer .sub (frei + 1), .binden nameX (frei + 1), .lesen (frei + 3) 0, .blockEnde 1,
   .binden nameX (frei + 0), .lesen (frei + 2) 0, .blockEnde 1, .binaer .sub (frei + 1),
   .binden nameX (frei + 1), .lesen aus 0, .blockEnde 1, .binden nameX (frei + 3),
   .lesen (frei + 1) 0, .blockEnde 1, .vergleichen .lt (frei + 1),
   .springeWenn (frei + 1) false 4, .binden nameX (frei + 0), .lesen aus 0, .blockEnde 1]

/-- The relocatable block for `right`: search prefix followed by selection. -/
def rightBlk (ein aus frei : Nat) : List Befehl :=
  sqrtPrefix ein frei ++ rightSel ein aus frei

theorem rightBlkLaenge (ein aus frei : Nat) : (rightBlk ein aus frei).length = 57 := by
  rfl

/-- The squared root, the difference and the twice-subtracted value as exact
    runtime integers. -/
def sqPack (s : Nat) : Dynamisch :=
  Ganzzahl.pack ⟨_, _, Arith.auswerten .mul (Zahl.literal (s : Int)) (Zahl.literal (s : Int))⟩

def diffPack (n s : Nat) : Dynamisch :=
  Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int))
    (Arith.auswerten .mul (Zahl.literal (s : Int)) (Zahl.literal (s : Int)))⟩

def diffSubPack (n s : Nat) : Dynamisch :=
  Ganzzahl.pack ⟨_, _, Arith.auswerten .sub
    (Arith.auswerten .sub (Zahl.literal (n : Int))
      (Arith.auswerten .mul (Zahl.literal (s : Int)) (Zahl.literal (s : Int))))
    (Zahl.literal (s : Int))⟩

/-- The twice-subtracted machine value is the exact natural `d - s`. -/
theorem packDiffSub (s n : Nat) (h : s * s ≤ n) (h2 : s ≤ n - s * s) :
    diffSubPack n s = natVal (n - s * s - s) := by
  let d := n - s * s
  have hmulLo : (Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).1 = ((s * s : Nat) : Int) := by
    show min (min ((s : Int) * (s : Int)) ((s : Int) * (s : Int)))
      (min ((s : Int) * (s : Int)) ((s : Int) * (s : Int))) = _
    rw [hmul_lo s]
    exact (Nat.cast_mul s s).symm
  have hmulHi : (Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).2 = ((s * s : Nat) : Int) := by
    show max (max ((s : Int) * (s : Int)) ((s : Int) * (s : Int)))
      (max ((s : Int) * (s : Int)) ((s : Int) * (s : Int))) = _
    rw [hmul_hi s]
    exact (Nat.cast_mul s s).symm
  have hcast1 : (n : Int) - ((s * s : Nat) : Int) = ((d : Nat) : Int) := by
    dsimp only [d]
    rw [← Nat.cast_mul]
    exact intSubNat s n h
  have hcast2 : ((d : Nat) : Int) - (s : Int) = (((d - s : Nat)) : Int) := (Nat.cast_sub h2).symm
  have hbounds1 : (Arith.sub.bounds (n : Int) (n : Int)
      ((Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).1)
      ((Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).2)) =
      (((d : Nat) : Int), ((d : Nat) : Int)) := by
    simp only [Arith.bounds]
    rw [hmulLo, hmulHi, hcast1]
  have hlo : (Arith.sub.bounds ((Arith.sub.bounds (n : Int) (n : Int)
      ((Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).1)
      ((Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).2)).1)
      ((Arith.sub.bounds (n : Int) (n : Int)
      ((Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).1)
      ((Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).2)).2)
      (s : Int) (s : Int)).1 = (((d - s : Nat)) : Int) := by
    rw [show (Arith.sub.bounds (n : Int) (n : Int)
      ((Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).1)
      ((Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).2)).1 = ((d : Nat) : Int) from
        congrArg Prod.fst hbounds1]
    exact hcast2
  have hhi : (Arith.sub.bounds ((Arith.sub.bounds (n : Int) (n : Int)
      ((Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).1)
      ((Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).2)).1)
      ((Arith.sub.bounds (n : Int) (n : Int)
      ((Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).1)
      ((Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).2)).2)
      (s : Int) (s : Int)).2 = (((d - s : Nat)) : Int) := by
    rw [show (Arith.sub.bounds (n : Int) (n : Int)
      ((Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).1)
      ((Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).2)).2 = ((d : Nat) : Int) from
        congrArg Prod.snd hbounds1]
    exact hcast2
  have hw : (Arith.auswerten .sub
      (Arith.auswerten .sub (Zahl.literal (n : Int))
        (Arith.auswerten .mul (Zahl.literal (s : Int)) (Zahl.literal (s : Int))))
      (Zahl.literal (s : Int))).wert = (((d - s : Nat)) : Int) := by
    change ((n : Int) - (s : Int) * (s : Int)) - (s : Int) = (((d - s : Nat)) : Int)
    rw [← Nat.cast_mul, hcast1, hcast2]
  unfold diffSubPack
  exact packEqOfBounds _ _ _ _ hlo hhi hw

/-- The unpairing splits on the difference against the root. -/
theorem hunRight (n : Nat) : (Nat.unpair n).2 =
    (if n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n
      then Nat.sqrt n
      else n - Nat.sqrt n * Nat.sqrt n - Nat.sqrt n) := by
  rw [hunLeft]
  split <;> rfl

/-- Selection states from the search exit, with `s` the integer root. -/
def frameR1 (e : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { e with pc := 28, temp := Function.update e.temp (frei + 1) (some (natVal (Nat.sqrt n))) }
def frameR2 (e : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameR1 e ein aus frei n with pc := 31, temp := Function.update (frameR1 e ein aus frei n).temp (frei + 2) (some (natVal (Nat.sqrt n))) }
def frameR3 (e : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameR2 e ein aus frei n with pc := 32, temp := Function.update (frameR2 e ein aus frei n).temp (frei + 1) (some (sqPack (Nat.sqrt n))) }
def frameR4 (e : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameR3 e ein aus frei n with pc := 35, temp := Function.update (frameR3 e ein aus frei n).temp (frei + 2) (some (sqPack (Nat.sqrt n))) }
def frameR5 (e : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameR4 e ein aus frei n with pc := 38, temp := Function.update (frameR4 e ein aus frei n).temp (frei + 1) (some (natVal n)) }
def frameR6 (e : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameR5 e ein aus frei n with pc := 39, temp := Function.update (frameR5 e ein aus frei n).temp (frei + 1) (some (diffPack n (Nat.sqrt n))) }
def frameR7 (e : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameR6 e ein aus frei n with pc := 42, temp := Function.update (frameR6 e ein aus frei n).temp (frei + 3) (some (diffPack n (Nat.sqrt n))) }
def frameR8 (e : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameR7 e ein aus frei n with pc := 45, temp := Function.update (frameR7 e ein aus frei n).temp (frei + 2) (some (natVal (Nat.sqrt n))) }
def frameR9 (e : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameR8 e ein aus frei n with pc := 46, temp := Function.update (frameR8 e ein aus frei n).temp (frei + 1) (some (diffSubPack n (Nat.sqrt n))) }
def frameR10 (e : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameR9 e ein aus frei n with pc := 49, temp := Function.update (frameR9 e ein aus frei n).temp aus (some (diffSubPack n (Nat.sqrt n))) }
def frameR11 (e : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameR10 e ein aus frei n with pc := 52, temp := Function.update (frameR10 e ein aus frei n).temp (frei + 1) (some (diffPack n (Nat.sqrt n))) }
def frameR12 (e : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameR11 e ein aus frei n with pc := 53, temp := Function.update (frameR11 e ein aus frei n).temp (frei + 1) (some ⟨.bool, cmpBoolLeft (Nat.sqrt n) n⟩) }
def frameR13e (e : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameR12 e ein aus frei n with pc := 57 }
def frameR14t (e : Rahmen) (ein aus frei n : Nat) : Rahmen :=
  { frameR12 e ein aus frei n with pc := 57, temp := Function.update (frameR12 e ein aus frei n).temp aus (some (natVal (Nat.sqrt n))) }

theorem selLinkR1 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n))) :
    (Schritt (rightBlk ein aus frei))^[3] (some e) = some (frameR1 e ein aus frei n) := by
  have g0 : (rightBlk ein aus frei)[25]? = some (.binden nameX (frei + 0)) := by rfl
  have g1 : (rightBlk ein aus frei)[25 + 1]? = some (.lesen (frei + 1) 0) := by rfl
  have g2 : (rightBlk ein aus frei)[25 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 25 (frei + 1) (frei + 0) _ hepc hes g0 g1 g2
  simpa only [frameR1] using e0

theorem selLinkR2 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n))) :
    (Schritt (rightBlk ein aus frei))^[6] (some e) = some (frameR2 e ein aus frei n) := by
  have h11 := selLinkR1 ein aus frei n e hepc hes
  have hpc : (frameR1 e ein aus frei n).pc = 28 := rfl
  have hq : (frameR1 e ein aus frei n).temp (frei + 1) = some (natVal (Nat.sqrt n)) := updateHit _ _ _
  have g0 : (rightBlk ein aus frei)[28]? = some (.binden nameX (frei + 1)) := by rfl
  have g1 : (rightBlk ein aus frei)[28 + 1]? = some (.lesen (frei + 2) 0) := by rfl
  have g2 : (rightBlk ein aus frei)[28 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 28 (frei + 2) (frei + 1) _ hpc hq g0 g1 g2
  rw [show (6 : Nat) = 3 + 3 from rfl, Function.iterate_add_apply, h11]
  simpa only [frameR2] using e0

theorem selLinkR3 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n))) :
    (Schritt (rightBlk ein aus frei))^[7] (some e) = some (frameR3 e ein aus frei n) := by
  have h22 := selLinkR2 ein aus frei n e hepc hes
  have ha : (frameR2 e ein aus frei n).zahl (frei + 1) =
      some ⟨((Nat.sqrt n : Nat) : Int), ((Nat.sqrt n : Nat) : Int), Zahl.literal ((Nat.sqrt n : Nat) : Int)⟩ := by
    have hA : (frameR2 e ein aus frei n).temp (frei + 1) = some (natVal (Nat.sqrt n)) := by
      show Function.update _ (frei + 2) _ (frei + 1) = _
      rw [updateMiss _ _ _ _ (addNeLinks (by decide : (1 : Nat) ≠ 2))]
      exact updateHit _ _ _
    exact zahlOfNat _ _ _ hA
  have hb : (frameR2 e ein aus frei n).zahl (frei + 2) =
      some ⟨((Nat.sqrt n : Nat) : Int), ((Nat.sqrt n : Nat) : Int), Zahl.literal ((Nat.sqrt n : Nat) : Int)⟩ :=
    zahlOfNat _ _ _ (updateHit _ _ _)
  have g : (rightBlk ein aus frei)[31]? = some (.binaer .mul (frei + 1)) := by rfl
  have e0 : (Schritt (rightBlk ein aus frei))^[1] (some (frameR2 e ein aus frei n)) =
      some (frameR3 e ein aus frei n) :=
    schrittBinaer _ _ _ _ .mul _ _ (by rfl) ha hb g
  rw [show (7 : Nat) = 1 + 6 from rfl, Function.iterate_add_apply, h22]
  exact e0

theorem selLinkR4 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n))) :
    (Schritt (rightBlk ein aus frei))^[10] (some e) = some (frameR4 e ein aus frei n) := by
  have h33 := selLinkR3 ein aus frei n e hepc hes
  have hq : (frameR3 e ein aus frei n).temp (frei + 1) = some (sqPack (Nat.sqrt n)) := updateHit _ _ _
  have g0 : (rightBlk ein aus frei)[32]? = some (.binden nameX (frei + 1)) := by rfl
  have g1 : (rightBlk ein aus frei)[32 + 1]? = some (.lesen (frei + 2) 0) := by rfl
  have g2 : (rightBlk ein aus frei)[32 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 32 (frei + 2) (frei + 1) _ (by rfl : (frameR3 e ein aus frei n).pc = 32) hq g0 g1 g2
  rw [show (10 : Nat) = 3 + 7 from rfl, Function.iterate_add_apply, h33]
  simpa only [frameR4] using e0

theorem selLinkR5 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (rightBlk ein aus frei))^[13] (some e) = some (frameR5 e ein aus frei n) := by
  have h44 := selLinkR4 ein aus frei n e hepc hes
  have hq : (frameR4 e ein aus frei n).temp ein = some (natVal n) := by
    show Function.update _ (frei + 2) _ ein = _
    rw [updateMiss _ _ _ _ (ltNeAdd hein)]
    show Function.update _ (frei + 1) _ ein = _
    rw [updateMiss _ _ _ _ (ltNeAdd hein)]
    show Function.update _ (frei + 2) _ ein = _
    rw [updateMiss _ _ _ _ (ltNeAdd hein)]
    show Function.update _ (frei + 1) _ ein = _
    rw [updateMiss _ _ _ _ (ltNeAdd hein)]
    exact heq
  have g0 : (rightBlk ein aus frei)[35]? = some (.binden nameX ein) := by rfl
  have g1 : (rightBlk ein aus frei)[35 + 1]? = some (.lesen (frei + 1) 0) := by rfl
  have g2 : (rightBlk ein aus frei)[35 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 35 (frei + 1) ein _ (by rfl) hq g0 g1 g2
  rw [show (13 : Nat) = 3 + 10 from rfl, Function.iterate_add_apply, h44]
  simpa only [frameR5] using e0

theorem selLinkR6 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (rightBlk ein aus frei))^[14] (some e) = some (frameR6 e ein aus frei n) := by
  have h55 := selLinkR5 ein aus frei n e hepc hes heq hein
  have ha : (frameR5 e ein aus frei n).zahl (frei + 1) = some ⟨(n : Int), (n : Int), Zahl.literal (n : Int)⟩ := by
    have hA : (frameR5 e ein aus frei n).temp (frei + 1) = some (natVal n) := updateHit _ _ _
    exact zahlOfNat _ _ _ hA
  have hb : (frameR5 e ein aus frei n).zahl (frei + 2) = some ⟨_, _, Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int))⟩ := by
    have hA : (frameR5 e ein aus frei n).temp (frei + 2) = some (sqPack (Nat.sqrt n)) := by
      show Function.update _ (frei + 1) _ (frei + 2) = _
      rw [updateMiss _ _ _ _ (addNeLinks (by decide : (2 : Nat) ≠ 1))]
      exact updateHit _ _ _
    show (((frameR5 e ein aus frei n).temp (frei + 2)).bind alsGanzzahl) = some ⟨_, _, Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int))⟩
    rw [hA]
    rfl
  have g : (rightBlk ein aus frei)[38]? = some (.binaer .sub (frei + 1)) := by rfl
  have e0 : (Schritt (rightBlk ein aus frei))^[1] (some (frameR5 e ein aus frei n)) =
      some (frameR6 e ein aus frei n) :=
    schrittBinaer _ _ _ _ .sub _ _ (by rfl) ha hb g
  rw [show (14 : Nat) = 1 + 13 from rfl, Function.iterate_add_apply, h55]
  exact e0

theorem selLinkR7 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (rightBlk ein aus frei))^[17] (some e) = some (frameR7 e ein aus frei n) := by
  have h66 := selLinkR6 ein aus frei n e hepc hes heq hein
  have hq : (frameR6 e ein aus frei n).temp (frei + 1) = some (diffPack n (Nat.sqrt n)) := updateHit _ _ _
  have g0 : (rightBlk ein aus frei)[39]? = some (.binden nameX (frei + 1)) := by rfl
  have g1 : (rightBlk ein aus frei)[39 + 1]? = some (.lesen (frei + 3) 0) := by rfl
  have g2 : (rightBlk ein aus frei)[39 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 39 (frei + 3) (frei + 1) _ (by rfl) hq g0 g1 g2
  rw [show (17 : Nat) = 3 + 14 from rfl, Function.iterate_add_apply, h66]
  simpa only [frameR7] using e0

theorem selLinkR8 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (rightBlk ein aus frei))^[20] (some e) = some (frameR8 e ein aus frei n) := by
  have h77 := selLinkR7 ein aus frei n e hepc hes heq hein
  have hq : (frameR7 e ein aus frei n).temp (frei + 0) = some (natVal (Nat.sqrt n)) := by
    show Function.update _ (frei + 3) _ (frei + 0) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 3))]
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
  have g0 : (rightBlk ein aus frei)[42]? = some (.binden nameX (frei + 0)) := by rfl
  have g1 : (rightBlk ein aus frei)[42 + 1]? = some (.lesen (frei + 2) 0) := by rfl
  have g2 : (rightBlk ein aus frei)[42 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 42 (frei + 2) (frei + 0) _ (by rfl) hq g0 g1 g2
  rw [show (20 : Nat) = 3 + 17 from rfl, Function.iterate_add_apply, h77]
  simpa only [frameR8] using e0

theorem selLinkR9 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (rightBlk ein aus frei))^[21] (some e) = some (frameR9 e ein aus frei n) := by
  have h88 := selLinkR8 ein aus frei n e hepc hes heq hein
  have ha : (frameR8 e ein aus frei n).zahl (frei + 1) = some ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩ := by
    have hA : (frameR8 e ein aus frei n).temp (frei + 1) = some (diffPack n (Nat.sqrt n)) := by
      show Function.update _ (frei + 2) _ (frei + 1) = _
      rw [updateMiss _ _ _ _ (addNeLinks (by decide : (1 : Nat) ≠ 2))]
      show Function.update _ (frei + 3) _ (frei + 1) = _
      rw [updateMiss _ _ _ _ (addNeLinks (by decide : (1 : Nat) ≠ 3))]
      exact updateHit _ _ _
    show (((frameR8 e ein aus frei n).temp (frei + 1)).bind alsGanzzahl) = some ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩
    rw [hA]
    rfl
  have hb : (frameR8 e ein aus frei n).zahl (frei + 2) = some ⟨((Nat.sqrt n : Nat) : Int), ((Nat.sqrt n : Nat) : Int), Zahl.literal ((Nat.sqrt n : Nat) : Int)⟩ :=
    zahlOfNat _ _ _ (updateHit _ _ _)
  have g : (rightBlk ein aus frei)[45]? = some (.binaer .sub (frei + 1)) := by rfl
  have e0 : (Schritt (rightBlk ein aus frei))^[1] (some (frameR8 e ein aus frei n)) =
      some (frameR9 e ein aus frei n) :=
    schrittBinaer _ _ _ _ .sub _ _ (by rfl) ha hb g
  rw [show (21 : Nat) = 1 + 20 from rfl, Function.iterate_add_apply, h88]
  exact e0

theorem selLinkR10 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) (haus : aus < frei) :
    (Schritt (rightBlk ein aus frei))^[24] (some e) = some (frameR10 e ein aus frei n) := by
  have h99 := selLinkR9 ein aus frei n e hepc hes heq hein
  have hq : (frameR9 e ein aus frei n).temp (frei + 1) = some (diffSubPack n (Nat.sqrt n)) := updateHit _ _ _
  have g0 : (rightBlk ein aus frei)[46]? = some (.binden nameX (frei + 1)) := by rfl
  have g1 : (rightBlk ein aus frei)[46 + 1]? = some (.lesen aus 0) := by rfl
  have g2 : (rightBlk ein aus frei)[46 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 46 aus (frei + 1) _ (by rfl) hq g0 g1 g2
  rw [show (24 : Nat) = 3 + 21 from rfl, Function.iterate_add_apply, h99]
  simpa only [frameR10] using e0

theorem selLinkR11 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) (haus : aus < frei) :
    (Schritt (rightBlk ein aus frei))^[27] (some e) = some (frameR11 e ein aus frei n) := by
  have h1010 := selLinkR10 ein aus frei n e hepc hes heq hein haus
  have hq : (frameR10 e ein aus frei n).temp (frei + 3) = some (diffPack n (Nat.sqrt n)) := by
    show Function.update _ aus _ (frei + 3) = _
    rw [updateMiss _ _ _ _ (scratchNeAus (Nat.le_add_right frei 3) haus)]
    show Function.update _ (frei + 1) _ (frei + 3) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (3 : Nat) ≠ 1))]
    show Function.update _ (frei + 2) _ (frei + 3) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (3 : Nat) ≠ 2))]
    exact updateHit _ _ _
  have g0 : (rightBlk ein aus frei)[49]? = some (.binden nameX (frei + 3)) := by rfl
  have g1 : (rightBlk ein aus frei)[49 + 1]? = some (.lesen (frei + 1) 0) := by rfl
  have g2 : (rightBlk ein aus frei)[49 + 2]? = some (.blockEnde 1) := by rfl
  have e0 := laufKopie _ _ 49 (frei + 1) (frei + 3) _ (by rfl) hq g0 g1 g2
  rw [show (27 : Nat) = 3 + 24 from rfl, Function.iterate_add_apply, h1010]
  simpa only [frameR11] using e0

theorem selLinkR12 (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) (haus : aus < frei) :
    (Schritt (rightBlk ein aus frei))^[28] (some e) = some (frameR12 e ein aus frei n) := by
  have h1111 := selLinkR11 ein aus frei n e hepc hes heq hein haus
  have ha : (frameR11 e ein aus frei n).zahl (frei + 1) = some ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int)) (Arith.auswerten .mul (Zahl.literal ((Nat.sqrt n : Nat) : Int)) (Zahl.literal ((Nat.sqrt n : Nat) : Int)))⟩ := by
    show (((frameR11 e ein aus frei n).temp (frei + 1)).bind alsGanzzahl) = _
    rw [show (frameR11 e ein aus frei n).temp (frei + 1) = some (diffPack n (Nat.sqrt n)) from updateHit _ _ _]
    rfl
  have hb : (frameR11 e ein aus frei n).zahl (frei + 2) = some ⟨((Nat.sqrt n : Nat) : Int), ((Nat.sqrt n : Nat) : Int), Zahl.literal ((Nat.sqrt n : Nat) : Int)⟩ := by
    have hA : (frameR11 e ein aus frei n).temp (frei + 2) = some (natVal (Nat.sqrt n)) := by
      show Function.update _ (frei + 1) _ (frei + 2) = _
      rw [updateMiss _ _ _ _ (addNeLinks (by decide : (2 : Nat) ≠ 1))]
      show Function.update _ aus _ (frei + 2) = _
      rw [updateMiss _ _ _ _ (scratchNeAus (Nat.le_add_right frei 2) haus)]
      show Function.update _ (frei + 1) _ (frei + 2) = _
      rw [updateMiss _ _ _ _ (addNeLinks (by decide : (2 : Nat) ≠ 1))]
      exact updateHit _ _ _
    exact zahlOfNat _ _ _ hA
  have g : (rightBlk ein aus frei)[52]? = some (.vergleichen .lt (frei + 1)) := by rfl
  have e0 : (Schritt (rightBlk ein aus frei))^[1] (some (frameR11 e ein aus frei n)) =
      some (frameR12 e ein aus frei n) :=
    schrittVergleichen _ _ _ _ .lt _ _ (by rfl) ha hb g
  rw [show (28 : Nat) = 1 + 27 from rfl, Function.iterate_add_apply, h1111]
  exact e0

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
