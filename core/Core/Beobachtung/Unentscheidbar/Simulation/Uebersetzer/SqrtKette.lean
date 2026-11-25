module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.SqrtSchritt

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Loop states after each prefix of one iteration, from the loop entry `q`
    (program counter 2, counter value `s`, input `n`). -/
def frameA1 (q : Rahmen) (frei s : Nat) : Rahmen :=
  { q with pc := 2 + 3, temp := Function.update q.temp (frei + 1) (some (natVal s)) }

def frameA2 (q : Rahmen) (frei s : Nat) : Rahmen :=
  { frameA1 q frei s with pc := 2 + 4, temp := Function.update (frameA1 q frei s).temp (frei + 1) (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int))⟩)) }

def frameA3 (q : Rahmen) (frei s : Nat) : Rahmen :=
  { frameA2 q frei s with pc := 2 + 7, temp := Function.update (frameA2 q frei s).temp (frei + 3) (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int))⟩)) }

def frameA4 (q : Rahmen) (frei s : Nat) : Rahmen :=
  { frameA3 q frei s with pc := 2 + 10, temp := Function.update (frameA3 q frei s).temp (frei + 4) (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int))⟩)) }

def frameA5 (q : Rahmen) (frei s : Nat) : Rahmen :=
  { frameA4 q frei s with pc := 2 + 11, temp := Function.update (frameA4 q frei s).temp (frei + 3) (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .mul (Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int))) (Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int)))⟩)) }

def frameA6 (q : Rahmen) (frei s : Nat) : Rahmen :=
  { frameA5 q frei s with pc := 2 + 14, temp := Function.update (frameA5 q frei s).temp (frei + 5) (some (Ganzzahl.pack ⟨_, _, Arith.auswerten .mul (Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int))) (Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int)))⟩)) }

def frameA7 (q : Rahmen) (frei s n : Nat) : Rahmen :=
  { frameA6 q frei s with pc := 2 + 17, temp := Function.update (frameA6 q frei s).temp (frei + 6) (some (natVal n)) }

def cmpBool (s n : Nat) : Bool :=
  Compare.eval .le (Arith.auswerten .mul (Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int))) (Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int)))).wert (Zahl.literal (n : Int)).wert

def frameA8 (q : Rahmen) (frei s n : Nat) : Rahmen :=
  { frameA7 q frei s n with pc := 2 + 18, temp := Function.update (frameA7 q frei s n).temp (frei + 5) (some ⟨.bool, cmpBool s n⟩) }

/-- Loop states after the conditional jump: continue at 21 or exit at 25. -/
def frameA9w (q : Rahmen) (frei s n : Nat) : Rahmen :=
  { frameA8 q frei s n with pc := 21 }

def frameA9e (q : Rahmen) (frei s n : Nat) : Rahmen :=
  { frameA8 q frei s n with pc := 25 }

/-- Loop states after writing back the successor and jumping to the top. -/
def frameA10 (q : Rahmen) (frei s n : Nat) : Rahmen :=
  { frameA9w q frei s n with pc := 24, temp := Function.update (frameA9w q frei s n).temp (frei + 0) (some (natVal (s + 1))) }

def frameA11 (q : Rahmen) (frei s n : Nat) : Rahmen :=
  { frameA10 q frei s n with pc := 2 }

/-- The squared successor read back from the machine state. -/
theorem mulWert (s : Nat) : (Arith.auswerten .mul
    (Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int)))
    (Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int)))).wert =
      ((s : Int) + ((1 : Nat) : Int)) * ((s : Int) + ((1 : Nat) : Int)) := rfl

/-- First three steps: copy the counter into the working slot. -/
theorem kette1 (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqs : q.temp (frei + 0) = some (natVal s)) :
    (Schritt (sqrtPrefix ein frei ++ rest))^[3] (some q) =
      some (frameA1 q frei s) := by
  have hlen : (sqrtPrefix ein frei).length = 25 := sqrtPrefixLaenge _ _
  have g0 : ((sqrtPrefix ein frei ++ rest)[2]?) = some (.binden nameX (frei + 0)) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have g1 : ((sqrtPrefix ein frei ++ rest)[2 + 1]?) = some (.lesen (frei + 1) 0) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have g2 : ((sqrtPrefix ein frei ++ rest)[2 + 2]?) = some (.blockEnde 1) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have e := laufKopie _ q 2 (frei + 1) (frei + 0) (some (natVal s)) hqpc hqs g0 g1 g2
  simp only [frameA1] at *
  exact e

/-- Next step: add one to the working slot. -/
theorem kette2 (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqs : q.temp (frei + 0) = some (natVal s))
    (hq1 : q.temp (frei + 2) = some (natVal 1)) :
    (Schritt (sqrtPrefix ein frei ++ rest))^[4] (some q) =
      some (frameA2 q frei s) := by
  have h11 := kette1 ein frei s n q rest hqpc hqs
  have hlen : (sqrtPrefix ein frei).length = 25 := sqrtPrefixLaenge _ _
  have hpcA1 : (frameA1 q frei s).pc = 5 := rfl
  have ht1 : (frameA1 q frei s).temp (frei + 1) = some (natVal s) :=
    updateHit _ _ _
  have ha1 : (frameA1 q frei s).zahl (frei + 1) =
      some ⟨(s : Int), (s : Int), Zahl.literal (s : Int)⟩ := by
    show (((frameA1 q frei s).temp (frei + 1)).bind alsGanzzahl) = _
    rw [ht1]
    rfl
  have ht1b : (frameA1 q frei s).temp (frei + 2) = some (natVal 1) := by
    show Function.update q.temp (frei + 1) (some (natVal s)) (frei + 2) = _
    rw [updateMiss _ _ _ _ (by omega), hq1]
  have hb1 : (frameA1 q frei s).zahl (frei + 2) =
      some ⟨((1 : Nat) : Int), ((1 : Nat) : Int), Zahl.literal ((1 : Nat) : Int)⟩ := by
    show (((frameA1 q frei s).temp (frei + 2)).bind alsGanzzahl) = _
    rw [ht1b]
    rfl
  have g3 : ((sqrtPrefix ein frei ++ rest)[5]?) = some (.binaer .add (frei + 1)) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have e1 : (Schritt (sqrtPrefix ein frei ++ rest))^[1] (some (frameA1 q frei s)) =
      some (frameA2 q frei s) :=
    schrittBinaer _ _ _ _ .add _ _ hpcA1 ha1 hb1 g3
  have e : (Schritt (sqrtPrefix ein frei ++ rest))^[4] (some q) =
      (Schritt (sqrtPrefix ein frei ++ rest))^[1]
        ((Schritt (sqrtPrefix ein frei ++ rest))^[3] (some q)) := by
    rw [show (4 : Nat) = 1 + 3 from rfl, Function.iterate_add_apply]
  rw [e, h11, e1]

/-- Copy the successor into both squaring slots (first copy). -/
theorem kette3 (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqs : q.temp (frei + 0) = some (natVal s))
    (hq1 : q.temp (frei + 2) = some (natVal 1)) :
    (Schritt (sqrtPrefix ein frei ++ rest))^[7] (some q) =
      some (frameA3 q frei s) := by
  have h22 := kette2 ein frei s n q rest hqpc hqs hq1
  have hlen : (sqrtPrefix ein frei).length = 25 := sqrtPrefixLaenge _ _
  have hpcA2 : (frameA2 q frei s).pc = 6 := rfl
  have hq : (frameA2 q frei s).temp (frei + 1) = some (Ganzzahl.pack ⟨_, _,
      Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int))⟩) :=
    updateHit _ _ _
  have g6 : ((sqrtPrefix ein frei ++ rest)[6]?) = some (.binden nameX (frei + 1)) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have g7 : ((sqrtPrefix ein frei ++ rest)[6 + 1]?) = some (.lesen (frei + 3) 0) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have g8 : ((sqrtPrefix ein frei ++ rest)[6 + 2]?) = some (.blockEnde 1) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have e1 := laufKopie _ _ 6 (frei + 3) (frei + 1) _ hpcA2 hq g6 g7 g8
  have e : (Schritt (sqrtPrefix ein frei ++ rest))^[7] (some q) =
      (Schritt (sqrtPrefix ein frei ++ rest))^[3]
        ((Schritt (sqrtPrefix ein frei ++ rest))^[4] (some q)) := by
    rw [show (7 : Nat) = 3 + 4 from rfl, Function.iterate_add_apply]
  rw [e, h22]
  simp only [frameA3] at *
  exact e1

/-- Copy the successor into both squaring slots (second copy). -/
theorem kette4 (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqs : q.temp (frei + 0) = some (natVal s))
    (hq1 : q.temp (frei + 2) = some (natVal 1)) :
    (Schritt (sqrtPrefix ein frei ++ rest))^[10] (some q) =
      some (frameA4 q frei s) := by
  have h33 := kette3 ein frei s n q rest hqpc hqs hq1
  have hlen : (sqrtPrefix ein frei).length = 25 := sqrtPrefixLaenge _ _
  have hpcA3 : (frameA3 q frei s).pc = 9 := rfl
  have hq : (frameA3 q frei s).temp (frei + 1) = some (Ganzzahl.pack ⟨_, _,
      Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int))⟩) := by
    show Function.update _ (frei + 3) _ (frei + 1) = _
    rw [updateMiss _ _ _ _ (by omega)]
    exact updateHit _ _ _
  have g9 : ((sqrtPrefix ein frei ++ rest)[9]?) = some (.binden nameX (frei + 1)) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have g10 : ((sqrtPrefix ein frei ++ rest)[9 + 1]?) = some (.lesen (frei + 4) 0) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have g11 : ((sqrtPrefix ein frei ++ rest)[9 + 2]?) = some (.blockEnde 1) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have e1 := laufKopie _ _ 9 (frei + 4) (frei + 1) _ hpcA3 hq g9 g10 g11
  have e : (Schritt (sqrtPrefix ein frei ++ rest))^[10] (some q) =
      (Schritt (sqrtPrefix ein frei ++ rest))^[3]
        ((Schritt (sqrtPrefix ein frei ++ rest))^[7] (some q)) := by
    rw [show (10 : Nat) = 3 + 7 from rfl, Function.iterate_add_apply]
  rw [e, h33]
  simp only [frameA4] at *
  exact e1

/-- Square the successor. -/
theorem kette5 (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqs : q.temp (frei + 0) = some (natVal s))
    (hq1 : q.temp (frei + 2) = some (natVal 1)) :
    (Schritt (sqrtPrefix ein frei ++ rest))^[11] (some q) =
      some (frameA5 q frei s) := by
  have h44 := kette4 ein frei s n q rest hqpc hqs hq1
  have hlen : (sqrtPrefix ein frei).length = 25 := sqrtPrefixLaenge _ _
  have hpcA4 : (frameA4 q frei s).pc = 12 := rfl
  have ha4 : (frameA4 q frei s).zahl (frei + 3) = some ⟨_, _, Arith.auswerten .add
      (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int))⟩ := by
    have hA4t : (frameA4 q frei s).temp (frei + 3) = some (Ganzzahl.pack ⟨_, _,
        Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int))⟩) := by
      show Function.update _ (frei + 4) _ (frei + 3) = _
      rw [updateMiss _ _ _ _ (by omega)]
      exact updateHit _ _ _
    show (((frameA4 q frei s).temp (frei + 3)).bind alsGanzzahl) = _
    rw [hA4t]
    rfl
  have hb4 : (frameA4 q frei s).zahl (frei + 4) = some ⟨_, _, Arith.auswerten .add
      (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int))⟩ := by
    show (((frameA4 q frei s).temp (frei + 4)).bind alsGanzzahl) = _
    rw [show (frameA4 q frei s).temp (frei + 4) = some (Ganzzahl.pack ⟨_, _,
      Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int))⟩) from updateHit _ _ _]
    rfl
  have g12 : ((sqrtPrefix ein frei ++ rest)[12]?) = some (.binaer .mul (frei + 3)) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have e1 : (Schritt (sqrtPrefix ein frei ++ rest))^[1] (some (frameA4 q frei s)) =
      some (frameA5 q frei s) :=
    schrittBinaer _ _ _ _ .mul _ _ hpcA4 ha4 hb4 g12
  have e : (Schritt (sqrtPrefix ein frei ++ rest))^[11] (some q) =
      (Schritt (sqrtPrefix ein frei ++ rest))^[1]
        ((Schritt (sqrtPrefix ein frei ++ rest))^[10] (some q)) := by
    rw [show (11 : Nat) = 1 + 10 from rfl, Function.iterate_add_apply]
  rw [e, h44, e1]

/-- Copy the square into the comparison cell. -/
theorem kette6 (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqs : q.temp (frei + 0) = some (natVal s))
    (hq1 : q.temp (frei + 2) = some (natVal 1)) :
    (Schritt (sqrtPrefix ein frei ++ rest))^[14] (some q) =
      some (frameA6 q frei s) := by
  have h55 := kette5 ein frei s n q rest hqpc hqs hq1
  have hlen : (sqrtPrefix ein frei).length = 25 := sqrtPrefixLaenge _ _
  have hpcA5 : (frameA5 q frei s).pc = 13 := rfl
  have hq : (frameA5 q frei s).temp (frei + 3) = some (Ganzzahl.pack ⟨_, _,
      Arith.auswerten .mul
        (Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int)))
        (Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int)))⟩) :=
    updateHit _ _ _
  have g13 : ((sqrtPrefix ein frei ++ rest)[13]?) = some (.binden nameX (frei + 3)) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have g14 : ((sqrtPrefix ein frei ++ rest)[13 + 1]?) = some (.lesen (frei + 5) 0) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have g15 : ((sqrtPrefix ein frei ++ rest)[13 + 2]?) = some (.blockEnde 1) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have e1 := laufKopie _ _ 13 (frei + 5) (frei + 3) _ hpcA5 hq g13 g14 g15
  have e : (Schritt (sqrtPrefix ein frei ++ rest))^[14] (some q) =
      (Schritt (sqrtPrefix ein frei ++ rest))^[3]
        ((Schritt (sqrtPrefix ein frei ++ rest))^[11] (some q)) := by
    rw [show (14 : Nat) = 3 + 11 from rfl, Function.iterate_add_apply]
  rw [e, h55]
  simp only [frameA6] at *
  exact e1

/-- Copy the input into the comparison cell. -/
theorem kette7 (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqs : q.temp (frei + 0) = some (natVal s))
    (hq1 : q.temp (frei + 2) = some (natVal 1))
    (hqe : q.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (sqrtPrefix ein frei ++ rest))^[17] (some q) =
      some (frameA7 q frei s n) := by
  have h66 := kette6 ein frei s n q rest hqpc hqs hq1
  have hlen : (sqrtPrefix ein frei).length = 25 := sqrtPrefixLaenge _ _
  have hpcA6 : (frameA6 q frei s).pc = 16 := rfl
  have hq : (frameA6 q frei s).temp ein = some (natVal n) := by
    show Function.update _ (frei + 5) _ ein = _
    rw [updateMiss _ _ _ _ (by omega)]
    show Function.update _ (frei + 3) _ ein = _
    rw [updateMiss _ _ _ _ (by omega)]
    show Function.update _ (frei + 4) _ ein = _
    rw [updateMiss _ _ _ _ (by omega)]
    show Function.update _ (frei + 3) _ ein = _
    rw [updateMiss _ _ _ _ (by omega)]
    show Function.update _ (frei + 1) _ ein = _
    rw [updateMiss _ _ _ _ (by omega)]
    show Function.update _ (frei + 1) _ ein = _
    rw [updateMiss _ _ _ _ (by omega)]
    exact hqe
  have g16 : ((sqrtPrefix ein frei ++ rest)[16]?) = some (.binden nameX ein) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have g17 : ((sqrtPrefix ein frei ++ rest)[16 + 1]?) = some (.lesen (frei + 6) 0) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have g18 : ((sqrtPrefix ein frei ++ rest)[16 + 2]?) = some (.blockEnde 1) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have e1 := laufKopie _ _ 16 (frei + 6) ein _ hpcA6 hq g16 g17 g18
  have e : (Schritt (sqrtPrefix ein frei ++ rest))^[17] (some q) =
      (Schritt (sqrtPrefix ein frei ++ rest))^[3]
        ((Schritt (sqrtPrefix ein frei ++ rest))^[14] (some q)) := by
    rw [show (17 : Nat) = 3 + 14 from rfl, Function.iterate_add_apply]
  rw [e, h66]
  simp only [frameA7] at *
  exact e1

/-- Compare the squared successor with the input. -/
theorem kette8 (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqs : q.temp (frei + 0) = some (natVal s))
    (hq1 : q.temp (frei + 2) = some (natVal 1))
    (hqe : q.temp ein = some (natVal n)) (hein : ein < frei) :
    (Schritt (sqrtPrefix ein frei ++ rest))^[18] (some q) =
      some (frameA8 q frei s n) := by
  have h77 := kette7 ein frei s n q rest hqpc hqs hq1 hqe hein
  have hlen : (sqrtPrefix ein frei).length = 25 := sqrtPrefixLaenge _ _
  have hpcA7 : (frameA7 q frei s n).pc = 19 := rfl
  have ha7 : (frameA7 q frei s n).zahl (frei + 5) = some ⟨_, _,
      Arith.auswerten .mul
        (Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int)))
        (Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int)))⟩ := by
    have hA7t : (frameA7 q frei s n).temp (frei + 5) = some (Ganzzahl.pack ⟨_, _,
        Arith.auswerten .mul
          (Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int)))
          (Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int)))⟩) := by
      show Function.update _ (frei + 6) _ (frei + 5) = _
      rw [updateMiss _ _ _ _ (by omega)]
      exact updateHit _ _ _
    show (((frameA7 q frei s n).temp (frei + 5)).bind alsGanzzahl) = _
    rw [hA7t]
    rfl
  have hb7 : (frameA7 q frei s n).zahl (frei + 6) =
      some ⟨(n : Int), (n : Int), Zahl.literal (n : Int)⟩ := by
    show (((frameA7 q frei s n).temp (frei + 6)).bind alsGanzzahl) = _
    rw [show (frameA7 q frei s n).temp (frei + 6) = some (natVal n) from updateHit _ _ _]
    rfl
  have g19 : ((sqrtPrefix ein frei ++ rest)[19]?) = some (.vergleichen .le (frei + 5)) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have e1 : (Schritt (sqrtPrefix ein frei ++ rest))^[1] (some (frameA7 q frei s n)) =
      some (frameA8 q frei s n) :=
    schrittVergleichen _ _ _ _ .le _ _ hpcA7 ha7 hb7 g19
  have e : (Schritt (sqrtPrefix ein frei ++ rest))^[18] (some q) =
      (Schritt (sqrtPrefix ein frei ++ rest))^[1]
        ((Schritt (sqrtPrefix ein frei ++ rest))^[17] (some q)) := by
    rw [show (18 : Nat) = 1 + 17 from rfl, Function.iterate_add_apply]
  rw [e, h77, e1]

/-- The comparison is true: the successor square still fits, so continue. -/
theorem kette9w (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqs : q.temp (frei + 0) = some (natVal s))
    (hq1 : q.temp (frei + 2) = some (natVal 1))
    (hqe : q.temp ein = some (natVal n)) (hein : ein < frei)
    (h : (s + 1) * (s + 1) ≤ n) :
    (Schritt (sqrtPrefix ein frei ++ rest))^[19] (some q) =
      some (frameA9w q frei s n) := by
  have h88 := kette8 ein frei s n q rest hqpc hqs hq1 hqe hein
  have hlen : (sqrtPrefix ein frei).length = 25 := sqrtPrefixLaenge _ _
  have hpcA8 : (frameA8 q frei s n).pc = 20 := rfl
  have hbool : cmpBool s n = true := by
    simp only [cmpBool, mulWert, Compare.eval]
    exact decide_eq_true ((intSqSuccLe s n).mpr h)
  have htemp : (frameA8 q frei s n).temp (frei + 5) = some ⟨.bool, cmpBool s n⟩ :=
    updateHit _ _ _
  have g20 : ((sqrtPrefix ein frei ++ rest)[20]?) =
      some (.springeWenn (frei + 5) false 5) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have e1 : (Schritt (sqrtPrefix ein frei ++ rest))^[1] (some (frameA8 q frei s n)) =
      some (frameA9w q frei s n) :=
    schrittSpringeWennFalsch _ _ _ _ _ _ _ hpcA8 htemp
      (by rw [hbool]; decide) g20
  have e : (Schritt (sqrtPrefix ein frei ++ rest))^[19] (some q) =
      (Schritt (sqrtPrefix ein frei ++ rest))^[1]
        ((Schritt (sqrtPrefix ein frei ++ rest))^[18] (some q)) := by
    rw [show (19 : Nat) = 1 + 18 from rfl, Function.iterate_add_apply]
  rw [e, h88, e1]

/-- The comparison is false: the successor square exceeds the input, so exit. -/
theorem kette9e (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqs : q.temp (frei + 0) = some (natVal s))
    (hq1 : q.temp (frei + 2) = some (natVal 1))
    (hqe : q.temp ein = some (natVal n)) (hein : ein < frei)
    (h : ¬ ((s + 1) * (s + 1) ≤ n)) :
    (Schritt (sqrtPrefix ein frei ++ rest))^[19] (some q) =
      some (frameA9e q frei s n) := by
  have h88 := kette8 ein frei s n q rest hqpc hqs hq1 hqe hein
  have hlen : (sqrtPrefix ein frei).length = 25 := sqrtPrefixLaenge _ _
  have hpcA8 : (frameA8 q frei s n).pc = 20 := rfl
  have hbool : cmpBool s n = false := by
    have hle : ¬ (((s : Int) + ((1 : Nat) : Int)) * ((s : Int) + ((1 : Nat) : Int)) ≤ (n : Int)) :=
      fun hle => h ((intSqSuccLe s n).mp hle)
    simp only [cmpBool, mulWert, Compare.eval]
    exact decide_eq_false hle
  have htemp : (frameA8 q frei s n).temp (frei + 5) = some ⟨.bool, cmpBool s n⟩ :=
    updateHit _ _ _
  have g20 : ((sqrtPrefix ein frei ++ rest)[20]?) =
      some (.springeWenn (frei + 5) false 5) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have e1 : (Schritt (sqrtPrefix ein frei ++ rest))^[1] (some (frameA8 q frei s n)) =
      some (frameA9e q frei s n) :=
    schrittSpringeWennWahr _ _ _ _ _ _ _ hpcA8 htemp hbool g20
  have e : (Schritt (sqrtPrefix ein frei ++ rest))^[19] (some q) =
      (Schritt (sqrtPrefix ein frei ++ rest))^[1]
        ((Schritt (sqrtPrefix ein frei ++ rest))^[18] (some q)) := by
    rw [show (19 : Nat) = 1 + 18 from rfl, Function.iterate_add_apply]
  rw [e, h88, e1]

/-- Write the successor back into the counter. -/
theorem kette10w (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqs : q.temp (frei + 0) = some (natVal s))
    (hq1 : q.temp (frei + 2) = some (natVal 1))
    (hqe : q.temp ein = some (natVal n)) (hein : ein < frei)
    (h : (s + 1) * (s + 1) ≤ n) :
    (Schritt (sqrtPrefix ein frei ++ rest))^[22] (some q) =
      some (frameA10 q frei s n) := by
  have h99 := kette9w ein frei s n q rest hqpc hqs hq1 hqe hein h
  have hlen : (sqrtPrefix ein frei).length = 25 := sqrtPrefixLaenge _ _
  have hpcA9 : (frameA9w q frei s n).pc = 21 := rfl
  have hq : (frameA9w q frei s n).temp (frei + 1) = some (natVal (s + 1)) := by
    have hA : (frameA9w q frei s n).temp (frei + 1) =
        (frameA2 q frei s).temp (frei + 1) := by
      show Function.update _ (frei + 5) _ (frei + 1) = _
      rw [updateMiss _ _ _ _ (by omega)]
      show Function.update _ (frei + 6) _ (frei + 1) = _
      rw [updateMiss _ _ _ _ (by omega)]
      show Function.update _ (frei + 5) _ (frei + 1) = _
      rw [updateMiss _ _ _ _ (by omega)]
      show Function.update _ (frei + 3) _ (frei + 1) = _
      rw [updateMiss _ _ _ _ (by omega)]
      show Function.update _ (frei + 4) _ (frei + 1) = _
      rw [updateMiss _ _ _ _ (by omega)]
      show Function.update _ (frei + 3) _ (frei + 1) = _
      rw [updateMiss _ _ _ _ (by omega)]
    rw [hA]
    show Function.update _ (frei + 1) _ (frei + 1) = _
    rw [updateHit]
    exact congrArg some (packAddSucc s)
  have g21 : ((sqrtPrefix ein frei ++ rest)[21]?) = some (.binden nameX (frei + 1)) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have g22 : ((sqrtPrefix ein frei ++ rest)[21 + 1]?) = some (.lesen (frei + 0) 0) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have g23 : ((sqrtPrefix ein frei ++ rest)[21 + 2]?) = some (.blockEnde 1) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have e1 := laufKopie _ _ 21 (frei + 0) (frei + 1) _ hpcA9 hq g21 g22 g23
  have e : (Schritt (sqrtPrefix ein frei ++ rest))^[22] (some q) =
      (Schritt (sqrtPrefix ein frei ++ rest))^[3]
        ((Schritt (sqrtPrefix ein frei ++ rest))^[19] (some q)) := by
    rw [show (22 : Nat) = 3 + 19 from rfl, Function.iterate_add_apply]
  rw [e, h99]
  simp only [frameA10] at *
  exact e1

/-- Jump back to the loop top with the increased counter. -/
theorem kette11w (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqs : q.temp (frei + 0) = some (natVal s))
    (hq1 : q.temp (frei + 2) = some (natVal 1))
    (hqe : q.temp ein = some (natVal n)) (hein : ein < frei)
    (h : (s + 1) * (s + 1) ≤ n) :
    (Schritt (sqrtPrefix ein frei ++ rest))^[23] (some q) =
      some (frameA11 q frei s n) := by
  have h1010 := kette10w ein frei s n q rest hqpc hqs hq1 hqe hein h
  have hlen : (sqrtPrefix ein frei).length = 25 := sqrtPrefixLaenge _ _
  have hpcA10 : (frameA10 q frei s n).pc = 24 := rfl
  have g24 : ((sqrtPrefix ein frei ++ rest)[24]?) = some (.zurueckSprung 22) := by
    rw [getAnhangLinks _ _ _ (by omega)]
    rfl
  have e1 : (Schritt (sqrtPrefix ein frei ++ rest))^[1] (some (frameA10 q frei s n)) =
      some (frameA11 q frei s n) :=
    schrittZurueck _ _ _ _ hpcA10 g24
  have e : (Schritt (sqrtPrefix ein frei ++ rest))^[23] (some q) =
      (Schritt (sqrtPrefix ein frei ++ rest))^[1]
        ((Schritt (sqrtPrefix ein frei ++ rest))^[22] (some q)) := by
    rw [show (23 : Nat) = 1 + 22 from rfl, Function.iterate_add_apply]
  rw [e, h1010, e1]


end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
