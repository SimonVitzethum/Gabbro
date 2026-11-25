module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBeweise.PaarSegmente

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

theorem pb7fLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[3] (some (pb6f r a b frei)) = some (pb7f r a b frei) := by
  have ht : (pb6f r a b frei).temp (frei + 2) = some (natVal a) := by
    show Function.update (pb4 r a b frei).temp frei (some ⟨.bool, Compare.eval .lt (a : Int) (b : Int)⟩) (frei + 2) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 2 ≠ frei)]
    show Function.update (pb3 r a b frei).temp (frei + 3) (some (natVal b)) (frei + 2) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 2 ≠ frei + 3)]
    show Function.update (pb2 r a b frei).temp (frei + 2) (some (natVal a)) (frei + 2) = _
    exact updateHit _ _ _
  have g0 : (paarBerechnung aSlot bSlot aus frei)[14]? = some (.binden nameX (frei + 2)) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g1 : (paarBerechnung aSlot bSlot aus frei)[15]? = some (.lesen (frei + 4) 0) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g2 : (paarBerechnung aSlot bSlot aus frei)[16]? = some (.blockEnde 1) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := laufKopie _ (pb6f r a b frei) 14 (frei + 4) (frei + 2) (some (natVal a)) rfl ht g0 g1 g2
  rw [e]
  rfl

theorem pb8fLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[3] (some (pb7f r a b frei)) = some (pb8f r a b frei) := by
  have ht : (pb7f r a b frei).temp (frei + 2) = some (natVal a) := by
    show Function.update (pb6f r a b frei).temp (frei + 4) (some (natVal a)) (frei + 2) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 2 ≠ frei + 4)]
    show Function.update (pb4 r a b frei).temp frei (some ⟨.bool, Compare.eval .lt (a : Int) (b : Int)⟩) (frei + 2) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 2 ≠ frei)]
    show Function.update (pb3 r a b frei).temp (frei + 3) (some (natVal b)) (frei + 2) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 2 ≠ frei + 3)]
    show Function.update (pb2 r a b frei).temp (frei + 2) (some (natVal a)) (frei + 2) = _
    exact updateHit _ _ _
  have g0 : (paarBerechnung aSlot bSlot aus frei)[17]? = some (.binden nameX (frei + 2)) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g1 : (paarBerechnung aSlot bSlot aus frei)[18]? = some (.lesen (frei + 5) 0) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g2 : (paarBerechnung aSlot bSlot aus frei)[19]? = some (.blockEnde 1) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := laufKopie _ (pb7f r a b frei) 17 (frei + 5) (frei + 2) (some (natVal a)) rfl ht g0 g1 g2
  rw [e]
  rfl

theorem pb9fLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) :
    Schritt (paarBerechnung aSlot bSlot aus frei) (some (pb8f r a b frei)) = some (pb9f r a b frei) := by
  have hx : (pb8f r a b frei).temp (frei + 4) = some (natVal a) := by
    show Function.update (pb7f r a b frei).temp (frei + 5) (some (natVal a)) (frei + 4) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 4 ≠ frei + 5)]
    show Function.update (pb6f r a b frei).temp (frei + 4) (some (natVal a)) (frei + 4) = _
    exact updateHit _ _ _
  have hy : (pb8f r a b frei).temp (frei + 5) = some (natVal a) := by
    show Function.update (pb7f r a b frei).temp (frei + 5) (some (natVal a)) (frei + 5) = _
    exact updateHit _ _ _
  have g : (paarBerechnung aSlot bSlot aus frei)[20]? = some (.binaer .mul (frei + 4)) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := schrittMulNat _ (pb8f r a b frei) 20 (frei + 4) a a rfl hx hy g
  exact e

theorem pb10fLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) :
    Schritt (paarBerechnung aSlot bSlot aus frei) (some (pb9f r a b frei)) = some (pb10f r a b frei) := by
  have hx : (pb9f r a b frei).temp (frei + 4) = some (natVal (a * a)) := by
    show Function.update (pb8f r a b frei).temp (frei + 4) (some (natVal (a * a))) (frei + 4) = _
    exact updateHit _ _ _
  have hy : (pb9f r a b frei).temp (frei + 5) = some (natVal a) := by
    show Function.update (pb8f r a b frei).temp (frei + 4) (some (natVal (a * a))) (frei + 5) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 5 ≠ frei + 4)]
    show Function.update (pb7f r a b frei).temp (frei + 5) (some (natVal a)) (frei + 5) = _
    exact updateHit _ _ _
  have g : (paarBerechnung aSlot bSlot aus frei)[21]? = some (.binaer .add (frei + 4)) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := schrittAddNat _ (pb9f r a b frei) 21 (frei + 4) (a * a) a rfl hx hy g
  exact e

theorem pb11fLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[3] (some (pb10f r a b frei)) = some (pb11f r a b frei) := by
  have ht : (pb10f r a b frei).temp (frei + 3) = some (natVal b) := by
    show Function.update (pb9f r a b frei).temp (frei + 4) (some (natVal (a * a + a))) (frei + 3) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 3 ≠ frei + 4)]
    show Function.update (pb8f r a b frei).temp (frei + 4) (some (natVal (a * a))) (frei + 3) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 3 ≠ frei + 4)]
    show Function.update (pb7f r a b frei).temp (frei + 5) (some (natVal a)) (frei + 3) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 3 ≠ frei + 5)]
    show Function.update (pb6f r a b frei).temp (frei + 4) (some (natVal a)) (frei + 3) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 3 ≠ frei + 4)]
    show Function.update (pb4 r a b frei).temp frei (some ⟨.bool, Compare.eval .lt (a : Int) (b : Int)⟩) (frei + 3) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 3 ≠ frei)]
    show Function.update (pb3 r a b frei).temp (frei + 3) (some (natVal b)) (frei + 3) = _
    exact updateHit _ _ _
  have g0 : (paarBerechnung aSlot bSlot aus frei)[22]? = some (.binden nameX (frei + 3)) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g1 : (paarBerechnung aSlot bSlot aus frei)[23]? = some (.lesen (frei + 5) 0) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g2 : (paarBerechnung aSlot bSlot aus frei)[24]? = some (.blockEnde 1) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := laufKopie _ (pb10f r a b frei) 22 (frei + 5) (frei + 3) (some (natVal b)) rfl ht g0 g1 g2
  rw [e]
  rfl

theorem pb12fLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) :
    Schritt (paarBerechnung aSlot bSlot aus frei) (some (pb11f r a b frei)) = some (pb12f r a b frei) := by
  have hx : (pb11f r a b frei).temp (frei + 4) = some (natVal (a * a + a)) := by
    show Function.update (pb10f r a b frei).temp (frei + 5) (some (natVal b)) (frei + 4) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 4 ≠ frei + 5)]
    show Function.update (pb9f r a b frei).temp (frei + 4) (some (natVal (a * a + a))) (frei + 4) = _
    exact updateHit _ _ _
  have hy : (pb11f r a b frei).temp (frei + 5) = some (natVal b) := by
    show Function.update (pb10f r a b frei).temp (frei + 5) (some (natVal b)) (frei + 5) = _
    exact updateHit _ _ _
  have g : (paarBerechnung aSlot bSlot aus frei)[25]? = some (.binaer .add (frei + 4)) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := schrittAddNat _ (pb11f r a b frei) 25 (frei + 4) (a * a + a) b rfl hx hy g
  exact e

theorem pb13fLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[3] (some (pb12f r a b frei)) = some (pb13f r a b aus frei) := by
  have ht : (pb12f r a b frei).temp (frei + 4) = some (natVal (a * a + a + b)) := by
    show Function.update (pb11f r a b frei).temp (frei + 4) (some (natVal (a * a + a + b))) (frei + 4) = _
    exact updateHit _ _ _
  have g0 : (paarBerechnung aSlot bSlot aus frei)[26]? = some (.binden nameX (frei + 4)) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g1 : (paarBerechnung aSlot bSlot aus frei)[27]? = some (.lesen aus 0) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g2 : (paarBerechnung aSlot bSlot aus frei)[28]? = some (.blockEnde 1) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := laufKopie _ (pb12f r a b frei) 26 aus (frei + 4) (some (natVal (a * a + a + b))) rfl ht g0 g1 g2
  rw [e]
  rfl

theorem pb14fLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) :
    Schritt (paarBerechnung aSlot bSlot aus frei) (some (pb13f r a b aus frei)) = some (pb14f r a b aus frei) := by
  have hpc : (pb13f r a b aus frei).pc = 29 := rfl
  have g : (paarBerechnung aSlot bSlot aus frei)[29]? = some (.springe 15) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := schrittSpringe _ (pb13f r a b aus frei) 29 15 hpc g
  exact e

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
