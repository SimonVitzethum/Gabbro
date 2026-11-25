module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarFrame

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

theorem pb1Lauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a : Nat)
    (hpc : r.pc = 0) (ha : r.temp aSlot = some (natVal a)) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[3] (some r) = some (pb1 r a frei) := by
  have g0 : (paarBerechnung aSlot bSlot aus frei)[0]? = some (.binden nameX aSlot) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g1 : (paarBerechnung aSlot bSlot aus frei)[1]? = some (.lesen frei 0) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g2 : (paarBerechnung aSlot bSlot aus frei)[2]? = some (.blockEnde 1) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := laufKopie _ r 0 frei aSlot (some (natVal a)) hpc ha g0 g1 g2
  rw [e]
  rfl

theorem pb2Lauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat)
    (ha : r.temp aSlot = some (natVal a)) (hb : r.temp bSlot = some (natVal b))
    (hbf : bSlot ≠ frei) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[3] (some (pb1 r a frei)) = some (pb2 r a b frei) := by
  have ht : (pb1 r a frei).temp bSlot = some (natVal b) := by
    show Function.update r.temp frei (some (natVal a)) bSlot = _
    rw [updateMiss _ _ _ _ hbf]
    exact hb
  have g0 : (paarBerechnung aSlot bSlot aus frei)[3]? = some (.binden nameX bSlot) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g1 : (paarBerechnung aSlot bSlot aus frei)[4]? = some (.lesen (frei + 1) 0) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g2 : (paarBerechnung aSlot bSlot aus frei)[5]? = some (.blockEnde 1) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := laufKopie _ (pb1 r a frei) 3 (frei + 1) bSlot (some (natVal b)) rfl ht g0 g1 g2
  rw [e]
  rfl

theorem pb3Lauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat)
    (ha : r.temp aSlot = some (natVal a)) (hb : r.temp bSlot = some (natVal b))
    (haf : aSlot ≠ frei) (haf1 : aSlot ≠ frei + 1) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[3] (some (pb2 r a b frei)) = some (pb3 r a b frei) := by
  have ht : (pb2 r a b frei).temp aSlot = some (natVal a) := by
    show Function.update (pb1 r a frei).temp (frei + 1) (some (natVal b)) aSlot = _
    rw [updateMiss _ _ _ _ haf1]
    show Function.update r.temp frei (some (natVal a)) aSlot = _
    rw [updateMiss _ _ _ _ haf]
    exact ha
  have g0 : (paarBerechnung aSlot bSlot aus frei)[6]? = some (.binden nameX aSlot) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g1 : (paarBerechnung aSlot bSlot aus frei)[7]? = some (.lesen (frei + 2) 0) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g2 : (paarBerechnung aSlot bSlot aus frei)[8]? = some (.blockEnde 1) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := laufKopie _ (pb2 r a b frei) 6 (frei + 2) aSlot (some (natVal a)) rfl ht g0 g1 g2
  rw [e]
  rfl

theorem pb4Lauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat)
    (hb : r.temp bSlot = some (natVal b))
    (hbf : bSlot ≠ frei) (hbf1 : bSlot ≠ frei + 1) (hbf2 : bSlot ≠ frei + 2) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[3] (some (pb3 r a b frei)) = some (pb4 r a b frei) := by
  have ht : (pb3 r a b frei).temp bSlot = some (natVal b) := by
    show Function.update (pb2 r a b frei).temp (frei + 2) (some (natVal a)) bSlot = _
    rw [updateMiss _ _ _ _ hbf2]
    show Function.update (pb1 r a frei).temp (frei + 1) (some (natVal b)) bSlot = _
    rw [updateMiss _ _ _ _ hbf1]
    show Function.update r.temp frei (some (natVal a)) bSlot = _
    rw [updateMiss _ _ _ _ hbf]
    exact hb
  have g0 : (paarBerechnung aSlot bSlot aus frei)[9]? = some (.binden nameX bSlot) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g1 : (paarBerechnung aSlot bSlot aus frei)[10]? = some (.lesen (frei + 3) 0) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g2 : (paarBerechnung aSlot bSlot aus frei)[11]? = some (.blockEnde 1) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := laufKopie _ (pb3 r a b frei) 9 (frei + 3) bSlot (some (natVal b)) rfl ht g0 g1 g2
  rw [e]
  rfl

set_option maxHeartbeats 400000 in
theorem pb5Lauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[1] (some (pb4 r a b frei)) = some (pb5 r a b frei) := by
  have hx : (pb4 r a b frei).temp frei = some (natVal a) := by
    show Function.update (pb3 r a b frei).temp (frei + 3) (some (natVal b)) frei = _
    rw [updateMiss _ _ _ _ (by omega : frei ≠ frei + 3)]
    show Function.update (pb2 r a b frei).temp (frei + 2) (some (natVal a)) frei = _
    rw [updateMiss _ _ _ _ (by omega : frei ≠ frei + 2)]
    show Function.update (pb1 r a frei).temp (frei + 1) (some (natVal b)) frei = _
    rw [updateMiss _ _ _ _ (by omega : frei ≠ frei + 1)]
    show Function.update r.temp frei (some (natVal a)) frei = _
    exact updateHit _ _ _
  have hy : (pb4 r a b frei).temp (frei + 1) = some (natVal b) := by
    show Function.update (pb3 r a b frei).temp (frei + 3) (some (natVal b)) (frei + 1) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (1 : Nat) ≠ 3))]
    show Function.update (pb2 r a b frei).temp (frei + 2) (some (natVal a)) (frei + 1) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (1 : Nat) ≠ 2))]
    show Function.update (pb1 r a frei).temp (frei + 1) (some (natVal b)) (frei + 1) = _
    exact updateHit _ _ _
  have g : (paarBerechnung aSlot bSlot aus frei)[12]? = some (.vergleichen .lt frei) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := schrittVergleichNat _ (pb4 r a b frei) 12 frei a b rfl hx hy g
  exact e

set_option maxHeartbeats 400000 in
theorem pb6wLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) (hab : a < b) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[1] (some (pb5 r a b frei)) = some (pb6w r a b frei) := by
  have hw : Compare.eval .lt (a : Int) (b : Int) = true := (vergleichLtNat a b).mpr hab
  have ht : (pb5 r a b frei).temp frei = some ⟨.bool, true⟩ := by
    show Function.update (pb4 r a b frei).temp frei (some ⟨.bool, Compare.eval .lt (a : Int) (b : Int)⟩) frei = _
    rw [updateHit]
    rw [hw]
  have g : (paarBerechnung aSlot bSlot aus frei)[13]? = some (.springeWenn frei true 17) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := schrittSpringeWennWahr _ (pb5 r a b frei) 13 frei true true 17 rfl ht rfl g
  exact e

set_option maxHeartbeats 400000 in
theorem pb6fLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) (hab : ¬ a < b) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[1] (some (pb5 r a b frei)) = some (pb6f r a b frei) := by
  have hw : Compare.eval .lt (a : Int) (b : Int) ≠ true := by
    intro h
    exact hab ((vergleichLtNat a b).mp h)
  have ht : (pb5 r a b frei).temp frei = some ⟨.bool, false⟩ := by
    show Function.update (pb4 r a b frei).temp frei (some ⟨.bool, Compare.eval .lt (a : Int) (b : Int)⟩) frei = _
    rw [updateHit]
    cases h : Compare.eval .lt (a : Int) (b : Int) with
    | true => exact (hw h).elim
    | false => rfl
  have g : (paarBerechnung aSlot bSlot aus frei)[13]? = some (.springeWenn frei true 17) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := schrittSpringeWennFalsch _ (pb5 r a b frei) 13 frei true false 17 rfl ht (by decide : false ≠ true) g
  exact e

theorem pb7wLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[3] (some (pb6w r a b frei)) = some (pb7w r a b frei) := by
  have ht : (pb6w r a b frei).temp (frei + 3) = some (natVal b) := by
    show (pb5 r a b frei).temp (frei + 3) = _
    show Function.update (pb4 r a b frei).temp frei (some ⟨.bool, Compare.eval .lt (a : Int) (b : Int)⟩) (frei + 3) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 3 ≠ frei)]
    show Function.update (pb3 r a b frei).temp (frei + 3) (some (natVal b)) (frei + 3) = _
    exact updateHit _ _ _
  have g0 : (paarBerechnung aSlot bSlot aus frei)[30]? = some (.binden nameX (frei + 3)) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g1 : (paarBerechnung aSlot bSlot aus frei)[31]? = some (.lesen (frei + 4) 0) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g2 : (paarBerechnung aSlot bSlot aus frei)[32]? = some (.blockEnde 1) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := laufKopie _ (pb6w r a b frei) 30 (frei + 4) (frei + 3) (some (natVal b)) rfl ht g0 g1 g2
  rw [e]
  rfl

theorem pb8wLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[3] (some (pb7w r a b frei)) = some (pb8w r a b frei) := by
  have ht : (pb7w r a b frei).temp (frei + 3) = some (natVal b) := by
    show Function.update (pb6w r a b frei).temp (frei + 4) (some (natVal b)) (frei + 3) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (3 : Nat) ≠ 4))]
    show (pb5 r a b frei).temp (frei + 3) = _
    show Function.update (pb4 r a b frei).temp frei (some ⟨.bool, Compare.eval .lt (a : Int) (b : Int)⟩) (frei + 3) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 3 ≠ frei)]
    show Function.update (pb3 r a b frei).temp (frei + 3) (some (natVal b)) (frei + 3) = _
    exact updateHit _ _ _
  have g0 : (paarBerechnung aSlot bSlot aus frei)[33]? = some (.binden nameX (frei + 3)) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g1 : (paarBerechnung aSlot bSlot aus frei)[34]? = some (.lesen (frei + 5) 0) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g2 : (paarBerechnung aSlot bSlot aus frei)[35]? = some (.blockEnde 1) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := laufKopie _ (pb7w r a b frei) 33 (frei + 5) (frei + 3) (some (natVal b)) rfl ht g0 g1 g2
  rw [e]
  rfl

set_option maxHeartbeats 400000 in
theorem pb9wLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[1] (some (pb8w r a b frei)) = some (pb9w r a b frei) := by
  have hx : (pb8w r a b frei).temp (frei + 4) = some (natVal b) := by
    show Function.update (pb7w r a b frei).temp (frei + 5) (some (natVal b)) (frei + 4) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (4 : Nat) ≠ 5))]
    show Function.update (pb6w r a b frei).temp (frei + 4) (some (natVal b)) (frei + 4) = _
    exact updateHit _ _ _
  have hy : (pb8w r a b frei).temp (frei + 5) = some (natVal b) := by
    show Function.update (pb7w r a b frei).temp (frei + 5) (some (natVal b)) (frei + 5) = _
    exact updateHit _ _ _
  have g : (paarBerechnung aSlot bSlot aus frei)[36]? = some (.binaer .mul (frei + 4)) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := schrittMulNat _ (pb8w r a b frei) 36 (frei + 4) b b rfl hx hy g
  exact e

theorem pb10wLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat)
    (h2a : frei + 2 ≠ frei + 4) (h2a5 : frei + 2 ≠ frei + 5) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[3] (some (pb9w r a b frei)) = some (pb10w r a b frei) := by
  have ht : (pb9w r a b frei).temp (frei + 2) = some (natVal a) := by
    show Function.update (pb8w r a b frei).temp (frei + 4) (some (natVal (b * b))) (frei + 2) = _
    rw [updateMiss _ _ _ _ h2a]
    show Function.update (pb7w r a b frei).temp (frei + 5) (some (natVal b)) (frei + 2) = _
    rw [updateMiss _ _ _ _ h2a5]
    show Function.update (pb6w r a b frei).temp (frei + 4) (some (natVal b)) (frei + 2) = _
    rw [updateMiss _ _ _ _ h2a]
    show (pb5 r a b frei).temp (frei + 2) = _
    show Function.update (pb4 r a b frei).temp frei (some ⟨.bool, Compare.eval .lt (a : Int) (b : Int)⟩) (frei + 2) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 2 ≠ frei)]
    show Function.update (pb3 r a b frei).temp (frei + 3) (some (natVal b)) (frei + 2) = _
    rw [updateMiss _ _ _ _ (by omega : frei + 2 ≠ frei + 3)]
    show Function.update (pb2 r a b frei).temp (frei + 2) (some (natVal a)) (frei + 2) = _
    exact updateHit _ _ _
  have g0 : (paarBerechnung aSlot bSlot aus frei)[37]? = some (.binden nameX (frei + 2)) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g1 : (paarBerechnung aSlot bSlot aus frei)[38]? = some (.lesen (frei + 5) 0) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g2 : (paarBerechnung aSlot bSlot aus frei)[39]? = some (.blockEnde 1) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := laufKopie _ (pb9w r a b frei) 37 (frei + 5) (frei + 2) (some (natVal a)) rfl ht g0 g1 g2
  rw [e]
  rfl

set_option maxHeartbeats 400000 in
theorem pb11wLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[1] (some (pb10w r a b frei)) = some (pb11w r a b frei) := by
  have hx : (pb10w r a b frei).temp (frei + 4) = some (natVal (b * b)) := by
    show Function.update (pb9w r a b frei).temp (frei + 5) (some (natVal a)) (frei + 4) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (4 : Nat) ≠ 5))]
    show Function.update (pb8w r a b frei).temp (frei + 4) (some (natVal (b * b))) (frei + 4) = _
    exact updateHit _ _ _
  have hy : (pb10w r a b frei).temp (frei + 5) = some (natVal a) := by
    show Function.update (pb9w r a b frei).temp (frei + 5) (some (natVal a)) (frei + 5) = _
    exact updateHit _ _ _
  have g : (paarBerechnung aSlot bSlot aus frei)[40]? = some (.binaer .add (frei + 4)) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := schrittAddNat _ (pb10w r a b frei) 40 (frei + 4) (b * b) a rfl hx hy g
  exact e

theorem pb12wLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat)
    (haus4 : aus ≠ frei + 4) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[3] (some (pb11w r a b frei)) = some (pb12w r a b aus frei) := by
  have ht : (pb11w r a b frei).temp (frei + 4) = some (natVal (b * b + a)) := by
    show Function.update (pb10w r a b frei).temp (frei + 4) (some (natVal (b * b + a))) (frei + 4) = _
    exact updateHit _ _ _
  have g0 : (paarBerechnung aSlot bSlot aus frei)[41]? = some (.binden nameX (frei + 4)) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g1 : (paarBerechnung aSlot bSlot aus frei)[42]? = some (.lesen aus 0) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have g2 : (paarBerechnung aSlot bSlot aus frei)[43]? = some (.blockEnde 1) := by
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, Nat.add_zero]
  have e := laufKopie _ (pb11w r a b frei) 41 aus (frei + 4) (some (natVal (b * b + a))) rfl ht g0 g1 g2
  rw [e]
  rfl

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
