module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecSchleife

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The boolean written by the primitive-recursion comparison. -/
def precBool (s k : Nat) : Bool := Compare.eval .lt (s : Int) (k : Int)

theorem precBoolEq (s k : Nat) : precBool s k = decide (s < k) := by
  simp only [precBool, Compare.eval, Nat.cast_lt]

def precBoolWert (s k : Nat) : Dynamisch := ⟨.bool, precBool s k⟩

def precVergleichWert (s k : Nat) : Dynamisch :=
  ⟨Ty.bool, Compare.eval .lt (s : Int) (k : Int)⟩

/-- The comparison segment: copy the counter and the limit into the adjacent
    comparison slots, then compare. -/
theorem precCheckLauf (r : Rahmen) (frei s k : Nat)
    (hpc : r.pc = 0)
    (hs : r.temp (frei + 2) = some (natVal s))
    (hk : r.temp (frei + 1) = some (natVal k)) :
    ∃ rC, (Schritt (precCheck frei))^[7] (some r) = some rC ∧
      rC.pc = 7 ∧
      rC.temp (frei + 6) = some (precBoolWert s k) ∧
      rC.temp (frei + 7) = some (natVal k) ∧
      (∀ t, t < frei → rC.temp t = r.temp t) ∧
      rC.lokale = r.lokale ∧ rC.rueckgabe = r.rueckgabe ∧ rC.stopp = r.stopp := by
  have kk0 : (kopie (frei + 6) (frei + 2))[0]? = some (.binden nameX (frei + 2)) := by
    simp only [kopie, List.getElem?_cons_zero]
  have kk1 : (kopie (frei + 6) (frei + 2))[1]? = some (.lesen (frei + 6) 0) := by
    simp only [kopie, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have kk2 : (kopie (frei + 6) (frei + 2))[2]? = some (.blockEnde 1) := by
    simp only [kopie, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have kk3 : (kopie (frei + 7) (frei + 1))[0]? = some (.binden nameX (frei + 1)) := by
    simp only [kopie, List.getElem?_cons_zero]
  have kk4 : (kopie (frei + 7) (frei + 1))[1]? = some (.lesen (frei + 7) 0) := by
    simp only [kopie, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have kk5 : (kopie (frei + 7) (frei + 1))[2]? = some (.blockEnde 1) := by
    simp only [kopie, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hk1 : (kopie (frei + 6) (frei + 2)).length = 3 := kopieLaenge _ _
  have hlt6 (n : Nat) (h : n < 6) :
      n < (kopie (frei + 6) (frei + 2) ++ kopie (frei + 7) (frei + 1)).length := by
    simp only [List.length_append, kopieLaenge]
    omega
  have hge6 (n : Nat) (h : 6 ≤ n) :
      (kopie (frei + 6) (frei + 2) ++ kopie (frei + 7) (frei + 1)).length ≤ n := by
    simp only [List.length_append, kopieLaenge]
    omega
  have g0 : (precCheck frei)[0]? = some (.binden nameX (frei + 2)) := by
    unfold precCheck
    rw [List.getElem?_append_left (hlt6 0 (by omega))]
    rw [List.getElem?_append_left (by simp only [hk1]; omega)]
    exact kk0
  have g1 : (precCheck frei)[0 + 1]? = some (.lesen (frei + 6) 0) := by
    unfold precCheck
    rw [List.getElem?_append_left (hlt6 (0 + 1) (by omega))]
    rw [List.getElem?_append_left (by simp only [hk1]; omega)]
    simpa only [Nat.zero_add] using kk1
  have g2 : (precCheck frei)[0 + 2]? = some (.blockEnde 1) := by
    unfold precCheck
    rw [List.getElem?_append_left (hlt6 (0 + 2) (by omega))]
    rw [List.getElem?_append_left (by simp only [hk1]; omega)]
    simpa only [Nat.zero_add] using kk2
  have g3 : (precCheck frei)[3]? = some (.binden nameX (frei + 1)) := by
    unfold precCheck
    rw [List.getElem?_append_left (hlt6 3 (by omega))]
    rw [List.getElem?_append_right (by simp only [hk1]; omega)]
    rw [show 3 - (kopie (frei + 6) (frei + 2)).length = 0 by simp only [hk1]]
    exact kk3
  have g4 : (precCheck frei)[3 + 1]? = some (.lesen (frei + 7) 0) := by
    unfold precCheck
    rw [List.getElem?_append_left (hlt6 (3 + 1) (by omega))]
    rw [List.getElem?_append_right (by simp only [hk1]; omega)]
    rw [show 3 + 1 - (kopie (frei + 6) (frei + 2)).length = 1 by simp only [hk1]]
    exact kk4
  have g5 : (precCheck frei)[3 + 2]? = some (.blockEnde 1) := by
    unfold precCheck
    rw [List.getElem?_append_left (hlt6 (3 + 2) (by omega))]
    rw [List.getElem?_append_right (by simp only [hk1]; omega)]
    rw [show 3 + 2 - (kopie (frei + 6) (frei + 2)).length = 2 by simp only [hk1]]
    exact kk5
  have g6 : (precCheck frei)[6]? = some (.vergleichen .lt (frei + 6)) := by
    unfold precCheck
    rw [List.getElem?_append_right (hge6 6 (by omega))]
    rw [show (kopie (frei + 6) (frei + 2) ++ kopie (frei + 7) (frei + 1)).length = 6 by
      simp only [List.length_append, kopieLaenge]]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  let r1 : Rahmen := { r with pc := 3, temp := Function.update r.temp (frei + 6) (some (natVal s)) }
  have e1 : (Schritt (precCheck frei))^[3] (some r) = some r1 := by
    simpa only [r1, Nat.zero_add] using
      (laufKopie (precCheck frei) r 0 (frei + 6) (frei + 2) (some (natVal s)) hpc hs g0 g1 g2)
  have hr1k : r1.temp (frei + 1) = some (natVal k) := by
    show Function.update r.temp (frei + 6) (some (natVal s)) (frei + 1) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (1 : Nat) ≠ 6))]
    exact hk
  let r2 : Rahmen := { r1 with pc := 6, temp := Function.update r1.temp (frei + 7) (some (natVal k)) }
  have e2 : (Schritt (precCheck frei))^[3] (some r1) = some r2 := by
    have hpc1 : r1.pc = 3 := rfl
    simpa only [r2, Nat.reduceAdd] using
      (laufKopie (precCheck frei) r1 3 (frei + 7) (frei + 1) (some (natVal k)) hpc1 hr1k g3 g4 g5)
  have hr2s : r2.temp (frei + 6) = some (natVal s) := by
    show Function.update r1.temp (frei + 7) (some (natVal k)) (frei + 6) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (6 : Nat) ≠ 7))]
    show Function.update r.temp (frei + 6) (some (natVal s)) (frei + 6) = _
    exact updateHit _ _ _
  have hr2k : r2.temp (frei + 7) = some (natVal k) := by
    show Function.update r1.temp (frei + 7) (some (natVal k)) (frei + 7) = _
    exact updateHit _ _ _
  have hza : r2.zahl (frei + 6) = some ⟨(s : Int), (s : Int), Zahl.literal (s : Int)⟩ :=
    zahlOfNat _ _ _ hr2s
  have hzb : r2.zahl (frei + 7) = some ⟨(k : Int), (k : Int), Zahl.literal (k : Int)⟩ :=
    zahlOfNat _ _ _ hr2k
  have hpc2 : r2.pc = 6 := rfl
  let r3 : Rahmen := r2.schreibe (frei + 6) (some (precVergleichWert s k))
  have e3 : (Schritt (precCheck frei))^[1] (some r2) = some r3 := by
    simpa only [r3, Rahmen.schreibe, precVergleichWert, Zahl.literal, Function.iterate_one] using
      (schrittVergleichen (precCheck frei) r2 6 (frei + 6) .lt
        ⟨(s : Int), (s : Int), Zahl.literal (s : Int)⟩
        ⟨(k : Int), (k : Int), Zahl.literal (k : Int)⟩ hpc2 hza hzb g6)
  refine ⟨r3, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · have ec : (Schritt (precCheck frei))^[7] (some r) =
        (Schritt (precCheck frei))^[1]
          ((Schritt (precCheck frei))^[3]
            ((Schritt (precCheck frei))^[3] (some r))) := by
      rw [show (7 : Nat) = 1 + 3 + 3 by omega, Function.iterate_add_apply, Function.iterate_add_apply]
    rw [ec, e1, e2, e3]
  · show r2.pc + 1 = 7
    rw [hpc2]
  · change Function.update r2.temp (frei + 6) (some (precBoolWert s k)) (frei + 6) = _
    exact updateHit _ _ _
  · change Function.update r2.temp (frei + 6) (some (precBoolWert s k)) (frei + 7) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (7 : Nat) ≠ 6))]
    exact hr2k
  · intro t ht
    show Function.update r2.temp (frei + 6) (some (precBoolWert s k)) t = r.temp t
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
    show Function.update r1.temp (frei + 7) (some (natVal k)) t = r.temp t
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]
    show Function.update r.temp (frei + 6) (some (natVal s)) t = r.temp t
    rw [updateMiss _ _ _ _ (ltNeAdd ht)]

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
