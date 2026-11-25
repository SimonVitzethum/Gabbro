module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarLauf
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Paar

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

theorem paarVorwaerts (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat)
    (hpc : r.pc = 0) (ha : r.temp aSlot = some (natVal a))
    (hb : r.temp bSlot = some (natVal b))
    (haF : aSlot < frei) (hbF : bSlot < frei) :
    ∃ k rEnd, (Schritt (paarBerechnung aSlot bSlot aus frei))^[k] (some r) = some rEnd ∧
      rEnd.pc = 44 ∧ rEnd.temp aus = some (natVal (Nat.pair a b)) ∧
      (∀ s, s < frei → s ≠ aus → rEnd.temp s = r.temp s) ∧
      rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp := by
  by_cases hab : a < b
  · refine ⟨28, pb12w r a b aus frei, paarVorwaertsWahr aSlot bSlot aus frei r a b hpc ha hb haF hbF hab, rfl, ?_, ?_, rfl, rfl, rfl⟩
    · show (pb12w r a b aus frei).temp aus = some (natVal (Nat.pair a b))
      rw [natPairFormel, if_pos hab]
      show Function.update (pb11w r a b frei).temp aus (some (natVal (b * b + a))) aus = _
      exact updateHit _ _ _
    · exact pb12wPres r a b aus frei
  · refine ⟨30, pb14f r a b aus frei, paarVorwaertsFalsch aSlot bSlot aus frei r a b hpc ha hb haF hbF hab, rfl, ?_, ?_, rfl, rfl, rfl⟩
    · show (pb14f r a b aus frei).temp aus = some (natVal (Nat.pair a b))
      rw [natPairFormel, if_neg hab]
      show (pb13f r a b aus frei).temp aus = _
      show Function.update (pb12f r a b frei).temp aus (some (natVal (a * a + a + b))) aus = _
      exact updateHit _ _ _
    · exact pb14fPres r a b aus frei

theorem paarRueck (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat)
    (hpc : r.pc = 0) (ha : r.temp aSlot = some (natVal a))
    (hb : r.temp bSlot = some (natVal b))
    (haF : aSlot < frei) (hbF : bSlot < frei)
    (k : Nat) (rEnd : Rahmen)
    (hk : (Schritt (paarBerechnung aSlot bSlot aus frei))^[k] (some r) = some rEnd)
    (hpcEnd : rEnd.pc = 44) :
    rEnd.temp aus = some (natVal (Nat.pair a b)) ∧
    (∀ s, s < frei → s ≠ aus → rEnd.temp s = r.temp s) ∧
    rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp := by
  by_cases hab : a < b
  · have hF := paarVorwaertsWahr aSlot bSlot aus frei r a b hpc ha hb haF hbF hab
    have hpcF : (pb12w r a b aus frei).pc = (paarBerechnung aSlot bSlot aus frei).length := by
      rw [paarBerechnungLaenge]
      rfl
    have hpcEnd' : rEnd.pc = (paarBerechnung aSlot bSlot aus frei).length := by
      rw [hpcEnd, paarBerechnungLaenge]
    have hkEq : k = 28 := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact laufStirbtNach (paarBerechnung aSlot bSlot aus frei) r k 28 rEnd (pb12w r a b aus frei) hk hpcEnd' hF hlt
      · exact laufStirbtNach (paarBerechnung aSlot bSlot aus frei) r 28 k (pb12w r a b aus frei) rEnd hF hpcF hk hgt
    have hEq : rEnd = pb12w r a b aus frei := by
      subst k
      exact Option.some.inj (hk.symm.trans hF)
    rw [hEq]
    refine ⟨?_, pb12wPres r a b aus frei, rfl, rfl, rfl⟩
    rw [natPairFormel, if_pos hab]
    show Function.update (pb11w r a b frei).temp aus (some (natVal (b * b + a))) aus = _
    exact updateHit _ _ _
  · have hF := paarVorwaertsFalsch aSlot bSlot aus frei r a b hpc ha hb haF hbF hab
    have hpcF : (pb14f r a b aus frei).pc = (paarBerechnung aSlot bSlot aus frei).length := by
      rw [paarBerechnungLaenge]
      rfl
    have hpcEnd' : rEnd.pc = (paarBerechnung aSlot bSlot aus frei).length := by
      rw [hpcEnd, paarBerechnungLaenge]
    have hkEq : k = 30 := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact laufStirbtNach (paarBerechnung aSlot bSlot aus frei) r k 30 rEnd (pb14f r a b aus frei) hk hpcEnd' hF hlt
      · exact laufStirbtNach (paarBerechnung aSlot bSlot aus frei) r 30 k (pb14f r a b aus frei) rEnd hF hpcF hk hgt
    have hEq : rEnd = pb14f r a b aus frei := by
      subst k
      exact Option.some.inj (hk.symm.trans hF)
    rw [hEq]
    refine ⟨?_, pb14fPres r a b aus frei, rfl, rfl, rfl⟩
    rw [natPairFormel, if_neg hab]
    show (pb13f r a b aus frei).temp aus = _
    show Function.update (pb12f r a b frei).temp aus (some (natVal (a * a + a + b))) aus = _
    exact updateHit _ _ _

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
