module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBerechnung

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Compute `Nat.pair a b` from two input slots into the output slot. The
    comparison and the two arithmetic branches use slots at or above `frei`, so
    every user slot below `frei` except the output is left untouched. The
    forward conditional selects the `b * b + a` branch; the fall-through
    computes `a * a + a + b`. -/
def paarBerechnung (aSlot bSlot aus frei : Nat) : List Befehl :=
  kopie (frei + 0) aSlot ++ kopie (frei + 1) bSlot ++
    kopie (frei + 2) aSlot ++ kopie (frei + 3) bSlot ++
    [.vergleichen .lt (frei + 0), .springeWenn (frei + 0) true 17] ++
    kopie (frei + 4) (frei + 2) ++ kopie (frei + 5) (frei + 2) ++
    [.binaer .mul (frei + 4), .binaer .add (frei + 4)] ++
    kopie (frei + 5) (frei + 3) ++ [.binaer .add (frei + 4)] ++
    kopie aus (frei + 4) ++ [.springe 15] ++
    kopie (frei + 4) (frei + 3) ++ kopie (frei + 5) (frei + 3) ++
    [.binaer .mul (frei + 4)] ++ kopie (frei + 5) (frei + 2) ++
    [.binaer .add (frei + 4)] ++ kopie aus (frei + 4)

theorem paarBerechnungLaenge (aSlot bSlot aus frei : Nat) :
    (paarBerechnung aSlot bSlot aus frei).length = 44 := by
  simp only [paarBerechnung, kopie, List.length_append, List.length_cons,
    List.length_nil]

/-- The pairing computation stays inside itself: its conditional lands on the
    second branch and its unconditional jump lands exactly on the block end. -/
theorem bleibtImBlockPaarBerechnung (aSlot bSlot aus frei : Nat) :
    BleibtImBlock (paarBerechnung aSlot bSlot aus frei) := by
  unfold BleibtImBlock
  rintro ⟨pc, temp, lok, rueck, stopp, z, o, g, fs, f, fu, m, ar, pl, env⟩ b hlt hget
  rw [paarBerechnungLaenge] at hlt ⊢
  interval_cases pc <;>
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append,
      List.append_nil, List.cons_append, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, List.length_cons,
      List.length_nil] at hget <;>
    injection hget with hb <;> subst b <;>
    simp only [Befehl.auswerten, Rahmen.schreibe] <;> (try split) <;> omega

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
