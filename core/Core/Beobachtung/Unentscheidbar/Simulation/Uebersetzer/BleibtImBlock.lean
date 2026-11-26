module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.RightAblauf
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Succ
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Null
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.BlockKette
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The constant block stays inside itself. -/
theorem bleibtImBlockZero (ein aus frei : Nat) : BleibtImBlock (zeroBlk ein aus frei) := by
  unfold BleibtImBlock
  rintro ⟨pc, temp, lok, rueck, stopp, z, o, g, fs, f, fu, m, ar, pl, env⟩ b hlt hget
  rw [zeroBlkLaenge] at hlt ⊢
  interval_cases pc <;>
    simp only [zeroBlk, List.getElem?_cons_zero] at hget <;>
    injection hget with hb <;> subst b <;>
    simp only [Befehl.auswerten, Rahmen.schreibe] <;> omega

/-- The successor block stays inside itself. -/
theorem bleibtImBlockSucc (ein aus frei : Nat) : BleibtImBlock (succBlk ein aus frei) := by
  unfold BleibtImBlock
  rintro ⟨pc, temp, lok, rueck, stopp, z, o, g, fs, f, fu, m, ar, pl, env⟩ b hlt hget
  rw [succBlkLaenge] at hlt ⊢
  interval_cases pc <;>
    simp only [succBlk, kopie, List.append_assoc, List.nil_append, List.append_nil,
      List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, List.length_cons, List.length_nil] at hget <;>
    injection hget with hb <;> subst b <;>
    simp only [Befehl.auswerten, Rahmen.schreibe] <;> omega

/-- The square-root search prefix stays inside itself. Its only backward jump
    lands at the loop entry; its forward conditional stays at or before the
    exit. -/
theorem bleibtImBlockSqrtPrefix (ein frei : Nat) : BleibtImBlock (sqrtPrefix ein frei) := by
  unfold BleibtImBlock
  rintro ⟨pc, temp, lok, rueck, stopp, z, o, g, fs, f, fu, m, ar, pl, env⟩ b hlt hget
  rw [sqrtPrefixLaenge] at hlt ⊢
  interval_cases pc <;>
    simp only [sqrtPrefix, sqrtInit, sqrtLoop, kopie, List.append_assoc,
      List.nil_append, List.append_nil, List.cons_append, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, List.length_cons,
      List.length_nil] at hget <;>
    injection hget with hb <;> subst b <;>
    simp only [Befehl.auswerten, Rahmen.schreibe] <;> (try split) <;> omega

/-- The left-projection block stays inside itself. -/
theorem bleibtImBlockLeft (ein aus frei : Nat) : BleibtImBlock (leftBlk ein aus frei) := by
  unfold BleibtImBlock
  rintro ⟨pc, temp, lok, rueck, stopp, z, o, g, fs, f, fu, m, ar, pl, env⟩ b hlt hget
  rw [leftBlkLaenge] at hlt ⊢
  interval_cases pc <;>
    simp only [leftBlk, sqrtPrefix, sqrtInit, sqrtLoop, kopie, leftSel,
      List.append_assoc, List.nil_append, List.append_nil, List.cons_append,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      List.length_cons, List.length_nil] at hget <;>
    injection hget with hb <;> subst b <;>
    simp only [Befehl.auswerten, Rahmen.schreibe] <;> (try split) <;> omega

/-- The right-projection block stays inside itself. -/
theorem bleibtImBlockRight (ein aus frei : Nat) : BleibtImBlock (rightBlk ein aus frei) := by
  unfold BleibtImBlock
  rintro ⟨pc, temp, lok, rueck, stopp, z, o, g, fs, f, fu, m, ar, pl, env⟩ b hlt hget
  rw [rightBlkLaenge] at hlt ⊢
  interval_cases pc <;>
    simp only [rightBlk, sqrtPrefix, sqrtInit, sqrtLoop, kopie, rightSel,
      List.append_assoc, List.nil_append, List.append_nil, List.cons_append,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      List.length_cons, List.length_nil] at hget <;>
    injection hget with hb <;> subst b <;>
    simp only [Befehl.auswerten, Rahmen.schreibe] <;> (try split) <;> omega

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
