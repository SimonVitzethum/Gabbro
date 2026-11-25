module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBeweise.PaarKorrekt
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Every instruction emitted by the pairing computation is relocatable, and
    none of them is a backward jump. -/
theorem verschiebbarPaarBerechnung (aSlot bSlot aus frei : Nat) :
    VerschiebbaresProgramm (paarBerechnung aSlot bSlot aus frei) := by
  unfold VerschiebbaresProgramm
  intro j hj
  rw [paarBerechnungLaenge] at hj
  interval_cases j <;>
    simp only [paarBerechnung, kopie, List.append_assoc, List.nil_append,
      List.append_nil, List.cons_append, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, List.length_cons,
      List.length_nil] at hj ⊢
  all_goals
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [Verschiebbar]
    · intro d hd
      cases hd

/-- Staying inside a block is preserved by concatenation. A counter inside the
    first block is discharged there; a counter inside the second block is
    discharged on the frame shifted back by the first block's length, with the
    relocation identity turning the shifted result back into an absolute one. -/
theorem bleibtImBlockAppend (blkA blkB : List Befehl)
    (hA : BleibtImBlock blkA) (hvB : VerschiebbaresProgramm blkB)
    (hB : BleibtImBlock blkB) : BleibtImBlock (blkA ++ blkB) := by
  unfold BleibtImBlock
  intro r b hlt hget
  by_cases hltA : r.pc < blkA.length
  · have hgetA : blkA[r.pc]? = some b := by
      rw [← getAnhangLinks blkA blkB r.pc hltA]
      exact hget
    have hle := hA r b hltA hgetA
    simp only [List.length_append]
    omega
  · have hltMid : r.pc - blkA.length < blkB.length := by
      simp only [List.length_append] at hlt
      omega
    let r0 : Rahmen := { r with pc := r.pc - blkA.length }
    have hmr : mitPc blkA.length r0 = r := by
      show { r with pc := blkA.length + (r.pc - blkA.length) } = r
      rw [show blkA.length + (r.pc - blkA.length) = r.pc by omega]
    have hgetB : blkB[r0.pc]? = some b := by
      have hgp := getNachPrefix blkA blkB r0.pc hltMid
      rw [← hgp]
      have hidx : blkA.length + r0.pc = r.pc := by
        simp only [r0]
        omega
      rw [hidx]
      exact hget
    have hstepComp : Schritt (blkA ++ blkB) (some r) = some (b.auswerten r) := by
      show (match (blkA ++ blkB)[r.pc]? with
        | none => none | some c => some (c.auswerten r)) = some (b.auswerten r)
      rw [hget]
    have hstepB : Schritt blkB (some r0) = some (b.auswerten r0) := by
      show (match blkB[r0.pc]? with
        | none => none | some c => some (c.auswerten r0)) = some (b.auswerten r0)
      rw [hgetB]
    have hshift := schrittMitPcBei blkA blkB [] hvB r0 hltMid
    simp only [List.append_nil, hmr, hstepB] at hshift
    have heq : b.auswerten r = mitPc blkA.length (b.auswerten r0) :=
      Option.some.inj (hstepComp.symm.trans hshift)
    rw [heq]
    simp only [mitPc, List.length_append]
    have hle := hB r0 b hltMid hgetB
    omega

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
