module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBeweise.Hilfen
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBlock
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecSchleife

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The primitive-recursion body stays inside itself. The two pairing segments
    are discharged by their concrete block lemma; the step block is discharged
    by the induction hypothesis `BleibtImBlock cgBlk`, shifted by the pairing
    prefix. Relocatability of the step block is the companion induction
    hypothesis and is needed only to align the shifted evaluation. -/
theorem bleibtImBlockPrecRumpf (cgBlk : List Befehl) (aus frei : Nat)
    (hcg : BleibtImBlock cgBlk) (hvCg : VerschiebbaresProgramm cgBlk) :
    BleibtImBlock (precRumpf cgBlk aus frei) := by
  let paar1 := paarBerechnung (frei + 2) aus (frei + 4) (frei + 10)
  let paar2 := paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
  have h1 : BleibtImBlock paar1 := by
    dsimp only [paar1]
    exact bleibtImBlockPaarBerechnung (frei + 2) aus (frei + 4) (frei + 10)
  have h2 : BleibtImBlock paar2 := by
    dsimp only [paar2]
    exact bleibtImBlockPaarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
  have hv2 : VerschiebbaresProgramm paar2 := by
    dsimp only [paar2]
    exact verschiebbarPaarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
  have h12 : BleibtImBlock (paar1 ++ paar2) :=
    bleibtImBlockAppend paar1 paar2 h1 hv2 h2
  have hres : BleibtImBlock ((paar1 ++ paar2) ++ cgBlk) :=
    bleibtImBlockAppend (paar1 ++ paar2) cgBlk h12 hvCg hcg
  simpa only [precRumpf, paar1, paar2] using hres

/-- The comparison segment stays inside itself. -/
theorem bleibtImBlockPrecCheck (frei : Nat) : BleibtImBlock (precCheck frei) := by
  unfold BleibtImBlock
  rintro ⟨pc, temp, lok, rueck, stopp, z, o, g, fs, f, fu, m, ar, pl, env⟩ b hlt hget
  rw [precCheckLaenge] at hlt ⊢
  interval_cases pc <;>
    simp only [precCheck, kopie, List.append_assoc, List.nil_append,
      List.append_nil, List.cons_append, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, List.length_cons,
      List.length_nil] at hget <;>
    injection hget with hb <;> subst b <;>
    simp only [Befehl.auswerten, Rahmen.schreibe] <;> (try split) <;> omega

/-- The conditional of the check stays inside its one-instruction block. -/
theorem bleibtImBlockPrecCond (cgBlk : List Befehl) (frei : Nat) :
    BleibtImBlock [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)] := by
  unfold BleibtImBlock
  rintro ⟨pc, temp, lok, rueck, stopp, z, o, g, fs, f, fu, m, ar, pl, env⟩ b hlt hget
  simp only [List.length_cons, List.length_nil] at hlt ⊢
  interval_cases pc
  simp only [List.getElem?_cons_zero] at hget
  injection hget with hb
  subst b
  simp only [Befehl.auswerten] <;> (try split) <;> omega

/-- The back edge stays inside its three-instruction block. -/
theorem bleibtImBlockPrecEnde (cgBlk : List Befehl) (frei : Nat) : BleibtImBlock (precEnde cgBlk frei) := by
  unfold BleibtImBlock
  rintro ⟨pc, temp, lok, rueck, stopp, z, o, g, fs, f, fu, m, ar, pl, env⟩ b hlt hget
  rw [precEndeLaenge] at hlt ⊢
  interval_cases pc <;>
    simp only [precEnde, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil] at hget <;>
    injection hget with hb <;> subst b <;>
    simp only [Befehl.auswerten, Rahmen.schreibe] <;> omega

/-- One relocated step with a base-offset relocatability premise. -/
theorem schrittMitPcBeiVon (pre mid post : List Befehl)
    (hv : VerschiebbarVon pre.length mid) (r : Rahmen) (hlt : r.pc < mid.length) :
    Schritt (pre ++ mid ++ post) (some (mitPc pre.length r)) =
      match Schritt mid (some r) with
      | none => none
      | some r' => some (mitPc pre.length r') := by
  obtain ⟨b, hb, hvb, hzd⟩ := hv r.pc hlt
  have hgetConcat : (pre ++ mid ++ post)[pre.length + r.pc]? = some b := by
    rw [getAnhangLinks (pre ++ mid) post (pre.length + r.pc)]
    · exact (getNachPrefix pre mid r.pc hlt).trans hb
    · simp only [List.length_append]
      omega
  have hgetConcat' : (pre ++ mid ++ post)[(mitPc pre.length r).pc]? = some b := by
    simpa only [mitPc] using hgetConcat
  have e2 : b.auswerten (mitPc pre.length r) = mitPc pre.length (b.auswerten r) :=
    auswertenMitPc pre.length b r hvb hzd
  simp only [Schritt, hgetConcat', hb]
  rw [e2]

/-- Staying inside is preserved by appending a block whose backward jumps are
    bounded relative to the prefix length. -/
theorem bleibtImBlockAppendVon (blkA blkB : List Befehl)
    (hA : BleibtImBlock blkA) (hvB : VerschiebbarVon blkA.length blkB)
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
    have hshift := schrittMitPcBeiVon blkA blkB [] hvB r0 hltMid
    simp only [List.append_nil, hmr, hstepB] at hshift
    have heq : b.auswerten r = mitPc blkA.length (b.auswerten r0) :=
      Option.some.inj (hstepComp.symm.trans hshift)
    rw [heq]
    simp only [mitPc, List.length_append]
    have hle := hB r0 b hltMid hgetB
    omega

/-- The comparison plus its conditional stays inside its eight instructions. -/
theorem bleibtImBlockPrecV (cgBlk : List Befehl) (frei : Nat) :
    BleibtImBlock (precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]) := by
  apply bleibtImBlockAppend
  · exact bleibtImBlockPrecCheck frei
  · simp only [VerschiebbaresProgramm, List.length_cons, List.length_nil]
    intro j hj
    interval_cases j
    exact ⟨_, rfl, by simp only [Verschiebbar], by intro d hd; cases hd⟩
  · exact bleibtImBlockPrecCond cgBlk frei

/-- The whole primitive-recursion loop stays inside itself. -/
theorem bleibtImBlockPrecSchleife (cgBlk : List Befehl) (aus frei : Nat)
    (hcg : BleibtImBlock cgBlk) (hvCg : VerschiebbaresProgramm cgBlk) :
    BleibtImBlock (precSchleife cgBlk aus frei) := by
  let V := precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]
  let R := precRumpf cgBlk aus frei
  let E := precEnde cgBlk frei
  have hV : BleibtImBlock V := by
    dsimp only [V]
    exact bleibtImBlockPrecV cgBlk frei
  have hVR : BleibtImBlock (V ++ R) := by
    apply bleibtImBlockAppend
    · exact hV
    · rw [← verschiebbarVonNull]
      dsimp only [R]
      exact verschiebbarPrecRumpf 0 cgBlk aus frei hvCg
    · dsimp only [R]
      exact bleibtImBlockPrecRumpf cgBlk aus frei hcg hvCg
  have hlenVR : (V ++ R).length = cgBlk.length + 96 := by
    dsimp only [V, R]
    simp only [List.length_append, precCheckLaenge, precRumpfLaenge,
      List.length_cons, List.length_nil]
    omega
  have hvE : VerschiebbarVon (V ++ R).length E := by
    rw [hlenVR]
    dsimp only [E]
    exact verschiebbarPrecEnde (cgBlk.length + 96) cgBlk frei rfl
  have hE : BleibtImBlock E := by
    dsimp only [E]
    exact bleibtImBlockPrecEnde cgBlk frei
  have hres := bleibtImBlockAppendVon (V ++ R) E hVR hvE hE
  simpa only [precSchleife, V, R, E] using hres

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
