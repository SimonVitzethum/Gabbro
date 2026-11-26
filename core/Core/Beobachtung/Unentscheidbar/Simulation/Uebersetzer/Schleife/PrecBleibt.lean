module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBeweise.Hilfen
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBlock
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecSchleife
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecEinSchritt

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

/-- The whole primitive-recursion loop stays inside itself. The check and the
    back edge are discharged concretely; the body is discharged by the body
    lemma shifted by the check prefix. -/
theorem bleibtImBlockPrecSchleife (cgBlk : List Befehl) (aus frei : Nat)
    (hcg : BleibtImBlock cgBlk) (hvCg : VerschiebbaresProgramm cgBlk) :
    BleibtImBlock (precSchleife cgBlk aus frei) := by
  unfold BleibtImBlock
  intro r b hlt hget
  rw [precSchleifeLaenge] at hlt ⊢
  by_cases hltV : r.pc < 8
  · by_cases hlt7 : r.pc < 7
    · have hgetCheck : (precCheck frei)[r.pc]? = some b := by
        rw [← getAnhangLinks (precCheck frei)
          ([(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)] ++
            (precRumpf cgBlk aus frei ++ precEnde cgBlk frei)) r.pc
            (by rw [precCheckLaenge]; exact hlt7)]
        simpa only [precSchleife, List.append_assoc] using hget
      have hle := bleibtImBlockPrecCheck frei r b hlt7 hgetCheck
      rw [precCheckLaenge] at hle
      omega
    · have hrpc7 : r.pc = 7 := by omega
      have hget7 : (precSchleife cgBlk aus frei)[7]? =
          some (.springeWenn (frei + 6) false (cgBlk.length + 92)) :=
        precSchleifeBei7 cgBlk aus frei
      rw [hrpc7, hget7] at hget
      injection hget with hb
      subst b
      simp only [Befehl.auswerten]
      rw [hrpc7]
      by_cases hcond : (r.temp (frei + 6)).bind alsBoolean = some false <;>
        simp only [hcond, if_true, if_false] <;> omega
  · have hgeV : 8 ≤ r.pc := by omega
    by_cases hltR : r.pc < 96 + cgBlk.length
    · let V := precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]
      let R := precRumpf cgBlk aus frei
      let r0 : Rahmen := { r with pc := r.pc - 8 }
      have hltMid : r0.pc < R.length := by
        dsimp only [r0, R]
        rw [precRumpfLaenge]
        omega
      have hmr : mitPc 8 r0 = r := by
        show { r with pc := 8 + (r.pc - 8) } = r
        rw [show 8 + (r.pc - 8) = r.pc by omega]
      have hlenV : V.length = 8 := by
        dsimp only [V]
        simp only [List.length_append, precCheckLaenge, List.length_cons, List.length_nil]
      have hlenVR : (V ++ R).length = 96 + cgBlk.length := by
        dsimp only [V, R]
        simp only [List.length_append, precCheckLaenge, precRumpfLaenge,
          List.length_cons, List.length_nil]
        omega
      have hgetR : R[r0.pc]? = some b := by
        have hidx := getNachPrefix V R r0.pc hltMid
        rw [hlenV] at hidx
        rw [show 8 + r0.pc = r.pc by dsimp only [r0]; omega] at hidx
        change ((V ++ R) ++ precEnde cgBlk frei)[r.pc]? = some b at hget
        rw [getAnhangLinks (V ++ R) (precEnde cgBlk frei) r.pc (by rw [hlenVR]; exact hltR)] at hget
        rw [← hidx]
        exact hget
      have hvR : VerschiebbaresProgramm R := by
        dsimp only [R]
        rw [← verschiebbarVonNull]
        exact verschiebbarPrecRumpf 0 cgBlk aus frei hvCg
      obtain ⟨_, hgetR0, hvb, hzd⟩ := hvR r0.pc hltMid
      have hshift := auswertenMitPc 8 b r0 hvb hzd
      rw [hmr] at hshift
      have hle := bleibtImBlockPrecRumpf cgBlk aus frei hcg hvCg r0 b hltMid hgetR
      rw [precRumpfLaenge] at hle
      rw [hshift]
      simp only [mitPc]
      omega
    · let t := r.pc - (96 + cgBlk.length)
      have htlt : t < 3 := by omega
      let VR := (precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]) ++
        precRumpf cgBlk aus frei
      have hlenVR : VR.length = 96 + cgBlk.length := by
        dsimp only [VR]
        simp only [List.length_append, precCheckLaenge, precRumpfLaenge,
          List.length_cons, List.length_nil]
        omega
      have hgetE : (precEnde cgBlk frei)[t]? = some b := by
        have hidx := getNachPrefix VR (precEnde cgBlk frei) t htlt
        rw [hlenVR] at hidx
        change (VR ++ precEnde cgBlk frei)[r.pc]? = some b at hget
        rw [show 96 + cgBlk.length + t = r.pc by dsimp only [t]; omega] at hidx
        rw [← hidx]
        exact hget
      have hpcDecomp : r.pc = 96 + cgBlk.length + t := by
        dsimp only [t]
        omega
      interval_cases t <;>
        simp only [precEnde, List.getElem?_cons_zero, List.getElem?_cons_succ,
          List.getElem?_nil] at hgetE <;>
        injection hgetE with hb <;> subst b <;>
        simp only [Befehl.auswerten, Rahmen.schreibe] <;> omega

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
