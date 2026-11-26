module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecEinSchritt
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecFolge
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecBleibt

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The check and its untaken conditional, run inside their own eight-instruction
    block: the counter is below the limit, so the jump is not taken. -/
theorem precCheckCondLauf (cgBlk : List Befehl) (aus frei y k : Nat) (r : Rahmen)
    (hpc : r.pc = 0) (hy : r.temp (frei + 2) = some (natVal y))
    (hk : r.temp (frei + 1) = some (natVal k)) (hyk : y < k) :
    ∃ r7 : Rahmen,
      (Schritt (precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]))^[8] (some r) = some r7 ∧
      r7.pc = 8 ∧
      (∀ s, s ≠ frei + 6 → s ≠ frei + 7 → r7.temp s = r.temp s) ∧
      r7.lokale = r.lokale ∧ r7.rueckgabe = r.rueckgabe ∧ r7.stopp = r.stopp := by
  obtain ⟨rC, hrunC, hpcC, hCb, hCk, hCpres, hlokC, hrueckC, hstoppC⟩ :=
    precCheckLauf r frei y k hpc hy hk
  have hbleibC := laufBleibtVorEnde (precCheck frei) r 7 rC hrunC hpcC
  let V := precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]
  have hrunV7 : (Schritt V)^[7] (some r) = some rC := by
    dsimp only [V]
    exact (laufAnhang (precCheck frei)
      [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)] r 7 hbleibC).trans hrunC
  have hboolval : precBool y k = true := by
    rw [precBoolEq, decide_eq_true_eq]
    exact hyk
  have hCbool : rC.temp (frei + 6) = some ⟨.bool, true⟩ := by
    rw [hCb]
    change some (precBoolWert y k) = some ⟨.bool, true⟩
    congr 1
    simp only [precBoolWert, hboolval]
  have hget7 : V[7]? = some (.springeWenn (frei + 6) false (cgBlk.length + 92)) := by
    dsimp only [V]
    rw [List.getElem?_append_right (by rw [precCheckLaenge])]
    rw [show 7 - (precCheck frei).length = 0 by rw [precCheckLaenge]]
    simp only [List.getElem?_cons_zero]
  have eJump := schrittSpringeWennFalsch V rC 7 (frei + 6) false true
    (cgBlk.length + 92) hpcC hCbool (by decide) hget7
  let r7 : Rahmen := { rC with pc := 8 }
  have eJump' : (Schritt V)^[1] (some rC) = some r7 := by
    change Schritt V (some rC) = some r7
    rw [eJump]
    congr 1
    rw [hpcC]
  refine ⟨r7, ?_, rfl, ?_, hlokC, hrueckC, hstoppC⟩
  · rw [show (8 : Nat) = 1 + 7 by omega, Function.iterate_add_apply, hrunV7, eJump']
  · intro s hs6 hs7
    change rC.temp s = r.temp s
    exact hCpres s hs6 hs7

/-- Reverse direction of the primitive-recursion body, as a pinned obligation.
    A successful run of the body that reaches its end with `v` in the output slot
    forces the step code to evaluate to `v` at `pair a (pair y i)`. The two
    pairing boundaries are located with `randAusEndePrefix` and the remaining
    segment is the step block, whose reverse lemma (`BlockKorrekt`) supplies the
    evaluation witness. Difficulty: hard; proof sketch: locate the boundary at
    length 88, use `rueckMitPc` to obtain a standalone step-block run, and apply
    the reverse half of the step block's `BlockKorrekt`. -/
def precRumpfRueckAussage (cgBlk : List Befehl) (cg : Nat.Partrec.Code)
    (aus frei freiCg y i a : Nat) (r rEnd : Rahmen) (k : Nat)
    (hlenCg : 0 < cgBlk.length)
    (hpc : r.pc = 0)
    (hy : r.temp (frei + 2) = some (natVal y))
    (hi : r.temp aus = some (natVal i))
    (ha : r.temp (frei + 0) = some (natVal a))
    (hausFrei : aus < frei) (hfreiCg : frei + 20 ≤ freiCg)
    (hcg : BlockKorrekt cgBlk cg (frei + 5) aus freiCg)
    (hvCg : VerschiebbaresProgramm cgBlk)
    (hk : (Schritt (precRumpf cgBlk aus frei))^[k] (some r) = some rEnd)
    (hpcEnd : rEnd.pc = (precRumpf cgBlk aus frei).length) : Prop :=
  ∃ v, Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair y i)) = Part.some v ∧
    rEnd.temp aus = some (natVal v) ∧
    (∀ s, s < frei + 10 → s ≠ aus → s ≠ frei + 4 → s ≠ frei + 5 → rEnd.temp s = r.temp s) ∧
    rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp

/-- Reverse direction of the primitive-recursion loop, as a pinned obligation.
    A run from the loop entry that reaches the loop end with `v` in the
    accumulator forces Mathlib's evaluation of `prec cf cg` to be `v`.
    Difficulty: hard; proof sketch: induction over `k`; for `k = 0` use
    `precExitLauf` with `laufStirbtNach`; for `k + 1` take the deterministic
    first eight steps, locate the body boundary with `randAusEndePrefix`, read
    the step value with `precRumpfRueckAussage`, take the three back-edge steps
    and apply the induction hypothesis at the incremented counter. -/
def precSchleifeRueckAussage (cgBlk : List Befehl) (cf cg : Nat.Partrec.Code)
    (a aus frei freiCg : Nat) : Prop :=
  ∀ (j i k v : Nat) (r rEnd : Rahmen) (schr : Nat),
    r.pc = 0 →
    r.temp (frei + 0) = some (natVal a) →
    r.temp (frei + 1) = some (natVal (j + k)) →
    r.temp (frei + 2) = some (natVal j) →
    r.temp aus = some (natVal i) →
    aus < frei → frei + 20 ≤ freiCg →
    BlockKorrekt cgBlk cg (frei + 5) aus freiCg →
    VerschiebbaresProgramm cgBlk →
    BleibtImBlock cgBlk →
    (Schritt (precSchleife cgBlk aus frei))^[schr] (some r) = some rEnd →
    rEnd.pc = (precSchleife cgBlk aus frei).length →
    rEnd.temp aus = some (natVal v) →
    precFolgeVon cg a j k i = Part.some v

/-- The first pairing segment of the recursion body. It is opaque so that its
    length and instructions are reached only through the lemmas below, never by
    unfolding a concrete forty-four-instruction list during elaboration. -/
@[irreducible] def precPaarEins (aus frei : Nat) : List Befehl :=
  paarBerechnung (frei + 2) aus (frei + 4) (frei + 10)

theorem precPaarEinsGleich (aus frei : Nat) :
    precPaarEins aus frei = paarBerechnung (frei + 2) aus (frei + 4) (frei + 10) := by
  unfold precPaarEins
  rfl

theorem precPaarEinsLaenge (aus frei : Nat) : (precPaarEins aus frei).length = 44 := by
  rw [precPaarEinsGleich, paarBerechnungLaenge]

theorem precPaarEinsBleibt (aus frei : Nat) : BleibtImBlock (precPaarEins aus frei) := by
  rw [precPaarEinsGleich]
  exact bleibtImBlockPaarBerechnung (frei + 2) aus (frei + 4) (frei + 10)

theorem precPaarEinsVerschiebbar (aus frei : Nat) :
    VerschiebbaresProgramm (precPaarEins aus frei) := by
  rw [precPaarEinsGleich]
  exact verschiebbarPaarBerechnung (frei + 2) aus (frei + 4) (frei + 10)

/-- The second pairing segment of the recursion body, opaque for the same
    reason as the first. -/
@[irreducible] def precPaarZwei (aus frei : Nat) : List Befehl :=
  paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)

theorem precPaarZweiGleich (aus frei : Nat) :
    precPaarZwei aus frei = paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20) := by
  unfold precPaarZwei
  rfl

theorem precPaarZweiLaenge (aus frei : Nat) : (precPaarZwei aus frei).length = 44 := by
  rw [precPaarZweiGleich, paarBerechnungLaenge]

theorem precPaarZweiBleibt (aus frei : Nat) : BleibtImBlock (precPaarZwei aus frei) := by
  rw [precPaarZweiGleich]
  exact bleibtImBlockPaarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)

theorem precPaarZweiVerschiebbar (aus frei : Nat) :
    VerschiebbaresProgramm (precPaarZwei aus frei) := by
  rw [precPaarZweiGleich]
  exact verschiebbarPaarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)

/-- Any run of the two pairing segments that reaches their common end writes
    the paired step argument into `frei+5`. Both segment boundaries are located
    with `randAusEndePrefix`; `paarRueck` is applied through the opaque segment
    variables and their length/general equality lemmas. -/
theorem precPaarPaarWert (aus frei y i a : Nat) (r rEnd : Rahmen) (k : Nat)
    (hpc : r.pc = 0)
    (hy : r.temp (frei + 2) = some (natVal y))
    (hi : r.temp aus = some (natVal i))
    (ha : r.temp (frei + 0) = some (natVal a))
    (hausFrei : aus < frei)
    (hk : (Schritt (precPaarEins aus frei ++ precPaarZwei aus frei))^[k]
      (some r) = some rEnd)
    (hpcEnd : rEnd.pc = 44 + 44) :
    rEnd.temp (frei + 5) = some (natVal (Nat.pair a (Nat.pair y i))) ∧
      (∀ s, s < frei + 10 → s ≠ aus → s ≠ frei + 4 → s ≠ frei + 5 → rEnd.temp s = r.temp s) ∧
      rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp := by
  have hlen1 : 0 < (precPaarEins aus frei).length := by
    rw [precPaarEinsLaenge]
    omega
  have hlen2 : 0 < (precPaarZwei aus frei).length := by
    rw [precPaarZweiLaenge]
    omega
  have hpcEnd' : rEnd.pc = (precPaarEins aus frei ++ precPaarZwei aus frei).length := by
    rw [List.length_append, precPaarEinsLaenge, precPaarZweiLaenge]
    exact hpcEnd
  obtain ⟨j2, r1, hj2k, hrunC, hrun1, hpc1⟩ :=
    randAusEndePrefix (precPaarEins aus frei) (precPaarZwei aus frei)
      (precPaarEinsBleibt aus frei) hlen1 hlen2 r k rEnd hpc hk hpcEnd'
  have hrun1' : (Schritt (paarBerechnung (frei + 2) aus (frei + 4) (frei + 10)))^[j2]
      (some r) = some r1 := by
    rw [← precPaarEinsGleich]
    exact hrun1
  have hpc1' : r1.pc = 44 := by
    rw [hpc1, precPaarEinsLaenge]
  obtain ⟨hr1q, hpres1, hlok1, hrueck1, hstopp1⟩ :=
    paarRueck (frei + 2) aus (frei + 4) (frei + 10) r y i hpc hy hi
      (by omega) (by omega) j2 r1 hrun1' hpc1'
  have hkdecomp : (Schritt (precPaarEins aus frei ++ precPaarZwei aus frei))^[k] (some r) =
      (Schritt (precPaarEins aus frei ++ precPaarZwei aus frei))^[k - j2]
        ((Schritt (precPaarEins aus frei ++ precPaarZwei aus frei))^[j2] (some r)) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  have hkS : (Schritt (precPaarEins aus frei ++ precPaarZwei aus frei))^[k - j2]
      (some r1) = some rEnd := by
    rw [hkdecomp, hrunC] at hk
    exact hk
  let r1_0 : Rahmen := { r1 with pc := 0 }
  have hr1_0a : r1_0.temp (frei + 0) = some (natVal a) := by
    change r1.temp (frei + 0) = some (natVal a)
    rw [hpres1 (frei + 0) (by omega) (by omega)]
    exact ha
  have hr1_0q : r1_0.temp (frei + 4) = some (natVal (Nat.pair y i)) := hr1q
  have hmit1 : mitPc (precPaarEins aus frei).length r1_0 = r1 := by
    show { r1 with pc := (precPaarEins aus frei).length + 0 } = r1
    rw [show (precPaarEins aus frei).length + 0 = r1.pc by rw [hpc1, Nat.add_zero]]
  have hpcEnd2 : rEnd.pc = (precPaarEins aus frei).length + (precPaarZwei aus frei).length := by
    simpa only [List.length_append] using hpcEnd'
  have hkS' : (Schritt (precPaarEins aus frei ++ precPaarZwei aus frei))^[k - j2]
      (some (mitPc (precPaarEins aus frei).length r1_0)) = some rEnd := by
    rw [hmit1]
    exact hkS
  obtain ⟨rEnd2, hrun2, hpc2, hEq2⟩ :=
    rueckMitPc (precPaarEins aus frei) (precPaarZwei aus frei)
      (precPaarZweiVerschiebbar aus frei) r1_0 (k - j2) rEnd hkS' hpcEnd2
  have hrun2' : (Schritt (paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)))^[k - j2]
      (some r1_0) = some rEnd2 := by
    rw [← precPaarZweiGleich]
    exact hrun2
  have hpc2' : rEnd2.pc = 44 := by
    rw [hpc2, precPaarZweiLaenge]
  obtain ⟨hr2pair, hpres2, hlok2, hrueck2, hstopp2⟩ :=
    paarRueck (frei + 0) (frei + 4) (frei + 5) (frei + 20) r1_0 a (Nat.pair y i)
      rfl hr1_0a hr1_0q (by omega) (by omega) (k - j2) rEnd2 hrun2' hpc2'
  have hEnd : rEnd = mitPc 44 rEnd2 := by
    rw [hEq2, precPaarEinsLaenge]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hEnd]
    change rEnd2.temp (frei + 5) = some (natVal (Nat.pair a (Nat.pair y i)))
    exact hr2pair
  · intro s hs hneAus hne4 hne5
    rw [hEnd]
    change rEnd2.temp s = r.temp s
    rw [hpres2 s (by omega) hne5]
    change r1.temp s = r.temp s
    rw [hpres1 s (by omega) hne4]
  · rw [hEnd]
    change rEnd2.lokale = r.lokale
    exact hlok2.trans hlok1
  · rw [hEnd]
    change rEnd2.rueckgabe = r.rueckgabe
    exact hrueck2.trans hrueck1
  · rw [hEnd]
    change rEnd2.stopp = r.stopp
    exact hstopp2.trans hstopp1

/-- Reverse direction of the primitive-recursion body. The boundary before the
    step block is located with `randAusEndePrefix`; the opaque pairing segments
    supply the paired argument to the step block's own reverse rule. -/
theorem precRumpfRueck (cgBlk : List Befehl) (cg : Nat.Partrec.Code)
    (aus frei freiCg y i a : Nat) (r rEnd : Rahmen) (k : Nat)
    (hlenCg : 0 < cgBlk.length)
    (hpc : r.pc = 0)
    (hy : r.temp (frei + 2) = some (natVal y))
    (hi : r.temp aus = some (natVal i))
    (ha : r.temp (frei + 0) = some (natVal a))
    (hausFrei : aus < frei) (hfreiCg : frei + 20 ≤ freiCg)
    (hcg : BlockKorrekt cgBlk cg (frei + 5) aus freiCg)
    (hvCg : VerschiebbaresProgramm cgBlk)
    (hk : (Schritt (precRumpf cgBlk aus frei))^[k] (some r) = some rEnd)
    (hpcEnd : rEnd.pc = (precRumpf cgBlk aus frei).length) :
    precRumpfRueckAussage cgBlk cg aus frei freiCg y i a r rEnd k
      hlenCg hpc hy hi ha hausFrei hfreiCg hcg hvCg hk hpcEnd := by
  rcases hcg with ⟨hcgEin, hcgAus, hcgUn, hcgNr⟩
  let P := precPaarEins aus frei ++ precPaarZwei aus frei
  have hlenP : 0 < P.length := by
    dsimp only [P]
    rw [List.length_append, precPaarEinsLaenge, precPaarZweiLaenge]
    omega
  have hlocalP : BleibtImBlock P := by
    dsimp only [P]
    exact bleibtImBlockAppend (precPaarEins aus frei) (precPaarZwei aus frei)
      (precPaarEinsBleibt aus frei) (precPaarZweiVerschiebbar aus frei)
      (precPaarZweiBleibt aus frei)
  have hkC : (Schritt (P ++ cgBlk))^[k] (some r) = some rEnd := by
    simpa only [P, precRumpf, precPaarEinsGleich, precPaarZweiGleich] using hk
  have hpcEndC : rEnd.pc = P.length + cgBlk.length := by
    rw [hpcEnd, precRumpfLaenge]
    dsimp only [P]
    rw [List.length_append, precPaarEinsLaenge, precPaarZweiLaenge]
  obtain ⟨j1, r2, hj1k, hrunC1, hrun12, hpc2⟩ :=
    randAusEndePrefix P cgBlk hlocalP hlenP hlenCg r k rEnd hpc hkC
      (by simpa only [List.length_append] using hpcEndC)
  have hkdecomp : (Schritt (P ++ cgBlk))^[k] (some r) =
      (Schritt (P ++ cgBlk))^[k - j1] ((Schritt (P ++ cgBlk))^[j1] (some r)) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  have hkS : (Schritt (P ++ cgBlk))^[k - j1] (some r2) = some rEnd := by
    rw [hkdecomp, hrunC1] at hkC
    exact hkC
  let r2_0 : Rahmen := { r2 with pc := 0 }
  have hmit2 : mitPc P.length r2_0 = r2 := by
    show { r2 with pc := P.length + 0 } = r2
    rw [show P.length + 0 = r2.pc by rw [hpc2, Nat.add_zero]]
  have hkS' : (Schritt (P ++ cgBlk))^[k - j1]
      (some (mitPc P.length r2_0)) = some rEnd := by
    rw [hmit2]
    exact hkS
  obtain ⟨rCg, hrunCg, hpcCg, hEqCg⟩ :=
    rueckMitPc P cgBlk hvCg r2_0 (k - j1) rEnd hkS' hpcEndC
  have hpc2' : r2.pc = 44 + 44 := by
    rw [hpc2]
    dsimp only [P]
    rw [List.length_append, precPaarEinsLaenge, precPaarZweiLaenge]
  obtain ⟨hr2pair, hpres2, hlok2, hrueck2, hstopp2⟩ :=
    precPaarPaarWert aus frei y i a r r2 j1 hpc hy hi ha hausFrei hrun12 hpc2'
  have hr2_0p : r2_0.temp (frei + 5) = some (natVal (Nat.pair a (Nat.pair y i))) := hr2pair
  obtain ⟨v, hvEval, hrCgaus, hpresCg, hlokCg, hrueckCg, hstoppCg⟩ :=
    (hcgNr (Nat.pair a (Nat.pair y i)) r2_0 rfl hr2_0p).2 (k - j1) rCg hrunCg hpcCg
  have hEqEnd : rEnd = mitPc P.length rCg := hEqCg
  refine ⟨v, hvEval, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEqEnd]
    change rCg.temp aus = some (natVal v)
    exact hrCgaus
  · intro s hs hneAus hne4 hne5
    rw [hEqEnd]
    change rCg.temp s = r.temp s
    rw [hpresCg s (by omega) hneAus]
    change r2.temp s = r.temp s
    exact hpres2 s (by omega) hneAus hne4 hne5
  · rw [hEqEnd]
    change rCg.lokale = r.lokale
    exact hlokCg.trans hlok2
  · rw [hEqEnd]
    change rCg.rueckgabe = r.rueckgabe
    exact hrueckCg.trans hrueck2
  · rw [hEqEnd]
    change rCg.stopp = r.stopp
    exact hstoppCg.trans hstopp2

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
