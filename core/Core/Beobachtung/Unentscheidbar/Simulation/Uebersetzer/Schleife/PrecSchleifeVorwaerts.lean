module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecEinSchritt

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- When the counter has reached the limit the check writes false and the
    conditional jumps straight to the program end. -/
theorem precExitLauf (cgBlk : List Befehl) (aus frei j : Nat) (r : Rahmen)
    (hpc : r.pc = 0) (hy : r.temp (frei + 2) = some (natVal j))
    (hk : r.temp (frei + 1) = some (natVal j)) :
    ∃ rEnd : Rahmen, (Schritt (precSchleife cgBlk aus frei))^[8] (some r) = some rEnd ∧
      rEnd.pc = (precSchleife cgBlk aus frei).length ∧
      (∀ s, s ≠ frei + 6 → s ≠ frei + 7 → rEnd.temp s = r.temp s) ∧
      rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp := by
  obtain ⟨rC, hrunC, hpcC, hCb, hCk, hCpres, hlokC, hrueckC, hstoppC⟩ :=
    precCheckLauf r frei j j hpc hy hk
  have hbleibC := laufBleibtVorEnde (precCheck frei) r 7 rC hrunC hpcC
  have hrunC' : (Schritt (precSchleife cgBlk aus frei))^[7] (some r) = some rC := by
    rw [precSchleife, List.append_assoc, List.append_assoc]
    exact (laufAnhang (precCheck frei)
      ([.springeWenn (frei + 6) false (cgBlk.length + 92)] ++
        (precRumpf cgBlk aus frei ++ precEnde cgBlk frei)) r 7 hbleibC).trans hrunC
  have hboolval : precBool j j = false := by
    rw [precBoolEq]
    simp only [Nat.lt_irrefl, decide_false]
  have hCbool : rC.temp (frei + 6) = some ⟨.bool, false⟩ := by
    rw [hCb]
    change some (precBoolWert j j) = some ⟨.bool, false⟩
    congr 1
    simp only [precBoolWert, hboolval]
  have eJump : (Schritt (precSchleife cgBlk aus frei))^[1] (some rC) =
      some { rC with pc := rC.pc + (cgBlk.length + 92) } := by
    exact schrittSpringeWennWahr (precSchleife cgBlk aus frei) rC 7 (frei + 6)
      false false (cgBlk.length + 92) hpcC hCbool rfl (precSchleifeBei7 cgBlk aus frei)
  let rEnd : Rahmen := { rC with pc := cgBlk.length + 99 }
  have eJump' : (Schritt (precSchleife cgBlk aus frei))^[1] (some rC) = some rEnd := by
    rw [eJump]
    congr 1
    rw [hpcC]
    omega
  refine ⟨rEnd, ?_, ?_, ?_, hlokC, hrueckC, hstoppC⟩
  · rw [show (8 : Nat) = 1 + 7 by omega, Function.iterate_add_apply, hrunC', eJump']
  · change cgBlk.length + 99 = (precSchleife cgBlk aus frei).length
    rw [precSchleifeLaenge]
  · intro s hs6 hs7
    change rC.temp s = r.temp s
    exact hCpres s hs6 hs7

/-- The forward run of `precFolgeVon`: starting at counter `j`, limit `j+k`
    and accumulator `i`, the loop performs exactly the `k` steps of the step
    sequence and leaves its result in the accumulator. -/
theorem precFolgeVonLauf (cgBlk : List Befehl) (cg : Nat.Partrec.Code)
    (a aus frei freiCg : Nat) :
    ∀ (j i k v : Nat) (r : Rahmen),
      r.pc = 0 →
      r.temp (frei + 0) = some (natVal a) →
      r.temp (frei + 1) = some (natVal (j + k)) →
      r.temp (frei + 2) = some (natVal j) →
      r.temp aus = some (natVal i) →
      aus < frei → frei + 20 ≤ freiCg →
      BlockKorrekt cgBlk cg (frei + 5) aus freiCg →
      VerschiebbaresProgramm cgBlk →
      precFolgeVon cg a j k i = Part.some v →
      ∃ schr rEnd, (Schritt (precSchleife cgBlk aus frei))^[schr] (some r) = some rEnd ∧
        rEnd.pc = (precSchleife cgBlk aus frei).length ∧
        rEnd.temp aus = some (natVal v) ∧
        (∀ s, s < frei → s ≠ aus → rEnd.temp s = r.temp s) ∧
        rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp := by
  intro j i k v r hpc ha hk hy hi haus hcgf hcg hvCg hv
  induction k generalizing j i r v with
  | zero =>
    have hvi : v = i := by simpa only [precFolgeVon] using hv
    subst v
    obtain ⟨rEnd, hrun, hpcEnd, hpres, hlok, hrueck, hstopp⟩ :=
      precExitLauf cgBlk aus frei j r hpc hy hk
    refine ⟨8, rEnd, hrun, hpcEnd, hi, ?_, hlok, hrueck, hstopp⟩
    intro s hs hne
    exact hpres s (by omega) (by omega)
  | succ k ih =>
    rw [precFolgeVonSchritt] at hv
    obtain ⟨v1, hv1, hvRest⟩ := Part.bind_eq_some_iff.mp hv
    have hylt : j < j + (k + 1) := by omega
    obtain ⟨kEin, r1, hrun1, hpc1, hr1y, hr1aus, hpres1, hlok1, hrueck1, hstopp1⟩ :=
      precEinSchritt cgBlk cg a aus frei freiCg j (j + (k + 1)) i v1 r
        hpc ha hk hy hi hylt haus hcgf hcg hvCg hv1
    have hr1limit : r1.temp (frei + 1) = some (natVal ((j + 1) + k)) := by
      rw [hpres1 (frei + 1) (by omega) (by omega)]
      rw [hk]
      congr 1
      omega
    have hr1a : r1.temp (frei + 0) = some (natVal a) := by
      rw [hpres1 (frei + 0) (by omega) (by omega)]
      exact ha
    obtain ⟨kRest, rEnd, hrunRest, hpcEnd, hrEndaus, hpresRest, hlokRest, hrueckRest, hstoppRest⟩ :=
      ih (j + 1) v1 v1 r1 hpc1 hr1a hr1limit hr1y hr1aus haus hcgf hcg hvCg hvRest
    refine ⟨kRest + kEin, rEnd, ?_, hpcEnd, hrEndaus, ?_, ?_, ?_, ?_⟩
    · rw [Function.iterate_add_apply, hrun1, hrunRest]
    · intro s hs hne
      rw [hpresRest s hs hne]
      exact hpres1 s hs hne
    · exact hlokRest.trans hlok1
    · exact hrueckRest.trans hrueck1
    · exact hstoppRest.trans hstopp1

/-- The forward half of the primitive-recursion block: Mathlib's evaluation
    of `prec cf cg` is exactly the step sequence the loop performs. -/
theorem precSchleifeVorwaerts (cgBlk : List Befehl) (cf cg : Nat.Partrec.Code)
    (a aus frei freiCg k v0 v : Nat) (r : Rahmen)
    (hpc : r.pc = 0)
    (ha : r.temp (frei + 0) = some (natVal a))
    (hk : r.temp (frei + 1) = some (natVal k))
    (hcounter : r.temp (frei + 2) = some (natVal 0))
    (hi : r.temp aus = some (natVal v0))
    (hausFrei : aus < frei) (hfreiCg : frei + 20 ≤ freiCg)
    (hcg : BlockKorrekt cgBlk cg (frei + 5) aus freiCg)
    (hvCg : VerschiebbaresProgramm cgBlk)
    (hcf : Nat.Partrec.Code.eval cf a = Part.some v0)
    (hv : Nat.Partrec.Code.eval (Nat.Partrec.Code.prec cf cg) (Nat.pair a k) = Part.some v) :
    ∃ schr rEnd, (Schritt (precSchleife cgBlk aus frei))^[schr] (some r) = some rEnd ∧
      rEnd.pc = (precSchleife cgBlk aus frei).length ∧
      rEnd.temp aus = some (natVal v) ∧
      (∀ s, s < frei → s ≠ aus → rEnd.temp s = r.temp s) ∧
      rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp := by
  rw [evalPrecAlsFolge, hcf] at hv
  simp only [Part.bind_some] at hv
  exact precFolgeVonLauf cgBlk cg a aus frei freiCg 0 v0 k v r
    hpc ha hk hcounter hi hausFrei hfreiCg hcg hvCg hv

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
