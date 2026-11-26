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

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
