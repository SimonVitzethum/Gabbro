module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Grundlagen

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Shift a frame's program counter by a fixed base. All jumps in the
    translator are relative, so running a block at a shifted base behaves as
    running it at zero and shifting the resulting counters back. -/
def mitPc (p : Nat) (r : Rahmen) : Rahmen :=
  { r with pc := p + r.pc }

/-- The instructions the translator emits. Every one of them touches the
    program counter only by adding a constant, or (for the backward jump) by
    subtracting a constant not larger than the counter. -/
def Verschiebbar (b : Befehl) : Prop :=
  match b with
  | .literal _ _ | .binaer _ _ | .binden _ _ | .wahrheitswert _ _
  | .lesen _ _ | .negativ _ _ | .negieren _ | .verneinen _ | .teilen _
  | .vergleichen _ _ | .springeWenn _ _ _ | .zuweisen _ _ _
  | .springe _ | .blockEnde _ | .zurueckSprung _ | .ende => True
  | _ => False

/-- Evaluation of a translator instruction commutes with a program-counter
    shift. The backward jump needs its distance not to exceed the counter. -/
theorem auswertenMitPc (p : Nat) (b : Befehl) (r : Rahmen)
    (hv : Verschiebbar b)
    (hz : ∀ d, b = .zurueckSprung d → d ≤ r.pc) :
    b.auswerten (mitPc p r) = mitPc p (b.auswerten r) := by
  cases b with
  | literal z v => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | binaer op l => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | binden n q => simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | wahrheitswert z v => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | lesen z i => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | negativ z m => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | negieren z => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | verneinen z => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | teilen l => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | vergleichen op l => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | zuweisen q i t => simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | springe d => simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | blockEnde c => simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | ende => simp only [Befehl.auswerten, mitPc]
  | springeWenn q wv d =>
    by_cases hc : (r.temp q).bind alsBoolean = some wv <;>
      simp only [Befehl.auswerten, mitPc, Nat.add_assoc, hc]
  | zurueckSprung d =>
    have hpc : (p + r.pc) - d = p + (r.pc - d) := by
      have hd : d ≤ r.pc := hz d rfl
      omega
    simp only [Befehl.auswerten, mitPc, hpc]
  | _ => cases hv

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
