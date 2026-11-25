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

/-- Evaluation of an instruction commutes with a program-counter shift. The
    only instruction whose effect depends on the absolute counter is the
    backward jump; there the jump distance never exceeds the counter, which is
    recorded as the premise `hz`. -/
theorem auswertenMitPc (p : Nat) (b : Befehl) (r : Rahmen)
    (hz : ∀ d, b = .zurueckSprung d → d ≤ r.pc) :
    b.auswerten (mitPc p r) = mitPc p (b.auswerten r) := by
  cases b with
  | literal z v =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | binaer op l =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | binden n q =>
    simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | wahrheitswert z v =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | lesen z i =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | negativ z m =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | negieren z =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | verneinen z =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | teilen l =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | vergleichen op l =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | springeWenn q wv d =>
    simp only [Befehl.auswerten, mitPc]
    split <;> omega
  | zuweisen q i z t =>
    simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | zurueck q t =>
    simp only [Befehl.auswerten, mitPc]
  | springe d =>
    simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | blockEnde c =>
    simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | bindeWert q t g =>
    simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | definiere n ps rs gs sk m calls eff =>
    simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | rufe n args bind =>
    simp only [Befehl.auswerten, mitPc]
  | rueckVoid =>
    simp only [Befehl.auswerten, mitPc]
  | pruefeMass q =>
    simp only [Befehl.auswerten, mitPc]
  | setzePasszahl q st =>
    simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | whileTest q e h =>
    simp only [Befehl.auswerten, mitPc]
  | forAnfang lo hi ix sk sh mh =>
    simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | forTest e h =>
    simp only [Befehl.auswerten, mitPc]
  | forNaechster back ix =>
    have hd : back ≤ r.pc := hz back rfl
    simp only [Befehl.auswerten, mitPc]
    omega
  | zurueckSprung d =>
    have hd : d ≤ r.pc := hz d rfl
    simp only [Befehl.auswerten, mitPc]
    omega
  | starte n =>
    simp only [Befehl.auswerten, mitPc]
  | ende =>
    simp only [Befehl.auswerten, mitPc]
  | baueArray z e c =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | liesArray b e c =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | baueTupel z t =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | liesTupelfeld b t i =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | bindeTupel q t bind =>
    simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | definiereRecord n l t =>
    simp only [Befehl.auswerten, mitPc]
  | baueRecord z n l t s =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | liesRecordFeld b n l t i =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | setzeRecordFeld q i l t ix =>
    simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | definiereVariante n l t =>
    simp only [Befehl.auswerten, mitPc]
  | baueVariante z n l t i =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | waehleVariante q n l t br =>
    simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | textLiteral z d =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | textConcat b a c =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | textIndex b c =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | substring b c =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | textLength b c =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | definiereTraeger c l t ex =>
    simp only [Befehl.auswerten, mitPc]
  | optionIstBesetzt z c =>
    simp only [Befehl.auswerten, Rahmen.schreibe, mitPc, Nat.add_assoc]
  | definiereEffektgruppe e =>
    simp only [Befehl.auswerten, mitPc]
  | waehleUmgebung n abi row =>
    simp only [Befehl.auswerten, mitPc]
  | bindeRegion r init =>
    simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | zugriff f =>
    simp only [Befehl.auswerten, mitPc]
  | faden f =>
    simp only [Befehl.auswerten, mitPc]

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
