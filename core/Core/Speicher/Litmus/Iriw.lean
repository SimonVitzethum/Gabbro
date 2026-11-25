/-
  File:      core/Core/Speicher/Litmus/Iriw.lean
  Subject:   IRIW litmus group: independent reads of independent writes as a catalogue entry. This
             module does not rebuild the graph or the proofs: it imports the pinned statements and
             their proofs from `Core/Ziel/Korrektheit/Beweise/Iriw.lean` and joins them under one
             group root, adding only the completeness of the release/acquire witness.

  Source: Lahav et al., "Repairing Sequential Consistency in C/C++11" (PLDI 2017), the IRIW test;
  Batty et al., "Mathematizing C++ Concurrency" (POPL 2011); the herd/C11 catalogue (`IRIW`).

  Modes: every access `.sc` (forbidden half), release/acquire `.ra` (allowed half). Below `seq_cst`
  the two readers may disagree on the order of two independent writes.

  Expected: FORBIDDEN with `seq_cst` (`IriwScVerbotenAussage`, proved by `iriw_sc_verboten`),
  ALLOWED with release/acquire (`IriwRaErlaubtAussage`, proved by `iriw_ra_erlaubt`, and the
  completeness-bearing `IriwRaVollstaendigErlaubtAussage` below). No model deviation.
-/
module

public import Core.Ziel.Korrektheit.Beweise.Iriw

@[expose] public section

namespace Gabbro.Core.Speicher

open Gabbro.Core.Ziel.Korrektheit

/-- The release/acquire IRIW witness is complete: each of its four reads has a reads-from source. -/
theorem ir_vollstaendig : (irGraph .ra).Vollstaendig := by
  intro r hr
  cases r with
  | irIX => exact (hr : False).elim
  | irIY => exact (hr : False).elim
  | irWX => exact (hr : False).elim
  | irWY => exact (hr : False).elim
  | irR1X => exact ⟨irWX, by show irRf irWX irR1X; decide⟩
  | irR1Y => exact ⟨irIY, by show irRf irIY irR1Y; decide⟩
  | irR2Y => exact ⟨irWY, by show irRf irWY irR2Y; decide⟩
  | irR2X => exact ⟨irIX, by show irRf irIX irR2X; decide⟩

/-- **The allowed half in catalogue form:** a consistent and complete graph in which the two
    readers disagree on the independent writes. The graph, its consistency proof and its four
    accesses are those of `iriw_ra_erlaubt`; only `Vollstaendig` (`ir_vollstaendig`) is added. -/
def IriwRaVollstaendigErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧ G.Vollstaendig ∧
      ∃ wx wy r1x r1y r2y r2x : E,
        G.rf wx r1x ∧ G.po r1x r1y ∧ G.rb r1y wy ∧
        G.rf wy r2y ∧ G.po r2y r2x ∧ G.rb r2x wx

theorem iriw_ra_vollstaendig_erlaubt : IriwRaVollstaendigErlaubtAussage := by
  have hf₁ : (irGraph .ra).rf irWX irR1X := by
    show irRf irWX irR1X
    decide
  have hp₁ : (irGraph .ra).po irR1X irR1Y := by
    show irPo irR1X irR1Y
    decide
  have hrb₁ : (irGraph .ra).rb irR1Y irWY :=
    ⟨irIY, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inr ⟨rfl, rfl⟩, by decide⟩
  have hf₂ : (irGraph .ra).rf irWY irR2Y := by
    show irRf irWY irR2Y
    decide
  have hp₂ : (irGraph .ra).po irR2Y irR2X := by
    show irPo irR2Y irR2X
    decide
  have hrb₂ : (irGraph .ra).rb irR2X irWX :=
    ⟨irIX, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), Or.inl ⟨rfl, rfl⟩, by decide⟩
  exact ⟨IriwEv, Bool, Nat, irGraph .ra, ir_konsistent, ir_vollstaendig,
    irWX, irWY, irR1X, irR1Y, irR2Y, irR2X, hf₁, hp₁, hrb₁, hf₂, hp₂, hrb₂⟩

/-- **The IRIW group root.** The forbidden and the allowed statements are the pinned ones from
    `Core/Ziel/Korrektheit/Speicher.lean`, with their proofs imported, not redefined. -/
def IriwLitmusAussage : Prop :=
  IriwScVerbotenAussage ∧ IriwRaErlaubtAussage ∧ IriwRaVollstaendigErlaubtAussage

theorem iriw_litmus : IriwLitmusAussage :=
  ⟨iriw_sc_verboten, iriw_ra_erlaubt, iriw_ra_vollstaendig_erlaubt⟩

end Gabbro.Core.Speicher
