/-
  File:      Grammatik/SimPruef.lean
  Subject:   THE STAGE-(b) SIMULATION-CERTIFICATE CHECKER FOR 124
              (`beispiele/124-two-threads-private.gab`):
              the Rust printer (`crates/gabbro-check/src/corrcert.rs`,
              `SimCert124`) prints the per-thread position tables of the
              simulation relation `R124` (`Schlusssatz124.lean`); this file
              checks the printed tables (`pruefeSim`) and turns a checked
              certificate into the simulation (`sim124`-shape,
              `simpruef_liefert`). The per-step G segments (`gBlatt`,
              `gNimm`, `gSetze`, `gGib`, `gPruefe`) stay hand-fed: the
              checker covers the relation tables, not the segments
              (named gap for program #2, see CUTS).
-/
import Grammatik.Schlusssatz124

namespace Gabbro.Grammatik

open K124

/-- The printed simulation certificate for 124: the C-position to G-residue
    maps (`gOfA`, `gOfB`) and the held-lock flags (`heldGA`, `heldGB`) as
    data. `hA`/`hB` are `1` where the residue holds `lL`, else `0`. -/
structure SimCert where
  gA : List Nat
  hA : List Nat
  gB : List Nat
  hB : List Nat

/-- The expected tables, read off `gOfA`/`heldGA`/`gOfB`/`heldGB`. -/
def erwartetGA : List Nat := [0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 6, 6]
def erwartetHA : List Nat := [0, 0, 0, 1, 1, 0, 0]
def erwartetGB : List Nat := [0, 0, 1, 1, 2, 2, 3, 4, 4]
def erwartetHB : List Nat := [0, 0, 1, 1, 0]

/-- **The expected tables ARE the relation tables of `R124`** (review
    2026-09-21, G01): without this link `pruefeSim` compares the printed
    certificate with four literals that nothing ties to `gOfA`/`heldGA`/
    `gOfB`/`heldGB`, and a typo in both the Rust and the Lean literal would
    pass. Positions `0..12` (A) and `0..8` (B), residues `0..6` and `0..4`;
    a held-lock flag is the number of locks the residue holds. -/
theorem erwartet_ist_r124 :
    erwartetGA = (List.range 13).map gOfA ∧
    erwartetHA = (List.range 7).map (fun r => (heldGA r).length) ∧
    erwartetGB = (List.range 9).map gOfB ∧
    erwartetHB = (List.range 5).map (fun r => (heldGB r).length) := by
  decide

/-- **The checker**: the printed tables equal the expected ones. -/
def pruefeSim (c : SimCert) : Bool :=
  decide (c.gA = erwartetGA ∧ c.hA = erwartetHA ∧ c.gB = erwartetGB ∧ c.hB = erwartetHB)

/-- A checked certificate carries the expected tables. -/
theorem simpruef_tab (c : SimCert) (h : pruefeSim c = true) :
    c.gA = erwartetGA ∧ c.hA = erwartetHA ∧ c.gB = erwartetGB ∧ c.hB = erwartetHB :=
  of_decide_eq_true h

/-- **The checked result**: the simulation plus the checked table facts. -/
structure SimPruefErg (c : SimCert) (w : Faden → Option Nat) (passes : Nat) where
  sim : SimC c124 (startC c124 w st0) kEL lnr PR OR passes (M0 w)
  tabA : c.gA = erwartetGA
  tabHA : c.hA = erwartetHA
  tabB : c.gB = erwartetGB
  tabHB : c.hB = erwartetHB

/-- **A checked certificate yields the simulation** (`sim124`-shape) together
    with the checked table facts. Named premises: the runtime's root
    assignment is well-formed (`Wurzeln`); `DRFSC`/`LaufzeitC` enter only at
    `schlusssatz_124_bei`, not here. A `def` (not a `theorem`) because the
    package lives in `Type`. -/
def simpruef_liefert (c : SimCert) (w : Faden → Option Nat) (hw : Wurzeln w)
    (h : pruefeSim c = true) (passes : Nat) : SimPruefErg c w passes := by
  obtain ⟨hA, hHA, hB, hHB⟩ := simpruef_tab c h
  exact ⟨sim124 passes w hw, hA, hHA, hB, hHB⟩

/-- The printed certificate for 124, exactly as the Rust printer emits it
    (`SimCert124::to_lean` in `crates/gabbro-check/src/corrcert.rs`). -/
def cert124_printed : SimCert :=
  ⟨[0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 6, 6], [0, 0, 0, 1, 1, 0, 0],
   [0, 0, 1, 1, 2, 2, 3, 4, 4], [0, 0, 1, 1, 0]⟩

/-- **WITNESS** (rule 13): the checker premises instantiated JOINTLY on the
    non-degenerate two-thread program 124 -- the printed certificate checks,
    the runtime starts both roots, and the reached configuration `Kf` moved
    memory (`privA[0]` was `0` at the start, is `7` there: a memory-changing
    step lies on the run). -/
theorem simpruef_124_zeuge :
    pruefeSim cert124_printed = true ∧ Wurzeln wAB ∧
    ∃ Kf : KonfC, ErreichbarC c124 sperrAbstrakt KAB Kf ∧
      Kf.faeden 0 = .aus ∧ Kf.faeden 1 = .aus ∧ Kf.halter 0 = none ∧
      Kf.st.mem (.tab 0) 0 = Kf.st.mem (.tab 0) 4 ∧ Kf.st.mem (.tab 1) 0 = .int 7 ∧
      st0.mem (.tab 1) 0 = .int 0 := by
  refine ⟨by decide, wAB_wurzeln, ?_⟩
  obtain ⟨_, _, _, _, _, Kf, _, _, _, _, _, _, hKf, hf0, hf1, hfr, hmem, h7, hstart⟩ :=
    schlusssatz_124_zeuge
  exact ⟨Kf, hKf, hf0, hf1, hfr, hmem, h7, hstart⟩

/-
CUTS: what this file does not do, by name.
- The checker covers the relation TABLES of 124 only (`gOfA`/`heldGA`/
  `gOfB`/`heldGB` as data). The per-step G segments (`gBlatt`, `gNimm`,
  `gSetze`, `gGib`, `gPruefe`) and the per-position case splits
  (`schrittA`, `schrittB`) stay hand-fed through `sim124`: a certificate
  for program #2 needs checked segments (`SegPasst` per step), not just
  checked tables.
- The C unit `c124` and the G program `kP` are the hand transcriptions of
  `Schlusssatz124.lean`/`Korpus124.lean` (no Lean C parser, exporter
  refuses 124); the checker does not re-establish them.
- `DRFSC` and `LaufzeitC` are named premises of `schlusssatz_124_bei`,
  not checked here.
-/

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.simpruef_tab
#print axioms Gabbro.Grammatik.erwartet_ist_r124
#print axioms Gabbro.Grammatik.simpruef_124_zeuge
