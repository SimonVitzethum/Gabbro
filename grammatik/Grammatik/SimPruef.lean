/-
  File:      Grammatik/SimPruef.lean
  Subject:   THE STAGE-(b) SIMULATION-CERTIFICATE CHECKER FOR 124
              (`beispiele/124-two-threads-private.gab`):
              the Rust printer (`crates/gabbro-check/src/corrcert.rs`,
              `SimCert124`) prints the per-thread position tables of the
              simulation relation `R124` (`Schlusssatz124.lean`); this file
              checks the printed tables against `R124`'s own functions
              (`pruefeSim`) and turns a checked certificate into a
              simulation WHOSE RELATION IS READ FROM THE CERTIFICATE
              (`R124c c`, `simpruef_liefert`, `r124c_eq`). What the
              certificate decides is the relation; the per-step G segments
              (`gBlatt`, `gNimm`, `gSetze`, `gGib`, `gPruefe`) and the step
              cases `schrittA`/`schrittB` stay hand-proved for `R124`: the
              checker covers the relation tables, not the segments (named
              gap for program #2, see CUTS).
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
    2026-09-21, G01). Until fix lane F8, `pruefeSim` compared the printed
    certificate with these four literals, and nothing tied them to
    `gOfA`/`heldGA`/`gOfB`/`heldGB`: a typo in both the Rust and the Lean
    literal passed (it happened, `gB[7]`). `pruefeSim` now compares with the
    functions directly; the literals stay as the Rust printer's mirror
    (`SimCert124::erwartet_*`). Positions `0..12` (A) and `0..8` (B), residues `0..6` and `0..4`;
    a held-lock flag is the number of locks the residue holds. -/
theorem erwartet_ist_r124 :
    erwartetGA = (List.range 13).map gOfA ∧
    erwartetHA = (List.range 7).map (fun r => (heldGA r).length) ∧
    erwartetGB = (List.range 9).map gOfB ∧
    erwartetHB = (List.range 5).map (fun r => (heldGB r).length) := by
  decide

/-- **The checker**: the printed tables are the tables of `R124` -- compared
    with `gOfA`/`heldGA`/`gOfB`/`heldGB` themselves (fix lane F8), not with a
    second hand-typed copy. -/
def pruefeSim (c : SimCert) : Bool :=
  decide (c.gA = (List.range 13).map gOfA ∧
    c.hA = (List.range 7).map (fun r => (heldGA r).length) ∧
    c.gB = (List.range 9).map gOfB ∧
    c.hB = (List.range 5).map (fun r => (heldGB r).length))

/-- A checked certificate carries the expected tables. -/
theorem simpruef_tab (c : SimCert) (h : pruefeSim c = true) :
    c.gA = erwartetGA ∧ c.hA = erwartetHA ∧ c.gB = erwartetGB ∧ c.hB = erwartetHB := by
  obtain ⟨hA, hHA, hB, hHB⟩ := of_decide_eq_true h
  obtain ⟨eA, eHA, eB, eHB⟩ := erwartet_ist_r124
  exact ⟨hA.trans eA.symm, hHA.trans eHA.symm, hB.trans eB.symm, hHB.trans eHB.symm⟩

/-! ### The relation READ FROM the certificate

The simulation that `simpruef_liefert` hands out is NOT `R124` with the
certificate beside it: its relation `R124c c` is built from the
certificate's four tables (`c.gA`/`c.gB` give the G residue of each C
position, `c.hA`/`c.hB` the number of locks each residue holds). The
checker is what makes that relation a simulation: a checked certificate's
relation IS `R124` (`r124c_eq`), and only then do `r124_start` and the
step cases `schrittA`/`schrittB` apply. A wrong table (review 2026-09-21
integration: `gB[7] = 3` instead of `4`) fails `pruefeSim`
(`pruefeSim_falsch`), and its relation relates the C position 7 of
`hauptB` to the G residue 3, which is not the residue the proved steps
reach (`r124c_falsch_anders`). -/

/-- The G residue of C position `i` according to a table. -/
def tabG (tab : List Nat) (i : Nat) : Nat := tab.getD i 0

/-- The locks a residue holds according to a flag table: `n` copies of `L`. -/
def tabH (tab : List Nat) (r : Nat) : List DR.Lock := List.replicate (tab.getD r 0) lL

/-- `ThreadA` with the certificate's tables in place of `gOfA`/`heldGA`. -/
def ThreadAc (c : SimCert) (x : CFaden) (z : RufFadenG DR) : Prop :=
  ∃ (i : Nat) (sp : List (Ereignis DR)) (log : List (RufEreignisF DR)), i ≤ 12 ∧ x = posA i ∧
    z = ⟨[], frA (tabG c.gA i), sp, log⟩ ∧ offen sp = tabH c.hA (tabG c.gA i)

/-- `ThreadB` with the certificate's tables in place of `gOfB`/`heldGB`. -/
def ThreadBc (c : SimCert) (x : CFaden) (z : RufFadenG DR) : Prop :=
  ∃ (i : Nat) (sp : List (Ereignis DR)) (log : List (RufEreignisF DR)), i ≤ 8 ∧ x = posB i ∧
    z = ⟨[], frB (tabG c.gB i), sp, log⟩ ∧ offen sp = tabH c.hB (tabG c.gB i)

def FadenRelc (c : SimCert) : Option Nat → CFaden → RufFadenG DR → Prop
  | some 2, x, z => ThreadAc c x z
  | some 3, x, z => ThreadBc c x z
  | _, x, _ => x = .aus

/-- **The simulation relation read from a certificate**: `R124` with the
    four tables replaced by the certificate's. -/
def R124c (c : SimCert) (w : Faden → Option Nat) (K : KonfC) (M : RufMaschineG DR) : Prop :=
  corrW kEL (M.speicher.welt []) K.st ∧ SperrRel K M ∧
    ∀ t, FadenRelc c (w t) (K.faeden t) (M.faeden t)

theorem tabG_A (i : Nat) (hi : i ≤ 12) : tabG ((List.range 13).map gOfA) i = gOfA i := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _
  | 12, _ => rfl

theorem tabG_B (i : Nat) (hi : i ≤ 8) : tabG ((List.range 9).map gOfB) i = gOfB i := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ => rfl

theorem tabH_A (r : Nat) : tabH ((List.range 7).map (fun r => (heldGA r).length)) r = heldGA r := by
  match r with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => rfl
  | n + 7 =>
      have h : ((List.range 7).map (fun r => (heldGA r).length)).getD (n + 7) 0 = 0 := by
        simp [List.getD_eq_getElem?_getD]
      unfold tabH
      rw [h]
      unfold heldGA
      split <;> simp_all

theorem tabH_B (r : Nat) : tabH ((List.range 5).map (fun r => (heldGB r).length)) r = heldGB r := by
  match r with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | n + 5 =>
      have h : ((List.range 5).map (fun r => (heldGB r).length)).getD (n + 5) 0 = 0 := by
        simp [List.getD_eq_getElem?_getD]
      unfold tabH
      rw [h]
      unfold heldGB
      split <;> simp_all

/-- **A checked certificate's relation IS `R124`.** This is the only way
    the certificate reaches the simulation, and the only place `pruefeSim`
    is used for it. -/
theorem r124c_eq (c : SimCert) (h : pruefeSim c = true) (w : Faden → Option Nat) :
    R124c c w = R124 w := by
  obtain ⟨hA, hHA, hB, hHB⟩ := of_decide_eq_true h
  have eA : ∀ x z, ThreadAc c x z ↔ ThreadA x z := by
    intro x z
    unfold ThreadAc ThreadA
    rw [hA, hHA]
    constructor
    · rintro ⟨i, sp, log, hi, hx, hz, ho⟩
      exact ⟨i, sp, log, hi, hx, by rw [hz, tabG_A i hi], by rw [ho, tabG_A i hi, tabH_A]⟩
    · rintro ⟨i, sp, log, hi, hx, hz, ho⟩
      exact ⟨i, sp, log, hi, hx, by rw [hz, tabG_A i hi], by rw [ho, tabG_A i hi, tabH_A]⟩
  have eB : ∀ x z, ThreadBc c x z ↔ ThreadB x z := by
    intro x z
    unfold ThreadBc ThreadB
    rw [hB, hHB]
    constructor
    · rintro ⟨i, sp, log, hi, hx, hz, ho⟩
      exact ⟨i, sp, log, hi, hx, by rw [hz, tabG_B i hi], by rw [ho, tabG_B i hi, tabH_B]⟩
    · rintro ⟨i, sp, log, hi, hx, hz, ho⟩
      exact ⟨i, sp, log, hi, hx, by rw [hz, tabG_B i hi], by rw [ho, tabG_B i hi, tabH_B]⟩
  have eF : ∀ o x z, FadenRelc c o x z ↔ FadenRel o x z := by
    intro o x z
    match o with
    | some 2 => exact eA x z
    | some 3 => exact eB x z
    | none => exact Iff.rfl
    | some 0 => exact Iff.rfl
    | some 1 => exact Iff.rfl
    | some (n + 4) => exact Iff.rfl
  funext K M
  apply propext
  unfold R124c R124
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun t => (eF _ _ _).1 (h3 t)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun t => (eF _ _ _).2 (h3 t)⟩

/-- **The checked result**: a simulation whose relation is the one read
    from the certificate, plus the checked table facts. -/
structure SimPruefErg (c : SimCert) (w : Faden → Option Nat) (passes : Nat) where
  sim : SimC c124 (startC c124 w st0) kEL lnr PR OR passes (M0 w)
  rel : sim.R = R124c c w
  tabA : c.gA = erwartetGA
  tabHA : c.hA = erwartetHA
  tabB : c.gB = erwartetGB
  tabHB : c.hB = erwartetHB

/-- **A checked certificate yields the simulation, with the certificate's
    relation**: `R := R124c c w`. Its start and step obligations are
    discharged by transporting along `r124c_eq` (which needs the check) to
    `r124_start` and the proved step cases `schrittA`/`schrittB` of
    `sim124`. Named premises: the runtime's root assignment is well-formed
    (`Wurzeln`); `DRFSC`/`LaufzeitC` enter only at `schlusssatz_124_bei`.
    What stays hand-fed: the per-step G segments (`gBlatt`, `gNimm`,
    `gSetze`, `gGib`, `gPruefe`) inside `schrittA`/`schrittB` -- the
    certificate names the relation, not the segments. A `def` because the
    package lives in `Type`. -/
def simpruef_liefert (c : SimCert) (w : Faden → Option Nat) (hw : Wurzeln w)
    (h : pruefeSim c = true) (passes : Nat) : SimPruefErg c w passes :=
  let e := r124c_eq c h w
  let S : SimC c124 (startC c124 w st0) kEL lnr PR OR passes (M0 w) :=
    { R := R124c c w
      start := by rw [e]; exact r124_start w hw
      schritt := fun K M t ℓ K' hK hM hR hs => by
        rw [e] at hR ⊢
        exact (sim124 passes w hw).schritt K M t ℓ K' hK hM hR hs }
  let ⟨hA, hHA, hB, hHB⟩ := simpruef_tab c h
  ⟨S, rfl, hA, hHA, hB, hHB⟩

/-- The printed certificate for 124, exactly as the Rust printer emits it
    (`SimCert124::to_lean` in `crates/gabbro-check/src/corrcert.rs`). -/
def cert124_printed : SimCert :=
  ⟨[0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 6, 6], [0, 0, 0, 1, 1, 0, 0],
   [0, 0, 1, 1, 2, 2, 3, 4, 4], [0, 0, 1, 1, 0]⟩

/-- The integration finding of 2026-09-21 as a certificate: `gB[7] = 3`. -/
def cert124_falsch : SimCert :=
  ⟨[0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 6, 6], [0, 0, 0, 1, 1, 0, 0],
   [0, 0, 1, 1, 2, 2, 3, 3, 4], [0, 0, 1, 1, 0]⟩

/-- **The checker refuses it.** -/
theorem pruefeSim_falsch : pruefeSim cert124_falsch = false := by decide

/-- **And its relation is not `R124`'s**: at C position 7 of `hauptB` it
    names residue 3, where `R124` names residue 4 (the residue after
    `setze`, which the proved step `k_setze` reaches). -/
theorem r124c_falsch_anders :
    tabG cert124_falsch.gB 7 = 3 ∧ gOfB 7 = 4 := ⟨rfl, rfl⟩

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
      st0.mem (.tab 1) 0 = .int 0 ∧
      ∃ M, RufErreichbarG PR OR 0 (M0 wAB) M ∧ R124c cert124_printed wAB Kf M := by
  have hc : pruefeSim cert124_printed = true := by decide
  refine ⟨hc, wAB_wurzeln, ?_⟩
  obtain ⟨_, _, _, _, _, Kf, _, _, _, _, _, _, hKf, hf0, hf1, hfr, hmem, h7, hstart⟩ :=
    schlusssatz_124_zeuge
  let E := simpruef_liefert cert124_printed wAB wAB_wurzeln hc 0
  obtain ⟨M, hM, hR⟩ := sim_erreichbar E.sim hKf
  exact ⟨Kf, hKf, hf0, hf1, hfr, hmem, h7, hstart, M, hM, E.rel ▸ hR⟩

/-
CUTS: what this file does not do, by name.
- The certificate decides the RELATION (`R124c c`), and the checker proves
  that relation equal to `R124` (`r124c_eq`); the simulation obligations of
  that relation are then the hand-proved `r124_start`/`schrittA`/`schrittB`.
  So a wrong table is caught (`pruefeSim_falsch`: the integration finding
  `gB[7] = 3`), but a certificate cannot teach the checker a relation it
  does not already have a proof for. The per-step G segments (`gBlatt`,
  `gNimm`, `gSetze`, `gGib`, `gPruefe`) and the per-position case splits
  stay hand-fed. What carries over to program #2: the shape (`SimCert`
  tables, `R124c`-style relation read from them, the JSON/Lean printer).
  What does NOT carry over: any proof -- program #2 needs a checker that
  establishes `SegPasst` per C step from the certificate (a segment per
  position), which this file does not have.
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
#print axioms Gabbro.Grammatik.r124c_eq
#print axioms Gabbro.Grammatik.simpruef_liefert
#print axioms Gabbro.Grammatik.pruefeSim_falsch
#print axioms Gabbro.Grammatik.r124c_falsch_anders
