/-
  File:      Grammatik/X86/PipelineSpillHoming.lean
  Subject:   Pipeline spills: variable homing with live-range splitting
              (lane 1227, follow-up of lane 1191 `PipelineSpill.lean`).

  Lane 1191 saves/reloads whole named slots but makes no homing decision
  and keeps whole-block live ranges. Here an untrusted homing decides, per
  variable, a private spill home slot (`heim`, parallel to the register
  allocation) plus live-range splits at statement boundaries (`schnitte`:
  variable index with its slot at that boundary). The decided validator
  (`pipeHomingOk`) reuses the accepted checks unchanged: the whole-block
  register allocation (`pipeRegAllocOk`), the spill plan over all named
  slots (`spillPlanOk`), home/register length agreement, and in-range
  split variables. The closing theorem composes the accepted pipeline
  correctness with homing privacy; a clobbering homing is refused.
-/
import Grammatik.X86.Pipeline.Kern.Pipeline
import Grammatik.X86.Pipeline.Kern.PipelineWitnesses
import Grammatik.X86.Pipeline.Kern.PipelineRegAlloc
import Grammatik.X86.Pipeline.Aufrufe.PipelineSpill

namespace Gabbro.Grammatik.X86.PipeSpillHoming

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipeRegAlloc
open Gabbro.Grammatik.X86.PipeSpill
open Gabbro.Grammatik.X86.OptimizationRules

/-- An untrusted variable homing with live-range splits: the whole-block
    register allocation, one spill home slot per variable, and split
    points naming a variable index with its slot at that boundary. -/
structure PipeSpillHoming where
  alloc : PipeRegAlloc
  heim : List Nat
  schnitte : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- Every slot the homing names: per-variable homes plus split slots. -/
def homingSlots (H : PipeSpillHoming) : List Nat :=
  H.heim ++ H.schnitte.map (fun q => q.2)

/-- THE VALIDATOR: the allocation validates, homes align with variables,
    every named slot validates as a spill plan, and every split names a
    variable in range. -/
def pipeHomingOk (H : PipeSpillHoming) (c : PipeCfg) (codeLen : Nat)
    (daten : List Nat) : Bool :=
  pipeRegAllocOk H.alloc c codeLen &&
  decide (H.alloc.belegung.length = H.heim.length) &&
  spillPlanOk H.alloc.rahmen (homingSlots H) c.codeBase codeLen daten &&
  H.schnitte.all (fun q => decide (q.1 < H.alloc.belegung.length))

/-! ## 1. Validator projections: one leg per check. -/

/-- A validated homing carries a validated register allocation. -/
theorem pipeHoming_allocOk (H : PipeSpillHoming) (c : PipeCfg)
    (codeLen : Nat) (daten : List Nat)
    (h : pipeHomingOk H c codeLen daten = true) :
    pipeRegAllocOk H.alloc c codeLen = true := by
  unfold pipeHomingOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

/-- A validated homing aligns homes with variables. -/
theorem pipeHoming_laengen (H : PipeSpillHoming) (c : PipeCfg)
    (codeLen : Nat) (daten : List Nat)
    (h : pipeHomingOk H c codeLen daten = true) :
    H.alloc.belegung.length = H.heim.length := by
  unfold pipeHomingOk at h
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1.2

/-- A validated homing carries a validated spill plan over every slot
    the homing names (homes plus split slots). -/
theorem pipeHoming_planOk (H : PipeSpillHoming) (c : PipeCfg)
    (codeLen : Nat) (daten : List Nat)
    (h : pipeHomingOk H c codeLen daten = true) :
    spillPlanOk H.alloc.rahmen (homingSlots H) c.codeBase codeLen daten = true := by
  unfold pipeHomingOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

/-- A validated homing names only in-range variables at its splits. -/
theorem pipeHoming_schnittOk (H : PipeSpillHoming) (c : PipeCfg)
    (codeLen : Nat) (daten : List Nat)
    (h : pipeHomingOk H c codeLen daten = true)
    (q : Nat × Nat) (hmem : q ∈ H.schnitte) :
    q.1 < H.alloc.belegung.length := by
  unfold pipeHomingOk at h
  simp only [Bool.and_eq_true] at h
  have hall := (List.all_eq_true.mp h.2) q hmem
  exact of_decide_eq_true hall

variable {D : Deklaration}

/-- Homing-table privacy: every named slot footprint is disjoint from
    every placed source slot footprint. -/
def HomingVonTabellenGetrennt (H : PipeSpillHoming) (L : Layout D) : Prop :=
  SpillVonTabellenGetrennt H.alloc.rahmen (homingSlots H) L

/-- A validated homing over a table-free frame is homing-private. -/
theorem pipeHoming_tabellenGetrennt (H : PipeSpillHoming) (L : Layout D)
    (c : PipeCfg) (codeLen : Nat) (daten : List Nat)
    (h : pipeHomingOk H c codeLen daten = true)
    (hrahmen : PipeRahmenGetrennt H.alloc.rahmen L) :
    HomingVonTabellenGetrennt H L :=
  spillPlan_tabellenGetrennt H.alloc.rahmen (homingSlots H) L
    c.codeBase codeLen daten (pipeHoming_planOk H c codeLen daten h) hrahmen

/-- Two distinct named slots share no byte. -/
theorem pipeHoming_schlitze_getrennt (H : PipeSpillHoming)
    (c : PipeCfg) (codeLen : Nat) (daten : List Nat)
    (h : pipeHomingOk H c codeLen daten = true)
    (i j : Nat) (hi : i ∈ homingSlots H) (hj : j ∈ homingSlots H)
    (hne : i ≠ j) :
    Disjunkt (spillSlot H.alloc.rahmen i) (spillSlot H.alloc.rahmen j) := by
  have hplan := pipeHoming_planOk H c codeLen daten h
  exact spill_schlitze_getrennt H.alloc.rahmen i j
    (spillPlan_schranke H.alloc.rahmen (homingSlots H) c.codeBase codeLen daten hplan)
    (spillPlan_inRahmen H.alloc.rahmen (homingSlots H) c.codeBase codeLen daten hplan i hi)
    (spillPlan_inRahmen H.alloc.rahmen (homingSlots H) c.codeBase codeLen daten hplan j hj)
    hne

/-! ## 2. The closing theorem: a validated homing preserves the
    source meaning and touches neither a source table nor another
    named slot.

    If the pipeline validator accepts candidate bytes under the homed
    allocation and the homing validates over a table-free frame, then
    every real source run of the block is matched by a fetched byte run
    with world and environment represented — the allocation is
    interference-free, every named slot lies disjoint from every placed
    source slot, distinct named slots are pairwise footprint-disjoint,
    and every named slot avoids every declared table extent. -/

/-- HOMING PRESERVATION: validated pipeline bytes under the homed
    allocation plus a validated homing give the fetched run with world
    and environment represented, interference freedom, slot-vs-table
    privacy, pairwise slot separation, and slot-vs-extent separation. -/
theorem pipeHoming_haelt_bedeutung (c : PipeCfg) (L : Layout D)
    (H : PipeSpillHoming)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (src : Block D V l Γ Λ Λ')
    (bytes : List Byte)
    (daten : List Nat)
    (hval : validate (pipeAllocCfg H.alloc c) L certs src bytes = true)
    (hsep : LayoutSep L)
    (hhom : pipeHomingOk H c bytes.length daten = true)
    (hrahmen : PipeRahmenGetrennt H.alloc.rahmen L)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (s : Zustand)
    (hcode : CodeAt s.speicher (natAdresse (pipeAllocCfg H.alloc c).codeBase) bytes)
    (hrip : s.rip = natAdresse (pipeAllocCfg H.alloc c).codeBase)
    (hW : WorldRep L s.speicher σ)
    (hE : EnvRepr ρ s.register (abbOf (pipeAllocCfg H.alloc c)))
    (σ' : World D) (ρ' : Env D Γ)
    (hsrc : execBlock O passes R src σ ρ = .ok σ' ρ') :
    (∃ n s', laufBytes n s = .weiter s' ∧
      s'.rip = natAdresse ((pipeAllocCfg H.alloc c).codeBase + bytes.length) ∧
      WorldRep L s'.speicher σ' ∧
      EnvRepr ρ' s'.register (abbOf (pipeAllocCfg H.alloc c))) ∧
    PipeInterferenzFrei H.alloc ∧
    HomingVonTabellenGetrennt H L ∧
    (∀ i j, i ∈ homingSlots H → j ∈ homingSlots H → i ≠ j →
      Disjunkt (spillSlot H.alloc.rahmen i) (spillSlot H.alloc.rahmen j)) ∧
    (∀ a ∈ daten, ∀ q ∈ homingSlots H,
      a + 8 ≤ H.alloc.rahmen.schlitzNat q ∨ H.alloc.rahmen.schlitzNat q + 8 ≤ a) := by
  have halloc := pipeHoming_allocOk H c bytes.length daten hhom
  have hplan := pipeHoming_planOk H c bytes.length daten hhom
  obtain ⟨n, s', hrun, hrip', hW', hE'⟩ :=
    pipeline_correct (pipeAllocCfg H.alloc c) L certs src bytes hval hsep O passes R
      σ ρ s hcode hrip hW hE σ' ρ' hsrc
  refine ⟨⟨n, s', hrun, hrip', hW', hE'⟩,
    pipe_alloc_interferenzFrei H.alloc c bytes.length halloc,
    pipeHoming_tabellenGetrennt H L c bytes.length daten hhom hrahmen, ?_, ?_⟩
  · intro i j hi hj hne
    exact pipeHoming_schlitze_getrennt H c bytes.length daten hhom i j hi hj hne
  · intro a ha q hq
    exact spillPlan_offDaten H.alloc.rahmen (homingSlots H) c.codeBase bytes.length
      daten hplan a ha q hq

/-! ## 3. Refusals: loud on every path. -/

/-- CLOBBER REFUSAL: two distinct variables in one register refuse the
    whole homing, through the allocation refusal. -/
theorem pipeHoming_verweigert_kollision (H : PipeSpillHoming) (c : PipeCfg)
    (codeLen : Nat) (daten : List Nat)
    (i j : Fin H.alloc.belegung.length) (r : Register)
    (hne : (↑i : Nat) ≠ ↑j)
    (hi : H.alloc.belegung[↑i]? = some (some r))
    (hj : H.alloc.belegung[↑j]? = some (some r)) :
    pipeHomingOk H c codeLen daten = false := by
  have halloc := pipe_alloc_verweigert_kollision H.alloc c codeLen i j r hne hi hj
  unfold pipeHomingOk
  simp [halloc]

/-- TABLE REFUSAL: a named slot overlapping a declared table extent is
    never admitted. -/
theorem pipeHoming_verweigert_tabelle (H : PipeSpillHoming) (c : PipeCfg)
    (codeLen : Nat) (daten : List Nat)
    (a : Nat) (hmem : a ∈ daten) (s : Nat) (hs : s ∈ homingSlots H)
    (h : ¬ (a + 8 ≤ H.alloc.rahmen.schlitzNat s ∨
      H.alloc.rahmen.schlitzNat s + 8 ≤ a)) :
    pipeHomingOk H c codeLen daten = false := by
  cases heq : pipeHomingOk H c codeLen daten with
  | true =>
    exact absurd (spillPlan_offDaten H.alloc.rahmen (homingSlots H) c.codeBase
      codeLen daten (pipeHoming_planOk H c codeLen daten heq) a hmem s hs) h
  | false => rfl

/-- OUT-OF-FRAME REFUSAL: a named slot past the frame is never admitted. -/
theorem pipeHoming_verweigert_aussen (H : PipeSpillHoming) (c : PipeCfg)
    (codeLen : Nat) (daten : List Nat)
    (s : Nat) (hs : s ∈ homingSlots H) (h : H.alloc.rahmen.schlitzZahl ≤ s) :
    pipeHomingOk H c codeLen daten = false := by
  cases heq : pipeHomingOk H c codeLen daten with
  | true =>
    have hlt := spillPlan_inRahmen H.alloc.rahmen (homingSlots H) c.codeBase
      codeLen daten (pipeHoming_planOk H c codeLen daten heq) s hs
    omega
  | false => rfl

/-- SPLIT REFUSAL: a split naming a variable out of range is never
    admitted. -/
theorem pipeHoming_verweigert_schnitt (H : PipeSpillHoming) (c : PipeCfg)
    (codeLen : Nat) (daten : List Nat)
    (q : Nat × Nat) (hmem : q ∈ H.schnitte)
    (h : ¬ q.1 < H.alloc.belegung.length) :
    pipeHomingOk H c codeLen daten = false := by
  cases heq : pipeHomingOk H c codeLen daten with
  | true =>
    exact absurd (pipeHoming_schnittOk H c codeLen daten heq q hmem) h
  | false => rfl

/-! ## 4. Poison probes.

    One positive probe (the witness homing validates) and one refused
    probe per validator leg: clobbered registers (through the refusal
    theorem), a home in a table extent (through the refusal theorem), a
    home past the frame (through the refusal theorem), a split naming a
    variable out of range (through the refusal theorem), and a frame
    over the code. The witness homing keeps `pipeA0` (`x` in `r10`,
    frame at 16384), homes `x` to slot 0, and splits variable 0 to
    slot 1 at the statement boundary; table extents sit at 8192/8200. -/

/-- The witness homing: `x` homed to slot 0, split of variable 0 to
    slot 1 at the statement boundary. -/
def pipeH0 : PipeSpillHoming :=
  { alloc := pipeA0, heim := [0], schnitte := [(0, 1)] }

def pipeHD0 : List Nat := [8192, 8200]

/-- POSITIVE PROBE: the witness homing validates, by computation. -/
theorem pipeHoming_probe_pos :
    pipeHomingOk pipeH0 pwCfg pwBytes.length pipeHD0 = true := by
  decide

/-- CLOBBER: two variables in `r10` are refused, through the refusal
    theorem. -/
def pipeHBadClash : PipeSpillHoming :=
  { alloc := pipeBadClash, heim := [0, 1], schnitte := [] }

theorem pipeHoming_probe_clash :
    pipeHomingOk pipeHBadClash pwCfg pwBytes.length pipeHD0 = false :=
  pipeHoming_verweigert_kollision pipeHBadClash pwCfg pwBytes.length pipeHD0
    ⟨0, by decide⟩ ⟨1, by decide⟩ .r10 (by decide) rfl rfl

/-- TABLE EXTENT: slot 0 at 16384 overlaps the declared extent 16384,
    through the refusal theorem. -/
theorem pipeHoming_probe_tabelle :
    pipeHomingOk pipeH0 pwCfg pwBytes.length [16384] = false :=
  pipeHoming_verweigert_tabelle pipeH0 pwCfg pwBytes.length [16384]
    16384 (by decide) 0 (by decide) (by decide)

/-- OUT-OF-FRAME: slot 7 past the two-slot frame is refused, through
    the refusal theorem. -/
def pipeHBadAussen : PipeSpillHoming :=
  { alloc := pipeA0, heim := [7], schnitte := [] }

theorem pipeHoming_probe_aussen :
    pipeHomingOk pipeHBadAussen pwCfg pwBytes.length pipeHD0 = false :=
  pipeHoming_verweigert_aussen pipeHBadAussen pwCfg pwBytes.length pipeHD0
    7 (by decide) (by decide)

/-- SPLIT RANGE: a split naming variable 5 of a one-variable block is
    refused, through the refusal theorem. -/
def pipeHBadSchnitt : PipeSpillHoming :=
  { alloc := pipeA0, heim := [0], schnitte := [(5, 1)] }

theorem pipeHoming_probe_schnitt :
    pipeHomingOk pipeHBadSchnitt pwCfg pwBytes.length pipeHD0 = false :=
  pipeHoming_verweigert_schnitt pipeHBadSchnitt pwCfg pwBytes.length pipeHD0
    (5, 1) (by decide) (by decide)

/-- CODE OVERLAP: a frame over the code region is refused. -/
def pipeHBadCode : PipeSpillHoming :=
  { alloc := pipeBadCode, heim := [0], schnitte := [] }

theorem pipeHoming_probe_code :
    pipeHomingOk pipeHBadCode pwCfg pwBytes.length pipeHD0 = false := by
  decide

/-! ## 5. Joint witness on a non-degenerate program.

    Every premise of `pipeHoming_haelt_bedeutung` holds jointly on the
    pipeline witness program (one variable, two slots written, check
    passed; memory 7 -> 35 and 9 -> 6, so the run is non-degenerate
    and memory-changing); the closing theorem delivers the fetched run
    plus interference freedom, homing privacy, pairwise slot
    separation and slot-vs-extent separation. -/

/-- The witness frame holds no source table byte. -/
theorem pipeH0_getrennt : PipeRahmenGetrennt pipeH0.alloc.rahmen pwL :=
  pipeA0_getrennt

/-- The witness homing keeps the witness configuration. -/
theorem pipeH0_cfg : pipeAllocCfg pipeH0.alloc pwCfg = pwCfg :=
  pipeA0_cfg

/-- JOINT WITNESS for `pipeHoming_haelt_bedeutung`: every premise holds
    jointly on the pipeline witness program with the witness homing;
    the source run changes memory (rows 7 -> 35, 9 -> 6). -/
theorem pipeHoming_haelt_bedeutung_zeuge :
    ∃ (σ' : World pwD) (ρ' : Env pwD pwCtx),
      pipeHomingOk pipeH0 pwCfg pwBytes.length pipeHD0 = true ∧
      PipeRahmenGetrennt pipeH0.alloc.rahmen pwL ∧
      validate (pipeAllocCfg pipeH0.alloc pwCfg) pwL pwCerts pwSrc pwBytes = true ∧
      LayoutSep pwL ∧
      CodeAt (pwStart 30).speicher
        (natAdresse (pipeAllocCfg pipeH0.alloc pwCfg).codeBase) pwBytes ∧
      (pwStart 30).rip = natAdresse (pipeAllocCfg pipeH0.alloc pwCfg).codeBase ∧
      WorldRep pwL (pwStart 30).speicher pwSigma ∧
      EnvRepr pwEnv30 (pwStart 30).register (abbOf (pipeAllocCfg pipeH0.alloc pwCfg)) ∧
      execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
      (pwSigma.slots () 0 ()).n = 7 ∧ (σ'.slots () 0 ()).n = 35 ∧
      (pwSigma.slots () 1 ()).n = 9 ∧ (σ'.slots () 1 ()).n = 6 ∧
      (∃ n s', laufBytes n (pwStart 30) = .weiter s' ∧
        s'.rip = natAdresse ((pipeAllocCfg pipeH0.alloc pwCfg).codeBase + pwBytes.length) ∧
        WorldRep pwL s'.speicher σ' ∧
        EnvRepr ρ' s'.register (abbOf (pipeAllocCfg pipeH0.alloc pwCfg))) ∧
      PipeInterferenzFrei pipeH0.alloc ∧
      HomingVonTabellenGetrennt pipeH0 pwL ∧
      (∀ i j, i ∈ homingSlots pipeH0 → j ∈ homingSlots pipeH0 → i ≠ j →
        Disjunkt (spillSlot pipeH0.alloc.rahmen i) (spillSlot pipeH0.alloc.rahmen j)) ∧
      (∀ a ∈ pipeHD0, ∀ q ∈ homingSlots pipeH0,
        a + 8 ≤ pipeH0.alloc.rahmen.schlitzNat q ∨
          pipeH0.alloc.rahmen.schlitzNat q + 8 ≤ a) := by
  obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pw_quelle30
  obtain ⟨hv0, hv1⟩ := pw_quelle_vorher
  have hval : validate (pipeAllocCfg pipeH0.alloc pwCfg) pwL pwCerts pwSrc pwBytes = true := by
    rw [pipeH0_cfg]
    exact pw_validate
  have hcode : CodeAt (pwStart 30).speicher
      (natAdresse (pipeAllocCfg pipeH0.alloc pwCfg).codeBase) pwBytes := by
    rw [pipeH0_cfg]
    exact pw_code
  have hrip : (pwStart 30).rip =
      natAdresse (pipeAllocCfg pipeH0.alloc pwCfg).codeBase := by
    rw [pipeH0_cfg]
    rfl
  have hE : EnvRepr pwEnv30 (pwStart 30).register
      (abbOf (pipeAllocCfg pipeH0.alloc pwCfg)) := by
    rw [pipeH0_cfg]
    exact pw_envRepr30
  obtain ⟨⟨n, s', hrun, hrip', hW, hE'⟩, hfrei, hpriv, hsep2, hdat⟩ :=
    pipeHoming_haelt_bedeutung pwCfg pwL pipeH0 pwCerts pwSrc pwBytes pipeHD0 hval
      pw_layoutSep pipeHoming_probe_pos pipeH0_getrennt pwO 0 pwR
      pwSigma pwEnv30 (pwStart 30) hcode hrip pw_worldRep hE σ' ρ' hsrc
  exact ⟨σ', ρ', pipeHoming_probe_pos, pipeH0_getrennt, hval, pw_layoutSep, hcode,
    hrip, pw_worldRep, hE, hsrc, hv0, h0, hv1, h1,
    ⟨n, s', hrun, hrip', hW, hE'⟩, hfrei, hpriv, hsep2, hdat⟩

/- CUTS:
    - Proved here: untrusted variable homing with live-range splits
      (`PipeSpillHoming`: whole-block register allocation, one spill
      home slot per variable, split points naming a variable index with
      its slot at that boundary); every slot the homing names
      (`homingSlots`: homes plus split slots); the decided validator
      (`pipeHomingOk`: validated allocation, home/variable length
      agreement, validated spill plan over every named slot, in-range
      split variables) with one projection per leg; homing-table
      privacy over an arbitrary layout (`HomingVonTabellenGetrennt`,
      `pipeHoming_tabellenGetrennt`); pairwise slot separation
      (`pipeHoming_schlitze_getrennt`); the closing composition of
      validated pipeline bytes under the homed allocation with a
      validated homing (`pipeHoming_haelt_bedeutung` via
      `pipeline_correct` plus the accepted allocator and spill legs);
      general refusals for clobbered registers, table extent,
      out-of-frame slot and out-of-range split; one positive and five
      refusal probes (clash, table, out-of-frame and split through
      their refusal theorems); joint non-degenerate witness on the
      pipeline witness program (`pipeHoming_haelt_bedeutung_zeuge`:
      rows 7 -> 35, 9 -> 6).
    - OPEN / not claimed: interleaved save/reload lowering at split
      points (the homing decides homes; no bytes are inserted at the
      boundaries here — the accepted `spillSaveCode`/`spillLoadCode`
      fragments of lane 1191 are the lowering vocabulary a splitter
      would splice, and combining them needs the allocator's
      working-register freshness, which this validator takes from the
      reused `pipeRegAllocOk` rather than re-checking); liveness finer
      than per-variable homes (a variable keeps one home slot plus its
      split slots; overlapping live ranges of two variables in one
      slot are refused by the plan `Nodup`, never merged); callee-saved
      restore and argument passing (no calls in the fragment, inherited
      from the pipeline); TSO freshness of home slots beyond the reused
      `SpillFrisch` vocabulary (`ComposeSpillPrivacy.lean` owns the
      composed level); read-trace representation (inherited from the
      pipeline); full loaded-image connection
      (`pipeline_correct_loaded` shape, not re-proved here).
    - The refusal `Bool` is validator admission, never a hardware fault.
    - No second IR and no second evaluator: only the accepted pipeline
      lowering, validator and machine vocabulary are reused.
-/

#print axioms PipeSpillHoming
#print axioms homingSlots
#print axioms pipeHomingOk
#print axioms pipeHoming_allocOk
#print axioms pipeHoming_laengen
#print axioms pipeHoming_planOk
#print axioms pipeHoming_schnittOk
#print axioms HomingVonTabellenGetrennt
#print axioms pipeHoming_tabellenGetrennt
#print axioms pipeHoming_schlitze_getrennt
#print axioms pipeHoming_haelt_bedeutung
#print axioms pipeHoming_verweigert_kollision
#print axioms pipeHoming_verweigert_tabelle
#print axioms pipeHoming_verweigert_aussen
#print axioms pipeHoming_verweigert_schnitt
#print axioms pipeH0
#print axioms pipeHD0
#print axioms pipeHoming_probe_pos
#print axioms pipeHBadClash
#print axioms pipeHoming_probe_clash
#print axioms pipeHoming_probe_tabelle
#print axioms pipeHBadAussen
#print axioms pipeHoming_probe_aussen
#print axioms pipeHBadSchnitt
#print axioms pipeHoming_probe_schnitt
#print axioms pipeHBadCode
#print axioms pipeHoming_probe_code
#print axioms pipeH0_getrennt
#print axioms pipeH0_cfg
#print axioms pipeHoming_haelt_bedeutung_zeuge

end Gabbro.Grammatik.X86.PipeSpillHoming
