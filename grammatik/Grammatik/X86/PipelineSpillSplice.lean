/-
  File:      Grammatik/X86/PipelineSpillSplice.lean
  Subject:   Pipeline spills: splice save/reload at split points,
             callee-saved and argument handling (lane 1257).

  Follow-up of lane 1191 (`PipelineSpill.lean`): the save/reload
  fragments exist there but no bytes are spliced at split points, and
  calls/callee-saved/argument passing are not covered. Here a split
  point names a position in the lowered program with a slot, a
  register and a direction; splicing inserts the 1191 fragment there.
  The closing theorem preserves the source meaning and the privacy of
  the frame; callee-saved/argument handling reuses `PipelineCalls`
  (`rufOk`, `calleeGerettet`, `rufParam_orte`) over the `Stapel`
  layout (`Belegung`: spills at bare indices, callee-saved behind
  them, stack arguments last).

  Reused unchanged: `spillSaveCode`/`spillLoadCode`/`spillSave_lauf`/
  `spillLoad_lauf`/`spillPlanOk` and its legs/`spill_schlitze_getrennt`/
  `spill_haelt_bedeutung`, `pipeline_correct`, `rufOk`/`rufOk_teile`/
  `rufParam_orte`/`calleeGerettet`/`rufOk_argSchranke`/`rufOk_getrennt`,
  `spill_gerettet_getrennt`/`bereich_getrennt`, `lauf_anhang`.
  No second IR, no second source interpreter, no optimiser edit.
-/
import Grammatik.X86.PipelineSpill
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.PipelineCalls

namespace Gabbro.Grammatik.X86.PipeSpillSplice

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipeSpill
open Gabbro.Grammatik.X86.PipelineCalls

/-- Splice direction: save the register into the slot, or reload the
    slot into the register. -/
inductive SpleissRichtung where
  | sichern | laden
  deriving DecidableEq, Repr

/-- A split point: position in the lowered program, spill slot,
    register saved/reloaded, direction. -/
structure SpleissPunkt where
  pos : Nat
  schlitz : Nat
  reg : Register
  richtung : SpleissRichtung
  deriving DecidableEq, Repr

/-- The fragment spliced at a split point: lane 1191's save/reload
    code for the point's slot and register. -/
def spleissFrag (c : PipeCfg) (r : Rahmen) (p : SpleissPunkt) : List Befehl :=
  match p.richtung with
  | .sichern => spillSaveCode c r p.schlitz p.reg
  | .laden => spillLoadCode c r p.schlitz p.reg

/-! ## 1. Single splice: shape and straight-line fragments. -/

/-- SINGLE SPLICE: insert the point's fragment at its position. -/
def spleissEins (c : PipeCfg) (r : Rahmen) (P : List Befehl)
    (p : SpleissPunkt) : List Befehl :=
  (P.take p.pos) ++ spleissFrag c r p ++ (P.drop p.pos)

/-- Shape of a single splice: prefix, fragment, suffix. -/
theorem spleissEins_gestalt (c : PipeCfg) (r : Rahmen) (P : List Befehl)
    (p : SpleissPunkt) :
    spleissEins c r P p =
      (P.take p.pos) ++ spleissFrag c r p ++ (P.drop p.pos) := rfl

/-- Every spliced fragment is straight-line pilot code. -/
theorem spleissFrag_gerade (c : PipeCfg) (r : Rahmen) (p : SpleissPunkt) :
    (spleissFrag c r p).all gerade = true := by
  rcases p with ⟨pos, schlitz, reg, richtung⟩
  cases richtung
  · simp only [spleissFrag]
    exact spillSave_gerade c r schlitz reg
  · simp only [spleissFrag]
    exact spillLoad_gerade c r schlitz reg

/-- A reached whole run splits at any prefix: the prefix reaches an
    intermediate state the suffix continues from. -/
theorem lauf_praefix (A B : List Decodiert) (s u : Zustand)
    (h : lauf (A ++ B) s = some u) :
    ∃ t, lauf A s = some t ∧ lauf B t = some u := by
  induction A generalizing s with
  | nil => exact ⟨s, rfl, by simpa using h⟩
  | cons d rest ih =>
    simp only [List.cons_append, lauf] at h
    cases hst : schritt d s with
    | none => simp [hst] at h
    | some t =>
      simp [hst] at h
      obtain ⟨m, hm1, hm2⟩ := ih _ h
      exact ⟨m, by simp [lauf, hst, hm1], hm2⟩

/-! ## 2. Exact clobber sets: a save touches only the address
    register, a reload only the address and destination registers.
    Every other register keeps its value along any reached fragment
    run. The run itself is lane 1191's (`spillSave_lauf`,
    `spillLoad_lauf`); what is new here is the full preservation. -/

/-- SAVE CLOBBER: along any reached save run, every register but the
    address register is kept. -/
theorem spleiss_save_fremd (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (reg : Register) (s s2 : Zustand) (m' : Speicher)
    (hne : reg ≠ c.adr)
    (hwr : write64 s.speicher (spillSlot r slot) (s.register reg) = some m')
    (hrun : lauf ((spillSaveCode c r slot reg).map kanon) s = some s2)
    (q : Register) (hq : q ≠ c.adr) :
    s2.register q = s.register q := by
  have hmi := schritt_movImm64 (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot))))
    s c.adr (natAdresse (r.schlitzNat slot)) (laengeOk_encode _) rfl
  have hmap : (spillSaveCode c r slot reg).map kanon =
      [kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))] ++
      [kanon (.store64 c.adr reg (BitVec.ofNat 32 0))] := rfl
  rw [hmap] at hrun
  have e1 : lauf [kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))] s =
      some (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) := by
    simp only [lauf, hmi]
  obtain ⟨mid, hmid, hrun2⟩ := lauf_praefix _ _ _ _ hrun
  rw [e1] at hmid
  cases hmid
  have hs1a : (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))).register c.adr =
      natAdresse (r.schlitzNat slot) :=
    regSet_gleich _ _ _
  have hs1s : (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))).register reg =
      s.register reg :=
    regSet_fremd _ _ _ _ hne
  have heff : effAddr (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))) c.adr
      (BitVec.ofNat 32 0) = spillSlot r slot := by
    rw [effAddr_null, hs1a]
    rfl
  have hw : write64 (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))).speicher
      (effAddr (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) c.adr (BitVec.ofNat 32 0))
      ((schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))).register reg) = some m' := by
    rw [heff, hs1s]
    exact hwr
  have hst := schritt_store64_erfolg
    (kanon (.store64 c.adr reg (BitVec.ofNat 32 0)))
    (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot)))
    c.adr reg (BitVec.ofNat 32 0) m' (laengeOk_encode _) rfl hw
  simp only [lauf, hst] at hrun2
  cases hrun2
  exact regSet_fremd _ _ _ _ hq

/-- RELOAD CLOBBER: along any reached reload run, every register but
    the address and destination registers is kept. -/
theorem spleiss_load_fremd (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (dst : Register) (s s2 : Zustand) (v : Wort)
    (hrd : read64 s.speicher (spillSlot r slot) = some v)
    (hrun : lauf ((spillLoadCode c r slot dst).map kanon) s = some s2)
    (q : Register) (hq : q ≠ c.adr) (hqd : q ≠ dst) :
    s2.register q = s.register q := by
  have hmi := schritt_movImm64 (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot))))
    s c.adr (natAdresse (r.schlitzNat slot)) (laengeOk_encode _) rfl
  have hmap : (spillLoadCode c r slot dst).map kanon =
      [kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))] ++
      [kanon (.load64 dst c.adr (BitVec.ofNat 32 0))] := rfl
  rw [hmap] at hrun
  have e1 : lauf [kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))] s =
      some (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) := by
    simp only [lauf, hmi]
  obtain ⟨mid, hmid, hrun2⟩ := lauf_praefix _ _ _ _ hrun
  rw [e1] at hmid
  cases hmid
  have hs1a : (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))).register c.adr =
      natAdresse (r.schlitzNat slot) :=
    regSet_gleich _ _ _
  have heff : effAddr (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))) c.adr
      (BitVec.ofNat 32 0) = spillSlot r slot := by
    rw [effAddr_null, hs1a]
    rfl
  have hrd2 : read64 (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))).speicher
      (effAddr (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) c.adr
        (BitVec.ofNat 32 0)) = some v := by
    rw [heff]
    exact hrd
  have hld := schritt_load64_erfolg
    (kanon (.load64 dst c.adr (BitVec.ofNat 32 0)))
    (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot)))
    dst c.adr (BitVec.ofNat 32 0) v (laengeOk_encode _) rfl hrd2
  simp only [lauf, hld] at hrun2
  cases hrun2
  show regSet (regSet s.register c.adr (natAdresse (r.schlitzNat slot))) dst v q =
    s.register q
  rw [regSet_fremd _ _ _ _ hqd]
  exact regSet_fremd _ _ _ _ hq

/-! ## 3. Multi-splice over sorted split points, and the validator.

    Segments of the original program with each point's fragment
    inserted at its position; `verbraucht` counts original
    instructions already emitted. Positions are original-program
    positions, so strictly ascending positions keep every segment
    well formed. -/

/-- MULTI-SPLICE segments over sorted points. -/
def spleissSeg (c : PipeCfg) (r : Rahmen) (P : List Befehl)
    (pts : List SpleissPunkt) (verbraucht : Nat) : List Befehl :=
  match pts with
  | [] => P.drop verbraucht
  | p :: rest =>
    ((P.drop verbraucht).take (p.pos - verbraucht)) ++ spleissFrag c r p ++
      spleissSeg c r P rest p.pos

/-- Multi-splice of a whole program: no instruction consumed yet. -/
def spleissMehr (c : PipeCfg) (r : Rahmen) (P : List Befehl)
    (pts : List SpleissPunkt) : List Befehl :=
  spleissSeg c r P pts 0

/-- Decided strictly ascending positions. -/
def spleissSortiert : List SpleissPunkt → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a.pos < b.pos) && spleissSortiert (b :: rest)

/-- THE SPLICE VALIDATOR: lane 1191's plan over the splice slots, plus
    every position inside the program, strictly ascending positions,
    and no save onto the address register (lane 1191's save needs
    `src ≠ adr`; a reload may target any register). -/
def spleissPlanOk (c : PipeCfg) (r : Rahmen) (P : List Befehl)
    (pts : List SpleissPunkt) (codeBase codeLen : Nat)
    (daten : List Nat) : Bool :=
  spillPlanOk r (pts.map (·.schlitz)) codeBase codeLen daten &&
  (pts.all fun p => decide (p.pos ≤ P.length)) &&
  spleissSortiert pts &&
  (pts.all fun p => match p.richtung with
    | .sichern => decide (p.reg ≠ c.adr)
    | .laden => true)

/-- The 1191 plan over the splice slots holds. -/
theorem spleissPlan_spill (c : PipeCfg) (r : Rahmen) (P : List Befehl)
    (pts : List SpleissPunkt) (codeBase codeLen : Nat) (daten : List Nat)
    (h : spleissPlanOk c r P pts codeBase codeLen daten = true) :
    spillPlanOk r (pts.map (·.schlitz)) codeBase codeLen daten = true := by
  unfold spleissPlanOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

/-- Every split position lies inside the program. -/
theorem spleissPlan_pos (c : PipeCfg) (r : Rahmen) (P : List Befehl)
    (pts : List SpleissPunkt) (codeBase codeLen : Nat) (daten : List Nat)
    (h : spleissPlanOk c r P pts codeBase codeLen daten = true)
    (p : SpleissPunkt) (hmem : p ∈ pts) : p.pos ≤ P.length := by
  unfold spleissPlanOk at h
  simp only [Bool.and_eq_true] at h
  have hall := (List.all_eq_true.mp h.1.1.2) p hmem
  exact of_decide_eq_true hall

/-- The points are strictly ascending. -/
theorem spleissPlan_sortiert (c : PipeCfg) (r : Rahmen) (P : List Befehl)
    (pts : List SpleissPunkt) (codeBase codeLen : Nat) (daten : List Nat)
    (h : spleissPlanOk c r P pts codeBase codeLen daten = true) :
    spleissSortiert pts = true := by
  unfold spleissPlanOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

/-- No save targets the address register. -/
theorem spleissPlan_saveReg (c : PipeCfg) (r : Rahmen) (P : List Befehl)
    (pts : List SpleissPunkt) (codeBase codeLen : Nat) (daten : List Nat)
    (h : spleissPlanOk c r P pts codeBase codeLen daten = true)
    (p : SpleissPunkt) (hmem : p ∈ pts) (hdir : p.richtung = .sichern) :
    p.reg ≠ c.adr := by
  unfold spleissPlanOk at h
  simp only [Bool.and_eq_true] at h
  have hall := (List.all_eq_true.mp h.2) p hmem
  cases hrt : p.richtung with
  | sichern =>
    rw [hrt] at hall
    exact of_decide_eq_true hall
  | laden =>
    rw [hrt] at hdir
    exact absurd hdir (by decide)

/-- Empty plan: the program is unchanged. -/
theorem spleissMehr_nil (c : PipeCfg) (r : Rahmen) (P : List Befehl) :
    spleissMehr c r P [] = P := rfl

/-- Single point: prefix, fragment, suffix. -/
theorem spleissMehr_einz (c : PipeCfg) (r : Rahmen) (P : List Befehl)
    (p : SpleissPunkt) :
    spleissMehr c r P [p] =
      (P.take p.pos) ++ spleissFrag c r p ++ (P.drop p.pos) := by
  simp [spleissMehr, spleissSeg]

/- CUTS:
     - Skeleton only: split-point type and fragment selection over the
       accepted 1191 fragments. Run lemmas, multi-splice, validator,
       closing, call handling, refusals, probes and witnesses OPEN.
-/

#print axioms SpleissPunkt
#print axioms spleissFrag

end Gabbro.Grammatik.X86.PipeSpillSplice
