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
open Gabbro.Grammatik.X86.PipeRegAlloc
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

/-! ## 4. Paired save/reload round-trip across an explicit middle
    segment.

    A save spliced before a middle segment and its reload after it
    carry the register value through the slot. The middle segment's
    non-interference (its run, and slot-byte preservation across it)
    is an explicit premise on explicit states, in the established
    token style: discharging it is the allocator/homing layer's job
    (lane 1227's homing is not merged here, see CUTS). -/

/-- PAIRED ROUND-TRIP: prefix runs, the save stores the register word
    in the slot, the middle segment runs and keeps the slot bytes, the
    reload restores the saved word into the register, the suffix runs.
    The save keeps every register but the address register. -/
theorem spleiss_paar_rundreise (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (reg : Register)
    (pre mid post : List Befehl)
    (s t1 t1m t2 t3 u : Zustand) (m' : Speicher)
    (hne : reg ≠ c.adr)
    (hslot : slot < r.schlitzZahl)
    (hpre : lauf (pre.map kanon) s = some t1)
    (hwr : write64 t1.speicher (spillSlot r slot) (t1.register reg) = some m')
    (hrd : lesbar8 t1.speicher (spillSlot r slot) = true)
    (hsave : lauf ((spillSaveCode c r slot reg).map kanon) t1 = some t1m)
    (hmid : lauf (mid.map kanon) t1m = some t2)
    (hslotmid : read64 t2.speicher (spillSlot r slot) =
      read64 m' (spillSlot r slot))
    (hload : lauf ((spillLoadCode c r slot reg).map kanon) t2 = some t3)
    (hpost : lauf (post.map kanon) t3 = some u) :
    lauf (((pre ++ spillSaveCode c r slot reg) ++ mid ++
      spillLoadCode c r slot reg ++ post).map kanon) s = some u ∧
      t3.register reg = t1.register reg ∧
      t3.speicher = t2.speicher ∧
      (∀ q, q ≠ c.adr → t1m.register q = t1.register q) := by
  have hsw : sichereWort t1.speicher r slot (t1.register reg) = some m' := by
    unfold sichereWort
    rw [if_pos hslot]
    exact hwr
  have hround : ladeWort m' r slot = some (t1.register reg) :=
    sichere_lade_rundreise _ _ _ _ _ hslot hsw hrd
  have hrdm : read64 m' (spillSlot r slot) = some (t1.register reg) := by
    unfold ladeWort at hround
    rw [if_pos hslot] at hround
    exact hround
  have hrd2 : read64 t2.speicher (spillSlot r slot) =
      some (t1.register reg) := by
    rw [hslotmid]
    exact hrdm
  obtain ⟨s2, hs2run, hs2mem, hs2reg⟩ :=
    spillLoad_lauf c r slot reg t2 (t1.register reg) hrd2
  cases Option.some_inj.mp (hs2run.symm.trans hload)
  have hmap1 : ((pre ++ spillSaveCode c r slot reg) ++ mid ++
      spillLoadCode c r slot reg ++ post).map kanon =
      (pre.map kanon) ++ ((spillSaveCode c r slot reg ++ mid ++
        spillLoadCode c r slot reg ++ post).map kanon) := by
    simp [List.map_append, List.append_assoc]
  have hmap2 : (spillSaveCode c r slot reg ++ mid ++
      spillLoadCode c r slot reg ++ post).map kanon =
      ((spillSaveCode c r slot reg).map kanon) ++
        ((mid ++ spillLoadCode c r slot reg ++ post).map kanon) := by
    simp [List.map_append, List.append_assoc]
  have hmap3 : (mid ++ spillLoadCode c r slot reg ++ post).map kanon =
      (mid.map kanon) ++
        ((spillLoadCode c r slot reg ++ post).map kanon) := by
    simp [List.map_append, List.append_assoc]
  have hmap4 : (spillLoadCode c r slot reg ++ post).map kanon =
      ((spillLoadCode c r slot reg).map kanon) ++ (post.map kanon) := by
    simp [List.map_append]
  have hrun : lauf (((pre ++ spillSaveCode c r slot reg) ++ mid ++
      spillLoadCode c r slot reg ++ post).map kanon) s = some u := by
    rw [hmap1, lauf_anhang _ _ _ _ hpre, hmap2,
      lauf_anhang _ _ _ _ hsave, hmap3, lauf_anhang _ _ _ _ hmid,
      hmap4, lauf_anhang _ _ _ _ hload]
    exact hpost
  refine ⟨hrun, hs2reg, hs2mem, ?_⟩
  intro q hq
  exact spleiss_save_fremd c r slot reg t1 t1m m' hne hwr hsave q hq

variable {D : Deklaration}

/-! ## 5. The closing theorem: the spliced lowering preserves the
    source meaning and the privacy of the frame.

    Validated pipeline bytes give the fetched run with world and
    environment represented (lane 1191's `spill_haelt_bedeutung`,
    itself over `pipeline_correct`); the validated splice plan adds
    slot-vs-table privacy, pairwise slot separation, slot-vs-extent
    separation, and per-point fragment facts (straight-line, in-frame
    slot, no save onto the address register). -/

/-- SPLICE PRESERVATION: validated pipeline bytes plus a validated
    splice plan give the fetched run with world and environment
    represented, slot-vs-table privacy, pairwise slot separation,
    slot-vs-extent separation, and per-point fragment admission. -/
theorem spleiss_haelt_bedeutung (c : PipeCfg) (L : Layout D)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (src : Block D V l Γ Λ Λ')
    (bytes : List Byte)
    (r : Rahmen) (P : List Befehl) (pts : List SpleissPunkt)
    (daten : List Nat)
    (hval : validate c L certs src bytes = true)
    (hsep : LayoutSep L)
    (hplan : spillPlanOk r (pts.map (·.schlitz)) c.codeBase bytes.length
      daten = true)
    (hspleiss : spleissPlanOk c r P pts c.codeBase bytes.length daten = true)
    (hrahmen : PipeRahmenGetrennt r L)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (s : Zustand)
    (hcode : CodeAt s.speicher (natAdresse c.codeBase) bytes)
    (hrip : s.rip = natAdresse c.codeBase)
    (hW : WorldRep L s.speicher σ)
    (hE : EnvRepr ρ s.register (abbOf c))
    (σ' : World D) (ρ' : Env D Γ)
    (hsrc : execBlock O passes R src σ ρ = .ok σ' ρ') :
    (∃ n s', laufBytes n s = .weiter s' ∧
      s'.rip = natAdresse (c.codeBase + bytes.length) ∧
      WorldRep L s'.speicher σ' ∧
      EnvRepr ρ' s'.register (abbOf c)) ∧
    SpillVonTabellenGetrennt r (pts.map (·.schlitz)) L ∧
    (∀ i j, i ∈ (pts.map (·.schlitz)) → j ∈ (pts.map (·.schlitz)) →
      i ≠ j → Disjunkt (spillSlot r i) (spillSlot r j)) ∧
    (∀ a ∈ daten, ∀ q ∈ (pts.map (·.schlitz)),
      a + 8 ≤ r.schlitzNat q ∨ r.schlitzNat q + 8 ≤ a) ∧
    (∀ p ∈ pts, (spleissFrag c r p).all gerade = true ∧
      p.schlitz < r.schlitzZahl ∧
      (p.richtung = .sichern → p.reg ≠ c.adr)) := by
  obtain ⟨hrun, hpriv, hsep2, hdat⟩ :=
    spill_haelt_bedeutung c L certs src bytes r (pts.map (·.schlitz))
      daten hval hsep hplan hrahmen O passes R σ ρ s hcode hrip hW hE
      σ' ρ' hsrc
  have hspill : spillPlanOk r (pts.map (·.schlitz)) c.codeBase bytes.length
      daten = true :=
    spleissPlan_spill c r P pts c.codeBase bytes.length daten hspleiss
  refine ⟨hrun, hpriv, hsep2, hdat, ?_⟩
  intro p hp
  refine ⟨spleissFrag_gerade c r p, ?_, ?_⟩
  · exact spillPlan_inRahmen r (pts.map (·.schlitz)) c.codeBase
      bytes.length daten hspill p.schlitz (List.mem_map.mpr ⟨p, hp, rfl⟩)
  · intro hdir
    exact spleissPlan_saveReg c r P pts c.codeBase bytes.length daten
      hspleiss p hp hdir

/-! ## 6. Callee-saved and argument handling, consistent with
    `PipelineCalls`.

    The `Stapel` layout puts spills at bare indices below `b.spill`,
    callee-saved words behind them, stack-passed arguments last.
    Callee-saved saves ARE lane 1191 spill fragments at the reserved
    callee indices (the canonical slot address is the same
    `spillSlot`); every spill slot is proved disjoint from every
    callee-saved slot (`spill_gerettet_getrennt`) and every
    stack-argument slot (`bereich_getrennt`), and stack-passed
    arguments are in-frame (`rufOk_argSchranke`). -/

/-- THE CALL-SPLICE VALIDATOR: an admitted call layout (`rufOk`:
    frame fit, 64-bit top, exact stack-word count, six callee-saved
    words, no red zone) with an admitted spill plan whose slots all
    live at bare spill indices below `b.spill`. -/
def spleissRufOk (b : Belegung) (r : Rahmen) (slots : List Nat)
    (nArgs : Nat) (benutztRot : Bool) (codeBase codeLen : Nat)
    (daten : List Nat) : Bool :=
  rufOk b r nArgs benutztRot &&
  spillPlanOk r slots codeBase codeLen daten &&
  slots.all (fun s => decide (s < b.spill))

/-- The call layout is admitted. -/
theorem spleissRuf_ruf (b : Belegung) (r : Rahmen) (slots : List Nat)
    (nArgs : Nat) (benutztRot : Bool) (codeBase codeLen : Nat)
    (daten : List Nat)
    (h : spleissRufOk b r slots nArgs benutztRot codeBase codeLen daten
      = true) :
    rufOk b r nArgs benutztRot = true := by
  unfold spleissRufOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- The spill plan is admitted. -/
theorem spleissRuf_spill (b : Belegung) (r : Rahmen) (slots : List Nat)
    (nArgs : Nat) (benutztRot : Bool) (codeBase codeLen : Nat)
    (daten : List Nat)
    (h : spleissRufOk b r slots nArgs benutztRot codeBase codeLen daten
      = true) :
    spillPlanOk r slots codeBase codeLen daten = true := by
  unfold spleissRufOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

/-- Every spill slot lives at a bare spill index. -/
theorem spleissRuf_unten (b : Belegung) (r : Rahmen) (slots : List Nat)
    (nArgs : Nat) (benutztRot : Bool) (codeBase codeLen : Nat)
    (daten : List Nat)
    (h : spleissRufOk b r slots nArgs benutztRot codeBase codeLen daten
      = true)
    (s : Nat) (hs : s ∈ slots) : s < b.spill := by
  unfold spleissRufOk at h
  simp only [Bool.and_eq_true] at h
  have hall := (List.all_eq_true.mp h.2) s hs
  exact of_decide_eq_true hall

/-- SPILL VS CALLEE-SAVED: no spill slot shares a byte with a
    callee-saved slot. -/
theorem spleissRuf_spillGerettet (b : Belegung) (r : Rahmen)
    (slots : List Nat) (nArgs : Nat) (benutztRot : Bool)
    (codeBase codeLen : Nat) (daten : List Nat)
    (h : spleissRufOk b r slots nArgs benutztRot codeBase codeLen daten
      = true)
    (s : Nat) (hs : s ∈ slots) (j : Nat) (hj : j < b.gerettet) :
    Disjunkt (spillSlot r s) (spillSlot r (b.gerettetIdx j)) := by
  have hr := spleissRuf_ruf b r slots nArgs benutztRot codeBase codeLen
    daten h
  obtain ⟨hp, hle, -, -, -⟩ := rufOk_teile b r nArgs benutztRot hr
  have hpasst : b.braucht * 8 ≤ r.tiefe := by
    unfold Belegung.passt at hp
    exact of_decide_eq_true hp
  have hb : s < b.spill := spleissRuf_unten b r slots nArgs benutztRot
    codeBase codeLen daten h s hs
  exact spill_gerettet_getrennt b r s j hb hj hpasst hle

/-- SPILL VS STACK ARGUMENTS: no spill slot shares a byte with a
    stack-passed argument slot. -/
theorem spleissRuf_spillStapel (b : Belegung) (r : Rahmen)
    (slots : List Nat) (nArgs : Nat) (benutztRot : Bool)
    (codeBase codeLen : Nat) (daten : List Nat)
    (h : spleissRufOk b r slots nArgs benutztRot codeBase codeLen daten
      = true)
    (s : Nat) (hs : s ∈ slots) (j : Nat) (hj : j < b.stapelArgs) :
    Disjunkt (spillSlot r s) (spillSlot r (b.stapelArgIdx j)) := by
  have hr := spleissRuf_ruf b r slots nArgs benutztRot codeBase codeLen
    daten h
  obtain ⟨hp, hle, -, -, -⟩ := rufOk_teile b r nArgs benutztRot hr
  have hpasst : b.braucht * 8 ≤ r.tiefe := by
    unfold Belegung.passt at hp
    exact of_decide_eq_true hp
  have hb : s < b.spill := spleissRuf_unten b r slots nArgs benutztRot
    codeBase codeLen daten h s hs
  have hbb : b.spill + b.gerettet + b.stapelArgs ≤ r.schlitzZahl := by
    unfold Belegung.braucht at hpasst
    unfold Rahmen.schlitzZahl
    omega
  unfold Belegung.stapelArgIdx
  exact bereich_getrennt r 0 b.spill (b.spill + b.gerettet)
    (b.spill + b.gerettet + b.stapelArgs) s (b.spill + b.gerettet + j)
    (Nat.zero_le _) hb (by omega) (by omega) (Or.inl (by omega))
    (by omega) hbb hle

/-- SPILL VS STACK-PASSED ARGUMENT: at call-argument position `i ≥ 6`
    the stack slot is disjoint from every spill slot. -/
theorem spleissRuf_spillArg (b : Belegung) (r : Rahmen)
    (slots : List Nat) (nArgs : Nat) (benutztRot : Bool)
    (codeBase codeLen : Nat) (daten : List Nat)
    (h : spleissRufOk b r slots nArgs benutztRot codeBase codeLen daten
      = true)
    (s : Nat) (hs : s ∈ slots) (i : Nat) (hi : i < nArgs) (h6 : 6 ≤ i) :
    Disjunkt (spillSlot r s) (r.schlitzAddr (argStapelIdx b i)) := by
  have hr := spleissRuf_ruf b r slots nArgs benutztRot codeBase codeLen
    daten h
  obtain ⟨-, -, hfit, -, -⟩ := rufOk_teile b r nArgs benutztRot hr
  have hj : i - 6 < b.stapelArgs := by omega
  have hdis := spleissRuf_spillStapel b r slots nArgs benutztRot codeBase
    codeLen daten h s hs (i - 6) hj
  have heq : argStapelIdx b i = b.stapelArgIdx (i - 6) := rfl
  rw [heq]
  exact hdis

/-- Every callee-saved register has an in-frame slot. -/
theorem spleissRuf_rettetAlle (b : Belegung) (r : Rahmen)
    (slots : List Nat) (nArgs : Nat) (benutztRot : Bool)
    (codeBase codeLen : Nat) (daten : List Nat)
    (h : spleissRufOk b r slots nArgs benutztRot codeBase codeLen daten
      = true)
    (k : Nat) (hk : k < calleeGerettet.length) :
    b.gerettetIdx k < r.schlitzZahl := by
  have hr := spleissRuf_ruf b r slots nArgs benutztRot codeBase codeLen
    daten h
  obtain ⟨hp, -, -, hg, -⟩ := rufOk_teile b r nArgs benutztRot hr
  have hpasst : b.braucht * 8 ≤ r.tiefe := by
    unfold Belegung.passt at hp
    exact of_decide_eq_true hp
  have hbb : b.spill + b.gerettet + b.stapelArgs ≤ r.schlitzZahl := by
    unfold Belegung.braucht at hpasst
    unfold Rahmen.schlitzZahl
    omega
  rw [calleeGerettet_sechs] at hk
  unfold Belegung.gerettetIdx
  omega

/-- ARGUMENT CARRIAGE: argument `i` travels in a register (`i < 6`)
    or on the stack in-frame (`6 ≤ i`). -/
theorem spleissRuf_argTraeger (b : Belegung) (r : Rahmen)
    (slots : List Nat) (nArgs : Nat) (benutztRot : Bool)
    (codeBase codeLen : Nat) (daten : List Nat)
    (h : spleissRufOk b r slots nArgs benutztRot codeBase codeLen daten
      = true)
    (i : Nat) (hi : i < nArgs) :
    (∃ rg, argReg i = some rg) ∨
      (6 ≤ i ∧ argStapelIdx b i < r.schlitzZahl) := by
  have hr := spleissRuf_ruf b r slots nArgs benutztRot codeBase codeLen
    daten h
  rcases Nat.lt_or_ge i 6 with h6 | h6
  · left
    have h5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases h5 with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.rdi, by decide⟩
    · exact ⟨.rsi, by decide⟩
    · exact ⟨.rdx, by decide⟩
    · exact ⟨.rcx, by decide⟩
    · exact ⟨.r8, by decide⟩
    · exact ⟨.r9, by decide⟩
  · right
    exact ⟨h6, rufOk_argSchranke b r nArgs benutztRot i hi h6 hr⟩

/-- Callee-saved save fragment at the reserved callee index: a lane
    1191 save at the `Belegung` slot. -/
def rufRettFrag (c : PipeCfg) (r : Rahmen) (b : Belegung) (i : Nat)
    (reg : Register) : List Befehl :=
  spillSaveCode c r (b.gerettetIdx i) reg

/-- Callee-saved reload fragment at the reserved callee index. -/
def rufHolFrag (c : PipeCfg) (r : Rahmen) (b : Belegung) (i : Nat)
    (reg : Register) : List Befehl :=
  spillLoadCode c r (b.gerettetIdx i) reg

theorem rufRettFrag_gerade (c : PipeCfg) (r : Rahmen) (b : Belegung)
    (i : Nat) (reg : Register) :
    (rufRettFrag c r b i reg).all gerade = true :=
  spillSave_gerade c r (b.gerettetIdx i) reg

theorem rufHolFrag_gerade (c : PipeCfg) (r : Rahmen) (b : Belegung)
    (i : Nat) (reg : Register) :
    (rufHolFrag c r b i reg).all gerade = true :=
  spillLoad_gerade c r (b.gerettetIdx i) reg

/-- CALLEE-SAVED SAVE RUNS: the reserved slot receives the register
    word through the canonical slot store. -/
theorem rufRett_lauf (c : PipeCfg) (r : Rahmen) (b : Belegung) (i : Nat)
    (reg : Register) (s : Zustand) (m' : Speicher)
    (hne : reg ≠ c.adr)
    (hwr : write64 s.speicher (spillSlot r (b.gerettetIdx i))
      (s.register reg) = some m') :
    ∃ s2, lauf ((rufRettFrag c r b i reg).map kanon) s = some s2 ∧
      s2.speicher = m' ∧
      s2.register c.adr = natAdresse (r.schlitzNat (b.gerettetIdx i)) ∧
      s2.register reg = s.register reg :=
  spillSave_lauf c r (b.gerettetIdx i) reg s m' hne hwr

/-- CALLEE-SAVED RELOAD RUNS: the reserved slot word reaches the
    register through the canonical slot load. -/
theorem rufHol_lauf (c : PipeCfg) (r : Rahmen) (b : Belegung) (i : Nat)
    (reg : Register) (s : Zustand) (v : Wort)
    (hrd : read64 s.speicher (spillSlot r (b.gerettetIdx i)) = some v) :
    ∃ s2, lauf ((rufHolFrag c r b i reg).map kanon) s = some s2 ∧
      s2.speicher = s.speicher ∧
      s2.register reg = v :=
  spillLoad_lauf c r (b.gerettetIdx i) reg s v hrd

/- CUTS:
     - Skeleton only: split-point type and fragment selection over the
       accepted 1191 fragments. Run lemmas, multi-splice, validator,
       closing, call handling, refusals, probes and witnesses OPEN.
-/

#print axioms SpleissPunkt
#print axioms spleissFrag

end Gabbro.Grammatik.X86.PipeSpillSplice
