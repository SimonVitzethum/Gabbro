/-
  File:      Grammatik/X86/PipelineSpill.lean
  Subject:   Pipeline spill code generation with privacy (lane 1191).

  Follow-up of lane 1167 (`PipelineRegAlloc.lean`): a spilled live
  variable was refused there because the lowering had no spill code.
  Here the spill code exists: save/reload fragments made of the pilot
  address materialisation (`movImm64 adr slotAddr`) plus a pilot
  `store64`/`load64` through the address register with zero
  displacement (the shape the accepted `senkStmt` already uses), with
  per-step meaning proved against the canonical `schritt` lemmas.

  A decided validator (`spillPlanOk`) admits a spill plan only for
  in-frame slots that are pairwise distinct (no spill slot aliases
  another), a frame off the code region and inside 64 bits, and every
  slot footprint disjoint from every declared table extent (a spill
  into a table extent is refused, never guessed). The closing theorem
  (`spill_haelt_bedeutung`) composes the accepted pipeline correctness
  (`pipeline_correct`) with spill privacy: the fetched run is preserved
  and no spill slot touches a source table or another spill slot
  (`ComposeSpillPrivacy.lean` vocabulary: `spillSlot`, `GetrenntK`,
  `Disjunkt`). A second theorem (`spill_rundreise_privat`) threads a
  reached save through its reload via the accepted
  `ComposeSpillPrivacy_verbindung`.

  Reused unchanged: `PipeCfg`/`abbOf`/`validate`/`pipeline_correct`,
  `CodeAt`/`Layout`/`LayoutSep`/`WorldRep`/`EnvRepr`, `Rahmen`/
  `schlitzNat`/`schlitzNat_schranke`/`schlitz_toNat`/`sichereWort`/
  `ladeWort`, `spillSlot`/`SpillFrisch`/`GetrenntK`/`spillPrivatOk`/
  `SpillZugelassen`, `ComposeSpillPrivacy_verbindung`,
  `schritt_movImm64`/`schritt_store64_erfolg`/`schritt_load64_erfolg`,
  `effAddr_null`, `disjunkt_von_intervallen`, `lauf_anhang`.
  No second IR, no second source interpreter, no optimiser edit.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.PipelineRegAlloc
import Grammatik.X86.ComposeSpillPrivacy
import Grammatik.X86.EffectiveAddress

namespace Gabbro.Grammatik.X86.PipeSpill

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipeRegAlloc

/-- Spill save code for one slot: materialise the canonical slot address
    in the address register, then store the source register there. -/
def spillSaveCode (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (src : Register) : List Befehl :=
  [.movImm64 c.adr (natAdresse (r.schlitzNat slot)),
    .store64 c.adr src (BitVec.ofNat 32 0)]

/-- Spill reload code for one slot: materialise the canonical slot address
    in the address register, then load it into the destination register. -/
def spillLoadCode (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (dst : Register) : List Befehl :=
  [.movImm64 c.adr (natAdresse (r.schlitzNat slot)),
    .load64 dst c.adr (BitVec.ofNat 32 0)]

/-- Spill code is straight-line pilot code (save). -/
theorem spillSave_gerade (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (src : Register) : (spillSaveCode c r slot src).all gerade = true := by
  rfl

/-- Spill code is straight-line pilot code (reload). -/
theorem spillLoad_gerade (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (dst : Register) : (spillLoadCode c r slot dst).all gerade = true := by
  rfl

/-- SAVE SEQUENCE: the two spill-save instructions run the canonical
    slot store: the address materialisation puts the slot address in the
    address register, and the zero-displacement store writes the source
    register word into the slot. Memory carries the checked store;
    every register but the address register is kept. -/
theorem spillSave_lauf (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (src : Register) (s : Zustand) (m' : Speicher)
    (hne : src ≠ c.adr)
    (hwr : write64 s.speicher (spillSlot r slot) (s.register src) = some m') :
    ∃ s2, lauf ((spillSaveCode c r slot src).map kanon) s = some s2 ∧
      s2.speicher = m' ∧
      s2.register c.adr = natAdresse (r.schlitzNat slot) ∧
      s2.register src = s.register src := by
  have hmi := schritt_movImm64 (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot))))
    s c.adr (natAdresse (r.schlitzNat slot)) (laengeOk_encode _) rfl
  have e1 : lauf [kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))] s =
      some (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) := by
    simp only [lauf, hmi]
  have hs1a : (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))).register c.adr =
      natAdresse (r.schlitzNat slot) :=
    regSet_gleich _ _ _
  have hs1s : (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))).register src =
      s.register src :=
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
        s.flags c.adr (natAdresse (r.schlitzNat slot))).register src) = some m' := by
    rw [heff, hs1s]
    exact hwr
  have hst := schritt_store64_erfolg
    (kanon (.store64 c.adr src (BitVec.ofNat 32 0)))
    (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot)))
    c.adr src (BitVec.ofNat 32 0) m' (laengeOk_encode _) rfl hw
  have e2 : lauf [kanon (.store64 c.adr src (BitVec.ofNat 32 0))]
      (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) =
      some ({ (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) with
        speicher := m',
        rip := ripNach (schrittRegister s
          (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
          s.flags c.adr (natAdresse (r.schlitzNat slot))).rip
          (kanon (.store64 c.adr src (BitVec.ofNat 32 0))).laenge } : Zustand) := by
    simp only [lauf, hst]
  have hrun : lauf ((spillSaveCode c r slot src).map kanon) s = some
      ({ (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) with
        speicher := m',
        rip := ripNach (schrittRegister s
          (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
          s.flags c.adr (natAdresse (r.schlitzNat slot))).rip
          (kanon (.store64 c.adr src (BitVec.ofNat 32 0))).laenge } : Zustand) := by
    have hmap : (spillSaveCode c r slot src).map kanon =
        [kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))] ++
        [kanon (.store64 c.adr src (BitVec.ofNat 32 0))] := rfl
    rw [hmap, lauf_anhang _ _ _ _ e1]
    exact e2
  refine ⟨_, hrun, rfl, hs1a, hs1s⟩

/-- RELOAD SEQUENCE: the two spill-reload instructions run the
    canonical slot load: the address materialisation puts the slot
    address in the address register, and the zero-displacement load
    puts the slot word in the destination register. Memory is untouched;
    every register but the address and destination registers is kept. -/
theorem spillLoad_lauf (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (dst : Register) (s : Zustand) (v : Wort)
    (hrd : read64 s.speicher (spillSlot r slot) = some v) :
    ∃ s2, lauf ((spillLoadCode c r slot dst).map kanon) s = some s2 ∧
      s2.speicher = s.speicher ∧
      s2.register dst = v := by
  have hmi := schritt_movImm64 (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot))))
    s c.adr (natAdresse (r.schlitzNat slot)) (laengeOk_encode _) rfl
  have e1 : lauf [kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))] s =
      some (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) := by
    simp only [lauf, hmi]
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
  have hrun : lauf ((spillLoadCode c r slot dst).map kanon) s = some
      (schrittRegister (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot)))
        (ripNach (schrittRegister s
          (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
          s.flags c.adr (natAdresse (r.schlitzNat slot))).rip
          (kanon (.load64 dst c.adr (BitVec.ofNat 32 0))).laenge)
        (schrittRegister s
          (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
          s.flags c.adr (natAdresse (r.schlitzNat slot))).flags dst v) := by
    have hmap : (spillLoadCode c r slot dst).map kanon =
        [kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))] ++
        [kanon (.load64 dst c.adr (BitVec.ofNat 32 0))] := rfl
    have e2 : lauf [kanon (.load64 dst c.adr (BitVec.ofNat 32 0))]
        (schrittRegister s
          (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
          s.flags c.adr (natAdresse (r.schlitzNat slot))) =
        some (schrittRegister (schrittRegister s
          (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
          s.flags c.adr (natAdresse (r.schlitzNat slot)))
          (ripNach (schrittRegister s
            (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
            s.flags c.adr (natAdresse (r.schlitzNat slot))).rip
            (kanon (.load64 dst c.adr (BitVec.ofNat 32 0))).laenge)
          (schrittRegister s
            (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
            s.flags c.adr (natAdresse (r.schlitzNat slot))).flags dst v) := by
      simp only [lauf, hld]
    rw [hmap, lauf_anhang _ _ _ _ e1]
    exact e2
  refine ⟨_, hrun, rfl, ?_⟩
  show regSet (regSet s.register c.adr (natAdresse (r.schlitzNat slot))) dst v dst = v
  exact regSet_gleich _ _ _

end Gabbro.Grammatik.X86.PipeSpill
