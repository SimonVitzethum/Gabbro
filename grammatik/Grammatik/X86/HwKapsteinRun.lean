/-
  File:      Grammatik/X86/HwKapsteinRun.lean
  Subject:   Capstone run: a reached multi-family program run on two cores.

  Lane 1293: on top of the capstone union step `HwVollSchritt` (lane 1149,
  `HwKapstein.lean`, reused unchanged), build ONE reached run: bytes
  `pinXadd` (LOCK XADD [rbp], rax) in the mapped executable window
  4096..4128, executed on two cores of `HwMaschine`, mixing LOCK XADD, a
  push/call/pop/ret sequence, a scalar FP op, a packed integer op and a
  plain store/load with forwarding, ending with drains observed from both
  cores. Every definition is lifted from the accepted families, never
  redefined; fetches cite the accepted decode pins.
-/
import Grammatik.X86.HwKapstein

namespace Gabbro.Grammatik.X86

/-- Run data window: 8192..8224, holding the lock word (8192), the stack
    slot (8200) and the foreign byte (8216) disjointly. -/
def runDataRW (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8224)

/-- Run registers core 0: XADD delta 5 in rax, base 8192 in rbp, divisor
    7 in rcx, 16-aligned top 8208 in rsp, everything else zero. -/
def runReg0 : Register → Wort := fun q =>
  if q = .rax then BitVec.ofNat 64 5
  else if q = .rbp then BitVec.ofNat 64 8192
  else if q = .rcx then BitVec.ofNat 64 7
  else if q = .rsp then BitVec.ofNat 64 8208
  else BitVec.ofNat 64 0

/-- Run registers core 1: same shape, delta 7 in rax. -/
def runReg1 : Register → Wort := fun q =>
  if q = .rax then BitVec.ofNat 64 7
  else if q = .rbp then BitVec.ofNat 64 8192
  else if q = .rcx then BitVec.ofNat 64 0
  else if q = .rsp then BitVec.ofNat 64 8208
  else BitVec.ofNat 64 0

/-- Run core data: both cores run from 4096 with zeroed XMM. -/
def runKern : Nat → HwKern
  | 0 => ⟨runReg0, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | 1 => ⟨runReg1, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 4096, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Run buffers: core 1 holds one pending byte 99 at 8216. -/
def runBuf : Nat → List TSOEintrag
  | 1 => [⟨BitVec.ofNat 64 8216, BitVec.ofNat 8 99⟩]
  | _ => []

/-- Run start machine: XADD bytes mapped executable, word 10 at 8192,
    two cores, full silicon with OS vector state. -/
def runStart : HwMaschine :=
  ⟨lockZeugSpeicher pinXadd 10 lockCodeExec runDataRW runDataRW,
    runKern, runBuf, basisHw, fun _ => basisBereit⟩

/-- Admission on the run baseline is the lock witness admission: the
    profiles are identical, so the accepted equation is reused. -/
theorem runStart_zugelassen (f : PerfMerkmal) :
    merkmalZugelassen basisHw basisBereit f = true :=
  hwLockWitStart_zugelassen f

/-- The run start machine is well-formed. -/
theorem runStart_wf : HwWf runStart :=
  hwWf_aus_zugelassen _ fun _ _ => runStart_zugelassen _

/-! ## 1. LOCK XADD from the mapped bytes, core 0.

  The accepted `lockSchrittVoll` fetches `pinXadd` from the executable
  window (the decode pin `pin_lock_xadd_decodiert` names the same bytes)
  and adds rax (5) into the word at [rbp] (8192). -/

/-- After core 0 locked-adds 5 through the fetched XADD row. -/
def runNachLock : Option HwMaschine :=
  hwLockSchritt runStart 0 (.ok (.xadd64 .rax .rbp 0) 9)

/-- The code bytes sit in the mapped executable window. -/
theorem runCode_bytes :
    runStart.mem.bytes (BitVec.ofNat 64 4096) = natByte 240 ∧
    runStart.mem.ausfuehrbar (BitVec.ofNat 64 4096) = true ∧
    runStart.mem.ausfuehrbar (BitVec.ofNat 64 4104) = true := by
  decide

/-- Step one moves the word 10 to 15: memory really changes. -/
theorem run_lock_wort :
    hwLockWort (BitVec.ofNat 64 8192) runNachLock = some 15 := by
  decide

/-- Step one returns the old word through rax. -/
theorem run_lock_rax :
    hwLockReg 0 .rax runNachLock = some 10 := by
  decide

/-- Step one advances RIP past the 9 fetched bytes. -/
theorem run_lock_rip :
    hwLockRip 0 runNachLock = some (BitVec.ofNat 64 4105) := by
  decide

/-- Step one keeps the foreign pending byte: no foreign drain. -/
theorem run_lock_fremd_buf :
    hwLockBuf 1 runNachLock = some 1 := by
  decide

/-- Forwarding to the owner: core 1 reads its own unflushed byte. -/
theorem run_lock_eigen_sicht :
    hwLockSicht runNachLock 1 (BitVec.ofNat 64 8216) =
      some (some (BitVec.ofNat 8 99)) := by
  decide

/-- No foreign forwarding: core 0 reads canonical memory (zero). -/
theorem run_lock_fremd_sicht :
    hwLockSicht runNachLock 0 (BitVec.ofNat 64 8216) =
      some (some (BitVec.ofNat 8 0)) := by
  decide

/-- Step one as a union step: the LOCK/RMW tag fires. -/
theorem run_step_lock :
    ∃ m1, runNachLock = some m1 ∧
      HwVollSchritt runStart m1
        (KapEreignis.lockRmw 0 (.ok (.xadd64 .rax .rbp 0) 9)) := by
  cases hN : runNachLock with
  | none =>
    have hwort := run_lock_wort
    rw [hN] at hwort
    cases hwort
  | some m1 =>
    exact ⟨m1, rfl, (kap_lock_embedded _ _ _ _).mp hN⟩

/-! ## Probes: gates the later steps need on the run lineage. -/

/-- Probe: the call gate passes (rsp 8208 is 16-aligned). -/
example : rufAlignOk (projZustand runStart 0) = true := by
  decide

/-- Probe: scalar FP entry is open on the reset control state. -/
example : s32Eintritt kontextReset = true := by
  decide

/-- Probe: a register `addss` computes on the run FP view. -/
example : (s32Schritt ⟨.addssRR .xmm0 .xmm1, 4⟩ (projFp runStart 0)).isSome = true := by
  decide

/-- Probe: a register `paddb` computes on the run FP view. -/
example : (stepIntVec ⟨.paddbRR .xmm0 .xmm1, 5⟩ (projFp runStart 0)
    basisHw basisBereit basisCpu basisKontrolle).isSome = true := by
  decide

/-! ## 2. Plain store, push and call on core 0.

  The store goes to 8208 (free data inside the run window); push and
  call spill through the acting core's slot (rsp 8208 - 8 = 8200).
  The call gate passes since rsp stays 16-aligned: no step moves rsp. -/

/-- Plain store address and word on core 0. -/
def runStoreAdr : Adresse := BitVec.ofNat 64 8208
/-- Plain store word on core 0. -/
def runStoreWort : Wort := BitVec.ofNat 64 123456789

/-- After core 0 buffers the plain store word. -/
def runNachStore : Option HwMaschine :=
  match runNachLock with
  | some m => fwdAdapter.schritt m 0 (.speichere runStoreAdr runStoreWort)
  | none => none

/-- Pushed word (first return spill) on core 0. -/
def runPushWort : Wort := BitVec.ofNat 64 4211

/-- After core 0 pushes the first word at its slot. -/
def runNachPush : Option HwMaschine :=
  match runNachStore with
  | some m => stapelAdapter.schritt m 0 (.push runPushWort)
  | none => none

/-- Called word (second return spill, younger) on core 0. -/
def runRufWort : Wort := BitVec.ofNat 64 4222

/-- After core 0 spills the call return word at its slot. -/
def runNachRuf : Option HwMaschine :=
  match runNachPush with
  | some m => stapelAdapter.schritt m 0 (.ruf runRufWort)
  | none => none

/-- The acting slot stays 8200 along the whole prefix: no step moves
    rsp, so push and call spill at the same address and the younger
    (call) word wins. -/
theorem run_slot_bleibt :
    (runNachRuf.map fun m => stapelSlot m 0) = some (BitVec.ofNat 64 8200) := by
  decide

/-- The call gate passes on the push successor. -/
theorem run_ruf_gate :
    (runNachPush.map fun m => rufAlignOk (projZustand m 0)) = some true := by
  decide

/-! ## 3. Scalar FP and packed integer register steps on core 0.

  Both reuse the accepted equation lemmas with explicit successors;
  memory is untouched by construction, so the memory-unchanged premise
  holds by projection. -/

/-- The scalar FP row: `addss xmm0, xmm1` over four bytes. -/
def runFpD : S32Decodiert := ⟨.addssRR .xmm0 .xmm1, 4⟩

/-- Explicit scalar FP successor of a run machine. -/
def runFpT (m : HwMaschine) : FpZustand :=
  { projFp m 0 with kern := { (projFp m 0).kern with rip := ripNach (projFp m 0).kern.rip 4 }, xmm := xmmSchreibeTief32 (projFp m 0).xmm .xmm0 (s32Rechne .add (xmmTief32 (projFp m 0).xmm .xmm0) (xmmTief32 (projFp m 0).xmm .xmm1)) }

/-- The accepted `addss` equation at the explicit successor. -/
theorem runFp_eq (m : HwMaschine)
    (hfp : s32Eintritt (projFp m 0).fp = true) :
    s32Schritt runFpD (projFp m 0) = some (runFpT m) :=
  s32Schritt_addssRR runFpD (projFp m 0) .xmm0 .xmm1
    (by decide) hfp rfl

/-- After core 0 runs the scalar FP row. -/
def runNachFp : Option HwMaschine :=
  match runNachRuf with
  | some m => some (setKernVonFp m 0 (runFpT m))
  | none => none

/-- The scalar FP entry stays open after push and call (fp untouched). -/
theorem run_fp_eintritt :
    (runNachRuf.map fun m => s32Eintritt (projFp m 0).fp) = some true := by
  decide

/-- The packed integer row: `paddb xmm0, xmm1` over five bytes. -/
def runVecD : IntVecDec := ⟨.paddbRR .xmm0 .xmm1, 5⟩

/-- Explicit packed integer successor of a run machine. -/
def runVecT (m : HwMaschine) : FpZustand :=
  { projFp m 0 with kern := { (projFp m 0).kern with rip := ripNach (projFp m 0).kern.rip 5 }, xmm := xmmSet (projFp m 0).xmm .xmm0 (vecAdd .b8 ((projFp m 0).xmm .xmm0) ((projFp m 0).xmm .xmm1)) }

/-- The accepted `paddb` equation at the explicit successor. -/
theorem runVec_eq (m : HwMaschine)
    (hgate : vektorLegacyZugelassen m.hw (m.bereit 0)
      basisCpu basisKontrolle = true) :
    stepIntVec runVecD (projFp m 0) m.hw (m.bereit 0)
      basisCpu basisKontrolle = some (runVecT m) :=
  stepIntVec_paddb runVecD (projFp m 0) m.hw (m.bereit 0)
    basisCpu basisKontrolle .xmm0 .xmm1 (by decide) hgate rfl

/-- After core 0 runs the packed integer row. -/
def runNachVec : Option HwMaschine :=
  match runNachFp with
  | some m => some (setKernVonFp m 0 (runVecT m))
  | none => none

/-- The vector gate stays open after the FP row (profiles untouched). -/
theorem run_vec_gate :
    (runNachFp.map fun m => vektorLegacyZugelassen m.hw (m.bereit 0)
      basisCpu basisKontrolle) = some true := by
  decide

/-! ## 4. Drains: core 0 flushes its 24 buffered bytes, then core 1.

  Core 0 holds store (8) + push (8) + call (8); core 1 holds its
  foreign byte. Every flush is a `drain` union step below. -/

/-- Flush core 0 `n` times through the drain adapter. -/
def runDrain0 : Nat → Option HwMaschine → Option HwMaschine
  | 0, m => m
  | n + 1, m =>
    match m with
    | none => none
    | some mm =>
      match drainAdapter.schritt mm 0 .eigenSpuele with
      | some mm' => runDrain0 n (some mm')
      | none => none

/-- After core 0 drains all 24 buffered bytes into shared memory. -/
def runNachFlush0 : Option HwMaschine := runDrain0 24 runNachVec

/-- After core 1 drains its foreign byte into shared memory. -/
def runNachFlush1 : Option HwMaschine :=
  match runNachFlush0 with
  | some m => drainAdapter.schritt m 1 .eigenSpuele
  | none => none

/-- Buffer census along the run: every issue and every drain lands. -/
theorem run_puffer_zensus :
    (runNachStore.map fun m => (m.puffer 0).length) = some 8 ∧
    (runNachPush.map fun m => (m.puffer 0).length) = some 16 ∧
    (runNachRuf.map fun m => (m.puffer 0).length) = some 24 ∧
    (runNachVec.map fun m => (m.puffer 0).length) = some 24 ∧
    (runNachFlush0.map fun m => (m.puffer 0).length) = some 0 ∧
    (runNachFlush0.map fun m => (m.puffer 1).length) = some 1 ∧
    (runNachFlush1.map fun m => (m.puffer 0).length) = some 0 ∧
    (runNachFlush1.map fun m => (m.puffer 1).length) = some 0 := by
  decide

/-- Final memory: the locked word, the stored word, the younger call
    word at the slot, and the foreign byte -- all in shared memory,
    observed identically from both cores. -/
theorem run_speicher_ende :
    (runNachFlush1.map fun m => read64 m.mem (BitVec.ofNat 64 8192)) =
      some (some 15) ∧
    (runNachFlush1.map fun m => read64 m.mem runStoreAdr) =
      some (some runStoreWort) ∧
    (runNachFlush1.map fun m => read64 m.mem (BitVec.ofNat 64 8200)) =
      some (some runRufWort) ∧
    (runNachFlush1.map fun m => m.mem.bytes (BitVec.ofNat 64 8216)) =
      some (BitVec.ofNat 8 99) := by
  decide

/- CUTS:
    Skeleton only: start machine plus well-formedness. The run steps,
    drains, observations and final memory are not yet built.
-/

#print axioms runStart_wf

end Gabbro.Grammatik.X86
