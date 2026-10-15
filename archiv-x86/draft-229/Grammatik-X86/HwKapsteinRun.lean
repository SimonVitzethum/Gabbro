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

/-! ## 5. In-run observations: forwarding, slot reads, both-core loads.

  Every observation is a silent union step (state unchanged): the owner
  forwards its buffered word, the foreign core reads canonical memory
  until the drain, pop/ret read the slot, and after the drains both
  cores read the flushed bytes from shared memory. -/

/-- Owner forwarding: core 0 reads its buffered store word. -/
theorem run_fwd_beobachte_pin :
    (runNachStore.map fun m =>
      stapelLadeWort (tsoAnsicht m) 0 runStoreAdr) =
      some (some runStoreWort) := by
  decide

/-- No foreign forwarding: core 1 reads canonical memory (zero). -/
theorem run_basis_fremd_pin :
    (runNachStore.map fun m => loadByte (tsoAnsicht m) 1 runStoreAdr) =
      some (some (BitVec.ofNat 8 0)) := by
  decide

/-- Pop reads the pushed word at the slot. -/
theorem run_pop_pin :
    (runNachPush.map fun m =>
      stapelLadeWort (tsoAnsicht m) 0 (BitVec.ofNat 64 8200)) =
      some (some runPushWort) := by
  decide

/-- Pop and ret read the younger call word at the slot. -/
theorem run_ruf_liest_pin :
    (runNachRuf.map fun m =>
      stapelLadeWort (tsoAnsicht m) 0 (BitVec.ofNat 64 8200)) =
      some (some runRufWort) := by
  decide

/-- After the drains both cores read the flushed byte from memory. -/
theorem run_ende_beobachte_pin :
    (runNachFlush1.map fun m =>
      loadByte (tsoAnsicht m) 0 (BitVec.ofNat 64 8216)) =
      some (some (BitVec.ofNat 8 99)) ∧
    (runNachFlush1.map fun m =>
      loadByte (tsoAnsicht m) 1 (BitVec.ofNat 64 8216)) =
      some (some (BitVec.ofNat 8 99)) := by
  decide

/-! ## 6. Runs: chains of union steps with their family tags. -/

/-- A run: a chain of union steps carrying each step's family tag. -/
inductive RunKap : HwMaschine → HwMaschine → List KapEreignis → Prop where
  | nil (m : HwMaschine) : RunKap m m []
  | cons {m m' m'' : HwMaschine} {k : KapEreignis}
    {ks : List KapEreignis} :
    HwVollSchritt m m' k → RunKap m' m'' ks → RunKap m m'' (k :: ks)

/-- Runs append: the tag lists concatenate. -/
theorem runKap_anhang {m1 m2 m3 : HwMaschine}
    {ks js : List KapEreignis} :
    RunKap m1 m2 ks → RunKap m2 m3 js → RunKap m1 m3 (ks ++ js) := by
  intro h1
  induction h1 with
  | nil _ =>
    intro h2
    simpa using h2
  | cons hstep _ ih =>
    intro h2
    exact .cons hstep (ih h2)

/-- Well-formedness holds along every run. -/
theorem runKap_wf {m m' : HwMaschine} {ks : List KapEreignis} :
    RunKap m m' ks → HwWf m → HwWf m' := by
  intro h
  induction h with
  | nil _ =>
    intro hwf
    exact hwf
  | cons hstep _ ih =>
    intro hwf
    exact ih (kap_wf _ _ _ hstep hwf)

/-- A single union step is a one-step run. -/
theorem runKap_einzel {m m' : HwMaschine} {k : KapEreignis} :
    HwVollSchritt m m' k → RunKap m m' [k] :=
  fun h => .cons h (RunKap.nil _)

/-- A uniform list of known length is the replicate. -/
theorem liste_gleich_replicate (ks : List KapEreignis)
    (e : KapEreignis) :
    ∀ (n : Nat), ks.length = n → (∀ k ∈ ks, k = e) →
      ks = List.replicate n e := by
  induction ks with
  | nil =>
    intro n hlen _
    cases n with
    | zero => rfl
    | succ _ => simp at hlen
  | cons k rest ih =>
    intro n hlen hmem
    cases n with
    | zero => simp at hlen
    | succ n =>
      have hk : k = e := hmem k (by simp)
      have hrest : ∀ x ∈ rest, x = e :=
        fun x hx => hmem x (by simp [hx])
      have hlen2 : rest.length = n := by
        simp at hlen
        omega
      rw [hk, ih n hlen2 hrest]
      rfl

/-- The core-0 drain loop yields a run of silent drain steps. -/
theorem runDrain0_run (n : Nat) (m m' : HwMaschine)
    (h : runDrain0 n (some m) = some m') :
    ∃ ks, RunKap m m' ks ∧ ks.length = n ∧
      ∀ k ∈ ks, k = KapEreignis.drain 0 .eigenSpuele := by
  induction n generalizing m with
  | zero =>
    have hm : m = m' := by
      simpa [runDrain0] using h
    cases hm
    exact ⟨[], .nil _, rfl, fun k hk => by simp at hk⟩
  | succ n ih =>
    cases hF : drainAdapter.schritt m 0 .eigenSpuele with
    | none =>
      have hred : runDrain0 (n + 1) (some m) = none := by
        simp only [runDrain0, hF]
      rw [hred] at h
      cases h
    | some mm =>
      have hred : runDrain0 (n + 1) (some m) = runDrain0 n (some mm) := by
        simp only [runDrain0, hF]
      rw [hred] at h
      obtain ⟨ks, hrun, hlen, hmem⟩ := ih mm h
      refine ⟨KapEreignis.drain 0 .eigenSpuele :: ks,
        .cons ((kap_drain_embedded _ _ _ _).mp hF) hrun, ?_, ?_⟩
      · simp [hlen]
      · intro k hk
        simp at hk
        cases hk with
        | inl hkk => exact hkk
        | inr hkr => exact hmem k hkr

/-! ## 7. The run: thirty-eight union steps on two cores. -/

/-- The vector row moves no buffer: core 0 still holds 24 bytes. -/
theorem run_vec_puffer_pin :
    (runNachVec.map fun m => (m.puffer 0).length) = some 24 := by
  decide

theorem run_haupt :
    ∃ (m8 : HwMaschine) (ks : List KapEreignis),
      runNachFlush1 = some m8 ∧
      RunKap runStart m8 ks ∧
      ks = [KapEreignis.lockRmw 0 (.ok (.xadd64 .rax .rbp 0) 9),
        KapEreignis.fwd 0 (.speichere runStoreAdr runStoreWort),
        KapEreignis.fwd 0 (.beobachte runStoreAdr),
        KapEreignis.basis (.leseBeob 1 runStoreAdr (BitVec.ofNat 8 0)),
        KapEreignis.stapel 0 (.push runPushWort),
        KapEreignis.stapel 0 (.pop (BitVec.ofNat 64 8200)),
        KapEreignis.stapel 0 (.ruf runRufWort),
        KapEreignis.stapel 0 (.pop (BitVec.ofNat 64 8200)),
        KapEreignis.stapel 0 (.ret (BitVec.ofNat 64 8200)),
        KapEreignis.fp (.s32reg 0 runFpD),
        KapEreignis.vec (.vecReg 0 basisCpu basisKontrolle runVecD)] ++
        List.replicate 24 (KapEreignis.drain 0 .eigenSpuele) ++
        [KapEreignis.drain 1 .eigenSpuele,
        KapEreignis.basis
          (.leseBeob 0 (BitVec.ofNat 64 8216) (BitVec.ofNat 8 99)),
        KapEreignis.basis
          (.leseBeob 1 (BitVec.ofNat 64 8216) (BitVec.ofNat 8 99))] ∧
      HwWf m8 ∧
      (m8.puffer 0).length = 0 ∧ (m8.puffer 1).length = 0 ∧
      read64 m8.mem (BitVec.ofNat 64 8192) = some 15 ∧
      read64 m8.mem runStoreAdr = some runStoreWort ∧
      read64 m8.mem (BitVec.ofNat 64 8200) = some runRufWort ∧
      m8.mem.bytes (BitVec.ofNat 64 8216) = BitVec.ofNat 8 99 := by
  cases h1 : runNachLock with
  | none =>
    have hwort := run_lock_wort
    rw [h1] at hwort
    cases hwort
  | some m1 =>
    have eLock : adapterLockRmw.schritt runStart 0
        (.ok (.xadd64 .rax .rbp 0) 9) = some m1 := h1
    have s1 : HwVollSchritt runStart m1
        (KapEreignis.lockRmw 0 (.ok (.xadd64 .rax .rbp 0) 9)) :=
      (kap_lock_embedded _ _ _ _).mp eLock
    cases h2 : runNachStore with
    | none =>
      have hpin := run_puffer_zensus.1
      rw [h2] at hpin
      cases hpin
    | some m2 =>
      have hE2 : fwdAdapter.schritt m1 0
          (.speichere runStoreAdr runStoreWort) = some m2 := by
        simpa [runNachStore, h1] using h2
      have s2 : HwVollSchritt m1 m2
          (KapEreignis.fwd 0 (.speichere runStoreAdr runStoreWort)) :=
        (kap_fwd_embedded _ _ _ _).mp hE2
      have hL2 : stapelLadeWort (tsoAnsicht m2) 0 runStoreAdr =
          some runStoreWort := by
        simpa [runNachStore, h1, hE2] using run_fwd_beobachte_pin
      have oFwd : HwVollSchritt m2 m2
          (KapEreignis.fwd 0 (.beobachte runStoreAdr)) := by
        have heq : fwdAdapter.schritt m2 0
            (.beobachte runStoreAdr) = some m2 := by
          show (match stapelLadeWort (tsoAnsicht m2) 0 runStoreAdr with
            | some _ => some m2 | none => none) = some m2
          rw [hL2]
        exact (kap_fwd_embedded _ _ _ _).mp heq
      have hB2 : loadByte (tsoAnsicht m2) 1 runStoreAdr =
          some (BitVec.ofNat 8 0) := by
        simpa [runNachStore, h1, hE2] using run_basis_fremd_pin
      have oBasis : HwVollSchritt m2 m2 (KapEreignis.basis
          (.leseBeob 1 runStoreAdr (BitVec.ofNat 8 0))) :=
        (kap_basis_embedded _ _ _).mp (HwSchritt.lade 1 _ _ hB2)
      cases h3 : runNachPush with
      | none =>
        have hpin := run_puffer_zensus.2.1
        rw [h3] at hpin
        cases hpin
      | some m3 =>
        have hE3 : stapelAdapter.schritt m2 0
            (.push runPushWort) = some m3 := by
          simpa [runNachPush, h2] using h3
        have s3 : HwVollSchritt m2 m3
            (KapEreignis.stapel 0 (.push runPushWort)) :=
          (kap_stapel_embedded _ _ _ _).mp hE3
        have hL3 : stapelLadeWort (tsoAnsicht m3) 0
            (BitVec.ofNat 64 8200) = some runPushWort := by
          simpa [runNachPush, h2, hE3] using run_pop_pin
        have oPop : HwVollSchritt m3 m3 (KapEreignis.stapel 0
            (.pop (BitVec.ofNat 64 8200))) := by
          have heq : stapelAdapter.schritt m3 0
              (.pop (BitVec.ofNat 64 8200)) = some m3 := by
            show (match stapelLadeWort (tsoAnsicht m3) 0
                (BitVec.ofNat 64 8200) with
              | some _ => some m3 | none => none) = some m3
            rw [hL3]
          exact (kap_stapel_embedded _ _ _ _).mp heq
        cases h4 : runNachRuf with
        | none =>
          have hpin := run_puffer_zensus.2.2.1
          rw [h4] at hpin
          cases hpin
        | some m4 =>
          have hgate : rufAlignOk (projZustand m3 0) = true := by
            simpa [runNachPush, h2, hE3] using run_ruf_gate
          have hruf : stapelAdapter.schritt m3 0
              (.ruf runRufWort) = stapelCall m3 0 runRufWort := by
            show (if rufAlignOk (projZustand m3 0) then
              stapelCall m3 0 runRufWort else none) = _
            rw [if_pos hgate]
          have hC4 : stapelCall m3 0 runRufWort = some m4 := by
            have h := h4
            simp only [runNachRuf, h3] at h
            rw [hruf] at h
            exact h
          have s4 : HwVollSchritt m3 m4
              (KapEreignis.stapel 0 (.ruf runRufWort)) := by
            have heq : stapelAdapter.schritt m3 0
                (.ruf runRufWort) = some m4 := by
              rw [hruf]
              exact hC4
            exact (kap_stapel_embedded _ _ _ _).mp heq
          have hL4 : stapelLadeWort (tsoAnsicht m4) 0
              (BitVec.ofNat 64 8200) = some runRufWort := by
            simpa [runNachRuf, h3, hruf, hC4] using run_ruf_liest_pin
          have oPop2 : HwVollSchritt m4 m4 (KapEreignis.stapel 0
              (.pop (BitVec.ofNat 64 8200))) := by
            have heq : stapelAdapter.schritt m4 0
                (.pop (BitVec.ofNat 64 8200)) = some m4 := by
              show (match stapelLadeWort (tsoAnsicht m4) 0
                  (BitVec.ofNat 64 8200) with
                | some _ => some m4 | none => none) = some m4
              rw [hL4]
            exact (kap_stapel_embedded _ _ _ _).mp heq
          have oRet : HwVollSchritt m4 m4 (KapEreignis.stapel 0
              (.ret (BitVec.ofNat 64 8200))) := by
            have heq : stapelAdapter.schritt m4 0
                (.ret (BitVec.ofNat 64 8200)) = some m4 := by
              show (match stapelLadeWort (tsoAnsicht m4) 0
                  (BitVec.ofNat 64 8200) with
                | some _ => some m4 | none => none) = some m4
              rw [hL4]
            exact (kap_stapel_embedded _ _ _ _).mp heq
          cases h5 : runNachFp with
          | none =>
            have hpin := run_vec_gate
            rw [h5] at hpin
            cases hpin
          | some m5 =>
            have hfp : s32Eintritt (projFp m4 0).fp = true := by
              have h := run_fp_eintritt
              rw [h4] at h
              simpa using h
            have hEq5 : setKernVonFp m4 0 (runFpT m4) = m5 := by
              have h := h5
              unfold runNachFp at h
              rw [h4] at h
              simpa using h
            have hmem5 : (runFpT m4).kern.speicher = m4.mem :=
              projFp_speicher m4 0
            have s10 : HwVollSchritt m4 m5
                (KapEreignis.fp (.s32reg 0 runFpD)) := by
              rw [← hEq5]
              exact (kap_fp_embedded _ _ _).mp
                (FpCtrlSchritt.s32reg 0 runFpD (runFpT m4)
                  (runFp_eq m4 hfp) hmem5)
            cases h6 : runNachVec with
            | none =>
              have hpin := run_vec_puffer_pin
              rw [h6] at hpin
              cases hpin
            | some m6 =>
              have hgateV : vektorLegacyZugelassen m5.hw (m5.bereit 0)
                  basisCpu basisKontrolle = true := by
                have h := run_vec_gate
                rw [h5] at h
                simpa using h
              have hEq6 : setKernVonFp m5 0 (runVecT m5) = m6 := by
                have h := h6
                unfold runNachVec at h
                rw [h5] at h
                simpa using h
              have s11 : HwVollSchritt m5 m6 (KapEreignis.vec
                  (.vecReg 0 basisCpu basisKontrolle runVecD)) := by
                rw [← hEq6]
                exact (kap_vec_embedded _ _ _).mp
                  (vecReg_ist_schritt m5 0 basisCpu basisKontrolle
                    runVecD (runVecT m5) (by decide) (by decide)
                    hgateV (runVec_eq m5 hgateV)
                    (projFp_speicher m5 0))
              cases h7 : runNachFlush0 with
              | none =>
                have hpin := run_puffer_zensus.2.2.2.2.1
                rw [h7] at hpin
                cases hpin
              | some m7 =>
                have hLoop : runDrain0 24 (some m6) = some m7 := by
                  have h := h7
                  unfold runNachFlush0 at h
                  rw [h6] at h
                  simpa using h
                obtain ⟨ksLoop, hRunLoop, hLenLoop, hMemLoop⟩ :=
                  runDrain0_run 24 m6 m7 hLoop
                have hRep : ksLoop = List.replicate 24
                    (KapEreignis.drain 0 .eigenSpuele) :=
                  liste_gleich_replicate ksLoop _ 24 hLenLoop hMemLoop
                cases h8 : runNachFlush1 with
                | none =>
                  have hpin := run_puffer_zensus.2.2.2.2.2.2.1
                  rw [h8] at hpin
                  cases hpin
                | some m8 =>
                  have hF1 : drainAdapter.schritt m7 1
                      .eigenSpuele = some m8 := by
                    have h := h8
                    unfold runNachFlush1 at h
                    rw [h7] at h
                    simpa using h
                  have sF1 : HwVollSchritt m7 m8
                      (KapEreignis.drain 1 .eigenSpuele) :=
                    (kap_drain_embedded _ _ _ _).mp hF1
                  have hO0 : loadByte (tsoAnsicht m8) 0
                      (BitVec.ofNat 64 8216) =
                      some (BitVec.ofNat 8 99) := by
                    have h := run_ende_beobachte_pin.1
                    rw [h8] at h
                    simpa using h
                  have hO1 : loadByte (tsoAnsicht m8) 1
                      (BitVec.ofNat 64 8216) =
                      some (BitVec.ofNat 8 99) := by
                    have h := run_ende_beobachte_pin.2
                    rw [h8] at h
                    simpa using h
                  have oEnd0 : HwVollSchritt m8 m8 (KapEreignis.basis
                      (.leseBeob 0 (BitVec.ofNat 64 8216)
                        (BitVec.ofNat 8 99))) :=
                    (kap_basis_embedded _ _ _).mp
                      (HwSchritt.lade 0 _ _ hO0)
                  have oEnd1 : HwVollSchritt m8 m8 (KapEreignis.basis
                      (.leseBeob 1 (BitVec.ofNat 64 8216)
                        (BitVec.ofNat 8 99))) :=
                    (kap_basis_embedded _ _ _).mp
                      (HwSchritt.lade 1 _ _ hO1)
                  have p1 := runKap_einzel s1
                  have p2 := runKap_anhang p1 (runKap_einzel s2)
                  have p3 := runKap_anhang p2 (runKap_einzel oFwd)
                  have p4 := runKap_anhang p3 (runKap_einzel oBasis)
                  have p5 := runKap_anhang p4 (runKap_einzel s3)
                  have p6 := runKap_anhang p5 (runKap_einzel oPop)
                  have p7 := runKap_anhang p6 (runKap_einzel s4)
                  have p8 := runKap_anhang p7 (runKap_einzel oPop2)
                  have p9 := runKap_anhang p8 (runKap_einzel oRet)
                  have p10 := runKap_anhang p9 (runKap_einzel s10)
                  have hPre := runKap_anhang p10 (runKap_einzel s11)
                  rw [hRep] at hRunLoop
                  have q1 := runKap_einzel sF1
                  have q2 := runKap_anhang q1 (runKap_einzel oEnd0)
                  have hSuf := runKap_anhang q2 (runKap_einzel oEnd1)
                  have hFull :=
                    runKap_anhang (runKap_anhang hPre hRunLoop) hSuf
                  have hBuf0 : (m8.puffer 0).length = 0 := by
                    have h := run_puffer_zensus.2.2.2.2.2.2.1
                    rw [h8] at h
                    simpa using h
                  have hBuf1 : (m8.puffer 1).length = 0 := by
                    have h := run_puffer_zensus.2.2.2.2.2.2.2
                    rw [h8] at h
                    simpa using h
                  have hWort : read64 m8.mem
                      (BitVec.ofNat 64 8192) = some 15 := by
                    have h := run_speicher_ende.1
                    rw [h8] at h
                    simpa using h
                  have hStore : read64 m8.mem runStoreAdr =
                      some runStoreWort := by
                    have h := run_speicher_ende.2.1
                    rw [h8] at h
                    simpa using h
                  have hSlot : read64 m8.mem
                      (BitVec.ofNat 64 8200) = some runRufWort := by
                    have h := run_speicher_ende.2.2.1
                    rw [h8] at h
                    simpa using h
                  have hByte : m8.mem.bytes
                      (BitVec.ofNat 64 8216) =
                      BitVec.ofNat 8 99 := by
                    have h := run_speicher_ende.2.2.2
                    rw [h8] at h
                    simpa using h
                  refine ⟨m8, _, rfl, hFull, rfl, runKap_wf hFull
                    runStart_wf, hBuf0, hBuf1, hWort, hStore,
                    hSlot, hByte⟩

/- CUTS:
    Proved here, over the reused accepted vocabulary only (every
    definition lifted, never redefined):
    - `RunKap`: runs as chains of the capstone union step
      `HwVollSchritt` with one family tag per step, plus append
      (`runKap_anhang`), preservation (`runKap_wf`, via `kap_wf`),
      the drain-loop induction (`runDrain0_run`) and the uniform-list
      helper (`liste_gleich_replicate`);
    - `run_haupt`: a reached 38-step run on two cores from the mapped
      `pinXadd` bytes: LOCK XADD (fetched decode, word 10 to 15),
      plain store, owner-only forwarding observation plus foreign
      canonical observation, push, pop, call, pop, ret, scalar `addss`,
      packed `paddb`, twenty-four core-0 drains, the core-1 drain, and
      both-core end observations; `HwWf` along the run and the exact
      final memory (locked word 15, stored word, younger call word at
      the slot, foreign byte 99; both buffers empty).
    NOT proved here, and not claimed:
    - fetched decoding per step: only the LOCK step runs through
      fetched bytes in this run (`pin_lock_xadd_decodiert` names the
      same row; `zeug_xadd_fetch_ok` is the accepted fetched shape).
      The FP/vector rows cite their families' accepted byte pins
      (`hvecWit_fetch_pin` for `paddb`; `mxcsrWit_fetch1` and the
      `s32Byteschritt` fetch lemmas for the scalar lane) and execute
      here as direct family events at named addresses. Full
      per-step fetched decoding through one dispatcher stays open
      (decoder disjointness beyond width-vs-unified is already open
      in the capstone CUTS);
    - the MECHANISM paragraph of the lane task describes connecting
      ONE family with a new `HwAdapter` (a stale copy of an earlier
      single-family lane); this lane instead builds the capstone run
      named in its TASK paragraph, reusing all 21 adapters unchanged;
    - no hardware correspondence beyond self-consistency (silicon
      and timing assumptions live in the family files); no W/GX
      bridge; no source, checker, contract, entry, ABI, loader,
      budget or liveness claim.
-/

#print axioms runStart_wf
#print axioms run_haupt
#print axioms runDrain0_run
#print axioms runKap_anhang
#print axioms runKap_wf

end Gabbro.Grammatik.X86
