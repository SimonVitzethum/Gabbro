/-
  File:      Grammatik/X86/HwLockRmw.lean
  Subject:   LOCK XADD / LOCK CMPXCHG and MFENCE on the coherent machine.

  Lane 1119: lifts the accepted `LockedInstructionExecution` vocabulary
  (`LockAnweisung`, `lockSchrittVoll`, `lockSchritt`/`casSchritt`) onto the
  coherent `HwMaschine`/`HwSchritt` of `HardwareExecution`, replacing the
  refusal `adapterLocked662`/`hwLock_verweigert` by an admitted step under
  its guards. The old evaluator is lifted, never redefined.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.LockedInstructionExecution

namespace Gabbro.Grammatik.X86

/-- Project core `c` of the coherent machine to a locked machine:
    canonical core view plus the shared buffers. -/
def lockMaschineVonHw (m : HwMaschine) (c : Nat) : LockMaschine :=
  ⟨projZustand m c, m.puffer⟩

/-- The projection carries the shared TSO view. -/
theorem lockMaschineVonHw_tso (m : HwMaschine) (c : Nat) :
    toTSO (lockMaschineVonHw m c) = tsoAnsicht m := rfl

/-- Re-embed a locked successor: core data moves, foreign core data and
    both profiles stay. Memory and buffers come from the locked step. -/
def einbettenLock (m : HwMaschine) (c : Nat)
    (lm' : LockMaschine) : HwMaschine :=
  setTso (setKernDaten m c ⟨lm'.zu.register, lm'.zu.flags, lm'.zu.rip,
    (m.kerne c).xmm, (m.kerne c).fp⟩) ⟨lm'.zu.speicher, lm'.puffer⟩

/-- Re-embedding preserves well-formedness (profiles untouched). -/
theorem einbettenLock_wf (m : HwMaschine) (c : Nat)
    (lm' : LockMaschine) (h : HwWf m) : HwWf (einbettenLock m c lm') :=
  setTso_wf _ _ (setKernDaten_wf _ _ _ h)

/-- One admitted LOCK/RMW step on the coherent machine: run the accepted
    `lockSchrittVoll` on the core projection with the machine profiles;
    only `.ok` is admitted, everything else refuses with `none`. -/
def hwLockSchritt (m : HwMaschine) (c : Nat)
    (a : LockAnweisung) : Option HwMaschine :=
  match lockSchrittVoll a c (lockMaschineVonHw m c) m.hw (m.bereit c) with
  | .ok lm' _ => some (einbettenLock m c lm')
  | _ => none

/-- The LOCK/RMW producer plug: the admitted step as an `HwAdapter`. -/
def adapterLockRmw : HwAdapter LockAnweisung := ⟨hwLockSchritt⟩

/-! ## 2. Event-exposing step, observers and the ok/none bridge.

  `hwLockSchritt` drops the accepted access event; `hwLockSchrittEv`
  keeps it so agreement with `lockSchritt`/`casSchritt` is stated on
  both state and event. Observers project admitted outcomes to
  decidable facts for the closed pins below. -/

/-- Admitted step keeping the accepted access event. -/
def hwLockSchrittEv (m : HwMaschine) (c : Nat)
    (a : LockAnweisung) : Option (HwMaschine × LockEreignis) :=
  match lockSchrittVoll a c (lockMaschineVonHw m c) m.hw (m.bereit c) with
  | .ok lm' ev => some (einbettenLock m c lm', ev)
  | _ => none

/-- The plug step is the event step without the event. -/
theorem hwLockSchritt_als_event (m : HwMaschine) (c : Nat)
    (a : LockAnweisung) :
    hwLockSchritt m c a = Option.map Prod.fst (hwLockSchrittEv m c a) := by
  unfold hwLockSchritt hwLockSchrittEv
  cases h1 : lockSchrittVoll a c (lockMaschineVonHw m c) m.hw
    (m.bereit c) with
  | ok lm ev => rfl
  | speicherFehler => rfl
  | udFehler g => rfl
  | verweigert => rfl

/-- Observe one 64-bit word of an admitted outcome (`none` if refused). -/
def hwLockWort (a : Adresse) : Option HwMaschine → Option Wort
  | some m' => read64 m'.mem a
  | none => none

/-- Observe one register of an admitted outcome (`none` if refused). -/
def hwLockReg (c : Nat) (r : Register) : Option HwMaschine → Option Wort
  | some m' => some ((m'.kerne c).register r)
  | none => none

/-- Observe the acting core's RIP of an admitted outcome. -/
def hwLockRip (c : Nat) : Option HwMaschine → Option Adresse
  | some m' => some ((m'.kerne c).rip)
  | none => none

/-- Observe a core buffer length of an admitted outcome. -/
def hwLockBuf (c : Nat) : Option HwMaschine → Option Nat
  | some m' => some (((m'.puffer c).length))
  | none => none

/-! ## 5. Two-core witness: locked adds with a foreign buffered byte.

  Word 10 at 8192 (data window, readable and writable); core 0 adds 5,
  core 1 adds 7. Core 1 holds one pending buffered byte at 8200 --
  inside the data window but outside the word footprint -- so the
  locked steps must succeed beside it (only the own buffer gates),
  keep it (no foreign drain), forward it to its owner only, and never
  tear the canonical word. Memory definitions are reused from 662
  (`lockZeugSpeicher`, `lockZeugReg`, `lockCodeExec`, `lockDataRW`),
  never duplicated. -/

/-- Witness registers core 0: delta 5 in rax, base 8192 in rbp. -/
def hwLockWitReg0 : Register → Wort := lockZeugReg 5 8192 7

/-- Witness registers core 1: delta 7 in rax, base 8192 in rbp. -/
def hwLockWitReg1 : Register → Wort := lockZeugReg 7 8192 0

/-- Witness core data: both cores run, with their own deltas. -/
def hwLockWitKern : Nat → HwKern
  | 0 => ⟨hwLockWitReg0, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | 1 => ⟨hwLockWitReg1, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 4096, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness buffers: core 1 holds one pending byte at 8200, readable
    and writable data outside the 8192-word footprint. -/
def hwLockWitBuf : Nat → List TSOEintrag
  | 1 => [⟨BitVec.ofNat 64 8200, BitVec.ofNat 8 99⟩]
  | _ => []

/-- Witness start machine: shared word memory, two cores, full
    silicon with OS vector state. -/
def hwLockWitStart : HwMaschine :=
  ⟨lockZeugSpeicher pinXadd 10 lockCodeExec lockDataRW lockDataRW,
    hwLockWitKern, hwLockWitBuf, basisHw, fun _ => basisBereit⟩

/-- After core 0 locked-adds 5. -/
def hwLockWitNach1 : Option HwMaschine :=
  hwLockSchritt hwLockWitStart 0 (.ok (.xadd64 .rax .rbp 0) 9)

/-- Core 1 drains its pending byte into shared memory. -/
def hwLockWitFlush1 : Option TSOZustand :=
  match hwLockWitNach1 with
  | some m1 => flushKern (tsoAnsicht m1) 1
  | none => none

/-- The drained machine: core 1 buffer empty, byte 99 in memory. -/
def hwLockWitBereit2 : Option HwMaschine :=
  match hwLockWitNach1, hwLockWitFlush1 with
  | some m1, some s => some (setTso m1 s)
  | _, _ => none

/-- After core 1 locked-adds 7 on top. -/
def hwLockWitNach2 : Option HwMaschine :=
  match hwLockWitBereit2 with
  | some m2 => hwLockSchritt m2 1 (.ok (.xadd64 .rax .rbp 0) 9)
  | none => none

/-- Observe a core byte load through the shared TSO view
    (`none` if the step refused). Forwarding is owner-only by the
    accepted `loadByte` equation. -/
def hwLockSicht (o : Option HwMaschine) (c : Nat)
    (a : Adresse) : Option (Option Byte) :=
  match o with
  | some m => some (loadByte (tsoAnsicht m) c a)
  | none => none

/-- Admission on the witness baseline, closed per feature. -/
theorem hwLockWitStart_zugelassen (f : PerfMerkmal) :
    merkmalZugelassen basisHw basisBereit f = true := by
  cases f with
  | skalar64 => rfl
  | skalar32 => rfl
  | sseDoppel => decide
  | paketInt128 => rfl

/-- The witness machine is well-formed: full silicon admits all,
    uniformly over cores (readiness is constant). -/
theorem hwLockWitStart_wf : HwWf hwLockWitStart :=
  hwWf_aus_zugelassen _ fun _ => hwLockWitStart_zugelassen

/-! ## 6. Closed pins: reached steps, forwarding, refusal outcomes.

  Every pin below evaluates the complete computation on closed
  machines (`decide`/`rfl`); no machine equality is ever decided.
  Success pins observe words, registers, buffers and TSO loads;
  refusal pins go through the ok/none bridge. -/

/-- Witness word address. -/
def hwLockWitAdr : Adresse := BitVec.ofNat 64 8192

/-- Witness foreign-byte address: data, outside the word footprint. -/
def hwLockWitFremdAdr : Adresse := BitVec.ofNat 64 8200

/-- The word starts at 10: the run really changes memory. -/
theorem hwLockWit_anfang :
    read64 hwLockWitStart.mem hwLockWitAdr = some 10 := by
  decide

/-- Step one moves the word 10 to 15. -/
theorem hwLockWit_nach1_wort :
    hwLockWort hwLockWitAdr hwLockWitNach1 = some 15 := by
  decide

/-- Step one returns the old word through rax. -/
theorem hwLockWit_nach1_rax :
    hwLockReg 0 .rax hwLockWitNach1 = some 10 := by
  decide

/-- Step one keeps the foreign pending byte: no foreign drain. -/
theorem hwLockWit_nach1_fremd_buf :
    hwLockBuf 1 hwLockWitNach1 = some 1 := by
  decide

/-- Forwarding to the owner: core 1 reads its own unflushed byte. -/
theorem hwLockWit_nach1_eigen_sicht :
    hwLockSicht hwLockWitNach1 1 hwLockWitFremdAdr =
      some (some (BitVec.ofNat 8 99)) := by
  decide

/-- No foreign forwarding: core 0 reads canonical memory. -/
theorem hwLockWit_nach1_fremd_sicht :
    hwLockSicht hwLockWitNach1 0 hwLockWitFremdAdr =
      some (some (BitVec.ofNat 8 0)) := by
  decide

/-- Step two moves the word 15 to 22 on the other core. -/
theorem hwLockWit_nach2_wort :
    hwLockWort hwLockWitAdr hwLockWitNach2 = some 22 := by
  decide

/-- The drained byte lands in shared memory: both cores observe 99. -/
theorem hwLockWit_gespült_sichtbar :
    hwLockSicht hwLockWitBereit2 0 hwLockWitFremdAdr =
      some (some (BitVec.ofNat 8 99)) ∧
    hwLockSicht hwLockWitBereit2 1 hwLockWitFremdAdr =
      some (some (BitVec.ofNat 8 99)) := by
  refine ⟨by decide, by decide⟩

/-- Step two returns the old word through core 1 rax. -/
theorem hwLockWit_nach2_rax1 :
    hwLockReg 1 .rax hwLockWitNach2 = some 15 := by
  decide

/-- No torn word for the foreign core: its whole pending buffer sits
    outside the locked word footprint. -/
theorem hwLockWit_fremd_ohne_fuss :
    hwLockWitBuf 1 = [⟨hwLockWitFremdAdr, BitVec.ofNat 8 99⟩] ∧
    hwLockWitFremdAdr ∉ Fuss hwLockWitAdr := by
  refine ⟨by decide, by decide⟩

/-- Fetched-fence analogue on the plug: the fence succeeds on core 0
    past its 3 bytes while core 1 keeps its pending store. -/
theorem hwLockWit_mfence_ok :
    hwLockRip 0 (hwLockSchritt hwLockWitStart 0 (.ok .mfence 3)) =
      some (BitVec.ofNat 64 4099) ∧
    hwLockBuf 1 (hwLockSchritt hwLockWitStart 0 (.ok .mfence 3)) =
      some 1 := by
  refine ⟨by decide, by decide⟩

/-- A non-`ok` accepted outcome refuses the plug step. -/
theorem hwLockSchritt_verweigert_bei (m : HwMaschine) (c : Nat)
    (a : LockAnweisung)
    (h : lockArt (lockSchrittVoll a c (lockMaschineVonHw m c) m.hw
      (m.bereit c)) ≠ .ok) :
    hwLockSchritt m c a = none := by
  unfold hwLockSchritt
  cases h1 : lockSchrittVoll a c (lockMaschineVonHw m c) m.hw
    (m.bereit c) with
  | ok lm ev =>
    rw [h1] at h
    exact absurd rfl h
  | speicherFehler => rfl
  | udFehler g => rfl
  | verweigert => rfl

/-- An `ok` accepted outcome is admitted. -/
theorem hwLockSchritt_ok_bei (m : HwMaschine) (c : Nat)
    (a : LockAnweisung) (lm' : LockMaschine) (ev : LockEreignis)
    (h : lockSchrittVoll a c (lockMaschineVonHw m c) m.hw
      (m.bereit c) = .ok lm' ev) :
    hwLockSchritt m c a = some (einbettenLock m c lm') := by
  unfold hwLockSchritt
  rw [h]

/-! ## 3. Exact agreement: the accepted evaluator rides along.

  Each admitted form is pinned by the accepted step equation with the
  SAME guards: empty own buffer, alignment, permissions, length. The
  old evaluator is lifted, never redefined. -/

/-- XADD agreement: under the accepted guards the plug step admits
    exactly the accepted successor and event, the word reads back, and
    every buffer is kept. -/
theorem hwLock_xadd_stimmt (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (alt sval : Wort) (mem' : Speicher)
    (hbuf : m.puffer c = [])
    (hali : ausgerichtet8 (effAddr (projZustand m c) base d) = true)
    (hrd : read64 m.mem (effAddr (projZustand m c) base d) = some alt)
    (hreg : (m.kerne c).register src = sval)
    (hok : laengeOk len = true)
    (hwr : write64 m.mem (effAddr (projZustand m c) base d)
      (alt + sval) = some mem')
    (hles : lesbar8 m.mem (effAddr (projZustand m c) base d) = true) :
    hwLockSchrittEv m c (.ok (.xadd64 src base d) len) =
      some (einbettenLock m c ⟨{ schrittRegister (lockMaschineVonHw m c).zu
        (ripNach (lockMaschineVonHw m c).zu.rip len) (add64 alt sval).2 src alt
        with speicher := mem' }, (lockMaschineVonHw m c).puffer⟩,
      ⟨c, Fuss (effAddr (lockMaschineVonHw m c).zu base d),
        Fuss (effAddr (lockMaschineVonHw m c).zu base d),
        some alt, some (alt + sval), true, false⟩) ∧
    read64 (einbettenLock m c ⟨{ schrittRegister (lockMaschineVonHw m c).zu
      (ripNach (lockMaschineVonHw m c).zu.rip len) (add64 alt sval).2 src alt
      with speicher := mem' }, (lockMaschineVonHw m c).puffer⟩).mem
      (effAddr (projZustand m c) base d) = some (alt + sval) ∧
    (einbettenLock m c ⟨{ schrittRegister (lockMaschineVonHw m c).zu
      (ripNach (lockMaschineVonHw m c).zu.rip len) (add64 alt sval).2 src alt
      with speicher := mem' }, (lockMaschineVonHw m c).puffer⟩).puffer =
      m.puffer := by
  have hstep := lockSchrittVoll_xadd_erfolg (lockMaschineVonHw m c) c
    src base d len m.hw (m.bereit c) alt sval mem'
    hbuf hali hrd hreg hok hwr
  refine ⟨?_, ?_, ?_⟩
  · unfold hwLockSchrittEv
    rw [hstep]
  · exact read64_nach_write64 m.mem mem'
      (effAddr (projZustand m c) base d) (alt + sval) hwr hles
  · rfl

/-- CMPXCHG success agreement: the source installs, RAX is untouched,
    ZF is set through the comparison flags, buffers are kept. -/
theorem hwLock_cmpxchg_ok_stimmt (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (dest sval : Wort) (mem' : Speicher)
    (hbuf : m.puffer c = [])
    (hali : ausgerichtet8 (effAddr (projZustand m c) base d) = true)
    (hrd : read64 m.mem (effAddr (projZustand m c) base d) = some dest)
    (hgleich : (dest == (m.kerne c).register .rax) = true)
    (hsrc : (m.kerne c).register src = sval)
    (hok : laengeOk len = true)
    (hwr : write64 m.mem (effAddr (projZustand m c) base d) sval =
      some mem')
    (hles : lesbar8 m.mem (effAddr (projZustand m c) base d) = true) :
    hwLockSchrittEv m c (.ok (.cmpxchg64 src base d) len) =
      some (einbettenLock m c ⟨{ { { (lockMaschineVonHw m c).zu
        with rip := ripNach (lockMaschineVonHw m c).zu.rip len }
        with speicher := mem' }
        with flags := (sub64 dest ((lockMaschineVonHw m c).zu.register
          .rax)).2 }, (lockMaschineVonHw m c).puffer⟩,
      ⟨c, Fuss (effAddr (lockMaschineVonHw m c).zu base d),
        Fuss (effAddr (lockMaschineVonHw m c).zu base d),
        some dest, some sval, true, false⟩) ∧
    read64 (einbettenLock m c ⟨{ { { (lockMaschineVonHw m c).zu
      with rip := ripNach (lockMaschineVonHw m c).zu.rip len }
      with speicher := mem' }
      with flags := (sub64 dest ((lockMaschineVonHw m c).zu.register
        .rax)).2 }, (lockMaschineVonHw m c).puffer⟩).mem
      (effAddr (projZustand m c) base d) = some sval ∧
    (einbettenLock m c ⟨{ { { (lockMaschineVonHw m c).zu
      with rip := ripNach (lockMaschineVonHw m c).zu.rip len }
      with speicher := mem' }
      with flags := (sub64 dest ((lockMaschineVonHw m c).zu.register
        .rax)).2 }, (lockMaschineVonHw m c).puffer⟩).puffer =
      m.puffer := by
  have hstep := lockSchrittVoll_cmpxchg_erfolg (lockMaschineVonHw m c) c
    src base d len m.hw (m.bereit c) dest sval mem'
    hbuf hali hrd hgleich hsrc hok hwr
  refine ⟨?_, ?_, ?_⟩
  · unfold hwLockSchrittEv
    rw [hstep]
  · exact read64_nach_write64 m.mem mem'
      (effAddr (projZustand m c) base d) sval hwr hles
  · rfl

/-- CMPXCHG failure agreement (the resolved mismatch): the word is
    written back unchanged, RAX takes the word, ZF is cleared -- and
    the write-back pins full write permission of the footprint, so a
    readable-but-not-writable word refuses even the failing
    comparison. Buffers are kept. -/
theorem hwLock_cmpxchg_nein_stimmt (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (dest : Wort) (mem' : Speicher)
    (hbuf : m.puffer c = [])
    (hali : ausgerichtet8 (effAddr (projZustand m c) base d) = true)
    (hrd : read64 m.mem (effAddr (projZustand m c) base d) = some dest)
    (hfehl : (dest == (m.kerne c).register .rax) = false)
    (hok : laengeOk len = true)
    (hwr : write64 m.mem (effAddr (projZustand m c) base d) dest =
      some mem') :
    hwLockSchrittEv m c (.ok (.cmpxchg64 src base d) len) =
      some (einbettenLock m c ⟨{ schrittRegister (lockMaschineVonHw m c).zu
        (ripNach (lockMaschineVonHw m c).zu.rip len)
        (sub64 dest ((lockMaschineVonHw m c).zu.register .rax)).2 .rax dest
        with speicher := mem' }, (lockMaschineVonHw m c).puffer⟩,
      ⟨c, Fuss (effAddr (lockMaschineVonHw m c).zu base d),
        Fuss (effAddr (lockMaschineVonHw m c).zu base d),
        some dest, some dest, true, false⟩) ∧
    schreibbar8 m.mem (effAddr (projZustand m c) base d) = true ∧
    (einbettenLock m c ⟨{ schrittRegister (lockMaschineVonHw m c).zu
      (ripNach (lockMaschineVonHw m c).zu.rip len)
      (sub64 dest ((lockMaschineVonHw m c).zu.register .rax)).2 .rax dest
      with speicher := mem' }, (lockMaschineVonHw m c).puffer⟩).puffer =
      m.puffer := by
  have hstep := lockSchrittVoll_cmpxchg_fehlschlag (lockMaschineVonHw m c) c
    src base d len m.hw (m.bereit c) dest mem'
    hbuf hali hrd hfehl hok hwr
  refine ⟨?_, ?_, ?_⟩
  · unfold hwLockSchrittEv
    rw [hstep]
  · exact write64_braucht_schreibbar m.mem
      (effAddr (projZustand m c) base d) dest mem' hwr
  · rfl

/-- MFENCE agreement: only RIP advances, memory and every buffer are
    untouched, the event is fence-only. -/
theorem hwLock_mfence_stimmt (m : HwMaschine) (c : Nat) (len : Nat)
    (hzulaessig : merkmalZugelassen m.hw (m.bereit c) .sseDoppel = true)
    (hbuf : m.puffer c = [])
    (hok : laengeOk len = true) :
    hwLockSchrittEv m c (.ok .mfence len) =
      some (einbettenLock m c ⟨{ (lockMaschineVonHw m c).zu
        with rip := ripNach (lockMaschineVonHw m c).zu.rip len },
        (lockMaschineVonHw m c).puffer⟩,
      ⟨c, [], [], none, none, false, true⟩) ∧
    (einbettenLock m c ⟨{ (lockMaschineVonHw m c).zu
      with rip := ripNach (lockMaschineVonHw m c).zu.rip len },
      (lockMaschineVonHw m c).puffer⟩).mem.bytes = m.mem.bytes ∧
    (einbettenLock m c ⟨{ (lockMaschineVonHw m c).zu
      with rip := ripNach (lockMaschineVonHw m c).zu.rip len },
      (lockMaschineVonHw m c).puffer⟩).puffer = m.puffer := by
  have hstep := lockSchrittVoll_mfence_erfolg (lockMaschineVonHw m c) c
    len m.hw (m.bereit c) hzulaessig hbuf hok
  refine ⟨?_, ?_, ?_⟩
  · unfold hwLockSchrittEv
    rw [hstep]
  · rfl
  · rfl

/-! ## 4. Plug preservation and general refusals.

  The plug preserves `HwWf` (profiles untouched). What is not
  admitted stays refused: parsed #UD (LOCK on a register destination,
  LOCK on the fence, missing SSE2 gate at `.ud`), a pending own
  store, and a misaligned word. Each refusal cites its accepted
  equation through the ok/none bridge. -/

/-- Every admitted plug step preserves well-formedness. -/
theorem adapterLockRmw_wf (m : HwMaschine) (c : Nat)
    (a : LockAnweisung) (m' : HwMaschine)
    (h : adapterLockRmw.schritt m c a = some m') (hwf : HwWf m) :
    HwWf m' := by
  have h2 : hwLockSchritt m c a = some m' := h
  unfold hwLockSchritt at h2
  cases h1 : lockSchrittVoll a c (lockMaschineVonHw m c) m.hw
    (m.bereit c) with
  | ok lm ev =>
    rw [h1] at h2
    cases h2
    exact einbettenLock_wf _ _ _ hwf
  | speicherFehler => rw [h1] at h2; cases h2
  | udFehler g => rw [h1] at h2; cases h2
  | verweigert => rw [h1] at h2; cases h2

/-- Parsed architectural #UD never executes: LOCK on a register
    destination, LOCK on the fence, and the control-state #UD marker
    all refuse the plug step. -/
theorem hwLock_ud_bleibt_verweigert (m : HwMaschine) (c : Nat)
    (g : LockUdGrund) (len : Nat) :
    hwLockSchritt m c (.ud g len) = none := by
  apply hwLockSchritt_verweigert_bei
  rw [lockSchrittVoll_ud]
  intro h
  cases h

/-- A pending own store refuses the locked word step. -/
theorem hwLock_puffer_bleibt_verweigert (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (e : TSOEintrag) (rest : List TSOEintrag)
    (hbuf : m.puffer c = e :: rest)
    (hok : laengeOk len = true) :
    hwLockSchritt m c (.ok (.xadd64 src base d) len) = none := by
  apply hwLockSchritt_verweigert_bei
  have h := lockSchrittVoll_xadd_puffer_verweigert (lockMaschineVonHw m c)
    c src base d len m.hw (m.bereit c) e rest hbuf hok
  rw [h]
  decide

/-- A misaligned word refuses the locked step as an unsupported
    profile, never as a hardware fault claim. -/
theorem hwLock_unaligned_bleibt_verweigert (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (hbuf : m.puffer c = [])
    (hok : laengeOk len = true)
    (hfehl : ausgerichtet8 (effAddr (projZustand m c) base d) = false) :
    hwLockSchritt m c (.ok (.xadd64 src base d) len) = none := by
  apply hwLockSchritt_verweigert_bei
  have h := lockSchrittVoll_xadd_unaligned_verweigert (lockMaschineVonHw m c)
    c src base d len m.hw (m.bereit c) hbuf hok hfehl
  rw [h]
  decide

/-- Without admitted SSE2 the fence refuses (parsed as #UD by 662,
    gated here to `none`). -/
theorem hwLock_mfence_ohne_sse2_verweigert (m : HwMaschine) (c : Nat)
    (len : Nat)
    (hok : laengeOk len = true)
    (hfehlt : merkmalZugelassen m.hw (m.bereit c) .sseDoppel = false) :
    hwLockSchritt m c (.ok .mfence len) = none := by
  apply hwLockSchritt_verweigert_bei
  have h := lockSchrittVoll_mfence_ohne_sse2 (lockMaschineVonHw m c) c
    len m.hw (m.bereit c) hok hfehlt
  rw [h]
  decide

/- CUTS:
    Proved here: projection with the shared TSO view, re-embedding with
    `HwWf` preservation, the admitted-step plug with its event-exposing
    twin and ok/none bridge, decidable observers, XADD/CMPXCHG/MFENCE
    exact agreement (same guards, same successor and event, read-back,
    kept buffers, write permission pinned on the failure write-back),
    plug `HwWf` preservation, and general refusals (#UD markers,
    pending own store, misaligned word, fence without SSE2).
    NOT proved yet: closed refusal pins (fault classes), two-core
    witness, no W/GX claim.
-/

#print axioms lockMaschineVonHw_tso
#print axioms einbettenLock_wf
#print axioms hwLockSchritt_als_event
#print axioms hwLockSchritt_verweigert_bei
#print axioms hwLockSchritt_ok_bei
#print axioms hwLock_xadd_stimmt
#print axioms hwLock_cmpxchg_ok_stimmt
#print axioms hwLock_cmpxchg_nein_stimmt
#print axioms hwLock_mfence_stimmt
#print axioms adapterLockRmw_wf
#print axioms hwLock_ud_bleibt_verweigert
#print axioms hwLock_puffer_bleibt_verweigert
#print axioms hwLock_unaligned_bleibt_verweigert
#print axioms hwLock_mfence_ohne_sse2_verweigert
