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
def hwLockReg (r : Register) : Option HwMaschine → Option Wort
  | some m' => some ((m'.kerne 0).register r)
  | none => none

/-- Observe the acting core's RIP of an admitted outcome. -/
def hwLockRip (c : Nat) : Option HwMaschine → Option Adresse
  | some m' => some ((m'.kerne c).rip)
  | none => none

/-- Observe a core buffer length of an admitted outcome. -/
def hwLockBuf (c : Nat) : Option HwMaschine → Option Nat
  | some m' => some (((m'.puffer c).length))
  | none => none

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

/- CUTS:
    Proved here: projection with the shared TSO view, re-embedding with
    `HwWf` preservation, the admitted-step plug with its event-exposing
    twin and ok/none bridge, decidable observers, and XADD exact
    agreement (same guards, same successor and event, read-back, kept
    buffers). NOT proved yet: CMPXCHG/MFENCE agreement, planted
    refusals, two-core witness, no W/GX claim.
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
