/-
  File:      Grammatik/X86/TsoRmwBridge.lean
  Subject:   TSO to W bridge: LOCK XADD / LOCK CMPXCHG as read-modify-write
             steps over the coherent machine.

  Lane 1145: lifts the accepted LOCK/RMW producer (`HwLockRmw`:
  `adapterLockRmw`, `hwLockSchrittEv`, `hwLock_xadd_stimmt`,
  `hwLock_cmpxchg_ok_stimmt`, `hwLock_cmpxchg_nein_stimmt`) and the
  accepted connection vocabulary (`LockXaddFetch`, `LockCmpxchgSuccess`,
  `CasRetryBound`, `LockedInstructionExecution`, `LockedOps`) to the
  read-modify-write shape the W `rmw` field consumes: single RMW events
  over full word footprints that chain without loss. The old evaluator
  is lifted, never redefined. No bounded-retry or fairness claim.

  Manual provenance: none new -- Intel SDM 325462-093US Sep 2026 via
  the accepted 662 module (LOCK Vol. 2A 3-565/3-566, XADD Vol. 2D
  6-27/6-28, CMPXCHG Vol. 2A 3-193/3-194). This lane adds no new
  silicon claim beyond reusing those rows.
-/
import Grammatik.X86.HwLockRmw
import Grammatik.X86.LockXaddFetch
import Grammatik.X86.LockCmpxchgSuccess
import Grammatik.X86.CasRetryBound

namespace Gabbro.Grammatik.X86

/-- The TSO-to-RMW bridge plug: the accepted admitted LOCK/RMW step,
    reused unchanged (never a second evaluator). -/
def tsoRmwAdapter : HwAdapter LockAnweisung := adapterLockRmw

/-- The bridge plug preserves well-formedness (profiles untouched):
    exactly the accepted plug lemma, lifted. -/
theorem tsoRmwAdapter_wf (m : HwMaschine) (c : Nat)
    (a : LockAnweisung) (m' : HwMaschine)
    (h : tsoRmwAdapter.schritt m c a = some m') (hwf : HwWf m) :
    HwWf m' :=
  adapterLockRmw_wf m c a m' h hwf

/-! ## 2. Exact agreement: admitted LOCK steps ARE single RMW events.

  Each admitted form is pinned by its accepted step equation with the
  SAME guards (empty own buffer, alignment, permissions, length). The
  old evaluator is lifted, never redefined. Every premise below feeds
  exactly one guard of the cited accepted lemma. -/

/-- XADD agreement: the admitted step is ONE read-modify-write event
    over the full word footprint -- the observed word grows by the
    source register -- with the read-back, kept buffers and the
    `RmwForm` shape the W `rmw` field consumes. -/
theorem tsoRmw_xadd_einzel_rmw (m : HwMaschine) (c : Nat)
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
    ∃ (m2 : HwMaschine) (ev : LockEreignis),
      hwLockSchrittEv m c (.ok (.xadd64 src base d) len) = some (m2, ev) ∧
      ev.istRmw = true ∧ ev.istZaun = false ∧
      ev.lesen = Fuss (effAddr (projZustand m c) base d) ∧
      ev.schreiben = Fuss (effAddr (projZustand m c) base d) ∧
      ev.gelesen = some alt ∧ ev.geschrieben = some (alt + sval) ∧
      RmwForm [ev] = true ∧
      read64 m2.mem (effAddr (projZustand m c) base d) =
        some (alt + sval) ∧
      m2.puffer = m.puffer := by
  obtain ⟨hEv, hRd, hBuf⟩ := hwLock_xadd_stimmt m c src base d len
    alt sval mem' hbuf hali hrd hreg hok hwr hles
  refine ⟨_, _, hEv, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hRd, hBuf⟩
  simp [RmwForm]

/-- CMPXCHG-success agreement: the admitted step installs the source
    word as ONE read-modify-write event over the full footprint, with
    the `CmpxchgErfolgForm` shape, `RmwForm` and the read-back. -/
theorem tsoRmw_cmpxchg_erfolg_einzel_rmw (m : HwMaschine) (c : Nat)
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
    ∃ (m2 : HwMaschine) (ev : LockEreignis),
      hwLockSchrittEv m c (.ok (.cmpxchg64 src base d) len) =
        some (m2, ev) ∧
      CmpxchgErfolgForm ev (effAddr (projZustand m c) base d) dest sval ∧
      RmwForm [ev] = true ∧
      read64 m2.mem (effAddr (projZustand m c) base d) = some sval ∧
      m2.puffer = m.puffer := by
  obtain ⟨hEv, hRd, hBuf⟩ := hwLock_cmpxchg_ok_stimmt m c src base d len
    dest sval mem' hbuf hali hrd hgleich hsrc hok hwr hles
  refine ⟨_, _, hEv, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, hRd, hBuf⟩
  simp [RmwForm]

/-- CMPXCHG-failure agreement (the resolved mismatch): even the
    failed comparison is ONE read-modify-write event -- the word is
    written back unchanged, so full write permission is pinned -- with
    `RmwForm` and kept buffers. -/
theorem tsoRmw_cmpxchg_fehlschlag_rmw (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (dest : Wort) (mem' : Speicher)
    (hbuf : m.puffer c = [])
    (hali : ausgerichtet8 (effAddr (projZustand m c) base d) = true)
    (hrd : read64 m.mem (effAddr (projZustand m c) base d) = some dest)
    (hfehl : (dest == (m.kerne c).register .rax) = false)
    (hok : laengeOk len = true)
    (hwr : write64 m.mem (effAddr (projZustand m c) base d) dest =
      some mem') :
    ∃ (m2 : HwMaschine) (ev : LockEreignis),
      hwLockSchrittEv m c (.ok (.cmpxchg64 src base d) len) =
        some (m2, ev) ∧
      ev.istRmw = true ∧ ev.istZaun = false ∧
      ev.lesen = Fuss (effAddr (projZustand m c) base d) ∧
      ev.schreiben = Fuss (effAddr (projZustand m c) base d) ∧
      ev.gelesen = some dest ∧ ev.geschrieben = some dest ∧
      RmwForm [ev] = true ∧
      schreibbar8 m.mem (effAddr (projZustand m c) base d) = true ∧
      m2.puffer = m.puffer := by
  obtain ⟨hEv, hSchr, hBuf⟩ := hwLock_cmpxchg_nein_stimmt m c src base d
    len dest mem' hbuf hali hrd hfehl hok hwr
  refine ⟨_, _, hEv, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hSchr, hBuf⟩
  simp [RmwForm]

/-! ## 3. RMW atomicity: no split pair, no lost update.

  The admitted LOCK events are single atomic accesses: no
  load-then-store pair observes what one locked access does, and two
  chained locked adds serialize -- the second reads the first one's
  write. This is the hardware-side shape the W `rmw` field consumes
  (cf. `w_kein_verlust`, RMW.lean). -/

/-- No split pair reproduces an admitted RMW observation: two non-RMW
    events carry no RMW shape while the locked event does. -/
theorem tsoRmw_kein_split (ev e1 e2 : LockEreignis)
    (hrmw : ev.istRmw = true)
    (h1 : e1.istRmw = false) (h2 : e2.istRmw = false) :
    RmwForm [e1, e2] = false ∧ RmwForm [e1, e2] ≠ RmwForm [ev] :=
  cmpxchg_erfolg_kein_split ev e1 e2 hrmw h1 h2

/-- Chained LOCK XADDs serialize without loss: two admitted locked
    adds on the same target -- the second running on the first one's
    successor -- read and write in sequence, so the second event reads
    exactly what the first one wrote. Every premise feeds one guard of
    the two accepted step equations (`hstep1`/`hstep2` select the
    computed successors, `htgt` pins the shared target). -/
theorem tsoRmw_kette_ohne_verlust (m1 m2 m3 : HwMaschine) (c1 c2 : Nat)
    (ev1 ev2 : LockEreignis)
    (src1 base1 : Register) (d1 : BitVec 32) (len1 : Nat)
    (alt1 sval1 : Wort) (mem2 : Speicher)
    (hbuf1 : m1.puffer c1 = [])
    (hali1 : ausgerichtet8 (effAddr (projZustand m1 c1) base1 d1) = true)
    (hrd1 : read64 m1.mem (effAddr (projZustand m1 c1) base1 d1) =
      some alt1)
    (hreg1 : (m1.kerne c1).register src1 = sval1)
    (hok1 : laengeOk len1 = true)
    (hwr1 : write64 m1.mem (effAddr (projZustand m1 c1) base1 d1)
      (alt1 + sval1) = some mem2)
    (hles1 : lesbar8 m1.mem (effAddr (projZustand m1 c1) base1 d1) = true)
    (src2 base2 : Register) (d2 : BitVec 32) (len2 : Nat)
    (alt2 sval2 : Wort) (mem3 : Speicher)
    (hbuf2 : m2.puffer c2 = [])
    (hali2 : ausgerichtet8 (effAddr (projZustand m2 c2) base2 d2) = true)
    (hrd2 : read64 m2.mem (effAddr (projZustand m2 c2) base2 d2) =
      some alt2)
    (hreg2 : (m2.kerne c2).register src2 = sval2)
    (hok2 : laengeOk len2 = true)
    (hwr2 : write64 m2.mem (effAddr (projZustand m2 c2) base2 d2)
      (alt2 + sval2) = some mem3)
    (hles2 : lesbar8 m2.mem (effAddr (projZustand m2 c2) base2 d2) = true)
    (hstep1 : hwLockSchrittEv m1 c1 (.ok (.xadd64 src1 base1 d1) len1) =
      some (m2, ev1))
    (hstep2 : hwLockSchrittEv m2 c2 (.ok (.xadd64 src2 base2 d2) len2) =
      some (m3, ev2))
    (htgt : effAddr (projZustand m2 c2) base2 d2 =
      effAddr (projZustand m1 c1) base1 d1) :
    ev2.gelesen = ev1.geschrieben := by
  obtain ⟨hEv1, hRd1, -⟩ := hwLock_xadd_stimmt m1 c1 src1 base1 d1 len1
    alt1 sval1 mem2 hbuf1 hali1 hrd1 hreg1 hok1 hwr1 hles1
  obtain ⟨hEv2, -, -⟩ := hwLock_xadd_stimmt m2 c2 src2 base2 d2 len2
    alt2 sval2 mem3 hbuf2 hali2 hrd2 hreg2 hok2 hwr2 hles2
  rw [hstep1] at hEv1
  rw [hstep2] at hEv2
  simp only [Option.some_inj, Prod.mk.injEq] at hEv1 hEv2
  obtain ⟨hm2, hev1⟩ := hEv1
  obtain ⟨-, hev2⟩ := hEv2
  rw [hev1, hev2]
  show some alt2 = some (alt1 + sval1)
  have hmem : read64 m2.mem (effAddr (projZustand m1 c1) base1 d1) =
      some (alt1 + sval1) := by
    rw [hm2]
    exact hRd1
  rw [htgt] at hrd2
  rw [hrd2] at hmem
  exact hmem

/-! ## 4. Refusals: what is not admitted stays refused.

  Parsed architectural #UD, a pending own store, a misaligned word
  and a fence without admitted SSE2 all refuse the bridge plug --
  exactly the accepted refusal lemmas, lifted. The fence admits but
  is never an RMW (it carries no `rmw` shape). -/

/-- Parsed architectural #UD never executes through the bridge plug. -/
theorem tsoRmw_ud_bleibt_verweigert (m : HwMaschine) (c : Nat)
    (g : LockUdGrund) (len : Nat) :
    tsoRmwAdapter.schritt m c (.ud g len) = none :=
  hwLock_ud_bleibt_verweigert m c g len

/-- A pending own store refuses the locked word step. -/
theorem tsoRmw_puffer_bleibt_verweigert (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (e : TSOEintrag) (rest : List TSOEintrag)
    (hbuf : m.puffer c = e :: rest)
    (hok : laengeOk len = true) :
    tsoRmwAdapter.schritt m c (.ok (.xadd64 src base d) len) = none :=
  hwLock_puffer_bleibt_verweigert m c src base d len e rest hbuf hok

/-- A misaligned word refuses as unsupported, never as a fault. -/
theorem tsoRmw_unaligned_bleibt_verweigert (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (hbuf : m.puffer c = [])
    (hok : laengeOk len = true)
    (hfehl : ausgerichtet8 (effAddr (projZustand m c) base d) = false) :
    tsoRmwAdapter.schritt m c (.ok (.xadd64 src base d) len) = none :=
  hwLock_unaligned_bleibt_verweigert m c src base d len hbuf hok hfehl

/-- Without admitted SSE2 the fence refuses the bridge plug. -/
theorem tsoRmw_mfence_ohne_sse2_verweigert (m : HwMaschine) (c : Nat)
    (len : Nat)
    (hok : laengeOk len = true)
    (hfehlt : merkmalZugelassen m.hw (m.bereit c) .sseDoppel = false) :
    tsoRmwAdapter.schritt m c (.ok .mfence len) = none :=
  hwLock_mfence_ohne_sse2_verweigert m c len hok hfehlt

/-- The fence admits but is never an RMW: its event is fence-only,
    so it carries no `rmw` shape for the W field. -/
theorem tsoRmw_mfence_kein_rmw (m : HwMaschine) (c : Nat) (len : Nat)
    (hzulaessig : merkmalZugelassen m.hw (m.bereit c) .sseDoppel = true)
    (hbuf : m.puffer c = [])
    (hok : laengeOk len = true) :
    ∃ (m2 : HwMaschine) (ev : LockEreignis),
      hwLockSchrittEv m c (.ok .mfence len) = some (m2, ev) ∧
      ev.istRmw = false ∧ ev.istZaun = true ∧
      RmwForm [ev] = false := by
  obtain ⟨hEv, -, -⟩ := hwLock_mfence_stimmt m c len hzulaessig hbuf hok
  refine ⟨_, _, hEv, rfl, rfl, ?_⟩
  simp [RmwForm]

/-! ## 5. Cost shape: constant fetch-add, unbounded CAS retry.

  One fetch-add costs one shape unit below every CAS retry count; no
  constant bounds CAS retry; unknown contention derives divergence
  (`none`), never a free constant. No bounded-retry, fairness,
  progress or cycle claim is made here. -/

/-- Cost shape without any retry promise: fetch-add is constant,
    CAS retry is unbounded, unknown contention diverges. -/
theorem tsoRmw_kosten_gestalt (a : Adresse) (delta : Wort) (n : Nat) :
    xaddKosten a delta = 1 ∧
    xaddKosten a delta ≤ casKosten n ∧
    (¬ ∃ K, ∀ k, casKosten k ≤ K) ∧
    retryBoundOf .unbekannt = none := by
  refine ⟨xadd_kosten_eins a delta, xadd_guenstiger_als_cas a delta n,
    cas_schleife_unbeschraenkt, retryBoundOf_unbekannt⟩

/-! ## 6. Joint witness: two cores, chained RMWs, owner-only forwarding.

  Reuses the accepted reached run (`hwLockWitStart`: word 10 at the
  witness address, core 1 holding one pending buffered byte outside
  the footprint): core 0 locked-adds 10 to 15, core 1 drains its byte
  and locked-adds 15 to 22. The second event reads exactly what the
  first one wrote -- the chaining conclusion on a reached run -- with
  the buffered byte forwarded to its owner only. -/

/-- First bridge event: core 0 locked-adds on the witness start. -/
def tsoRmwWitEv1 : Option (HwMaschine × LockEreignis) :=
  hwLockSchrittEv hwLockWitStart 0 (.ok (.xadd64 .rax .rbp 0) 9)

/-- Second bridge event: core 1 locked-adds after draining its byte. -/
def tsoRmwWitEv2 : Option (HwMaschine × LockEreignis) :=
  match hwLockWitBereit2 with
  | some m2 => hwLockSchrittEv m2 1 (.ok (.xadd64 .rax .rbp 0) 9)
  | none => none

/-- Observe the RMW tag of a bridge event (`none` if refused). -/
def tsoRmwEvRmw : Option (HwMaschine × LockEreignis) → Option Bool
  | some (_, ev) => some ev.istRmw
  | none => none

/-- Observe the read word of a bridge event (`none` if refused). -/
def tsoRmwEvGelesen : Option (HwMaschine × LockEreignis) →
    Option (Option Wort)
  | some (_, ev) => some ev.gelesen
  | none => none

/-- Observe the written word of a bridge event (`none` if refused). -/
def tsoRmwEvGeschrieben : Option (HwMaschine × LockEreignis) →
    Option (Option Wort)
  | some (_, ev) => some ev.geschrieben
  | none => none

/-- Observe the RMW trace shape of a bridge event (`none` if refused). -/
def tsoRmwEvForm : Option (HwMaschine × LockEreignis) → Option Bool
  | some (_, ev) => some (RmwForm [ev])
  | none => none

/-- First event is an RMW. -/
theorem tsoRmwWit_ev1_rmw : tsoRmwEvRmw tsoRmwWitEv1 = some true := by
  decide

/-- First event reads the initial word 10. -/
theorem tsoRmwWit_ev1_gelesen :
    tsoRmwEvGelesen tsoRmwWitEv1 = some (some 10) := by
  decide

/-- First event installs 15. -/
theorem tsoRmwWit_ev1_geschrieben :
    tsoRmwEvGeschrieben tsoRmwWitEv1 = some (some 15) := by
  decide

/-- Second event reads 15: no lost update on the reached run. -/
theorem tsoRmwWit_ev2_gelesen :
    tsoRmwEvGelesen tsoRmwWitEv2 = some (some 15) := by
  decide

/-- Second event installs 22 on the other core. -/
theorem tsoRmwWit_ev2_geschrieben :
    tsoRmwEvGeschrieben tsoRmwWitEv2 = some (some 22) := by
  decide

/-- First event carries the RMW trace shape. -/
theorem tsoRmwWit_ev1_form : tsoRmwEvForm tsoRmwWitEv1 = some true := by
  decide

/-- Joint bridge witness: a reached two-core run whose chained
    locked adds move the word 10 to 15 to 22 -- the second event reads
    exactly what the first one wrote -- with the buffered byte
    forwarded to its owner only, well-formedness, and the planted
    refusals beside the run. Non-degenerate: both steps change ACTUAL
    shared memory on different cores. -/
theorem tsoRmw_bruecke_zeuge :
    tsoRmwEvRmw tsoRmwWitEv1 = some true ∧
    tsoRmwEvGelesen tsoRmwWitEv1 = some (some 10) ∧
    tsoRmwEvGeschrieben tsoRmwWitEv1 = some (some 15) ∧
    tsoRmwEvGelesen tsoRmwWitEv2 = some (some 15) ∧
    tsoRmwEvGeschrieben tsoRmwWitEv2 = some (some 22) ∧
    tsoRmwEvForm tsoRmwWitEv1 = some true ∧
    HwWf hwLockWitStart ∧
    hwLockSicht hwLockWitNach1 1 hwLockWitFremdAdr =
      some (some (BitVec.ofNat 8 99)) ∧
    hwLockSicht hwLockWitNach1 0 hwLockWitFremdAdr =
      some (some (BitVec.ofNat 8 0)) ∧
    tsoRmwAdapter.schritt hwLockWitStart 1
      (.ok (.xadd64 .rax .rbp 0) 9) = none ∧
    tsoRmwAdapter.schritt hwLockWitUnaligned 0
      (.ok (.xadd64 .rax .rbp 0) 9) = none := by
  refine ⟨tsoRmwWit_ev1_rmw, tsoRmwWit_ev1_gelesen,
    tsoRmwWit_ev1_geschrieben, tsoRmwWit_ev2_gelesen,
    tsoRmwWit_ev2_geschrieben, tsoRmwWit_ev1_form, hwLockWitStart_wf,
    hwLockWit_nach1_eigen_sicht, hwLockWit_nach1_fremd_sicht,
    hwLockWit_puffer, hwLockWit_unaligned⟩

/- CUTS:
    Proved here: the TSO-to-RMW bridge plug (`tsoRmwAdapter`, reusing
    the accepted `adapterLockRmw` unchanged) with `HwWf` preservation
    (§1); exact agreement of admitted LOCK XADD, CMPXCHG-success and
    CMPXCHG-failure steps with the accepted step equations -- same
    guards, same successor and event, read-back, kept buffers, write
    permission pinned on the failure write-back -- each as ONE
    read-modify-write event over the full word footprint with
    `RmwForm` (§2); RMW atomicity -- no split pair reproduces the
    observation, chained locked adds serialize without loss
    (`ev2.gelesen = ev1.geschrieben`, the hardware-side shape behind
    `w_kein_verlust`) (§3); planted refusals -- parsed #UD, pending
    own store, misaligned word, fence without SSE2 -- plus the fence
    admitting as fence-only with no RMW shape (§4); cost shape --
    constant fetch-add below every CAS retry count, unbounded CAS
    retry, unknown contention diverges, no bounded-retry, fairness,
    progress or cycle claim (§5); the reached non-degenerate two-core
    joint witness `tsoRmw_bruecke_zeuge` (word 10 to 15 to 22 across
    two cores, owner-only forwarding, all refusals beside the run)
    (§6).
    Silicon provenance: Intel SDM 325462-093US Sep 2026 via the
    accepted 662 module (LOCK Vol. 2A 3-565/3-566, XADD Vol. 2D
    6-27/6-28, CMPXCHG Vol. 2A 3-193/3-194) and the accepted HwLockRmw
    producer -- this lane adds no new silicon claim beyond reusing
    those rows. Aligned whole-word atomicity stays a selected-profile
    contract (`ausgerichtet8` plus the empty own buffer), never a
    hardware proof.
    NOT proved here, and not claimed:
    - No per-access target-to-W/GX simulation: the timestamp/value
      link from the LOCK event words to the W history messages
      (`wahl`/`neu`, `Frisch`, the lowering certificate's value link)
      stays OPEN with the source/table-write consumer lanes. The
      `rmw` field of a full `SchrittW` is therefore supported (single
      atomic read-write pairing with no intervening buffered store)
      but not discharged here.
    - No hardware correspondence beyond self-consistency: encodings,
      flag effects and ordering rules are the accepted 662 rows.
    - No fetched-byte dispatch on `HwMaschine`: the plug takes parsed
      `LockAnweisung`; fetch stays with 662 `lockByteschritt`.
    - Narrower widths (8/16/32-bit), other addressing modes and
      split-lock detection stay open with 662/HwLockRmw.
    - No source, checker, contract, budget, duty or goal change:
      nothing here speaks about `Vertrag`, `Stmt`, duties or
      `gabbro_ziel`.
-/

#print axioms tsoRmwAdapter_wf
#print axioms tsoRmw_xadd_einzel_rmw
#print axioms tsoRmw_cmpxchg_erfolg_einzel_rmw
#print axioms tsoRmw_cmpxchg_fehlschlag_rmw
#print axioms tsoRmw_kein_split
#print axioms tsoRmw_kette_ohne_verlust
#print axioms tsoRmw_ud_bleibt_verweigert
#print axioms tsoRmw_puffer_bleibt_verweigert
#print axioms tsoRmw_unaligned_bleibt_verweigert
#print axioms tsoRmw_mfence_ohne_sse2_verweigert
#print axioms tsoRmw_mfence_kein_rmw
#print axioms tsoRmw_kosten_gestalt
#print axioms tsoRmwWit_ev1_rmw
#print axioms tsoRmwWit_ev1_gelesen
#print axioms tsoRmwWit_ev1_geschrieben
#print axioms tsoRmwWit_ev2_gelesen
#print axioms tsoRmwWit_ev2_geschrieben
#print axioms tsoRmwWit_ev1_form
#print axioms tsoRmw_bruecke_zeuge

end Gabbro.Grammatik.X86
