/-
  File:      Grammatik/X86/DeviceCommonExecution.lean
  Subject:   Port and device execution on the common machine.

  Lane 1102: lifts the accepted port/device rows (676 codecs,
  694 UC machine, 704 bus with IO permissions) onto HwMaschine:
  ordered IO event trace over fetched port/device bytes,
  privilege/IOPL/TSS outcomes derived through the accepted 728
  descriptor layer (reused definitions, never a parallel
  descriptor model), and a GENERIC device-response interface
  (explicit pending responses stay refused by a checked gate,
  never answered by fiat). The 694 construction is preserved:
  no TSOZustand buffer ever carries a device byte.

  Manual provenance: Intel SDM edition 325462-093US as cited in
  the accepted 676/694/704/728 headers; no new hardware claim.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.DeviceHardwareForms
import Grammatik.X86.HardwareExecution
import Grammatik.X86.DeviceBusHardwareExecution
import Grammatik.X86.MemoryTypeHardwareExecution
import Grammatik.X86.InterruptDescriptorHardware

namespace Gabbro.Grammatik.X86

namespace DeviceCommon1102

/-- Explicit pending device response: port, direction, width, value.
    A pending response is never consumed as an answer: the gate
    below refuses every step while one is outstanding. -/
structure PendingResp where
  port : Nat
  dir : IoDir
  breite : IoBreite
  wert : Nat
  deriving DecidableEq, Repr

/-- The pending gate: only an empty pending list admits a step. -/
def pendingLeer : List PendingResp → Bool
  | [] => true
  | _ :: _ => false

/-- An outstanding pending response refuses the gate. -/
theorem pending_belegt_verweigert (p : PendingResp)
    (rest : List PendingResp) :
    pendingLeer (p :: rest) = false := rfl

/-- The empty pending list passes the gate. -/
theorem pending_leer_ok : pendingLeer [] = true := rfl

/-! ## 2. Privilege through the accepted 728 descriptor layer.

    No parallel descriptor model is built here: the TSS bitmap
    window (base/limit) is read from the accepted 728 control
    state `Steuerstand`, the DPL check is the accepted
    `dplZugelassen`, and denial is classified in the accepted
    fault family (`busFehler` #GP beside `alsArch` #GP). -/

/-- TSS bitmap card from the 728 control state: base and limit are
    the TSS window, the bits are checked configuration data. -/
def devKarteAusSteuer (s : Steuerstand) (bit : Nat → Bool) :
    Bus704.TssKarte :=
  { basis := s.tssBasis.toNat, grenze := s.tssLimit, bit := bit }

/-- IO privilege from the 728 control state: CPL is the current
    level, IOPL arrives as explicit checked data. -/
def devRechtAusSteuer (s : Steuerstand) (iopl : Nat) :
    Bus704.IoBerechtigung :=
  ⟨s.cpl, iopl⟩

/-- A missing TSS window denies every byte through the 728-derived
    card: the accepted missing-map rule, lifted. -/
theorem dev_karte_fehlt_verweigert (s : Steuerstand)
    (bit : Nat → Bool) (q : Nat)
    (h : s.tssLimit ≤ s.tssBasis.toNat) :
    Bus704.tssBitFrei (devKarteAusSteuer s bit) q = false :=
  Bus704.karte_fehlt_verweigert _ q h

/-- DPL refusal through the accepted 728 check: a software INT at a
    higher CPL than the gate DPL is refused. -/
theorem dev_dpl_verweigert_software (gateDpl cpl : Nat)
    (h : ¬ cpl ≤ gateDpl) :
    dplZugelassen (.softwareInt false) gateDpl cpl = false :=
  dpl_verweigert_software gateDpl cpl h

/-- Denial faults in the accepted family: the port #GP beside the
    728 #GP member (no parallel fault class). -/
theorem dev_verweigerung_ist_gp (v : Nat) :
    Bus704.busFehler false = some .gp ∧
      alsArch (.limitFehler v) = some .gp :=
  ⟨rfl, rfl⟩

/-! ## 3. Generic device step on the common machine.

    The step reuses the accepted generic `BusSchritt` on the core
    projection: no second IN/OUT interpreter, no second decoder and
    no TSO buffer is ever touched (the successor only re-embeds
    core data, exactly like `setKernVonFp`). The TSO drain
    obligation (`ordnungOk`) and the pending gate are exposed
    premises, never derived. -/

/-- Core-data successor from a reached bus core: registers, flags
    and RIP move; XMM and FP context are kept. -/
def hwKernAusZustand (m : HwMaschine) (c : Nat) (z : Zustand) : HwKern :=
  ⟨z.register, z.flags, z.rip, (m.kerne c).xmm, (m.kerne c).fp⟩

/-- Direction bridge: both IO directions share the one
    fence-readiness gate (Table 20-1 needs a drained own buffer on
    both rows). -/
theorem ordnungOk_zaun (tso : TSOZustand) (c : Nat) (dir : IoDir) :
    Bus704.ordnungOk tso c dir = zaunBereit tso c := by
  cases dir <;> rfl

/-- One generic device step on the common machine: a reached
    accepted bus step on the core projection, under a drained own
    TSO buffer and an empty pending list. Denial (bad fetch,
    denied permission, full buffer, pending response, no allowed
    answer) has NO constructor: it is the absence of a step. -/
inductive DeviceCommonSchritt (D : Type)
    (erlaubt : Bus704.BusAntwort D) (r : Bus704.IoBerechtigung)
    (k : Bus704.TssKarte) (pend : List PendingResp)
    (m : HwMaschine) (c : Nat) (g : D) (spur : List IoEreignis) :
    HwMaschine → D → List IoEreignis → Prop where
  | schritt (s' : Bus704.BusZustand D)
      (hbus : Bus704.BusSchritt D erlaubt r k
        ⟨projZustand m c, g, spur⟩ s')
      (hord : zaunBereit (tsoAnsicht m) c = true)
      (hpend : pendingLeer pend = true) :
      DeviceCommonSchritt D erlaubt r k pend m c g spur
        (setKernDaten m c (hwKernAusZustand m c s'.kern))
        s'.geraet s'.spur

/-- A common device step never touches shared memory. -/
theorem devSchritt_speicher (D : Type)
    (erlaubt : Bus704.BusAntwort D) (r : Bus704.IoBerechtigung)
    (k : Bus704.TssKarte) (pend : List PendingResp)
    (m m' : HwMaschine) (c : Nat) (g : D) (spur : List IoEreignis)
    (g' : D) (spur' : List IoEreignis)
    (h : DeviceCommonSchritt D erlaubt r k pend m c g spur
      m' g' spur') :
    m'.mem = m.mem := by
  cases h
  rfl

/-- A common device step never touches any TSO buffer: no buffer
    ever carries a device byte, by construction. -/
theorem devSchritt_puffer (D : Type)
    (erlaubt : Bus704.BusAntwort D) (r : Bus704.IoBerechtigung)
    (k : Bus704.TssKarte) (pend : List PendingResp)
    (m m' : HwMaschine) (c : Nat) (g : D) (spur : List IoEreignis)
    (g' : D) (spur' : List IoEreignis)
    (h : DeviceCommonSchritt D erlaubt r k pend m c g spur
      m' g' spur') :
    m'.puffer = m.puffer := by
  cases h
  rfl

/-- A common device step appends exactly one ordered event. -/
theorem devSchritt_spur_waechst (D : Type)
    (erlaubt : Bus704.BusAntwort D) (r : Bus704.IoBerechtigung)
    (k : Bus704.TssKarte) (pend : List PendingResp)
    (m m' : HwMaschine) (c : Nat) (g : D) (spur : List IoEreignis)
    (g' : D) (spur' : List IoEreignis)
    (h : DeviceCommonSchritt D erlaubt r k pend m c g spur
      m' g' spur') :
    spur'.length = spur.length + 1 := by
  cases h with
  | schritt s' hbus hord hpend =>
    exact Bus704.busSchritt_spur_waechst D erlaubt r k _ s' hbus

/-- A common device step keeps every XMM register of the acting core. -/
theorem devSchritt_xmm (D : Type)
    (erlaubt : Bus704.BusAntwort D) (r : Bus704.IoBerechtigung)
    (k : Bus704.TssKarte) (pend : List PendingResp)
    (m m' : HwMaschine) (c : Nat) (g : D) (spur : List IoEreignis)
    (g' : D) (spur' : List IoEreignis)
    (h : DeviceCommonSchritt D erlaubt r k pend m c g spur
      m' g' spur')
    (q : XmmReg) :
    ((m'.kerne c).xmm q) = ((m.kerne c).xmm q) := by
  cases h with
  | schritt s' hbus hord hpend =>
    unfold setKernDaten hwKernAusZustand
    simp

/-! ## 4. Fetched port/device step on the common machine.

    Fetch reads the acting core projection's ACTUAL executable
    bytes through the accepted `fetchIo`; the successor cores reuse
    the accepted `ausKern`/`einKern`; the latch answers come from
    the accepted computable `geraetAntwort`. The generic Prop
    interface of §3 stays the semantic reference: both selection
    lemmas below tie the computable step to a reached generic
    step, so no fiat answer is ever consumed. -/

/-- Outcome of one fetched common device step. -/
inductive DevCommonAusgang where
  | weiter : HwMaschine → GeraetZustand → List IoEreignis →
      DevCommonAusgang
  | verweigert : DevCommonAusgang

/-- One fetched port/device step on core `c`: fetch from actual
    bytes, architectural permission at the effective port, drained
    own TSO buffer, empty pending list, then the accepted latch
    answer. Anything else is `.verweigert`. -/
def deviceCommon_byteschritt (r : Bus704.IoBerechtigung)
    (k : Bus704.TssKarte) (pend : List PendingResp) (m : HwMaschine)
    (c : Nat) (g : GeraetZustand) (spur : List IoEreignis) :
    DevCommonAusgang :=
  match fetchIo (projZustand m c) with
  | none => .verweigert
  | some (dec, _) =>
    match dec.op with
    | ⟨.aus, b, _⟩ =>
      if laengeOk dec.laenge &&
          Bus704.archZugelassen r k
            (portVon dec.op (projZustand m c).register) b &&
          zaunBereit (tsoAnsicht m) c && pendingLeer pend then
        .weiter
          (setKernDaten m c
            (hwKernAusZustand m c
              (Bus704.ausKern (projZustand m c) dec)))
          (geraetAntwort g .aus b
            (ausGabe b ((projZustand m c).register .rax))).1
          (spur ++ [⟨.aus, b,
            portVon dec.op (projZustand m c).register,
            ausGabe b ((projZustand m c).register .rax)⟩])
      else .verweigert
    | ⟨.ein, b, _⟩ =>
      if laengeOk dec.laenge &&
          Bus704.archZugelassen r k
            (portVon dec.op (projZustand m c).register) b &&
          zaunBereit (tsoAnsicht m) c && pendingLeer pend then
        .weiter
          (setKernDaten m c
            (hwKernAusZustand m c
              (Bus704.einKern (projZustand m c) dec b
                (geraetAntwort g .ein b 0).2)))
          (geraetAntwort g .ein b 0).1
          (spur ++ [⟨.ein, b,
            portVon dec.op (projZustand m c).register,
            (geraetAntwort g .ein b 0).2⟩])
      else .verweigert

/-- The latch OUT pair in projection form. -/
theorem latchAus_paar (g : GeraetZustand) (b : IoBreite)
    (v : Nat) :
    (geraetAntwort g .aus b v).1 = ⟨v % ioMaske b, g.zaehl + 1⟩ :=
  rfl

/-- The latch OUT answer is the channel zero. -/
theorem latchAus_ant0 (g : GeraetZustand) (b : IoBreite)
    (v : Nat) :
    (geraetAntwort g .aus b v).2 = 0 := rfl

/-- The latch IN pair in projection form. -/
theorem latchEin_paar (g : GeraetZustand) (b : IoBreite) :
    (geraetAntwort g .ein b 0).1 = ⟨g.daten, g.zaehl + 1⟩ := rfl

/-- The latch IN answer in projection form. -/
theorem latchEin_ant (g : GeraetZustand) (b : IoBreite) :
    (geraetAntwort g .ein b 0).2 = g.daten % ioMaske b := rfl

/-- SELECTION (OUT): a fetched port OUT under permission, drained
    buffer and empty pending list computes the successor AND
    justifies a reached generic step. -/
theorem deviceCommon_aus_fetch (r : Bus704.IoBerechtigung)
    (k : Bus704.TssKarte) (pend : List PendingResp) (m : HwMaschine)
    (c : Nat) (g : GeraetZustand) (spur : List IoEreignis)
    (d : IoDec) (rest : List Byte) (b : IoBreite) (q : PortQuelle)
    (hf : fetchIo (projZustand m c) = some (d, rest))
    (hop : d.op = ⟨.aus, b, q⟩)
    (hlen : laengeOk d.laenge = true)
    (hperm : Bus704.archZugelassen r k
      (portVon ⟨.aus, b, q⟩ (projZustand m c).register) b = true)
    (hord : zaunBereit (tsoAnsicht m) c = true)
    (hpend : pendingLeer pend = true) :
    deviceCommon_byteschritt r k pend m c g spur =
      .weiter
        (setKernDaten m c
          (hwKernAusZustand m c (Bus704.ausKern (projZustand m c) d)))
        (geraetAntwort g .aus b
          (ausGabe b ((projZustand m c).register .rax))).1
        (spur ++ [⟨.aus, b,
          portVon d.op (projZustand m c).register,
          ausGabe b ((projZustand m c).register .rax)⟩]) ∧
    DeviceCommonSchritt GeraetZustand Bus704.latchErlaubt r k pend
      m c g spur
      (setKernDaten m c
        (hwKernAusZustand m c (Bus704.ausKern (projZustand m c) d)))
      (geraetAntwort g .aus b
        (ausGabe b ((projZustand m c).register .rax))).1
      (spur ++ [⟨.aus, b,
        portVon d.op (projZustand m c).register,
        ausGabe b ((projZustand m c).register .rax)⟩]) := by
  have hant : Bus704.latchErlaubt g .aus b
      (portVon d.op (projZustand m c).register)
      (ausGabe b ((projZustand m c).register .rax))
      (geraetAntwort g .aus b
        (ausGabe b ((projZustand m c).register .rax))).1
      0 := by
    rw [latchAus_paar]
    exact Bus704.latch_aus_sound g b _ _
  have hperm' : Bus704.archZugelassen r k
      (portVon d.op (projZustand m c).register) b = true := by
    rw [hop]
    exact hperm
  refine ⟨?_, .schritt _ (.aus _ d b q _ hlen hop hperm' hant) hord
    hpend⟩
  unfold deviceCommon_byteschritt
  rw [hf]
  simp [hop, hlen, hperm, hord, hpend]

/-- SELECTION (IN): a fetched port IN under permission, drained
    buffer and empty pending list computes the successor AND
    justifies a reached generic step. -/
theorem deviceCommon_ein_fetch (r : Bus704.IoBerechtigung)
    (k : Bus704.TssKarte) (pend : List PendingResp) (m : HwMaschine)
    (c : Nat) (g : GeraetZustand) (spur : List IoEreignis)
    (d : IoDec) (rest : List Byte) (b : IoBreite) (q : PortQuelle)
    (hf : fetchIo (projZustand m c) = some (d, rest))
    (hop : d.op = ⟨.ein, b, q⟩)
    (hlen : laengeOk d.laenge = true)
    (hperm : Bus704.archZugelassen r k
      (portVon ⟨.ein, b, q⟩ (projZustand m c).register) b = true)
    (hord : zaunBereit (tsoAnsicht m) c = true)
    (hpend : pendingLeer pend = true) :
    deviceCommon_byteschritt r k pend m c g spur =
      .weiter
        (setKernDaten m c
          (hwKernAusZustand m c
            (Bus704.einKern (projZustand m c) d b
              (geraetAntwort g .ein b 0).2)))
        (geraetAntwort g .ein b 0).1
        (spur ++ [⟨.ein, b,
          portVon d.op (projZustand m c).register,
          (geraetAntwort g .ein b 0).2⟩]) ∧
    DeviceCommonSchritt GeraetZustand Bus704.latchErlaubt r k pend
      m c g spur
      (setKernDaten m c
        (hwKernAusZustand m c
          (Bus704.einKern (projZustand m c) d b
            (geraetAntwort g .ein b 0).2)))
      (geraetAntwort g .ein b 0).1
      (spur ++ [⟨.ein, b,
        portVon d.op (projZustand m c).register,
        (geraetAntwort g .ein b 0).2⟩]) := by
  have hant : Bus704.latchErlaubt g .ein b
      (portVon d.op (projZustand m c).register) 0
      (geraetAntwort g .ein b 0).1
      (geraetAntwort g .ein b 0).2 := by
    rw [latchEin_paar, latchEin_ant]
    exact Bus704.latch_ein_sound g b _
  have hperm' : Bus704.archZugelassen r k
      (portVon d.op (projZustand m c).register) b = true := by
    rw [hop]
    exact hperm
  refine ⟨?_, .schritt _ (.ein _ d b q _ _ hlen hop hperm' hant) hord
    hpend⟩
  unfold deviceCommon_byteschritt
  rw [hf]
  simp [hop, hlen, hperm, hord, hpend]

/-- The pending gate is a premise of every reached step: an
    outstanding pending response is never consumed as an answer. -/
theorem devSchritt_pending_leer (D : Type)
    (erlaubt : Bus704.BusAntwort D) (r : Bus704.IoBerechtigung)
    (k : Bus704.TssKarte) (pend : List PendingResp)
    (m m' : HwMaschine) (c : Nat) (g : D) (spur : List IoEreignis)
    (g' : D) (spur' : List IoEreignis)
    (h : DeviceCommonSchritt D erlaubt r k pend m c g spur
      m' g' spur') :
    pendingLeer pend = true := by
  cases h with
  | schritt s' hbus hord hpend => exact hpend

/-! ## 5. The two target separation theorems.

    `deviceCommon_tso_verweigert`: no TSO buffer ever carries a
    device byte -- every reached common step leaves every buffer
    unchanged (construction, §3 frames), and a device byte offered
    to the RAM TSO rule is refused by the rule itself
    (`issue_verweigert` over checked permissions).

    `deviceCommon_mmio_ordnung`: MMIO never inherits WB-RAM
    ordering -- a retired UC store bypasses the WB buffer
    (`ucStore_bypass`) and bus completion preserves it
    (`busFortschritt_fifo`), so neither side orders the other. -/

/-- TARGET: device traffic is excluded from the RAM TSO rule --
    buffers are unchanged by every reached step, and the issue
    rule refuses the device address. -/
theorem deviceCommon_tso_verweigert (D : Type)
    (erlaubt : Bus704.BusAntwort D) (r : Bus704.IoBerechtigung)
    (k : Bus704.TssKarte) (pend : List PendingResp)
    (m m' : HwMaschine) (c : Nat) (g : D) (spur : List IoEreignis)
    (g' : D) (spur' : List IoEreignis) (a : Adresse) (v : Byte)
    (hstep : DeviceCommonSchritt D erlaubt r k pend m c g spur
      m' g' spur')
    (hro : (tsoAnsicht m).mem.schreibbar a = false) :
    m'.puffer c = m.puffer c ∧
      issueByte (tsoAnsicht m) c a v = none := by
  have hpuffer := devSchritt_puffer D erlaubt r k pend m m' c g spur
    g' spur' hstep
  have hnone := issue_verweigert (tsoAnsicht m) c a v hro
  rw [hpuffer]
  exact ⟨rfl, hnone⟩

/-- TARGET: MMIO never inherits WB-RAM ordering -- a UC store
    retires past the WB buffer and bus completion drains past it;
    the pending WB stores are untouched on both legs. -/
theorem deviceCommon_mmio_ordnung (m : MmioMaschine) (hw : HwProfil)
    (bp : BereitProfil) (b : Breite) (a : Adresse) (v : Wort)
    (m1 m2 : MmioMaschine) (p : PostedSchreib)
    (rest : List PostedSchreib) (g' : Geraet)
    (hstore : ucStoreZugriff m hw bp b a v = some m1)
    (he : m1.ausstehend = p :: rest)
    (hg : geraetSchreibt m1.geraet p.breite (geraetOff p.addr)
      p.wert = some g')
    (hbus : busFortschritt m1 = some m2) :
    m1.pending = m.pending ∧ m2.pending = m.pending ∧
      m2.ausstehend = rest ∧ m2.ucLog = m1.ucLog := by
  obtain ⟨hp1, _, _, _, _, _⟩ :=
    ucStore_bypass m hw bp b a v m1 hstore
  obtain ⟨m', hbm, _, haus, hlog, _, hpend2⟩ :=
    busFortschritt_fifo m1 p rest g' he hg
  rw [hbm] at hbus
  have heq : m2 = m' := (Option.some_inj.mp hbus).symm
  subst heq
  exact ⟨hp1, hpend2.trans hp1, haus, hlog⟩

/-! ## 6. Joint witness: fetched run on the common machine.

    Core 0 stands on the accepted port image (`ioWitKern`: an 8-bit
    IN from port 96, an 8-bit OUT to 96, then the pilot 64-bit
    store); the device starts at `0x1234`. Privilege is the direct
    leg (CPL 3 against IOPL 3) over the fully spanned map. The run
    reaches the memory-changing pilot store (reused
    `ioWit_dritter_speichert` from a zeroed cell), beside the three
    planted refusals: a device byte offered to the RAM TSO rule,
    an unprivileged access under a denying 728-derived card, and a
    pending response consumed as an answer. -/

/-- Witness core data: core 0 on the accepted port image, the rest
    idle on the data page. -/
def devWitKern : Nat → HwKern
  | 0 => ⟨ioWitKern.register, ioWitKern.flags, ioWitKern.rip,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0,
      kontextReset⟩

/-- Witness start machine: shared port image, empty buffers, full
    silicon with OS vector state. -/
def devWitStart : HwMaschine :=
  ⟨ioWitSpeicher, devWitKern, fun _ => [], basisHw,
    fun _ => basisBereit⟩

/-- First fetched step on core 0. -/
def devWitO1 : DevCommonAusgang :=
  deviceCommon_byteschritt Bus704.witRecht Bus704.witKarte []
    devWitStart 0 ⟨0x1234, 0⟩ []

/-- Second fetched step on core 0 (over the first successor). -/
def devWitO2 : DevCommonAusgang :=
  match devWitO1 with
  | .weiter m g sp =>
    deviceCommon_byteschritt Bus704.witRecht Bus704.witKarte []
      m 0 g sp
  | .verweigert => .verweigert

/-- Observe the accumulator of core 0 as a natural. -/
def devAkkOut : DevCommonAusgang → Option Nat
  | .weiter m _ _ => some ((m.kerne 0).register .rax).toNat
  | .verweigert => none

/-- Observe the ordered trace. -/
def devSpurOut : DevCommonAusgang → Option (List IoEreignis)
  | .weiter _ _ sp => some sp
  | .verweigert => none

/-- Observe RIP of core 0 as a natural. -/
def devRipOut : DevCommonAusgang → Option Nat
  | .weiter m _ _ => some (m.kerne 0).rip.toNat
  | .verweigert => none

/-- Observe the device register and counter. -/
def devGeraetOut : DevCommonAusgang → Option (Nat × Nat)
  | .weiter _ g _ => some (g.daten, g.zaehl)
  | .verweigert => none

/-- Observe one shared-memory byte as a natural. -/
def devMemOut (o : DevCommonAusgang) (n : Nat) : Option Nat :=
  match o with
  | .weiter m _ _ => some (m.mem.bytes (BitVec.ofNat 64 n)).toNat
  | .verweigert => none

/-- Observe a buffer length. -/
def devPufferOut : DevCommonAusgang → Nat → Option Nat
  | .weiter m _ _, c => some (m.puffer c).length
  | .verweigert, _ => none

/-- Refusal probe out of a step outcome. -/
def devVerweigert : DevCommonAusgang → Bool
  | .weiter _ _ _ => false
  | .verweigert => true

/-- First step: the fetched IN answers 52 into AL. -/
theorem dev_wit_s1_akk : devAkkOut devWitO1 = some 52 := by
  decide

/-- The first fetch decodes the actual IN from the witness window,
    with the 13 remaining window bytes. -/
theorem dev_fetch_s1 :
    fetchIo (projZustand devWitStart 0) =
      some (⟨⟨.ein, .p8, .imm 96⟩, 2⟩,
        [natByte 230, natByte 96, natByte 72, natByte 137,
          natByte 131, natByte 0, natByte 0, natByte 0, natByte 0,
          natByte 0, natByte 0, natByte 0, natByte 0]) := by
  decide

/-- Exhibited reached generic step: the first fetched IN is a
    `DeviceCommonSchritt` with all premises jointly instantiated
    (fetch, length, direct-leg permission, drained buffer, empty
    pending list, allowed latch answer). -/
theorem deviceCommon_schritt_zeuge :
    ∃ (m' : HwMaschine) (g' : GeraetZustand) (sp' : List IoEreignis),
      DeviceCommonSchritt GeraetZustand Bus704.latchErlaubt
        Bus704.witRecht Bus704.witKarte [] devWitStart 0
        ⟨0x1234, 0⟩ [] m' g' sp' ∧
      g'.daten = 0x1234 ∧ g'.zaehl = 1 ∧
        sp' = [⟨.ein, .p8, 96, 52⟩] := by
  have h := (deviceCommon_ein_fetch Bus704.witRecht Bus704.witKarte
    [] devWitStart 0 ⟨0x1234, 0⟩ []
    ⟨⟨.ein, .p8, .imm 96⟩, 2⟩
    [natByte 230, natByte 96, natByte 72, natByte 137,
      natByte 131, natByte 0, natByte 0, natByte 0, natByte 0,
      natByte 0, natByte 0, natByte 0, natByte 0]
    .p8 (.imm 96) dev_fetch_s1 rfl (by decide) (by decide)
    (by decide) rfl).2
  exact ⟨_, _, _, h, rfl, rfl, rfl⟩

/-- First step logs exactly the ordered IN event. -/
theorem dev_wit_s1_spur :
    devSpurOut devWitO1 = some [⟨.ein, .p8, 96, 52⟩] := by
  decide

/-- Both steps: the device moved `0x1234` to 52 with two
    observations and the accumulator holds 52. -/
theorem dev_wit_s2_geraet :
    devGeraetOut devWitO2 = some (52, 2) ∧
      devAkkOut devWitO2 = some 52 := by
  decide

/-- Both steps log IN then OUT in order. -/
theorem dev_wit_s2_spur :
    devSpurOut devWitO2 =
      some [⟨.ein, .p8, 96, 52⟩, ⟨.aus, .p8, 96, 52⟩] := by
  decide

/-- Both steps land RIP at 4100: the pilot store starts from the
    same core state as the accepted run. -/
theorem dev_wit_s2_rip : devRipOut devWitO2 = some 4100 := by
  decide

/-- FRAME: both steps bypass RAM -- the cell the pilot store will
    write still reads zero. -/
theorem dev_wit_s2_mem_null : devMemOut devWitO2 8192 = some 0 := by
  decide

/-- FRAME: both steps issue no buffer entry on any core. -/
theorem dev_wit_s2_puffer_leer :
    devPufferOut devWitO2 0 = some 0 ∧
      devPufferOut devWitO2 1 = some 0 := by
  decide

/-! ## 7. Planted refusals: one per target separation.

    PROBE 1 (TSO exclusion): the MMIO window byte offered to the
    RAM TSO issue rule is refused -- the device window is not
    writable RAM in the witness image.
    PROBE 2 (privilege): an unprivileged access (CPL 3 against
    IOPL 0) under a 728-derived denying card (missing TSS window,
    so no bitmap byte is spanned) refuses before any device
    contact; the 728 software-INT DPL check refuses the same
    privilege shape.
    PROBE 3 (pending): the reached first step with one outstanding
    pending response refuses -- the pending answer is never
    consumed. -/

/-- Denying control state: CPL 3 with a missing TSS window (limit
    below base), so every bitmap byte denies. -/
def devSteuerDunkel : Steuerstand :=
  ⟨BitVec.ofNat 64 4096, 47, BitVec.ofNat 64 12288, 0, 3, true⟩

/-- Denying card derived from the denying control state: all bits
    set, and the window missing in any case. -/
def devKarteDunkel : Bus704.TssKarte :=
  devKarteAusSteuer devSteuerDunkel (fun _ => true)

/-- PROBE 1: the device-window byte is refused by the RAM TSO
    issue rule. -/
theorem dev_probe_tso_verweigert :
    issueByte ⟨ioWitSpeicher, fun _ => []⟩ 0 (natAdresse 65536)
      (natByte 1) = none := by
  decide

/-- PROBE 2a: the denying card refuses port 96 above IOPL. -/
theorem dev_probe_privileg_karte :
    Bus704.archZugelassen ⟨3, 0⟩ devKarteDunkel 96 .p8 = false := by
  decide

/-- PROBE 2b: the fetched step refuses under the denying card. -/
theorem dev_probe_privileg_schritt :
    devVerweigert
      (deviceCommon_byteschritt ⟨3, 0⟩ devKarteDunkel []
        devWitStart 0 ⟨0x1234, 0⟩ []) = true := by
  decide

/-- PROBE 2c: the 728 DPL check refuses the same privilege shape
    for a software interrupt. -/
theorem dev_probe_privileg_dpl :
    dplZugelassen (.softwareInt false) 0 3 = false := by
  decide

/-- PROBE 3: one outstanding pending response refuses the reached
    first step. -/
theorem dev_probe_pending_verweigert :
    devVerweigert
      (deviceCommon_byteschritt Bus704.witRecht Bus704.witKarte
        [⟨96, .ein, .p8, 52⟩] devWitStart 0 ⟨0x1234, 0⟩ []) =
      true := by
  decide

/-! ## 8. Joint witness and target companions.

    One conjunction ties the reached fetched IN/OUT run (device
    `0x1234` to 52, two observations, ordered log, RIP at the pilot
    store, empty buffers, zeroed RAM cell) to the memory-changing
    pilot store and all three planted refusals. Non-degenerate:
    the device observably changed state AND the run reaches the
    memory-changing pilot store. -/

/-- JOINT WITNESS. -/
theorem deviceCommon_zeuge_gemeinsam :
    devAkkOut devWitO1 = some 52 ∧
      devGeraetOut devWitO2 = some (52, 2) ∧
      devSpurOut devWitO2 =
        some [⟨.ein, .p8, 96, 52⟩, ⟨.aus, .p8, 96, 52⟩] ∧
      devRipOut devWitO2 = some 4100 ∧
      devMemOut devWitO2 8192 = some 0 ∧
      devPufferOut devWitO2 0 = some 0 ∧
      ausgangByte (BitVec.ofNat 64 8192) ioWitSchritt3 =
        some (BitVec.ofNat 8 52) ∧
      ioWitStart.kern.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 ∧
      issueByte ⟨ioWitSpeicher, fun _ => []⟩ 0 (natAdresse 65536)
        (natByte 1) = none ∧
      Bus704.archZugelassen ⟨3, 0⟩ devKarteDunkel 96 .p8 = false ∧
      devVerweigert
        (deviceCommon_byteschritt ⟨3, 0⟩ devKarteDunkel []
          devWitStart 0 ⟨0x1234, 0⟩ []) = true ∧
      dplZugelassen (.softwareInt false) 0 3 = false ∧
      devVerweigert
        (deviceCommon_byteschritt Bus704.witRecht Bus704.witKarte
          [⟨96, .ein, .p8, 52⟩] devWitStart 0 ⟨0x1234, 0⟩ []) =
        true := by
  refine ⟨dev_wit_s1_akk, dev_wit_s2_geraet.1, dev_wit_s2_spur,
    dev_wit_s2_rip, dev_wit_s2_mem_null, dev_wit_s2_puffer_leer.1,
    ioWit_dritter_speichert.1, ioWit_anfang_null,
    dev_probe_tso_verweigert, dev_probe_privileg_karte,
    dev_probe_privileg_schritt, dev_probe_privileg_dpl,
    dev_probe_pending_verweigert⟩

/-- Companion for `deviceCommon_byteschritt`: the fetched step
    succeeds on the witness with the device answer and the ordered
    event. -/
theorem deviceCommon_byteschritt_zeuge :
    devAkkOut devWitO1 = some 52 ∧
      devSpurOut devWitO1 = some [⟨.ein, .p8, 96, 52⟩] ∧
      devVerweigert
        (deviceCommon_byteschritt Bus704.witRecht Bus704.witKarte
          [⟨96, .ein, .p8, 52⟩] devWitStart 0 ⟨0x1234, 0⟩ []) =
        true :=
  ⟨dev_wit_s1_akk, dev_wit_s1_spur, dev_probe_pending_verweigert⟩

/-- Witness MMIO machine: the reset device, no pending WB stores,
    the device-window profile. -/
def ordWitM : MmioMaschine :=
  ⟨witFp, [], geraetAnfang, [], [], witProfil⟩

/-- The MMIO store/complete chain is jointly instantiable on the
    witness: retire then bus-complete succeeds. -/
theorem ordWit_kette :
    ((ucStoreZugriff ordWitM basisHw basisBereit .b64
      (natAdresse 65536) (BitVec.ofNat 64 42)).bind
      busFortschritt).isSome = true := by
  decide

/-- Companion for `deviceCommon_tso_verweigert`: buffers unchanged
    on the reached witness run, and the RAM rule refuses the
    device byte. -/
theorem deviceCommon_tso_verweigert_zeuge :
    devPufferOut devWitO2 0 = some 0 ∧
      devPufferOut devWitO2 1 = some 0 ∧
      issueByte ⟨ioWitSpeicher, fun _ => []⟩ 0 (natAdresse 65536)
        (natByte 1) = none :=
  ⟨dev_wit_s2_puffer_leer.1, dev_wit_s2_puffer_leer.2,
    dev_probe_tso_verweigert⟩

/-- Companion for `deviceCommon_mmio_ordnung`: the witness
    store/complete chain runs with empty WB pending throughout. -/
theorem deviceCommon_mmio_ordnung_zeuge :
    ((ucStoreZugriff ordWitM basisHw basisBereit .b64
      (natAdresse 65536) (BitVec.ofNat 64 42)).bind
      busFortschritt).isSome = true ∧
      ordWitM.pending = [] :=
  ⟨ordWit_kette, rfl⟩

/- CUTS:
   Proved here, over the REUSED accepted vocabulary (`Typen`,
   `Speicher`, `TSO`, `DeviceHardwareForms`, `HardwareExecution`,
   `Bus704`, 694 `MmioMaschine`, 728 descriptors -- no second
   decoder, no parallel descriptor model, no second IN/OUT
   interpreter, no new machine):
   - generic device-response interface over an arbitrary device
     type (the accepted `BusAntwort` relation) with the explicit
     pending gate: outstanding pending responses refuse every
     step (`devSchritt_pending_leer`, `pending_belegt_verweigert`);
   - privilege/IOPL/TSS through the 728 layer (card and right
     from `Steuerstand`, DPL check, shared #GP family);
   - fetched port/device step on HwMaschine with both selection
     lifts to reached generic steps;
   - TSO exclusion (buffers never carry device bytes; the RAM
     rule refuses the device byte) and MMIO order separation
     (UC bypass and bus completion both pass the WB buffer by);
   - joint reached fetched-IN/OUT run (device `0x1234` to 52)
     into the accepted memory-changing pilot store, beside the
     three planted refusals.
   NOT proved here, and not claimed:
   - No hardware correspondence beyond the cited Intel SDM
     entries of 676/694/704/728 (provenance, not proofs).
   - Pending responses enumerated, never answered: no claim
     about what any concrete device answers.
   - No per-access target-to-W/GX simulation and no whole-word
     atomicity beyond the accepted grouping.
   - No source correspondence, no ABI/image/entry/relocation/
     budget link, no syscall/interrupt scope.
-/

#print axioms pending_belegt_verweigert
#print axioms pending_leer_ok
#print axioms dev_karte_fehlt_verweigert
#print axioms dev_dpl_verweigert_software
#print axioms dev_verweigerung_ist_gp
#print axioms ordnungOk_zaun
#print axioms devSchritt_speicher
#print axioms devSchritt_puffer
#print axioms devSchritt_spur_waechst
#print axioms devSchritt_xmm
#print axioms devSchritt_pending_leer
#print axioms deviceCommon_aus_fetch
#print axioms deviceCommon_ein_fetch
#print axioms deviceCommon_tso_verweigert
#print axioms deviceCommon_mmio_ordnung
#print axioms deviceCommon_zeuge_gemeinsam
#print axioms deviceCommon_schritt_zeuge
#print axioms deviceCommon_byteschritt_zeuge
#print axioms deviceCommon_tso_verweigert_zeuge
#print axioms deviceCommon_mmio_ordnung_zeuge

#print axioms pending_belegt_verweigert
#print axioms pending_leer_ok

end DeviceCommon1102

end Gabbro.Grammatik.X86
