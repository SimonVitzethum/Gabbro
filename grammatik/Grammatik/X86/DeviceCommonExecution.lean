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

#print axioms pending_belegt_verweigert
#print axioms pending_leer_ok

end DeviceCommon1102

end Gabbro.Grammatik.X86
