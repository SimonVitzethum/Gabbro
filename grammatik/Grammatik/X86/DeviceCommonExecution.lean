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

#print axioms pending_belegt_verweigert
#print axioms pending_leer_ok

end DeviceCommon1102

end Gabbro.Grammatik.X86
