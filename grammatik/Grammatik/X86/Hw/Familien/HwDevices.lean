/-
  File:      Grammatik/X86/HwDevices.lean
  Subject:   Device/MMIO and memory types on the coherent machine.

  Lane 1133: lifts the accepted UC MMIO evaluator (lane 694,
  `MemoryTypeHardwareExecution`) and the generic port bus (lane 704,
  `DeviceBusHardwareExecution`) onto the coherent machine (lane 660,
  `HardwareExecution`). Uncacheable/MMIO accesses are never
  store-buffered like write-back RAM: the exact ordering rule is stated
  as a named assumption; bus/device events are exposed as `HwAdapter`
  plugs; DMA stays a named assumption with no step.

  Manual provenance: Intel SDM edition 325462-093US as cited in the
  accepted 676/694/704 headers; no new hardware claim here.
-/
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Grundlage.DeviceHardwareForms
import Grammatik.X86.Hw.Grundlage.DeviceBusHardwareExecution
import Grammatik.X86.Speicher.MemoryTypeHardwareExecution

namespace Gabbro.Grammatik.X86

namespace HwDev1133

/-- The extended coherent device machine: the coherent machine plus
    the software-established UC profile, the generic MMIO device,
    posted UC writes awaiting bus completion, and the UC
    program-order log. WB buffers stay inside `masch`. -/
structure HwDevMaschine where
  masch : HwMaschine
  profil : UcProfil
  geraet : Geraet
  ausstehend : List PostedSchreib
  ucLog : List UcEreignis

/-! ## 1. Named assumptions: the UC ordering rule and DMA.

  The exact ordering rule used (SDM Vol.1 20.5/20.6, Vol.3A 14.3
  Table 14-2, as cited in the accepted 694 header): UC reads and
  writes appear on the bus in program order without reordering and
  without speculation; a retired UC store bypasses the WB store
  buffer entirely (posted, never buffered); CPU retirement is not
  device completion (chipsets may post UC writes); a UC load over an
  overlapping posted write refuses instead of forwarding silently.
  The model discharges the checkable content (bypass, FIFO log
  order, refusal); that the PINS show the log order is silicon and
  stays a named assumption (`UcBusAnnahme`). DMA engines have no
  form here at all: every DMA access refuses (`DmaAnnahme`). -/

/-- DMA request stub: DMA has no execution form on this machine, so
    every request refuses. This is the whole DMA model. -/
def dmaAnfrage (_m : HwDevMaschine) (_c : Nat) (_a : Adresse)
    (_n : Nat) : Option HwDevMaschine := none

/-- Every DMA request refuses. -/
theorem dmaAnfrage_verweigert (m : HwDevMaschine) (c : Nat)
    (a : Adresse) (n : Nat) :
    dmaAnfrage m c a n = none := rfl

/-- NAMED ASSUMPTION (DMA): no DMA engine step exists -- every DMA
    access at every core, address and length refuses. Timing,
    engines and completion of DMA stay outside the model (see CUTS). -/
def DmaAnnahme (m : HwDevMaschine) : Prop :=
  ∀ (c : Nat) (a : Adresse) (n : Nat), dmaAnfrage m c a n = none

/-- The stub satisfies the named DMA assumption, jointly. -/
theorem dmaAnnahme_gilt (m : HwDevMaschine) : DmaAnnahme m :=
  fun _ _ _ => rfl

/-- From the named assumption, one concrete DMA access refuses. -/
theorem dmaAnnahme_verweigert (m : HwDevMaschine)
    (h : DmaAnnahme m) (c : Nat) (a : Adresse) (n : Nat) :
    dmaAnfrage m c a n = none := h c a n

/-- NAMED ASSUMPTION (UC bus order): the pins present the retired UC
    log in order. The model retires in program order and completes
    FIFO (proved below); the bus appearance itself is hardware. -/
def UcBusAnnahme (log pins : List UcEreignis) : Prop := pins = log

/-- From the named bus assumption, pins and log run together. -/
theorem ucPinsLaenge (log pins : List UcEreignis)
    (h : UcBusAnnahme log pins) :
    pins.length = log.length := by rw [h]

/-! ## 2. Projection onto the accepted UC machine.

  Core `c` sees the accepted `MmioMaschine` over its own projection:
  its FP data over shared memory, its OWN WB buffer, the shared
  device, the shared posted queue and log, and the machine UC
  profile. No second UC evaluator is built: every step below runs
  the accepted functions on this projection. -/

/-- Core projection: the accepted UC machine for core `c`. -/
def devProj (m : HwDevMaschine) (c : Nat) : MmioMaschine :=
  ⟨projFp m.masch c, m.masch.puffer c, m.geraet, m.ausstehend,
    m.ucLog, m.profil⟩

/-- The projection carries the core FP view. -/
theorem devProj_kern (m : HwDevMaschine) (c : Nat) :
    (devProj m c).kern = projFp m.masch c := rfl

/-- The projection carries the acting core's own WB buffer. -/
theorem devProj_pending (m : HwDevMaschine) (c : Nat) :
    (devProj m c).pending = m.masch.puffer c := rfl

/-- The projection carries the machine UC profile. -/
theorem devProj_profil (m : HwDevMaschine) (c : Nat) :
    (devProj m c).profil = m.profil := rfl

/-- Well-formedness: admitted features have silicon behind them --
    exactly `HwWf` of the coherent machine (profiles are shared). -/
def HwDevWf (m : HwDevMaschine) : Prop := HwWf m.masch

/-- Core-data updates preserve well-formedness. -/
theorem hwDevKern_wf (m : HwDevMaschine) (c : Nat) (k : HwKern)
    (h : HwDevWf m) :
    HwDevWf { m with masch := setKernDaten m.masch c k } := h

/-- Device/posted/log updates preserve well-formedness. -/
theorem hwDevGeraet_wf (m : HwDevMaschine) (g : Geraet)
    (aus : List PostedSchreib) (log : List UcEreignis)
    (h : HwDevWf m) :
    HwDevWf { m with geraet := g, ausstehend := aus, ucLog := log } :=
  h

/-! ## 3. Device steps on the coherent machine.

  Each case runs the accepted evaluator on the core projection and
  re-embeds exactly its effects: a retired UC store posts (machine,
  buffer and device bytes untouched -- `ucStore_bypass`); a UC load
  moves the destination register, the device counter and the log
  (`ucLoad_rahmen`); bus completion drains the oldest posted write
  FIFO (`busFortschritt_fifo`). Denial at any gate has NO
  constructor: it is the absence of a step. -/

/-- Device-side observable events: UC retirements and bus
    completions. DMA and WC/WT/WP forms have no constructor here. -/
inductive DevEreignis1133 where
  | ucSpeichern : Breite → Adresse → Wort → DevEreignis1133
  | ucLaden : Breite → Register → Adresse → DevEreignis1133
  | busVollendung : DevEreignis1133
  deriving DecidableEq, Repr

/-- One device step on the extended coherent machine, each case from
    its accepted equation on the core projection. -/
inductive HwDevSchritt :
    HwDevMaschine → HwDevMaschine → DevEreignis1133 → Prop where
  | ucSpeichern (m : HwDevMaschine) (c : Nat) (b : Breite)
      (a : Adresse) (v : Wort) (m0 : MmioMaschine)
      (h : ucStoreZugriff (devProj m c) m.masch.hw
        (m.masch.bereit c) b a v = some m0) :
      HwDevSchritt m
        { masch := m.masch, profil := m.profil, geraet := m0.geraet,
          ausstehend := m0.ausstehend, ucLog := m0.ucLog }
        (.ucSpeichern b a v)
  | ucLaden (m : HwDevMaschine) (c : Nat) (b : Breite)
      (dst : Register) (a : Adresse) (m0 : MmioMaschine) (v : Wort)
      (h : ucLoadZugriff (devProj m c) m.masch.hw
        (m.masch.bereit c) b dst a = some (m0, v)) :
      HwDevSchritt m
        { masch := setKernDaten m.masch c
            ⟨m0.kern.kern.register, m0.kern.kern.flags,
              m0.kern.kern.rip, (m.masch.kerne c).xmm,
              (m.masch.kerne c).fp⟩,
          profil := m.profil, geraet := m0.geraet,
          ausstehend := m0.ausstehend, ucLog := m0.ucLog }
        (.ucLaden b dst a)
  | busVollendung (m : HwDevMaschine) (c : Nat) (m0 : MmioMaschine)
      (h : busFortschritt (devProj m c) = some m0) :
      HwDevSchritt m
        { masch := m.masch, profil := m.profil, geraet := m0.geraet,
          ausstehend := m0.ausstehend, ucLog := m0.ucLog }
        .busVollendung

/-! ## 4. Step agreement: the old evaluator is lifted, never redefined.

  BYPASS (the stated model): a retired UC store touches no coherent
  byte, no WB buffer, no device byte and no core datum -- the posted
  queue and the log each grow by exactly the new event. A UC load
  moves only its destination register, the device counter and the
  log. Bus completion drains FIFO with CPU state, log and pending WB
  stores preserved. -/

/-- BYPASS, lifted: a UC-store step leaves machine, buffers and
    device bytes alone and posts exactly one write. -/
theorem hwDevStore_bypass (m m' : HwDevMaschine)
    (b : Breite) (a : Adresse) (v : Wort)
    (h : HwDevSchritt m m' (.ucSpeichern b a v)) :
    m'.masch = m.masch ∧
      m'.geraet.daten = m.geraet.daten ∧
      m'.geraet.zugriffe = m.geraet.zugriffe ∧
      m'.ausstehend =
        m.ausstehend ++ [{ addr := a, breite := b, wert := v }] ∧
      m'.ucLog = m.ucLog ++ [.schreibe a b] := by
  cases h with
  | ucSpeichern c b a v m0 h =>
    obtain ⟨hpend, hdat, hzaehl, _, hlog, haus⟩ :=
      ucStore_bypass (devProj m c) m.masch.hw (m.masch.bereit c)
        b a v m0 h
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · have : m0.geraet.daten = (devProj m c).geraet.daten := hdat
      simpa [devProj] using this
    · have : m0.geraet.zugriffe = (devProj m c).geraet.zugriffe :=
        hzaehl
      simpa [devProj] using this
    · have : m0.ausstehend = (devProj m c).ausstehend ++
        [{ addr := a, breite := b, wert := v }] := haus
      simpa [devProj] using this
    · have : m0.ucLog = (devProj m c).ucLog ++ [.schreibe a b] :=
        hlog
      simpa [devProj] using this

/-- No WB buffer ever carries a UC byte: the store step keeps every
    core buffer, by the bypass. -/
theorem hwDevStore_puffer (m m' : HwDevMaschine)
    (b : Breite) (a : Adresse) (v : Wort)
    (h : HwDevSchritt m m' (.ucSpeichern b a v)) (d : Nat) :
    (m'.masch.puffer d) = (m.masch.puffer d) := by
  have hmach := (hwDevStore_bypass m m' b a v h).1
  rw [hmach]

/-- LOAD FRAME, lifted: a UC-load step changes no RAM byte, no flag,
    no RIP, no XMM, no control word, no pending WB store and no
    posted write; only the destination register, the device counter
    and the log move. -/
theorem hwDevLaden_rahmen (m m' : HwDevMaschine)
    (b : Breite) (dst : Register) (a : Adresse)
    (h : HwDevSchritt m m' (.ucLaden b dst a)) :
    (m'.masch.mem.bytes) = (m.masch.mem.bytes) ∧
      m'.ausstehend = m.ausstehend ∧
      m'.ucLog = m.ucLog ++ [.lese a b] ∧
      m'.masch.puffer = m.masch.puffer := by
  cases h with
  | ucLaden c b dst a m0 v h =>
    obtain ⟨_, _, _, _, _, _, haus, hlog⟩ :=
      ucLoad_rahmen (devProj m c) m.masch.hw (m.masch.bereit c)
        b dst a m0 v h
    refine ⟨rfl, ?_, ?_, rfl⟩
    · have : m0.ausstehend = (devProj m c).ausstehend := haus
      simpa [devProj] using this
    · have : m0.ucLog = (devProj m c).ucLog ++ [.lese a b] := hlog
      simpa [devProj] using this

/-- The load lands exactly the answered value, merged with width
    discipline, in the acting core's destination register. -/
theorem hwDevLaden_register_bei (m : HwDevMaschine) (c : Nat)
    (b : Breite) (dst : Register) (a : Adresse) (g' : Geraet)
    (v : Wort)
    (hz : breiteZugelassen m.masch.hw (m.masch.bereit c) b = true)
    (hu : istUc m.profil a b.bytes = true)
    (hf : imFenster a b.bytes = true)
    (hp : ueberlapptPosted m.ausstehend a b.bytes = false)
    (hg : geraetLiest m.geraet b (geraetOff a) = some (g', v)) :
    ∃ m' : HwDevMaschine,
      HwDevSchritt m m' (.ucLaden b dst a) ∧
        (m'.masch.kerne c).register dst =
          mergeRegNarrow b ((devProj m c).kern.kern.register dst) v := by
  have hacc := ucLoadZugriff_erfolg (devProj m c) m.masch.hw
    (m.masch.bereit c) b dst a g' v hz hu hf hp hg
  refine ⟨_, HwDevSchritt.ucLaden m c b dst a _ v hacc, ?_⟩
  have hreg := maschineRegLaden_gleich (devProj m c) b dst v
  show ((setKernDaten m.masch c _).kerne c).register dst = _
  unfold setKernDaten
  simp only
  exact hreg

/-- FIFO COMPLETION, lifted: bus completion drains the oldest
    posted write first; CPU state, log and pending WB stores are
    preserved, and the machine is untouched. -/
theorem hwDevBus_fifo (m m' : HwDevMaschine)
    (h : HwDevSchritt m m' .busVollendung)
    (p : PostedSchreib) (rest : List PostedSchreib) (g' : Geraet)
    (he : m.ausstehend = p :: rest)
    (hg : geraetSchreibt m.geraet p.breite (geraetOff p.addr) p.wert =
      some g') :
    m'.geraet = g' ∧ m'.ausstehend = rest ∧ m'.ucLog = m.ucLog ∧
      m'.masch = m.masch ∧ m'.profil = m.profil := by
  cases h with
  | busVollendung c m0 h =>
    have he' : (devProj m c).ausstehend = p :: rest := by
      simpa [devProj] using he
    have hg' : geraetSchreibt (devProj m c).geraet p.breite
        (geraetOff p.addr) p.wert = some g' := by
      simpa [devProj] using hg
    obtain ⟨m0', hbm, hgeraet, haus, hlog, _, _⟩ :=
      busFortschritt_fifo (devProj m c) p rest g' he' hg'
    rw [hbm] at h
    have heq : m0' = m0 := Option.some_inj.mp h
    subst heq
    refine ⟨?_, ?_, ?_, rfl, rfl⟩
    · simpa [devProj] using hgeraet
    · simpa [devProj] using haus
    · simpa [devProj] using hlog

/-- Every device step preserves well-formedness: profiles are never
    touched, core updates go through `setKernDaten`. -/
theorem hwDevSchritt_wf (m m' : HwDevMaschine)
    (e : DevEreignis1133) (h : HwDevSchritt m m' e)
    (hwf : HwDevWf m) : HwDevWf m' := by
  cases h with
  | ucSpeichern c b a v m0 h => exact hwf
  | ucLaden c b dst a m0 v h =>
    exact setKernDaten_wf m.masch c _ hwf
  | busVollendung c m0 h => exact hwf

/-! ## 5. Bus/device events as `HwAdapter` plugs.

  `HwAdapter` carries no device state by construction (its step maps
  machine and event to a machine only), so each plug exposes exactly
  the machine-visible content: the UC-store plug admits under the
  accepted triple gate and changes nothing (bypass); the UC-load leg
  refuses here because its register update needs the device answer;
  the port plug computes the latch answer through the accepted total
  function (never by fiat) but stays stateless across steps; DMA
  refuses outright. Full stateful agreement rides §3. -/

/-- UC access request on the bare coherent machine: width, address,
    value plus the software-established UC profile as checked input
    data. The posted queue and log ride the extended relation. -/
inductive UcZugriff1133 where
  | speichere : Breite → Adresse → Wort → UcProfil → UcZugriff1133
  | lade : Breite → Register → Adresse → UcProfil → UcZugriff1133
  deriving DecidableEq, Repr

/-- UC adapter step: a UC store is admitted exactly under the
    accepted triple gate and changes nothing on the machine; a UC
    load refuses (its answer lives in the device). No gate beyond
    the accepted conjunction is added. -/
def ucAdapterSchritt (m : HwMaschine) (c : Nat) :
    UcZugriff1133 → Option HwMaschine
  | .speichere b a _ profil =>
    if breiteZugelassen m.hw (m.bereit c) b && istUc profil a b.bytes &&
        imFenster a b.bytes then some m else none
  | .lade _ _ _ _ => none

/-- The UC plug as a coherent-machine adapter. -/
def adapterUc1133 : HwAdapter UcZugriff1133 := ⟨ucAdapterSchritt⟩

/-- ADMITTED: a UC store under the triple gate steps to the same
    machine (bypass, machine-visible content). -/
theorem ucAdapterSchritt_speichern (m : HwMaschine) (c : Nat)
    (b : Breite) (a : Adresse) (v : Wort) (profil : UcProfil)
    (hz : breiteZugelassen m.hw (m.bereit c) b = true)
    (hu : istUc profil a b.bytes = true)
    (hf : imFenster a b.bytes = true) :
    ucAdapterSchritt m c (.speichere b a v profil) = some m := by
  have hgate : (breiteZugelassen m.hw (m.bereit c) b &&
      istUc profil a b.bytes && imFenster a b.bytes) = true := by
    simp [hz, hu, hf]
  show (if breiteZugelassen m.hw (m.bereit c) b &&
      istUc profil a b.bytes && imFenster a b.bytes then some m
    else none) = some m
  exact if_pos hgate

/-- REFUSED: the UC-load leg has no device answer on the bare
    machine. -/
theorem ucAdapterSchritt_lade_verweigert (m : HwMaschine) (c : Nat)
    (b : Breite) (dst : Register) (a : Adresse) (profil : UcProfil) :
    ucAdapterSchritt m c (.lade b dst a profil) = none := rfl

/-- REFUSED: a store outside UC membership is no UC access. -/
theorem ucAdapterSchritt_nichtUc_verweigert (m : HwMaschine)
    (c : Nat) (b : Breite) (a : Adresse) (v : Wort)
    (profil : UcProfil)
    (hu : istUc profil a b.bytes = false) :
    ucAdapterSchritt m c (.speichere b a v profil) = none := by
  show (if breiteZugelassen m.hw (m.bereit c) b &&
      istUc profil a b.bytes && imFenster a b.bytes then some m
    else none) = none
  have hgate : ¬ (breiteZugelassen m.hw (m.bereit c) b &&
      istUc profil a b.bytes && imFenster a b.bytes) = true := by
    simp [hu]
  exact if_neg hgate

/-- The UC plug preserves well-formedness (admitted steps keep the
    machine; refused steps keep it too). -/
theorem adapterUc1133_wf (m m' : HwMaschine) (c : Nat)
    (e : UcZugriff1133)
    (h : (adapterUc1133).schritt m c e = some m')
    (hwf : HwWf m) : HwWf m' := by
  cases e with
  | speichere b a v profil =>
    have h' : ucAdapterSchritt m c (.speichere b a v profil) =
        some m' := h
    have hred : ucAdapterSchritt m c (.speichere b a v profil) =
        (if breiteZugelassen m.hw (m.bereit c) b &&
          istUc profil a b.bytes && imFenster a b.bytes then some m
        else none) := rfl
    rw [hred] at h'
    cases hgate : breiteZugelassen m.hw (m.bereit c) b &&
        istUc profil a b.bytes && imFenster a b.bytes with
    | true =>
      rw [if_pos hgate] at h'
      cases h'
      exact hwf
    | false =>
      have hn : ¬ (breiteZugelassen m.hw (m.bereit c) b &&
          istUc profil a b.bytes && imFenster a b.bytes) = true := by
        simp [hgate]
      rw [if_neg hn] at h'
      cases h'
  | lade b dst a profil =>
    have h' : ucAdapterSchritt m c (.lade b dst a profil) =
        some m' := h
    have hred : ucAdapterSchritt m c (.lade b dst a profil) =
        (none : Option HwMaschine) := rfl
    rw [hred] at h'
    cases h'

/-- AGREEMENT: an admitted UC-plug store is exactly a reached
    extended UC-store step whose machine is unchanged. -/
theorem adapterUc1133_stimmt_ueberein (d : HwDevMaschine) (c : Nat)
    (b : Breite) (a : Adresse) (v : Wort)
    (hz : breiteZugelassen d.masch.hw (d.masch.bereit c) b = true)
    (hu : istUc d.profil a b.bytes = true)
    (hf : imFenster a b.bytes = true) :
    (adapterUc1133).schritt d.masch c
        (.speichere b a v d.profil) = some d.masch ∧
      ∃ d' : HwDevMaschine,
        HwDevSchritt d d' (.ucSpeichern b a v) ∧
          d'.masch = d.masch := by
  have hacc := ucStoreZugriff_erfolg (devProj d c) d.masch.hw
    (d.masch.bereit c) b a v hz hu hf
  have hplug : (adapterUc1133).schritt d.masch c
      (.speichere b a v d.profil) = some d.masch :=
    ucAdapterSchritt_speichern d.masch c b a v d.profil hz hu hf
  have hm0 : ∃ m0 : MmioMaschine,
      ucStoreZugriff (devProj d c) d.masch.hw (d.masch.bereit c)
        b a v = some m0 := ⟨_, hacc⟩
  obtain ⟨m0, hm0⟩ := hm0
  exact ⟨hplug,
    { masch := d.masch, profil := d.profil, geraet := m0.geraet,
      ausstehend := m0.ausstehend, ucLog := m0.ucLog },
    HwDevSchritt.ucSpeichern d c b a v m0 hm0, rfl⟩

/-! ## 6. Port plug: fetched latch steps as `HwAdapter` events.

  The port plug computes the latch answer through the accepted TOTAL
  function `geraetAntwort` (never by fiat) under the accepted
  fetch/length/permission/drain gates. It is stateless across steps
  by construction -- device continuity rides the extended relation
  of §3. -/

/-- Port access request: the fetched decode plus the latch pre-state,
    log, privilege and map as checked input data. -/
inductive PortZugriff1133 where
  | aus : IoDec → GeraetZustand → List IoEreignis →
    Bus704.IoBerechtigung → Bus704.TssKarte → PortZugriff1133
  | ein : IoDec → GeraetZustand → List IoEreignis →
    Bus704.IoBerechtigung → Bus704.TssKarte → PortZugriff1133

/-- Core-data successor for a port OUT: registers, flags and RIP from
    the accepted `ausKern`; XMM and FP context kept. -/
def portAusKern (m : HwMaschine) (c : Nat) (dec : IoDec) : HwKern :=
  ⟨(Bus704.ausKern (projZustand m c) dec).register,
    (Bus704.ausKern (projZustand m c) dec).flags,
    (Bus704.ausKern (projZustand m c) dec).rip,
    (m.kerne c).xmm, (m.kerne c).fp⟩

/-- Core-data successor for a port IN: the accepted `einKern` with
    the latch answer from the accepted total function. -/
def portEinKern (m : HwMaschine) (c : Nat) (dec : IoDec)
    (b : IoBreite) (g : GeraetZustand) : HwKern :=
  ⟨(Bus704.einKern (projZustand m c) dec b
      (geraetAntwort g .ein b 0).2).register,
    (Bus704.einKern (projZustand m c) dec b
      (geraetAntwort g .ein b 0).2).flags,
    (Bus704.einKern (projZustand m c) dec b
      (geraetAntwort g .ein b 0).2).rip,
    (m.kerne c).xmm, (m.kerne c).fp⟩

/-- Port adapter core step: fetch from actual bytes, decoded match,
    accepted length/permission/drain gates, then the accepted latch
    answer. Anything else refuses. -/
def portAdapterKern (m : HwMaschine) (c : Nat) :
    PortZugriff1133 → Option HwKern
  | .aus dec _ _ r k =>
    match fetchIo (projZustand m c) with
    | none => none
    | some (d, _) =>
      if d = dec then
        match dec.op with
        | ⟨.aus, b, _⟩ =>
          if laengeOk dec.laenge &&
              Bus704.archZugelassen r k
                (portVon dec.op (projZustand m c).register) b &&
              zaunBereit (tsoAnsicht m) c then
            some (portAusKern m c dec)
          else none
        | _ => none
      else none
  | .ein dec g _ r k =>
    match fetchIo (projZustand m c) with
    | none => none
    | some (d, _) =>
      if d = dec then
        match dec.op with
        | ⟨.ein, b, _⟩ =>
          if laengeOk dec.laenge &&
              Bus704.archZugelassen r k
                (portVon dec.op (projZustand m c).register) b &&
              zaunBereit (tsoAnsicht m) c then
            some (portEinKern m c dec b g)
          else none
        | _ => none
      else none

/-- Port adapter machine step: the core step re-embedded. -/
def portAdapterSchritt (m : HwMaschine) (c : Nat)
    (e : PortZugriff1133) : Option HwMaschine :=
  (portAdapterKern m c e).map (setKernDaten m c)

/-- The port plug as a coherent-machine adapter. -/
def adapterPort1133 : HwAdapter PortZugriff1133 :=
  ⟨portAdapterSchritt⟩

/-- SELECTION (OUT): a fetched port OUT under the accepted gates
    computes the core successor AND justifies a reached generic bus
    step with the latch answer. -/
theorem portAdapter_aus_fetch (m : HwMaschine) (c : Nat)
    (dec : IoDec) (g : GeraetZustand) (spur : List IoEreignis)
    (r : Bus704.IoBerechtigung) (k : Bus704.TssKarte)
    (d : IoDec) (rest : List Byte) (b : IoBreite) (q : PortQuelle)
    (hf : fetchIo (projZustand m c) = some (d, rest))
    (heq : d = dec)
    (hop : dec.op = ⟨.aus, b, q⟩)
    (hlen : laengeOk dec.laenge = true)
    (hperm : Bus704.archZugelassen r k
      (portVon dec.op (projZustand m c).register) b = true)
    (hord : zaunBereit (tsoAnsicht m) c = true) :
    portAdapterKern m c (.aus dec g spur r k) =
        some (portAusKern m c dec) ∧
      Bus704.BusSchritt GeraetZustand Bus704.latchErlaubt r k
        ⟨projZustand m c, g, spur⟩
        ⟨Bus704.ausKern (projZustand m c) dec,
          (geraetAntwort g .aus b
            (ausGabe b ((projZustand m c).register .rax))).1,
          spur ++ [⟨.aus, b,
            portVon dec.op (projZustand m c).register,
            ausGabe b ((projZustand m c).register .rax)⟩]⟩ := by
  have hop' : d.op = ⟨.aus, b, q⟩ := by rw [heq, hop]
  have hperm' : Bus704.archZugelassen r k
      (portVon d.op (projZustand m c).register) b = true := by
    rw [heq]
    exact hperm
  have hant : Bus704.latchErlaubt g .aus b
      (portVon d.op (projZustand m c).register)
      (ausGabe b ((projZustand m c).register .rax))
      (geraetAntwort g .aus b
        (ausGabe b ((projZustand m c).register .rax))).1
      0 := by
    rw [heq]
    exact Bus704.latch_aus_sound g b _ _
  have hbus := Bus704.busSchritt_aus_fetch GeraetZustand
    Bus704.latchErlaubt r k ⟨projZustand m c, g, spur⟩ d rest _ b q
    hf hop' hperm' hant
  rw [heq] at hbus
  rw [hop] at hperm
  refine ⟨?_, hbus⟩
  unfold portAdapterKern
  rw [hf]
  simp [heq, hop, hlen, hperm, hord]

/-- SELECTION (IN): a fetched port IN under the accepted gates
    computes the core successor AND justifies a reached generic bus
    step with the latch answer. -/
theorem portAdapter_ein_fetch (m : HwMaschine) (c : Nat)
    (dec : IoDec) (g : GeraetZustand) (spur : List IoEreignis)
    (r : Bus704.IoBerechtigung) (k : Bus704.TssKarte)
    (d : IoDec) (rest : List Byte) (b : IoBreite) (q : PortQuelle)
    (hf : fetchIo (projZustand m c) = some (d, rest))
    (heq : d = dec)
    (hop : dec.op = ⟨.ein, b, q⟩)
    (hlen : laengeOk dec.laenge = true)
    (hperm : Bus704.archZugelassen r k
      (portVon dec.op (projZustand m c).register) b = true)
    (hord : zaunBereit (tsoAnsicht m) c = true) :
    portAdapterKern m c (.ein dec g spur r k) =
        some (portEinKern m c dec b g) ∧
      Bus704.BusSchritt GeraetZustand Bus704.latchErlaubt r k
        ⟨projZustand m c, g, spur⟩
        ⟨Bus704.einKern (projZustand m c) dec b
            (geraetAntwort g .ein b 0).2,
          (geraetAntwort g .ein b 0).1,
          spur ++ [⟨.ein, b,
            portVon dec.op (projZustand m c).register,
            (geraetAntwort g .ein b 0).2⟩]⟩ := by
  have hop' : d.op = ⟨.ein, b, q⟩ := by rw [heq, hop]
  have hperm' : Bus704.archZugelassen r k
      (portVon d.op (projZustand m c).register) b = true := by
    rw [heq]
    exact hperm
  have hant : Bus704.latchErlaubt g .ein b
      (portVon d.op (projZustand m c).register) 0
      (geraetAntwort g .ein b 0).1
      (geraetAntwort g .ein b 0).2 := by
    rw [heq]
    exact Bus704.latch_ein_sound g b _
  have hbus := Bus704.busSchritt_ein_fetch GeraetZustand
    Bus704.latchErlaubt r k ⟨projZustand m c, g, spur⟩ d rest _ _ b q
    hf hop' hperm' hant
  rw [heq] at hbus
  rw [hop] at hperm
  refine ⟨?_, hbus⟩
  unfold portAdapterKern
  rw [hf]
  simp [heq, hop, hlen, hperm, hord]

/-- REFUSED: fetch refusal is plug refusal. -/
theorem portAdapter_fetch_verweigert (m : HwMaschine) (c : Nat)
    (dec : IoDec) (g : GeraetZustand) (spur : List IoEreignis)
    (r : Bus704.IoBerechtigung) (k : Bus704.TssKarte)
    (hf : fetchIo (projZustand m c) = none) :
    portAdapterSchritt m c (.aus dec g spur r k) = none := by
  unfold portAdapterSchritt portAdapterKern
  simp [hf]

/-- REFUSED: a forged decode that the fetch did not produce. -/
theorem portAdapter_falschDecodiert_verweigert (m : HwMaschine)
    (c : Nat) (dec : IoDec) (g : GeraetZustand)
    (spur : List IoEreignis) (r : Bus704.IoBerechtigung)
    (k : Bus704.TssKarte) (d : IoDec) (rest : List Byte)
    (hf : fetchIo (projZustand m c) = some (d, rest))
    (hne : ¬ d = dec) :
    portAdapterSchritt m c (.aus dec g spur r k) = none := by
  unfold portAdapterSchritt portAdapterKern
  rw [hf]
  simp [hne]

/-- REFUSED: denied architectural permission admits no step. -/
theorem portAdapter_ohneBerechtigung_verweigert (m : HwMaschine)
    (c : Nat) (dec : IoDec) (g : GeraetZustand)
    (spur : List IoEreignis) (r : Bus704.IoBerechtigung)
    (k : Bus704.TssKarte) (d : IoDec) (rest : List Byte)
    (b : IoBreite) (q : PortQuelle)
    (hf : fetchIo (projZustand m c) = some (d, rest))
    (heq : d = dec) (hop : dec.op = ⟨.aus, b, q⟩)
    (hlen : laengeOk dec.laenge = true)
    (hperm : Bus704.archZugelassen r k
      (portVon dec.op (projZustand m c).register) b = false)
    (hord : zaunBereit (tsoAnsicht m) c = true) :
    portAdapterSchritt m c (.aus dec g spur r k) = none := by
  rw [hop] at hperm
  unfold portAdapterSchritt portAdapterKern
  rw [hf]
  simp [heq, hop, hlen, hperm, hord]

/-- REFUSED: a pending WB store refuses the port gate (Table 20-1). -/
theorem portAdapter_vollerPuffer_verweigert (m : HwMaschine)
    (c : Nat) (dec : IoDec) (g : GeraetZustand)
    (spur : List IoEreignis) (r : Bus704.IoBerechtigung)
    (k : Bus704.TssKarte) (d : IoDec) (rest : List Byte)
    (b : IoBreite) (q : PortQuelle)
    (hf : fetchIo (projZustand m c) = some (d, rest))
    (heq : d = dec) (hop : dec.op = ⟨.aus, b, q⟩)
    (hlen : laengeOk dec.laenge = true)
    (hperm : Bus704.archZugelassen r k
      (portVon dec.op (projZustand m c).register) b = true)
    (hord : zaunBereit (tsoAnsicht m) c = false) :
    portAdapterSchritt m c (.aus dec g spur r k) = none := by
  rw [hop] at hperm
  unfold portAdapterSchritt portAdapterKern
  rw [hf]
  simp [heq, hop, hlen, hperm, hord]

/-- The port plug preserves well-formedness: every admitted step
    re-embeds core data through `setKernDaten`. -/
theorem adapterPort1133_wf (m m' : HwMaschine) (c : Nat)
    (e : PortZugriff1133)
    (h : (adapterPort1133).schritt m c e = some m')
    (hwf : HwWf m) : HwWf m' := by
  have h' : portAdapterSchritt m c e = some m' := h
  unfold portAdapterSchritt at h'
  cases hker : portAdapterKern m c e with
  | none =>
    simp [hker] at h'
  | some k =>
    simp [hker] at h'
    cases h'
    exact setKernDaten_wf m c k hwf

/-! ## 7. DMA plug: refused, by the named assumption.

  DMA engines have no execution form on this machine: the plug is
  the refused default over an explicit request vocabulary, and the
  §1 assumption discharges every request. -/

/-- DMA request vocabulary: reads and writes by address and length.
    It has no step: every event refuses. -/
inductive DmaZugriff1133 where
  | lese : Adresse → Nat → DmaZugriff1133
  | schreibe : Adresse → Nat → DmaZugriff1133

/-- The DMA plug: refused, exactly like the named assumption. -/
def adapterDma1133 : HwAdapter DmaZugriff1133 := verweigertAdapter _

/-- Every DMA plug event refuses. -/
theorem adapterDma1133_verweigert (m : HwMaschine) (c : Nat)
    (e : DmaZugriff1133) :
    (adapterDma1133).schritt m c e = none :=
  verweigertAdapter_verweigert _ _ _ _

/-! ## 8. Joint witness: UC retire, bus completion, WB forwarding.

  Core 0 retires a UC store (posted, machine untouched), the bus
  completes it into the device byte, and a WB store at the RAM cell
  forwards to the owner only before the drain makes it visible to
  core 1. Beside the run: the DMA, kind, posted-overlap and profile
  refusals. Non-degenerate: the device byte AND the RAM cell change. -/

/-- Witness UC profile: exactly the 8-byte device window. -/
def witProfil1133 : UcProfil :=
  [{ basis := 65536, len := 8, lesbar := true, schreibbar := true, ausfuehrbar := false }]

/-- The witness device address. -/
def witDev1133 : Adresse := natAdresse 65536

/-- The witness RAM cell. -/
def witRam1133 : Adresse := BitVec.ofNat 64 8192

/-- Witness cores: core 0 holds the store value in rax, core 1 idles
    on the data page. Memory and permissions are the accepted 660
    witness image. -/
def witKern1133 : Nat → HwKern
  | 0 => ⟨fun q =>
      if q = Register.rax then BitVec.ofNat 64 7
      else if q = Register.rsp then BitVec.ofNat 64 8704
      else BitVec.ofNat 64 0,
    zeugeFlags, BitVec.ofNat 64 4096,
    fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
    BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness coherent machine: shared memory, two cores, empty
    buffers, full silicon with OS vector state. -/
def witMasch1133 : HwMaschine :=
  ⟨hwWitMem, witKern1133, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- Witness start: reset device, nothing posted, empty log. -/
def witStart1133 : HwDevMaschine :=
  ⟨witMasch1133, witProfil1133, geraetAnfang, [], []⟩

/-- The witness machine is well-formed. -/
theorem witStart1133_wf : HwDevWf witStart1133 := by
  intro c f _
  cases f <;> rfl

/-- After the UC store: posted write plus log event; machine,
    buffers and device bytes untouched. -/
def witD11133 : HwDevMaschine :=
  ⟨witMasch1133, witProfil1133, geraetAnfang,
    [⟨witDev1133, .b64, BitVec.ofNat 64 7⟩],
    [.schreibe witDev1133 .b64]⟩

/-- Stage 1: the UC store retires (posted, bypassed). -/
theorem wit_schritt1_1133 :
    HwDevSchritt witStart1133 witD11133
      (.ucSpeichern .b64 witDev1133 (BitVec.ofNat 64 7)) := by
  have hz : breiteZugelassen basisHw basisBereit Breite.b64 = true := by
    decide
  have hu : istUc witProfil1133 witDev1133 8 = true := by decide
  have hf : imFenster witDev1133 8 = true := by decide
  have hacc := ucStoreZugriff_erfolg (devProj witStart1133 0) basisHw
    basisBereit .b64 witDev1133 (BitVec.ofNat 64 7) hz hu hf
  exact HwDevSchritt.ucSpeichern witStart1133 0 .b64 witDev1133
    (BitVec.ofNat 64 7) _ hacc

/-- Bus completion over stage 1. -/
def witBus1133 : Option MmioMaschine :=
  busFortschritt (devProj witD11133 0)

/-- The posted write completes: queue drained. -/
theorem wit_bus_ausstehend_1133 :
    witBus1133.map (fun m' => m'.ausstehend) = some [] := by
  decide

/-- The posted write completes: log kept. -/
theorem wit_bus_log_1133 :
    witBus1133.map (fun m' => m'.ucLog) =
      some [.schreibe witDev1133 .b64] := by
  decide

/-- The posted write completes: device byte 0 reads 7. -/
theorem wit_bus_geraet_1133 :
    witBus1133.map (fun m' => m'.geraet.daten ⟨0, by decide⟩) =
      some (natByte 7) := by
  decide

/-- Stage 2: the bus completes the posted write FIFO. -/
theorem wit_schritt2_1133 :
    ∃ d' : HwDevMaschine,
      HwDevSchritt witD11133 d' .busVollendung ∧
        d'.ausstehend = [] ∧
        d'.ucLog = [.schreibe witDev1133 .b64] ∧
        d'.masch = witMasch1133 ∧
        d'.geraet.daten ⟨0, by decide⟩ = natByte 7 := by
  obtain ⟨m2, hm2⟩ : ∃ m2, witBus1133 = some m2 := ⟨_, rfl⟩
  have hstep : busFortschritt (devProj witD11133 0) = some m2 := hm2
  have haus : m2.ausstehend = [] := by
    have h := wit_bus_ausstehend_1133
    rw [hm2] at h
    simpa using h
  have hlog : m2.ucLog = [.schreibe witDev1133 .b64] := by
    have h := wit_bus_log_1133
    rw [hm2] at h
    simpa using h
  have hdat : m2.geraet.daten ⟨0, by decide⟩ = natByte 7 := by
    have h := wit_bus_geraet_1133
    rw [hm2] at h
    simpa using h
  refine ⟨
    { masch := witMasch1133, profil := witProfil1133,
      geraet := m2.geraet, ausstehend := m2.ausstehend,
      ucLog := m2.ucLog },
    HwDevSchritt.busVollendung witD11133 0 m2 hstep, ?_, ?_, ?_,
    ?_⟩
  · simpa using haus
  · simpa using hlog
  · rfl
  · simpa using hdat

/-- WB issue on core 0 at the RAM cell. -/
def witIssue1133 : Option TSOZustand :=
  issueByte (tsoAnsicht witMasch1133) 0 witRam1133
    (BitVec.ofNat 8 42)

/-- Owner forwarding: core 0 reads its own byte. -/
theorem wit_eigen_1133 :
    witIssue1133.bind (fun s => loadByte s 0 witRam1133) =
      some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem wit_fremd_1133 :
    witIssue1133.bind (fun s => loadByte s 1 witRam1133) =
      some (some (BitVec.ofNat 8 0)) := by
  decide

/-- Drain: core 0 flushes into shared memory. -/
def witFlush1133 : Option TSOZustand :=
  witIssue1133.bind (fun s => flushKern s 0)

/-- The drain changes shared memory: the cell reads 42. -/
theorem wit_spuelung_1133 :
    witFlush1133.map (fun s => s.mem.bytes witRam1133) =
      some (BitVec.ofNat 8 42) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem wit_fremdNeu_1133 :
    witFlush1133.bind (fun s => loadByte s 1 witRam1133) =
      some (some (BitVec.ofNat 8 42)) := by
  decide

/-- The RAM cell starts zeroed. -/
theorem wit_ramNull_1133 :
    hwWitMem.bytes witRam1133 = BitVec.ofNat 8 0 := by
  decide

/-- DMA REFUSAL on the witness. -/
theorem wit_dma_1133 :
    dmaAnfrage witStart1133 0 witDev1133 8 = none := rfl

/-- KIND REFUSAL: DMA is no admitted memory kind. -/
theorem wit_art_1133 :
    speicherArtZugelassen speicherProfilZeuge .dma = false := rfl

/-- ORDERING REFUSAL: a UC load over the posted write refuses. -/
theorem wit_ueberlapp_1133 :
    ucLoadZugriff (devProj witD11133 0) basisHw basisBereit .b64
      .rcx witDev1133 = none := by
  apply ucLoad_verweigert_bei_ausstehend
  decide

/-- PROFILE REFUSAL: a store at the RAM cell is no UC access. -/
theorem wit_nichtUc_1133 :
    ucStoreZugriff (devProj witStart1133 0) basisHw basisBereit .b64
      witRam1133 (BitVec.ofNat 64 7) = none := by
  apply ucStore_verweigert_ohne_profil
  decide

/-- JOINT WITNESS: the UC store retires posted, the bus completes
    it into the device byte, the WB store forwards to the owner only
    before the drain changes shared memory -- beside the DMA, kind,
    posted-overlap and profile refusals. The named assumptions enter
    as premises and are discharged into concrete facts. Non-degenerate:
    the device byte AND the RAM cell change, on two cores. -/
theorem hwDev_zeuge (pins : List UcEreignis)
    (hbus : UcBusAnnahme [.schreibe witDev1133 .b64] pins)
    (hdma : DmaAnnahme witStart1133) :
    HwDevSchritt witStart1133 witD11133
        (.ucSpeichern .b64 witDev1133 (BitVec.ofNat 64 7)) ∧
      (∃ d' : HwDevMaschine,
        HwDevSchritt witD11133 d' .busVollendung ∧
          d'.ausstehend = [] ∧
          d'.geraet.daten ⟨0, by decide⟩ = natByte 7) ∧
      witIssue1133.bind (fun s => loadByte s 0 witRam1133) =
        some (some (BitVec.ofNat 8 42)) ∧
      witIssue1133.bind (fun s => loadByte s 1 witRam1133) =
        some (some (BitVec.ofNat 8 0)) ∧
      witFlush1133.map (fun s => s.mem.bytes witRam1133) =
        some (BitVec.ofNat 8 42) ∧
      hwWitMem.bytes witRam1133 = BitVec.ofNat 8 0 ∧
      pins.length = 1 ∧
      dmaAnfrage witStart1133 0 witDev1133 8 = none ∧
      ucLoadZugriff (devProj witD11133 0) basisHw basisBereit .b64
        .rcx witDev1133 = none := by
  refine ⟨wit_schritt1_1133, ?_, wit_eigen_1133, wit_fremd_1133,
    wit_spuelung_1133, wit_ramNull_1133, ?_, ?_,
    wit_ueberlapp_1133⟩
  · obtain ⟨d', hd', haus, _, _, hdat⟩ := wit_schritt2_1133
    exact ⟨d', hd', haus, hdat⟩
  · have hlen := ucPinsLaenge _ _ hbus
    simpa using hlen
  · exact dmaAnnahme_verweigert _ hdma _ _ _

/- CUTS:
    Proved here, over the REUSED accepted vocabulary (`HardwareExecution`:
    `HwMaschine/HwWf/setKernDaten/HwAdapter/verweigertAdapter`,
    `projZustand/projFp/tsoAnsicht`, `hwWitMem`; `DeviceHardwareForms`:
    `IoDec/IoBreite/PortQuelle/IoEreignis/GeraetZustand/geraetAntwort`,
    `portVon/ausGabe/einMische`, `SpeicherProfil/speicherArtZugelassen`,
    `fetchIo`; `DeviceBusHardwareExecution` (`Bus704`): `TssKarte`,
    `archZugelassen`, `BusAntwort/BusZustand/ausKern/einKern`,
    `BusSchritt`, `busSchritt_aus/ein_fetch`, `latch_aus/ein_sound`,
    `ordnungOk`; `MemoryTypeHardwareExecution`: `UcProfil/istUc`,
    `imFenster/Geraet/geraetLiest/geraetSchreibt/geraetOff`,
    `MmioMaschine/UcEreignis/PostedSchreib`,
    `ucStoreZugriff/ucStoreZugriff_erfolg/ucStore_bypass`,
    `ucLoadZugriff/ucLoadZugriff_erfolg/ucLoad_rahmen`,
    `ucLoad_verweigert_bei_ausstehend`,
    `ucStore_verweigert_ohne_profil`,
    `busFortschritt/busFortschritt_fifo`, `maschineRegLaden_gleich`;
    no second decoder, no copied device arithmetic, no new machine):
    - the exact UC ordering rule as a named assumption
      (`UcBusAnnahme`: pins present the retired log in order; the
      model discharges bypass, FIFO and log order) and DMA as a named
      assumption (`DmaAnnahme`: every DMA access refuses);
    - the extended coherent device machine with per-core projection
      onto the accepted UC machine, `HwWf` preservation, and three
      step cases lifted with exact bypass/load-frame/FIFO agreement;
    - bus/device events as `HwAdapter` plugs: the UC-store gate
      (exact triple gate, machine unchanged), the fetched latch port
      plug (OUT and IN selection tied to reached generic steps),
      planted plug refusals (fetch, forged decode, permission,
      pending buffer), and the refused DMA plug;
    - a reached joint witness (UC retire, FIFO bus completion into
      the device byte, WB store with owner-only forwarding and drain
      into shared memory on two cores) beside DMA/kind/overlap/
      profile refusals, with both named assumptions discharged.
    NOT proved here, and not claimed:
    - No hardware correspondence beyond the cited Intel SDM entries
      (provenance in the family headers, not proofs); UC profile
      population (MTRR/PAT/page tables) is software user logic.
    - No WC/WT/WP forms, no DMA engines, no chipset-posting model:
      CPU completion never implies device completion; no liveness,
      fairness, timing or retry bounds.
    - The port plug is stateless across steps by construction
      (`HwAdapter` carries no device state); device continuity rides
      the extended relation. The UC-load leg refuses on the bare
      machine (its answer lives in the device).
    - No per-access target-to-W/GX simulation, no source/checker/
      Spec/goal/emitter correspondence, no syscall/interrupt scope.
-/

#print axioms dmaAnfrage_verweigert
#print axioms dmaAnnahme_gilt
#print axioms dmaAnnahme_verweigert
#print axioms ucPinsLaenge
#print axioms devProj_kern
#print axioms hwDevStore_bypass
#print axioms hwDevStore_puffer
#print axioms hwDevLaden_rahmen
#print axioms hwDevLaden_register_bei
#print axioms hwDevBus_fifo
#print axioms hwDevSchritt_wf
#print axioms ucAdapterSchritt_speichern
#print axioms ucAdapterSchritt_lade_verweigert
#print axioms ucAdapterSchritt_nichtUc_verweigert
#print axioms adapterUc1133_wf
#print axioms adapterUc1133_stimmt_ueberein
#print axioms portAdapter_aus_fetch
#print axioms portAdapter_ein_fetch
#print axioms portAdapter_fetch_verweigert
#print axioms portAdapter_ohneBerechtigung_verweigert
#print axioms adapterPort1133_wf
#print axioms adapterDma1133_verweigert
#print axioms wit_schritt1_1133
#print axioms wit_schritt2_1133
#print axioms hwDev_zeuge

end HwDev1133

end Gabbro.Grammatik.X86
