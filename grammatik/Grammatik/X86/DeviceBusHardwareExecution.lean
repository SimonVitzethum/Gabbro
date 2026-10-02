/-
  File:      Grammatik/X86/DeviceBusHardwareExecution.lean
  Subject:   Generic port bus and precise architectural IO permissions over
              the accepted port decoder and canonical state.

  Lane 704: the accepted `geraetAntwort` (DeviceHardwareForms676) is one
  latch/counter device shared across all ports -- a concrete witness, not a
  semantics of every device. This module adds the generic bus/device
  response interface (arbitrary device state plus an allowed read/write
  response relation keyed by port/direction/width/value) and the precise
  long-mode privilege rule (CPL<=IOPL direct, else per-byte TSS bitmap
  checks with #GP outcomes), reusing the accepted byte decoder/fetch and
  accumulator helpers. No second IN/OUT interpreter is built here.

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`):
  - Intel SDM edition 325462-093US, September 2026 (combined volumes 1-4);
    sha256 a4a62e6a7ba11a76c7753a195b825087306812aac39b930973f9168ee599f321,
    verified 2026-10-02T18:40:25Z (REFERENCES.json). Intel-profile
    architectural evidence only; no vendor-difference or silicon claim.
  - IN opcodes/Operation/exceptions: Vol. 2A pages 3-454/3-455,
    txt lines 58368-58460.
  - OUT opcodes/Operation/exceptions: Vol. 2B pages 4-170/4-171,
    txt lines 72010-72100.
  - IOPL/TSS bitmap/per-byte/missing-map rules: Vol. 1 sections
    20.5/20.5.1/20.5.2, pages 20-3/20-4, txt lines 24391-24498.
  - Port ordering/serialization: Vol. 1 section 20.6 plus Table 20-1,
    pages 20-5/20-6, txt lines 24500-24553.
-/
import Grammatik.X86.DeviceHardwareForms
import Grammatik.X86.HardwareFaults
import Grammatik.X86.TSO

namespace Gabbro.Grammatik.X86

/-- TSS IO permission map from checked software/configuration data: the
    bitmap base and TSS limit plus the bit for each port byte address
    (`true` = set/denied, `false` = clear/allowed). No trusted OS-ready
    Bool bypass: the map content is data, checked byte by byte below. -/
structure TssKarte where
  basis : Nat
  grenze : Nat
  bit : Nat → Bool

/-- One port byte is free: inside the 16-bit port space, its bitmap byte
    sits inside the TSS limit, and its bit is clear. Anything unspanned
    (bitmap byte outside the limit, port past 65535) reads as denied,
    matching "treated as if they had set bits" (20.5.2). -/
def tssBitFrei (k : TssKarte) (q : Nat) : Bool :=
  if q < 65536 then
    if k.basis + (q / 8) < k.grenze then !(k.bit q) else false
  else false

/-- Full-map witness card: the whole port space is spanned, all clear. -/
def volleKarte : TssKarte :=
  { basis := 0, grenze := 8192, bit := fun _ => false }

/-- The full-map card frees port byte 96. -/
theorem volleKarte_96_frei : tssBitFrei volleKarte 96 = true := by
  decide

/-! ## Precise TSS range checks: every byte covered by the width.

   "The processor tests all the bits corresponding to the I/O port being
   addressed. For a doubleword access, for example, the processor tests
   the four bits corresponding to the four adjacent 8-bit port addresses.
   If any tested bit is set, #GP is signaled" (20.5.2). -/

/-- Range helper: all `n` bytes from `q` upwards are free. -/
def tssBereichAux (k : TssKarte) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, q => tssBitFrei k q && tssBereichAux k n (q + 1)

/-- Range check for one access: every byte covered by the width must be
    free. A zero width never occurs (widths carry 1, 2 or 4 bytes) and
    refuses outright. -/
def tssBereichFrei (k : TssKarte) (port nbytes : Nat) : Bool :=
  match nbytes with
  | 0 => false
  | n + 1 => tssBereichAux k (n + 1) port

/-- The range helper unfolds one byte. -/
theorem tssBereichAux_succ (k : TssKarte) (n q : Nat) :
    tssBereichAux k (n + 1) q =
      (tssBitFrei k q && tssBereichAux k n (q + 1)) := rfl

/-! ## Selected architectural privilege rule (64-bit long mode).

   "If in protected mode and the CPL is less than or equal to the current
   IOPL, the processor allows all I/O operations to proceed. If the CPL is
   greater than the IOPL ..., the processor checks the I/O permission bit
   map" (20.5.2); the IN/OUT Operation pseudocode takes the same branch,
   and denial is #GP(0) in 64-bit mode (IN Vol. 2A 3-455, OUT Vol. 2B
   4-171). No master-switch Bool lives here: the lane-676 switch was a
   compiler-side admission aid, not silicon. -/

/-- Privilege data for the selected rule: CPL and IOPL only. -/
structure IoBerechtigung where
  cpl : Nat
  iopl : Nat

/-- Selected architectural rule: CPL<=IOPL admits directly with no bitmap
    consult; otherwise every byte covered by the width must be free in
    the TSS map. -/
def archZugelassen (r : IoBerechtigung) (k : TssKarte)
    (port : Nat) (b : IoBreite) : Bool :=
  if r.cpl ≤ r.iopl then true
  else tssBereichFrei k port (ioBreiteBytes b)

/-- The direct leg: CPL<=IOPL admits with no bitmap consult. -/
theorem arch_direkt (r : IoBerechtigung) (k : TssKarte)
    (port : Nat) (b : IoBreite) (h : r.cpl ≤ r.iopl) :
    archZugelassen r k port b = true := by
  unfold archZugelassen
  simp [h]

/-- The bitmap leg: above IOPL the range check decides. -/
theorem arch_bitmap (r : IoBerechtigung) (k : TssKarte)
    (port : Nat) (b : IoBreite) (h : ¬ r.cpl ≤ r.iopl) :
    archZugelassen r k port b =
      tssBereichFrei k port (ioBreiteBytes b) := by
  unfold archZugelassen
  simp [h]

/-- A missing map denies every byte: "If the I/O bit map base address is
    greater than or equal to the TSS segment limit, there is no I/O
    permission map, and all I/O instructions generate exceptions when the
    CPL is greater than the current IOPL" (20.5.2). -/
theorem karte_fehlt_verweigert (k : TssKarte) (q : Nat)
    (h : k.grenze ≤ k.basis) : tssBitFrei k q = false := by
  unfold tssBitFrei
  by_cases hq : q < 65536
  · rw [if_pos hq]
    have hle : ¬ (k.basis + q / 8 < k.grenze) := by omega
    simp [hle]
  · simp [hq]

/-- Past the 16-bit port space every byte denies: DX carries 0..65535 and
    the immediate form zero-extends its upper bits (IN/OUT Description),
    so no access names a byte here. -/
theorem port_raum_ende_verweigert (k : TssKarte) (q : Nat)
    (h : 65536 ≤ q) : tssBitFrei k q = false := by
  unfold tssBitFrei
  have hq : ¬ (q < 65536) := by omega
  simp [hq]

/-- Denial faults as #GP: the accepted fault vocabulary (`ArchFehler.gp`
    of lane 670), no new fault class. Success carries no fault. -/
def busFehler (zugelassen : Bool) : Option ArchFehler :=
  if zugelassen then none else some .gp

/-- An admitted access carries no fault. -/
theorem busFehler_kein_bei_erlaubnis (zugelassen : Bool)
    (h : zugelassen = true) : busFehler zugelassen = none := by
  simp [busFehler, h]

/-- A denied access faults as #GP. -/
theorem busFehler_gp_bei_verweigerung (zugelassen : Bool)
    (h : zugelassen = false) :
    busFehler zugelassen = some .gp := by
  simp [busFehler, h]

/-! ## Compiler admission: conservative, never the hardware rule.

   The lane-676 conjunction (switch AND CPL<=IOPL AND bitmap) is kept
   ONLY as a sufficient compiler admission profile. It is never presented
   as the full architectural rule, and its refusal is never a fault: a
   program it refuses may still be silicon-legal through the direct leg. -/

/-- Compiler-side admission profile: switch, CPL/IOPL, one abstract
    per-port bit. Sound but incomplete by construction. -/
structure CompilerProfil where
  cpl : Nat
  iopl : Nat
  schalter : Bool
  bit : Nat → Bool

/-- Compiler admission: the old conjunction, unchanged. -/
def compilerZugelassen (c : CompilerProfil) (port : Nat) : Bool :=
  c.schalter && decide (c.cpl ≤ c.iopl) && !(c.bit port)

/-- The compiler profile reads its privilege the architectural way. -/
def compilerRecht (c : CompilerProfil) : IoBerechtigung :=
  { cpl := c.cpl, iopl := c.iopl }

/-- SOUNDNESS: whatever the compiler admits, silicon admits too -- the
    direct leg covers it, since compiler admission carries CPL<=IOPL. -/
theorem compiler_sound (c : CompilerProfil) (k : TssKarte)
    (port : Nat) (b : IoBreite)
    (h : compilerZugelassen c port = true) :
    archZugelassen (compilerRecht c) k port b = true := by
  unfold compilerZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨_, hle⟩, _⟩ := h
  apply arch_direkt
  exact of_decide_eq_true hle

/-- Witness card: fully spanned, only port byte 96 set. -/
def sperrKarte : TssKarte :=
  { basis := 0, grenze := 8192, bit := fun q => decide (q = 96) }

/-- INCOMPLETENESS: at CPL 0 with IOPL 3 silicon admits port 96 despite
    the set bitmap bit (direct leg, no consult), while the compiler
    profile refuses on that same bit. The old conjunction is therefore
    not the hardware rule. -/
theorem compiler_unvollstaendig :
    archZugelassen ⟨0, 3⟩ sperrKarte 96 .p8 = true ∧
    compilerZugelassen ⟨0, 3, true, fun q => decide (q = 96)⟩ 96 =
      false := by
  decide

/-! ## Generic bus/device response interface.

   The device is an ARBITRARY type `D` with an allowed read/write
   response relation keyed by the actual port, direction, width and (for
   OUT) the driven value. Named hardware assumptions may constrain the
   relation; OS or binding contracts never do. The lane-676 latch is one
   instance below, never the definition. -/

/-- Allowed device answer: from old state `g`, at `port`, in direction
    `dir` with width `b` (OUT drives `getrieben`, IN passes 0), the
    device may move to `g'` answering `antwort` (the IN value, 0 for
    OUT). A port with no allowed answer simply has no step. -/
def BusAntwort (D : Type) :=
  D → IoDir → IoBreite → Nat → Nat → D → Nat → Prop

/-- Generic bus state: the canonical core, an arbitrary device state,
    and the ordered port-event log. No TSO buffer appears here by
    construction: device bytes never enter a RAM store buffer. -/
structure BusZustand (D : Type) where
  kern : Zustand
  geraet : D
  spur : List IoEreignis

/-- OUT core successor: RIP advances past the decoded length; registers,
    flags and memory are kept (the accumulator is only read). -/
def ausKern (s : Zustand) (dec : IoDec) : Zustand :=
  { s with rip := ripNach s.rip dec.laenge }

/-- IN core successor: RIP advances and the accumulator merges the device
    answer with width discipline (`einMische`); flags and memory kept. -/
def einKern (s : Zustand) (dec : IoDec) (b : IoBreite) (ans : Nat) : Zustand :=
  { s with rip := ripNach s.rip dec.laenge, register := regSet s.register .rax (einMische b (s.register .rax) (BitVec.ofNat 64 ans)) }

/-- One generic bus step under checked privilege data and map: decode
    length ok, architectural permission at the effective port, then an
    allowed device answer. OUT reads the accumulator implicitly
    (`ausGabe`); IN merges the answer with width discipline
    (`einMische`: 8/16-bit preserve the upper bits, 32-bit zero-extends).
    Reuses the accepted decoder vocabulary and accumulator helpers; no
    second opcode or register arithmetic lives here. Denial (bad length,
    denied permission, no allowed answer) has NO constructor: it is the
    absence of a step, never a silent skip. -/
inductive BusSchritt (D : Type) (erlaubt : BusAntwort D)
    (r : IoBerechtigung) (k : TssKarte) :
    BusZustand D → BusZustand D → Prop where
  | aus (s : BusZustand D) (dec : IoDec) (b : IoBreite)
      (q : PortQuelle) (g' : D)
      (hlen : laengeOk dec.laenge = true)
      (hop : dec.op = ⟨.aus, b, q⟩)
      (hperm : archZugelassen r k (portVon dec.op s.kern.register) b =
        true)
      (hant : erlaubt s.geraet .aus b (portVon dec.op s.kern.register)
        (ausGabe b (s.kern.register .rax)) g' 0) :
      BusSchritt D erlaubt r k s
        ⟨ausKern s.kern dec, g',
          s.spur ++ [⟨.aus, b, portVon dec.op s.kern.register,
            ausGabe b (s.kern.register .rax)⟩]⟩
  | ein (s : BusZustand D) (dec : IoDec) (b : IoBreite)
      (q : PortQuelle) (g' : D) (ans : Nat)
      (hlen : laengeOk dec.laenge = true)
      (hop : dec.op = ⟨.ein, b, q⟩)
      (hperm : archZugelassen r k (portVon dec.op s.kern.register) b =
        true)
      (hant : erlaubt s.geraet .ein b (portVon dec.op s.kern.register)
        0 g' ans) :
      BusSchritt D erlaubt r k s
        ⟨einKern s.kern dec b ans, g',
          s.spur ++ [⟨.ein, b, portVon dec.op s.kern.register, ans⟩]⟩

/-- A bus step never touches canonical memory: device bytes bypass RAM
    (and its TSO ordering) for EVERY device relation, by construction. -/
theorem busSchritt_speicher (D : Type) (erlaubt : BusAntwort D)
    (r : IoBerechtigung) (k : TssKarte) (s s' : BusZustand D)
    (h : BusSchritt D erlaubt r k s s') :
    s'.kern.speicher = s.kern.speicher := by
  cases h <;> rfl

/-- A bus step preserves the flags (IN/OUT are flag-neutral per both
    entries: "Flags Affected: None"), for every device relation. -/
theorem busSchritt_flags (D : Type) (erlaubt : BusAntwort D)
    (r : IoBerechtigung) (k : TssKarte) (s s' : BusZustand D)
    (h : BusSchritt D erlaubt r k s s') :
    s'.kern.flags = s.kern.flags := by
  cases h <;> rfl

/-- A bus step appends exactly one ordered event, for every relation. -/
theorem busSchritt_spur_waechst (D : Type) (erlaubt : BusAntwort D)
    (r : IoBerechtigung) (k : TssKarte) (s s' : BusZustand D)
    (h : BusSchritt D erlaubt r k s s') :
    s'.spur.length = s.spur.length + 1 := by
  cases h <;> simp

/-- Every bus step carried architectural permission: denial has no step,
    so a reached step is never a wrong-privilege access. -/
theorem busSchritt_perm (D : Type) (erlaubt : BusAntwort D)
    (r : IoBerechtigung) (k : TssKarte) (s s' : BusZustand D)
    (h : BusSchritt D erlaubt r k s s') :
    ∃ (port : Nat) (b : IoBreite),
      archZugelassen r k port b = true := by
  cases h with
  | aus dec b q g' hlen hop hperm hant => exact ⟨_, _, hperm⟩
  | ein dec b q g' ans hlen hop hperm hant => exact ⟨_, _, hperm⟩

/-- A bus step advances RIP past a valid decoded length, for every
    device relation. -/
theorem busSchritt_rip (D : Type) (erlaubt : BusAntwort D)
    (r : IoBerechtigung) (k : TssKarte) (s s' : BusZustand D)
    (h : BusSchritt D erlaubt r k s s') :
    ∃ l : Nat,
      s'.kern.rip = ripNach s.kern.rip l ∧ laengeOk l = true := by
  cases h with
  | aus dec _ _ _ hlen _ _ _ => exact ⟨dec.laenge, rfl, hlen⟩
  | ein dec _ _ _ _ hlen _ _ _ => exact ⟨dec.laenge, rfl, hlen⟩

/-! ## Fetched selection through the accepted fetch.

   `fetchIo` (lane 676) decodes the state's ACTUAL fetched window
   (`Byteschritt.geholt`) under the unified admission discipline. The
   generic step builds on it directly: a forged `IoDec` cannot inject an
   access, and malformed bytes refuse at fetch, before any device contact. -/

/-- SELECTION (OUT): a fetched port instruction plus an allowed device
    answer take a generic bus step. -/
theorem busSchritt_aus_fetch (D : Type) (erlaubt : BusAntwort D)
    (r : IoBerechtigung) (k : TssKarte) (s : BusZustand D)
    (d : IoDec) (rest : List Byte) (g' : D) (b : IoBreite)
    (q : PortQuelle)
    (hf : fetchIo s.kern = some (d, rest))
    (hop : d.op = ⟨.aus, b, q⟩)
    (hperm : archZugelassen r k (portVon d.op s.kern.register) b = true)
    (hant : erlaubt s.geraet .aus b (portVon d.op s.kern.register)
      (ausGabe b (s.kern.register .rax)) g' 0) :
    BusSchritt D erlaubt r k s
      ⟨ausKern s.kern d, g',
        s.spur ++ [⟨.aus, b, portVon d.op s.kern.register,
          ausGabe b (s.kern.register .rax)⟩]⟩ := by
  have hlen := (fetchIo_erfolg s.kern d rest hf).2.2.1
  exact .aus s d b q g' hlen hop hperm hant

/-- SELECTION (IN): a fetched port instruction plus an allowed device
    answer take a generic bus step. -/
theorem busSchritt_ein_fetch (D : Type) (erlaubt : BusAntwort D)
    (r : IoBerechtigung) (k : TssKarte) (s : BusZustand D)
    (d : IoDec) (rest : List Byte) (g' : D) (ans : Nat) (b : IoBreite)
    (q : PortQuelle)
    (hf : fetchIo s.kern = some (d, rest))
    (hop : d.op = ⟨.ein, b, q⟩)
    (hperm : archZugelassen r k (portVon d.op s.kern.register) b = true)
    (hant : erlaubt s.geraet .ein b (portVon d.op s.kern.register)
      0 g' ans) :
    BusSchritt D erlaubt r k s
      ⟨einKern s.kern d b ans, g',
        s.spur ++ [⟨.ein, b, portVon d.op s.kern.register, ans⟩]⟩ := by
  have hlen := (fetchIo_erfolg s.kern d rest hf).2.2.1
  exact .ein s d b q g' ans hlen hop hperm hant

/-! ## TSO-relative port ordering and completion events.

   Vol. 1 20.6: "The processor never buffers I/O writes. Therefore,
   strict ordering of I/O operations is enforced by the processor."
   Table 20-1 pins the serialization: IN delays the CURRENT instruction
   until pending stores complete, and OUT delays the NEXT instruction
   until pending stores AND the current store complete ("Pending
   Stores?" is Yes on both rows; "Current Store?" is Yes on OUT).
   Chipset posting ("it is possible for a chipset to post writes in
   certain I/O ranges", 20.6) stays outside the CPU model: see CUTS. -/

/-- Ordering gate for one port access on core `c`: the own TSO buffer
    must be drained first. This is an EXPOSED obligation, never a
    derived drain: no no-race proof discharges it. -/
def ordnungOk (tso : TSOZustand) (c : Nat) : IoDir → Bool
  | .ein => zaunBereit tso c
  | .aus => zaunBereit tso c

/-- An ordering-ok access runs on a literally empty own buffer. -/
theorem ordnung_braucht_leeren_puffer (tso : TSOZustand) (c : Nat)
    (dir : IoDir) (h : ordnungOk tso c dir = true) :
    tso.puffer c = [] := by
  unfold ordnungOk zaunBereit at h
  cases hp : tso.puffer c with
  | nil => rfl
  | cons e rest =>
    simp [hp] at h
    cases dir <;> simp at h

/-- A pending byte refuses the ordering gate, in either direction. -/
theorem ordnung_verweigert_bei_vollem_puffer (tso : TSOZustand) (c : Nat)
    (dir : IoDir) (e : TSOEintrag) (rest : List TSOEintrag)
    (h : tso.puffer c = e :: rest) : ordnungOk tso c dir = false := by
  have hle : zaunBereit tso c = false := by
    unfold zaunBereit
    simp [h]
  unfold ordnungOk
  cases dir
  · exact hle
  · exact hle

/-- Completion events: CPU-side completion and device-side response are
    DISTINCT constructors. For posted OUT ranges CPU completion never
    implies the device has consumed the byte; IN completes with its
    answer. No fake device answer for all ports: a device-side event
    exists only where the response relation allows one. -/
inductive BusFertig where
  | cpu : IoDir → IoBreite → Nat → Nat → BusFertig
  | geraet : IoDir → IoBreite → Nat → Nat → BusFertig
  deriving DecidableEq, Repr

/-- CPU and device completion never coincide, even with equal fields:
    posted access keeps them apart. -/
theorem fertig_getrennt (d : IoDir) (b : IoBreite) (port wert : Nat) :
    BusFertig.cpu d b port wert ≠ BusFertig.geraet d b port wert := by
  intro h
  cases h

/-- OUT needs a separate device-side completion (posted-write ranges,
    20.6); IN carries its answer synchronously with CPU completion. -/
def brauchtGeraetVollendung : IoDir → Bool
  | .aus => true
  | .ein => false

/-- OUT posts: its device completion is a separate obligation. -/
theorem aus_braucht_geraet : brauchtGeraetVollendung .aus = true := rfl

/-- IN answers: no separate device completion is owed. -/
theorem ein_braucht_kein_geraet :
    brauchtGeraetVollendung .ein = false := rfl

/-! ## First instance: the lane-676 latch, where sound.

   `geraetAntwort` is one latch/counter device shared across all ports.
   As a relation it is port-indifferent by construction -- that
   limitation stays explicit here (the port argument is unconstrained),
   and the second instance below shows what generality adds. -/

/-- The old port state as a generic bus state. -/
def busAusIo (s : IoZustand) : BusZustand GeraetZustand :=
  ⟨s.kern, s.geraet, s.spur⟩

/-- The latch as an allowed-answer relation: the answer IS
    `geraetAntwort`, at every port. The step fixes the driven value
    (`ausGabe` for OUT, 0 for IN), so no direction branch lives here. -/
def latchErlaubt : BusAntwort GeraetZustand :=
  fun g dir b _ treiber g' ans =>
    (geraetAntwort g dir b treiber) = (g', ans)

/-- SOUNDNESS (latch OUT): the stored truncated value is allowed. -/
theorem latch_aus_sound (g : GeraetZustand) (b : IoBreite) (port v : Nat) :
    latchErlaubt g .aus b port v ⟨v % ioMaske b, g.zaehl + 1⟩ 0 := by
  unfold latchErlaubt
  simp [geraetAntwort]

/-- SOUNDNESS (latch IN): the stored truncated value answers. -/
theorem latch_ein_sound (g : GeraetZustand) (b : IoBreite) (port : Nat) :
    latchErlaubt g .ein b port 0 ⟨g.daten, g.zaehl + 1⟩
      (g.daten % ioMaske b) := by
  unfold latchErlaubt
  simp [geraetAntwort]

/-- LIFT (latch OUT): a successful old OUT step is a generic bus step,
    reading privilege architecturally (the old admission carries
    CPL<=IOPL, so the direct leg covers it at the full map). -/
theorem latch_aus_lift (s : IoZustand) (dec : IoDec) (p : IoProfil)
    (b : IoBreite) (q : PortQuelle) (s' : IoZustand)
    (hok : laengeOk dec.laenge = true)
    (hop : dec.op = ⟨.aus, b, q⟩)
    (hperm : ioZugelassen p (portVon dec.op s.kern.register) = true)
    (hstep : ioSchritt dec s p = some s') :
    BusSchritt GeraetZustand latchErlaubt ⟨p.cpl, p.iopl⟩ volleKarte
      (busAusIo s) (busAusIo s') := by
  have hpriv := ioZugelassen_heisst_alle p _ hperm
  have hform := ioSchritt_aus_erfolg dec s p b q hok hop hperm
  rw [hform] at hstep
  cases hstep
  exact .aus (busAusIo s) dec b q _
    hok hop (arch_direkt _ _ _ _ hpriv.2.1)
    (latch_aus_sound _ _ _ _)

/-- LIFT (latch IN): a successful old IN step is a generic bus step,
    under the same architectural privilege reading. -/
theorem latch_ein_lift (s : IoZustand) (dec : IoDec) (p : IoProfil)
    (b : IoBreite) (q : PortQuelle) (s' : IoZustand)
    (hok : laengeOk dec.laenge = true)
    (hop : dec.op = ⟨.ein, b, q⟩)
    (hperm : ioZugelassen p (portVon dec.op s.kern.register) = true)
    (hstep : ioSchritt dec s p = some s') :
    BusSchritt GeraetZustand latchErlaubt ⟨p.cpl, p.iopl⟩ volleKarte
      (busAusIo s) (busAusIo s') := by
  have hpriv := ioZugelassen_heisst_alle p _ hperm
  have hform := ioSchritt_ein_erfolg dec s p b q hok hop hperm
  rw [hform] at hstep
  cases hstep
  exact .ein (busAusIo s) dec b q _ _
    hok hop (arch_direkt _ _ _ _ hpriv.2.1)
    (latch_ein_sound _ _ _)

/-! ## Second instance: a port-distinguishing table device.

   Generality witness: one register per port plus an observation
   counter. Two ports answer differently from the same start --
   something the latch can never do (its IN answer is port-independent,
   proved below). This is what the generic interface adds over 676. -/

/-- Table device: one register per port plus an access counter. -/
structure TabellenGeraet where
  tab : Nat → Nat
  zaehl : Nat

/-- The table device answers the ADDRESSED register truncated to the
    width; OUT stores the truncated value into the addressed register;
    every access advances the counter. -/
def tabellenErlaubt : BusAntwort TabellenGeraet :=
  fun g dir b port treiber g' ans =>
    match dir with
    | .aus =>
      g' = ⟨fun q => if q = port then treiber % ioMaske b else g.tab q,
        g.zaehl + 1⟩ ∧ ans = 0
    | .ein =>
      g' = ⟨g.tab, g.zaehl + 1⟩ ∧ ans = g.tab port % ioMaske b

/-- PORT-DISTINGUISHING: from a start whose registers differ at ports 96
    and 97 (mod 256), the two IN answers differ -- from the same device
    state, keyed by the actual port. -/
theorem tabelle_unterscheidet (t : Nat → Nat) (z : Nat)
    (h : t 96 % 256 ≠ t 97 % 256) :
    ∃ (g1 g2 : TabellenGeraet) (a1 a2 : Nat),
      tabellenErlaubt ⟨t, z⟩ .ein .p8 96 0 g1 a1 ∧
      tabellenErlaubt ⟨t, z⟩ .ein .p8 97 0 g2 a2 ∧ a1 ≠ a2 := by
  refine ⟨⟨t, z + 1⟩, ⟨t, z + 1⟩, t 96 % 256, t 97 % 256,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, h⟩

/-- The latch cannot distinguish ports: from one start, IN answers the
    same value at any two ports. This is the documented 676 limitation
    that the table instance removes. -/
theorem latch_unterscheidet_nicht (g : GeraetZustand) (b : IoBreite)
    (p q : Nat) (g1 g2 : GeraetZustand) (a1 a2 : Nat)
    (h1 : latchErlaubt g .ein b p 0 g1 a1)
    (h2 : latchErlaubt g .ein b q 0 g2 a2) : a1 = a2 := by
  unfold latchErlaubt at h1 h2
  have e1 : (geraetAntwort g .ein b 0).2 = a1 := congrArg Prod.snd h1
  have e2 : (geraetAntwort g .ein b 0).2 = a2 := congrArg Prod.snd h2
  exact e1.symm.trans e2

/-! ## Adapter for the common hardware execution (owner 660).

   The generic latch step lifted to the extended state: it runs on
   `kern`; XMM and FP control are untouched (mirroring `laufAlt` and
   `hw660Schritt`). Denial is the absence of a step, so the adapter
   takes successful steps only -- there is no refused case to smuggle a
   fault through. Syscall/interrupt scope stays with lane 672: no trap
   form exists here. -/

/-- Adapter step on the extended state under checked map data: the
    successor core with the caller's XMM file and FP context. Takes the
    reached successor plus its step evidence: the adapter never builds a
    triple from an unreached state. (No `IoDec` is taken: fetching and
    decoding happened before the step; the adapter does not re-decode.) -/
def bus660Schritt (t : FpZustand) (g : GeraetZustand)
    (spur : List IoEreignis) (r : IoBerechtigung) (k : TssKarte)
    (s' : BusZustand GeraetZustand)
    (h : BusSchritt GeraetZustand latchErlaubt r k ⟨t.kern, g, spur⟩ s') :
    FpZustand × GeraetZustand × List IoEreignis :=
  ⟨⟨s'.kern, t.xmm, t.fp⟩, s'.geraet, s'.spur⟩

/-- The adapter keeps every XMM register. -/
theorem bus660Schritt_xmm (t : FpZustand) (g : GeraetZustand)
    (spur : List IoEreignis) (r : IoBerechtigung) (k : TssKarte)
    (s' : BusZustand GeraetZustand)
    (h : BusSchritt GeraetZustand latchErlaubt r k ⟨t.kern, g, spur⟩ s')
    (q : XmmReg) :
    (bus660Schritt t g spur r k s' h).1.xmm q = t.xmm q := by
  unfold bus660Schritt
  rfl

/-- The adapter keeps the FP control word. -/
theorem bus660Schritt_fp (t : FpZustand) (g : GeraetZustand)
    (spur : List IoEreignis) (r : IoBerechtigung) (k : TssKarte)
    (s' : BusZustand GeraetZustand)
    (h : BusSchritt GeraetZustand latchErlaubt r k ⟨t.kern, g, spur⟩ s') :
    (bus660Schritt t g spur r k s' h).1.fp = t.fp := rfl

/-- The adapter never touches canonical memory. -/
theorem bus660Schritt_speicher (t : FpZustand)
    (g : GeraetZustand) (spur : List IoEreignis) (r : IoBerechtigung)
    (k : TssKarte) (s' : BusZustand GeraetZustand)
    (h : BusSchritt GeraetZustand latchErlaubt r k ⟨t.kern, g, spur⟩ s') :
    (bus660Schritt t g spur r k s' h).1.kern.speicher =
      t.kern.speicher := by
  have hm := busSchritt_speicher GeraetZustand latchErlaubt r k _ s' h
  exact hm

/- CUTS:
   Skeleton only: the TSS map type, one per-byte check and its witness.
   Range checks, the architectural rule, the generic device interface,
   ordering, instances, adapters and the joint witness are still OPEN.
-/

#print axioms volleKarte_96_frei

end Gabbro.Grammatik.X86
