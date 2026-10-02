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

/- Lane-704 scope: every declaration below lives in `Bus704`, so no
   flat `X86` name here can collide with another lane's module at
   umbrella build time (repair of the failed integration against
   `MemoryTypeHardwareExecution.witFp`; no semantic change). -/
namespace Bus704

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

/-! ## Device/MMIO adapter (owner 694) and validator admission.

   Port IO runs on the I/O address space; MMIO/DMA run on the memory
   address space under segmentation, paging and the MTRR memory-type
   rules (Vol. 1 20.5, first bullet; 20.6, first half: uncacheable
   regions keep program order externally). Those type and ordering rules
   are unmodelled here, so both device-memory kinds refuse at this
   layer -- the stub admits nothing silently, and the remaining
   memory-type/ordering obligations stay explicit in CUTS. -/

/-- MMIO/694 admission stub: RAM passes through (port IO runs beside
    ordinary RAM); MMIO and DMA refuse until their rules are modelled. -/
def mmio694Adapter : SpeicherArt → Option Unit
  | .ram => some ()
  | .mmio => none
  | .dma => none

/-- MMIO refuses at this layer. -/
theorem mmio694_verweigert_mmio : mmio694Adapter .mmio = none := rfl

/-- DMA refuses at this layer. -/
theorem mmio694_verweigert_dma : mmio694Adapter .dma = none := rfl

/-- Ordinary RAM passes the kind gate. -/
theorem mmio694_laesst_ram_zu : mmio694Adapter .ram = some () := rfl

/-- Validator admission for one port operation: architectural permission
    at the effective port AND an admitted memory kind AND a drained own
    TSO buffer (Table 20-1). All three are checked facts about the
    state's data, never assumed OS or binding contracts. -/
def busValOk (r : IoBerechtigung) (k : TssKarte) (mem : SpeicherProfil)
    (art : SpeicherArt) (tso : TSOZustand) (c : Nat) (dir : IoDir)
    (op : IoOp) (regs : Register → Wort) : Bool :=
  archZugelassen r k (portVon op regs) op.breite &&
    speicherArtZugelassen mem art && ordnungOk tso c dir

/-- Admission means all three sides hold, jointly. -/
theorem busValOk_heisst (r : IoBerechtigung) (k : TssKarte)
    (mem : SpeicherProfil) (art : SpeicherArt) (tso : TSOZustand)
    (c : Nat) (dir : IoDir) (op : IoOp) (regs : Register → Wort)
    (h : busValOk r k mem art tso c dir op regs = true) :
    archZugelassen r k (portVon op regs) op.breite = true ∧
      speicherArtZugelassen mem art = true ∧
      ordnungOk tso c dir = true := by
  unfold busValOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hperm, hkind⟩, hord⟩ := h
  exact ⟨hperm, hkind, hord⟩

/-! ## Joint witness: fetched generic IN/OUT, device change, RAM store.

   The same image as the lane-676 witness (`ioWitKern`: an 8-bit IN from
   port 0x60, an 8-bit OUT to 0x60, then the pilot 64-bit store): the
   device is preset to `0x1234`, so IN answers `0x34 = 52` and OUT stores
   52 back (device `0x1234` to 52, two observations). Privilege data is
   CPL 3 against IOPL 3 (direct leg); the map spans everything with only
   byte 97 set, so width-boundary and wrong-privilege denials are one
   mutation away. -/

/-- Witness privilege data: user CPL 3 with IOPL 3 (direct leg). -/
def witRecht : IoBerechtigung := ⟨3, 3⟩

/-- Witness map: fully spanned, only port byte 97 set. Port 96 is free
    for 8-bit accesses; 16-bit access at 96 covers the set byte 97. -/
def witKarte : TssKarte :=
  { basis := 0, grenze := 8192, bit := fun q => decide (q = 97) }

/-- Witness start: the accepted core image with the latch at `0x1234`. -/
def busWitStart : BusZustand GeraetZustand := ⟨ioWitKern, ⟨0x1234, 0⟩, []⟩

/-- Witness after the generic IN: the accumulator merged 52, the device
    kept `0x1234` with one observation, one ordered event logged. -/
def witS1 : BusZustand GeraetZustand :=
  ⟨einKern ioWitKern ⟨⟨.ein, .p8, .imm 96⟩, 2⟩ .p8 52, ⟨0x1234, 1⟩,
    [⟨.ein, .p8, 96, 52⟩]⟩

/-- Witness after the generic OUT: registers kept, the device moved to
    52 with two observations, IN then OUT logged in order. -/
def witS2 : BusZustand GeraetZustand :=
  ⟨ausKern witS1.kern ⟨⟨.aus, .p8, .imm 96⟩, 2⟩, ⟨52, 2⟩,
    witS1.spur ++ [⟨.aus, .p8, 96, 52⟩]⟩

/-- First step: the generic IN answers 52 into AL under the direct leg. -/
theorem wit_schritt1 :
    BusSchritt GeraetZustand latchErlaubt witRecht witKarte busWitStart
      witS1 := by
  exact .ein busWitStart ⟨⟨.ein, .p8, .imm 96⟩, 2⟩ .p8 (.imm 96)
    ⟨0x1234, 1⟩ 52 (by decide) rfl (by decide)
    (latch_ein_sound _ _ _)

/-- Second step: the generic OUT stores the received 52 into the device. -/
theorem wit_schritt2 :
    BusSchritt GeraetZustand latchErlaubt witRecht witKarte witS1
      witS2 := by
  exact .aus witS1 ⟨⟨.aus, .p8, .imm 96⟩, 2⟩ .p8 (.imm 96) ⟨52, 2⟩
    (by decide) rfl (by decide)
    (latch_aus_sound _ _ _ _)

/-- The device observably moved `0x1234` to 52 with two observations. -/
theorem wit_geraet_geaendert :
    witS2.geraet.daten = 52 ∧ witS2.geraet.zaehl = 2 := ⟨rfl, rfl⟩

/-- The accumulator holds the received 52 after both port steps. -/
theorem wit_akk_52 :
    witS2.kern.register .rax = BitVec.ofNat 64 52 := by
  decide

/-- Both port steps land RIP at 4100: the pilot store starts from the
    same core state as the accepted run (`ioWit_zweiter_sendet`). -/
theorem wit_rip_anschluss :
    witS2.kern.rip = BitVec.ofNat 64 4100 := by
  decide

/-- FRAME (memory): both generic steps bypassed RAM -- the cell the
    pilot store will write still reads zero. -/
theorem wit_rahmen_speicher :
    witS2.kern.speicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 0 := by
  have h1 := busSchritt_speicher GeraetZustand latchErlaubt witRecht
    witKarte busWitStart witS1 wit_schritt1
  have h2 := busSchritt_speicher GeraetZustand latchErlaubt witRecht
    witKarte witS1 witS2 wit_schritt2
  have h0 : busWitStart.kern.speicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 0 := ioWit_anfang_null
  rw [h2, h1]
  exact h0

/-- FRAME (flags): both generic steps are flag-neutral. -/
theorem wit_rahmen_flags :
    witS2.kern.flags = busWitStart.kern.flags := by
  have h1 := busSchritt_flags GeraetZustand latchErlaubt witRecht
    witKarte busWitStart witS1 wit_schritt1
  have h2 := busSchritt_flags GeraetZustand latchErlaubt witRecht
    witKarte witS1 witS2 wit_schritt2
  rw [h2, h1]

/-- Witness extended state over the port image (reset control word). -/
def witFp : FpZustand :=
  ⟨ioWitKern, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- FRAME (FP/XMM): the 660 adapter keeps XMM and control over the
    reached generic IN step. -/
theorem wit_rahmen_fp (q : XmmReg) :
    (bus660Schritt witFp ⟨0x1234, 0⟩ [] witRecht witKarte witS1
      wit_schritt1).1.xmm q = witFp.xmm q :=
  bus660Schritt_xmm _ _ _ _ _ _ _ _

/-- WIDTH BOUNDARY: above IOPL a 16-bit access at port 96 covers the set
    byte 97 and refuses -- every covered byte is checked. -/
theorem wit_breite_16_an_96_verweigert :
    archZugelassen ⟨3, 0⟩ witKarte 96 .p16 = false := by
  decide

/-- The same port at 8 bits is free above IOPL: byte 96 is clear. -/
theorem wit_breite_8_an_96_frei :
    archZugelassen ⟨3, 0⟩ witKarte 96 .p8 = true := by
  decide

/-- WRONG PRIVILEGE: port byte 97 denies above IOPL and faults as #GP. -/
theorem wit_falsches_privileg_gp :
    busFehler (archZugelassen ⟨3, 0⟩ witKarte 97 .p8) = some .gp := by
  decide

/-- MAP MUTATION: clearing the one set bit admits port 97 above IOPL --
    permission follows checked map data, not a fixed verdict. -/
theorem wit_kartenmutation_laesst_97_zu :
    archZugelassen ⟨3, 0⟩ volleKarte 97 .p8 = true := by
  decide

/-- MALFORMED FETCH: the forged `0xFF` first byte refuses fetch -- no
    device contact, no event, before any permission or answer question.
    Raw `BusSchritt` trusts its decoded argument; the selection theorems
    are the gate, so fetch refusal is byte-step refusal. -/
theorem wit_fehlbyte_fetch_verweigert :
    fetchIo ioWitStartFalsch.kern = none := by
  decide

/-- Witness TSO view over the port image memory, buffer drained. -/
def witTsoLeer : TSOZustand := ⟨ioWitSpeicher, fun _ => []⟩

/-- Witness TSO view with one pending byte on core 0. -/
def witTsoVoll : TSOZustand :=
  ⟨ioWitSpeicher, fun c =>
    if c = 0 then [⟨BitVec.ofNat 64 8192, BitVec.ofNat 8 1⟩] else []⟩

/-- ORDER OK: IN with a drained own buffer passes the gate. -/
theorem wit_ordnung_ok : ordnungOk witTsoLeer 0 .ein = true := by
  decide

/-- ORDER MUTATION: one pending byte refuses the gate in both
    directions (Table 20-1, "Pending Stores?" is Yes on both rows). -/
theorem wit_ordnung_mutation :
    ordnungOk witTsoVoll 0 .ein = false ∧
      ordnungOk witTsoVoll 0 .aus = false := by
  decide

/-- IN 32-bit zero-extends at the witness core: the upper half clears,
    independently of the concrete device relation. -/
theorem wit_p32_loescht_oben :
    (einKern ioWitKern ⟨⟨.ein, .p32, .imm 96⟩, 2⟩ .p32 0x11223344).register
        .rax =
      BitVec.ofNat 64 0x11223344 := by
  decide

/-- OUT reads the accumulator implicitly: the driven value is the
    received 52, never a caller-supplied constant. -/
theorem wit_aus_liest_rax :
    ausGabe .p8 (witS1.kern.register .rax) = 52 := by
  decide

/-- TABLE WITNESS (closed): the identity table answers 96 at port 96
    and 97 at port 97 -- port-distinguishing, jointly instantiated. -/
theorem tabelle_unterscheidet_zeuge :
    ∃ (g1 g2 : TabellenGeraet) (a1 a2 : Nat),
      tabellenErlaubt ⟨fun q => q, 0⟩ .ein .p8 96 0 g1 a1 ∧
      tabellenErlaubt ⟨fun q => q, 0⟩ .ein .p8 97 0 g2 a2 ∧
        a1 ≠ a2 :=
  tabelle_unterscheidet (fun q => q) 0 (by decide)

/-! ## Joint witness: the reached run beside every planted refusal. -/

/-- JOINT WITNESS: reached fetched generic IN/OUT under the direct leg
    (accumulator to 52, device `0x1234` to 52 with two observations,
    ordered IN-then-OUT log, RIP at the pilot store, memory/flags/FP
    frames) beside the RAM-store Anschluss (cell 8192 zero to 52), the
    width-boundary split (16-bit at 96 refused, 8-bit free), the
    wrong-privilege #GP at 97, the admitting map mutation, the
    malformed-byte fetch refusal and the order-gate mutation.
    Non-degenerate: the device changed state AND the run reaches the
    memory-changing pilot store, with planted refusals jointly
    instantiated. -/
theorem bus_zeuge_gemeinsam :
    BusSchritt GeraetZustand latchErlaubt witRecht witKarte busWitStart
        witS1 ∧
      BusSchritt GeraetZustand latchErlaubt witRecht witKarte witS1
        witS2 ∧
      witS2.geraet.daten = 52 ∧ witS2.geraet.zaehl = 2 ∧
      witS2.kern.register .rax = BitVec.ofNat 64 52 ∧
      witS2.kern.rip = BitVec.ofNat 64 4100 ∧
      ausgangByte (BitVec.ofNat 64 8192) ioWitSchritt3 =
        some (BitVec.ofNat 8 52) ∧
      ioWitStart.kern.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 ∧
      witS2.kern.flags = busWitStart.kern.flags ∧
      archZugelassen ⟨3, 0⟩ witKarte 96 .p16 = false ∧
      archZugelassen ⟨3, 0⟩ witKarte 96 .p8 = true ∧
      busFehler (archZugelassen ⟨3, 0⟩ witKarte 97 .p8) = some .gp ∧
      archZugelassen ⟨3, 0⟩ volleKarte 97 .p8 = true ∧
      fetchIo ioWitStartFalsch.kern = none ∧
      ordnungOk witTsoLeer 0 .ein = true ∧
      ordnungOk witTsoVoll 0 .aus = false := by
  refine ⟨wit_schritt1, wit_schritt2, wit_geraet_geaendert.1,
    wit_geraet_geaendert.2, wit_akk_52, wit_rip_anschluss,
    ioWit_dritter_speichert.1, ioWit_anfang_null, wit_rahmen_flags,
    wit_breite_16_an_96_verweigert, wit_breite_8_an_96_frei,
    wit_falsches_privileg_gp, wit_kartenmutation_laesst_97_zu,
    wit_fehlbyte_fetch_verweigert, wit_ordnung_ok,
    wit_ordnung_mutation.2⟩

/- CUTS:
    Proved here, over the REUSED accepted vocabulary (`Typen.Zustand`,
    `DeviceHardwareForms`: `IoBreite/IoDir/PortQuelle/IoOp/IoDec`,
    `decodeIo/fetchIo/ioByteschritt`, `portVon/ausGabe/einMische`,
    `ioZugelassen_heisst_alle`, `ioSchritt_aus/ein_erfolg`,
    `ioWitKern/ioWitStart/ioWitSchritt3/ioWitStartFalsch`,
    `ioWit_dritter_speichert/ioWit_anfang_null`,
    `SpeicherProfil/speicherArtZugelassen`, `HardwareFaults.ArchFehler`,
    `TSO.zaunBereit/TSOZustand`, `ScalarFloat.FpZustand`,
    `Gleitprofil.kontextReset` -- no second decoder, no copied opcode or
    register arithmetic, no new machine):
    - precise TSS bitmap checks for EVERY byte covered by 8/16/32-bit
      widths (range-end, unspanned and past-65535 bytes deny; missing
      map denies), with the selected 64-bit long-mode rule (CPL<=IOPL
      admits directly with no bitmap consult, else the range decides)
      and denial as #GP(0) in the accepted fault vocabulary;
    - the lane-676 conjunction kept ONLY as a conservative compiler
      admission profile, with soundness (admitted implies silicon
      admits) and incompleteness (direct leg admits what it refuses);
      profiles are checked data (CPL/IOPL plus the map), never a
      trusted OS-ready Bool;
    - one generic bus/device response interface over an arbitrary
      device type with an allowed read/write relation keyed by actual
      port/direction/width/driven-value; architectural IN truncation
      (8/16-bit preserve upper, 32-bit zero-extends) and OUT implicit
      source proved through the accepted helpers, independently of the
      concrete relation; RIP/flag/memory/log/permission frames for
      every relation; fetched selection through the accepted fetch;
    - TSO-relative ordering as an exposed gate (own buffer drained,
      both directions, per Table 20-1) with full-buffer refusal --
      never derived from a no-race proof; CPU and device completion as
      distinct events with the posted-OUT obligation;
    - the old latch as one explicit sound instance with both old-step
      lifts, plus a SECOND port-distinguishing table device (with the
      latch-indistinguishability limit proved);
    - the 660 adapter (XMM/control/memory frames over reached steps),
      the refusing MMIO/DMA 694 stub, and the three-sided validator
      admission;
    - a joint reached fetched-IN/OUT run (device `0x1234` to 52, two
      observations) into the accepted memory-changing pilot store,
      beside width-boundary, wrong-privilege #GP, map-mutation,
      malformed-byte and order-gate refusals.
    NOT proved here, and not claimed:
    - No hardware correspondence beyond the cited Intel SDM entries
      (provenance in the file header, not proofs): encodings stay the
      accepted canonical subset; the bitmap's OS-side population, the
      TSS layout bytes and chipset posting are named behaviour, not
      verified silicon.
    - No MMIO/DMA execution (refused: `mmio694_verweigert_*`); their
      UC/WC memory-type and ordering rules are unmodelled, and no TSO
      buffer ever carries a device byte by construction.
    - No string-IO forms (INS/OUTS), no REP prefix, no LOCK prefix on
      IN/OUT (#UD stays with the fault lane), no virtual-8086 mode, no
      timing: the selected rule is 64-bit long mode only.
    - No per-access target-to-W/GX simulation and no whole-word
      atomicity beyond the accepted grouping: the ordering gate exposes
      the drain obligation the TSO bridge must discharge.
    - No source correspondence, no ABI/image/entry/relocation/budget
      link, no syscall/interrupt scope (lane 672).
    - Raw `BusSchritt` trusts its decoded argument (like the accepted
      `ioSchritt`); fetched admission lives in the selection theorems.
      `none` is the absence of a transition, never a halt claim.
-/

#print axioms arch_direkt
#print axioms arch_bitmap
#print axioms karte_fehlt_verweigert
#print axioms busFehler_gp_bei_verweigerung
#print axioms compiler_sound
#print axioms compiler_unvollstaendig
#print axioms busSchritt_speicher
#print axioms busSchritt_flags
#print axioms busSchritt_spur_waechst
#print axioms busSchritt_perm
#print axioms busSchritt_rip
#print axioms busSchritt_aus_fetch
#print axioms busSchritt_ein_fetch
#print axioms ordnung_braucht_leeren_puffer
#print axioms ordnung_verweigert_bei_vollem_puffer
#print axioms fertig_getrennt
#print axioms latch_aus_sound
#print axioms latch_ein_sound
#print axioms latch_aus_lift
#print axioms latch_ein_lift
#print axioms tabelle_unterscheidet
#print axioms latch_unterscheidet_nicht
#print axioms bus660Schritt_xmm
#print axioms bus660Schritt_fp
#print axioms bus660Schritt_speicher
#print axioms mmio694_verweigert_mmio
#print axioms busValOk_heisst
#print axioms wit_schritt1
#print axioms wit_schritt2
#print axioms bus_zeuge_gemeinsam
#print axioms volleKarte_96_frei

end Bus704

end Gabbro.Grammatik.X86
