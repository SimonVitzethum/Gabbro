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

/- CUTS:
   Skeleton only: the TSS map type, one per-byte check and its witness.
   Range checks, the architectural rule, the generic device interface,
   ordering, instances, adapters and the joint witness are still OPEN.
-/

#print axioms volleKarte_96_frei

end Gabbro.Grammatik.X86
