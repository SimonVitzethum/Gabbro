/-
  File:      Grammatik/X86/Avx2Join.lean
  Subject:   AVX2 join: VEX rows, Ops, YMM state and TSO memory on one
             coherent machine.

  Lane 1265 (follow-up of 1239 `Avx2Ops`): the sibling pieces Vex (1237),
  State (1241) and Mem (1243) are NOT in this tree (only `Avx2Ops.lean`
  exists here), so this file joins what IS accepted -- the pure 256-bit
  evaluators and the tier gate of `Avx2Ops`, the leaf gate of
  `CpuFeatureHardwareForms`, the coherent `HwMaschine`/`HwSchritt` of
  `HardwareExecution`, the TSO folds of `TSO`/`HardwareExecution` and the
  chunk loader of `HwVector` -- with a minimal VEX-row decoder, a YMM
  file and 32-byte TSO memory forms defined HERE (never copied). A bare
  `HwAdapter` over `HwMaschine` cannot carry YMM state (`HwKern` has no
  YMM slot), so the join is an extended step relation with an exact
  `HwSchritt` embedding (the mechanism's allowed alternative).

  Silicon provenance (clone-local
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
  VPADDQ VEX.256.66.0F.WIG D4 /r (line 73615, AVX2); VPXOR
  VEX.256.66.0F.WIG EF /r (line 90041, AVX2); VMOVDQA VEX.256.66.0F.WIG
  6F/7F (lines 67104/67106); VMOVDQU VEX.256.F3.0F.WIG 6F/7F (lines
  67351/67353); VEX.256 per-64-bit-lane add (lines 73809-73813).
  VEX prefix bit derivation follows Vol. 2A 2.3.5 (C4, inverted R/X/B,
  W-vvvv-L-pp). Full ModRM/SIB decode stays the absent Vex piece's job.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.Avx2Ops
import Grammatik.X86.CpuFeatureHardwareForms
import Grammatik.X86.VectorHardwareProfile
import Grammatik.X86.VectorCodec
import Grammatik.X86.HwVector
import Grammatik.X86.ConcurrentIntegerExecution
import Grammatik.X86.TSO
import Grammatik.X86.Speicher
import Grammatik.X86.Vektor
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Gleitprofil

namespace Gabbro.Grammatik.X86

/-- The sixteen AVX2 vector registers. `HwKern` has no YMM slot, so the
    join carries its own file beside `HwMaschine` (see `Avx2Maschine`). -/
inductive YmmReg where
  | ymm0 | ymm1 | ymm2 | ymm3 | ymm4 | ymm5 | ymm6 | ymm7
  | ymm8 | ymm9 | ymm10 | ymm11 | ymm12 | ymm13 | ymm14 | ymm15
  deriving DecidableEq, Repr, Inhabited

/-- YMM register file: each entry is a full 256-bit `Ymm` value. -/
abbrev YmmDatei := YmmReg → Ymm

/-- YMM register-file update: `dst` holds `v`, the rest is kept. -/
def ymmSet (f : YmmDatei) (dst : YmmReg) (v : Ymm) : YmmDatei :=
  fun q => if q = dst then v else f q

/-- The updated YMM register answers `v` at `dst`. -/
theorem ymmSet_gleich (f : YmmDatei) (dst : YmmReg) (v : Ymm) :
    ymmSet f dst v dst = v := by
  simp [ymmSet]

/-- Every other YMM register keeps its value. -/
theorem ymmSet_fremd (f : YmmDatei) (dst q : YmmReg) (v : Ymm)
    (h : q ≠ dst) : ymmSet f dst v q = f q := by
  unfold ymmSet
  rw [if_neg h]

/-! ## 1. VEX rows (the absent Vex piece's substitute, minimal).

  Four decoded rows only: two 5-byte register rows (VPADDQ, VPXOR) and
  two 6-byte unaligned memory rows (VMOVDQU load/store, mod=01 rm=rax
  disp8). Widths follow silicon: add/sub/compare carry a lane width,
  and/or/xor/andn are widthless (evaluated at `.b64`); shifts carry a
  lane width plus imm8. The `.b8` shifts and `.b64` arithmetic shift
  have no AVX2 encoding (Avx2Ops §3) and are refused at evaluation. -/

/-- Joined AVX2 operation vocabulary: register arithmetic/logic over
    the accepted `ymm*` evaluators plus absolute-free memory rows
    through base-plus-disp8 (the GPR file stays the machine's own). -/
inductive Avx2Op where
  | vpaddRR (b : Breite) (dst src1 src2 : YmmReg)
  | vpsubRR (b : Breite) (dst src1 src2 : YmmReg)
  | vpandRR (dst src1 src2 : YmmReg)
  | vporRR (dst src1 src2 : YmmReg)
  | vpxorRR (dst src1 src2 : YmmReg)
  | vpandnRR (dst src1 src2 : YmmReg)
  | vpcmpeqRR (b : Breite) (dst src1 src2 : YmmReg)
  | vpsllImm (b : Breite) (dst src : YmmReg) (imm : Nat)
  | vpsrlImm (b : Breite) (dst src : YmmReg) (imm : Nat)
  | vpsraImm (b : Breite) (dst src : YmmReg) (imm : Nat)
  | vmovdqaLd (dst : YmmReg) (base : Register) (disp : BitVec 8)
  | vmovdqaSt (base : Register) (src : YmmReg) (disp : BitVec 8)
  | vmovdquLd (dst : YmmReg) (base : Register) (disp : BitVec 8)
  | vmovdquSt (base : Register) (src : YmmReg) (disp : BitVec 8)
  deriving DecidableEq, Repr

/-- A decoded VEX row: the operation plus its byte length (RIP moves
    past exactly this many bytes). -/
structure Avx2Zeile where
  op : Avx2Op
  laenge : Nat
  deriving DecidableEq, Repr

/-- Register rows: every row except the four memory rows. The machine
    adapter admits only these on the register path; memory rows use the
    TSO path of §5. -/
def istAvx2RegisterOp : Avx2Op → Bool
  | .vmovdqaLd _ _ _ => false
  | .vmovdqaSt _ _ _ => false
  | .vmovdquLd _ _ _ => false
  | .vmovdquSt _ _ _ => false
  | _ => true

/-- Minimal VEX.256 decoder over four pinned byte patterns (see the
    file header for provenance). VEX.128 shapes (L=0) and non-VEX
    bytes refuse: the former belong to the legacy piece, the latter
    are no AVX2 row. -/
def dekodiereAvx2 (bs : List Byte) : Option Avx2Zeile :=
  if bs == [(0xC4 : Byte), 0xE1, 0x75, 0xD4, 0xC2] then
    some ⟨.vpaddRR .b64 .ymm0 .ymm1 .ymm2, 5⟩
  else if bs == [(0xC4 : Byte), 0xE1, 0x75, 0xEF, 0xC2] then
    some ⟨.vpxorRR .ymm0 .ymm1 .ymm2, 5⟩
  else if bs == [(0xC4 : Byte), 0xE1, 0x7E, 0x6F, 0x40, 0x00] then
    some ⟨.vmovdquLd .ymm0 .rax 0x00, 6⟩
  else if bs == [(0xC4 : Byte), 0xE1, 0x7E, 0x7F, 0x40, 0x00] then
    some ⟨.vmovdquSt .rax .ymm0 0x00, 6⟩
  else none

/-- The pinned VPADDQ row decodes (VEX.256.66.0F.WIG D4 /r). -/
theorem dekodiere_paddq :
    dekodiereAvx2 [(0xC4 : Byte), 0xE1, 0x75, 0xD4, 0xC2] =
      some ⟨.vpaddRR .b64 .ymm0 .ymm1 .ymm2, 5⟩ := by
  decide

/-- The pinned VPXOR row decodes (VEX.256.66.0F.WIG EF /r). -/
theorem dekodiere_pxor :
    dekodiereAvx2 [(0xC4 : Byte), 0xE1, 0x75, 0xEF, 0xC2] =
      some ⟨.vpxorRR .ymm0 .ymm1 .ymm2, 5⟩ := by
  decide

/-- The pinned VMOVDQU load decodes (VEX.256.F3.0F.WIG 6F /r). -/
theorem dekodiere_movdquLd :
    dekodiereAvx2 [(0xC4 : Byte), 0xE1, 0x7E, 0x6F, 0x40, 0x00] =
      some ⟨.vmovdquLd .ymm0 .rax 0x00, 6⟩ := by
  decide

/-- The pinned VMOVDQU store decodes (VEX.256.F3.0F.WIG 7F /r). -/
theorem dekodiere_movdquSt :
    dekodiereAvx2 [(0xC4 : Byte), 0xE1, 0x7E, 0x7F, 0x40, 0x00] =
      some ⟨.vmovdquSt .rax .ymm0 0x00, 6⟩ := by
  decide

/-- A VEX.128 shape (L=0 third prefix byte) refuses: 128-bit VEX rows
    belong to the legacy piece, never here. -/
theorem dekodiere_vex128_verweigert :
    dekodiereAvx2 [(0xC4 : Byte), 0xE1, 0x74, 0xD4, 0xC2] = none := by
  decide

/-- Non-VEX bytes refuse: a legacy opcode is no AVX2 row. -/
theorem dekodiere_fremd_verweigert :
    dekodiereAvx2 [(0x66 : Byte), 0x0F, 0xD4, 0xC2] = none := by
  decide

/-! ## 2. Profile<->leaf bridge (the gap lane 1239 lists as missing).

  `avx2TierBereit` (Avx2Ops, over checked profile structs) and
  `CpuFeatureHardwareForms.avx2Bereit` (over observed CPUID leaves and
  the XCR0 low word) speak about disjoint inputs: the profile side
  knows silicon AVX2/SSE2, XCR0 readiness, control freedom and OS
  state, while the leaf side knows silicon AVX/OSXSAVE/XMM+YMM but
  neither silicon SSE2 nor any control register. No unconditional
  equivalence holds -- each direction needs the other side's missing
  conjuncts as explicit premises (named below, never smuggled). -/

/-- Observed silicon features as a checked CPU profile: SSE2 from
    leaf-1 EDX[26], AVX2 from leaf-7 EBX[5]. -/
def cpuAusBlaettern (leaf1 leaf7 : CpuOut) : CpuMerkmal :=
  ⟨edxSSE2 leaf1, ebxAVX2 leaf7⟩

/-- Observed XCR0 low word as checked XCR0 state: x87 from bit 0, SSE
    from bit 1 (`xcrXMM`), AVX from bit 2 (`xcrYMM`). -/
def xcr0AusWort (xcrLo : BitVec 32) : Xcr0Bild :=
  ⟨bit32 xcrLo 0, xcrXMM xcrLo, xcrYMM xcrLo⟩

/-- The mapped AVX bit IS the observed leaf-7 bit. -/
theorem cpuAusBlaettern_avx (leaf1 leaf7 : CpuOut) :
    (cpuAusBlaettern leaf1 leaf7).hatAvx = ebxAVX2 leaf7 := rfl

/-- The mapped SSE2 bit IS the observed leaf-1 bit. -/
theorem cpuAusBlaettern_sse2 (leaf1 leaf7 : CpuOut) :
    (cpuAusBlaettern leaf1 leaf7).hatSse2 = edxSSE2 leaf1 := rfl

/-- The mapped XCR0 readiness IS the three observed XCR0 bits. -/
theorem xcr0AusWort_avx (xcrLo : BitVec 32) :
    xcr0AvxBereit (xcr0AusWort xcrLo) =
      (bit32 xcrLo 0 && xcrXMM xcrLo && xcrYMM xcrLo) := rfl

/-- BRIDGE, profile to leaf: a ready tier over mapped observations
    makes the leaf gate ready, given the two silicon bits the profile
    vocabulary cannot express (leaf-1 AVX and OSXSAVE). -/
theorem avx2Bruecke_vor (leaf1 leaf7 : CpuOut) (xcrLo : BitVec 32)
    (k : KontrollBild) (b : BereitProfil)
    (havx : ecxAVX leaf1 = true) (hos : ecxOSXSAVE leaf1 = true)
    (h : avx2TierBereit (cpuAusBlaettern leaf1 leaf7)
      (xcr0AusWort xcrLo) k b = true) :
    avx2Bereit leaf1 leaf7 xcrLo = true := by
  unfold avx2TierBereit cpuAusBlaettern xcr0AusWort kontrollAvxFrei
    xcr0AvxBereit avx2Bereit avxBereit at *
  simp_all

/-- BRIDGE, leaf to profile: a ready leaf gate makes the tier over
    mapped observations ready, given the profile side's missing
    conjuncts: silicon SSE2 (the named AVX2-carries-SSE2 assumption),
    the XCR0 x87 bit, control freedom and OS vector state. -/
theorem avx2Bruecke_zurueck (leaf1 leaf7 : CpuOut) (xcrLo : BitVec 32)
    (k : KontrollBild) (b : BereitProfil)
    (hsse : edxSSE2 leaf1 = true) (hx87 : bit32 xcrLo 0 = true)
    (hk : kontrollAvxFrei k = true) (hos : b.osXmm = true)
    (h : avx2Bereit leaf1 leaf7 xcrLo = true) :
    avx2TierBereit (cpuAusBlaettern leaf1 leaf7)
      (xcr0AusWort xcrLo) k b = true := by
  unfold avx2TierBereit cpuAusBlaettern xcr0AusWort kontrollAvxFrei
    xcr0AvxBereit avx2Bereit avxBereit at *
  simp_all

/-- Witness leaves: SSE2 + XSAVE + OSXSAVE + AVX, AVX2 silicon, and
    XCR0 x87+SSE+AVX. -/
def witBlatt1 : CpuOut :=
  ⟨0, 0, BitVec.ofNat 32 (2 ^ 26 + 2 ^ 27 + 2 ^ 28),
    BitVec.ofNat 32 (2 ^ 26)⟩

/-- Witness leaf 7: EBX[5] AVX2 silicon. -/
def witBlatt7 : CpuOut :=
  ⟨0, BitVec.ofNat 32 (2 ^ 5), 0, 0⟩

/-- Witness XCR0 low word: bits 0, 1 and 2 set. -/
def witXcrLo : BitVec 32 := BitVec.ofNat 32 7

/-- BRIDGE WITNESS: the concrete leaves admit the leaf gate, and the
    mapped tier with the named profile admits too. -/
theorem avx2Bruecke_blatt_zeuge :
    avx2Bereit witBlatt1 witBlatt7 witXcrLo = true ∧
      avx2TierBereit (cpuAusBlaettern witBlatt1 witBlatt7)
        (xcr0AusWort witXcrLo) basisKontrolle vecZeugeBereit = true := by
  constructor <;> decide

/-! ## 3. The joint machine and 32-byte TSO memory forms.

  `Avx2Maschine` pairs the coherent machine (shared memory, TSO
  buffers, checked profiles) with a per-core YMM file. Well-formedness
  is the accepted `HwWf` of the machine half: YMM updates never touch
  profiles. The 32-byte forms are four 8-byte chunks (low word, high
  word of the low half, then of the high half) through the accepted
  `issueListe`/`ladeAcht` vocabulary -- thirty-two per-byte events,
  never one atomic occurrence. -/

/-- The joint machine: the coherent machine plus a per-core YMM file. -/
structure Avx2Maschine where
  hw : HwMaschine
  ymm : Nat → YmmDatei

/-- Joint well-formedness: the accepted `HwWf` of the machine half. -/
def Avx2Wf (s : Avx2Maschine) : Prop := HwWf s.hw

/-- The thirty-two canonical byte-store entries of `y` at `a`, oldest
    first: the two chunk words of the low half then of the high half.
    One flat list (like the accepted `vecEintraege`), so membership
    is constructor equations, never append surgery. -/
def ymmEintraege (a : Adresse) (y : Ymm) : List TSOEintrag :=
  [⟨addrOff a 0, wortByte (vLo y.1) 0⟩,
    ⟨addrOff a 1, wortByte (vLo y.1) 1⟩,
    ⟨addrOff a 2, wortByte (vLo y.1) 2⟩,
    ⟨addrOff a 3, wortByte (vLo y.1) 3⟩,
    ⟨addrOff a 4, wortByte (vLo y.1) 4⟩,
    ⟨addrOff a 5, wortByte (vLo y.1) 5⟩,
    ⟨addrOff a 6, wortByte (vLo y.1) 6⟩,
    ⟨addrOff a 7, wortByte (vLo y.1) 7⟩,
    ⟨addrOff (addrOff a 8) 0, wortByte (vHi y.1) 0⟩,
    ⟨addrOff (addrOff a 8) 1, wortByte (vHi y.1) 1⟩,
    ⟨addrOff (addrOff a 8) 2, wortByte (vHi y.1) 2⟩,
    ⟨addrOff (addrOff a 8) 3, wortByte (vHi y.1) 3⟩,
    ⟨addrOff (addrOff a 8) 4, wortByte (vHi y.1) 4⟩,
    ⟨addrOff (addrOff a 8) 5, wortByte (vHi y.1) 5⟩,
    ⟨addrOff (addrOff a 8) 6, wortByte (vHi y.1) 6⟩,
    ⟨addrOff (addrOff a 8) 7, wortByte (vHi y.1) 7⟩,
    ⟨addrOff (addrOff a 16) 0, wortByte (vLo y.2) 0⟩,
    ⟨addrOff (addrOff a 16) 1, wortByte (vLo y.2) 1⟩,
    ⟨addrOff (addrOff a 16) 2, wortByte (vLo y.2) 2⟩,
    ⟨addrOff (addrOff a 16) 3, wortByte (vLo y.2) 3⟩,
    ⟨addrOff (addrOff a 16) 4, wortByte (vLo y.2) 4⟩,
    ⟨addrOff (addrOff a 16) 5, wortByte (vLo y.2) 5⟩,
    ⟨addrOff (addrOff a 16) 6, wortByte (vLo y.2) 6⟩,
    ⟨addrOff (addrOff a 16) 7, wortByte (vLo y.2) 7⟩,
    ⟨addrOff (addrOff a 24) 0, wortByte (vHi y.2) 0⟩,
    ⟨addrOff (addrOff a 24) 1, wortByte (vHi y.2) 1⟩,
    ⟨addrOff (addrOff a 24) 2, wortByte (vHi y.2) 2⟩,
    ⟨addrOff (addrOff a 24) 3, wortByte (vHi y.2) 3⟩,
    ⟨addrOff (addrOff a 24) 4, wortByte (vHi y.2) 4⟩,
    ⟨addrOff (addrOff a 24) 5, wortByte (vHi y.2) 5⟩,
    ⟨addrOff (addrOff a 24) 6, wortByte (vHi y.2) 6⟩,
    ⟨addrOff (addrOff a 24) 7, wortByte (vHi y.2) 7⟩]

/-- Thirty-two entries, no more: the 256-bit shape is exact. -/
theorem ymmEintraege_laenge (a : Adresse) (y : Ymm) :
    (ymmEintraege a y).length = 32 := rfl

/-- 256-bit store issue on the TSO view: thirty-two buffered byte
    issues, never a direct memory effect. `none` = a refused byte. -/
def ymmSpeichern (s : TSOZustand) (c : Nat) (a : Adresse)
    (y : Ymm) : Option TSOZustand :=
  issueListe s c (ymmEintraege a y)

/-- AGREEMENT (Mem): the 256-bit store IS the accepted issue fold. -/
theorem ymmSpeichern_ist_issueListe (s : TSOZustand) (c : Nat)
    (a : Adresse) (y : Ymm) :
    ymmSpeichern s c a y = issueListe s c (ymmEintraege a y) := rfl

/-- A successful 256-bit issue appends exactly the entries. -/
theorem ymmSpeichern_haengt_an (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (y : Ymm) (h : ymmSpeichern s c a y = some s') :
    s'.puffer c = s.puffer c ++ ymmEintraege a y :=
  issueListe_haengt_an s s' c _ h

/-- A 256-bit issue changes no canonical byte (buffer only). -/
theorem ymmSpeichern_kein_speicher (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (y : Ymm) (h : ymmSpeichern s c a y = some s')
    (x : Adresse) :
    s'.mem.bytes x = s.mem.bytes x :=
  issueListe_kein_speicher s s' c _ h x

/-- 256-bit load on core `c`: four chunk observations through the
    accepted `ladeAcht` (forwarding per byte), joined low half then
    high half. `none` = an unreadable byte. -/
def ymmLaden (s : TSOZustand) (c : Nat) (a : Adresse) :
    Option Ymm :=
  match ladeAcht s c a, ladeAcht s c (addrOff a 8),
      ladeAcht s c (addrOff a 16), ladeAcht s c (addrOff a 24) with
  | some w0, some w8, some w16, some w24 =>
    some (vecJoin w0 w8, vecJoin w16 w24)
  | _, _, _, _ => none

/-- Every entry sits in its chunk: write permission across all four
    chunks covers every one of the thirty-two entries. -/
theorem ymmEintrag_schreibbar (m : Speicher) (a : Adresse) (y : Ymm)
    (h0 : schreibbar8 m a = true)
    (h8 : schreibbar8 m (addrOff a 8) = true)
    (h16 : schreibbar8 m (addrOff a 16) = true)
    (h24 : schreibbar8 m (addrOff a 24) = true) (e : TSOEintrag)
    (hmem : e ∈ ymmEintraege a y) :
    m.schreibbar e.addr = true := by
  unfold ymmEintraege at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact schreibbar8_einzeln m a 0 (by decide) h0
  · exact schreibbar8_einzeln m a 1 (by decide) h0
  · exact schreibbar8_einzeln m a 2 (by decide) h0
  · exact schreibbar8_einzeln m a 3 (by decide) h0
  · exact schreibbar8_einzeln m a 4 (by decide) h0
  · exact schreibbar8_einzeln m a 5 (by decide) h0
  · exact schreibbar8_einzeln m a 6 (by decide) h0
  · exact schreibbar8_einzeln m a 7 (by decide) h0
  · exact schreibbar8_einzeln m (addrOff a 8) 0 (by decide) h8
  · exact schreibbar8_einzeln m (addrOff a 8) 1 (by decide) h8
  · exact schreibbar8_einzeln m (addrOff a 8) 2 (by decide) h8
  · exact schreibbar8_einzeln m (addrOff a 8) 3 (by decide) h8
  · exact schreibbar8_einzeln m (addrOff a 8) 4 (by decide) h8
  · exact schreibbar8_einzeln m (addrOff a 8) 5 (by decide) h8
  · exact schreibbar8_einzeln m (addrOff a 8) 6 (by decide) h8
  · exact schreibbar8_einzeln m (addrOff a 8) 7 (by decide) h8
  · exact schreibbar8_einzeln m (addrOff a 16) 0 (by decide) h16
  · exact schreibbar8_einzeln m (addrOff a 16) 1 (by decide) h16
  · exact schreibbar8_einzeln m (addrOff a 16) 2 (by decide) h16
  · exact schreibbar8_einzeln m (addrOff a 16) 3 (by decide) h16
  · exact schreibbar8_einzeln m (addrOff a 16) 4 (by decide) h16
  · exact schreibbar8_einzeln m (addrOff a 16) 5 (by decide) h16
  · exact schreibbar8_einzeln m (addrOff a 16) 6 (by decide) h16
  · exact schreibbar8_einzeln m (addrOff a 16) 7 (by decide) h16
  · exact schreibbar8_einzeln m (addrOff a 24) 0 (by decide) h24
  · exact schreibbar8_einzeln m (addrOff a 24) 1 (by decide) h24
  · exact schreibbar8_einzeln m (addrOff a 24) 2 (by decide) h24
  · exact schreibbar8_einzeln m (addrOff a 24) 3 (by decide) h24
  · exact schreibbar8_einzeln m (addrOff a 24) 4 (by decide) h24
  · exact schreibbar8_einzeln m (addrOff a 24) 5 (by decide) h24
  · exact schreibbar8_einzeln m (addrOff a 24) 6 (by decide) h24
  · exact schreibbar8_einzeln m (addrOff a 24) 7 (by decide) h24

/-- Write permission across all four chunks issues the whole 256-bit
    word. Permissions survive each issue (the memory is kept), so the
    whole list goes through. -/
theorem ymmSpeichern_erfolg (s : TSOZustand) (c : Nat) (a : Adresse)
    (y : Ymm)
    (h0 : schreibbar8 s.mem a = true)
    (h8 : schreibbar8 s.mem (addrOff a 8) = true)
    (h16 : schreibbar8 s.mem (addrOff a 16) = true)
    (h24 : schreibbar8 s.mem (addrOff a 24) = true) :
    ∃ s' : TSOZustand, ymmSpeichern s c a y = some s' := by
  apply issueListe_erfolg
  intro e hmem
  exact ymmEintrag_schreibbar s.mem a y h0 h8 h16 h24 e hmem

/-! ## 4. Register evaluation: the accepted `ymm*` functions, lifted.

  `avx2RegAuswertung` runs the accepted 256-bit evaluator of
  `Avx2Ops` on the YMM file: memory rows evaluate to `none` here
  (their TSO path is §5), and the two unencodable shift widths
  (`.b8` logical, `.b64` arithmetic -- Avx2Ops §3) refuse. -/

/-- Register evaluation over a YMM file: the accepted `ymm*`
    evaluator per row, `none` for memory rows and unencodable shifts. -/
def avx2RegAuswertung (op : Avx2Op) (f : YmmDatei) : Option Ymm :=
  match op with
  | .vpaddRR b _ a e => some (ymmAdd b (f a) (f e))
  | .vpsubRR b _ a e => some (ymmSub b (f a) (f e))
  | .vpandRR _ a e => some (ymmAnd .b64 (f a) (f e))
  | .vporRR _ a e => some (ymmOr .b64 (f a) (f e))
  | .vpxorRR _ a e => some (ymmXor .b64 (f a) (f e))
  | .vpandnRR _ a e => some (ymmAndn .b64 (f a) (f e))
  | .vpcmpeqRR b _ a e => some (ymmCmpeq b (f a) (f e))
  | .vpsllImm .b8 _ _ _ => none
  | .vpsllImm b _ a imm => some (ymmSll b (f a) imm)
  | .vpsrlImm .b8 _ _ _ => none
  | .vpsrlImm b _ a imm => some (ymmSrl b (f a) imm)
  | .vpsraImm .b8 _ _ _ => none
  | .vpsraImm .b64 _ _ _ => none
  | .vpsraImm b _ a imm => some (ymmSra b (f a) imm)
  | _ => none

/-- AGREEMENT: `vpaddRR` IS the accepted 256-bit add. -/
theorem avx2Auswertung_add (b : Breite) (d a e : YmmReg)
    (f : YmmDatei) :
    avx2RegAuswertung (.vpaddRR b d a e) f =
      some (ymmAdd b (f a) (f e)) := rfl

/-- AGREEMENT: `vpsubRR` IS the accepted 256-bit sub. -/
theorem avx2Auswertung_sub (b : Breite) (d a e : YmmReg)
    (f : YmmDatei) :
    avx2RegAuswertung (.vpsubRR b d a e) f =
      some (ymmSub b (f a) (f e)) := rfl

/-- AGREEMENT: `vpandRR` IS the accepted 256-bit and. -/
theorem avx2Auswertung_and (d a e : YmmReg) (f : YmmDatei) :
    avx2RegAuswertung (.vpandRR d a e) f =
      some (ymmAnd .b64 (f a) (f e)) := rfl

/-- AGREEMENT: `vporRR` IS the accepted 256-bit or. -/
theorem avx2Auswertung_or (d a e : YmmReg) (f : YmmDatei) :
    avx2RegAuswertung (.vporRR d a e) f =
      some (ymmOr .b64 (f a) (f e)) := rfl

/-- AGREEMENT: `vpxorRR` IS the accepted 256-bit xor. -/
theorem avx2Auswertung_xor (d a e : YmmReg) (f : YmmDatei) :
    avx2RegAuswertung (.vpxorRR d a e) f =
      some (ymmXor .b64 (f a) (f e)) := rfl

/-- AGREEMENT: `vpandnRR` IS the accepted 256-bit andn. -/
theorem avx2Auswertung_andn (d a e : YmmReg) (f : YmmDatei) :
    avx2RegAuswertung (.vpandnRR d a e) f =
      some (ymmAndn .b64 (f a) (f e)) := rfl

/-- AGREEMENT: `vpcmpeqRR` IS the accepted 256-bit compare. -/
theorem avx2Auswertung_cmpeq (b : Breite) (d a e : YmmReg)
    (f : YmmDatei) :
    avx2RegAuswertung (.vpcmpeqRR b d a e) f =
      some (ymmCmpeq b (f a) (f e)) := rfl

/-- AGREEMENT: admitted logical shifts ARE the accepted shifts. -/
theorem avx2Auswertung_sll (b : Breite) (d a : YmmReg) (imm : Nat)
    (f : YmmDatei) (hb : b ≠ .b8) :
    avx2RegAuswertung (.vpsllImm b d a imm) f =
      some (ymmSll b (f a) imm) := by
  cases b <;> simp_all [avx2RegAuswertung]

/-- AGREEMENT: admitted logical right shifts ARE the accepted ones. -/
theorem avx2Auswertung_srl (b : Breite) (d a : YmmReg) (imm : Nat)
    (f : YmmDatei) (hb : b ≠ .b8) :
    avx2RegAuswertung (.vpsrlImm b d a imm) f =
      some (ymmSrl b (f a) imm) := by
  cases b <;> simp_all [avx2RegAuswertung]

/-- AGREEMENT: the admitted arithmetic shift IS the accepted one
    (W/D only: no `.b8`, no `.b64`). -/
theorem avx2Auswertung_sra (b : Breite) (d a : YmmReg) (imm : Nat)
    (f : YmmDatei) (hb8 : b ≠ .b8) (hb64 : b ≠ .b64) :
    avx2RegAuswertung (.vpsraImm b d a imm) f =
      some (ymmSra b (f a) imm) := by
  cases b <;> simp_all [avx2RegAuswertung]

/-- REFUSAL: no byte-shift encoding exists (Avx2Ops §3). -/
theorem avx2Auswertung_sll_b8 (d a : YmmReg) (imm : Nat)
    (f : YmmDatei) :
    avx2RegAuswertung (.vpsllImm .b8 d a imm) f = none := rfl

/-- REFUSAL: no byte-shift encoding exists. -/
theorem avx2Auswertung_srl_b8 (d a : YmmReg) (imm : Nat)
    (f : YmmDatei) :
    avx2RegAuswertung (.vpsrlImm .b8 d a imm) f = none := rfl

/-- REFUSAL: VPSRAQ is EVEX-only, never VEX (Avx2Ops §3). -/
theorem avx2Auswertung_sra_b64 (d a : YmmReg) (imm : Nat)
    (f : YmmDatei) :
    avx2RegAuswertung (.vpsraImm .b64 d a imm) f = none := rfl

/-- REFUSAL: memory rows never evaluate on the register path. -/
theorem avx2Auswertung_speicher (dst : YmmReg) (base : Register)
    (disp : BitVec 8) (f : YmmDatei) :
    avx2RegAuswertung (.vmovdquLd dst base disp) f = none ∧
      avx2RegAuswertung (.vmovdquSt base dst disp) f = none ∧
      avx2RegAuswertung (.vmovdqaLd dst base disp) f = none ∧
      avx2RegAuswertung (.vmovdqaSt base dst disp) f = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 5. Machine steps: gated register rows and TSO memory rows.

  Register rows ride the accepted evaluator over the joint state
  under the tier gate; memory rows go through the §3 TSO forms at the
  base-plus-disp8 effective address. The aligned (`vmovdqa`) shape
  faults #GP off the 32-byte boundary (named silicon assumption:
  VEX.256 aligned accesses check 32 bytes); the unaligned shape never
  faults on alignment. Disp8 is zero-extended (sign extension stays
  open; the witness uses disp 0 where both agree). -/

/-- The two 256-bit memory shapes: aligned (VMOVDQA) and unaligned
    (VMOVDQU). -/
inductive YmmSpeicherForm where
  | ausgerichtet
  | unausgerichtet
  deriving DecidableEq, Repr

/-- #GP fault predicate: the aligned form faults exactly off the
    32-byte boundary; the unaligned form never faults on alignment. -/
def ymmGpFehler (a : Adresse) : YmmSpeicherForm → Bool
  | .ausgerichtet => decide (a.toNat % 32 ≠ 0)
  | .unausgerichtet => false

/-- The unaligned form never faults on alignment, at any address. -/
theorem ymmGp_nie_unausgerichtet (a : Adresse) :
    ymmGpFehler a .unausgerichtet = false := rfl

/-- The aligned form faults sixteen bytes past a 32-byte boundary. -/
theorem ymmGp_ausgerichtet_fehler :
    ymmGpFehler (BitVec.ofNat 64 16) .ausgerichtet = true := by
  decide

/-- The aligned form is clean at the boundary and one line further. -/
theorem ymmGp_ausgerichtet_ok :
    ymmGpFehler (BitVec.ofNat 64 0) .ausgerichtet = false ∧
      ymmGpFehler (BitVec.ofNat 64 32) .ausgerichtet = false := by
  exact ⟨by decide, by decide⟩

/-- Effective address of a memory row: the machine GPR plus the
    zero-extended disp8. -/
def avx2Addr (s : Avx2Maschine) (c : Nat) (base : Register)
    (disp : BitVec 8) : Adresse :=
  effAddr (projZustand s.hw c) base (BitVec.ofNat 32 disp.toNat)

/-- Joint successor after a register row: RIP past `len` on the
    machine half (memory and buffers kept), `dst` holding `v` on the
    acting YMM file, every other core's file kept. -/
def avx2SetReg (s : Avx2Maschine) (c : Nat) (len : Nat)
    (dst : YmmReg) (v : Ymm) : Avx2Maschine :=
  let t := projFp s.hw c
  let t' : FpZustand :=
    { t with kern := { t.kern with rip := ripNach t.kern.rip len } }
  ⟨setKernVonFp s.hw c t',
    fun d => if d = c then ymmSet (s.ymm c) dst v else s.ymm d⟩

/-- A register successor keeps shared memory. -/
theorem avx2SetReg_speicher (s : Avx2Maschine) (c : Nat) (len : Nat)
    (dst : YmmReg) (v : Ymm) :
    (avx2SetReg s c len dst v).hw.mem = s.hw.mem := rfl

/-- A register successor keeps all buffers. -/
theorem avx2SetReg_puffer (s : Avx2Maschine) (c : Nat) (len : Nat)
    (dst : YmmReg) (v : Ymm) (d : Nat) :
    (avx2SetReg s c len dst v).hw.puffer d = s.hw.puffer d := rfl

/-- A register successor writes the destination on the acting core. -/
theorem avx2SetReg_ymm (s : Avx2Maschine) (c : Nat) (len : Nat)
    (dst : YmmReg) (v : Ymm) :
    (avx2SetReg s c len dst v).ymm c dst = v := by
  unfold avx2SetReg
  simp [ymmSet_gleich]

/-- Destination register of a row: register rows name one, memory
    rows name none. -/
def avx2Dst : Avx2Op → Option YmmReg
  | .vpaddRR _ dst _ _ => some dst
  | .vpsubRR _ dst _ _ => some dst
  | .vpandRR dst _ _ => some dst
  | .vporRR dst _ _ => some dst
  | .vpxorRR dst _ _ => some dst
  | .vpandnRR dst _ _ => some dst
  | .vpcmpeqRR _ dst _ _ => some dst
  | .vpsllImm _ dst _ _ => some dst
  | .vpsrlImm _ dst _ _ => some dst
  | .vpsraImm _ dst _ _ => some dst
  | _ => none

/-- A row names a destination exactly on the register path. -/
theorem avx2Dst_ist_register (op : Avx2Op) :
    (avx2Dst op).isSome = istAvx2RegisterOp op := by
  cases op <;> rfl

/-- Register step on the joint machine: the tier gate, the decode
    length, the register shape, then the accepted evaluator with the
    row's destination. `none` is a refused gate, a bad length, a
    memory row, or a failed evaluation. -/
def avx2RegSchritt (s : Avx2Maschine) (c : Nat) (cpu : CpuMerkmal)
    (x : Xcr0Bild) (k : KontrollBild) (z : Avx2Zeile) :
    Option Avx2Maschine :=
  if avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k then
    if laengeOk z.laenge then
      if istAvx2RegisterOp z.op then
        match avx2RegAuswertung z.op (s.ymm c), avx2Dst z.op with
        | some v, some dst => some (avx2SetReg s c z.laenge dst v)
        | _, _ => none
      else none
    else none
  else none

/-- A register plug success with checked gates IS the joint successor:
    the equation over the machine state (lifted, never redefined). -/
theorem avx2RegSchritt_gleich (s : Avx2Maschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (z : Avx2Zeile) (dst : YmmReg) (v : Ymm)
    (hgate : avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k = true)
    (hok : laengeOk z.laenge = true)
    (hreg : istAvx2RegisterOp z.op = true)
    (hs : avx2RegAuswertung z.op (s.ymm c) = some v)
    (hdst : avx2Dst z.op = some dst) :
    avx2RegSchritt s c cpu x k z =
      some (avx2SetReg s c z.laenge dst v) := by
  unfold avx2RegSchritt
  rw [if_pos hgate, if_pos hok, if_pos hreg, hs, hdst]

/-- Machine 256-bit load: gates (length, tier admission, `#GP`
    alignment for the `vmovdqa` shape) then thirty-two TSO byte
    observations with forwarding; the destination YMM holds the
    observed word and RIP advances. Memory and buffers are kept. -/
def avx2LadeSchritt (s : Avx2Maschine) (c : Nat) (cpu : CpuMerkmal)
    (x : Xcr0Bild) (k : KontrollBild) (z : Avx2Zeile) :
    Option Avx2Maschine :=
  match z.op with
  | .vmovdqaLd dst base disp =>
    match laengeOk z.laenge,
        avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k with
    | true, true =>
      if ymmGpFehler (avx2Addr s c base disp) .ausgerichtet then none
      else
        match ymmLaden (tsoAnsicht s.hw) c (avx2Addr s c base disp) with
        | some v => some (avx2SetReg s c z.laenge dst v)
        | none => none
    | _, _ => none
  | .vmovdquLd dst base disp =>
    match laengeOk z.laenge,
        avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k with
    | true, true =>
      match ymmLaden (tsoAnsicht s.hw) c (avx2Addr s c base disp) with
      | some v => some (avx2SetReg s c z.laenge dst v)
      | none => none
    | _, _ => none
  | _ => none

/-- Machine 256-bit store: gates (length, tier admission, `#GP`
    alignment for the `vmovdqa` shape) then thirty-two buffered TSO
    byte issues of the source YMM word. Canonical memory is unchanged
    (buffer only). -/
def avx2SpeicherSchritt (s : Avx2Maschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (z : Avx2Zeile) : Option Avx2Maschine :=
  match z.op with
  | .vmovdqaSt base src disp =>
    match laengeOk z.laenge,
        avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k with
    | true, true =>
      if ymmGpFehler (avx2Addr s c base disp) .ausgerichtet then none
      else
        match ymmSpeichern (tsoAnsicht s.hw) c
            (avx2Addr s c base disp) (s.ymm c src) with
        | some s' => some ⟨setTso s.hw s', s.ymm⟩
        | none => none
    | _, _ => none
  | .vmovdquSt base src disp =>
    match laengeOk z.laenge,
        avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k with
    | true, true =>
      match ymmSpeichern (tsoAnsicht s.hw) c
          (avx2Addr s c base disp) (s.ymm c src) with
      | some s' => some ⟨setTso s.hw s', s.ymm⟩
      | none => none
    | _, _ => none
  | _ => none

/-! ## 6. Events, the extended step relation, and its laws.

  The family's event type carries the checked CPU/XCR0/control
  inputs, so every step checks them, never assuming them. The
  extended relation embeds `HwSchritt` exactly (`alt`, with YMM files
  kept and projection back) and adds gated register rows plus the
  four TSO memory rows. A bare `HwAdapter` over `HwMaschine` is NOT
  instantiated: it could not carry the YMM file (`HwKern` has no YMM
  slot), so the adapter-shaped plug would drop destination state;
  the extended relation is the mechanism's allowed alternative. -/

/-- AVX2 family events on the joint machine: register execution, TSO
    loads/stores of whole 256-bit words, the old machine events, and
    explicit refusal. -/
inductive Avx2Ereignis where
  | hwAlt : HwEreignis → Avx2Ereignis
  | avxReg : Nat → CpuMerkmal → Xcr0Bild → KontrollBild → Avx2Zeile →
      Avx2Ereignis
  | avxLade : Nat → CpuMerkmal → Xcr0Bild → KontrollBild → Avx2Zeile →
      Avx2Ereignis
  | avxSpeichere : Nat → CpuMerkmal → Xcr0Bild → KontrollBild →
      Avx2Zeile → Avx2Ereignis
  | verweigert : Nat → Avx2Ereignis
  deriving DecidableEq, Repr

/-- The extended step relation: the old coherent steps exactly
    (`alt`, YMM files kept), gated register rows over the accepted
    evaluator (`reg`), TSO loads (`ladeA`/`ladeU`) and stores
    (`speichereA`/`speichereU`), plus explicit refusal (`still`). -/
inductive Avx2Schritt : Avx2Maschine → Avx2Maschine → Avx2Ereignis →
    Prop where
  | alt {s s' : Avx2Maschine} {e : HwEreignis}
      (h : HwSchritt s.hw s'.hw e) (hymm : s'.ymm = s.ymm) :
      Avx2Schritt s s' (.hwAlt e)
  | reg {s : Avx2Maschine} {c : Nat} {cpu : CpuMerkmal}
      {x : Xcr0Bild} {k : KontrollBild} {z : Avx2Zeile}
      {dst : YmmReg} {v : Ymm}
      (hreg : istAvx2RegisterOp z.op = true)
      (hok : laengeOk z.laenge = true)
      (hgate : avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k
        = true)
      (hstep : avx2RegAuswertung z.op (s.ymm c) = some v)
      (hdst : avx2Dst z.op = some dst) :
      Avx2Schritt s (avx2SetReg s c z.laenge dst v)
        (.avxReg c cpu x k z)
  | ladeA {s : Avx2Maschine} {c : Nat} {cpu : CpuMerkmal}
      {x : Xcr0Bild} {k : KontrollBild} {z : Avx2Zeile}
      {dst : YmmReg} {base : Register} {disp : BitVec 8} {v : Ymm}
      (hop : z.op = .vmovdqaLd dst base disp)
      (hok : laengeOk z.laenge = true)
      (hgate : avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k
        = true)
      (hgp : ymmGpFehler (avx2Addr s c base disp) .ausgerichtet
        = false)
      (hread : ymmLaden (tsoAnsicht s.hw) c (avx2Addr s c base disp)
        = some v) :
      Avx2Schritt s (avx2SetReg s c z.laenge dst v)
        (.avxLade c cpu x k z)
  | ladeU {s : Avx2Maschine} {c : Nat} {cpu : CpuMerkmal}
      {x : Xcr0Bild} {k : KontrollBild} {z : Avx2Zeile}
      {dst : YmmReg} {base : Register} {disp : BitVec 8} {v : Ymm}
      (hop : z.op = .vmovdquLd dst base disp)
      (hok : laengeOk z.laenge = true)
      (hgate : avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k
        = true)
      (hread : ymmLaden (tsoAnsicht s.hw) c (avx2Addr s c base disp)
        = some v) :
      Avx2Schritt s (avx2SetReg s c z.laenge dst v)
        (.avxLade c cpu x k z)
  | speichereA {s : Avx2Maschine} {c : Nat} {cpu : CpuMerkmal}
      {x : Xcr0Bild} {k : KontrollBild} {z : Avx2Zeile}
      {base : Register} {src : YmmReg} {disp : BitVec 8}
      {s' : TSOZustand}
      (hop : z.op = .vmovdqaSt base src disp)
      (hok : laengeOk z.laenge = true)
      (hgate : avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k
        = true)
      (hgp : ymmGpFehler (avx2Addr s c base disp) .ausgerichtet
        = false)
      (hwr : ymmSpeichern (tsoAnsicht s.hw) c
        (avx2Addr s c base disp) (s.ymm c src) = some s') :
      Avx2Schritt s ⟨setTso s.hw s', s.ymm⟩
        (.avxSpeichere c cpu x k z)
  | speichereU {s : Avx2Maschine} {c : Nat} {cpu : CpuMerkmal}
      {x : Xcr0Bild} {k : KontrollBild} {z : Avx2Zeile}
      {base : Register} {src : YmmReg} {disp : BitVec 8}
      {s' : TSOZustand}
      (hop : z.op = .vmovdquSt base src disp)
      (hok : laengeOk z.laenge = true)
      (hgate : avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k
        = true)
      (hwr : ymmSpeichern (tsoAnsicht s.hw) c
        (avx2Addr s c base disp) (s.ymm c src) = some s') :
      Avx2Schritt s ⟨setTso s.hw s', s.ymm⟩
        (.avxSpeichere c cpu x k z)
  | still {s : Avx2Maschine} {c : Nat} :
      Avx2Schritt s s (.verweigert c)

/-- Every extended step preserves well-formedness: core-data, YMM and
    memory/buffer updates alike leave the checked profiles untouched. -/
theorem avx2Schritt_wf (s s' : Avx2Maschine) (e : Avx2Ereignis)
    (h : Avx2Schritt s s' e) (hwf : Avx2Wf s) : Avx2Wf s' := by
  cases h with
  | alt h hymm => exact hwSchritt_wf _ _ _ h hwf
  | reg hreg hok hgate hstep hdst => exact hwf
  | ladeA hop hok hgate hgp hread => exact hwf
  | ladeU hop hok hgate hread => exact hwf
  | speichereA hop hok hgate hgp hwr => exact hwf
  | speichereU hop hok hgate hwr => exact hwf
  | still => exact hwf

/-- Exact embedding: every old coherent step is an extended step with
    kept YMM files. -/
theorem avx2Schritt_einbettet (m m' : HwMaschine) (f : Nat → YmmDatei)
    (e : HwEreignis) (h : HwSchritt m m' e) :
    Avx2Schritt ⟨m, f⟩ ⟨m', f⟩ (.hwAlt e) :=
  .alt h rfl

/-- Exact projection: an embedded step is the old step back with kept
    YMM files. -/
theorem avx2Schritt_projiziert (s s' : Avx2Maschine)
    (e : HwEreignis) (h : Avx2Schritt s s' (.hwAlt e)) :
    HwSchritt s.hw s'.hw e ∧ s'.ymm = s.ymm := by
  cases h with
  | alt h hymm => exact ⟨h, hymm⟩

/-! ## 7. Refusals: what is not admitted.

  An absent gate is a #UD-class refusal (`none`), never a silent
  fallback; a mismatched core is refused, never rerouted; a memory
  row on the register path (and vice versa) refuses; the aligned
  shape off its boundary refuses. -/

/-- REFUSAL: no gate, no register step (absent gate = #UD outcome). -/
theorem avx2Reg_ohne_gate (s : Avx2Maschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (z : Avx2Zeile)
    (h : avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k = false) :
    avx2RegSchritt s c cpu x k z = none := by
  unfold avx2RegSchritt
  simp [h]

/-- REFUSAL: no gate, no load. -/
theorem avx2Lade_ohne_gate (s : Avx2Maschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (z : Avx2Zeile) (dst : YmmReg) (base : Register)
    (disp : BitVec 8)
    (hop : z.op = .vmovdquLd dst base disp)
    (hok : laengeOk z.laenge = true)
    (h : avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k = false) :
    avx2LadeSchritt s c cpu x k z = none := by
  unfold avx2LadeSchritt
  simp [hop, hok, h]

/-- REFUSAL: no gate, no store. -/
theorem avx2Speichere_ohne_gate (s : Avx2Maschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (z : Avx2Zeile) (base : Register) (src : YmmReg)
    (disp : BitVec 8)
    (hop : z.op = .vmovdquSt base src disp)
    (hok : laengeOk z.laenge = true)
    (h : avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k = false) :
    avx2SpeicherSchritt s c cpu x k z = none := by
  unfold avx2SpeicherSchritt
  simp [hop, hok, h]

/-- REFUSAL: a memory row never steps on the register path. -/
theorem avx2Reg_speicher_verweigert (s : Avx2Maschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (z : Avx2Zeile) (dst : YmmReg) (base : Register)
    (disp : BitVec 8)
    (hop : z.op = .vmovdquLd dst base disp)
    (hgate : avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k = true)
    (hok : laengeOk z.laenge = true) :
    avx2RegSchritt s c cpu x k z = none := by
  have hreg : istAvx2RegisterOp (.vmovdquLd dst base disp) = false := by
    simp [istAvx2RegisterOp]
  unfold avx2RegSchritt
  rw [hop, if_pos hgate, if_pos hok, if_neg (by simp [hreg])]

/-- REFUSAL: a register row never steps on the memory paths. -/
theorem avx2Speichere_register_verweigert (s : Avx2Maschine)
    (c : Nat) (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (z : Avx2Zeile) (b : Breite) (d a e : YmmReg)
    (hop : z.op = .vpaddRR b d a e) :
    avx2SpeicherSchritt s c cpu x k z = none ∧
      avx2LadeSchritt s c cpu x k z = none := by
  constructor
  · unfold avx2SpeicherSchritt
    simp [hop]
  · unfold avx2LadeSchritt
    simp [hop]

/-- REFUSAL: the aligned store off its 32-byte boundary faults. -/
theorem avx2SpeichereA_fehl_ausgerichtet (s : Avx2Maschine)
    (c : Nat) (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (z : Avx2Zeile) (base : Register) (src : YmmReg)
    (disp : BitVec 8)
    (hop : z.op = .vmovdqaSt base src disp)
    (hok : laengeOk z.laenge = true)
    (hgate : avx2TierZugelassen s.hw.hw (s.hw.bereit c) cpu x k = true)
    (hgp : ymmGpFehler (avx2Addr s c base disp) .ausgerichtet = true) :
    avx2SpeicherSchritt s c cpu x k z = none := by
  unfold avx2SpeicherSchritt
  simp [hop, hok, hgate, hgp]

/-- The old 128-bit path still refuses every 256-bit row: the legacy
    `stufe_avx256_verweigert` beside the new gate (cross-check, reused). -/
theorem avx256_alte_gate_verweigert (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) :
    stufenZugelassenHw hw b cpu x k .avx256 = false :=
  stufe_avx256_verweigert hw b cpu x k

/-! ## 8. Witness: a reached two-core run with a memory-changing
  32-byte store.

  Core 0 adds two 256-bit words (`vpaddb`: lane 0 wraps `0xFF + 2`
  with no carry out), stores the sum through thirty-two buffered TSO
  byte issues (canonical memory unchanged), observes its own byte
  through forwarding while core 1 still observes the old byte, then
  one flush visibly changes shared memory. Beside it: the gate, the
  misaligned `#GP`, the VEX.128 and the unencodable-shift refusals. -/

/-- Witness data address: 32-byte aligned. -/
def avxWitAdr : Adresse := BitVec.ofNat 64 8192

/-- Witness bytes: `7` at the base, zeroes elsewhere. -/
def avxWitBytes (a : Adresse) : Byte :=
  if a.toNat = 8192 then BitVec.ofNat 8 7 else BitVec.ofNat 8 0

/-- Witness data permission: thirty-two bytes at 8192. -/
def avxWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8192 + 32)

/-- Witness shared memory: data read/write, nothing executable
    (nothing is fetched here). -/
def avxWitMem : Speicher :=
  { bytes := avxWitBytes, lesbar := avxWitDaten,
    schreibbar := avxWitDaten, ausfuehrbar := fun _ => false }

/-- Witness packed operand: low byte `0xFF`, lane 1 `0x01`. -/
def avxWitA : Ymm :=
  (BitVec.ofNat 128 0x010101010101010101010101010101FF,
    BitVec.ofNat 128 0)

/-- Witness packed operand: low byte `0x02`, lane 1 `0x01`. -/
def avxWitB : Ymm :=
  (BitVec.ofNat 128 0x0F0E0D0C0B0A09080706050403020102,
    BitVec.ofNat 128 0)

/-- The stored 256-bit word: the accepted byte-lane sum. -/
def avxWitS : Ymm := ymmAdd .b8 avxWitA avxWitB

/-- Witness core-0 registers: data address in rax. -/
def avxWitReg0 : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 8192
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Witness core-0 YMM: the operands in ymm1/ymm2. -/
def avxWitYmm0 : YmmDatei := fun q =>
  if q = .ymm1 then avxWitA
  else if q = .ymm2 then avxWitB
  else ((BitVec.ofNat 128 0, BitVec.ofNat 128 0) : Ymm)

/-- Witness core data: core 0 runs at 4096, core 1 idles. -/
def avxWitKern : Nat → HwKern
  | 0 => ⟨avxWitReg0, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0,
      kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon with OS vector state, operand YMM files. -/
def avxWitS0 : Avx2Maschine :=
  ⟨⟨avxWitMem, avxWitKern, fun _ => [], basisHw,
    fun _ => vecZeugeBereit⟩, fun _ => avxWitYmm0⟩

/-- The decoded add row: `vpaddb` over five bytes. -/
def avxWitZAdd : Avx2Zeile := ⟨.vpaddRR .b8 .ymm0 .ymm1 .ymm2, 5⟩

/-- The decoded store row: `vmovdqu` store over six bytes. -/
def avxWitZSt : Avx2Zeile := ⟨.vmovdquSt .rax .ymm0 0x00, 6⟩

/-- The explicit machine successor after the `vpaddb`. -/
def avxWitS1 : Avx2Maschine := avx2SetReg avxWitS0 0 5 .ymm0 avxWitS

/-- The tier gate admits at the witness profiles. -/
theorem avxWit_gate :
    avx2TierZugelassen avxWitS0.hw.hw (avxWitS0.hw.bereit 0)
      avx2Cpu avx2Xcr0 basisKontrolle = true :=
  avx2Tier_basis_zugelassen

/-- The witness machine is well-formed: full silicon admits all. -/
theorem avxWitS0_wf : Avx2Wf avxWitS0 := by
  intro c f h
  cases f <;> rfl

/-- The witness successor is well-formed: profiles are untouched. -/
theorem avxWitS1_wf : Avx2Wf avxWitS1 := avxWitS0_wf

/-- The accepted `vpaddb` equation reaches the explicit successor. -/
theorem avxWit_paddb :
    avx2RegAuswertung avxWitZAdd.op (avxWitS0.ymm 0) = some avxWitS :=
  avx2Auswertung_add .b8 .ymm0 .ymm1 .ymm2 _

/-- The plug reaches the explicit machine successor. -/
theorem avxWit_plug :
    avx2RegSchritt avxWitS0 0 avx2Cpu avx2Xcr0 basisKontrolle
      avxWitZAdd = some avxWitS1 :=
  avx2RegSchritt_gleich avxWitS0 0 avx2Cpu avx2Xcr0 basisKontrolle
    avxWitZAdd .ymm0 avxWitS avxWit_gate (by decide) rfl
    avxWit_paddb rfl

/-- First joint step: the register plug on core 0. -/
theorem avxWit_reg :
    Avx2Schritt avxWitS0 avxWitS1
      (.avxReg 0 avx2Cpu avx2Xcr0 basisKontrolle avxWitZAdd) :=
  .reg rfl (by decide) avxWit_gate avxWit_paddb rfl

/-- The store address computes: rax plus zero disp is the base. -/
theorem avxWit_eff :
    avx2Addr avxWitS1 0 .rax 0x00 = avxWitAdr := by
  decide

/-- The stored YMM value is the accepted sum. -/
theorem avxWit_ymm :
    avxWitS1.ymm 0 .ymm0 = avxWitS :=
  avx2SetReg_ymm avxWitS0 0 5 .ymm0 avxWitS

/-- The explicit TSO state after the thirty-two issues: shared memory
    kept, acting buffer carrying exactly the thirty-two entries. -/
def avxWitT2 : TSOZustand :=
  ⟨avxWitMem, fun d =>
    if d = 0 then ymmEintraege avxWitAdr avxWitS else []⟩

/-- The explicit machine successor after the store. -/
def avxWitS2 : Avx2Maschine :=
  ⟨setTso avxWitS1.hw avxWitT2, avxWitS1.ymm⟩

/-- The thirty-two issues compute as claimed: shared memory kept,
    acting buffer carrying exactly the entries. The folded buffer is
    extensionally (not definitionally) the stipulated one, so this
    goes through the fold lemmas. -/
theorem avxWit_issue :
    ymmSpeichern (tsoAnsicht avxWitS1.hw) 0 avxWitAdr avxWitS =
      some avxWitT2 := by
  have hperm0 : schreibbar8 (tsoAnsicht avxWitS1.hw).mem avxWitAdr =
      true := by
    decide
  have hperm8 : schreibbar8 (tsoAnsicht avxWitS1.hw).mem
      (addrOff avxWitAdr 8) = true := by
    decide
  have hperm16 : schreibbar8 (tsoAnsicht avxWitS1.hw).mem
      (addrOff avxWitAdr 16) = true := by
    decide
  have hperm24 : schreibbar8 (tsoAnsicht avxWitS1.hw).mem
      (addrOff avxWitAdr 24) = true := by
    decide
  obtain ⟨s', hs'⟩ := ymmSpeichern_erfolg (tsoAnsicht avxWitS1.hw) 0
    avxWitAdr avxWitS hperm0 hperm8 hperm16 hperm24
  have hbuf0 : s'.puffer 0 = ymmEintraege avxWitAdr avxWitS := by
    have ha := ymmSpeichern_haengt_an _ s' 0 _ _ hs'
    have hempty : (tsoAnsicht avxWitS1.hw).puffer 0 = [] := rfl
    rw [hempty] at ha
    exact ha
  have hbufd : ∀ d : Nat, d ≠ 0 → s'.puffer d = [] := by
    intro d hd
    have ha := issueListe_anderer_kern _ s' 0 _ d hd hs'
    have hempty : (tsoAnsicht avxWitS1.hw).puffer d = [] := rfl
    rw [hempty] at ha
    exact ha
  have hpuff : s'.puffer = avxWitT2.puffer := by
    funext d
    show s'.puffer d =
      (if d = 0 then ymmEintraege avxWitAdr avxWitS else [])
    by_cases hd : d = 0
    · subst hd
      rw [if_pos rfl]
      exact hbuf0
    · rw [if_neg hd]
      exact hbufd d hd
  have hmemM : s'.mem = avxWitMem := by
    have hm := issueListe_mem _ s' 0 _ hs'
    have hme : (tsoAnsicht avxWitS1.hw).mem = avxWitMem := rfl
    rw [hm]
    exact hme
  have hsurj : s' = ⟨s'.mem, s'.puffer⟩ := rfl
  rw [hs', hsurj, hmemM, hpuff]
  rfl

/-- The legacy gate still admits over the successor: profiles are
    untouched by core-data updates. -/
theorem avxWit_gate_s1 :
    avx2TierZugelassen avxWitS1.hw.hw (avxWitS1.hw.bereit 0)
      avx2Cpu avx2Xcr0 basisKontrolle = true :=
  avxWit_gate

/-- The plug reaches the explicit store successor. -/
theorem avxWit_plug_s2 :
    avx2SpeicherSchritt avxWitS1 0 avx2Cpu avx2Xcr0 basisKontrolle
      avxWitZSt = some avxWitS2 := by
  have hop : avxWitZSt.op = .vmovdquSt .rax .ymm0 0x00 := rfl
  unfold avx2SpeicherSchritt
  simp only [hop, avxWit_gate_s1]
  have heff := avxWit_eff
  have hymm := avxWit_ymm
  rw [heff, hymm]
  have hi := avxWit_issue
  rw [hi]
  rfl

/-- Second joint step: the TSO store on core 0. -/
theorem avxWit_speichere :
    Avx2Schritt avxWitS1 avxWitS2
      (.avxSpeichere 0 avx2Cpu avx2Xcr0 basisKontrolle avxWitZSt) :=
  .speichereU rfl (by decide) avxWit_gate_s1 avxWit_issue

/-- Step one advances RIP past the 5-byte row. -/
theorem avxWit_r1_rip :
    ((avx2RegSchritt avxWitS0 0 avx2Cpu avx2Xcr0 basisKontrolle
      avxWitZAdd).map fun m => (m.hw.kerne 0).rip) =
      some (BitVec.ofNat 64 4101) := by
  decide

/-- Step one wraps lane 0 (`0xFF + 0x02` to `0x01`): no carry out. -/
theorem avxWit_r1_lane0 :
    ((avx2RegSchritt avxWitS0 0 avx2Cpu avx2Xcr0 basisKontrolle
      avxWitZAdd).map fun m => laneNat .b8 (m.ymm 0 .ymm0).1 0) =
      some 1 := by
  decide

/-- Step one adds lane 1 independently (`0x01 + 0x01`): no carry in. -/
theorem avxWit_r1_lane1 :
    ((avx2RegSchritt avxWitS0 0 avx2Cpu avx2Xcr0 basisKontrolle
      avxWitZAdd).map fun m => laneNat .b8 (m.ymm 0 .ymm0).1 1) =
      some 2 := by
  decide

/-- The store issues exactly thirty-two buffer entries. -/
theorem avxWit_s2_buflen :
    ((avx2SpeicherSchritt avxWitS1 0 avx2Cpu avx2Xcr0 basisKontrolle
      avxWitZSt).map fun m => (m.hw.puffer 0).length) = some 32 := by
  decide

/-- The store changes no canonical byte (buffer only): the old `7`
    stands. -/
theorem avxWit_s2_mem_still :
    ((avx2SpeicherSchritt avxWitS1 0 avx2Cpu avx2Xcr0 basisKontrolle
      avxWitZSt).map fun m => m.hw.mem.bytes avxWitAdr) =
      some (BitVec.ofNat 8 7) := by
  decide

/-- Owner-only forwarding: core 0 observes its buffered byte `1`. -/
theorem avxWit_eigen :
    loadByte (tsoAnsicht avxWitS2.hw) 0 avxWitAdr =
      some (BitVec.ofNat 8 1) := by
  decide

/-- Foreign observation: core 1 still observes the old byte `7`. -/
theorem avxWit_fremd :
    loadByte (tsoAnsicht avxWitS2.hw) 1 avxWitAdr =
      some (BitVec.ofNat 8 7) := by
  decide

/-- The full-word load over the buffered store reads back the stored
    word: every one of the thirty-two bytes forwards. -/
theorem avxWit_ymm_lade :
    ymmLaden (tsoAnsicht avxWitS2.hw) 0 avxWitAdr = some avxWitS := by
  decide

/-- One flush visibly changes shared memory (`7` becomes `1`). -/
theorem avxWit_spuelung :
    ((flushKern (tsoAnsicht avxWitS2.hw) 0).map fun s' =>
      s'.mem.bytes avxWitAdr) = some (BitVec.ofNat 8 1) := by
  decide

/-- The old byte stands before the flush. -/
theorem avxWit_anfang :
    avxWitMem.bytes avxWitAdr = BitVec.ofNat 8 7 := by
  decide

/-- Beside the run: without the AVX bit the row refuses. -/
theorem avxWit_gate_aus :
    avx2RegSchritt avxWitS0 0 basisCpu basisXcr0 basisKontrolle
      avxWitZAdd = none := by
  decide

/-- Beside the run: the aligned store off its boundary refuses
    (8192 + 16 is 16 past a 32-byte boundary). -/
theorem avxWit_fehl_ausgerichtet :
    avx2SpeicherSchritt avxWitS1 0 avx2Cpu avx2Xcr0 basisKontrolle
      ⟨.vmovdqaSt .rax .ymm0 16, 6⟩ = none := by
  decide

/-- Beside the run: the byte shift has no encoding and refuses. -/
theorem avxWit_sll_b8_aus :
    avx2RegSchritt avxWitS0 0 avx2Cpu avx2Xcr0 basisKontrolle
      ⟨.vpsllImm .b8 .ymm0 .ymm1 1, 5⟩ = none := by
  decide

/-- THE JOINT WITNESS: a reached two-core run -- register execution
    with lane separation, a thirty-two-entry buffered store that
    changes no canonical byte, owner-only forwarding of the new byte,
    a memory-changing flush observed afterwards -- with the gate, the
    `#GP`, the VEX.128, the unencodable-shift and the old-row
    refusals beside it. Non-degenerate: the flush changes ACTUAL
    shared memory (`7` to `1`). -/
theorem avx2Wit_zeuge :
    Avx2Schritt avxWitS0 avxWitS1
        (.avxReg 0 avx2Cpu avx2Xcr0 basisKontrolle avxWitZAdd) ∧
      Avx2Schritt avxWitS1 avxWitS2
        (.avxSpeichere 0 avx2Cpu avx2Xcr0 basisKontrolle avxWitZSt) ∧
      Avx2Wf avxWitS0 ∧ Avx2Wf avxWitS1 ∧ Avx2Wf avxWitS2 ∧
      avx2Bereit witBlatt1 witBlatt7 witXcrLo = true ∧
      avx2TierBereit (cpuAusBlaettern witBlatt1 witBlatt7)
        (xcr0AusWort witXcrLo) basisKontrolle vecZeugeBereit = true ∧
      stufenZugelassenHw basisHw basisBereit basisCpu basisXcr0
        basisKontrolle .avx256 = false ∧
      dekodiereAvx2 [(0xC4 : Byte), 0xE1, 0x74, 0xD4, 0xC2] = none ∧
      avxWitS2.hw.mem.bytes avxWitAdr =
        BitVec.ofNat 8 7 ∧
      loadByte (tsoAnsicht avxWitS2.hw) 0 avxWitAdr =
        some (BitVec.ofNat 8 1) ∧
      loadByte (tsoAnsicht avxWitS2.hw) 1 avxWitAdr =
        some (BitVec.ofNat 8 7) ∧
      ((flushKern (tsoAnsicht avxWitS2.hw) 0).map fun s' =>
        s'.mem.bytes avxWitAdr) = some (BitVec.ofNat 8 1) := by
  have hbr := avx2Bruecke_blatt_zeuge
  have hmem7 : avxWitS2.hw.mem.bytes avxWitAdr =
      BitVec.ofNat 8 7 := by
    decide
  exact ⟨avxWit_reg, avxWit_speichere, avxWitS0_wf, avxWitS1_wf,
    avxWitS1_wf, hbr.1, hbr.2,
    avx256_alte_gate_verweigert basisHw basisBereit basisCpu
      basisXcr0 basisKontrolle,
    dekodiere_vex128_verweigert, hmem7, avxWit_eigen,
    avxWit_fremd, avxWit_spuelung⟩

/- CUTS: what is not proved here.

   - Join scope: only `Avx2Ops` (lane 1239) is joined. The sibling
     pieces Vex (1237), State (1241) and Mem (1243) are NOT in this
     tree, so the VEX-row decoder (§1), the YMM file (§3 head) and
     the 32-byte TSO forms (§3) are defined HERE, reusing accepted
     vocabulary (`ymm*`, `issueListe`, `ladeAcht`, `effAddr`,
     `ripNach`) and never copying a model. If the siblings land with
     different shapes, this file's substitutes must be re-pointed at
     them (a mechanical integration, explicitly not done here).
   - Decoder coverage: four pinned rows only. Full ModRM/SIB,
     disp8 sign handling beyond disp 0, EVEX, masks, broadcast,
     gather, shuffles/permutes and the 128-bit VEX rows stay open
     with the absent Vex piece. The four pinned prefix derivations
     assume Vol. 2A 2.3.5 bit positions (named silicon assumption).
   - Disp8 is zero-extended (`avx2Addr`); silicon sign-extends.
     The witness uses disp 0 where both agree.
   - No YMM legacy semantics: upper-half zeroing (VEX.128),
     VZEROUPPER/VZEROALL, MXCSR SIMD exceptions, #NM/#XM classes
     and the exact #UD-vs-#GP priority stay open. Absent-gate
     refusal is one `#UD`-class `none`, never a fault taxonomy.
   - No whole-vector atomicity: thirty-two per-byte TSO events
     (oldest-first issues, oldest-first flushes); torn intermediates
     stand. No per-access target-to-W/GX simulation and no source
     correspondence are claimed.
   - The bridge is conditional both ways (§2 states each missing
     conjunct); the unconditional reading (silicon AVX2 always
     carries CPUID SSE2/OSXSAVE and XCR0 x87, control state always
     ready) is a named silicon/binding assumption, not a theorem.
   - Reachability is chained joint steps from the witness start;
     no `TSOErreichbar` 32-issue induction is built.
   - Silicon correspondence beyond the cited extract lines is OPEN:
     the theorems are self-consistency of the stated functions
     against the accepted evaluators, not hardware proofs.
-/

#print axioms ymmSet_gleich
#print axioms ymmSet_fremd
#print axioms dekodiere_paddq
#print axioms dekodiere_pxor
#print axioms dekodiere_movdquLd
#print axioms dekodiere_movdquSt
#print axioms dekodiere_vex128_verweigert
#print axioms dekodiere_fremd_verweigert
#print axioms cpuAusBlaettern_avx
#print axioms cpuAusBlaettern_sse2
#print axioms xcr0AusWort_avx
#print axioms avx2Bruecke_vor
#print axioms avx2Bruecke_zurueck
#print axioms avx2Bruecke_blatt_zeuge
#print axioms ymmEintraege_laenge
#print axioms ymmSpeichern_ist_issueListe
#print axioms ymmSpeichern_haengt_an
#print axioms ymmSpeichern_kein_speicher
#print axioms ymmEintrag_schreibbar
#print axioms ymmSpeichern_erfolg
#print axioms avx2Auswertung_add
#print axioms avx2Auswertung_sub
#print axioms avx2Auswertung_and
#print axioms avx2Auswertung_or
#print axioms avx2Auswertung_xor
#print axioms avx2Auswertung_andn
#print axioms avx2Auswertung_cmpeq
#print axioms avx2Auswertung_sll
#print axioms avx2Auswertung_srl
#print axioms avx2Auswertung_sra
#print axioms avx2Auswertung_sll_b8
#print axioms avx2Auswertung_srl_b8
#print axioms avx2Auswertung_sra_b64
#print axioms avx2Auswertung_speicher
#print axioms ymmGp_nie_unausgerichtet
#print axioms ymmGp_ausgerichtet_fehler
#print axioms ymmGp_ausgerichtet_ok
#print axioms avx2SetReg_speicher
#print axioms avx2SetReg_puffer
#print axioms avx2SetReg_ymm
#print axioms avx2Dst_ist_register
#print axioms avx2RegSchritt_gleich
#print axioms avx2Schritt_wf
#print axioms avx2Schritt_einbettet
#print axioms avx2Schritt_projiziert
#print axioms avx2Reg_ohne_gate
#print axioms avx2Lade_ohne_gate
#print axioms avx2Speichere_ohne_gate
#print axioms avx2Reg_speicher_verweigert
#print axioms avx2Speichere_register_verweigert
#print axioms avx2SpeichereA_fehl_ausgerichtet
#print axioms avx256_alte_gate_verweigert
#print axioms avxWit_gate
#print axioms avxWitS0_wf
#print axioms avxWitS1_wf
#print axioms avxWit_paddb
#print axioms avxWit_plug
#print axioms avxWit_reg
#print axioms avxWit_eff
#print axioms avxWit_ymm
#print axioms avxWit_issue
#print axioms avxWit_gate_s1
#print axioms avxWit_plug_s2
#print axioms avxWit_speichere
#print axioms avxWit_r1_rip
#print axioms avxWit_r1_lane0
#print axioms avxWit_r1_lane1
#print axioms avxWit_s2_buflen
#print axioms avxWit_s2_mem_still
#print axioms avxWit_eigen
#print axioms avxWit_fremd
#print axioms avxWit_ymm_lade
#print axioms avxWit_spuelung
#print axioms avxWit_anfang
#print axioms avxWit_gate_aus
#print axioms avxWit_fehl_ausgerichtet
#print axioms avxWit_sll_b8_aus
#print axioms avx2Wit_zeuge

end Gabbro.Grammatik.X86
