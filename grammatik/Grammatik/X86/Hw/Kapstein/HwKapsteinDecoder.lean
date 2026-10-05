/-
  File:      Grammatik/X86/HwKapsteinDecoder.lean
  Subject:   Capstone: one byte-decoder priority chain over all families.

  Lane 1291: every byte decoder the capstone union uses
  (`decodeMulDivWidth` over `decodeExt`, `s32Decode`, `mxcsrDecode`,
  `decodeLock`, `decodeLockAdr`, `decodeC`, `decodeCore`,
  `dekodiereAvx2`) in ONE deterministic priority chain `kapDecode`,
  with per-level agreement, a proved lock/lockAdr partition, the
  known width overlap exhibits, and closed witness pins per level.
  Accepted definitions are reused unchanged, never redefined.
-/
import Grammatik.X86.Hw.Grundlage.ExtendedExecution
import Grammatik.X86.Befehle.Arithmetik.MulDivWidthHardwareForms
import Grammatik.X86.Hw.Familien.HwMulDivWidth
import Grammatik.X86.TSO.Verriegelt.LockedInstructionExecution
import Grammatik.X86.Speicher.AddressedHardwareExecution
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat32HardwareForms
import Grammatik.X86.Befehle.Gleitkomma.FpControlHardwareForms
import Grammatik.X86.Hw.Gleitkomma.HwFpDispatch
import Grammatik.X86.Befehle.ISA.ISA
import Grammatik.X86.Befehle.Kompakt.CompactForms
import Grammatik.X86.Befehle.Ganzzahl.IntegerCore
import Grammatik.X86.Befehle.Vektor.Avx2Join
namespace Gabbro.Grammatik.X86

/-- One decoded row of the capstone chain: the width dispatcher arm
    (which already carries the whole unified chain), then each later
    family arm in priority order. -/
inductive KapDekodiert where
  | breit : WdHwInstr → KapDekodiert
  | s32 : S32Decodiert → KapDekodiert
  | mxcsr : MxcsrDec → KapDekodiert
  | lock : LockAnweisung → KapDekodiert
  | lockAdr : Register → AdrForm → KapDekodiert
  | kompakt : CompactDecodiert → KapDekodiert
  | kern : CoreDecodiert → KapDekodiert
  | avx2 : Avx2Join.Avx2Zeile → KapDekodiert
  deriving DecidableEq, Repr

/-- The capstone priority chain over bytes: each decoder runs only
    where every earlier one refuses, so dispatch is disjoint by
    construction and deterministic (it is a function). -/
def kapDecode : List Byte → Option (KapDekodiert × List Byte) :=
  fun bs =>
    match decodeMulDivWidth bs with
    | some (w, rest) => some (KapDekodiert.breit w, rest)
    | none =>
      match s32Decode bs with
      | some (d, rest) => some (KapDekodiert.s32 d, rest)
      | none =>
        match mxcsrDecode bs with
        | some (d, rest) => some (KapDekodiert.mxcsr d, rest)
        | none =>
          match decodeLock bs with
          | some (a, rest) => some (KapDekodiert.lock a, rest)
          | none =>
            match decodeLockAdr bs with
            | some (r, f, rest) => some (KapDekodiert.lockAdr r f, rest)
            | none =>
              match decodeC bs with
              | some (d, rest) => some (KapDekodiert.kompakt d, rest)
              | none =>
                match decodeCore bs with
                | some (d, rest) => some (KapDekodiert.kern d, rest)
                | none =>
                  match Avx2Join.dekodiereAvx2 bs with
                  | some z => some (KapDekodiert.avx2 z, [])
                  | none => none

/-! ## 1. Agreement: each level takes its bytes exactly where earlier
    levels refuse. Every premise is used: the earlier `none`s route
    past the earlier arms, the `some` takes the level's arm. -/

/-- The width dispatcher arm agrees wherever it accepts. -/
theorem kapDecode_breit (bs : List Byte) (w : WdHwInstr)
    (rest : List Byte)
    (h : decodeMulDivWidth bs = some (w, rest)) :
    kapDecode bs = some (KapDekodiert.breit w, rest) := by
  unfold kapDecode
  rw [h]

/-- The s32 arm agrees where the width dispatcher refuses. -/
theorem kapDecode_s32 (bs : List Byte) (d : S32Decodiert)
    (rest : List Byte) (h1 : decodeMulDivWidth bs = none)
    (h2 : s32Decode bs = some (d, rest)) :
    kapDecode bs = some (KapDekodiert.s32 d, rest) := by
  unfold kapDecode
  rw [h1, h2]

/-- The MXCSR arm agrees where width and s32 refuse. -/
theorem kapDecode_mxcsr (bs : List Byte) (d : MxcsrDec)
    (rest : List Byte) (h1 : decodeMulDivWidth bs = none)
    (h2 : s32Decode bs = none)
    (h3 : mxcsrDecode bs = some (d, rest)) :
    kapDecode bs = some (KapDekodiert.mxcsr d, rest) := by
  unfold kapDecode
  rw [h1, h2, h3]

/-- The LOCK arm agrees where width, s32 and MXCSR refuse. -/
theorem kapDecode_lock (bs : List Byte) (a : LockAnweisung)
    (rest : List Byte) (h1 : decodeMulDivWidth bs = none)
    (h2 : s32Decode bs = none) (h3 : mxcsrDecode bs = none)
    (h4 : decodeLock bs = some (a, rest)) :
    kapDecode bs = some (KapDekodiert.lock a, rest) := by
  unfold kapDecode
  rw [h1, h2, h3, h4]

/-- The addressed-LOCK arm agrees where all earlier arms refuse. -/
theorem kapDecode_lockAdr (bs : List Byte) (r : Register) (f : AdrForm)
    (rest : List Byte) (h1 : decodeMulDivWidth bs = none)
    (h2 : s32Decode bs = none) (h3 : mxcsrDecode bs = none)
    (h4 : decodeLock bs = none)
    (h5 : decodeLockAdr bs = some (r, f, rest)) :
    kapDecode bs = some (KapDekodiert.lockAdr r f, rest) := by
  unfold kapDecode
  rw [h1, h2, h3, h4, h5]

/-- The compact arm agrees where all earlier arms refuse. -/
theorem kapDecode_kompakt (bs : List Byte) (d : CompactDecodiert)
    (rest : List Byte) (h1 : decodeMulDivWidth bs = none)
    (h2 : s32Decode bs = none) (h3 : mxcsrDecode bs = none)
    (h4 : decodeLock bs = none) (h5 : decodeLockAdr bs = none)
    (h6 : decodeC bs = some (d, rest)) :
    kapDecode bs = some (KapDekodiert.kompakt d, rest) := by
  unfold kapDecode
  rw [h1, h2, h3, h4, h5, h6]

/-- The core arm agrees where all earlier arms refuse. -/
theorem kapDecode_kern (bs : List Byte) (d : CoreDecodiert)
    (rest : List Byte) (h1 : decodeMulDivWidth bs = none)
    (h2 : s32Decode bs = none) (h3 : mxcsrDecode bs = none)
    (h4 : decodeLock bs = none) (h5 : decodeLockAdr bs = none)
    (h6 : decodeC bs = none)
    (h7 : decodeCore bs = some (d, rest)) :
    kapDecode bs = some (KapDekodiert.kern d, rest) := by
  unfold kapDecode
  rw [h1, h2, h3, h4, h5, h6, h7]

/-- The AVX2 arm agrees where every earlier arm refuses. -/
theorem kapDecode_avx2 (bs : List Byte) (z : Avx2Join.Avx2Zeile)
    (h1 : decodeMulDivWidth bs = none)
    (h2 : s32Decode bs = none) (h3 : mxcsrDecode bs = none)
    (h4 : decodeLock bs = none) (h5 : decodeLockAdr bs = none)
    (h6 : decodeC bs = none) (h7 : decodeCore bs = none)
    (h8 : Avx2Join.dekodiereAvx2 bs = some z) :
    kapDecode bs = some (KapDekodiert.avx2 z, []) := by
  unfold kapDecode
  rw [h1, h2, h3, h4, h5, h6, h7, h8]

/-- Where every decoder refuses, the chain refuses. -/
theorem kapDecode_nichts (bs : List Byte)
    (h1 : decodeMulDivWidth bs = none)
    (h2 : s32Decode bs = none) (h3 : mxcsrDecode bs = none)
    (h4 : decodeLock bs = none) (h5 : decodeLockAdr bs = none)
    (h6 : decodeC bs = none) (h7 : decodeCore bs = none)
    (h8 : Avx2Join.dekodiereAvx2 bs = none) :
    kapDecode bs = none := by
  unfold kapDecode
  rw [h1, h2, h3, h4, h5, h6, h7, h8]

/-- The chain is deterministic: one byte string, at most one answer. -/
theorem kapDecode_deterministisch (bs : List Byte)
    (x y : KapDekodiert × List Byte)
    (hx : kapDecode bs = some x) (hy : kapDecode bs = some y) :
    x = y := by
  rw [hx] at hy
  cases hy
  rfl

/-! ## 2. Witnesses: one closed byte string per level, each taken by
    its own arm. Every acceptance reuses an accepted pin or round
    trip, never re-decided. -/

/-- Width witness: 32-bit Group-3 multiply, refused by the unified chain. -/
def kapW_wd : List Byte := [natByte 247, natByte 225]

/-- s32 witness: scalar-single add, refused by the unified chain. -/
def kapW_s32 : List Byte := s32EncodeAddssRR .xmm2 .xmm3

/-- MXCSR witness: LDMXCSR, refused by the unified chain and s32. -/
def kapW_mxcsr : List Byte := mxcsrEncodeLd .rax (BitVec.ofNat 32 0)

/-- LOCK witness: LOCK XADD [rbp+0], rax, refused by the unified chain. -/
def kapW_lock : List Byte := pinXadd

/-- Addressed-LOCK witness: the extended scaled tail, refused by the
    accepted producer. -/
def kapW_lockAdr : List Byte :=
  [natByte 240, natByte 77, natByte 15, natByte 193,
   natByte 68, natByte 200, natByte 0]

/-- Compact witness: 32-bit immediate MOV, refused by the pilot. -/
def kapW_kompakt : List Byte :=
  encodeC (.movImm32Zx .rax (BitVec.ofNat 32 1))

/-- Core witness: 64-bit AND, refused by the pilot. -/
def kapW_kern : List Byte := encodeCore (.andReg64 .rax .rcx)

/-- AVX2 witness: the pinned VEX.256 VPADDQ row. -/
def kapW_avx2 : List Byte :=
  [(0xC4 : Byte), 0xE1, 0x75, 0xD4, 0xC2]

/-- The width arm takes its witness (accepted pin). -/
theorem kapW_wd_akzeptiert :
    decodeWd kapW_wd =
      some ((⟨WdBefehl.mul WdBreite.w32 Register.rcx, 2⟩ : WdDecodiert),
        []) := by
  unfold kapW_wd
  exact pin_wdmul_ecx_dekode

/-- The s32 arm takes its witness (accepted round trip). -/
theorem kapW_s32_akzeptiert :
    s32Decode kapW_s32 =
      some (⟨.addssRR .xmm2 .xmm3,
        (s32EncodeAddssRR .xmm2 .xmm3).length⟩, []) := by
  have h2 := s32Roundtrip_addssRR .xmm2 .xmm3 []
  simp only [List.append_nil] at h2
  unfold kapW_s32
  exact h2

/-- The MXCSR arm takes its witness (accepted round trip). -/
theorem kapW_mxcsr_akzeptiert :
    mxcsrDecode kapW_mxcsr =
      some (⟨.ldmxcsr .rax (BitVec.ofNat 32 0),
        (mxcsrEncodeLd .rax (BitVec.ofNat 32 0)).length, false⟩, []) := by
  have h3 := mxcsrRoundtrip_ld .rax (BitVec.ofNat 32 0) [] pin_disp_rax_code
  simp only [List.append_nil] at h3
  unfold kapW_mxcsr
  exact h3

/-- The LOCK arm takes its witness (accepted pin). -/
theorem kapW_lock_akzeptiert :
    decodeLock kapW_lock =
      some (LockAnweisung.ok (.xadd64 .rax .rbp 0) 9, []) := by
  unfold kapW_lock
  exact pin_lock_xadd_decodiert

/-- The addressed-LOCK arm takes its witness (accepted pin). -/
theorem kapW_lockAdr_akzeptiert :
    decodeLockAdr kapW_lockAdr =
      some (.r8,
        ⟨some .r8, some .rcx, 8, u8Nach32 (natByte 0), .d8, false⟩,
        []) := by
  unfold kapW_lockAdr
  exact decoder_nimmt_skaliert

/-- The compact arm takes its witness (accepted round trip). -/
theorem kapW_kompakt_akzeptiert :
    decodeC kapW_kompakt =
      some (⟨.movImm32Zx .rax (BitVec.ofNat 32 1),
        (encodeC (.movImm32Zx .rax (BitVec.ofNat 32 1))).length⟩, []) := by
  have h := roundtripC_movImm32Zx .rax (BitVec.ofNat 32 1) []
  simp only [List.append_nil] at h
  unfold kapW_kompakt
  exact h

/-- The core arm takes its witness (accepted round trip). -/
theorem kapW_kern_akzeptiert :
    decodeCore kapW_kern = some (⟨.andReg64 .rax .rcx, 3⟩, []) := by
  have h := roundtrip_andReg64 .rax .rcx []
  simp only [List.append_nil] at h
  unfold kapW_kern
  exact h

/-- The AVX2 arm takes its witness (accepted pin). -/
theorem kapW_avx2_akzeptiert :
    Avx2Join.dekodiereAvx2 kapW_avx2 =
      some ⟨.vpaddRR .b64 .ymm0 .ymm1 .ymm2, 5⟩ := by
  unfold kapW_avx2
  exact Avx2Join.dekodiere_paddq

/-! ## 3. Refusal matrix: every witness is refused by every other
    level's decoder. Reused accepted pins where they exist; closed
    `decide` evaluations otherwise. No overlap is exhibited here;
    overlaps with their winners live in §5. -/

/-- Width witness: refused by the unified chain (accepted pin). -/
theorem kapW_wd_verweigert_ext : decodeExt kapW_wd = none := by
  unfold kapW_wd
  exact ext_weist_wdmul32_zurueck

/-- Width witness: refused by s32, MXCSR, LOCK, addressed-LOCK,
    compact, core and AVX2. -/
theorem kapW_wd_verweigert_s32 : s32Decode kapW_wd = none := by decide
theorem kapW_wd_verweigert_mxcsr : mxcsrDecode kapW_wd = none := by decide
theorem kapW_wd_verweigert_lock : decodeLock kapW_wd = none := by decide
theorem kapW_wd_verweigert_lockAdr : decodeLockAdr kapW_wd = none := by decide
theorem kapW_wd_verweigert_kompakt : decodeC kapW_wd = none := by decide
theorem kapW_wd_verweigert_kern : decodeCore kapW_wd = none := by decide
theorem kapW_wd_verweigert_avx2 :
    Avx2Join.dekodiereAvx2 kapW_wd = none := by decide

/-- s32 witness: refused by the unified chain (accepted pin). -/
theorem kapW_s32_verweigert_ext : decodeExt kapW_s32 = none := by
  unfold kapW_s32
  exact pin_disp_vereinheitlicht_weist_s32_zurueck

/-- s32 witness: refused by MXCSR (accepted pin). -/
theorem kapW_s32_verweigert_mxcsr : mxcsrDecode kapW_s32 = none := by
  unfold kapW_s32
  exact pin_disp_mxcsr_weist_s32_zurueck

/-- s32 witness: refused by width, LOCK, addressed-LOCK, compact,
    core and AVX2. -/
theorem kapW_s32_verweigert_wd : decodeWd kapW_s32 = none := by decide
theorem kapW_s32_verweigert_lock : decodeLock kapW_s32 = none := by decide
theorem kapW_s32_verweigert_lockAdr : decodeLockAdr kapW_s32 = none := by decide
theorem kapW_s32_verweigert_kompakt : decodeC kapW_s32 = none := by decide
theorem kapW_s32_verweigert_kern : decodeCore kapW_s32 = none := by decide
theorem kapW_s32_verweigert_avx2 :
    Avx2Join.dekodiereAvx2 kapW_s32 = none := by decide

/-- MXCSR witness: refused by the unified chain (accepted pin). -/
theorem kapW_mxcsr_verweigert_ext : decodeExt kapW_mxcsr = none := by
  unfold kapW_mxcsr
  exact pin_disp_vereinheitlicht_weist_ldmxcsr_zurueck

/-- MXCSR witness: refused by s32 (accepted pin). -/
theorem kapW_mxcsr_verweigert_s32 : s32Decode kapW_mxcsr = none := by
  unfold kapW_mxcsr
  exact pin_disp_s32_weist_ldmxcsr_zurueck

/-- MXCSR witness: refused by width, LOCK, addressed-LOCK, compact,
    core and AVX2. -/
theorem kapW_mxcsr_verweigert_wd : decodeWd kapW_mxcsr = none := by decide
theorem kapW_mxcsr_verweigert_lock : decodeLock kapW_mxcsr = none := by decide
theorem kapW_mxcsr_verweigert_lockAdr :
    decodeLockAdr kapW_mxcsr = none := by decide
theorem kapW_mxcsr_verweigert_kompakt : decodeC kapW_mxcsr = none := by decide
theorem kapW_mxcsr_verweigert_kern : decodeCore kapW_mxcsr = none := by decide
theorem kapW_mxcsr_verweigert_avx2 :
    Avx2Join.dekodiereAvx2 kapW_mxcsr = none := by decide

/-- LOCK witness: refused by the unified chain (accepted pin). -/
theorem kapW_lock_verweigert_ext : decodeExt kapW_lock = none := by
  unfold kapW_lock
  exact pin_lock_ext_verweigert_xadd

/-- LOCK witness: refused by width, s32, MXCSR, addressed-LOCK,
    compact, core and AVX2. -/
theorem kapW_lock_verweigert_wd : decodeWd kapW_lock = none := by decide
theorem kapW_lock_verweigert_s32 : s32Decode kapW_lock = none := by decide
theorem kapW_lock_verweigert_mxcsr : mxcsrDecode kapW_lock = none := by decide
theorem kapW_lock_verweigert_lockAdr :
    decodeLockAdr kapW_lock = none := by decide
theorem kapW_lock_verweigert_kompakt : decodeC kapW_lock = none := by decide
theorem kapW_lock_verweigert_kern : decodeCore kapW_lock = none := by decide
theorem kapW_lock_verweigert_avx2 :
    Avx2Join.dekodiereAvx2 kapW_lock = none := by decide

/-- Addressed-LOCK witness: refused by the accepted producer
    (accepted pin). -/
theorem kapW_lockAdr_verweigert_lock : decodeLock kapW_lockAdr = none := by
  unfold kapW_lockAdr
  exact produzent_weist_skaliert_zurueck

/-- Addressed-LOCK witness: refused by unified, width, s32, MXCSR,
    compact, core and AVX2. -/
theorem kapW_lockAdr_verweigert_ext : decodeExt kapW_lockAdr = none := by decide
theorem kapW_lockAdr_verweigert_wd : decodeWd kapW_lockAdr = none := by decide
theorem kapW_lockAdr_verweigert_s32 : s32Decode kapW_lockAdr = none := by decide
theorem kapW_lockAdr_verweigert_mxcsr :
    mxcsrDecode kapW_lockAdr = none := by decide
theorem kapW_lockAdr_verweigert_kompakt :
    decodeC kapW_lockAdr = none := by decide
theorem kapW_lockAdr_verweigert_kern :
    decodeCore kapW_lockAdr = none := by decide
theorem kapW_lockAdr_verweigert_avx2 :
    Avx2Join.dekodiereAvx2 kapW_lockAdr = none := by decide

/-- Compact witness: refused by unified, width, s32, MXCSR, LOCK,
    addressed-LOCK, core and AVX2. -/
theorem kapW_kompakt_verweigert_ext : decodeExt kapW_kompakt = none := by decide
theorem kapW_kompakt_verweigert_wd : decodeWd kapW_kompakt = none := by decide
theorem kapW_kompakt_verweigert_s32 :
    s32Decode kapW_kompakt = none := by decide
theorem kapW_kompakt_verweigert_mxcsr :
    mxcsrDecode kapW_kompakt = none := by decide
theorem kapW_kompakt_verweigert_lock :
    decodeLock kapW_kompakt = none := by decide
theorem kapW_kompakt_verweigert_lockAdr :
    decodeLockAdr kapW_kompakt = none := by decide
theorem kapW_kompakt_verweigert_kern :
    decodeCore kapW_kompakt = none := by decide
theorem kapW_kompakt_verweigert_avx2 :
    Avx2Join.dekodiereAvx2 kapW_kompakt = none := by decide

/-- Core witness: refused by unified, width, s32, MXCSR, LOCK,
    addressed-LOCK, compact and AVX2. -/
theorem kapW_kern_verweigert_ext : decodeExt kapW_kern = none := by decide
theorem kapW_kern_verweigert_wd : decodeWd kapW_kern = none := by decide
theorem kapW_kern_verweigert_s32 : s32Decode kapW_kern = none := by decide
theorem kapW_kern_verweigert_mxcsr : mxcsrDecode kapW_kern = none := by decide
theorem kapW_kern_verweigert_lock : decodeLock kapW_kern = none := by decide
theorem kapW_kern_verweigert_lockAdr :
    decodeLockAdr kapW_kern = none := by decide
theorem kapW_kern_verweigert_kompakt : decodeC kapW_kern = none := by decide
theorem kapW_kern_verweigert_avx2 :
    Avx2Join.dekodiereAvx2 kapW_kern = none := by decide

/-- AVX2 witness: refused by unified, width, s32, MXCSR, LOCK,
    addressed-LOCK, compact and core. -/
theorem kapW_avx2_verweigert_ext : decodeExt kapW_avx2 = none := by decide
theorem kapW_avx2_verweigert_wd : decodeWd kapW_avx2 = none := by decide
theorem kapW_avx2_verweigert_s32 : s32Decode kapW_avx2 = none := by decide
theorem kapW_avx2_verweigert_mxcsr : mxcsrDecode kapW_avx2 = none := by decide
theorem kapW_avx2_verweigert_lock : decodeLock kapW_avx2 = none := by decide
theorem kapW_avx2_verweigert_lockAdr :
    decodeLockAdr kapW_avx2 = none := by decide
theorem kapW_avx2_verweigert_kompakt : decodeC kapW_avx2 = none := by decide
theorem kapW_avx2_verweigert_kern : decodeCore kapW_avx2 = none := by decide

/-! ## 4. The chain takes every witness in its own arm: each level is
    reachable, none is shadowed. The width-level refusal of the later
    witnesses goes through the accepted dispatcher-nothing lemma. -/

/-- The chain takes the width witness in the width arm. -/
theorem kapKette_wd :
    kapDecode kapW_wd =
      some (KapDekodiert.breit
        (.wd (⟨WdBefehl.mul WdBreite.w32 Register.rcx, 2⟩ : WdDecodiert)),
        []) :=
  kapDecode_breit _ _ _
    (decodeMulDivWidth_wd _ _ _ kapW_wd_verweigert_ext kapW_wd_akzeptiert)

/-- s32 witness: refused by the width dispatcher (accepted lemma). -/
theorem kapW_s32_breit_verweigert :
    decodeMulDivWidth kapW_s32 = none :=
  decodeMulDivWidth_nichts _ kapW_s32_verweigert_ext kapW_s32_verweigert_wd

/-- The chain takes the s32 witness in the s32 arm. -/
theorem kapKette_s32 :
    kapDecode kapW_s32 =
      some (KapDekodiert.s32
        ⟨.addssRR .xmm2 .xmm3, (s32EncodeAddssRR .xmm2 .xmm3).length⟩, []) :=
  kapDecode_s32 _ _ _ kapW_s32_breit_verweigert kapW_s32_akzeptiert

/-- MXCSR witness: refused by the width dispatcher (accepted lemma). -/
theorem kapW_mxcsr_breit_verweigert :
    decodeMulDivWidth kapW_mxcsr = none :=
  decodeMulDivWidth_nichts _ kapW_mxcsr_verweigert_ext kapW_mxcsr_verweigert_wd

/-- The chain takes the MXCSR witness in the MXCSR arm. -/
theorem kapKette_mxcsr :
    kapDecode kapW_mxcsr =
      some (KapDekodiert.mxcsr
        ⟨.ldmxcsr .rax (BitVec.ofNat 32 0),
          (mxcsrEncodeLd .rax (BitVec.ofNat 32 0)).length, false⟩, []) :=
  kapDecode_mxcsr _ _ _ kapW_mxcsr_breit_verweigert
    kapW_mxcsr_verweigert_s32 kapW_mxcsr_akzeptiert

/-- LOCK witness: refused by the width dispatcher (accepted lemma). -/
theorem kapW_lock_breit_verweigert :
    decodeMulDivWidth kapW_lock = none :=
  decodeMulDivWidth_nichts _ kapW_lock_verweigert_ext kapW_lock_verweigert_wd

/-- The chain takes the LOCK witness in the LOCK arm. -/
theorem kapKette_lock :
    kapDecode kapW_lock =
      some (KapDekodiert.lock
        (LockAnweisung.ok (.xadd64 .rax .rbp 0) 9), []) :=
  kapDecode_lock _ _ _ kapW_lock_breit_verweigert
    kapW_lock_verweigert_s32 kapW_lock_verweigert_mxcsr kapW_lock_akzeptiert

/-- Addressed-LOCK witness: refused by the width dispatcher. -/
theorem kapW_lockAdr_breit_verweigert :
    decodeMulDivWidth kapW_lockAdr = none :=
  decodeMulDivWidth_nichts _ kapW_lockAdr_verweigert_ext
    kapW_lockAdr_verweigert_wd

/-- The chain takes the addressed-LOCK witness in its own arm. -/
theorem kapKette_lockAdr :
    kapDecode kapW_lockAdr =
      some (KapDekodiert.lockAdr .r8
        ⟨some .r8, some .rcx, 8, u8Nach32 (natByte 0), .d8, false⟩, []) :=
  kapDecode_lockAdr _ _ _ _ kapW_lockAdr_breit_verweigert
    kapW_lockAdr_verweigert_s32 kapW_lockAdr_verweigert_mxcsr
    kapW_lockAdr_verweigert_lock kapW_lockAdr_akzeptiert

/-- Compact witness: refused by the width dispatcher. -/
theorem kapW_kompakt_breit_verweigert :
    decodeMulDivWidth kapW_kompakt = none :=
  decodeMulDivWidth_nichts _ kapW_kompakt_verweigert_ext
    kapW_kompakt_verweigert_wd

/-- The chain takes the compact witness in the compact arm. -/
theorem kapKette_kompakt :
    kapDecode kapW_kompakt =
      some (KapDekodiert.kompakt
        ⟨.movImm32Zx .rax (BitVec.ofNat 32 1),
          (encodeC (.movImm32Zx .rax (BitVec.ofNat 32 1))).length⟩, []) :=
  kapDecode_kompakt _ _ _ kapW_kompakt_breit_verweigert
    kapW_kompakt_verweigert_s32 kapW_kompakt_verweigert_mxcsr
    kapW_kompakt_verweigert_lock kapW_kompakt_verweigert_lockAdr
    kapW_kompakt_akzeptiert

/-- Core witness: refused by the width dispatcher. -/
theorem kapW_kern_breit_verweigert :
    decodeMulDivWidth kapW_kern = none :=
  decodeMulDivWidth_nichts _ kapW_kern_verweigert_ext
    kapW_kern_verweigert_wd

/-- The chain takes the core witness in the core arm. -/
theorem kapKette_kern :
    kapDecode kapW_kern =
      some (KapDekodiert.kern ⟨.andReg64 .rax .rcx, 3⟩, []) :=
  kapDecode_kern _ _ _ kapW_kern_breit_verweigert
    kapW_kern_verweigert_s32 kapW_kern_verweigert_mxcsr
    kapW_kern_verweigert_lock kapW_kern_verweigert_lockAdr
    kapW_kern_verweigert_kompakt kapW_kern_akzeptiert

/-- AVX2 witness: refused by the width dispatcher. -/
theorem kapW_avx2_breit_verweigert :
    decodeMulDivWidth kapW_avx2 = none :=
  decodeMulDivWidth_nichts _ kapW_avx2_verweigert_ext
    kapW_avx2_verweigert_wd

/-- The chain takes the AVX2 witness in the AVX2 arm. -/
theorem kapKette_avx2 :
    kapDecode kapW_avx2 =
      some (KapDekodiert.avx2
        ⟨.vpaddRR .b64 .ymm0 .ymm1 .ymm2, 5⟩, []) :=
  kapDecode_avx2 _ _ kapW_avx2_breit_verweigert
    kapW_avx2_verweigert_s32 kapW_avx2_verweigert_mxcsr
    kapW_avx2_verweigert_lock kapW_avx2_verweigert_lockAdr
    kapW_avx2_verweigert_kompakt kapW_avx2_verweigert_kern
    kapW_avx2_akzeptiert

/-! ## 5. Overlaps with winners: byte strings two decoders accept,
    and which chain prefix takes them. Every overlap below keeps the
    EARLIER chain level; the witness matrix of §3 shows no other
    level touches these strings. -/

/-- Overlap (width vs unified): the REX.W Group-3 multiply row is
    accepted by the unified chain, so the chain keeps the unified arm:
    the width prefix wins, the width row is shadowed there by design. -/
theorem kapUeber_wd_ext_mul64 :
    kapDecode [natByte 73, natByte 247, natByte 224] =
      some (KapDekodiert.breit
        (.ext (.muldiv ⟨.mulRax .r8, 3⟩)), []) :=
  kapDecode_breit _ _ _ (decodeMulDivWidth_prefers_ext _ _ _ pin_ext_wdmul64)

/-- Overlap (width vs unified): the REX.W Group-3 divide row stays
    unified: the width prefix wins. -/
theorem kapUeber_wd_ext_div64 :
    kapDecode [natByte 73, natByte 247, natByte 251] =
      some (KapDekodiert.breit
        (.ext (.muldiv ⟨.idivRax .r11, 3⟩)), []) :=
  kapDecode_breit _ _ _ (decodeMulDivWidth_prefers_ext _ _ _ pin_ext_wdidiv64)

/-- Overlap (width vs unified): the REX.W two-operand multiply row
    stays unified: the width prefix wins. -/
theorem kapUeber_wd_ext_imul2 :
    kapDecode [natByte 77, natByte 15, natByte 175, natByte 207] =
      some (KapDekodiert.breit
        (.ext (.muldiv ⟨.imul2 .r9 .r15, 4⟩)), []) :=
  kapDecode_breit _ _ _ (decodeMulDivWidth_prefers_ext _ _ _ pin_ext_wdimul2)

/-- No overlap: the new 32-bit divide row is refused by the unified
    chain and taken in the width arm. -/
theorem kapUeber_wd_neu_div32 :
    kapDecode [natByte 247, natByte 241] =
      some (KapDekodiert.breit
        (.wd (⟨WdBefehl.divWd WdBreite.w32 Register.rcx, 2⟩ :
          WdDecodiert)), []) :=
  kapDecode_breit _ _ _
    (decodeMulDivWidth_wd _ _ _ ext_weist_wddiv32_zurueck
      pin_wddiv_ecx_dekode)

/-- Overlap (unified vs s32/MXCSR): the scalar-DOUBLE row is accepted
    by the unified chain and refused by both FP arms, so the chain
    keeps the unified arm: the unified prefix wins. -/
theorem kapUeber_f64_bleibt_breit :
    kapDecode (fpEncodeMovsdRR .xmm0 .xmm1) =
      some (KapDekodiert.breit
        (.ext (.fp ⟨.movsdRR .xmm0 .xmm1, 4⟩)), []) :=
  kapDecode_breit _ _ _
    (decodeMulDivWidth_prefers_ext _ _ _ pin_disp_f64_bleibt_vereinheitlicht)

/-- MFENCE bytes are refused by the unified chain and taken in the
    LOCK arm: the LOCK level wins over every earlier level. -/
theorem kapW_mfence_verweigert_wd : decodeWd pinMfence = none := by decide
theorem kapW_mfence_verweigert_s32 : s32Decode pinMfence = none := by decide
theorem kapW_mfence_verweigert_mxcsr :
    mxcsrDecode pinMfence = none := by decide

theorem kapUeber_mfence_lock :
    kapDecode pinMfence =
      some (KapDekodiert.lock (LockAnweisung.ok .mfence 3), []) := by
  apply kapDecode_lock
  · unfold pinMfence
    exact decodeMulDivWidth_nichts _ pin_lock_ext_verweigert_mfence
      kapW_mfence_verweigert_wd
  · exact kapW_mfence_verweigert_s32
  · exact kapW_mfence_verweigert_mxcsr
  · exact pin_lock_mfence_decodiert

/-! ## 6. Partition (LOCK vs addressed-LOCK): after a shared LOCK +
    canonical REX.W + 0F + XADD-opcode prefix the two decoders never
    accept the same tail. mod=3 is the parsed #UD (extended refuses);
    mod=2 without SIB is producer-owned (extended refuses); mod=2
    with SIB splits on the SIB byte (36 is producer-owned, anything
    else extended); mod 0/1 is extended-only (producer refuses).
    The ModRM lemma is proved here; its top-level lift
    `kap_lock_gegen_lockAdr` follows §8 after the joint witness. -/

/-- ModRM-level partition: the accepted producer tail and the
    extended tail never accept together. -/
theorem kap_lockModrm_gegen_adrTail
    (mk : Register → Register → BitVec 32 → LockForm)
    (rh bh : Nat) (bs : List Byte) (a : LockAnweisung) (rest1 : List Byte)
    (r : Register) (f : AdrForm) (rest2 : List Byte)
    (h1 : decodeLockModrm mk rh bh bs = some (a, rest1))
    (h2 : parseAdrTail rh 0 bh bs = some (r, f, rest2)) : False := by
  cases bs with
  | nil =>
    simp [decodeLockModrm] at h1
  | cons m rest =>
    unfold decodeLockModrm at h1
    unfold parseAdrTail at h2
    cases hmod : byteNat m / 64 with
    | zero =>
      simp [hmod] at h1
    | succ n =>
      cases n with
      | zero =>
        simp [hmod] at h1
      | succ n =>
        cases n with
        | zero =>
          cases hqm : byteNat m % 8 == 4 with
          | false =>
            simp [hmod, hqm] at h2
            split at h2 <;> cases h2
          | true =>
            cases rest with
            | nil =>
              simp [hmod, hqm] at h1
            | cons s rest1' =>
              cases hsib : byteNat s == 36 with
              | false =>
                simp [hmod, hqm, hsib] at h1
              | true =>
                simp [hmod, hqm, hsib] at h2
                split at h2 <;> cases h2
        | succ n =>
          cases n with
          | zero =>
            simp [hmod] at h2
            split at h2 <;> cases h2
          | succ n =>
            have hlt : byteNat m < 256 := m.isLt
            omega

/-! ## 7. ISA-internal domain partition, lifted: wherever the
    compact (resp. core) decoder accepts, the six shared ISA family
    decoders refuse -- the accepted `familien_disjunkt` over
    arbitrary bytes, applied arm by arm. The fp-double, vector,
    width, LOCK, addressed-LOCK and AVX2 sides stay witness-level
    (§3) and are named in CUTS. -/

/-- Compact acceptance refuses the six shared ISA arms. -/
theorem kap_kompakt_weist_sechs_zurueck (bs : List Byte)
    (d : CompactDecodiert) (rest : List Byte)
    (h : decodeC bs = some (d, rest)) :
    decode bs = none ∧ decodeNarrow bs = none ∧ decodeMulDiv bs = none ∧
    decodeShift bs = none ∧ decodeSetCC bs = none ∧
    decodeCmov bs = none := by
  have hc : decF .compact bs =
      some (⟨.compact d.befehl, d.laenge⟩, rest) := by
    simp [decF, h]
  have hpilot : decode bs = none := by
    cases hdec : decode bs with
    | none => rfl
    | some v =>
      obtain ⟨d', r'⟩ := v
      have hF : decF .pilot bs =
          some (⟨.pilot d'.befehl, d'.laenge⟩, r') := by
        simp [decF, hdec]
      have hFG := familien_disjunkt .pilot .compact bs _ _ hF hc
      cases hFG
  have hnarrow : decodeNarrow bs = none := by
    cases hdec : decodeNarrow bs with
    | none => rfl
    | some v =>
      obtain ⟨d', r'⟩ := v
      have hF : decF .narrow bs =
          some (⟨.narrow d'.op, d'.laenge⟩, r') := by
        simp [decF, hdec]
      have hFG := familien_disjunkt .narrow .compact bs _ _ hF hc
      cases hFG
  have hmuldiv : decodeMulDiv bs = none := by
    cases hdec : decodeMulDiv bs with
    | none => rfl
    | some v =>
      obtain ⟨d', r'⟩ := v
      have hF : decF .muldiv bs =
          some (⟨.muldiv d'.befehl, d'.laenge⟩, r') := by
        simp [decF, hdec]
      have hFG := familien_disjunkt .muldiv .compact bs _ _ hF hc
      cases hFG
  have hshift : decodeShift bs = none := by
    cases hdec : decodeShift bs with
    | none => rfl
    | some v =>
      obtain ⟨d', r'⟩ := v
      have hF : decF .shift bs =
          some (⟨.shift d', shiftLaenge d'⟩, r') := by
        simp [decF, hdec]
      have hFG := familien_disjunkt .shift .compact bs _ _ hF hc
      cases hFG
  have hsetcc : decodeSetCC bs = none := by
    cases hdec : decodeSetCC bs with
    | none => rfl
    | some v =>
      obtain ⟨p, r'⟩ := v
      obtain ⟨c, dst⟩ := p
      have hF : decF .setcc bs =
          some (⟨.cond (.setcc c dst), 4⟩, r') := by
        simp [decF, hdec]
      have hFG := familien_disjunkt .setcc .compact bs _ _ hF hc
      cases hFG
  have hcmov : decodeCmov bs = none := by
    cases hdec : decodeCmov bs with
    | none => rfl
    | some v =>
      obtain ⟨p, r'⟩ := v
      obtain ⟨c, dst, src⟩ := p
      have hF : decF .cmov bs =
          some (⟨.cond (.cmov c dst src), 4⟩, r') := by
        simp [decF, hdec]
      have hFG := familien_disjunkt .cmov .compact bs _ _ hF hc
      cases hFG
  exact ⟨hpilot, hnarrow, hmuldiv, hshift, hsetcc, hcmov⟩

/-- Core acceptance refuses the six shared ISA arms. -/
theorem kap_kern_weist_sechs_zurueck (bs : List Byte)
    (d : CoreDecodiert) (rest : List Byte)
    (h : decodeCore bs = some (d, rest)) :
    decode bs = none ∧ decodeNarrow bs = none ∧ decodeMulDiv bs = none ∧
    decodeShift bs = none ∧ decodeSetCC bs = none ∧
    decodeCmov bs = none := by
  have hc : decF .core bs =
      some (⟨.core d.befehl, d.laenge⟩, rest) := by
    simp [decF, h]
  have hpilot : decode bs = none := by
    cases hdec : decode bs with
    | none => rfl
    | some v =>
      obtain ⟨d', r'⟩ := v
      have hF : decF .pilot bs =
          some (⟨.pilot d'.befehl, d'.laenge⟩, r') := by
        simp [decF, hdec]
      have hFG := familien_disjunkt .pilot .core bs _ _ hF hc
      cases hFG
  have hnarrow : decodeNarrow bs = none := by
    cases hdec : decodeNarrow bs with
    | none => rfl
    | some v =>
      obtain ⟨d', r'⟩ := v
      have hF : decF .narrow bs =
          some (⟨.narrow d'.op, d'.laenge⟩, r') := by
        simp [decF, hdec]
      have hFG := familien_disjunkt .narrow .core bs _ _ hF hc
      cases hFG
  have hmuldiv : decodeMulDiv bs = none := by
    cases hdec : decodeMulDiv bs with
    | none => rfl
    | some v =>
      obtain ⟨d', r'⟩ := v
      have hF : decF .muldiv bs =
          some (⟨.muldiv d'.befehl, d'.laenge⟩, r') := by
        simp [decF, hdec]
      have hFG := familien_disjunkt .muldiv .core bs _ _ hF hc
      cases hFG
  have hshift : decodeShift bs = none := by
    cases hdec : decodeShift bs with
    | none => rfl
    | some v =>
      obtain ⟨d', r'⟩ := v
      have hF : decF .shift bs =
          some (⟨.shift d', shiftLaenge d'⟩, r') := by
        simp [decF, hdec]
      have hFG := familien_disjunkt .shift .core bs _ _ hF hc
      cases hFG
  have hsetcc : decodeSetCC bs = none := by
    cases hdec : decodeSetCC bs with
    | none => rfl
    | some v =>
      obtain ⟨p, r'⟩ := v
      obtain ⟨c, dst⟩ := p
      have hF : decF .setcc bs =
          some (⟨.cond (.setcc c dst), 4⟩, r') := by
        simp [decF, hdec]
      have hFG := familien_disjunkt .setcc .core bs _ _ hF hc
      cases hFG
  have hcmov : decodeCmov bs = none := by
    cases hdec : decodeCmov bs with
    | none => rfl
    | some v =>
      obtain ⟨p, r'⟩ := v
      obtain ⟨c, dst, src⟩ := p
      have hF : decF .cmov bs =
          some (⟨.cond (.cmov c dst src), 4⟩, r') := by
        simp [decF, hdec]
      have hFG := familien_disjunkt .cmov .core bs _ _ hF hc
      cases hFG
  exact ⟨hpilot, hnarrow, hmuldiv, hshift, hsetcc, hcmov⟩

/-! ## 8. Overlap meaning agreement, joint witness.

  The width/unified overlap is not a divergent meaning: on the
  overlapping rows the width evaluator IS the unified evaluator
  (accepted `rfl` lemmas, cited). -/

/-- Overlap meaning agreement (cited): 64-bit MUL evaluates the
    same through both arms. -/
theorem kapUeber_wd_bedeutung_mul64 (s : Zustand) (l : Nat) :
    wdSchritt ⟨WdBefehl.mul WdBreite.w64 .r8, l⟩ s =
      mulDivSchritt ⟨.mulRax .r8, l⟩ s :=
  wd_mul64_ist_mulRax s .r8 l

/-- Overlap meaning agreement (cited): 64-bit DIV evaluates the
    same through both arms. -/
theorem kapUeber_wd_bedeutung_div64 (s : Zustand) (l : Nat) :
    wdSchritt ⟨WdBefehl.divWd WdBreite.w64 .r11, l⟩ s =
      mulDivSchritt ⟨.divRax .r11, l⟩ s :=
  wd_div64_ist_divRax s .r11 l

/-- Joint witness: all eight chain arms take their own closed byte
    string. Every agreement premise is jointly instantiated; no arm
    is empty and no two witnesses share an arm. -/
theorem kapDecode_zeuge :
    kapDecode kapW_wd =
      some (KapDekodiert.breit
        (.wd (⟨WdBefehl.mul WdBreite.w32 Register.rcx, 2⟩ : WdDecodiert)),
        []) ∧
    kapDecode kapW_s32 =
      some (KapDekodiert.s32
        ⟨.addssRR .xmm2 .xmm3, (s32EncodeAddssRR .xmm2 .xmm3).length⟩, []) ∧
    kapDecode kapW_mxcsr =
      some (KapDekodiert.mxcsr
        ⟨.ldmxcsr .rax (BitVec.ofNat 32 0),
          (mxcsrEncodeLd .rax (BitVec.ofNat 32 0)).length, false⟩, []) ∧
    kapDecode kapW_lock =
      some (KapDekodiert.lock
        (LockAnweisung.ok (.xadd64 .rax .rbp 0) 9), []) ∧
    kapDecode kapW_lockAdr =
      some (KapDekodiert.lockAdr .r8
        ⟨some .r8, some .rcx, 8, u8Nach32 (natByte 0), .d8, false⟩, []) ∧
    kapDecode kapW_kompakt =
      some (KapDekodiert.kompakt
        ⟨.movImm32Zx .rax (BitVec.ofNat 32 1),
          (encodeC (.movImm32Zx .rax (BitVec.ofNat 32 1))).length⟩, []) ∧
    kapDecode kapW_kern =
      some (KapDekodiert.kern ⟨.andReg64 .rax .rcx, 3⟩, []) ∧
    kapDecode kapW_avx2 =
      some (KapDekodiert.avx2
        ⟨.vpaddRR .b64 .ymm0 .ymm1 .ymm2, 5⟩, []) :=
  ⟨kapKette_wd, kapKette_s32, kapKette_mxcsr, kapKette_lock,
    kapKette_lockAdr, kapKette_kompakt, kapKette_kern, kapKette_avx2⟩

/- CUTS:
    Proved here, over the reused accepted vocabulary only (every
    decoder lifted, never redefined):
    - one deterministic priority chain `kapDecode` over all eight
      byte decoders the capstone union uses (width dispatcher over
      the unified chain, s32, MXCSR, LOCK, addressed-LOCK, compact,
      core, AVX2 VEX), with per-level agreement (§1), determinism
      and the refusal case;
    - eight closed witnesses, each taken in its own arm (§2, §4),
      with the full refusal matrix: every witness is refused by
      every other level's decoder (§3, accepted pins reused where
      they exist, closed `decide` evaluations otherwise);
    - overlaps with winners (§5): the three REX.W width/unified
      rows keep the unified arm (exhibited byte strings, chain
      evaluations), the new width divide row and the scalar-DOUBLE
      row likewise, MFENCE bytes go to the LOCK arm; overlap
      meaning agreement cited (`wd_mul64_ist_mulRax`,
      `wd_div64_ist_divRax`): NO divergent-meaning overlap found;
    - full domain partition LOCK vs addressed-LOCK (§6,
      `kap_lockModrm_gegen_adrTail` + `kap_lock_gegen_lockAdr`):
      after a shared prefix the two decoders never accept the same
      tail -- mod=3 is the parsed #UD, mod=2 splits producer-owned
      (non-SIB and SIB byte 36) vs extended (other SIB bytes),
      mod 0/1 is extended-only;
    - ISA-internal domain partition for compact/core against the
      six shared arms (§7, accepted `familien_disjunkt` lifted);
    - joint witness `kapDecode_zeuge` over all eight arms.
    NOT proved here, and not claimed:
    - domain disjointness beyond the partitions above stays open:
      width vs s32/MXCSR/LOCK/lockAdr/compact/core/AVX2, s32 vs
      MXCSR and later levels, MXCSR vs later levels, LOCK vs
      width/unified (the family-local open item of the capstone
      CUTS), lockAdr vs width/unified/compact/core/AVX2,
      compact/core vs the fp-double, vector and width sub-arms and
      vs s32/MXCSR/LOCK/lockAdr/AVX2, AVX2 vs all -- witness-level
      only (§3 exhibits no overlap on any witness);
    - system forms have no byte decoder (control snapshots, not
      bytes), so they are disjoint from the chain by construction,
      not by a proved bytes-fact;
    - the AVX2 VEX decoder covers four pinned rows only (accepted
      limitation of `Avx2Join`), the second compact family
      (`decodeCompact`/`decodeComboCompact`) is not in the union
      and not in the chain;
    - no silicon re-check beyond the accepted pins (encodings,
      fault classes and ordering rules are inherited unchanged);
      no W/GX bridge; no source, checker, contract, entry, ABI,
      loader, budget or liveness claim.
-/

#print axioms kapDecode_breit
#print axioms kapDecode_s32
#print axioms kapDecode_mxcsr
#print axioms kapDecode_lock
#print axioms kapDecode_lockAdr
#print axioms kapDecode_kompakt
#print axioms kapDecode_kern
#print axioms kapDecode_avx2
#print axioms kapDecode_nichts
#print axioms kapDecode_deterministisch
#print axioms kapKette_wd
#print axioms kapKette_s32
#print axioms kapKette_mxcsr
#print axioms kapKette_lock
#print axioms kapKette_lockAdr
#print axioms kapKette_kompakt
#print axioms kapKette_kern
#print axioms kapKette_avx2
#print axioms kapUeber_wd_ext_mul64
#print axioms kapUeber_wd_ext_div64
#print axioms kapUeber_wd_ext_imul2
#print axioms kapUeber_wd_neu_div32
#print axioms kapUeber_f64_bleibt_breit
#print axioms kapUeber_mfence_lock
#print axioms kapUeber_wd_bedeutung_mul64
#print axioms kapUeber_wd_bedeutung_div64
#print axioms kap_lockModrm_gegen_adrTail
#print axioms kap_kompakt_weist_sechs_zurueck
#print axioms kap_kern_weist_sechs_zurueck
#print axioms kapDecode_zeuge

/-- Top-level partition: LOCK and addressed-LOCK never accept the
    same byte string. Apart from the shared LOCK + REX + 0F +
    XADD-opcode shape (decided by the ModRM lemma) at least one
    side refuses at the prefix. -/
theorem kap_lock_gegen_lockAdr (bs : List Byte) (a : LockAnweisung)
    (rest1 : List Byte) (r : Register) (f : AdrForm) (rest2 : List Byte)
    (h1 : decodeLock bs = some (a, rest1))
    (h2 : decodeLockAdr bs = some (r, f, rest2)) : False := by
  cases bs with
  | nil =>
    simp [decodeLock] at h1
  | cons b0 rest0 =>
    unfold decodeLock at h1
    unfold decodeLockAdr at h2
    cases hb0 : byteNat b0 == 240 with
    | false =>
      simp [hb0] at h2
    | true =>
      cases rest0 with
      | nil =>
        simp [hb0] at h1
      | cons b1 rest1 =>
        cases hrex : rexLockBits b1 with
        | none =>
          simp [hb0, hrex] at h2
        | some rb =>
          obtain ⟨rh, bh⟩ := rb
          cases rest1 with
          | nil =>
            simp [hb0, hrex] at h1
          | cons b2 rest2 =>
            cases hb2 : byteNat b2 == 15 with
            | false =>
              simp [hb0, hrex, hb2] at h1
            | true =>
              cases rest2 with
              | nil =>
                simp [hb0, hrex, hb2] at h1
              | cons b3 rest3 =>
                cases hb3 : byteNat b3 == 193 with
                | false =>
                  simp [hb0, hrex, hb2, hb3] at h2
                | true =>
                  have hb3v : byteNat b3 = 193 := beq_iff_eq.mp hb3
                  simp [hb0, hrex, hb2, hb3v] at h1 h2
                  exact kap_lockModrm_gegen_adrTail _ _ _ _ _ _ _ _ _ h1 h2

#print axioms kap_lock_gegen_lockAdr

end Gabbro.Grammatik.X86
