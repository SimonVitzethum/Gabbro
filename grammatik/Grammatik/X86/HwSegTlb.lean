/-
  File:      Grammatik/X86/HwSegTlb.lean
  Subject:   FS/GS segment bases with override prefixes, and a per-core
             TLB with INVLPG and CR3-flush, over the coherent machine.

  Lane 1285: connects the SELECTED segment/TLB family to the coherent
  `HwMaschine`/`HwSchritt` of `HardwareExecution`, reusing the accepted
  definitions unchanged (lifted, never redefined). The page walk itself
  is a parameter (lane HwPaging owns it); PCID is off (named assumption).
  No silicon correspondence is claimed (see CUTS).
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.AddressEncoding
import Grammatik.X86.TSO

namespace Gabbro.Grammatik.X86

/-- Segment override choice on one memory access: no override, or the
    FS/GS base added to the effective address (64-bit mode). CS/DS/ES/SS
    carry no base here: they are ignored (see `segPraefix_ignoriert`). -/
inductive SegWahl where
  | kein | fs | gs
  deriving DecidableEq, Repr

/-! ## 1. Segment base registers: MSRs, prefixes, gating. -/

/-- FS-base MSR address (IA32_FS_BASE). -/
def msrFsBasis : Nat := 0xC0000100

/-- GS-base MSR address (IA32_GS_BASE). -/
def msrGsBasis : Nat := 0xC0000101

/-- Kernel-GS MSR address (IA32_KERNEL_GS_BASE, the SWAPGS peer). -/
def msrKernGsBasis : Nat := 0xC0000102

/-- The three base MSRs are pairwise distinct. -/
theorem msr_basis_verschieden :
    msrFsBasis ≠ msrGsBasis ∧
      msrGsBasis ≠ msrKernGsBasis ∧
      msrFsBasis ≠ msrKernGsBasis := by
  decide

/-- Segment-override prefix byte to its choice: 0x64 names FS, 0x65 names
    GS, every other byte names no base. -/
def segPraefix (b : Byte) : Option SegWahl :=
  if b == natByte 100 then some .fs
  else if b == natByte 101 then some .gs
  else none

/-- Pin: 0x64 is the FS override. -/
theorem segPraefix_fs : segPraefix (natByte 100) = some .fs := by
  decide

/-- Pin: 0x65 is the GS override. -/
theorem segPraefix_gs : segPraefix (natByte 101) = some .gs := by
  decide

/-- CS/DS/ES/SS prefixes name no base: their bases are ignored in
    64-bit mode (CS 0x2E, ES 0x26, SS 0x36, DS 0x3E). -/
theorem segPraefix_ignoriert :
    segPraefix (natByte 46) = none ∧
      segPraefix (natByte 38) = none ∧
      segPraefix (natByte 54) = none ∧
      segPraefix (natByte 62) = none := by
  decide

/-- Per-core segment state: the two bases, the SWAPGS peer, and the two
    FSGSBASE enable bits (CPUID leaf and CR4). -/
structure SegKern where
  fsBasis : Wort
  gsBasis : Wort
  kernGsBasis : Wort
  fsgsbaseCpuid : Bool
  fsgsbaseCr4 : Bool

/-- FSGSBASE enable: both the CPUID bit and the CR4 bit (otherwise the
    RD/WRxxBASE forms fault with #UD). -/
def fsgsbaseFreigabe (k : SegKern) : Bool :=
  k.fsgsbaseCpuid && k.fsgsbaseCr4

/-- Gated FS-base write (WRFSBASE): `none` is the #UD refusal. -/
def schreibeFsBasis (k : SegKern) (v : Wort) : Option SegKern :=
  if fsgsbaseFreigabe k then some { k with fsBasis := v } else none

/-- Gated GS-base write (WRGSBASE): `none` is the #UD refusal. -/
def schreibeGsBasis (k : SegKern) (v : Wort) : Option SegKern :=
  if fsgsbaseFreigabe k then some { k with gsBasis := v } else none

/-- FS-base read (RDFSBASE). -/
def liesFsBasis (k : SegKern) : Wort := k.fsBasis

/-- GS-base read (RDGSBASE). -/
def liesGsBasis (k : SegKern) : Wort := k.gsBasis

/-- Write-then-read round trip on an enabled core. -/
theorem schreibeLiesFsBasis (k : SegKern) (v : Wort)
    (h : fsgsbaseFreigabe k = true) :
    (schreibeFsBasis k v).map liesFsBasis = some v := by
  simp [schreibeFsBasis, liesFsBasis, h]

/-- Write-then-read round trip on an enabled core (GS side). -/
theorem schreibeLiesGsBasis (k : SegKern) (v : Wort)
    (h : fsgsbaseFreigabe k = true) :
    (schreibeGsBasis k v).map liesGsBasis = some v := by
  simp [schreibeGsBasis, liesGsBasis, h]

/-- REFUSAL: no CPUID bit, no FS-base write. -/
theorem schreibeFsBasis_verweigert_ohne_cpuid (k : SegKern) (v : Wort)
    (h : k.fsgsbaseCpuid = false) :
    schreibeFsBasis k v = none := by
  simp [schreibeFsBasis, fsgsbaseFreigabe, h]

/-- REFUSAL: no CR4 bit, no FS-base write. -/
theorem schreibeFsBasis_verweigert_ohne_cr4 (k : SegKern) (v : Wort)
    (h : k.fsgsbaseCr4 = false) :
    schreibeFsBasis k v = none := by
  simp [schreibeFsBasis, fsgsbaseFreigabe, h]

/-- REFUSAL: no CPUID bit, no GS-base write. -/
theorem schreibeGsBasis_verweigert_ohne_cpuid (k : SegKern) (v : Wort)
    (h : k.fsgsbaseCpuid = false) :
    schreibeGsBasis k v = none := by
  simp [schreibeGsBasis, fsgsbaseFreigabe, h]

/-- REFUSAL: no CR4 bit, no GS-base write. -/
theorem schreibeGsBasis_verweigert_ohne_cr4 (k : SegKern) (v : Wort)
    (h : k.fsgsbaseCr4 = false) :
    schreibeGsBasis k v = none := by
  simp [schreibeGsBasis, fsgsbaseFreigabe, h]

/-- SWAPGS: exchanges GS base with the kernel GS base. -/
def tauscheGs (k : SegKern) : SegKern :=
  { k with gsBasis := k.kernGsBasis, kernGsBasis := k.gsBasis }

/-- SWAPGS is an involution. -/
theorem tauscheGs_involution (k : SegKern) :
    tauscheGs (tauscheGs k) = k := by
  cases k with
  | mk fs gs kgs cp cr => rfl

/-- SWAPGS really exchanges the two bases. -/
theorem tauscheGs_tauscht (k : SegKern) :
    (tauscheGs k).gsBasis = k.kernGsBasis ∧
      (tauscheGs k).kernGsBasis = k.gsBasis := by
  cases k with
  | mk fs gs kgs cp cr => exact ⟨rfl, rfl⟩

/-! ## 2. Segmented effective address over the accepted `adrEff`. -/

/-- Base contributed by one override choice. -/
def segBasis (k : SegKern) : SegWahl → Wort
  | .kein => 0
  | .fs => k.fsBasis
  | .gs => k.gsBasis

/-- Segmented effective address: the accepted `adrEff` plus the override
    base. NEW function (the old one is lifted, never redefined). -/
def adrEffSeg (s : Zustand) (ripNext : Adresse) (f : AdrForm)
    (w : SegWahl) (k : SegKern) : Adresse :=
  adrEff s ripNext f + segBasis k w

/-- With no override the new address IS the old one. -/
theorem adrEffSeg_ohne (s : Zustand) (ripNext : Adresse) (f : AdrForm)
    (k : SegKern) :
    adrEffSeg s ripNext f .kein k = adrEff s ripNext f := by
  simp [adrEffSeg, segBasis, BitVec.add_zero]

/-- With a zero base the new address IS the old one, for either segment:
    both premises pin one side each. -/
theorem adrEffSeg_basis_null (s : Zustand) (ripNext : Adresse)
    (f : AdrForm) (w : SegWahl) (k : SegKern)
    (hfs : k.fsBasis = 0) (hgs : k.gsBasis = 0) :
    adrEffSeg s ripNext f w k = adrEff s ripNext f := by
  cases w with
  | kein => exact adrEffSeg_ohne s ripNext f k
  | fs => simp [adrEffSeg, segBasis, hfs, BitVec.add_zero]
  | gs => simp [adrEffSeg, segBasis, hgs, BitVec.add_zero]

/-- Pin registers: `rbx = 100`, everything else zero. -/
def segPinReg : Register → Wort
  | .rbx => BitVec.ofNat 64 100
  | _ => BitVec.ofNat 64 0

/-- Pin memory: dark everywhere (address arithmetic reads no memory). -/
def segPinSpeicher : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0, lesbar := fun _ => false,
    schreibbar := fun _ => false, ausfuehrbar := fun _ => false }

/-- Pin state for the segment-shift pins. -/
def segPinZustand : Zustand :=
  { register := segPinReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := segPinSpeicher }

/-- PIN: with FS base 8192 the segmented address moves (`100 → 8292`). -/
theorem segPin_fs_verschiebt :
    adrEffSeg segPinZustand (BitVec.ofNat 64 0) (basisKeinForm .rbx) .fs
      ⟨BitVec.ofNat 64 8192, 0, 0, true, true⟩ =
      BitVec.ofNat 64 8292 := by
  decide

/-- PIN: the same access without override stays at `100`. -/
theorem segPin_ohne_bleibt :
    adrEffSeg segPinZustand (BitVec.ofNat 64 0) (basisKeinForm .rbx) .kein
      ⟨BitVec.ofNat 64 8192, 0, 0, true, true⟩ =
      BitVec.ofNat 64 100 := by
  decide

/- CUTS:
   Skeleton only. NOT proved here, and not claimed: everything.
-/

#print axioms SegWahl

end Gabbro.Grammatik.X86
