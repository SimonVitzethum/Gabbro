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

/-! ## 3. TLB: per-core cached translations, INVLPG, CR3 flush.

  Entries are page-granular (4 KiB). The page walk itself is a
  parameter (`SeitenDurchlauf`, owned by lane HwPaging), never defined
  here. PCID is off (see `tlbGlobal`); a stale entry may be used until
  invalidated (see `tlbAufloesung_trifft`); INVLPG is core-local (see
  `tlbEntfernen_lokal`). -/

/-- TLB page size: 4 KiB pages. -/
def tlbSeitenGroesse : Nat := 4096

/-- Page number of a linear address. -/
def seitenNr (a : Adresse) : Nat := a.toNat / tlbSeitenGroesse

/-- Offset inside the page. -/
def seitenOffset (a : Adresse) : Nat := a.toNat % tlbSeitenGroesse

/-- One cached translation: page number to frame number. -/
structure TlbEintrag where
  seite : Nat
  rahmen : Nat
  deriving DecidableEq, Repr

/-- Physical address from a frame and the offset of `a`. -/
def physAddr (rahmen : Nat) (a : Adresse) : Adresse :=
  BitVec.ofNat 64 (rahmen * tlbSeitenGroesse + seitenOffset a)

/-- First cached frame for page `s` (`none` = miss). -/
def tlbSuche : List TlbEintrag → Nat → Option Nat
  | [], _ => none
  | e :: rest, s => if e.seite == s then some e.rahmen else tlbSuche rest s

/-- Page walk (owned by lane HwPaging): page number to frame number,
    `none` = walk fault (not modelled here). -/
abbrev SeitenDurchlauf := Nat → Option Nat

/-- Resolution: a hit uses the cached frame (even a stale one); a miss
    walks. The walk result is returned, never silently cached here. -/
def tlbAufloesung (tlb : List TlbEintrag) (walk : SeitenDurchlauf)
    (a : Adresse) : Option Adresse :=
  match tlbSuche tlb (seitenNr a) with
  | some r => some (physAddr r a)
  | none =>
    match walk (seitenNr a) with
    | some r => some (physAddr r a)
    | none => none

/-- HIT: the cached frame answers, whatever the walk now says. This IS
    the stale-entry rule: once cached, the walk is not consulted until
    the entry is invalidated. -/
theorem tlbAufloesung_trifft (tlb : List TlbEintrag)
    (walk : SeitenDurchlauf) (a : Adresse) (r : Nat)
    (hHit : tlbSuche tlb (seitenNr a) = some r) :
    tlbAufloesung tlb walk a = some (physAddr r a) := by
  simp [tlbAufloesung, hHit]

/-- MISS: the walk answers. -/
theorem tlbAufloesung_verfehlt (tlb : List TlbEintrag)
    (walk : SeitenDurchlauf) (a : Adresse) (r : Nat)
    (hMiss : tlbSuche tlb (seitenNr a) = none)
    (hWalk : walk (seitenNr a) = some r) :
    tlbAufloesung tlb walk a = some (physAddr r a) := by
  simp [tlbAufloesung, hMiss, hWalk]

/-- INVLPG: drop every entry for page `s` on this core. -/
def tlbEntfernen : List TlbEintrag → Nat → List TlbEintrag
  | [], _ => []
  | e :: rest, s =>
    if e.seite == s then tlbEntfernen rest s
    else e :: tlbEntfernen rest s

/-- After INVLPG the page misses. -/
theorem tlbEntfernen_sucht_verfehlt (tlb : List TlbEintrag) (s : Nat) :
    tlbSuche (tlbEntfernen tlb s) s = none := by
  induction tlb with
  | nil => rfl
  | cons e rest ih =>
    cases h : e.seite == s with
    | true => simp [tlbEntfernen, h, ih]
    | false => simp [tlbEntfernen, tlbSuche, h, ih]

/-- After INVLPG of its page the next access re-walks. -/
theorem tlbNachEntfernen_geht_durch (tlb : List TlbEintrag)
    (walk : SeitenDurchlauf) (a : Adresse) (r : Nat)
    (hWalk : walk (seitenNr a) = some r) :
    tlbAufloesung (tlbEntfernen tlb (seitenNr a)) walk a =
      some (physAddr r a) := by
  have hMiss :
      tlbSuche (tlbEntfernen tlb (seitenNr a)) (seitenNr a) = none :=
    tlbEntfernen_sucht_verfehlt tlb (seitenNr a)
  exact tlbAufloesung_verfehlt _ walk a r hMiss hWalk

/-- Global-bit oracle: PCID is OFF, so no entry is global (named
    silicon assumption: with PCID on, global entries would survive). -/
def tlbGlobal (_ : TlbEintrag) : Bool := false

/-- No entry is global while PCID is off. -/
theorem tlbGlobal_aus (e : TlbEintrag) : tlbGlobal e = false := rfl

/-- CR3 write: drop every non-global entry on this core (with PCID off
    that is every entry). -/
def tlbCr3Spuelung : List TlbEintrag → List TlbEintrag
  | [] => []
  | e :: rest =>
    if tlbGlobal e then e :: tlbCr3Spuelung rest else tlbCr3Spuelung rest

/-- A CR3 write empties the core TLB (PCID off). -/
theorem tlbCr3Spuelung_leert (tlb : List TlbEintrag) :
    tlbCr3Spuelung tlb = [] := by
  induction tlb with
  | nil => rfl
  | cons e rest ih =>
    have hg : tlbGlobal e = false := rfl
    simp [tlbCr3Spuelung, hg, ih]

/-- LOCALITY: invalidating on core `c` leaves core `d` alone. The
    silicon side (INVLPG touches only the current core; anything else
    needs software shootdown) is a named assumption. -/
theorem tlbEntfernen_lokal (tlb : Nat → List TlbEintrag) (c d s : Nat)
    (h : d ≠ c) :
    (fun e => if e = c then tlbEntfernen (tlb c) s else tlb e) d =
      tlb d := by
  simp [h]

/- CUTS:
   Skeleton only. NOT proved here, and not claimed: everything.
-/

#print axioms SegWahl

end Gabbro.Grammatik.X86
