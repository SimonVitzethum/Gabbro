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

/-! ## 4. Machine connection: segment/TLB state beside the machine.

  The extended machine keeps the coherent `HwMaschine` untouched and
  carries per-core segment state plus per-core TLBs beside it. Every
  extended step preserves the coherent well-formedness, and every
  coherent step embeds exactly. -/

/-- Extended machine: the coherent machine plus per-core segment state
    and per-core TLBs. Profiles and core data stay inside `hw`. -/
structure SegTlbMaschine where
  hw : HwMaschine
  seg : Nat → SegKern
  tlb : Nat → List TlbEintrag

/-- Well-formedness is the coherent well-formedness. -/
def SegTlbWf (m : SegTlbMaschine) : Prop := HwWf m.hw

/-- Family events: gated base writes, SWAPGS, INVLPG, CR3 write, plus a
    lifted coherent step. -/
inductive SegTlbEreignis where
  | wrFs : Nat → Wort → SegTlbEreignis
  | wrGs : Nat → Wort → SegTlbEreignis
  | swapgs : Nat → SegTlbEreignis
  | invlpg : Nat → Adresse → SegTlbEreignis
  | cr3 : Nat → SegTlbEreignis
  | hwSchritt : HwEreignis → SegTlbEreignis
  deriving DecidableEq, Repr

/-- Extended steps: the family moves only its own state; the coherent
    step rides along with segment/TLB state kept. -/
inductive SegTlbSchritt :
    SegTlbMaschine → SegTlbMaschine → SegTlbEreignis → Prop where
  | wrFs {m : SegTlbMaschine} (c : Nat) (v : Wort) (k' : SegKern)
      (h : schreibeFsBasis (m.seg c) v = some k') :
      SegTlbSchritt m
        ⟨m.hw, fun d => if d = c then k' else m.seg d, m.tlb⟩
        (.wrFs c v)
  | wrGs {m : SegTlbMaschine} (c : Nat) (v : Wort) (k' : SegKern)
      (h : schreibeGsBasis (m.seg c) v = some k') :
      SegTlbSchritt m
        ⟨m.hw, fun d => if d = c then k' else m.seg d, m.tlb⟩
        (.wrGs c v)
  | swapgs {m : SegTlbMaschine} (c : Nat) :
      SegTlbSchritt m
        ⟨m.hw, fun d => if d = c then tauscheGs (m.seg c) else m.seg d,
          m.tlb⟩
        (.swapgs c)
  | invlpg {m : SegTlbMaschine} (c : Nat) (a : Adresse) :
      SegTlbSchritt m
        ⟨m.hw, m.seg,
          fun d => if d = c then tlbEntfernen (m.tlb c) (seitenNr a)
            else m.tlb d⟩
        (.invlpg c a)
  | cr3 {m : SegTlbMaschine} (c : Nat) :
      SegTlbSchritt m
        ⟨m.hw, m.seg,
          fun d => if d = c then tlbCr3Spuelung (m.tlb c) else m.tlb d⟩
        (.cr3 c)
  | hw {m : SegTlbMaschine} (m' : HwMaschine) (e : HwEreignis)
      (h : HwSchritt m.hw m' e) :
      SegTlbSchritt m ⟨m', m.seg, m.tlb⟩ (.hwSchritt e)

/-- EXACT EMBEDDING: every coherent step lifts with segment/TLB state
    kept. The old machine is lifted, never redefined. -/
theorem segTlbSchritt_hw_einbettung (m : SegTlbMaschine)
    (m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt m.hw m' e) :
    SegTlbSchritt m ⟨m', m.seg, m.tlb⟩ (.hwSchritt e) :=
  .hw m' e h

/-- Every extended step preserves well-formedness: no case touches
    profiles or core data. -/
theorem segTlbSchritt_wf (m m' : SegTlbMaschine) (e : SegTlbEreignis)
    (h : SegTlbSchritt m m' e) (hwf : SegTlbWf m) : SegTlbWf m' := by
  cases h with
  | wrFs c v k' h => exact hwf
  | wrGs c v k' h => exact hwf
  | swapgs c => exact hwf
  | invlpg c a => exact hwf
  | cr3 c => exact hwf
  | hw m' e h => exact hwSchritt_wf m.hw m' e h hwf

/-- AGREEMENT: a WRFSBASE step installs exactly the gated successor on
    its core and keeps machine and TLBs. -/
theorem segTlb_wrFs_vereinbarung (m : SegTlbMaschine) (c : Nat)
    (v : Wort) (k' : SegKern)
    (h : schreibeFsBasis (m.seg c) v = some k') :
    ∃ m', SegTlbSchritt m m' (.wrFs c v) ∧
      m'.seg c = k' ∧ m'.hw = m.hw ∧ m'.tlb = m.tlb := by
  refine ⟨⟨m.hw, fun d => if d = c then k' else m.seg d, m.tlb⟩,
    .wrFs c v k' h, ?_, rfl, rfl⟩
  simp

/-- AGREEMENT: an INVLPG step drops exactly the page on its core and
    keeps machine and segments. -/
theorem segTlb_invlpg_vereinbarung (m : SegTlbMaschine) (c : Nat)
    (a : Adresse) :
    ∃ m', SegTlbSchritt m m' (.invlpg c a) ∧
      m'.tlb c = tlbEntfernen (m.tlb c) (seitenNr a) ∧
      m'.hw = m.hw ∧ m'.seg = m.seg := by
  refine ⟨⟨m.hw, m.seg,
    fun d => if d = c then tlbEntfernen (m.tlb c) (seitenNr a)
      else m.tlb d⟩, .invlpg c a, ?_, rfl, rfl⟩
  simp

/-- AGREEMENT: a CR3 step flushes exactly its core and keeps the rest. -/
theorem segTlb_cr3_vereinbarung (m : SegTlbMaschine) (c : Nat) :
    ∃ m', SegTlbSchritt m m' (.cr3 c) ∧
      m'.tlb c = tlbCr3Spuelung (m.tlb c) ∧
      m'.hw = m.hw ∧ m'.seg = m.seg := by
  refine ⟨⟨m.hw, m.seg,
    fun d => if d = c then tlbCr3Spuelung (m.tlb c) else m.tlb d⟩,
    .cr3 c, ?_, rfl, rfl⟩
  simp

/-- REFUSAL: with the gate closed no WRFSBASE step exists. -/
theorem segTlb_wrFs_verweigert (m : SegTlbMaschine) (c : Nat)
    (v : Wort)
    (h : fsgsbaseFreigabe (m.seg c) = false) :
    ∀ m', ¬ SegTlbSchritt m m' (.wrFs c v) := by
  intro m' hstep
  cases hstep with
  | wrFs d w k' h2 =>
    have hnone : schreibeFsBasis (m.seg c) v = none := by
      simp [schreibeFsBasis, h]
    rw [hnone] at h2
    cases h2

/-- REFUSAL: with the gate closed no WRGSBASE step exists. -/
theorem segTlb_wrGs_verweigert (m : SegTlbMaschine) (c : Nat)
    (v : Wort)
    (h : fsgsbaseFreigabe (m.seg c) = false) :
    ∀ m', ¬ SegTlbSchritt m m' (.wrGs c v) := by
  intro m' hstep
  cases hstep with
  | wrGs d w k' h2 =>
    have hnone : schreibeGsBasis (m.seg c) v = none := by
      simp [schreibeGsBasis, h]
    rw [hnone] at h2
    cases h2

/-! ## 5. Closed pins: pages, stale use, INVLPG, CR3. -/

/-- Pin: address 8197 lives on page 2 with offset 5. -/
theorem seitenNr_pin_8197 :
    seitenNr (BitVec.ofNat 64 8197) = 2 := by
  decide

/-- Pin: offset of 8197 inside its page is 5. -/
theorem seitenOffset_pin_8197 :
    seitenOffset (BitVec.ofNat 64 8197) = 5 := by
  decide

/-- Pin: frame 7 with offset 5 names 28677. -/
theorem physAddr_pin :
    physAddr 7 (BitVec.ofNat 64 8197) = BitVec.ofNat 64 28677 := by
  decide

/-- PIN: stale use -- the walk moved page 2 to frame 7, but the cached
    frame 3 still answers. -/
theorem tlbAufloesung_veraltet_pin :
    tlbAufloesung [⟨2, 3⟩] (fun s => if s == 2 then some 7 else none)
      (BitVec.ofNat 64 8197) =
      some (physAddr 3 (BitVec.ofNat 64 8197)) := by
  decide

/-- PIN: INVLPG drops the page entries and keeps the rest. -/
theorem tlbEntfernen_pin :
    tlbEntfernen [⟨2, 3⟩, ⟨2, 5⟩, ⟨4, 9⟩] 2 = [⟨4, 9⟩] := by
  decide

/-- PIN: after INVLPG the walk (frame 7) answers. -/
theorem tlbNachEntfernen_pin :
    tlbAufloesung
      (tlbEntfernen [⟨2, 3⟩] 2)
      (fun s => if s == 2 then some 7 else none)
      (BitVec.ofNat 64 8197) =
      some (physAddr 7 (BitVec.ofNat 64 8197)) := by
  decide

/-- PIN: a CR3 write empties the core TLB. -/
theorem tlbCr3Spuelung_pin :
    tlbCr3Spuelung [⟨2, 3⟩, ⟨4, 9⟩] = [] := by
  decide

/-! ## 6. Reached two-core witness.

  Core 0 accesses the window through FS (`rbx + FS = 8 + 8192 = 8200`)
  with page 2 cached; core 1 idles with an empty TLB. The buffered
  store is visible by forwarding to the owner only; the drain changes
  shared memory 0 to 42; INVLPG on core 0 re-walks. -/

/-- Witness bytes: zero everywhere (the drain installs 42). -/
def witBytes : Adresse → Byte := fun _ => BitVec.ofNat 8 0

/-- Witness data window: sixteen bytes at 8192, read/write. -/
def witFenster (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8208)

/-- Witness memory: the window is read/write, nothing executable. -/
def witMem : Speicher :=
  { bytes := witBytes, lesbar := witFenster,
    schreibbar := witFenster, ausfuehrbar := fun _ => false }

/-- Witness core-0 registers: `rbx = 8` (offset into the window). -/
def witReg0 : Register → Wort
  | .rbx => BitVec.ofNat 64 8
  | .rsp => BitVec.ofNat 64 8704
  | _ => BitVec.ofNat 64 0

/-- Witness core data: core 0 runs at 4096, core 1 idles on the data. -/
def witKern : Nat → HwKern
  | 0 => ⟨witReg0, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness coherent machine: shared window memory, two cores, empty
    buffers, full silicon. -/
def witHw : HwMaschine :=
  ⟨witMem, witKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed. -/
theorem witHw_wf : HwWf witHw := by
  intro c f _
  cases f <;> rfl

/-- Witness segment state: core 0 carries FS base 8192 enabled, core 1
    carries nothing. -/
def witSeg : Nat → SegKern
  | 0 => ⟨BitVec.ofNat 64 8192, BitVec.ofNat 64 0, BitVec.ofNat 64 0,
      true, true⟩
  | _ => ⟨BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 0,
      false, false⟩

/-- Witness TLBs: core 0 caches page 2 to frame 2, core 1 is empty. -/
def witTlb : Nat → List TlbEintrag
  | 0 => [⟨2, 2⟩]
  | _ => []

/-- Witness extended machine. -/
def witM : SegTlbMaschine := ⟨witHw, witSeg, witTlb⟩

/-- The witness is well-formed. -/
theorem witM_wf : SegTlbWf witM := witHw_wf

/-- Witness walk: page 2 maps to frame 2 (identity on the window). -/
def witWalk : SeitenDurchlauf :=
  fun s => if s == 2 then some 2 else none

/-- Witness address: segmented `rbx + FS = 8 + 8192 = 8200`. -/
def witAddr : Adresse := BitVec.ofNat 64 8200

/-- JOINT WITNESS joining every leg: segmented address, TLB hit,
    owner-only forwarding of the buffered store, drain changing shared
    memory 0 to 42, and a reached INVLPG step with re-walk. -/
theorem segTlb_zeuge :
    SegTlbWf witM ∧
    adrEffSeg (projZustand witM.hw 0) (BitVec.ofNat 64 0)
      (basisKeinForm .rbx) .fs (witM.seg 0) = witAddr ∧
    tlbAufloesung (witM.tlb 0) witWalk witAddr = some witAddr ∧
    (issueByte (tsoAnsicht witM.hw) 0 witAddr
      (BitVec.ofNat 8 42)).map (fun s => loadByte s 0 witAddr) =
      some (some (BitVec.ofNat 8 42)) ∧
    (issueByte (tsoAnsicht witM.hw) 0 witAddr
      (BitVec.ofNat 8 42)).map (fun s => loadByte s 1 witAddr) =
      some (some (BitVec.ofNat 8 0)) ∧
    ((issueByte (tsoAnsicht witM.hw) 0 witAddr
      (BitVec.ofNat 8 42)).bind
      (fun s => flushKern s 0)).map (fun s => s.mem.bytes witAddr) =
      some (BitVec.ofNat 8 42) ∧
    witM.hw.mem.bytes witAddr = BitVec.ofNat 8 0 ∧
    ∃ m2, SegTlbSchritt witM m2 (.invlpg 0 witAddr) ∧
      tlbAufloesung (m2.tlb 0) witWalk witAddr = some witAddr := by
  refine ⟨witM_wf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · refine ⟨⟨witHw, witM.seg,
      fun d => if d = 0 then tlbEntfernen (witM.tlb 0) (seitenNr witAddr)
        else witM.tlb d⟩, .invlpg 0 witAddr, ?_⟩
    decide

/- CUTS:
   Skeleton only. NOT proved here, and not claimed: everything.
-/

#print axioms SegWahl

end Gabbro.Grammatik.X86
