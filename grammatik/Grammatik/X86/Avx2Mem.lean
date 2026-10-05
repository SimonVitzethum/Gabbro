/-
  File:      Grammatik/X86/Avx2Mem.lean
  Subject:   AVX2 32-byte memory accesses (VMOVDQU/VMOVDQA) on the coherent
             TSO machine.

  Lane 1243 (Tier 3, first OPTIONAL selected-CPU profile): the two 256-bit
  memory shapes -- unaligned VMOVDQU (no alignment requirement) and aligned
  VMOVDQA (32-byte alignment, else #GP) -- as footprint-checked accesses on
  `HwMaschine`/`HwSchritt` (lane 660) over the accepted canonical TSO byte
  equations (`TSO`: `issueByte`/`loadByte`/`flushKern`). A 32-byte store is
  a sequence of byte issues in the acting core's buffer with the accepted
  forwarding and partial-overlap rules; page-crossing (permission) faults
  leave memory unchanged; NO whole-vector atomicity is claimed (tearing
  table: the access may be observed in parts, as the accepted byte model
  says). Values are two accepted 128-bit halves (`Vektor`); entry bytes ARE
  accepted chunk bytes by construction. Enabled only by the NAMED CPU
  profile plus CPUID/XCR0/OS-state gates; absent form = refused encoding
  (DIRECT-COMPILER-DESIGN §§2C/2D/6). Sibling AVX2 lanes (Vex, Ops, State)
  are not used here; YMM register-file binding stays with the State lane.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.HardwareExecution
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.Vektor
import Grammatik.X86.FeatureProfile
import Grammatik.X86.VectorHardwareProfile
import Grammatik.X86.VectorFootprints
import Grammatik.X86.Ausfuehrung

namespace Gabbro.Grammatik.X86

/-- The two selected 256-bit memory shapes: aligned (VMOVDQA) and
    unaligned (VMOVDQU). No other AVX2 memory form is admitted here. -/
inductive Avx2MemForm where
  | ausgerichtet
  | unausgerichtet
  deriving DecidableEq, Repr

/-! ## 1. Alignment faults: VMOVDQA needs 32-byte alignment (#GP),
   VMOVDQU never faults on alignment. This classifies the hardware
   trap; it is not a validator admission. -/

/-- #GP fault predicate: the aligned form (VMOVDQA, VEX.256) faults
    exactly on 32-byte-misaligned addresses; the unaligned form
    (VMOVDQU) never faults on alignment. -/
def avx2GpFehler (a : Adresse) : Avx2MemForm → Bool
  | .ausgerichtet => decide (a.toNat % 32 ≠ 0)
  | .unausgerichtet => false

/-- The unaligned form never faults on alignment, at any address. -/
theorem avx2Gp_nie_unausgerichtet (a : Adresse) :
    avx2GpFehler a .unausgerichtet = false := rfl

/-- The aligned form faults sixteen bytes past a 32-byte boundary. -/
theorem avx2Gp_ausgerichtet_fehler :
    avx2GpFehler (BitVec.ofNat 64 16) .ausgerichtet = true := by
  decide

/-- The aligned form is clean at the boundary and one line further. -/
theorem avx2Gp_ausgerichtet_ok :
    avx2GpFehler (BitVec.ofNat 64 0) .ausgerichtet = false ∧
      avx2GpFehler (BitVec.ofNat 64 32) .ausgerichtet = false := by
  exact ⟨by decide, by decide⟩

/-! ## 2. YMM values as two accepted 128-bit halves.

  No YMM register file exists here (binding stays with the State
  lane); the 256-bit value is two accepted `Vektor` halves, each two
  accepted words. Entry bytes ARE accepted chunk bytes by
  construction (`wortByte` over `vLo`/`vHi`). -/

/-- A 256-bit AVX2 memory value: low and high accepted 128-bit halves. -/
structure Avx2Vektor where
  lo : Vektor
  hi : Vektor
  deriving DecidableEq, Repr

/-- The four canonical 64-bit chunk words: low half then high half,
    each low word first -- the same order the accepted `vecWrite`
    uses per half. -/
def avx2Wort (v : Avx2Vektor) : Nat → Wort
  | 0 => vLo v.lo
  | 1 => vHi v.lo
  | 2 => vLo v.hi
  | _ => vHi v.hi

/-- The four canonical chunk bases: contiguous eight-byte chunks,
    the upper pair through the accepted second-chunk address. -/
def avx2Chunk (a : Adresse) : Nat → Adresse
  | 0 => a
  | 1 => vecHiAddr a
  | 2 => addrOff a 16
  | _ => vecHiAddr (addrOff a 16)

/-! ## 3. The thirty-two canonical byte entries of one YMM word.

  Eight bytes per chunk, four chunks oldest first -- the same chunk
  order the accepted `vecWrite` uses per half, so entry bytes ARE
  chunk bytes by construction (`rfl`). Thirty-two per-byte TSO
  events, never one atomic occurrence. -/

/-- Chunk-zero entries: the low word of the low half. -/
def avx2EintraegeC0 (a : Adresse) (v : Avx2Vektor) : List TSOEintrag :=
  [⟨addrOff a 0, wortByte (vLo v.lo) 0⟩,
    ⟨addrOff a 1, wortByte (vLo v.lo) 1⟩,
    ⟨addrOff a 2, wortByte (vLo v.lo) 2⟩,
    ⟨addrOff a 3, wortByte (vLo v.lo) 3⟩,
    ⟨addrOff a 4, wortByte (vLo v.lo) 4⟩,
    ⟨addrOff a 5, wortByte (vLo v.lo) 5⟩,
    ⟨addrOff a 6, wortByte (vLo v.lo) 6⟩,
    ⟨addrOff a 7, wortByte (vLo v.lo) 7⟩]

/-- Chunk-one entries: the high word of the low half. -/
def avx2EintraegeC1 (a : Adresse) (v : Avx2Vektor) : List TSOEintrag :=
  [⟨addrOff (vecHiAddr a) 0, wortByte (vHi v.lo) 0⟩,
    ⟨addrOff (vecHiAddr a) 1, wortByte (vHi v.lo) 1⟩,
    ⟨addrOff (vecHiAddr a) 2, wortByte (vHi v.lo) 2⟩,
    ⟨addrOff (vecHiAddr a) 3, wortByte (vHi v.lo) 3⟩,
    ⟨addrOff (vecHiAddr a) 4, wortByte (vHi v.lo) 4⟩,
    ⟨addrOff (vecHiAddr a) 5, wortByte (vHi v.lo) 5⟩,
    ⟨addrOff (vecHiAddr a) 6, wortByte (vHi v.lo) 6⟩,
    ⟨addrOff (vecHiAddr a) 7, wortByte (vHi v.lo) 7⟩]

/-- Chunk-two entries: the low word of the high half. -/
def avx2EintraegeC2 (a : Adresse) (v : Avx2Vektor) : List TSOEintrag :=
  [⟨addrOff (addrOff a 16) 0, wortByte (vLo v.hi) 0⟩,
    ⟨addrOff (addrOff a 16) 1, wortByte (vLo v.hi) 1⟩,
    ⟨addrOff (addrOff a 16) 2, wortByte (vLo v.hi) 2⟩,
    ⟨addrOff (addrOff a 16) 3, wortByte (vLo v.hi) 3⟩,
    ⟨addrOff (addrOff a 16) 4, wortByte (vLo v.hi) 4⟩,
    ⟨addrOff (addrOff a 16) 5, wortByte (vLo v.hi) 5⟩,
    ⟨addrOff (addrOff a 16) 6, wortByte (vLo v.hi) 6⟩,
    ⟨addrOff (addrOff a 16) 7, wortByte (vLo v.hi) 7⟩]

/-- Chunk-three entries: the high word of the high half, eight
    bytes past chunk two through the accepted second-chunk address. -/
def avx2EintraegeC3 (a : Adresse) (v : Avx2Vektor) : List TSOEintrag :=
  [⟨addrOff (vecHiAddr (addrOff a 16)) 0, wortByte (vHi v.hi) 0⟩,
    ⟨addrOff (vecHiAddr (addrOff a 16)) 1, wortByte (vHi v.hi) 1⟩,
    ⟨addrOff (vecHiAddr (addrOff a 16)) 2, wortByte (vHi v.hi) 2⟩,
    ⟨addrOff (vecHiAddr (addrOff a 16)) 3, wortByte (vHi v.hi) 3⟩,
    ⟨addrOff (vecHiAddr (addrOff a 16)) 4, wortByte (vHi v.hi) 4⟩,
    ⟨addrOff (vecHiAddr (addrOff a 16)) 5, wortByte (vHi v.hi) 5⟩,
    ⟨addrOff (vecHiAddr (addrOff a 16)) 6, wortByte (vHi v.hi) 6⟩,
    ⟨addrOff (vecHiAddr (addrOff a 16)) 7, wortByte (vHi v.hi) 7⟩]

/-- The thirty-two canonical byte-store entries of `v` at `a`, oldest
    first: the four chunk lists concatenated. -/
def avx2Eintraege (a : Adresse) (v : Avx2Vektor) : List TSOEintrag :=
  avx2EintraegeC0 a v ++ avx2EintraegeC1 a v ++
    avx2EintraegeC2 a v ++ avx2EintraegeC3 a v

/-- Thirty-two entries, no more: the YMM shape is exact. -/
theorem avx2Eintraege_laenge (a : Adresse) (v : Avx2Vektor) :
    (avx2Eintraege a v).length = 32 := rfl

/-- The low sixteen entries: the low half's two chunks. -/
def avx2EintraegeLo (a : Adresse) (v : Avx2Vektor) : List TSOEintrag :=
  avx2EintraegeC0 a v ++ avx2EintraegeC1 a v

/-- The high sixteen entries: the high half's two chunks. -/
def avx2EintraegeHi (a : Adresse) (v : Avx2Vektor) : List TSOEintrag :=
  avx2EintraegeC2 a v ++ avx2EintraegeC3 a v

/-- The thirty-two split into low then high halves. -/
theorem avx2Eintraege_zerlegt (a : Adresse) (v : Avx2Vektor) :
    avx2Eintraege a v =
      avx2EintraegeLo a v ++ avx2EintraegeHi a v := by
  simp [avx2Eintraege, avx2EintraegeLo, avx2EintraegeHi,
    List.append_assoc]

/-! ## 4. Footprint: every entry sits in the 32-byte footprint.

  The footprint is two accepted 16-byte `vecFuss` halves back to
  back -- the accepted footprint lifted, never redefined. -/

/-- The 32-byte footprint of a YMM access: two accepted 16-byte
    `vecFuss` halves back to back. Per-byte events, not one atomic
    occurrence. -/
def avx2Fuss (a : Adresse) : List Adresse :=
  vecFuss a ++ vecFuss (addrOff a 16)

/-- The 32-byte footprint is two accepted 16-byte footprints. -/
theorem avx2Fuss_halb (a : Adresse) :
    avx2Fuss a = vecFuss a ++ vecFuss (addrOff a 16) := rfl

/-- Every chunk-zero entry address lies in the footprint. -/
theorem avx2Eintrag_mem_c0 (a : Adresse) (k : Nat) (hk : k < 8) :
    addrOff a k ∈ avx2Fuss a := by
  unfold avx2Fuss
  simp only [List.mem_append]
  exact Or.inl (vecFuss_mem a _ |>.mpr (Or.inl (fuss_mem_offset a k hk)))

/-- Every chunk-one entry address lies in the footprint. -/
theorem avx2Eintrag_mem_c1 (a : Adresse) (k : Nat) (hk : k < 8) :
    addrOff (vecHiAddr a) k ∈ avx2Fuss a := by
  unfold avx2Fuss
  simp only [List.mem_append]
  exact Or.inl (vecFuss_mem a _ |>.mpr (Or.inr (fuss_mem_offset _ k hk)))

/-- Every chunk-two entry address lies in the footprint. -/
theorem avx2Eintrag_mem_c2 (a : Adresse) (k : Nat) (hk : k < 8) :
    addrOff (addrOff a 16) k ∈ avx2Fuss a := by
  unfold avx2Fuss
  simp only [List.mem_append]
  exact Or.inr (vecFuss_mem _ _ |>.mpr (Or.inl (fuss_mem_offset _ k hk)))

/-- Every chunk-three entry address lies in the footprint. -/
theorem avx2Eintrag_mem_c3 (a : Adresse) (k : Nat) (hk : k < 8) :
    addrOff (vecHiAddr (addrOff a 16)) k ∈ avx2Fuss a := by
  unfold avx2Fuss
  simp only [List.mem_append]
  exact Or.inr (vecFuss_mem _ _ |>.mpr (Or.inr (fuss_mem_offset _ k hk)))

/-! ## 5. No-wrap over 32 bytes and chunk separation.

  Under `OhneUmbruch32` the four chunks sit in one Nat interval, so
  all separation is `omega` over the accepted `addrOff_nat`, exactly
  like the accepted `vecChunks_disjoint`. -/

/-- No-wrap over all four eight-byte chunks: 32 bytes from the base. -/
def OhneUmbruch32 (a : Adresse) : Prop := a.toNat + 32 ≤ 2 ^ 64

/-- Chunk bases as Nat offsets: chunk `c` starts at `8 * c`. -/
theorem avx2Chunk_nat (a : Adresse) (h : OhneUmbruch32 a) (c : Nat)
    (hc : c < 4) : (avx2Chunk a c).toNat = a.toNat + 8 * c := by
  have h4 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · simp [avx2Chunk]
  · show (vecHiAddr a).toNat = a.toNat + 8 * 1
    have e := addrOff_nat a 8 (by unfold OhneUmbruch32 at h; omega)
    unfold vecHiAddr
    omega
  · show (addrOff a 16).toNat = a.toNat + 8 * 2
    have e := addrOff_nat a 16 (by unfold OhneUmbruch32 at h; omega)
    omega
  · show (vecHiAddr (addrOff a 16)).toNat = a.toNat + 8 * 3
    have e16 := addrOff_nat a 16 (by unfold OhneUmbruch32 at h; omega)
    have e8 := addrOff_nat (addrOff a 16) 8
      (by unfold OhneUmbruch32 at h; omega)
    unfold vecHiAddr
    omega

/-- Every chunk base is itself wrap-free for its eight bytes. -/
theorem avx2Chunk_ohneUmbruch (a : Adresse) (h : OhneUmbruch32 a)
    (c : Nat) (hc : c < 4) : OhneUmbruch (avx2Chunk a c) := by
  unfold OhneUmbruch
  have e := avx2Chunk_nat a h c hc
  unfold OhneUmbruch32 at h
  omega

/-- Later chunks start after earlier ones end: the four chunks are
    pairwise disjoint. Every premise is used. -/
theorem avx2Chunk_disjunkt (a : Adresse) (h : OhneUmbruch32 a)
    (c d : Nat) (hc : c < 4) (hd : d < 4) (hlt : c < d) :
    Disjunkt (avx2Chunk a c) (avx2Chunk a d) := by
  have h4c : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  have h4d : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  have e := avx2Chunk_nat a h c hc
  have f := avx2Chunk_nat a h d hd
  have hcU := avx2Chunk_ohneUmbruch a h c hc
  have hdU := avx2Chunk_ohneUmbruch a h d hd
  rcases h4c with rfl | rfl | rfl | rfl <;>
    rcases h4d with rfl | rfl | rfl | rfl
  · omega
  · exact disjunkt_von_intervallen _ _ hcU hdU (Or.inl (by omega))
  · exact disjunkt_von_intervallen _ _ hcU hdU (Or.inl (by omega))
  · exact disjunkt_von_intervallen _ _ hcU hdU (Or.inl (by omega))
  · omega
  · omega
  · exact disjunkt_von_intervallen _ _ hcU hdU (Or.inl (by omega))
  · exact disjunkt_von_intervallen _ _ hcU hdU (Or.inl (by omega))
  · omega
  · omega
  · omega
  · exact disjunkt_von_intervallen _ _ hcU hdU (Or.inl (by omega))
  · omega
  · omega
  · omega
  · omega

/-- Chunk-zero entries are chunk-zero bytes. -/
theorem avx2Eintrag_klass_c0 (a : Adresse) (v : Avx2Vektor)
    (e : TSOEintrag) (hmem : e ∈ avx2EintraegeC0 a v) :
    ∃ k, k < 8 ∧ e = ⟨addrOff a k, wortByte (vLo v.lo) k⟩ := by
  unfold avx2EintraegeC0 at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨5, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨7, by decide, rfl⟩

/-- Chunk-one entries are chunk-one bytes. -/
theorem avx2Eintrag_klass_c1 (a : Adresse) (v : Avx2Vektor)
    (e : TSOEintrag) (hmem : e ∈ avx2EintraegeC1 a v) :
    ∃ k, k < 8 ∧
      e = ⟨addrOff (vecHiAddr a) k, wortByte (vHi v.lo) k⟩ := by
  unfold avx2EintraegeC1 at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨5, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨7, by decide, rfl⟩

/-- Chunk-two entries are chunk-two bytes. -/
theorem avx2Eintrag_klass_c2 (a : Adresse) (v : Avx2Vektor)
    (e : TSOEintrag) (hmem : e ∈ avx2EintraegeC2 a v) :
    ∃ k, k < 8 ∧
      e = ⟨addrOff (addrOff a 16) k, wortByte (vLo v.hi) k⟩ := by
  unfold avx2EintraegeC2 at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨5, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨7, by decide, rfl⟩

/-- Chunk-three entries are chunk-three bytes. -/
theorem avx2Eintrag_klass_c3 (a : Adresse) (v : Avx2Vektor)
    (e : TSOEintrag) (hmem : e ∈ avx2EintraegeC3 a v) :
    ∃ k, k < 8 ∧
      e = ⟨addrOff (vecHiAddr (addrOff a 16)) k,
        wortByte (vHi v.hi) k⟩ := by
  unfold avx2EintraegeC3 at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨5, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨7, by decide, rfl⟩

/-- Every entry is one chunk byte: classification into the four
    chunks, via binary splits (no associativity assumed). -/
theorem avx2Eintrag_klass (a : Adresse) (v : Avx2Vektor)
    (e : TSOEintrag) (hmem : e ∈ avx2Eintraege a v) :
    (∃ k, k < 8 ∧ e = ⟨addrOff a k, wortByte (vLo v.lo) k⟩) ∨
    (∃ k, k < 8 ∧
      e = ⟨addrOff (vecHiAddr a) k, wortByte (vHi v.lo) k⟩) ∨
    (∃ k, k < 8 ∧
      e = ⟨addrOff (addrOff a 16) k, wortByte (vLo v.hi) k⟩) ∨
    (∃ k, k < 8 ∧
      e = ⟨addrOff (vecHiAddr (addrOff a 16)) k,
        wortByte (vHi v.hi) k⟩) := by
  unfold avx2Eintraege at hmem
  have h := List.mem_append.mp hmem
  rcases h with h012 | h3
  · have h := List.mem_append.mp h012
    rcases h with h01 | h2
    · have h := List.mem_append.mp h01
      rcases h with h0 | h1
      · exact Or.inl (avx2Eintrag_klass_c0 a v e h0)
      · apply Or.inr; apply Or.inl
        exact avx2Eintrag_klass_c1 a v e h1
    · apply Or.inr; apply Or.inr; apply Or.inl
      exact avx2Eintrag_klass_c2 a v e h2
  · apply Or.inr; apply Or.inr; apply Or.inr
    exact avx2Eintrag_klass_c3 a v e h3

/-- Every one of the thirty-two entries sits in the footprint. -/
theorem avx2Eintraege_mem_fuss (a : Adresse) (v : Avx2Vektor)
    (e : TSOEintrag) (hmem : e ∈ avx2Eintraege a v) :
    e.addr ∈ avx2Fuss a := by
  rcases avx2Eintrag_klass a v e hmem with
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact avx2Eintrag_mem_c0 a k hk
  · exact avx2Eintrag_mem_c1 a k hk
  · exact avx2Eintrag_mem_c2 a k hk
  · exact avx2Eintrag_mem_c3 a k hk

/-- The thirty-two entries name pairwise-distinct addresses: same
    address means same entry (hence same byte). Needs the 32-byte
    no-wrap so the four chunks stay apart. -/
theorem avx2Eintraege_nodup_addr (a : Adresse) (h : OhneUmbruch32 a)
    (v : Avx2Vektor) :
    ∀ e1 ∈ avx2Eintraege a v, ∀ e2 ∈ avx2Eintraege a v,
      e1.addr = e2.addr → e1 = e2 := by
  intro e1 h1 e2 h2 heq
  rcases avx2Eintrag_klass a v e1 h1 with
      ⟨k1, hk1, rfl⟩ | ⟨k1, hk1, rfl⟩ | ⟨k1, hk1, rfl⟩ | ⟨k1, hk1, rfl⟩ <;>
    rcases avx2Eintrag_klass a v e2 h2 with
      ⟨k2, hk2, rfl⟩ | ⟨k2, hk2, rfl⟩ | ⟨k2, hk2, rfl⟩ | ⟨k2, hk2, rfl⟩
  · have hkk : k1 = k2 := addrOff_inj8 hk1 hk2 heq
    subst hkk
    rfl
  · exact absurd heq (avx2Chunk_disjunkt a h 0 1
      (by decide) (by decide) (by decide) k1 k2 hk1 hk2)
  · exact absurd heq (avx2Chunk_disjunkt a h 0 2
      (by decide) (by decide) (by decide) k1 k2 hk1 hk2)
  · exact absurd heq (avx2Chunk_disjunkt a h 0 3
      (by decide) (by decide) (by decide) k1 k2 hk1 hk2)
  · exact absurd heq (Ne.symm (avx2Chunk_disjunkt a h 0 1
      (by decide) (by decide) (by decide) k2 k1 hk2 hk1))
  · have hkk : k1 = k2 := addrOff_inj8 hk1 hk2 heq
    subst hkk
    rfl
  · exact absurd heq (avx2Chunk_disjunkt a h 1 2
      (by decide) (by decide) (by decide) k1 k2 hk1 hk2)
  · exact absurd heq (avx2Chunk_disjunkt a h 1 3
      (by decide) (by decide) (by decide) k1 k2 hk1 hk2)
  · exact absurd heq (Ne.symm (avx2Chunk_disjunkt a h 0 2
      (by decide) (by decide) (by decide) k2 k1 hk2 hk1))
  · exact absurd heq (Ne.symm (avx2Chunk_disjunkt a h 1 2
      (by decide) (by decide) (by decide) k2 k1 hk2 hk1))
  · have hkk : k1 = k2 := addrOff_inj8 hk1 hk2 heq
    subst hkk
    rfl
  · exact absurd heq (avx2Chunk_disjunkt a h 2 3
      (by decide) (by decide) (by decide) k1 k2 hk1 hk2)
  · exact absurd heq (Ne.symm (avx2Chunk_disjunkt a h 0 3
      (by decide) (by decide) (by decide) k2 k1 hk2 hk1))
  · exact absurd heq (Ne.symm (avx2Chunk_disjunkt a h 1 3
      (by decide) (by decide) (by decide) k2 k1 hk2 hk1))
  · exact absurd heq (Ne.symm (avx2Chunk_disjunkt a h 2 3
      (by decide) (by decide) (by decide) k2 k1 hk2 hk1))
  · have hkk : k1 = k2 := addrOff_inj8 hk1 hk2 heq
    subst hkk
    rfl

/-! ## 6. The named-profile gate: Tier 3 is opt-in.

  The 256-bit forms are enabled ONLY by the NAMED selected-CPU
  profile (`avx2ProfilName`) AND the accepted CPUID/XCR0/OS-state
  readiness (AVX silicon bit, XCR0 XMM+YMM, control freedom plus
  OSXSAVE, finite packed-tier admission carrying OS vector state).
  Absent form = refused encoding: every missing side refuses. -/

/-- The one selected-CPU profile name that enables VEX.256 forms. -/
def avx2ProfilName : Nat := 7

/-- A named selected-CPU profile: its name is the whole claim. -/
structure Avx2Profil where
  name : Nat
  deriving DecidableEq, Repr

/-- The profile enables the tier exactly under its name. -/
def avx2ProfilFreigegeben (p : Avx2Profil) : Bool :=
  decide (p.name = avx2ProfilName)

/-- Full admission for a 256-bit memory access: the named profile AND
    AVX CPU/XCR0 readiness AND control freedom with OSXSAVE AND the
    finite packed-tier admission. Either side alone admits nothing. -/
def avx2MemZugelassen (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil) : Bool :=
  avx2ProfilFreigegeben p && stufenCpuBereit cpu x .avx256 &&
    kontrollSseFrei k && k.cr4Osxsave &&
    merkmalZugelassen hw b .paketInt128

/-- Admission needs the named profile. -/
theorem avx2Mem_braucht_profil (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil)
    (h : avx2MemZugelassen hw b cpu x k p = true) :
    avx2ProfilFreigegeben p = true := by
  simp only [avx2MemZugelassen, Bool.and_eq_true] at h
  exact h.1.1.1.1

/-- Admission needs AVX CPU/XCR0 readiness. -/
theorem avx2Mem_braucht_cpu (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil)
    (h : avx2MemZugelassen hw b cpu x k p = true) :
    stufenCpuBereit cpu x .avx256 = true := by
  simp only [avx2MemZugelassen, Bool.and_eq_true] at h
  exact h.1.1.1.2

/-- Admission needs control-register freedom. -/
theorem avx2Mem_braucht_kontrolle (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil)
    (h : avx2MemZugelassen hw b cpu x k p = true) :
    kontrollSseFrei k = true := by
  simp only [avx2MemZugelassen, Bool.and_eq_true] at h
  exact h.1.1.2

/-- Admission needs the finite packed-tier admission. -/
theorem avx2Mem_braucht_merkmal (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil)
    (h : avx2MemZugelassen hw b cpu x k p = true) :
    merkmalZugelassen hw b .paketInt128 = true := by
  simp only [avx2MemZugelassen, Bool.and_eq_true] at h
  exact h.2

/-- A foreign profile name refuses, whatever the rest claims. -/
theorem avx2Mem_ohne_profil (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil) (h : avx2ProfilFreigegeben p = false) :
    avx2MemZugelassen hw b cpu x k p = false := by
  simp [avx2MemZugelassen, h]

/-- Missing AVX CPU/XCR0 readiness refuses. -/
theorem avx2Mem_ohne_cpu (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil) (h : stufenCpuBereit cpu x .avx256 = false) :
    avx2MemZugelassen hw b cpu x k p = false := by
  simp [avx2MemZugelassen, h]

/-- Set control bits (emulation or task-switch) refuse. -/
theorem avx2Mem_ohne_kontrolle (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil) (h : kontrollSseFrei k = false) :
    avx2MemZugelassen hw b cpu x k p = false := by
  simp [avx2MemZugelassen, h]

/-- A refused finite profile refuses, however ready the rest is. -/
theorem avx2Mem_ohne_merkmal (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil)
    (h : merkmalZugelassen hw b .paketInt128 = false) :
    avx2MemZugelassen hw b cpu x k p = false := by
  simp [avx2MemZugelassen, h]

/-- Witness silicon: SSE2 present AND AVX present (refused row
    needs its bit). -/
def avx2WitCpu : CpuMerkmal := ⟨true, true⟩

/-- Witness XCR0: x87, SSE and AVX state set. -/
def avx2WitXcr0 : Xcr0Bild := ⟨true, true, true⟩

/-- The witness profile: exactly the named one. -/
def avx2WitProfil : Avx2Profil := ⟨avx2ProfilName⟩

/-- The named profile is enabled under its name. -/
theorem avx2WitProfil_freigegeben :
    avx2ProfilFreigegeben avx2WitProfil = true := by
  decide

/-- The full gate admits at the witness readiness. -/
theorem avx2Wit_gate :
    avx2MemZugelassen basisHw basisBereit avx2WitCpu avx2WitXcr0
      basisKontrolle avx2WitProfil = true := by
  decide

/-- NEGATIVE: the baseline CPU (no AVX bit) refuses. -/
theorem avx2Wit_neg_cpu :
    avx2MemZugelassen basisHw basisBereit basisCpu avx2WitXcr0
      basisKontrolle avx2WitProfil = false :=
  avx2Mem_ohne_cpu _ _ _ _ _ _
    (by simp [stufenCpuBereit, basisCpu])

/-- NEGATIVE: the baseline XCR0 (no AVX state) refuses. -/
theorem avx2Wit_neg_xcr0 :
    avx2MemZugelassen basisHw basisBereit avx2WitCpu basisXcr0
      basisKontrolle avx2WitProfil = false :=
  avx2Mem_ohne_cpu _ _ _ _ _ _
    (by simp [stufenCpuBereit, basisXcr0, xcr0AvxBereit])

/-- NEGATIVE: a foreign profile name refuses. -/
theorem avx2Wit_neg_profil :
    avx2MemZugelassen basisHw basisBereit avx2WitCpu avx2WitXcr0
      basisKontrolle ⟨0⟩ = false :=
  avx2Mem_ohne_profil _ _ _ _ _ _ (by decide)

/-! ## 7. Stores as thirty-two buffered byte issues.

  The 32-byte store is NEVER the direct two-`vecWrite` effect: it is
  `issueListe` over `avx2Eintraege`. One refused byte fails the whole
  access with memory unchanged (`none` carries no state). -/

/-- One byte of a writable chunk is writable. -/
theorem avx2Schreibbar8_einzeln (m : Speicher) (b : Adresse) (k : Nat)
    (hk : k < 8) (h : schreibbar8 m b = true) :
    m.schreibbar (addrOff b k) = true := by
  unfold schreibbar8 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have h8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 := by
    omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    assumption

/-- One byte of a readable chunk is readable. -/
theorem avx2Lesbar8_einzeln (m : Speicher) (b : Adresse) (k : Nat)
    (hk : k < 8) (h : lesbar8 m b = true) :
    m.lesbar (addrOff b k) = true := by
  unfold lesbar8 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have h8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 := by
    omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    assumption

/-- Write permission at any of the four chunk bytes, from the four
    chunk permissions. -/
theorem avx2Schreibbar_einzeln (m : Speicher) (a : Adresse)
    (c k : Nat) (hc : c < 4) (hk : k < 8)
    (h0 : schreibbar8 m a = true)
    (h1 : schreibbar8 m (vecHiAddr a) = true)
    (h2 : schreibbar8 m (addrOff a 16) = true)
    (h3 : schreibbar8 m (vecHiAddr (addrOff a 16)) = true) :
    m.schreibbar (addrOff (avx2Chunk a c) k) = true := by
  have h4 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · show m.schreibbar (addrOff a k) = true
    exact avx2Schreibbar8_einzeln m a k hk h0
  · show m.schreibbar (addrOff (vecHiAddr a) k) = true
    exact avx2Schreibbar8_einzeln m (vecHiAddr a) k hk h1
  · show m.schreibbar (addrOff (addrOff a 16) k) = true
    exact avx2Schreibbar8_einzeln m (addrOff a 16) k hk h2
  · show m.schreibbar (addrOff (vecHiAddr (addrOff a 16)) k) = true
    exact avx2Schreibbar8_einzeln m (vecHiAddr (addrOff a 16)) k hk h3

/-- Read permission at any of the four chunk bytes, from the four
    chunk permissions. -/
theorem avx2Lesbar_einzeln (m : Speicher) (a : Adresse)
    (c k : Nat) (hc : c < 4) (hk : k < 8)
    (h0 : lesbar8 m a = true)
    (h1 : lesbar8 m (vecHiAddr a) = true)
    (h2 : lesbar8 m (addrOff a 16) = true)
    (h3 : lesbar8 m (vecHiAddr (addrOff a 16)) = true) :
    m.lesbar (addrOff (avx2Chunk a c) k) = true := by
  have h4 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · show m.lesbar (addrOff a k) = true
    exact avx2Lesbar8_einzeln m a k hk h0
  · show m.lesbar (addrOff (vecHiAddr a) k) = true
    exact avx2Lesbar8_einzeln m (vecHiAddr a) k hk h1
  · show m.lesbar (addrOff (addrOff a 16) k) = true
    exact avx2Lesbar8_einzeln m (addrOff a 16) k hk h2
  · show m.lesbar (addrOff (vecHiAddr (addrOff a 16)) k) = true
    exact avx2Lesbar8_einzeln m (vecHiAddr (addrOff a 16)) k hk h3

/-- YMM store issue on the TSO view: thirty-two buffered byte
    issues, never the direct memory effect. `none` = a refused byte. -/
def avx2Speichern (s : TSOZustand) (c : Nat) (a : Adresse)
    (v : Avx2Vektor) : Option TSOZustand :=
  issueListe s c (avx2Eintraege a v)

/-- A successful YMM issue appends exactly the thirty-two entries. -/
theorem avx2Speichern_haengt_an (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Avx2Vektor)
    (h : avx2Speichern s c a v = some s') :
    s'.puffer c = s.puffer c ++ avx2Eintraege a v :=
  issueListe_haengt_an s s' c _ h

/-- A YMM issue changes no canonical byte (buffer only). -/
theorem avx2Speichern_kein_speicher (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Avx2Vektor)
    (h : avx2Speichern s c a v = some s') (x : Adresse) :
    s'.mem.bytes x = s.mem.bytes x :=
  issueListe_kein_speicher s s' c _ h x

/-- A fold of issues succeeds wherever every entry has write
    permission. Permissions survive each issue (the memory is kept),
    so the whole list goes through. -/
theorem avx2IssueListe_erfolg (l : List TSOEintrag) (s : TSOZustand)
    (c : Nat) (h : ∀ e ∈ l, s.mem.schreibbar e.addr = true) :
    ∃ s' : TSOZustand, issueListe s c l = some s' := by
  induction l generalizing s with
  | nil => exact ⟨s, rfl⟩
  | cons e rest ih =>
    have he : s.mem.schreibbar e.addr = true := h e (by simp)
    have h1 : issueByte s c e.addr e.wert =
        some ⟨s.mem, pufferSetze s.puffer c (s.puffer c ++ [e])⟩ := by
      unfold issueByte
      rw [if_pos he]
    have hrest : ∀ e' ∈ rest,
        (⟨s.mem, pufferSetze s.puffer c (s.puffer c ++ [e])⟩ :
          TSOZustand).mem.schreibbar e'.addr = true :=
      fun e' hm => h e' (by simp [hm])
    obtain ⟨s', hs'⟩ := ih _ hrest
    have hfold : issueListe s c (e :: rest) =
        issueListe ⟨s.mem, pufferSetze s.puffer c (s.puffer c ++ [e])⟩
          c rest := by
      show (match issueByte s c e.addr e.wert with
        | none => (none : Option TSOZustand)
        | some s1 => issueListe s1 c rest) = _
      rw [h1]
    rw [hfold]
    exact ⟨s', hs'⟩

/-- Write permission across all four chunks issues the whole YMM word. -/
theorem avx2Speichern_erfolg (s : TSOZustand) (c : Nat) (a : Adresse)
    (v : Avx2Vektor)
    (h0 : schreibbar8 s.mem a = true)
    (h1 : schreibbar8 s.mem (vecHiAddr a) = true)
    (h2 : schreibbar8 s.mem (addrOff a 16) = true)
    (h3 : schreibbar8 s.mem (vecHiAddr (addrOff a 16)) = true) :
    ∃ s' : TSOZustand, avx2Speichern s c a v = some s' := by
  apply avx2IssueListe_erfolg
  intro e hmem
  rcases avx2Eintrag_klass a v e hmem with
      ⟨c0, hk0, rfl⟩ | ⟨c0, hk0, rfl⟩ | ⟨c0, hk0, rfl⟩ | ⟨c0, hk0, rfl⟩
  · show s.mem.schreibbar (addrOff a c0) = true
    exact avx2Schreibbar8_einzeln s.mem a c0 hk0 h0
  · show s.mem.schreibbar (addrOff (vecHiAddr a) c0) = true
    exact avx2Schreibbar8_einzeln s.mem (vecHiAddr a) c0 hk0 h1
  · show s.mem.schreibbar (addrOff (addrOff a 16) c0) = true
    exact avx2Schreibbar8_einzeln s.mem (addrOff a 16) c0 hk0 h2
  · show s.mem.schreibbar
        (addrOff (vecHiAddr (addrOff a 16)) c0) = true
    exact avx2Schreibbar8_einzeln s.mem (vecHiAddr (addrOff a 16))
      c0 hk0 h3

/-- A fold of issues refuses wherever any entry lacks write
    permission: one refused byte fails the whole access. Permissions
    survive each issue, so the first refusal is reached. -/
theorem avx2IssueListe_verweigert (l : List TSOEintrag)
    (s : TSOZustand) (c : Nat) (e : TSOEintrag) (hmem : e ∈ l)
    (h : s.mem.schreibbar e.addr = false) :
    issueListe s c l = none := by
  induction l generalizing s with
  | nil =>
    simp at hmem
  | cons hd tl ih =>
    have heq : issueListe s c (hd :: tl) =
        match issueByte s c hd.addr hd.wert with
        | none => (none : Option TSOZustand)
        | some s1 => issueListe s1 c tl := rfl
    rw [heq]
    simp only [List.mem_cons] at hmem
    rcases hmem with hhead | hmem2
    · rw [hhead] at h
      have hn : issueByte s c hd.addr hd.wert = none := by
        unfold issueByte
        simp [h]
      rw [hn]
    · cases hb : issueByte s c hd.addr hd.wert with
      | none => rfl
      | some s1 =>
        have hperm : s1.mem.schreibbar e.addr = false := by
          have hp := issue_erhaelt_berechtigungen s s1 c hd.addr
            hd.wert hb
          rw [hp.2.1]
          exact h
        exact ih s1 hmem2 hperm

/-- A store without write permission at any listed entry refuses. -/
theorem avx2Speichern_verweigert_bei (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Avx2Vektor) (e : TSOEintrag)
    (hmem : e ∈ avx2Eintraege a v)
    (h : s.mem.schreibbar e.addr = false) :
    avx2Speichern s c a v = none :=
  avx2IssueListe_verweigert _ s c e hmem h

/-- A chunk-zero byte entry is in the thirty-two, by offset. -/
theorem avx2Eintraege_mem_c0_entry (a : Adresse) (v : Avx2Vektor)
    (k : Nat) (hk : k < 8) :
    (⟨addrOff a k, wortByte (vLo v.lo) k⟩ : TSOEintrag) ∈
      avx2Eintraege a v := by
  have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 := by
    omega
  have h0 : (⟨addrOff a k, wortByte (vLo v.lo) k⟩ : TSOEintrag) ∈
      avx2EintraegeC0 a v := by
    unfold avx2EintraegeC0
    rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact List.Mem.head _
    · exact List.Mem.tail _ (List.Mem.head _)
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _))))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))))
  unfold avx2Eintraege
  apply List.mem_append.mpr; apply Or.inl
  apply List.mem_append.mpr; apply Or.inl
  apply List.mem_append.mpr; apply Or.inl
  exact h0

/-- A chunk-one byte entry is in the thirty-two, by offset. -/
theorem avx2Eintraege_mem_c1_entry (a : Adresse) (v : Avx2Vektor)
    (k : Nat) (hk : k < 8) :
    (⟨addrOff (vecHiAddr a) k, wortByte (vHi v.lo) k⟩ : TSOEintrag) ∈
      avx2Eintraege a v := by
  have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 := by
    omega
  have h1 : (⟨addrOff (vecHiAddr a) k, wortByte (vHi v.lo) k⟩ :
      TSOEintrag) ∈ avx2EintraegeC1 a v := by
    unfold avx2EintraegeC1
    rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact List.Mem.head _
    · exact List.Mem.tail _ (List.Mem.head _)
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _))))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))))
  unfold avx2Eintraege
  apply List.mem_append.mpr; apply Or.inl
  apply List.mem_append.mpr; apply Or.inl
  apply List.mem_append.mpr; apply Or.inr
  exact h1

/-- A chunk-two byte entry is in the thirty-two, by offset. -/
theorem avx2Eintraege_mem_c2_entry (a : Adresse) (v : Avx2Vektor)
    (k : Nat) (hk : k < 8) :
    (⟨addrOff (addrOff a 16) k, wortByte (vLo v.hi) k⟩ : TSOEintrag) ∈
      avx2Eintraege a v := by
  have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 := by
    omega
  have h2 : (⟨addrOff (addrOff a 16) k, wortByte (vLo v.hi) k⟩ :
      TSOEintrag) ∈ avx2EintraegeC2 a v := by
    unfold avx2EintraegeC2
    rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact List.Mem.head _
    · exact List.Mem.tail _ (List.Mem.head _)
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _))))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))))
  unfold avx2Eintraege
  apply List.mem_append.mpr; apply Or.inl
  apply List.mem_append.mpr; apply Or.inr
  exact h2

/-- A chunk-three byte entry is in the thirty-two, by offset. -/
theorem avx2Eintraege_mem_c3_entry (a : Adresse) (v : Avx2Vektor)
    (k : Nat) (hk : k < 8) :
    (⟨addrOff (vecHiAddr (addrOff a 16)) k,
      wortByte (vHi v.hi) k⟩ : TSOEintrag) ∈ avx2Eintraege a v := by
  have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 := by
    omega
  have h3 : (⟨addrOff (vecHiAddr (addrOff a 16)) k,
      wortByte (vHi v.hi) k⟩ : TSOEintrag) ∈
      avx2EintraegeC3 a v := by
    unfold avx2EintraegeC3
    rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact List.Mem.head _
    · exact List.Mem.tail _ (List.Mem.head _)
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _))))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))))
  unfold avx2Eintraege
  apply List.mem_append.mpr; apply Or.inr
  exact h3

/-! ## 8. Loads as thirty-two TSO byte observations.

  Each chunk loads through eight `loadByte` observations (youngest
  own-buffer entry wins per byte: forwarding is observed, never
  bypassed); the four chunk words join into the YMM value through
  the accepted `vecJoin`. `none` = an unreadable byte. -/

/-- Assemble eight observed bytes into a chunk function. -/
def avx2AchtFun (b0 b1 b2 b3 b4 b5 b6 b7 : Byte) : Fin 8 → Byte :=
  fun j => match j with
  | ⟨0, _⟩ => b0 | ⟨1, _⟩ => b1 | ⟨2, _⟩ => b2 | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4 | ⟨5, _⟩ => b5 | ⟨6, _⟩ => b6 | ⟨_, _⟩ => b7

/-- Load one eight-byte chunk at `b` on core `c` through eight TSO
    byte observations, assembled low byte first. -/
def avx2Acht (s : TSOZustand) (c : Nat) (b : Adresse) : Option Wort :=
  match loadByte s c (addrOff b 0), loadByte s c (addrOff b 1),
      loadByte s c (addrOff b 2), loadByte s c (addrOff b 3),
      loadByte s c (addrOff b 4), loadByte s c (addrOff b 5),
      loadByte s c (addrOff b 6), loadByte s c (addrOff b 7) with
  | some b0, some b1, some b2, some b3, some b4, some b5, some b6,
    some b7 =>
    some (bytesWort (avx2AchtFun b0 b1 b2 b3 b4 b5 b6 b7))
  | _, _, _, _, _, _, _, _ => none

/-- A chunk load with no pending own entry at any of its eight bytes
    observes exactly the canonical chunk word: the accepted `read64`
    value, never a guessed one. -/
theorem avx2Acht_ist_read64 (s : TSOZustand) (c : Nat) (b : Adresse)
    (w : Wort)
    (hmiss : ∀ k : Nat, k < 8 →
      neuestens (s.puffer c) (addrOff b k) = none)
    (hrd : lesbar8 s.mem b = true)
    (h : avx2Acht s c b = some w) :
    read64 s.mem b = some w := by
  unfold avx2Acht at h
  cases h0 : loadByte s c (addrOff b 0) with
  | none =>
    rw [h0] at h
    dsimp only at h
    cases h
  | some b0 =>
    cases h1 : loadByte s c (addrOff b 1) with
    | none =>
      rw [h0, h1] at h
      dsimp only at h
      cases h
    | some b1 =>
      cases h2 : loadByte s c (addrOff b 2) with
      | none =>
        rw [h0, h1, h2] at h
        dsimp only at h
        cases h
      | some b2 =>
        cases h3 : loadByte s c (addrOff b 3) with
        | none =>
          rw [h0, h1, h2, h3] at h
          dsimp only at h
          cases h
        | some b3 =>
          cases h4 : loadByte s c (addrOff b 4) with
          | none =>
            rw [h0, h1, h2, h3, h4] at h
            dsimp only at h
            cases h
          | some b4 =>
            cases h5 : loadByte s c (addrOff b 5) with
            | none =>
              rw [h0, h1, h2, h3, h4, h5] at h
              dsimp only at h
              cases h
            | some b5 =>
              cases h6 : loadByte s c (addrOff b 6) with
              | none =>
                rw [h0, h1, h2, h3, h4, h5, h6] at h
                dsimp only at h
                cases h
              | some b6 =>
                cases h7 : loadByte s c (addrOff b 7) with
                | none =>
                  rw [h0, h1, h2, h3, h4, h5, h6, h7] at h
                  dsimp only at h
                  cases h
                | some b7 =>
                  rw [h0, h1, h2, h3, h4, h5, h6, h7] at h
                  dsimp only at h
                  obtain rfl := Option.some_inj.mp h
                  have m0 : b0 = s.mem.bytes (addrOff b 0) := by
                    have hg := load_ohne_eintrag s c (addrOff b 0)
                      (hmiss 0 (by decide))
                      (avx2Lesbar8_einzeln s.mem b 0 (by decide) hrd)
                    rw [h0] at hg
                    exact Option.some_inj.mp hg
                  have m1 : b1 = s.mem.bytes (addrOff b 1) := by
                    have hg := load_ohne_eintrag s c (addrOff b 1)
                      (hmiss 1 (by decide))
                      (avx2Lesbar8_einzeln s.mem b 1 (by decide) hrd)
                    rw [h1] at hg
                    exact Option.some_inj.mp hg
                  have m2 : b2 = s.mem.bytes (addrOff b 2) := by
                    have hg := load_ohne_eintrag s c (addrOff b 2)
                      (hmiss 2 (by decide))
                      (avx2Lesbar8_einzeln s.mem b 2 (by decide) hrd)
                    rw [h2] at hg
                    exact Option.some_inj.mp hg
                  have m3 : b3 = s.mem.bytes (addrOff b 3) := by
                    have hg := load_ohne_eintrag s c (addrOff b 3)
                      (hmiss 3 (by decide))
                      (avx2Lesbar8_einzeln s.mem b 3 (by decide) hrd)
                    rw [h3] at hg
                    exact Option.some_inj.mp hg
                  have m4 : b4 = s.mem.bytes (addrOff b 4) := by
                    have hg := load_ohne_eintrag s c (addrOff b 4)
                      (hmiss 4 (by decide))
                      (avx2Lesbar8_einzeln s.mem b 4 (by decide) hrd)
                    rw [h4] at hg
                    exact Option.some_inj.mp hg
                  have m5 : b5 = s.mem.bytes (addrOff b 5) := by
                    have hg := load_ohne_eintrag s c (addrOff b 5)
                      (hmiss 5 (by decide))
                      (avx2Lesbar8_einzeln s.mem b 5 (by decide) hrd)
                    rw [h5] at hg
                    exact Option.some_inj.mp hg
                  have m6 : b6 = s.mem.bytes (addrOff b 6) := by
                    have hg := load_ohne_eintrag s c (addrOff b 6)
                      (hmiss 6 (by decide))
                      (avx2Lesbar8_einzeln s.mem b 6 (by decide) hrd)
                    rw [h6] at hg
                    exact Option.some_inj.mp hg
                  have m7 : b7 = s.mem.bytes (addrOff b 7) := by
                    have hg := load_ohne_eintrag s c (addrOff b 7)
                      (hmiss 7 (by decide))
                      (avx2Lesbar8_einzeln s.mem b 7 (by decide) hrd)
                    rw [h7] at hg
                    exact Option.some_inj.mp hg
                  have hfun : readBytes s.mem b =
                      avx2AchtFun b0 b1 b2 b3 b4 b5 b6 b7 := by
                    funext ⟨jv, hj⟩
                    have h8 : jv = 0 ∨ jv = 1 ∨ jv = 2 ∨ jv = 3 ∨
                        jv = 4 ∨ jv = 5 ∨ jv = 6 ∨ jv = 7 := by
                      omega
                    rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                    · exact m0.symm
                    · exact m1.symm
                    · exact m2.symm
                    · exact m3.symm
                    · exact m4.symm
                    · exact m5.symm
                    · exact m6.symm
                    · exact m7.symm
                  have hrd8 : read64 s.mem b =
                      some (bytesWort (readBytes s.mem b)) := by
                    unfold read64
                    rw [if_pos hrd]
                  rw [hrd8, hfun]

/-- A chunk load with an unreadable byte refuses: one failed
    `loadByte` fails the whole chunk. -/
theorem avx2Acht_verweigert (s : TSOZustand) (c : Nat) (b : Adresse)
    (k0 : Nat) (hk0 : k0 < 8)
    (h : loadByte s c (addrOff b k0) = none) :
    avx2Acht s c b = none := by
  unfold avx2Acht
  cases h0 : loadByte s c (addrOff b 0) with
  | none => rfl
  | some b0 =>
    cases h1 : loadByte s c (addrOff b 1) with
    | none => rfl
    | some b1 =>
      cases h2 : loadByte s c (addrOff b 2) with
      | none => rfl
      | some b2 =>
        cases h3 : loadByte s c (addrOff b 3) with
        | none => rfl
        | some b3 =>
          cases h4 : loadByte s c (addrOff b 4) with
          | none => rfl
          | some b4 =>
            cases h5 : loadByte s c (addrOff b 5) with
            | none => rfl
            | some b5 =>
              cases h6 : loadByte s c (addrOff b 6) with
              | none => rfl
              | some b6 =>
                cases h7 : loadByte s c (addrOff b 7) with
                | none => rfl
                | some b7 =>
                  have hk8 : k0 = 0 ∨ k0 = 1 ∨ k0 = 2 ∨ k0 = 3 ∨
                      k0 = 4 ∨ k0 = 5 ∨ k0 = 6 ∨ k0 = 7 := by
                    omega
                  rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                  · rw [h0] at h
                    cases h
                  · rw [h1] at h
                    cases h
                  · rw [h2] at h
                    cases h
                  · rw [h3] at h
                    cases h
                  · rw [h4] at h
                    cases h
                  · rw [h5] at h
                    cases h
                  · rw [h6] at h
                    cases h
                  · rw [h7] at h
                    cases h

/-- Load a YMM word at `a` on core `c`: four chunk observations
    through the accepted `vecJoin`, low half then high half. -/
def avx2Laden (s : TSOZustand) (c : Nat) (a : Adresse) :
    Option Avx2Vektor :=
  match avx2Acht s c a, avx2Acht s c (vecHiAddr a),
      avx2Acht s c (addrOff a 16),
      avx2Acht s c (vecHiAddr (addrOff a 16)) with
  | some w0, some w1, some w2, some w3 =>
    some ⟨vecJoin w0 w1, vecJoin w2 w3⟩
  | _, _, _, _ => none

/-- The accepted memory-level YMM read: two accepted `vecRead`
    halves. The old evaluator lifted, never redefined. -/
def avx2Read (m : Speicher) (a : Adresse) : Option Avx2Vektor :=
  match vecRead m a, vecRead m (addrOff a 16) with
  | some lo, some hi => some ⟨lo, hi⟩
  | _, _ => none

/-- A YMM load with no pending own entry anywhere in its
    thirty-two footprint bytes observes exactly the accepted
    `avx2Read` value. -/
theorem avx2Laden_ist_avx2Read (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Avx2Vektor)
    (hmiss : ∀ x ∈ avx2Fuss a, neuestens (s.puffer c) x = none)
    (hrd0 : lesbar8 s.mem a = true)
    (hrd1 : lesbar8 s.mem (vecHiAddr a) = true)
    (hrd2 : lesbar8 s.mem (addrOff a 16) = true)
    (hrd3 : lesbar8 s.mem (vecHiAddr (addrOff a 16)) = true)
    (h : avx2Laden s c a = some v) :
    avx2Read s.mem a = some v := by
  have e : avx2Laden s c a = match avx2Acht s c a,
      avx2Acht s c (vecHiAddr a), avx2Acht s c (addrOff a 16),
      avx2Acht s c (vecHiAddr (addrOff a 16)) with
    | some w0, some w1, some w2, some w3 =>
      some (⟨vecJoin w0 w1, vecJoin w2 w3⟩ : Avx2Vektor)
    | _, _, _, _ => (none : Option Avx2Vektor) := rfl
  rw [e] at h
  cases hw0 : avx2Acht s c a with
  | none =>
    rw [hw0] at h
    dsimp only at h
    cases h
  | some w0 =>
    cases hw1 : avx2Acht s c (vecHiAddr a) with
    | none =>
      rw [hw0, hw1] at h
      dsimp only at h
      cases h
    | some w1 =>
      cases hw2 : avx2Acht s c (addrOff a 16) with
      | none =>
        rw [hw0, hw1, hw2] at h
        dsimp only at h
        cases h
      | some w2 =>
        cases hw3 : avx2Acht s c (vecHiAddr (addrOff a 16)) with
        | none =>
          rw [hw0, hw1, hw2, hw3] at h
          dsimp only at h
          cases h
        | some w3 =>
          rw [hw0, hw1, hw2, hw3] at h
          dsimp only at h
          obtain rfl := Option.some_inj.mp h
          have r0 := avx2Acht_ist_read64 s c a w0
            (fun k hk => hmiss _ (avx2Eintrag_mem_c0 a k hk))
            hrd0 hw0
          have r1 := avx2Acht_ist_read64 s c (vecHiAddr a) w1
            (fun k hk => hmiss _ (avx2Eintrag_mem_c1 a k hk))
            hrd1 hw1
          have r2 := avx2Acht_ist_read64 s c (addrOff a 16) w2
            (fun k hk => hmiss _ (avx2Eintrag_mem_c2 a k hk))
            hrd2 hw2
          have r3 := avx2Acht_ist_read64 s c
            (vecHiAddr (addrOff a 16)) w3
            (fun k hk => hmiss _ (avx2Eintrag_mem_c3 a k hk))
            hrd3 hw3
          have rlo : vecRead s.mem a = some (vecJoin w0 w1) := by
            unfold vecRead
            rw [r0, r1]
          have rhi : vecRead s.mem (addrOff a 16) =
              some (vecJoin w2 w3) := by
            unfold vecRead
            rw [r2, r3]
          unfold avx2Read
          rw [rlo, rhi]

/-! ## 9. Forwarding for the owner, old bytes for everyone else.

  Byte-level, general: after a successful thirty-two issue fold,
  every entry byte forwards to its owner (youngest own entry wins,
  older shadowed entries lose, later other-address issues do not
  disturb); another core without footprint entries still reads
  canonical memory. Whole-value assembly is witnessed, not
  re-arithmetised here. -/

/-- Appending a later list keeps an already-youngest match. -/
theorem avx2Neuestens_append_rechts (l r : List TSOEintrag)
    (x : Adresse) (w : Byte)
    (h : neuestens r x = some w) :
    neuestens (l ++ r) x = some w := by
  induction l with
  | nil => simpa
  | cons hd tl ih =>
    have e2 : (hd :: tl) ++ r = hd :: (tl ++ r) := rfl
    rw [e2]
    unfold neuestens
    rw [ih]

/-- A youngest match comes from a list member carrying it. -/
theorem avx2Neuestens_mem (l : List TSOEintrag) (x : Adresse)
    (w : Byte) (h : neuestens l x = some w) :
    ∃ e ∈ l, e.addr = x ∧ e.wert = w := by
  induction l with
  | nil =>
    simp [neuestens] at h
  | cons hd tl ih =>
    unfold neuestens at h
    cases ht : neuestens tl x with
    | some w' =>
      rw [ht] at h
      dsimp only at h
      obtain rfl := Option.some_inj.mp h
      obtain ⟨e, hm, had, hw⟩ := ih ht
      exact ⟨e, List.mem_cons.mpr (Or.inr hm), had, hw⟩
    | none =>
      rw [ht] at h
      dsimp only at h
      by_cases heq : hd.addr = x
      · rw [if_pos heq] at h
        obtain rfl := Option.some_inj.mp h
        exact ⟨hd, List.mem_cons.mpr (Or.inl rfl), heq, rfl⟩
      · rw [if_neg heq] at h
        cases h

/-- After issuing any sublist of the thirty-two, every issued byte
    forwards to its owner. Induction over the issued list; the new
    byte forwards (a later same-address match carries the same value
    by address uniqueness), older bytes are undisturbed. -/
theorem avx2Weiterleitung_sub (l : List TSOEintrag)
    (s s' : TSOZustand) (c : Nat) (a : Adresse) (v : Avx2Vektor)
    (hno : OhneUmbruch32 a)
    (hsub : ∀ e ∈ l, e ∈ avx2Eintraege a v)
    (hfold : issueListe s c l = some s') :
    ∀ e ∈ l, neuestens (s'.puffer c) e.addr = some e.wert := by
  induction l generalizing s s' with
  | nil =>
    intro e hmem
    simp at hmem
  | cons hd tl ih =>
    have hmem_hd : hd ∈ avx2Eintraege a v :=
      hsub hd (List.mem_cons.mpr (Or.inl rfl))
    have hsub_tl : ∀ e ∈ tl, e ∈ avx2Eintraege a v := by
      intro e hm
      exact hsub e (List.mem_cons.mpr (Or.inr hm))
    have heq : issueListe s c (hd :: tl) =
        match issueByte s c hd.addr hd.wert with
        | none => (none : Option TSOZustand)
        | some s1 => issueListe s1 c tl := rfl
    rw [heq] at hfold
    cases hb : issueByte s c hd.addr hd.wert with
    | none =>
      rw [hb] at hfold
      dsimp only at hfold
      cases hfold
    | some s1 =>
      rw [hb] at hfold
      dsimp only at hfold
      have ihh := ih s1 s' hsub_tl hfold
      have hbuf : s'.puffer c = s.puffer c ++ (hd :: tl) := by
        have ha := issueListe_haengt_an s1 s' c tl hfold
        have hb1 := issue_haengt_an s s1 c hd.addr hd.wert hb
        rw [ha, hb1, List.append_assoc]
        rfl
      intro e hmem2
      simp only [List.mem_cons] at hmem2
      rcases hmem2 with rfl | hmem2
      · rw [hbuf]
        have hnodup := avx2Eintraege_nodup_addr a hno v
        cases ht : neuestens tl e.addr with
        | some w' =>
          obtain ⟨e2, hm2, had2, hw2⟩ := avx2Neuestens_mem tl
            e.addr w' ht
          have heq2 := hnodup e2 (hsub_tl e2 hm2) e hmem_hd had2
          have e3 : neuestens (e :: tl) e.addr = some w' := by
            unfold neuestens
            rw [ht]
          have hhd : neuestens (e :: tl) e.addr = some e.wert := by
            rw [e3, ← hw2, heq2]
          exact avx2Neuestens_append_rechts (s.puffer c) (e :: tl)
            e.addr e.wert hhd
        | none =>
          have hhd : neuestens (e :: tl) e.addr = some e.wert := by
            unfold neuestens
            rw [ht]
            dsimp only
            rw [if_pos rfl]
          exact avx2Neuestens_append_rechts (s.puffer c) (e :: tl)
            e.addr e.wert hhd
      · exact ihh e hmem2

/-- After a successful thirty-two issue fold, every entry byte
    forwards to the acting core. -/
theorem avx2Weiterleitung (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Avx2Vektor) (hno : OhneUmbruch32 a)
    (h : avx2Speichern s c a v = some s') :
    ∀ e ∈ avx2Eintraege a v,
      neuestens (s'.puffer c) e.addr = some e.wert :=
  avx2Weiterleitung_sub _ s s' c a v hno (fun e hm => hm) h

/-- Another core without footprint entries in its buffer still reads
    canonical memory at every footprint byte. -/
theorem avx2FremdAlt_byte (s : TSOZustand) (c d : Nat) (a : Adresse)
    (x : Adresse) (hx : x ∈ avx2Fuss a)
    (hmiss : ∀ x ∈ avx2Fuss a, neuestens (s.puffer d) x = none)
    (hrd : s.mem.lesbar x = true) :
    loadByte s d x = some (s.mem.bytes x) :=
  load_ohne_eintrag s d x (hmiss x hx) hrd

/-! ## 10. Grouping: exact buffers group, partial and foreign do not.

  A grouped thirty-two drains to one unsplit value exactly under a
  structural exclusion check; tearing beyond it is refused
  structurally. No whole-vector atomicity is claimed. -/

/-- Foreign-footprint freedom over the 32-byte footprint: no other
    core holds a pending entry inside `avx2Fuss a`. -/
def Avx2FremdFrei (s : TSOZustand) (c : Nat) (a : Adresse) : Prop :=
  ∀ d : Nat, d ≠ c → ∀ e : TSOEintrag, e ∈ s.puffer d →
    e.addr ∉ avx2Fuss a

/-- Start-state grouping check: the acting core carries exactly the
    thirty-two canonical entries and no foreign entry touches the
    footprint. -/
def Avx2Gruppe (s : TSOZustand) (c : Nat) (a : Adresse)
    (v : Avx2Vektor) : Prop :=
  s.puffer c = avx2Eintraege a v ∧ Avx2FremdFrei s c a

/-- A partial buffer is no group: tearing is refused structurally. -/
theorem avx2Teilwort_keine_gruppe (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Avx2Vektor)
    (hne : s.puffer c ≠ avx2Eintraege a v) :
    ¬ Avx2Gruppe s c a v := by
  intro hgrp
  obtain ⟨hbufl, _⟩ := hgrp
  exact hne hbufl

/-- A foreign footprint entry refuses the group. -/
theorem avx2Gruppe_verweigert_bei_fremdeintrag (s : TSOZustand)
    (c : Nat) (a : Adresse) (v : Avx2Vektor) (d : Nat) (hne : d ≠ c)
    (e : TSOEintrag) (hmem : e ∈ s.puffer d)
    (hfuss : e.addr ∈ avx2Fuss a) :
    ¬ Avx2Gruppe s c a v := by
  intro hgrp
  obtain ⟨_, hff⟩ := hgrp
  exact (hff d hne e hmem) hfuss

/-! ## 11. Drains: byte-wise flushes with an explicit tearing table.

  A drain flushes one oldest entry at a time: after flushing a
  prefix of the thirty-two, the flushed bytes are new while the
  rest still reads the pre-drain bytes. No whole-vector atomicity
  is claimed anywhere. -/

/-- Flush the oldest entries of core `c` named by `l`, in order:
    `none` = the buffer ran dry. -/
def avx2Drain (s : TSOZustand) (c : Nat) : List TSOEintrag →
    Option TSOZustand
  | [] => some s
  | _e :: rest =>
    match flushKern s c with
    | none => none
    | some s1 => avx2Drain s1 c rest

/-- A drain changes nothing outside the drained entries (frame). -/
theorem avx2Drain_rahmen (l : List TSOEintrag) (s s' : TSOZustand)
    (c : Nat) (rest : List TSOEintrag)
    (hbuf : s.puffer c = l ++ rest)
    (h : avx2Drain s c l = some s')
    (x : Adresse) (hxa : ∀ e ∈ l, e.addr ≠ x) :
    s'.mem.bytes x = s.mem.bytes x := by
  induction l generalizing s with
  | nil =>
    have e : avx2Drain s c [] = some s := rfl
    rw [e] at h
    obtain rfl := Option.some_inj.mp h
    rfl
  | cons hd tl ih =>
    have e : avx2Drain s c (hd :: tl) = match flushKern s c with
      | none => (none : Option TSOZustand)
      | some s1 => avx2Drain s1 c tl := rfl
    rw [e] at h
    cases hk : flushKern s c with
    | none =>
      rw [hk] at h
      dsimp only at h
      cases h
    | some s1 =>
      rw [hk] at h
      dsimp only at h
      have hhead : s.puffer c = hd :: (tl ++ rest) := hbuf
      have hbuf1 : s1.puffer c = tl ++ rest :=
        flush_entfernt_kopf s s1 c hk hd (tl ++ rest) hhead
      have hfr := ih s1 hbuf1 h (fun e hm => hxa e (by simp [hm]))
      have hhx : x ≠ hd.addr := Ne.symm (hxa hd (by simp))
      have hkeep := flush_rahmen s s1 c hk hd (tl ++ rest) hhead x hhx
      rw [hfr, hkeep]

/-- A drain installs the latest drained byte at every touched
    address. -/
theorem avx2Drain_schreibt_allg (l : List TSOEintrag)
    (s s' : TSOZustand) (c : Nat) (rest : List TSOEintrag)
    (hbuf : s.puffer c = l ++ rest)
    (h : avx2Drain s c l = some s')
    (x : Adresse) (w : Byte)
    (hw : ∀ e ∈ l, e.addr = x → e.wert = w)
    (hmem : ∃ e ∈ l, e.addr = x) :
    s'.mem.bytes x = w := by
  induction l generalizing s with
  | nil =>
    simp at hmem
  | cons hd tl ih =>
    have e : avx2Drain s c (hd :: tl) = match flushKern s c with
      | none => (none : Option TSOZustand)
      | some s1 => avx2Drain s1 c tl := rfl
    rw [e] at h
    cases hk : flushKern s c with
    | none =>
      rw [hk] at h
      dsimp only at h
      cases h
    | some s1 =>
      rw [hk] at h
      dsimp only at h
      have hhead : s.puffer c = hd :: (tl ++ rest) := hbuf
      have hbuf1 : s1.puffer c = tl ++ rest :=
        flush_entfernt_kopf s s1 c hk hd (tl ++ rest) hhead
      have hwt : ∀ e ∈ tl, e.addr = x → e.wert = w :=
        fun e hm had => hw e (by simp [hm]) had
      by_cases heq : hd.addr = x
      · have hwv : hd.wert = w := hw hd (by simp) heq
        have hinst := flush_schreibt_kopf s s1 c hk hd (tl ++ rest)
          hhead
        rw [heq] at hinst
        by_cases hex : ∃ e ∈ tl, e.addr = x
        · obtain ⟨e2, hm2, had2⟩ := hex
          exact ih s1 hbuf1 h hwt ⟨e2, hm2, had2⟩
        · have hxa : ∀ e ∈ tl, e.addr ≠ x := by
            intro e hm had
            exact hex ⟨e, hm, had⟩
          have hfr := avx2Drain_rahmen tl s1 s' c rest hbuf1 h x hxa
          rw [hfr, hinst, hwv]
      · obtain ⟨e, hmeml, hadr⟩ := hmem
        simp only [List.mem_cons] at hmeml
        have hmem2 : e ∈ tl := by
          rcases hmeml with rfl | hm
          · exact absurd hadr heq
          · exact hm
        exact ih s1 hbuf1 h hwt ⟨e, hmem2, hadr⟩

/-- FULL DRAIN: draining all thirty-two installs every entry byte. -/
theorem avx2Drain_schreibt (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Avx2Vektor) (rest : List TSOEintrag)
    (hbuf : s.puffer c = avx2Eintraege a v ++ rest)
    (h : avx2Drain s c (avx2Eintraege a v) = some s')
    (hdis : ∀ e1 ∈ avx2Eintraege a v, ∀ e2 ∈ avx2Eintraege a v,
      e1.addr = e2.addr → e1 = e2)
    (e : TSOEintrag) (hmem : e ∈ avx2Eintraege a v) :
    s'.mem.bytes e.addr = e.wert := by
  exact avx2Drain_schreibt_allg (avx2Eintraege a v) s s' c rest hbuf h
    e.addr e.wert
    (fun e' hm' had => by
      have heq := hdis e' hm' e hmem had
      rw [heq])
    ⟨e, hmem, rfl⟩

/-- Low-half entries are chunk-zero or chunk-one bytes. -/
theorem avx2Eintrag_klass_lo (a : Adresse) (v : Avx2Vektor)
    (e : TSOEintrag) (hmem : e ∈ avx2EintraegeLo a v) :
    (∃ k, k < 8 ∧ e = ⟨addrOff a k, wortByte (vLo v.lo) k⟩) ∨
    (∃ k, k < 8 ∧
      e = ⟨addrOff (vecHiAddr a) k, wortByte (vHi v.lo) k⟩) := by
  unfold avx2EintraegeLo at hmem
  have h := List.mem_append.mp hmem
  rcases h with h0 | h1
  · exact Or.inl (avx2Eintrag_klass_c0 a v e h0)
  · exact Or.inr (avx2Eintrag_klass_c1 a v e h1)

/-- A chunk-zero byte entry is in the low sixteen, by offset. -/
theorem avx2Lo_mem_c0_entry (a : Adresse) (v : Avx2Vektor)
    (k : Nat) (hk : k < 8) :
    (⟨addrOff a k, wortByte (vLo v.lo) k⟩ : TSOEintrag) ∈
      avx2EintraegeLo a v := by
  have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 := by
    omega
  have h0 : (⟨addrOff a k, wortByte (vLo v.lo) k⟩ : TSOEintrag) ∈
      avx2EintraegeC0 a v := by
    unfold avx2EintraegeC0
    rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact List.Mem.head _
    · exact List.Mem.tail _ (List.Mem.head _)
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _))))))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))))
  unfold avx2EintraegeLo
  apply List.mem_append.mpr; apply Or.inl
  exact h0

/-- TEARING: draining the low sixteen installs the low-half bytes
    while the high-half bytes still read pre-drain. No
    whole-vector atomicity is claimed anywhere. -/
theorem avx2Drain_teilt16 (s s1 : TSOZustand) (c : Nat)
    (a : Adresse) (v : Avx2Vektor) (rest : List TSOEintrag)
    (hno : OhneUmbruch32 a)
    (hbuf : s.puffer c = avx2Eintraege a v ++ rest)
    (h : avx2Drain s c (avx2EintraegeLo a v) = some s1)
    (k : Nat) (hk : k < 8) :
    s1.mem.bytes (addrOff a k) = wortByte (vLo v.lo) k ∧
      s1.mem.bytes (addrOff (addrOff a 16) k) =
        s.mem.bytes (addrOff (addrOff a 16) k) := by
  rw [avx2Eintraege_zerlegt, List.append_assoc] at hbuf
  have hmemLo : ∀ k : Nat, k < 8 →
      ∃ e ∈ avx2EintraegeLo a v, e.addr = addrOff a k := by
    intro k hk
    exact ⟨_, avx2Lo_mem_c0_entry a v k hk, rfl⟩
  refine ⟨?_, ?_⟩
  · exact avx2Drain_schreibt_allg (avx2EintraegeLo a v) s s1 c
      (avx2EintraegeHi a v ++ rest) hbuf h (addrOff a k)
      (wortByte (vLo v.lo) k)
      (fun e hm had => by
        rcases avx2Eintrag_klass_lo a v e hm with
            ⟨k', hk', rfl⟩ | ⟨k', hk', rfl⟩
        · have hkk : k' = k := addrOff_inj8 hk' hk had
          subst hkk
          rfl
        · exact absurd had (Ne.symm (avx2Chunk_disjunkt a hno 0 1
            (by decide) (by decide) (by decide) k k' hk hk')))
      (hmemLo k hk)
  · exact avx2Drain_rahmen (avx2EintraegeLo a v) s s1 c
      (avx2EintraegeHi a v ++ rest) hbuf h
      (addrOff (addrOff a 16) k) (fun e hm => by
        rcases avx2Eintrag_klass_lo a v e hm with
            ⟨k', hk', rfl⟩ | ⟨k', hk', rfl⟩
        · exact avx2Chunk_disjunkt a hno 0 2
            (by decide) (by decide) (by decide) k' k hk' hk
        · exact avx2Chunk_disjunkt a hno 1 2
            (by decide) (by decide) (by decide) k' k hk' hk)

/-! ## 12. Events, plugs and adapter on the coherent machine.

  The family's event type carries the checked CPU/XCR0/control
  inputs plus the named profile, so every plug checks them per
  step, never assuming them. Store values are handed to the plug
  (YMM register-file binding stays with the State lane); loads are
  state-unchanged observations. -/

/-- AVX2 memory family events on the coherent machine: TSO stores
    of whole YMM words, TSO load observations, the old machine
    events, and explicit refusal. -/
inductive Avx2MemEreignis where
  | hwAlt : HwEreignis → Avx2MemEreignis
  | speichere : Nat → CpuMerkmal → Xcr0Bild → KontrollBild →
      Avx2Profil → Avx2MemForm → Register → BitVec 32 →
      Avx2Vektor → Avx2MemEreignis
  | lade : Nat → CpuMerkmal → Xcr0Bild → KontrollBild → Avx2Profil →
      Avx2MemForm → Register → BitVec 32 → Avx2MemEreignis
  | verweigert : Nat → Avx2MemEreignis
  deriving DecidableEq, Repr

/-- Machine YMM store: gates (named profile, AVX readiness, `#GP`
    alignment for the `ausgerichtet` shape) then thirty-two buffered
    TSO byte issues of the handed value. Canonical memory is
    unchanged (buffer only); no direct memory effect is ever
    substituted. -/
def avx2SpeicherSchritt (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
    (x : Xcr0Bild) (k : KontrollBild) (p : Avx2Profil)
    (f : Avx2MemForm) (base : Register) (disp : BitVec 32)
    (v : Avx2Vektor) : Option HwMaschine :=
  match avx2MemZugelassen m.hw (m.bereit c) cpu x k p with
  | true =>
    if avx2GpFehler (effAddr (projZustand m c) base disp) f then none
    else
      match avx2Speichern (tsoAnsicht m) c
          (effAddr (projZustand m c) base disp) v with
      | some s' => some (setTso m s')
      | none => none
  | false => none

/-- Machine YMM load: gates as above, then thirty-two TSO byte
    observations with forwarding; the observation succeeds exactly
    where `avx2Laden` succeeds. Memory and buffers are kept. -/
def avx2LadeSchritt (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
    (x : Xcr0Bild) (k : KontrollBild) (p : Avx2Profil)
    (f : Avx2MemForm) (base : Register) (disp : BitVec 32) :
    Option HwMaschine :=
  match avx2MemZugelassen m.hw (m.bereit c) cpu x k p with
  | true =>
    if avx2GpFehler (effAddr (projZustand m c) base disp) f then none
    else
      match avx2Laden (tsoAnsicht m) c
          (effAddr (projZustand m c) base disp) with
      | some _ => some m
      | none => none
  | false => none

/-- The AVX2 memory producer plug: stores through the issue fold,
    loads through the observation, everything else refused. A
    mismatched core is refused, never rerouted. -/
def adapterAvx2Mem : HwAdapter Avx2MemEreignis :=
  ⟨fun m c e => match e with
    | .speichere c' cpu x k p f base disp v =>
      if c' = c then avx2SpeicherSchritt m c cpu x k p f base disp v
      else none
    | .lade c' cpu x k p f base disp =>
      if c' = c then avx2LadeSchritt m c cpu x k p f base disp
      else none
    | _ => none⟩

/-- The adapter refuses old events: nothing is admitted silently. -/
theorem adapterAvx2Mem_verweigert_alt (m : HwMaschine) (c : Nat)
    (e : HwEreignis) :
    adapterAvx2Mem.schritt m c (.hwAlt e) = none := rfl

/-- The adapter refuses bare refusals. -/
theorem adapterAvx2Mem_verweigert_fehler (m : HwMaschine) (c d : Nat) :
    adapterAvx2Mem.schritt m c (.verweigert d) = none := rfl

/-- A mismatched core is refused on the store path, never rerouted. -/
theorem adapterAvx2Mem_fremder_kern_speichere (m : HwMaschine)
    (c c' : Nat) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (p : Avx2Profil) (f : Avx2MemForm)
    (base : Register) (disp : BitVec 32) (v : Avx2Vektor)
    (hne : c' ≠ c) :
    adapterAvx2Mem.schritt m c
      (.speichere c' cpu x k p f base disp v) = none := by
  show (if c' = c then
    avx2SpeicherSchritt m c cpu x k p f base disp v else none) = none
  exact if_neg hne

/-- A mismatched core is refused on the load path. -/
theorem adapterAvx2Mem_fremder_kern_lade (m : HwMaschine)
    (c c' : Nat) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (p : Avx2Profil) (f : Avx2MemForm)
    (base : Register) (disp : BitVec 32) (hne : c' ≠ c) :
    adapterAvx2Mem.schritt m c
      (.lade c' cpu x k p f base disp) = none := by
  show (if c' = c then avx2LadeSchritt m c cpu x k p f base disp
    else none) = none
  exact if_neg hne

/-- On its own core the adapter IS the store plug. -/
theorem adapterAvx2Mem_speichere (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil) (f : Avx2MemForm) (base : Register)
    (disp : BitVec 32) (v : Avx2Vektor) :
    adapterAvx2Mem.schritt m c
      (.speichere c cpu x k p f base disp v) =
      avx2SpeicherSchritt m c cpu x k p f base disp v := by
  show (if c = c then avx2SpeicherSchritt m c cpu x k p f base disp v
    else none) = _
  rw [if_pos rfl]

/-- On its own core the adapter IS the load plug. -/
theorem adapterAvx2Mem_lade (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil) (f : Avx2MemForm) (base : Register)
    (disp : BitVec 32) :
    adapterAvx2Mem.schritt m c (.lade c cpu x k p f base disp) =
      avx2LadeSchritt m c cpu x k p f base disp := by
  show (if c = c then avx2LadeSchritt m c cpu x k p f base disp
    else none) = _
  rw [if_pos rfl]

/-! ## 13. The extended step relation: old steps plus YMM rows.

  The old coherent steps embed exactly (`alt`, with projection
  back); the two aligned/unaligned TSO stores and the two TSO load
  observations join them, plus explicit gate refusal. -/

/-- The extended step relation: the old coherent steps exactly
    (`alt`), the aligned/unaligned TSO stores (`speichereA`/
    `speichereU`), the aligned/unaligned TSO load observations
    (`ladeA`/`ladeU`, state unchanged), and explicit gate refusal
    (`fehler`). -/
inductive HwAvx2Schritt :
    HwMaschine → HwMaschine → Avx2MemEreignis → Prop where
  | alt {m m' : HwMaschine} {e : HwEreignis} (h : HwSchritt m m' e) :
      HwAvx2Schritt m m' (.hwAlt e)
  | speichereA {m : HwMaschine} {c : Nat} {cpu : CpuMerkmal}
      {x : Xcr0Bild} {k : KontrollBild} {p : Avx2Profil}
      {base : Register} {disp : BitVec 32} {v : Avx2Vektor}
      {s' : TSOZustand}
      (hgate : avx2MemZugelassen m.hw (m.bereit c) cpu x k p = true)
      (hgp : avx2GpFehler (effAddr (projZustand m c) base disp)
        .ausgerichtet = false)
      (hwr : avx2Speichern (tsoAnsicht m) c
        (effAddr (projZustand m c) base disp) v = some s') :
      HwAvx2Schritt m (setTso m s')
        (.speichere c cpu x k p .ausgerichtet base disp v)
  | speichereU {m : HwMaschine} {c : Nat} {cpu : CpuMerkmal}
      {x : Xcr0Bild} {k : KontrollBild} {p : Avx2Profil}
      {base : Register} {disp : BitVec 32} {v : Avx2Vektor}
      {s' : TSOZustand}
      (hgate : avx2MemZugelassen m.hw (m.bereit c) cpu x k p = true)
      (hwr : avx2Speichern (tsoAnsicht m) c
        (effAddr (projZustand m c) base disp) v = some s') :
      HwAvx2Schritt m (setTso m s')
        (.speichere c cpu x k p .unausgerichtet base disp v)
  | ladeA {m : HwMaschine} {c : Nat} {cpu : CpuMerkmal}
      {x : Xcr0Bild} {k : KontrollBild} {p : Avx2Profil}
      {base : Register} {disp : BitVec 32} {v : Avx2Vektor}
      (hgate : avx2MemZugelassen m.hw (m.bereit c) cpu x k p = true)
      (hgp : avx2GpFehler (effAddr (projZustand m c) base disp)
        .ausgerichtet = false)
      (hread : avx2Laden (tsoAnsicht m) c
        (effAddr (projZustand m c) base disp) = some v) :
      HwAvx2Schritt m m
        (.lade c cpu x k p .ausgerichtet base disp)
  | ladeU {m : HwMaschine} {c : Nat} {cpu : CpuMerkmal}
      {x : Xcr0Bild} {k : KontrollBild} {p : Avx2Profil}
      {base : Register} {disp : BitVec 32} {v : Avx2Vektor}
      (hgate : avx2MemZugelassen m.hw (m.bereit c) cpu x k p = true)
      (hread : avx2Laden (tsoAnsicht m) c
        (effAddr (projZustand m c) base disp) = some v) :
      HwAvx2Schritt m m
        (.lade c cpu x k p .unausgerichtet base disp)
  | fehler {m : HwMaschine} {c : Nat} {cpu : CpuMerkmal}
      {x : Xcr0Bild} {k : KontrollBild} {p : Avx2Profil}
      (h : avx2MemZugelassen m.hw (m.bereit c) cpu x k p = false) :
      HwAvx2Schritt m m (.verweigert c)

/-- Every extended step preserves well-formedness: memory/buffer
    updates leave the checked profiles untouched, observations and
    refusals change nothing. -/
theorem hwAvx2Schritt_wf (m m' : HwMaschine) (e : Avx2MemEreignis)
    (h : HwAvx2Schritt m m' e) (hwf : HwWf m) : HwWf m' := by
  cases h with
  | alt h => exact hwSchritt_wf _ _ _ h hwf
  | speichereA hgate hgp hwr => exact setTso_wf _ _ hwf
  | speichereU hgate hwr => exact setTso_wf _ _ hwf
  | ladeA hgate hgp hread => exact hwf
  | ladeU hgate hread => exact hwf
  | fehler h => exact hwf

/-- Exact embedding: every old coherent step is an extended step. -/
theorem hwAvx2Schritt_einbettet (m m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt m m' e) : HwAvx2Schritt m m' (.hwAlt e) :=
  .alt h

/-- Exact projection: an embedded step is the old step back. -/
theorem hwAvx2Schritt_projiziert (m m' : HwMaschine) (e : HwEreignis)
    (h : HwAvx2Schritt m m' (.hwAlt e)) : HwSchritt m m' e := by
  cases h with
  | alt h => exact h

/-- A successful machine store IS an extended step: the equation
    unfolds to the structured premises. -/
theorem avx2Speichere_ist_schritt (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil) (f : Avx2MemForm) (base : Register)
    (disp : BitVec 32) (v : Avx2Vektor) (m' : HwMaschine)
    (h : avx2SpeicherSchritt m c cpu x k p f base disp v =
      some m') :
    HwAvx2Schritt m m' (.speichere c cpu x k p f base disp v) := by
  unfold avx2SpeicherSchritt at h
  cases hf : f with
  | ausgerichtet =>
    rw [hf] at h
    cases hg : avx2MemZugelassen m.hw (m.bereit c) cpu x k p with
    | false =>
      rw [hg] at h
      dsimp only at h
      cases h
    | true =>
      rw [hg] at h
      dsimp only at h
      cases hgp : avx2GpFehler (effAddr (projZustand m c) base disp)
          .ausgerichtet with
      | true =>
        rw [if_pos hgp] at h
        cases h
      | false =>
        have hneg : ¬ avx2GpFehler (effAddr (projZustand m c) base disp)
            .ausgerichtet = true := by
          simp [hgp]
        rw [if_neg hneg] at h
        cases hwr : avx2Speichern (tsoAnsicht m) c
            (effAddr (projZustand m c) base disp) v with
        | none =>
          rw [hwr] at h
          dsimp only at h
          cases h
        | some s' =>
          rw [hwr] at h
          dsimp only at h
          obtain rfl := Option.some_inj.mp h
          exact .speichereA hg hgp hwr
  | unausgerichtet =>
    rw [hf] at h
    cases hg : avx2MemZugelassen m.hw (m.bereit c) cpu x k p with
    | false =>
      rw [hg] at h
      dsimp only at h
      cases h
    | true =>
      rw [hg] at h
      dsimp only at h
      have hgp : avx2GpFehler (effAddr (projZustand m c) base disp)
          .unausgerichtet = false :=
        avx2Gp_nie_unausgerichtet _
      have hneg : ¬ avx2GpFehler (effAddr (projZustand m c) base disp)
          .unausgerichtet = true := by
        simp [hgp]
      rw [if_neg hneg] at h
      cases hwr : avx2Speichern (tsoAnsicht m) c
          (effAddr (projZustand m c) base disp) v with
      | none =>
        rw [hwr] at h
        dsimp only at h
        cases h
        | some s' =>
          rw [hwr] at h
          dsimp only at h
          obtain rfl := Option.some_inj.mp h
          exact .speichereU hg hwr

/-- A successful machine load IS an extended step. -/
theorem avx2Lade_ist_schritt (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil) (f : Avx2MemForm) (base : Register)
    (disp : BitVec 32) (m' : HwMaschine)
    (h : avx2LadeSchritt m c cpu x k p f base disp = some m') :
    HwAvx2Schritt m m' (.lade c cpu x k p f base disp) := by
  unfold avx2LadeSchritt at h
  cases hf : f with
  | ausgerichtet =>
    rw [hf] at h
    cases hg : avx2MemZugelassen m.hw (m.bereit c) cpu x k p with
    | false =>
      rw [hg] at h
      dsimp only at h
      cases h
    | true =>
      rw [hg] at h
      dsimp only at h
      cases hgp : avx2GpFehler (effAddr (projZustand m c) base disp)
          .ausgerichtet with
      | true =>
        rw [if_pos hgp] at h
        cases h
      | false =>
        have hneg : ¬ avx2GpFehler (effAddr (projZustand m c) base disp)
            .ausgerichtet = true := by
          simp [hgp]
        rw [if_neg hneg] at h
        cases hrd : avx2Laden (tsoAnsicht m) c
            (effAddr (projZustand m c) base disp) with
        | none =>
          rw [hrd] at h
          dsimp only at h
          cases h
        | some v =>
          rw [hrd] at h
          dsimp only at h
          obtain rfl := Option.some_inj.mp h
          exact .ladeA hg hgp hrd
  | unausgerichtet =>
    rw [hf] at h
    cases hg : avx2MemZugelassen m.hw (m.bereit c) cpu x k p with
    | false =>
      rw [hg] at h
      dsimp only at h
      cases h
    | true =>
      rw [hg] at h
      dsimp only at h
      have hgp : avx2GpFehler (effAddr (projZustand m c) base disp)
          .unausgerichtet = false :=
        avx2Gp_nie_unausgerichtet _
      have hneg : ¬ avx2GpFehler (effAddr (projZustand m c) base disp)
          .unausgerichtet = true := by
        simp [hgp]
      rw [if_neg hneg] at h
      cases hrd : avx2Laden (tsoAnsicht m) c
          (effAddr (projZustand m c) base disp) with
      | none =>
        rw [hrd] at h
        dsimp only at h
        cases h
      | some v =>
        rw [hrd] at h
        dsimp only at h
        obtain rfl := Option.some_inj.mp h
        exact .ladeU hg hrd

/-! ## 14. Planted refusals: gates refuse, never guess.

  Each enabled-state side (named profile, AVX CPU/XCR0, control
  freedom, finite profile admission), `#GP` alignment and per-byte
  permissions refuse explicitly -- on the machine plugs, reusing
  the accepted gate lemmas. -/

/-- A `#GP` classification refuses the aligned machine store. -/
theorem avx2SpeicherSchritt_gp_a (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil) (base : Register) (src : Avx2Vektor)
    (disp : BitVec 32)
    (hgate : avx2MemZugelassen m.hw (m.bereit c) cpu x k p = true)
    (hgp : avx2GpFehler (effAddr (projZustand m c) base disp)
      .ausgerichtet = true) :
    avx2SpeicherSchritt m c cpu x k p .ausgerichtet base disp src =
      none := by
  simp only [avx2SpeicherSchritt, hgate, if_pos hgp]

/-- A `#GP` classification refuses the aligned machine load. -/
theorem avx2LadeSchritt_gp_a (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil) (base : Register) (disp : BitVec 32)
    (hgate : avx2MemZugelassen m.hw (m.bereit c) cpu x k p = true)
    (hgp : avx2GpFehler (effAddr (projZustand m c) base disp)
      .ausgerichtet = true) :
    avx2LadeSchritt m c cpu x k p .ausgerichtet base disp = none := by
  simp only [avx2LadeSchritt, hgate, if_pos hgp]

/-- Refused admission refuses the store plug (validator admission,
    not a hardware fault). -/
theorem avx2SpeicherSchritt_profil (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil) (f : Avx2MemForm) (base : Register)
    (disp : BitVec 32) (v : Avx2Vektor)
    (h : avx2MemZugelassen m.hw (m.bereit c) cpu x k p = false) :
    avx2SpeicherSchritt m c cpu x k p f base disp v = none := by
  simp only [avx2SpeicherSchritt, h]

/-- Refused admission refuses the load plug. -/
theorem avx2LadeSchritt_profil (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil) (f : Avx2MemForm) (base : Register)
    (disp : BitVec 32)
    (h : avx2MemZugelassen m.hw (m.bereit c) cpu x k p = false) :
    avx2LadeSchritt m c cpu x k p f base disp = none := by
  simp only [avx2LadeSchritt, h]

/-- A store without write permission at any chunk-zero byte refuses
    on the machine (the `#GP` classification passes; the byte issue
    fails). -/
theorem avx2SpeicherSchritt_schreibrecht (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil) (base : Register) (disp : BitVec 32)
    (v : Avx2Vektor) (k0 : Nat) (hk0 : k0 < 8)
    (hgate : avx2MemZugelassen m.hw (m.bereit c) cpu x k p = true)
    (hperm : (tsoAnsicht m).mem.schreibbar
      (addrOff (effAddr (projZustand m c) base disp) k0) = false) :
    avx2SpeicherSchritt m c cpu x k p .unausgerichtet base disp v =
      none := by
  have hn : avx2Speichern (tsoAnsicht m) c
      (effAddr (projZustand m c) base disp) v = none := by
    have hmem := avx2Eintraege_mem_c0_entry
      (effAddr (projZustand m c) base disp) v k0 hk0
    exact avx2Speichern_verweigert_bei _ _ _ _ _ hmem hperm
  have hgp : avx2GpFehler (effAddr (projZustand m c) base disp)
      .unausgerichtet = false :=
    avx2Gp_nie_unausgerichtet _
  have hneg : ¬ avx2GpFehler (effAddr (projZustand m c) base disp)
      .unausgerichtet = true := by
    simp [hgp]
  simp only [avx2SpeicherSchritt, hgate, if_neg hneg, hn]

/-- A YMM load fails wherever its low chunk load fails. -/
theorem avx2Laden_verweigert_lo (s : TSOZustand) (c : Nat)
    (a : Adresse) (h : avx2Acht s c a = none) :
    avx2Laden s c a = none := by
  unfold avx2Laden
  rw [h]

/-- A load without read permission at any chunk-zero byte refuses
    on the machine. -/
theorem avx2LadeSchritt_leserecht (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (p : Avx2Profil) (base : Register) (disp : BitVec 32)
    (k0 : Nat) (hk0 : k0 < 8)
    (hgate : avx2MemZugelassen m.hw (m.bereit c) cpu x k p = true)
    (hperm : loadByte (tsoAnsicht m) c
      (addrOff (effAddr (projZustand m c) base disp) k0) = none) :
    avx2LadeSchritt m c cpu x k p .unausgerichtet base disp = none := by
  have hnA : avx2Acht (tsoAnsicht m) c
      (effAddr (projZustand m c) base disp) = none :=
    avx2Acht_verweigert _ _ _ k0 hk0 hperm
  have hnV : avx2Laden (tsoAnsicht m) c
      (effAddr (projZustand m c) base disp) = none :=
    avx2Laden_verweigert_lo _ _ _ hnA
  have hgp : avx2GpFehler (effAddr (projZustand m c) base disp)
      .unausgerichtet = false :=
    avx2Gp_nie_unausgerichtet _
  have hneg : ¬ avx2GpFehler (effAddr (projZustand m c) base disp)
      .unausgerichtet = true := by
    simp [hgp]
  simp only [avx2LadeSchritt, hgate, if_neg hneg, hnV]

/-! ## 15. Joint witness: two cores, buffered 32-byte store.

  Core 0 issues a buffered 32-byte store of a recognizable value
  (chunk words 1, 2, 3, 4) at the 32-aligned address 8192; core 0
  observes it by forwarding while core 1 still reads zero; the
  full drain observably changes shared memory on both cores, with
  the torn halfway state standing. Every claim below is a closed
  decidable observation; no machine equality is ever decided. -/

/-- Witness data address: 32-aligned. -/
def avx2WitAdr : Adresse := BitVec.ofNat 64 8192

/-- Witness misaligned address: sixteen past the boundary. -/
def avx2WitFehlAdr : Adresse := BitVec.ofNat 64 8208

/-- Witness data permission: thirty-two bytes at 8192. -/
def avx2WitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8192 + 32)

/-- Witness memory: all zero bytes, data read/write. -/
def avx2WitMem : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0, lesbar := avx2WitDaten,
    schreibbar := avx2WitDaten, ausfuehrbar := fun _ => false }

/-- Witness YMM value: chunk words 1, 2, 3, 4. -/
def avx2WitV : Avx2Vektor := ⟨vecJoin 1 2, vecJoin 3 4⟩

/-- The aligned form is clean at the witness address. -/
theorem avx2Wit_gp_ok :
    avx2GpFehler avx2WitAdr .ausgerichtet = false := by
  decide

/-- The aligned form faults sixteen past the boundary. -/
theorem avx2Wit_gp_fehler :
    avx2GpFehler avx2WitFehlAdr .ausgerichtet = true := by
  decide

/-- Witness start TSO state: zeroed memory, empty buffers. -/
def avx2WitS0 : TSOZustand := ⟨avx2WitMem, fun _ => []⟩

/-- Core 0 issues the thirty-two bytes. -/
def avx2WitS1 : Option TSOZustand :=
  avx2Speichern avx2WitS0 0 avx2WitAdr avx2WitV

/-- Read a buffer length out of a TSO outcome. -/
def avx2BufOut (o : Option TSOZustand) (c : Nat) : Option Nat :=
  match o with
  | some s => some (s.puffer c).length
  | none => none

/-- The store issues exactly thirty-two buffer entries. -/
theorem avx2Wit_s1_buflen : avx2BufOut avx2WitS1 0 = some 32 := by
  decide

/-- Core 0 observes its own value (forwarding). -/
def avx2WitLoadEigen : Option (Option Avx2Vektor) :=
  match avx2WitS1 with
  | some s => some (avx2Laden s 0 avx2WitAdr)
  | none => none

/-- Core 1 observes the old value (no foreign forwarding). -/
def avx2WitLoadFremd : Option (Option Avx2Vektor) :=
  match avx2WitS1 with
  | some s => some (avx2Laden s 1 avx2WitAdr)
  | none => none

/-- Forwarding: core 0 reads its own unflushed value. -/
theorem avx2Wit_weiterleitung :
    avx2WitLoadEigen = some (some avx2WitV) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem avx2Wit_fremd_alt :
    avx2WitLoadFremd = some (some ⟨0, 0⟩) := by
  decide

/-- The full thirty-two drain over the store successor. -/
def avx2WitDrain : Option TSOZustand :=
  match avx2WitS1 with
  | some s => avx2Drain s 0 (avx2Eintraege avx2WitAdr avx2WitV)
  | none => none

/-- The low-sixteen drain: the torn halfway state. -/
def avx2WitDrainLo : Option TSOZustand :=
  match avx2WitS1 with
  | some s => avx2Drain s 0 (avx2EintraegeLo avx2WitAdr avx2WitV)
  | none => none

/-- Read a drained shared-memory byte. -/
def avx2DrainMemOut (o : Option TSOZustand) (a : Adresse) :
    Option Byte :=
  match o with
  | some s => some (s.mem.bytes a)
  | none => none

/-- Read a drained load observation. -/
def avx2DrainLoad (o : Option TSOZustand) (c : Nat) (a : Adresse) :
    Option (Option Byte) :=
  match o with
  | some s => some (loadByte s c a)
  | none => none

/-- The data cell starts zeroed: the run really changes memory. -/
theorem avx2Wit_anfang_null :
    avx2WitMem.bytes avx2WitAdr = BitVec.ofNat 8 0 := rfl

/-- The drain changes shared memory: the first byte reads `0x01`. -/
theorem avx2Wit_spuelung_aendert_speicher :
    avx2DrainMemOut avx2WitDrain avx2WitAdr =
      some (BitVec.ofNat 8 1) := by
  decide

/-- The drain installs the last chunk: offset 24 reads `0x04`. -/
theorem avx2Wit_spuelung_letzt :
    avx2DrainMemOut avx2WitDrain (BitVec.ofNat 64 8216) =
      some (BitVec.ofNat 8 4) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem avx2Wit_fremd_neu :
    avx2DrainLoad avx2WitDrain 1 avx2WitAdr =
      some (some (BitVec.ofNat 8 1)) := by
  decide

/-- Torn halfway: the first byte is new after sixteen drains. -/
theorem avx2Wit_teil_neu :
    avx2DrainMemOut avx2WitDrainLo avx2WitAdr =
      some (BitVec.ofNat 8 1) := by
  decide

/-- Torn halfway: offset sixteen still reads pre-drain. -/
theorem avx2Wit_teil_alt :
    avx2DrainMemOut avx2WitDrainLo (BitVec.ofNat 64 8208) =
      some (BitVec.ofNat 8 0) := by
  decide

/-! ## 16. Machine witness and the joint theorem.

  The store plug runs on a two-core coherent machine over the
  witness readiness; the reached successor carries thirty-two
  buffer entries and is an extended step. A refused profile is an
  explicit refusal step. -/

/-- Witness core-0 registers: data address in rax. -/
def avx2WitReg0 : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 8192
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Witness core data: core 0 runs the address, core 1 idles. -/
def avx2WitKern : Nat → HwKern
  | 0 => ⟨avx2WitReg0, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0,
      kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    baseline silicon with OS vector state. -/
def avx2WitStart : HwMaschine :=
  ⟨avx2WitMem, avx2WitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed: full silicon admits all. -/
theorem avx2WitStart_wf : HwWf avx2WitStart := by
  intro c f _
  cases f <;> rfl

/-- The effective address at the witness core is the data cell. -/
theorem avx2Wit_eff :
    effAddr (projZustand avx2WitStart 0) .rax (0 : BitVec 32) =
      avx2WitAdr := by
  decide

/-- Write permission across all four witness chunks. -/
theorem avx2Wit_perm0 :
    schreibbar8 (tsoAnsicht avx2WitStart).mem avx2WitAdr = true := by
  decide

/-- Write permission across all four witness chunks. -/
theorem avx2Wit_perm1 :
    schreibbar8 (tsoAnsicht avx2WitStart).mem
      (vecHiAddr avx2WitAdr) = true := by
  decide

/-- Write permission across all four witness chunks. -/
theorem avx2Wit_perm2 :
    schreibbar8 (tsoAnsicht avx2WitStart).mem
      (addrOff avx2WitAdr 16) = true := by
  decide

/-- Write permission across all four witness chunks. -/
theorem avx2Wit_perm3 :
    schreibbar8 (tsoAnsicht avx2WitStart).mem
      (vecHiAddr (addrOff avx2WitAdr 16)) = true := by
  decide

/-- The gate admits over the witness machine: profiles are the
    baseline ones. -/
theorem avx2Wit_gate_m :
    avx2MemZugelassen avx2WitStart.hw (avx2WitStart.bereit 0)
      avx2WitCpu avx2WitXcr0 basisKontrolle avx2WitProfil = true :=
  avx2Wit_gate

/-- The store plug reaches a successor with thirty-two buffer
    entries, and it is an extended step. -/
theorem avx2Wit_store_schritt :
    ∃ m2 : HwMaschine,
      avx2SpeicherSchritt avx2WitStart 0 avx2WitCpu avx2WitXcr0
          basisKontrolle avx2WitProfil .unausgerichtet .rax
          (0 : BitVec 32) avx2WitV = some m2 ∧
        (m2.puffer 0).length = 32 ∧
        HwAvx2Schritt avx2WitStart m2 (.speichere 0 avx2WitCpu
          avx2WitXcr0 basisKontrolle avx2WitProfil .unausgerichtet
          .rax (0 : BitVec 32) avx2WitV) := by
  have hgp : avx2GpFehler
      (effAddr (projZustand avx2WitStart 0) .rax (0 : BitVec 32))
      .unausgerichtet = false :=
    avx2Gp_nie_unausgerichtet _
  have hneg : ¬ avx2GpFehler
      (effAddr (projZustand avx2WitStart 0) .rax (0 : BitVec 32))
      .unausgerichtet = true :=
    fun hcon => Bool.false_ne_true (hgp.symm.trans hcon)
  have heff := avx2Wit_eff
  obtain ⟨s', hs'⟩ := avx2Speichern_erfolg (tsoAnsicht avx2WitStart)
    0 avx2WitAdr avx2WitV avx2Wit_perm0 avx2Wit_perm1 avx2Wit_perm2
    avx2Wit_perm3
  have hsI : avx2Speichern (tsoAnsicht avx2WitStart) 0
      (effAddr (projZustand avx2WitStart 0) .rax (0 : BitVec 32))
      avx2WitV = some s' := by
    rw [heff]
    exact hs'
  have hplug : avx2SpeicherSchritt avx2WitStart 0 avx2WitCpu
      avx2WitXcr0 basisKontrolle avx2WitProfil .unausgerichtet .rax
      (0 : BitVec 32) avx2WitV = some (setTso avx2WitStart s') := by
    simp only [avx2SpeicherSchritt, avx2Wit_gate_m, if_neg hneg,
      hsI]
  have hbuf : (s'.puffer 0).length = 32 := by
    have ha := avx2Speichern_haengt_an (tsoAnsicht avx2WitStart) s'
      0 avx2WitAdr avx2WitV hs'
    have hempty : (tsoAnsicht avx2WitStart).puffer 0 = [] := rfl
    rw [hempty] at ha
    have hl := avx2Eintraege_laenge avx2WitAdr avx2WitV
    simp [ha, hl]
  refine ⟨setTso avx2WitStart s', hplug, ?_, ?_⟩
  · show (s'.puffer 0).length = 32
    exact hbuf
  · exact avx2Speichere_ist_schritt avx2WitStart 0 avx2WitCpu
      avx2WitXcr0 basisKontrolle avx2WitProfil .unausgerichtet .rax
      (0 : BitVec 32) avx2WitV _ hplug

/-- A refused profile is an explicit refusal step on the machine. -/
theorem avx2Wit_fehler_schritt :
    HwAvx2Schritt avx2WitStart avx2WitStart (.verweigert 1) :=
  .fehler avx2Wit_neg_cpu

/-- THE JOINT WITNESS: a reached two-core run that buffers a
    32-byte store under the named profile (thirty-two entries,
    owner-only forwarding), drains it into shared memory (0
    becomes `0x01` at the base and `0x04` at offset 24, observed
    from both cores, torn halfway) -- with the alignment, gate and
    profile refusals beside it. Non-degenerate: the drain changes
    ACTUAL shared memory. -/
theorem avx2Wit_zeuge :
    avx2BufOut avx2WitS1 0 = some 32 ∧
      avx2WitLoadEigen = some (some avx2WitV) ∧
      avx2WitLoadFremd = some (some ⟨0, 0⟩) ∧
      avx2WitMem.bytes avx2WitAdr = BitVec.ofNat 8 0 ∧
      avx2DrainMemOut avx2WitDrain avx2WitAdr =
        some (BitVec.ofNat 8 1) ∧
      avx2DrainMemOut avx2WitDrain (BitVec.ofNat 64 8216) =
        some (BitVec.ofNat 8 4) ∧
      avx2DrainLoad avx2WitDrain 1 avx2WitAdr =
        some (some (BitVec.ofNat 8 1)) ∧
      avx2DrainMemOut avx2WitDrainLo avx2WitAdr =
        some (BitVec.ofNat 8 1) ∧
      avx2DrainMemOut avx2WitDrainLo (BitVec.ofNat 64 8208) =
        some (BitVec.ofNat 8 0) ∧
      avx2GpFehler avx2WitAdr .ausgerichtet = false ∧
      avx2GpFehler avx2WitFehlAdr .ausgerichtet = true ∧
      avx2MemZugelassen basisHw basisBereit basisCpu avx2WitXcr0
        basisKontrolle avx2WitProfil = false ∧
      (∃ m2 : HwMaschine,
        avx2SpeicherSchritt avx2WitStart 0 avx2WitCpu avx2WitXcr0
            basisKontrolle avx2WitProfil .unausgerichtet .rax
            (0 : BitVec 32) avx2WitV = some m2 ∧
          (m2.puffer 0).length = 32 ∧
          HwAvx2Schritt avx2WitStart m2 (.speichere 0 avx2WitCpu
            avx2WitXcr0 basisKontrolle avx2WitProfil .unausgerichtet
            .rax (0 : BitVec 32) avx2WitV)) ∧
      HwAvx2Schritt avx2WitStart avx2WitStart (.verweigert 1) ∧
      HwWf avx2WitStart := by
  refine ⟨avx2Wit_s1_buflen, avx2Wit_weiterleitung, avx2Wit_fremd_alt,
    avx2Wit_anfang_null, avx2Wit_spuelung_aendert_speicher,
    avx2Wit_spuelung_letzt, avx2Wit_fremd_neu, avx2Wit_teil_neu,
    avx2Wit_teil_alt, avx2Wit_gp_ok, avx2Wit_gp_fehler,
    avx2Wit_neg_cpu, avx2Wit_store_schritt, avx2Wit_fehler_schritt,
    avx2WitStart_wf⟩

/- CUTS: what is not proved here.

   - No hardware correspondence: the two 256-bit shapes, the
     32-byte #GP rule for the aligned form, the 32-byte footprint
     order and the named-profile gate are stated architectural
     facts in long-documented shape (DIRECT-COMPILER-DESIGN
     §§2C/2D/6; Intel SDM 325462-093US September 2026 local
     snapshot `.tmp/HARDWARE-REFERENCES/`, same edition the
     accepted 128-bit rows cite). Silicon correspondence of the
     alignment boundary, exception class and CPUID/XCR0 bit
     positions against the official manuals stays OPEN and is
     claimed nowhere. OS configuration and context-preservation
     code remain user logic: checked inputs, never
     assumed-correct behaviour.
   - No whole-vector atomicity: every 32-byte memory row is
     thirty-two per-byte TSO events (oldest-first issues,
     oldest-first drains). Torn intermediates stand
     (`avx2Drain_teilt16`, the accepted tearing shape at 32
     bytes); footprint disjointness never implies atomicity or
     reordering. Per-access TSO granularity beyond bytes, the GX
     refinement and any source correspondence stay open.
   - No YMM register file: store values are handed to the plug
     and loads are state-unchanged observations; binding YMM
     state (including upper-lane zeroing/VEX semantics) stays
     with the State lane, decode/encode with the Vex lane, lane
     arithmetic with the Ops lane. The plugs take effective
     addresses through the accepted `effAddr` (no second address
     model) but perform no fetch: the no-forgery discipline for
     decoded AVX2 forms stays with the Vex lane.
   - No source/IR/ABI/loader/entry/budget link: no per-access
     target-to-W/GX simulation, no budget transfer, no progress
     or call-log effect is proved; the full bridge to W/GX is not
     claimed. Fault trap classes beyond the #GP/permission
     refusal shapes (#NM, #UD, #PF ordering) are absent.
   - The accepted 256-bit refusal rows elsewhere
     (`stufe_avx256_verweigert`, `avx2_reihe_verweigert_immer`)
     are untouched: this file's strictly stronger named-profile
     gate admits a disjoint optional case and weakens no
     existing refusal.
-/

#print axioms avx2GpFehler
#print axioms avx2Gp_ausgerichtet_fehler
#print axioms avx2Gp_ausgerichtet_ok
#print axioms avx2Eintraege_laenge
#print axioms avx2Eintraege_zerlegt
#print axioms avx2Fuss_halb
#print axioms avx2Eintraege_mem_fuss
#print axioms avx2Eintraege_nodup_addr
#print axioms avx2MemZugelassen
#print axioms avx2Mem_braucht_profil
#print axioms avx2Mem_braucht_cpu
#print axioms avx2Mem_ohne_profil
#print axioms avx2Mem_ohne_cpu
#print axioms avx2Wit_gate
#print axioms avx2Speichern_haengt_an
#print axioms avx2Speichern_kein_speicher
#print axioms avx2Speichern_erfolg
#print axioms avx2Speichern_verweigert_bei
#print axioms avx2Acht_ist_read64
#print axioms avx2Laden_ist_avx2Read
#print axioms avx2Weiterleitung
#print axioms avx2Drain_schreibt
#print axioms avx2Drain_teilt16
#print axioms avx2Teilwort_keine_gruppe
#print axioms avx2Gruppe_verweigert_bei_fremdeintrag
#print axioms hwAvx2Schritt_wf
#print axioms hwAvx2Schritt_einbettet
#print axioms hwAvx2Schritt_projiziert
#print axioms adapterAvx2Mem_speichere
#print axioms adapterAvx2Mem_fremder_kern_speichere
#print axioms avx2Speichere_ist_schritt
#print axioms avx2Lade_ist_schritt
#print axioms avx2SpeicherSchritt_gp_a
#print axioms avx2LadeSchritt_gp_a
#print axioms avx2SpeicherSchritt_profil
#print axioms avx2SpeicherSchritt_schreibrecht
#print axioms avx2LadeSchritt_leserecht
#print axioms avx2Wit_zeuge
#print axioms avx2Wit_store_schritt

end Gabbro.Grammatik.X86
