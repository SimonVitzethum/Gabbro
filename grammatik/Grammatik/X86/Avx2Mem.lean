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

/- CUTS:
   Skeleton only: forms are named, nothing is proved yet.
-/

#print axioms Avx2MemForm

end Gabbro.Grammatik.X86
