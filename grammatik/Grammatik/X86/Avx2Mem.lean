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

/- CUTS:
   Skeleton only: forms are named, nothing is proved yet.
-/

#print axioms Avx2MemForm

end Gabbro.Grammatik.X86
