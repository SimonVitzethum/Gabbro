/-
  File:      Grammatik/X86/HwXsaveFull.lean
  Subject:   Full XSAVE area: x87 block, MXCSR_MASK, XSAVE header and
             the YMM_Hi128 component on the coherent multicore machine.

  Lane 1303: follow-up of lane 1247 (`HwContextState.lean`). Reuses
  `HwMaschine`/`HwSchritt`/`HwWf`/`HwAdapter` (HardwareExecution §11),
  `issueByte`/`loadByte`/`flushKern`/`issueListe` (TSO), the footprint
  helpers (`ctxAlle`, `fxEintraegeAux`, `neuestens_einmal`,
  `neuestens_nicht_enthalten`, `ctxLadeAux`, `ctxLade_geladen`,
  `ctxFalte`, `ctxNull`, `ctxByte`, `fxDekodiere`, `ctxOffsets` and
  the MXCSR/XMM image lemmas), `YmmDatei`/`xmmSet` (Avx2State),
  `xcr0SseBereit`/`xcr0AvxBereit` (VectorHardwareProfile),
  `mxcsrReserviertFrei` (FpControlHardwareForms) and `ArchFehler`
  (HwFaults) unchanged, never copied. The x87 FPU itself stays out of
  scope: its area bytes are an opaque but footprint-exact block.
-/
import Grammatik.X86.HwContextState
import Grammatik.X86.Avx2State
import Grammatik.X86.HwFaults

namespace Gabbro.Grammatik.X86

/-- Opaque x87 image: the 152 area bytes (0-23, 32-159) indexed
    linearly; the FPU has no model in this tree. -/
abbrev X87Bild := Nat → Byte

/-- Opaque x87 reset image (FINIT target): byte values are NOT
    claimed here (out of scope, see CUTS). -/
def x87Reset : X87Bild := fun _ => BitVec.ofNat 8 0

/-- XSAVE header image: XSTATE_BV plus XCOMP_BV (zero standard form). -/
structure XsaveKopf where
  bv : BitVec 64
  comp : BitVec 64
  deriving DecidableEq, Repr

/-- Standard-form header: XCOMP_BV is zero (no compaction). -/
def kopfStandard (sse avx : Bool) : XsaveKopf :=
  ⟨BitVec.ofNat 64 (1 + (if sse then 2 else 0) + (if avx then 4 else 0)),
    BitVec.ofNat 64 0⟩

/-- Standard-form header carries a zero compaction word. -/
theorem kopfStandard_comp (sse avx : Bool) :
    (kopfStandard sse avx).comp = BitVec.ofNat 64 0 := rfl

/-! ## 0. Footprint: x87 block, mask, legacy, header, YMM.

  The footprint is RFBM-selective (silicon writes only the
  enabled components): x87, mask and header always; the legacy
  MXCSR/XMM part iff SSE is saved; the YMM part iff AVX is saved. -/

/-- x87 footprint: bytes 0-23 then 32-159 (152 bytes). -/
def x87Offsets : List Nat :=
  List.range 24 ++ (List.range 128).map (32 + ·)

/-- MXCSR_MASK footprint: bytes 28-31. -/
def maskOffsets : List Nat := (List.range 4).map (28 + ·)

/-- XSAVE header footprint: bytes 512-575. -/
def kopfOffsets : List Nat := (List.range 64).map (512 + ·)

/-- YMM_Hi128 footprint: bytes 576-831. -/
def ymmOffsets : List Nat := (List.range 256).map (576 + ·)

/-- Full footprint for the saved set (`sse`, `avx`): 220 bytes
    without any component, 480 with SSE, 736 with both.
    Parenthesised right-nested so the membership API below reads. -/
def xsaveOffsets (sse avx : Bool) : List Nat :=
  x87Offsets ++ (maskOffsets ++ ((if sse then ctxOffsets else []) ++
    (kopfOffsets ++ (if avx then ymmOffsets else []))))

/-- x87 offsets fit the legacy half. -/
theorem x87Offsets_klein (i : Nat) (h : i ∈ x87Offsets) : i < 160 := by
  have h1 : ∀ j ∈ List.range 24, j < 160 := by
    intro j hj
    have := List.mem_range.mp hj
    omega
  have h2 : ∀ j ∈ (List.range 128).map (32 + ·), j < 160 := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
    have := List.mem_range.mp hk
    omega
  unfold x87Offsets at h
  rcases List.mem_append.mp h with hL | hR
  · exact h1 _ hL
  · exact h2 _ hR

/-- Mask offsets fit the legacy word. -/
theorem maskOffsets_klein (i : Nat) (h : i ∈ maskOffsets) :
    i < 32 := by
  unfold maskOffsets at h
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  have := List.mem_range.mp hk
  omega

/-- Header offsets fit the header. -/
theorem kopfOffsets_klein (i : Nat) (h : i ∈ kopfOffsets) :
    i < 576 := by
  unfold kopfOffsets at h
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  have := List.mem_range.mp hk
  omega

/-- YMM offsets fit the area. -/
theorem ymmOffsets_klein (i : Nat) (h : i ∈ ymmOffsets) : i < 832 := by
  unfold ymmOffsets at h
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  have := List.mem_range.mp hk
  omega

/-- Conditional legacy members are bounded (no case split on the
    flag inside a dependent hypothesis). -/
theorem bedingt_klein_legacy (sse : Bool) (i : Nat)
    (h : i ∈ (if sse then ctxOffsets else [])) : i < 512 := by
  by_cases hsse : sse = true
  · have e : (if sse then ctxOffsets else []) = ctxOffsets :=
      if_pos hsse
    rw [e] at h
    exact ctxOffsets_klein _ h
  · have e : (if sse then ctxOffsets else []) = ([] : List Nat) :=
      if_neg hsse
    rw [e] at h
    simp at h

/-- Conditional YMM members are bounded. -/
theorem bedingt_klein_ymm (avx : Bool) (i : Nat)
    (h : i ∈ (if avx then ymmOffsets else [])) : i < 832 := by
  by_cases havx : avx = true
  · have e : (if avx then ymmOffsets else []) = ymmOffsets :=
      if_pos havx
    rw [e] at h
    exact ymmOffsets_klein _ h
  · have e : (if avx then ymmOffsets else []) = ([] : List Nat) :=
      if_neg havx
    rw [e] at h
    simp at h

/-- Every footprint offset fits the 832-byte area. -/
theorem xsaveOffsets_klein (sse avx : Bool) (i : Nat)
    (h : i ∈ xsaveOffsets sse avx) : i < 832 := by
  unfold xsaveOffsets at h
  rcases List.mem_append.mp h with h1 | hrest
  · exact Nat.lt_trans (x87Offsets_klein _ h1) (by decide)
  · rcases List.mem_append.mp hrest with h2 | hrest2
    · exact Nat.lt_trans (maskOffsets_klein _ h2) (by decide)
    · rcases List.mem_append.mp hrest2 with h3 | hrest3
      · exact Nat.lt_trans (bedingt_klein_legacy _ _ h3) (by decide)
      · rcases List.mem_append.mp hrest3 with h4 | h5
        · exact Nat.lt_trans (kopfOffsets_klein _ h4) (by decide)
        · exact bedingt_klein_ymm _ _ h5

/-- Append preserves nodup across a disjoint right part. -/
theorem nodup_append_of (l₁ l₂ : List Nat)
    (h1 : l₁.Nodup) (h2 : l₂.Nodup)
    (hd : ∀ x ∈ l₁, x ∉ l₂) : (l₁ ++ l₂).Nodup := by
  induction l₁ with
  | nil =>
    simp only [List.nil_append]
    exact h2
  | cons a t ih =>
    have hhd : a ∉ t := (List.nodup_cons.mp h1).1
    have htl : t.Nodup := (List.nodup_cons.mp h1).2
    have hd' : ∀ x ∈ t, x ∉ l₂ := by
      intro x hx
      exact hd x (List.mem_cons.mpr (Or.inr hx))
    have ha : a ∉ l₂ := hd a (List.mem_cons.mpr (Or.inl rfl))
    have iht := ih htl hd'
    have e : (a :: t) ++ l₂ = a :: (t ++ l₂) := rfl
    rw [e]
    have hni : a ∉ t ++ l₂ := by
      intro hm
      rcases List.mem_append.mp hm with hmt | hml
      · exact hhd hmt
      · exact ha hml
    exact List.nodup_cons.mpr ⟨hni, iht⟩

/-- x87 members live in the two x87 bands. -/
theorem x87mem (x : Nat) (h : x ∈ x87Offsets) :
    x < 24 ∨ (32 ≤ x ∧ x < 160) := by
  unfold x87Offsets at h
  rcases List.mem_append.mp h with hL | hR
  · exact Or.inl (List.mem_range.mp hL)
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hR
    have := List.mem_range.mp ht
    exact Or.inr ⟨by omega, by omega⟩

/-- Mask members live in the mask word. -/
theorem maskmem (x : Nat) (h : x ∈ maskOffsets) :
    28 ≤ x ∧ x < 32 := by
  unfold maskOffsets at h
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  have := List.mem_range.mp hk
  exact ⟨by omega, by omega⟩

/-- Legacy members live in the MXCSR word or the XMM slots. -/
theorem ctxmem (x : Nat) (h : x ∈ ctxOffsets) :
    (24 ≤ x ∧ x < 28) ∨ (160 ≤ x ∧ x < 416) := by
  unfold ctxOffsets at h
  rcases List.mem_append.mp h with hL | hR
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hL
    have := List.mem_range.mp hk
    exact Or.inl ⟨by omega, by omega⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hR
    have := List.mem_range.mp hk
    exact Or.inr ⟨by omega, by omega⟩

/-- Header members live in the header. -/
theorem kopfmem (x : Nat) (h : x ∈ kopfOffsets) :
    512 ≤ x ∧ x < 576 := by
  unfold kopfOffsets at h
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  have := List.mem_range.mp hk
  exact ⟨by omega, by omega⟩

/-- YMM members live in the extended region. -/
theorem ymmmem (x : Nat) (h : x ∈ ymmOffsets) :
    576 ≤ x ∧ x < 832 := by
  unfold ymmOffsets at h
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  have := List.mem_range.mp hk
  exact ⟨by omega, by omega⟩

set_option maxRecDepth 10000 in
/-- The x87 image is duplicate-free. -/
theorem x87Offsets_nodup : x87Offsets.Nodup := by
  unfold x87Offsets
  apply nodup_append_of _ _ (by decide) (by decide)
  intro x hx hm
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
  have htr := List.mem_range.mp ht
  have := List.mem_range.mp hx
  omega

/-- The mask image is duplicate-free. -/
theorem maskOffsets_nodup : maskOffsets.Nodup := by decide

set_option maxRecDepth 10000 in
/-- The header image is duplicate-free. -/
theorem kopfOffsets_nodup : kopfOffsets.Nodup := by decide

set_option maxRecDepth 10000 in
/-- The YMM image is duplicate-free. -/
theorem ymmOffsets_nodup : ymmOffsets.Nodup := by decide

/-- Nothing is a member of the empty list. -/
theorem nicht_mem_nil (x : Nat) : x ∉ ([] : List Nat) := by
  intro hm
  simp at hm

/-- The x87 block meets no later footprint part. -/
theorem disj_x87_rest (sse avx : Bool) (x : Nat)
    (hx : x ∈ x87Offsets)
    (hm : x ∈ maskOffsets ++ ((if sse then ctxOffsets else []) ++
      (kopfOffsets ++ (if avx then ymmOffsets else [])))) :
    False := by
  rcases List.mem_append.mp hm with hm1 | hmrest
  · have h1 := x87mem _ hx
    have h2 := maskmem _ hm1
    omega
  · rcases List.mem_append.mp hmrest with hm2 | hmrest2
    · by_cases hsse : sse = true
      · have e : (if sse then ctxOffsets else []) = ctxOffsets :=
          if_pos hsse
        rw [e] at hm2
        have h1 := x87mem _ hx
        have h2 := ctxmem _ hm2
        omega
      · have e : (if sse then ctxOffsets else []) = ([] : List Nat) :=
          if_neg hsse
        rw [e] at hm2
        exact nicht_mem_nil _ hm2
    · rcases List.mem_append.mp hmrest2 with hm3 | hm4
      · have h1 := x87mem _ hx
        have h2 := kopfmem _ hm3
        omega
      · by_cases havx : avx = true
        · have e : (if avx then ymmOffsets else []) = ymmOffsets :=
            if_pos havx
          rw [e] at hm4
          have h1 := x87mem _ hx
          have h2 := ymmmem _ hm4
          omega
        · have e : (if avx then ymmOffsets else []) = ([] : List Nat) :=
            if_neg havx
          rw [e] at hm4
          exact nicht_mem_nil _ hm4

/-- The mask word meets no later footprint part. -/
theorem disj_maske_rest (sse avx : Bool) (x : Nat)
    (hx : x ∈ maskOffsets)
    (hm : x ∈ (if sse then ctxOffsets else []) ++
      (kopfOffsets ++ (if avx then ymmOffsets else []))) :
    False := by
  rcases List.mem_append.mp hm with hm1 | hmrest
  · by_cases hsse : sse = true
    · have e : (if sse then ctxOffsets else []) = ctxOffsets :=
        if_pos hsse
      rw [e] at hm1
      have h1 := maskmem _ hx
      have h2 := ctxmem _ hm1
      omega
    · have e : (if sse then ctxOffsets else []) = ([] : List Nat) :=
        if_neg hsse
      rw [e] at hm1
      exact nicht_mem_nil _ hm1
  · rcases List.mem_append.mp hmrest with hm2 | hm3
    · have h1 := maskmem _ hx
      have h2 := kopfmem _ hm2
      omega
    · by_cases havx : avx = true
      · have e : (if avx then ymmOffsets else []) = ymmOffsets :=
          if_pos havx
        rw [e] at hm3
        have h1 := maskmem _ hx
        have h2 := ymmmem _ hm3
        omega
      · have e : (if avx then ymmOffsets else []) = ([] : List Nat) :=
          if_neg havx
        rw [e] at hm3
        exact nicht_mem_nil _ hm3

/-- The legacy part meets no later footprint part. -/
theorem disj_ctx_rest (avx : Bool) (x : Nat)
    (hx : x ∈ ctxOffsets)
    (hm : x ∈ kopfOffsets ++ (if avx then ymmOffsets else [])) :
    False := by
  rcases List.mem_append.mp hm with hm1 | hm2
  · have h1 := ctxmem _ hx
    have h2 := kopfmem _ hm1
    omega
  · by_cases havx : avx = true
    · have e2 : (if avx then ymmOffsets else []) = ymmOffsets :=
        if_pos havx
      rw [e2] at hm2
      have h1 := ctxmem _ hx
      have h2 := ymmmem _ hm2
      omega
    · have e2 : (if avx then ymmOffsets else []) = ([] : List Nat) :=
        if_neg havx
      rw [e2] at hm2
      exact nicht_mem_nil _ hm2

/-- The header meets no later footprint part. -/
theorem disj_kopf_rest (avx : Bool) (x : Nat)
    (hx : x ∈ kopfOffsets)
    (hm : x ∈ (if avx then ymmOffsets else [])) :
    False := by
  by_cases havx : avx = true
  · have e : (if avx then ymmOffsets else []) = ymmOffsets :=
      if_pos havx
    rw [e] at hm
    have h1 := kopfmem _ hx
    have h2 := ymmmem _ hm
    omega
  · have e : (if avx then ymmOffsets else []) = ([] : List Nat) :=
      if_neg havx
    rw [e] at hm
    exact nicht_mem_nil _ hm

/-- The full footprint has no duplicate offset. -/
theorem xsaveOffsets_nodup (sse avx : Bool) :
    (xsaveOffsets sse avx).Nodup := by
  have hDE : (kopfOffsets ++
      (if avx then ymmOffsets else [])).Nodup := by
    apply nodup_append_of _ _ kopfOffsets_nodup
    · by_cases havx : avx = true
      · have e : (if avx then ymmOffsets else []) = ymmOffsets :=
          if_pos havx
        rw [e]
        exact ymmOffsets_nodup
      · have e : (if avx then ymmOffsets else []) = ([] : List Nat) :=
          if_neg havx
        rw [e]
        exact List.nodup_nil
    · intro x hx hm
      exact disj_kopf_rest avx x hx hm
  unfold xsaveOffsets
  apply nodup_append_of _ _ x87Offsets_nodup
  · apply nodup_append_of _ _ maskOffsets_nodup
    · by_cases hsse : sse = true
      · have e : (if sse then ctxOffsets else []) = ctxOffsets :=
          if_pos hsse
        rw [e]
        exact nodup_append_of _ _ ctxOffsets_nodup hDE
          (disj_ctx_rest avx)
      · have e : (if sse then ctxOffsets else []) = ([] : List Nat) :=
          if_neg hsse
        rw [e, List.nil_append]
        exact hDE
    · intro x hx hm
      exact disj_maske_rest sse avx x hx hm
  · intro x hx hm
    exact disj_x87_rest sse avx x hx hm

/-- x87 low offsets are in the footprint. -/
theorem xsaveOffsets_x87_lo (t : Nat) (ht : t < 24) (sse avx : Bool) :
    t ∈ xsaveOffsets sse avx := by
  have h1 : t ∈ x87Offsets := by
    unfold x87Offsets
    exact List.mem_append.mpr
      (Or.inl (List.mem_range.mpr ht))
  unfold xsaveOffsets
  exact List.mem_append.mpr (Or.inl h1)

/-- x87 high offsets are in the footprint. -/
theorem xsaveOffsets_x87_hi (t : Nat) (ht : t < 128) (sse avx : Bool) :
    32 + t ∈ xsaveOffsets sse avx := by
  have h1 : 32 + t ∈ x87Offsets := by
    unfold x87Offsets
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
      ⟨t, List.mem_range.mpr ht, rfl⟩))
  unfold xsaveOffsets
  exact List.mem_append.mpr (Or.inl h1)

/-- Mask offsets are in the footprint. -/
theorem xsaveOffsets_maske (j : Nat) (hj : j < 4) (sse avx : Bool) :
    28 + j ∈ xsaveOffsets sse avx := by
  have h1 : 28 + j ∈ maskOffsets :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  unfold xsaveOffsets
  exact List.mem_append.mpr
    (Or.inr (List.mem_append.mpr (Or.inl h1)))

/-- MXCSR offsets are in the footprint where SSE is saved. -/
theorem xsaveOffsets_mxcsr (j : Nat) (hj : j < 4) (hs : sse = true)
    (avx : Bool) :
    24 + j ∈ xsaveOffsets sse avx := by
  have e : (if sse then ctxOffsets else []) = ctxOffsets :=
    if_pos hs
  have h1 : 24 + j ∈ (if sse then ctxOffsets else []) := by
    rw [e]
    exact ctxOffsets_mxcsr j hj
  unfold xsaveOffsets
  exact List.mem_append.mpr
    (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr
      (Or.inl h1)))))

/-- XMM slot offsets are in the footprint where SSE is saved. -/
theorem xsaveOffsets_xmm (n j : Nat) (hn : n < 16) (hj : j < 16)
    (hs : sse = true) (avx : Bool) :
    160 + 16 * n + j ∈ xsaveOffsets sse avx := by
  have e : (if sse then ctxOffsets else []) = ctxOffsets :=
    if_pos hs
  have h1 : 160 + 16 * n + j ∈ (if sse then ctxOffsets else []) := by
    rw [e]
    exact ctxOffsets_xmm n j hn hj
  unfold xsaveOffsets
  exact List.mem_append.mpr
    (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr
      (Or.inl h1)))))

/-- Header offsets are in the footprint. -/
theorem xsaveOffsets_kopf (t : Nat) (ht : t < 64) (sse avx : Bool) :
    512 + t ∈ xsaveOffsets sse avx := by
  have h1 : 512 + t ∈ kopfOffsets :=
    List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩
  unfold xsaveOffsets
  exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
    (List.mem_append.mpr (Or.inr (List.mem_append.mpr
      (Or.inl h1)))))))

/-- YMM slot offsets are in the footprint where AVX is saved. -/
theorem xsaveOffsets_ymm (n j : Nat) (hn : n < 16) (hj : j < 16)
    (sse : Bool) (ha : avx = true) :
    576 + 16 * n + j ∈ xsaveOffsets sse avx := by
  have e : (if avx then ymmOffsets else []) = ymmOffsets :=
    if_pos ha
  have h1 : 576 + 16 * n + j ∈ (if avx then ymmOffsets else []) := by
    rw [e]
    exact List.mem_map.mpr ⟨16 * n + j, List.mem_range.mpr (by omega),
      by omega⟩
  unfold xsaveOffsets
  exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
    (List.mem_append.mpr (Or.inr (List.mem_append.mpr
      (Or.inr h1)))))))

/-! ## 1. Full area image: x87 block, mask, header, YMM.

  Selected 64-bit standard XSAVE map (SDM 325462-093US Vol.1 Ch.13,
  clone-local provenance only): legacy FXSAVE bytes 0-511 with x87
  state at 0-23 and 32-159 (opaque here), MXCSR at 24-27, MXCSR_MASK
  at 28-31, XMM0-15 at 160-415; the XSAVE header at 512-575
  (XSTATE_BV at 512-519, XCOMP_BV at 520-527, zero in the standard
  form); the AVX YMM_Hi128 component at 576-831 (16 registers of
  16 upper-half bytes). Total standard SSE+AVX area: 832 bytes. -/

/-- Full standard area length with SSE and AVX enabled. -/
def xsaveLaenge : Nat := 832

/-- Header image byte: BV low word, then the (zero) compaction word,
    then zero padding. -/
def kopfByte (h : XsaveKopf) (i : Nat) : Byte :=
  if i < 8 then wortByte h.bv i
  else if i < 16 then wortByte h.comp (i - 8)
  else BitVec.ofNat 8 0

/-- Header image at a BV offset is the BV byte. -/
theorem kopfByte_lo (h : XsaveKopf) (j : Nat) (hj : j < 8) :
    kopfByte h j = wortByte h.bv j := by
  unfold kopfByte
  have e1 : j < 8 := hj
  rw [if_pos e1]

/-- Header image at a compaction-word offset is the word byte. -/
theorem kopfByte_hi (h : XsaveKopf) (j : Nat) (hj : j < 8) :
    kopfByte h (8 + j) = wortByte h.comp j := by
  unfold kopfByte
  have e1 : ¬ (8 + j < 8) := by omega
  have e2 : 8 + j < 16 := by omega
  have e3 : 8 + j - 8 = j := by omega
  rw [if_neg e1, if_pos e2, e3]

/-- YMM upper-half image at absolute area offset `i` (base 576,
    16 bytes per register, low word then high word). -/
def ymmByteAt (y : YmmDatei) (i : Nat) : Byte :=
  match xmmVonIdx ((i - 576) / 16) with
  | some r =>
    if (i - 576) % 16 < 8 then wortByte (vLo (y r)) ((i - 576) % 16)
    else wortByte (vHi (y r)) ((i - 576) % 16 - 8)
  | none => BitVec.ofNat 8 0

/-- The full area image: x87 opaque bytes, legacy MXCSR/XMM via the
    accepted `ctxByte`, mask bytes, zero gaps, header, YMM. -/
def xsaveByte (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) : Nat → Byte :=
  fun i =>
  if i < 24 then b i
  else if i < 28 then ctxByte k x i
  else if i < 32 then mxcsrByte mm (i - 28)
  else if i < 160 then b (i - 8)
  else if i < 416 then ctxByte k x i
  else if i < 512 then BitVec.ofNat 8 0
  else if i < 576 then kopfByte h (i - 512)
  else if i < 832 then ymmByteAt y i
  else BitVec.ofNat 8 0

/-- Image at an x87 low offset is the opaque byte. -/
theorem xsaveByte_x87_lo (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (t : Nat)
    (ht : t < 24) :
    xsaveByte k x b mm h y t = b t := by
  unfold xsaveByte
  rw [if_pos ht]

/-- Image at an x87 high offset is the opaque byte. -/
theorem xsaveByte_x87_hi (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (t : Nat)
    (ht : t < 128) :
    xsaveByte k x b mm h y (32 + t) = b (24 + t) := by
  unfold xsaveByte
  have e1 : ¬ (32 + t < 24) := by omega
  have e2 : ¬ (32 + t < 28) := by omega
  have e3 : ¬ (32 + t < 32) := by omega
  have e4 : 32 + t < 160 := by omega
  have e5 : 32 + t - 8 = 24 + t := by omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_pos e4, e5]

/-- Image at a mask offset is the mask byte. -/
theorem xsaveByte_maske (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (j : Nat)
    (hj : j < 4) :
    xsaveByte k x b mm h y (28 + j) = mxcsrByte mm j := by
  unfold xsaveByte
  have e1 : ¬ (28 + j < 24) := by omega
  have e2 : ¬ (28 + j < 28) := by omega
  have e3 : 28 + j < 32 := by omega
  have e4 : 28 + j - 28 = j := by omega
  rw [if_neg e1, if_neg e2, if_pos e3, e4]

/-- Image at an MXCSR offset is the control byte (legacy path). -/
theorem xsaveByte_mxcsr (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (j : Nat)
    (hj : j < 4) :
    xsaveByte k x b mm h y (24 + j) = mxcsrByte k.mxcsr j := by
  unfold xsaveByte
  have e1 : ¬ (24 + j < 24) := by omega
  have e2 : 24 + j < 28 := by omega
  rw [if_neg e1, if_pos e2]
  exact ctxByte_mxcsr k x j hj

/-- Image at an XMM low-half offset (legacy path). -/
theorem xsaveByte_xmm_lo (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (r : XmmReg)
    (j : Nat) (hj : j < 8) :
    xsaveByte k x b mm h y (160 + 16 * xmmIdx r + j) =
      wortByte (vLo (x r)) j := by
  have hn := xmmIdx_klein r
  unfold xsaveByte
  have e1 : ¬ (160 + 16 * xmmIdx r + j < 24) := by omega
  have e2 : ¬ (160 + 16 * xmmIdx r + j < 28) := by omega
  have e3 : ¬ (160 + 16 * xmmIdx r + j < 32) := by omega
  have e4 : ¬ (160 + 16 * xmmIdx r + j < 160) := by omega
  have e5 : 160 + 16 * xmmIdx r + j < 416 := by omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_pos e5]
  exact ctxByte_xmm_lo k x r j hj

/-- Image at an XMM high-half offset (legacy path). -/
theorem xsaveByte_xmm_hi (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (r : XmmReg)
    (j : Nat) (hj : j < 8) :
    xsaveByte k x b mm h y (168 + 16 * xmmIdx r + j) =
      wortByte (vHi (x r)) j := by
  have hn := xmmIdx_klein r
  unfold xsaveByte
  have e1 : ¬ (168 + 16 * xmmIdx r + j < 24) := by omega
  have e2 : ¬ (168 + 16 * xmmIdx r + j < 28) := by omega
  have e3 : ¬ (168 + 16 * xmmIdx r + j < 32) := by omega
  have e4 : ¬ (168 + 16 * xmmIdx r + j < 160) := by omega
  have e5 : 168 + 16 * xmmIdx r + j < 416 := by omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_pos e5]
  exact ctxByte_xmm_hi k x r j hj

/-- Image at a header offset is the header byte. -/
theorem xsaveByte_kopf (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (t : Nat)
    (ht : t < 64) :
    xsaveByte k x b mm h y (512 + t) = kopfByte h t := by
  unfold xsaveByte
  have e1 : ¬ (512 + t < 24) := by omega
  have e2 : ¬ (512 + t < 28) := by omega
  have e3 : ¬ (512 + t < 32) := by omega
  have e4 : ¬ (512 + t < 160) := by omega
  have e5 : ¬ (512 + t < 416) := by omega
  have e6 : ¬ (512 + t < 512) := by omega
  have e7 : 512 + t < 576 := by omega
  have e8 : 512 + t - 512 = t := by omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5,
    if_neg e6, if_pos e7, e8]

/-- Image at a YMM low-half offset. -/
theorem xsaveByte_ymm_lo (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (r : XmmReg)
    (j : Nat) (hj : j < 8) :
    xsaveByte k x b mm h y (576 + 16 * xmmIdx r + j) =
      wortByte (vLo (y r)) j := by
  have hn := xmmIdx_klein r
  unfold xsaveByte
  have e1 : ¬ (576 + 16 * xmmIdx r + j < 24) := by omega
  have e2 : ¬ (576 + 16 * xmmIdx r + j < 28) := by omega
  have e3 : ¬ (576 + 16 * xmmIdx r + j < 32) := by omega
  have e4 : ¬ (576 + 16 * xmmIdx r + j < 160) := by omega
  have e5 : ¬ (576 + 16 * xmmIdx r + j < 416) := by omega
  have e6 : ¬ (576 + 16 * xmmIdx r + j < 512) := by omega
  have e7 : ¬ (576 + 16 * xmmIdx r + j < 576) := by omega
  have e8 : 576 + 16 * xmmIdx r + j < 832 := by omega
  have e9 : (576 + 16 * xmmIdx r + j - 576) / 16 = xmmIdx r := by omega
  have e10 : (576 + 16 * xmmIdx r + j - 576) % 16 = j := by omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5,
    if_neg e6, if_neg e7, if_pos e8]
  unfold ymmByteAt
  rw [e9, e10]
  simp [xmmVonIdx_idx, hj]

/-- Image at a YMM high-half offset. -/
theorem xsaveByte_ymm_hi (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (r : XmmReg)
    (j : Nat) (hj : j < 8) :
    xsaveByte k x b mm h y (584 + 16 * xmmIdx r + j) =
      wortByte (vHi (y r)) j := by
  have e : 584 + 16 * xmmIdx r + j = 576 + 16 * xmmIdx r + (8 + j) := by
    omega
  have hn := xmmIdx_klein r
  rw [e]
  unfold xsaveByte
  have e1 : ¬ (576 + 16 * xmmIdx r + (8 + j) < 24) := by omega
  have e2 : ¬ (576 + 16 * xmmIdx r + (8 + j) < 28) := by omega
  have e3 : ¬ (576 + 16 * xmmIdx r + (8 + j) < 32) := by omega
  have e4 : ¬ (576 + 16 * xmmIdx r + (8 + j) < 160) := by omega
  have e5 : ¬ (576 + 16 * xmmIdx r + (8 + j) < 416) := by omega
  have e6 : ¬ (576 + 16 * xmmIdx r + (8 + j) < 512) := by omega
  have e7 : ¬ (576 + 16 * xmmIdx r + (8 + j) < 576) := by omega
  have e8 : 576 + 16 * xmmIdx r + (8 + j) < 832 := by omega
  have e9 : (576 + 16 * xmmIdx r + (8 + j) - 576) / 16 = xmmIdx r := by
    omega
  have e10 : (576 + 16 * xmmIdx r + (8 + j) - 576) % 16 = 8 + j := by
    omega
  have e11 : ¬ (8 + j < 8) := by omega
  have e12 : 8 + j - 8 = j := by omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5,
    if_neg e6, if_neg e7, if_pos e8]
  unfold ymmByteAt
  rw [e9, e10]
  simp [xmmVonIdx_idx, e11, e12]

/-! ## 2. Decode and the pure round trip. -/

/-- x87 area offset of the linear opaque index. -/
def x87AreaOff (t : Nat) : Nat := if t < 24 then t else 32 + (t - 24)

/-- Decoded full state: legacy components share the accepted
    `fxDekodiere` shape; x87 is the opaque copy; mask, header and
    YMM decode from their fields. -/
structure XsaveBild where
  mxcsr : MXCSR
  xmm : XmmDatei
  x87img : X87Bild
  maske : BitVec 32
  kopf : XsaveKopf
  ymm : YmmDatei

/-- Decode a full area image. -/
def xsaveDekodiere (f : Nat → Byte) : XsaveBild :=
  ⟨mxcsrAusBytes (fun i => f (24 + i)),
   fun r => vecJoin
     (bytesWort (fun j : Fin 8 => f (160 + 16 * xmmIdx r + j.val)))
     (bytesWort (fun j : Fin 8 => f (168 + 16 * xmmIdx r + j.val))),
   fun t => f (x87AreaOff t),
   mxcsrAusBytes (fun i => f (28 + i)),
   ⟨bytesWort (fun j : Fin 8 => f (512 + j.val)),
    bytesWort (fun j : Fin 8 => f (520 + j.val))⟩,
   fun r => vecJoin
     (bytesWort (fun j : Fin 8 => f (576 + 16 * xmmIdx r + j.val)))
     (bytesWort (fun j : Fin 8 => f (584 + 16 * xmmIdx r + j.val)))⟩

/-- x87 area offset in the low range. -/
theorem x87AreaOff_lo (t : Nat) (ht : t < 24) :
    x87AreaOff t = t := by
  unfold x87AreaOff
  rw [if_pos ht]

/-- x87 area offset in the high range. -/
theorem x87AreaOff_hi (t : Nat) (ht : ¬ t < 24) :
    x87AreaOff t = 32 + (t - 24) := by
  unfold x87AreaOff
  rw [if_neg ht]

/-- Opaque x87 round trip: decoding the saved image recovers every
    opaque byte. -/
theorem xsaveRundlauf_x87 (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (t : Nat)
    (ht : t < 152) :
    (xsaveDekodiere (xsaveByte k x b mm h y)).x87img t = b t := by
  unfold xsaveDekodiere
  simp only
  by_cases hl : t < 24
  · rw [x87AreaOff_lo t hl]
    exact xsaveByte_x87_lo k x b mm h y t hl
  · rw [x87AreaOff_hi t hl]
    have ht24 : t - 24 < 128 := by omega
    have hrw := xsaveByte_x87_hi k x b mm h y (t - 24) ht24
    rw [hrw]
    have : 24 + (t - 24) = t := by omega
    rw [this]

/-- Mask round trip (the accepted MXCSR image lemmas, reused). -/
theorem xsaveRundlauf_maske (k : FPKontext) (x : XmmDatei)
    (b : X87Bild) (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) :
    (xsaveDekodiere (xsaveByte k x b mm h y)).maske = mm := by
  unfold xsaveDekodiere
  simp only
  have hkong := mxcsrAusBytes_kongr _ _
    (fun i hi => xsaveByte_maske k x b mm h y i hi)
  rw [hkong]
  exact mxcsr_rundlauf mm

/-- Header round trip: BV and compaction word decode back. -/
theorem xsaveRundlauf_kopf (k : FPKontext) (x : XmmDatei)
    (b : X87Bild) (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) :
    (xsaveDekodiere (xsaveByte k x b mm h y)).kopf = h := by
  have hbv : bytesWort (fun j : Fin 8 =>
      xsaveByte k x b mm h y (512 + j.val)) = h.bv := by
    have heq : (fun j : Fin 8 => xsaveByte k x b mm h y (512 + j.val)) =
        (fun j : Fin 8 => kopfByte h j.val) := by
      funext j
      have ht64 : j.val < 64 := by have h8 := j.isLt; omega
      exact xsaveByte_kopf k x b mm h y j.val ht64
    rw [heq]
    have heq2 : (fun j : Fin 8 => kopfByte h j.val) =
        (fun j : Fin 8 => wortByte h.bv j.val) := by
      funext j
      exact kopfByte_lo h j.val j.isLt
    rw [heq2]
    exact bytesWort_wortByte h.bv
  have hcomp : bytesWort (fun j : Fin 8 =>
      xsaveByte k x b mm h y (520 + j.val)) = h.comp := by
    have heq : (fun j : Fin 8 => xsaveByte k x b mm h y (520 + j.val)) =
        (fun j : Fin 8 => kopfByte h (8 + j.val)) := by
      funext j
      have e : 520 + j.val = 512 + (8 + j.val) := by omega
      have ht64 : 8 + j.val < 64 := by have h8 := j.isLt; omega
      rw [e]
      exact xsaveByte_kopf k x b mm h y (8 + j.val) ht64
    rw [heq]
    have heq2 : (fun j : Fin 8 => kopfByte h (8 + j.val)) =
        (fun j : Fin 8 => wortByte h.comp j.val) := by
      funext j
      exact kopfByte_hi h j.val j.isLt
    rw [heq2]
    exact bytesWort_wortByte h.comp
  unfold xsaveDekodiere
  simp only
  cases h with
  | mk bv comp =>
    simp only at hbv hcomp ⊢
    rw [hbv, hcomp]

/-- Legacy MXCSR/XMM round trip (the accepted pure identity). -/
theorem xsaveRundlauf_legacy (k : FPKontext) (x : XmmDatei)
    (b : X87Bild) (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) :
    (xsaveDekodiere (xsaveByte k x b mm h y)).mxcsr = k.mxcsr ∧
      ∀ r : XmmReg,
        (xsaveDekodiere (xsaveByte k x b mm h y)).xmm r = x r := by
  refine ⟨?_, ?_⟩
  · unfold xsaveDekodiere
    simp only
    have hkong := mxcsrAusBytes_kongr _ _
      (fun i hi => xsaveByte_mxcsr k x b mm h y i hi)
    rw [hkong]
    exact mxcsr_rundlauf k.mxcsr
  · intro r
    unfold xsaveDekodiere
    simp only
    have hlo : (fun j : Fin 8 => xsaveByte k x b mm h y
        (160 + 16 * xmmIdx r + j.val)) =
        (fun j : Fin 8 => wortByte (vLo (x r)) j.val) := by
      funext j
      exact xsaveByte_xmm_lo k x b mm h y r j.val j.isLt
    have hhi : (fun j : Fin 8 => xsaveByte k x b mm h y
        (168 + 16 * xmmIdx r + j.val)) =
        (fun j : Fin 8 => wortByte (vHi (x r)) j.val) := by
      funext j
      exact xsaveByte_xmm_hi k x b mm h y r j.val j.isLt
    rw [hlo, hhi, bytesWort_wortByte, bytesWort_wortByte]
    exact vecJoin_split (x r)

/-- YMM round trip: decoding the saved upper halves recovers them. -/
theorem xsaveRundlauf_ymm (k : FPKontext) (x : XmmDatei)
    (b : X87Bild) (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei)
    (r : XmmReg) :
    (xsaveDekodiere (xsaveByte k x b mm h y)).ymm r = y r := by
  unfold xsaveDekodiere
  simp only
  have hlo : (fun j : Fin 8 => xsaveByte k x b mm h y
      (576 + 16 * xmmIdx r + j.val)) =
      (fun j : Fin 8 => wortByte (vLo (y r)) j.val) := by
    funext j
    exact xsaveByte_ymm_lo k x b mm h y r j.val j.isLt
  have hhi : (fun j : Fin 8 => xsaveByte k x b mm h y
      (584 + 16 * xmmIdx r + j.val)) =
      (fun j : Fin 8 => wortByte (vHi (y r)) j.val) := by
    funext j
    exact xsaveByte_ymm_hi k x b mm h y r j.val j.isLt
  rw [hlo, hhi, bytesWort_wortByte, bytesWort_wortByte]
  exact vecJoin_split (y r)

/-- MXCSR decoding depends only on the footprint bytes
    where SSE is saved. -/
theorem xsaveKongr_mxcsr (f g : Nat → Byte) (sse avx : Bool)
    (hs : sse = true)
    (h : ∀ i ∈ xsaveOffsets sse avx, f i = g i) :
    (xsaveDekodiere f).mxcsr = (xsaveDekodiere g).mxcsr := by
  unfold xsaveDekodiere
  simp only
  apply mxcsrAusBytes_kongr
  intro i hi
  exact h (24 + i) (xsaveOffsets_mxcsr i hi hs avx)

/-- XMM decoding depends only on the footprint bytes
    where SSE is saved. -/
theorem xsaveKongr_xmm (f g : Nat → Byte) (sse avx : Bool)
    (hs : sse = true)
    (h : ∀ i ∈ xsaveOffsets sse avx, f i = g i) (r : XmmReg) :
    (xsaveDekodiere f).xmm r = (xsaveDekodiere g).xmm r := by
  unfold xsaveDekodiere
  simp only
  have hn := xmmIdx_klein r
  have hlo : (fun j : Fin 8 => f (160 + 16 * xmmIdx r + j.val)) =
      (fun j : Fin 8 => g (160 + 16 * xmmIdx r + j.val)) := by
    funext j
    have hj16 : j.val < 16 := by have h8 := j.isLt; omega
    exact h _ (xsaveOffsets_xmm (xmmIdx r) j.val hn hj16 hs avx)
  have hhi : (fun j : Fin 8 => f (168 + 16 * xmmIdx r + j.val)) =
      (fun j : Fin 8 => g (168 + 16 * xmmIdx r + j.val)) := by
    funext j
    have hj16 : 8 + j.val < 16 := by have := j.isLt; omega
    have e : 168 + 16 * xmmIdx r + j.val =
        160 + 16 * xmmIdx r + (8 + j.val) := by omega
    rw [e]
    exact h _ (xsaveOffsets_xmm (xmmIdx r) (8 + j.val) hn hj16 hs avx)
  rw [hlo, hhi]

/-- x87 decoding depends only on the footprint bytes (always saved). -/
theorem xsaveKongr_x87 (f g : Nat → Byte) (sse avx : Bool)
    (h : ∀ i ∈ xsaveOffsets sse avx, f i = g i) (t : Nat)
    (ht : t < 152) :
    (xsaveDekodiere f).x87img t = (xsaveDekodiere g).x87img t := by
  unfold xsaveDekodiere
  simp only
  by_cases hl : t < 24
  · rw [x87AreaOff_lo t hl]
    exact h t (xsaveOffsets_x87_lo t hl sse avx)
  · rw [x87AreaOff_hi t hl]
    exact h _ (xsaveOffsets_x87_hi (t - 24) (by omega) sse avx)

/-- Mask decoding depends only on the footprint bytes. -/
theorem xsaveKongr_maske (f g : Nat → Byte) (sse avx : Bool)
    (h : ∀ i ∈ xsaveOffsets sse avx, f i = g i) :
    (xsaveDekodiere f).maske = (xsaveDekodiere g).maske := by
  unfold xsaveDekodiere
  simp only
  apply mxcsrAusBytes_kongr
  intro i hi
  exact h (28 + i) (xsaveOffsets_maske i hi sse avx)

/-- Header decoding depends only on the footprint bytes. -/
theorem xsaveKongr_kopf (f g : Nat → Byte) (sse avx : Bool)
    (h : ∀ i ∈ xsaveOffsets sse avx, f i = g i) :
    (xsaveDekodiere f).kopf = (xsaveDekodiere g).kopf := by
  unfold xsaveDekodiere
  simp only
  have hbv : (fun j : Fin 8 => f (512 + j.val)) =
      (fun j : Fin 8 => g (512 + j.val)) := by
    funext j
    have ht64 : j.val < 64 := by have h8 := j.isLt; omega
    exact h _ (xsaveOffsets_kopf j.val ht64 sse avx)
  have hcomp : (fun j : Fin 8 => f (520 + j.val)) =
      (fun j : Fin 8 => g (520 + j.val)) := by
    funext j
    have e : 520 + j.val = 512 + (8 + j.val) := by omega
    have ht64 : 8 + j.val < 64 := by have h8 := j.isLt; omega
    rw [e]
    exact h _ (xsaveOffsets_kopf (8 + j.val) ht64 sse avx)
  rw [hbv, hcomp]

/-- YMM decoding depends only on the footprint bytes
    where AVX is saved. -/
theorem xsaveKongr_ymm (f g : Nat → Byte) (sse avx : Bool)
    (ha : avx = true)
    (h : ∀ i ∈ xsaveOffsets sse avx, f i = g i) (r : XmmReg) :
    (xsaveDekodiere f).ymm r = (xsaveDekodiere g).ymm r := by
  unfold xsaveDekodiere
  simp only
  have hn := xmmIdx_klein r
  have hlo : (fun j : Fin 8 => f (576 + 16 * xmmIdx r + j.val)) =
      (fun j : Fin 8 => g (576 + 16 * xmmIdx r + j.val)) := by
    funext j
    have hj16 : j.val < 16 := by have h8 := j.isLt; omega
    exact h _ (xsaveOffsets_ymm (xmmIdx r) j.val hn hj16 sse ha)
  have hhi : (fun j : Fin 8 => f (584 + 16 * xmmIdx r + j.val)) =
      (fun j : Fin 8 => g (584 + 16 * xmmIdx r + j.val)) := by
    funext j
    have hj16 : 8 + j.val < 16 := by have := j.isLt; omega
    have e : 584 + 16 * xmmIdx r + j.val =
        576 + 16 * xmmIdx r + (8 + j.val) := by omega
    rw [e]
    exact h _ (xsaveOffsets_ymm (xmmIdx r) (8 + j.val) hn hj16 sse ha)
  rw [hlo, hhi]

/-! ## 3. Machine state, save entries, and the TSO bridge.

  The full machine pairs the coherent YMM machine (which carries
  XMM, YMM upper halves, registers and the TSO view) with the
  opaque per-core x87 image and the per-core MXCSR_MASK value (a
  fixed CPU constant, carried, never computed). -/

/-- Full XSAVE machine: coherent YMM machine plus per-core opaque
    x87 image and mask value. -/
structure XsaveMaschine where
  ym : YmmMaschine
  x87 : Nat → X87Bild
  maske : Nat → BitVec 32

/-- The coherent machine inside the full state. -/
def xsaveHw (v : XsaveMaschine) : HwMaschine := v.ym.hw

/-- Well-formedness is the coherent well-formedness. -/
def XsaveWf (v : XsaveMaschine) : Prop := HwWf v.ym.hw

/-- Memory/buffer update from a TSO successor: core data, x87
    images and masks are untouched. -/
def setXsaveTso (v : XsaveMaschine) (s : TSOZustand) : XsaveMaschine :=
  { v with ym := ⟨setTso v.ym.hw s, v.ym.ober⟩ }

/-- The TSO view of a memory/buffer update is the successor state. -/
theorem setXsaveTso_ansicht (v : XsaveMaschine) (s : TSOZustand) :
    tsoAnsicht (xsaveHw (setXsaveTso v s)) = s := by
  unfold xsaveHw setXsaveTso
  simp only
  exact setTso_ansicht v.ym.hw s

/-- A save changes no core data. -/
theorem setXsaveTso_kern (v : XsaveMaschine) (s : TSOZustand)
    (c : Nat) :
    (xsaveHw (setXsaveTso v s)).kerne c = (xsaveHw v).kerne c := rfl

/-- A save keeps the x87 images. -/
theorem setXsaveTso_x87 (v : XsaveMaschine) (s : TSOZustand) :
    (setXsaveTso v s).x87 = v.x87 := rfl

/-- A save keeps the masks. -/
theorem setXsaveTso_maske (v : XsaveMaschine) (s : TSOZustand) :
    (setXsaveTso v s).maske = v.maske := rfl

/-- A save keeps the YMM upper files. -/
theorem setXsaveTso_ober (v : XsaveMaschine) (s : TSOZustand) :
    (setXsaveTso v s).ym.ober = v.ym.ober := rfl

/-- Memory/buffer updates preserve well-formedness. -/
theorem setXsaveTso_wf (v : XsaveMaschine) (s : TSOZustand)
    (h : XsaveWf v) : XsaveWf (setXsaveTso v s) :=
  setTso_wf v.ym.hw s h

/-- Install restored components on core `c`: FP context, XMM file,
    YMM upper file and the opaque x87 image. Masks are never
    installed (silicon leaves MXCSR_MASK unchanged on restore). -/
def setXsaveKern (v : XsaveMaschine) (c : Nat) (k : FPKontext)
    (x : XmmDatei) (y : YmmDatei) (b : X87Bild) : XsaveMaschine :=
  ⟨⟨setKernDaten v.ym.hw c
      ⟨(v.ym.hw.kerne c).register, (v.ym.hw.kerne c).flags,
        (v.ym.hw.kerne c).rip, x, k⟩,
    fun d => if d = c then y else v.ym.ober d⟩,
   fun d => if d = c then b else v.x87 d, v.maske⟩

/-- Installed core answers the restored control word. -/
theorem setXsaveKern_fp (v : XsaveMaschine) (c : Nat) (k : FPKontext)
    (x : XmmDatei) (y : YmmDatei) (b : X87Bild) :
    (((xsaveHw (setXsaveKern v c k x y b)).kerne c).fp).mxcsr =
      k.mxcsr := by
  unfold xsaveHw setXsaveKern
  rw [setKernDaten_fp]

/-- Installed core answers the restored XMM file. -/
theorem setXsaveKern_xmm (v : XsaveMaschine) (c : Nat) (k : FPKontext)
    (x : XmmDatei) (y : YmmDatei) (b : X87Bild) (r : XmmReg) :
    ((xsaveHw (setXsaveKern v c k x y b)).kerne c).xmm r = x r := by
  unfold xsaveHw setXsaveKern
  rw [setKernDaten_xmm]

/-- Installed core answers the restored upper half. -/
theorem setXsaveKern_ober (v : XsaveMaschine) (c : Nat) (k : FPKontext)
    (x : XmmDatei) (y : YmmDatei) (b : X87Bild) (r : XmmReg) :
    ((setXsaveKern v c k x y b).ym.ober c) r = y r := by
  show ((if c = c then y else v.ym.ober c)) r = y r
  rw [if_pos rfl]

/-- Installed core answers the restored opaque byte. -/
theorem setXsaveKern_x87 (v : XsaveMaschine) (c : Nat) (k : FPKontext)
    (x : XmmDatei) (y : YmmDatei) (b : X87Bild) (t : Nat) :
    ((setXsaveKern v c k x y b).x87 c) t = b t := by
  show ((if c = c then b else v.x87 c)) t = b t
  rw [if_pos rfl]

/-- An install keeps the mask (silicon ignores it on restore). -/
theorem setXsaveKern_maske (v : XsaveMaschine) (c : Nat) (k : FPKontext)
    (x : XmmDatei) (y : YmmDatei) (b : X87Bild) :
    (setXsaveKern v c k x y b).maske = v.maske := rfl

/-- An install preserves well-formedness (profiles untouched). -/
theorem setXsaveKern_wf (v : XsaveMaschine) (c : Nat) (k : FPKontext)
    (x : XmmDatei) (y : YmmDatei) (b : X87Bild)
    (h : XsaveWf v) : XsaveWf (setXsaveKern v c k x y b) :=
  setKernDaten_wf v.ym.hw c _ h

/-- The save entries of a full state at area base `a`. -/
def xsaveEintraege (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (sse avx : Bool)
    (a : Adresse) : List TSOEintrag :=
  fxEintraegeAux (xsaveByte k x b mm h y) a (xsaveOffsets sse avx)

/-- Observed fault preconditions for one request. Each is a
    CHECKED input (oracle): its derivation (CR0.TS, CPUID
    FXSR/XSAVE, LOCK prefix, segment limits, paging, CPL/AC)
    belongs to the feature/paging apparatus, never assumed here.
    Priority in the step below is NM > UD > GP > SS > PF > AC. -/
structure XsaveFehlerIn where
  nm : Bool
  cpuidOk : Bool
  lock : Bool
  ss : Bool
  pf : Bool
  ac : Bool

/-- Machine-level outcomes: successor, refusal, or the
    architectural fault class (the accepted `ArchFehler`). -/
inductive XsaveAusgang where
  | weiter : XsaveMaschine → XsaveAusgang
  | verweigert : XsaveAusgang
  | fehler : ArchFehler → XsaveAusgang

/-- 48-bit canonical address check (low half or sign-extended
    high half; a non-canonical XSAVE address raises #GP). -/
def xsaveKanonisch (a : Adresse) : Bool :=
  decide (a.toNat < 2 ^ 47 ∨ 2 ^ 64 - 2 ^ 47 ≤ a.toNat)

/-- One full save on core `c` at area base `a`: fault gates in
    priority order, XCR0/request gates, canonical and alignment
    gates, the permission gate over the footprint, then the
    buffered byte-issue fold. -/
def xsaveSpeichern (v : XsaveMaschine) (c : Nat) (a : Adresse)
    (xc : Xcr0Bild) (sse avx : Bool) (f : XsaveFehlerIn) :
    XsaveAusgang :=
  if f.nm then .fehler .nm
  else if !f.cpuidOk || f.lock then .fehler .ud
  else if !xc.x87 then .fehler .gp
  else if sse && !xcr0SseBereit xc then .fehler .ud
  else if avx && !xcr0AvxBereit xc then .fehler .ud
  else if !sse && !avx then .verweigert
  else if !xsaveKanonisch a then .fehler .gp
  else if !xAusgerichtet a then .fehler .gp
  else if f.ss then .fehler .ss
  else if f.pf then .fehler .pf
  else if f.ac then .fehler .ac
  else if !ctxAlle (xsaveHw v).mem.schreibbar a
      (xsaveOffsets sse avx) then .verweigert
  else match issueListe (tsoAnsicht (xsaveHw v)) c
      (xsaveEintraege ((xsaveHw v).kerne c).fp ((xsaveHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
        sse avx a) with
  | none => .verweigert
  | some s' => .weiter (setXsaveTso v s')

/-- Success shape: a successful save is a successful issue fold. -/
theorem xsaveSpeichern_erfolg (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (m' : XsaveMaschine)
    (h : xsaveSpeichern v c a xc sse avx f = .weiter m') :
    ∃ s' : TSOZustand,
      issueListe (tsoAnsicht (xsaveHw v)) c
        (xsaveEintraege ((xsaveHw v).kerne c).fp ((xsaveHw v).kerne c).xmm
          (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
          sse avx a) = some s' ∧
      m' = setXsaveTso v s' := by
  unfold xsaveSpeichern at h
  cases hn : f.nm with
  | true => simp [hn] at h
  | false =>
    cases hc : (!f.cpuidOk || f.lock) with
    | true => simp [hn, hc] at h
    | false =>
      cases hx : (!xc.x87) with
      | true => simp [hn, hc, hx] at h
      | false =>
        cases hsse : (sse && !xcr0SseBereit xc) with
        | true => simp [hn, hc, hx, hsse] at h
        | false =>
          cases havx : (avx && !xcr0AvxBereit xc) with
          | true => simp [hn, hc, hx, hsse, havx] at h
          | false =>
            cases hleer : (!sse && !avx) with
            | true => simp [hn, hc, hx, hsse, havx, hleer] at h
            | false =>
              cases hkan : (!xsaveKanonisch a) with
              | true => simp [hn, hc, hx, hsse, havx, hleer, hkan] at h
              | false =>
                cases hal : (!xAusgerichtet a) with
                | true =>
                  simp [hn, hc, hx, hsse, havx, hleer, hkan, hal] at h
                | false =>
                  cases hss : f.ss with
                  | true =>
                    simp [hn, hc, hx, hsse, havx, hleer, hkan, hal,
                      hss] at h
                  | false =>
                    cases hpf : f.pf with
                    | true =>
                      simp [hn, hc, hx, hsse, havx, hleer, hkan, hal,
                        hss, hpf] at h
                    | false =>
                      cases hac : f.ac with
                      | true =>
                        simp [hn, hc, hx, hsse, havx, hleer, hkan,
                          hal, hss, hpf, hac] at h
                      | false =>
                        cases hp : (!ctxAlle (xsaveHw v).mem.schreibbar
                            a (xsaveOffsets sse avx)) with
                        | true =>
                          simp [hn, hc, hx, hsse, havx, hleer, hkan,
                            hal, hss, hpf, hac, hp] at h
                        | false =>
                          simp [hn, hc, hx, hsse, havx, hleer, hkan,
                            hal, hss, hpf, hac, hp] at h
                          cases hs2 : issueListe (tsoAnsicht (xsaveHw v))
                              c (xsaveEintraege ((xsaveHw v).kerne c).fp
                                ((xsaveHw v).kerne c).xmm (v.x87 c)
                                (v.maske c) (kopfStandard sse avx)
                                (v.ym.ober c) sse avx a) with
                          | none =>
                            rw [hs2] at h
                            cases h
                          | some s' =>
                            have hm : setXsaveTso v s' = m' := by
                              simpa [hs2] using h
                            exact ⟨s', rfl, hm.symm⟩

/-- SAVE GOES THROUGH THE TSO BUFFER: the acting core's buffer
    grows by exactly the footprint entries. -/
theorem xsaveSpeichern_puffer (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (m' : XsaveMaschine)
    (h : xsaveSpeichern v c a xc sse avx f = .weiter m') :
    (xsaveHw m').puffer c = (xsaveHw v).puffer c ++
      xsaveEintraege ((xsaveHw v).kerne c).fp ((xsaveHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
        sse avx a := by
  obtain ⟨s', hs, rfl⟩ := xsaveSpeichern_erfolg v c a xc sse avx f m' h
  exact issueListe_haengt_an (tsoAnsicht (xsaveHw v)) s' c _ hs

/-- A save changes no canonical byte (buffer only). -/
theorem xsaveSpeichern_kein_speicher (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (m' : XsaveMaschine)
    (h : xsaveSpeichern v c a xc sse avx f = .weiter m')
    (x : Adresse) :
    (xsaveHw m').mem.bytes x = (xsaveHw v).mem.bytes x := by
  obtain ⟨s', hs, rfl⟩ := xsaveSpeichern_erfolg v c a xc sse avx f m' h
  exact issueListe_kein_speicher (tsoAnsicht (xsaveHw v)) s' c _ hs x

/-- A save preserves well-formedness (profiles untouched). -/
theorem xsaveSpeichern_wf (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (hwf : XsaveWf v) (m' : XsaveMaschine)
    (h : xsaveSpeichern v c a xc sse avx f = .weiter m') :
    XsaveWf m' := by
  obtain ⟨s', _, rfl⟩ := xsaveSpeichern_erfolg v c a xc sse avx f m' h
  exact setXsaveTso_wf v s' hwf

/-- Footprint addresses stay distinct below 832 (the accepted
    `addrOff_inj512` argument, widened: the full area reaches the
    YMM region at 576-831, so the 512 bound cannot be reused). -/
theorem addrOff_inj832 {a : Adresse} {i j : Nat}
    (hi : i < 832) (hj : j < 832)
    (h : addrOff a i = addrOff a j) : i = j := by
  unfold addrOff at h
  have h2 := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_add,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h2
  have ha := a.isLt
  omega

/-- An offset outside the list never matches the entries (832
    bound; the accepted `neuestens_nicht_enthalten` with the
    widened injectivity above). -/
theorem neuestens_nicht_enthalten832 (f : Nat → Byte) (a : Adresse)
    (os : List Nat) (k : Nat)
    (hk : k < 832) (hb : ∀ i ∈ os, i < 832)
    (h : ∀ i ∈ os, i ≠ k) :
    neuestens (fxEintraegeAux f a os) (addrOff a k) = none := by
  induction os with
  | nil => rfl
  | cons i rest ih =>
    have hi : i ≠ k := h i (by simp)
    have hni : addrOff a i ≠ addrOff a k := by
      intro he
      exact hi (addrOff_inj832 (hb i (by simp)) hk he)
    have ihr := ih (fun j hj => hb j (by simp [hj]))
      (fun j hj => h j (by simp [hj]))
    simp only [fxEintraegeAux, neuestens, ihr]
    simp [hni]

/-- A footprint offset reads its own entry byte (832 bound; the
    accepted `neuestens_einmal` with the widened injectivity). -/
theorem neuestens_einmal832 (f : Nat → Byte) (a : Adresse)
    (os : List Nat) (k : Nat) :
    ∀ (_hb : ∀ j ∈ os, j < 832) (_hk832 : k < 832),
    ∀ (_hnd : os.Nodup) (_hm : k ∈ os),
    neuestens (fxEintraegeAux f a os) (addrOff a k) = some (f k) := by
  induction os with
  | nil =>
    intro _hb _hk832 _hnd hm
    simp at hm
  | cons i rest ih =>
    intro hb hk832 hnd hm
    have hni : i ∉ rest := (List.nodup_cons.mp hnd).1
    have hmem : k = i ∨ k ∈ rest := by simpa using hm
    rcases hmem with heq | hmr
    · have hmiss : ∀ j ∈ rest, j ≠ k :=
        fun j hj hjeq => hni (heq ▸ (hjeq ▸ hj))
      have hnone := neuestens_nicht_enthalten832 f a rest k hk832
        (fun j hj => hb j (by simp [hj])) hmiss
      simp only [fxEintraegeAux, neuestens, hnone]
      rw [if_pos (by rw [heq]), heq]
    · have ihr := ih (fun j hj => hb j (by simp [hj])) hk832
        ((List.nodup_cons.mp hnd).2) hmr
      simp only [fxEintraegeAux, neuestens, ihr]

/-- FORWARDING AT SAVE: after a successful save, every footprint
    offset loads the saved image byte through the owner's buffer. -/
theorem xsaveWeiterleitung_gespeichert (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (sse avx : Bool) (s1' : TSOZustand)
    (hs : issueListe (tsoAnsicht (xsaveHw v)) c
      (xsaveEintraege ((xsaveHw v).kerne c).fp ((xsaveHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
        sse avx a) = some s1')
    (hles : ctxAlle (xsaveHw v).mem.lesbar a (xsaveOffsets sse avx)
      = true)
    (i : Nat) (hi : i ∈ xsaveOffsets sse avx) :
    loadByte s1' c (addrOff a i) =
      some (xsaveByte ((xsaveHw v).kerne c).fp ((xsaveHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
        i) := by
  have hbuf := issueListe_haengt_an (tsoAnsicht (xsaveHw v)) s1' c _ hs
  have hmem : s1'.mem = (tsoAnsicht (xsaveHw v)).mem :=
    issueListe_mem_still _ _ _ _ hs
  have hmemHw : s1'.mem = (xsaveHw v).mem := hmem
  have hlesbar : s1'.mem.lesbar (addrOff a i) = true := by
    rw [hmemHw]
    exact ctxAlle_holt (xsaveHw v).mem.lesbar a (xsaveOffsets sse avx)
      i hi hles
  have hneu : neuestens (s1'.puffer c) (addrOff a i) =
      some (xsaveByte ((xsaveHw v).kerne c).fp ((xsaveHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
        i) := by
    have he := neuestens_einmal832
      (xsaveByte ((xsaveHw v).kerne c).fp ((xsaveHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c))
      a (xsaveOffsets sse avx) i
      (fun j hj => xsaveOffsets_klein sse avx j hj)
      (xsaveOffsets_klein sse avx i hi) (xsaveOffsets_nodup sse avx) hi
    have hentries : xsaveEintraege ((xsaveHw v).kerne c).fp
        ((xsaveHw v).kerne c).xmm (v.x87 c) (v.maske c)
        (kopfStandard sse avx) (v.ym.ober c) sse avx a =
        fxEintraegeAux (xsaveByte ((xsaveHw v).kerne c).fp
          ((xsaveHw v).kerne c).xmm (v.x87 c) (v.maske c)
          (kopfStandard sse avx) (v.ym.ober c)) a
          (xsaveOffsets sse avx) := rfl
    rw [hbuf, hentries, neuestens_append, he]
  unfold loadByte
  rw [if_pos hlesbar, hneu]

/-! ## 4. Machine restore and the save/restore round trip.

  `xsaveWiederherstellen` loads the footprint through the TSO view
  (forwarding included), reassembles every saved component, and
  installs the enabled ones on the acting core, keeping
  registers/flags/RIP. The opaque x87 image is always installed;
  the mask is never installed (silicon leaves MXCSR_MASK
  unchanged); the header is decoded but not enforced (see CUTS).
  A set reserved MXCSR bit in the loaded image faults with
  `.fehler .gp` (the accepted `mxcsrReserviertFrei` refusal,
  lifted; where SSE is not restored the checked bytes are the
  zero fold base, so the check passes vacuously and nothing
  spurious is refused). -/

/-- One full restore on core `c` from area base `a`. -/
def xsaveWiederherstellen (v : XsaveMaschine) (c : Nat) (a : Adresse)
    (xc : Xcr0Bild) (sse avx : Bool) (f : XsaveFehlerIn) :
    XsaveAusgang :=
  if f.nm then .fehler .nm
  else if !f.cpuidOk || f.lock then .fehler .ud
  else if !xc.x87 then .fehler .gp
  else if sse && !xcr0SseBereit xc then .fehler .ud
  else if avx && !xcr0AvxBereit xc then .fehler .ud
  else if !sse && !avx then .verweigert
  else if !xsaveKanonisch a then .fehler .gp
  else if !xAusgerichtet a then .fehler .gp
  else if f.ss then .fehler .ss
  else if f.pf then .fehler .pf
  else if f.ac then .fehler .ac
  else if !ctxAlle (xsaveHw v).mem.lesbar a (xsaveOffsets sse avx) then
    .verweigert
  else match ctxLadeAux (tsoAnsicht (xsaveHw v)) c a
      (xsaveOffsets sse avx) with
  | none => .verweigert
  | some bs =>
    if !mxcsrReserviertFrei
        (mxcsrAusBytes (fun i => ctxFalte bs ctxNull (24 + i))) then
      .fehler .gp
    else .weiter (setXsaveKern v c
      (if sse then
        ⟨(xsaveDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
       else ((xsaveHw v).kerne c).fp)
      (if sse then (xsaveDekodiere (ctxFalte bs ctxNull)).xmm
       else ((xsaveHw v).kerne c).xmm)
      (if avx then (xsaveDekodiere (ctxFalte bs ctxNull)).ymm
       else v.ym.ober c)
      (xsaveDekodiere (ctxFalte bs ctxNull)).x87img)

/-- Success shape: a successful restore is a successful footprint
    load with a reserved-free control word where SSE is restored. -/
theorem xsaveWiederherstellen_erfolg (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (m' : XsaveMaschine)
    (h : xsaveWiederherstellen v c a xc sse avx f = .weiter m') :
    ∃ bs : List (Nat × Byte),
      ctxLadeAux (tsoAnsicht (xsaveHw v)) c a (xsaveOffsets sse avx) =
        some bs ∧
      m' = setXsaveKern v c
        (if sse then
          ⟨(xsaveDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
         else ((xsaveHw v).kerne c).fp)
        (if sse then (xsaveDekodiere (ctxFalte bs ctxNull)).xmm
         else ((xsaveHw v).kerne c).xmm)
        (if avx then (xsaveDekodiere (ctxFalte bs ctxNull)).ymm
         else v.ym.ober c)
        (xsaveDekodiere (ctxFalte bs ctxNull)).x87img := by
  unfold xsaveWiederherstellen at h
  cases hn : f.nm with
  | true => simp [hn] at h
  | false =>
    cases hc : (!f.cpuidOk || f.lock) with
    | true => simp [hn, hc] at h
    | false =>
      cases hx : (!xc.x87) with
      | true => simp [hn, hc, hx] at h
      | false =>
        cases hsse : (sse && !xcr0SseBereit xc) with
        | true => simp [hn, hc, hx, hsse] at h
        | false =>
          cases havx : (avx && !xcr0AvxBereit xc) with
          | true => simp [hn, hc, hx, hsse, havx] at h
          | false =>
            cases hleer : (!sse && !avx) with
            | true => simp [hn, hc, hx, hsse, havx, hleer] at h
            | false =>
              cases hkan : (!xsaveKanonisch a) with
              | true => simp [hn, hc, hx, hsse, havx, hleer, hkan] at h
              | false =>
                cases hal : (!xAusgerichtet a) with
                | true =>
                  simp [hn, hc, hx, hsse, havx, hleer, hkan, hal] at h
                | false =>
                  cases hss : f.ss with
                  | true =>
                    simp [hn, hc, hx, hsse, havx, hleer, hkan, hal,
                      hss] at h
                  | false =>
                    cases hpf : f.pf with
                    | true =>
                      simp [hn, hc, hx, hsse, havx, hleer, hkan, hal,
                        hss, hpf] at h
                    | false =>
                      cases hac : f.ac with
                      | true =>
                        simp [hn, hc, hx, hsse, havx, hleer, hkan,
                          hal, hss, hpf, hac] at h
                      | false =>
                        cases hp : (!ctxAlle (xsaveHw v).mem.lesbar
                            a (xsaveOffsets sse avx)) with
                        | true =>
                          simp [hn, hc, hx, hsse, havx, hleer, hkan,
                            hal, hss, hpf, hac, hp] at h
                        | false =>
                          simp [hn, hc, hx, hsse, havx, hleer, hkan,
                            hal, hss, hpf, hac, hp] at h
                          cases hbs : ctxLadeAux (tsoAnsicht (xsaveHw v))
                              c a (xsaveOffsets sse avx) with
                          | none =>
                            rw [hbs] at h
                            cases h
                          | some bs =>
                            cases hw : mxcsrReserviertFrei
                                (mxcsrAusBytes (fun i =>
                                  ctxFalte bs ctxNull (24 + i))) with
                            | false =>
                              simp [hbs, hw] at h
                            | true =>
                              simp [hbs, hw] at h
                              cases h
                              exact ⟨bs, rfl, rfl⟩

/-- A restore preserves well-formedness (profiles untouched). -/
theorem xsaveWiederherstellen_wf (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (hwf : XsaveWf v) (m' : XsaveMaschine)
    (h : xsaveWiederherstellen v c a xc sse avx f = .weiter m') :
    XsaveWf m' := by
  obtain ⟨bs, _, rfl⟩ := xsaveWiederherstellen_erfolg v c a xc sse avx
    f m' h
  exact setXsaveKern_wf v c _ _ _ _ hwf

/-- SAVE THEN RESTORE IS THE IDENTITY on the enabled components:
    restoring a just-saved area on the same core with the same
    request set recovers the opaque x87 image, the control word
    and every XMM register where SSE was saved, and every YMM
    upper half where AVX was saved. The mask is untouched by
    construction. Needs read permission beside the save's write
    permission (the restore observes through `loadByte`, which
    checks readability). -/
theorem xsaveRundlauf_maschine (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (v1 v2 : XsaveMaschine)
    (hles : ctxAlle (xsaveHw v).mem.lesbar a (xsaveOffsets sse avx)
      = true)
    (h1 : xsaveSpeichern v c a xc sse avx f = .weiter v1)
    (h2 : xsaveWiederherstellen v1 c a xc sse avx f = .weiter v2) :
    (∀ t : Nat, t < 152 → (v2.x87 c) t = (v.x87 c) t) ∧
      v2.maske c = v.maske c ∧
      (sse = true →
        (((xsaveHw v2).kerne c).fp).mxcsr =
          (((xsaveHw v).kerne c).fp).mxcsr) ∧
      (sse = true → ∀ r : XmmReg,
        ((xsaveHw v2).kerne c).xmm r =
          ((xsaveHw v).kerne c).xmm r) ∧
      (avx = true → ∀ r : XmmReg,
        (v2.ym.ober c) r = (v.ym.ober c) r) := by
  obtain ⟨s1', hs1, rfl⟩ := xsaveSpeichern_erfolg v c a xc sse avx f v1
    h1
  obtain ⟨bs, hbs, rfl⟩ := xsaveWiederherstellen_erfolg
    (setXsaveTso v s1') c a xc sse avx f v2 h2
  have hsicht : tsoAnsicht (xsaveHw (setXsaveTso v s1')) = s1' :=
    setXsaveTso_ansicht v s1'
  rw [hsicht] at hbs
  have hloads : ∀ i ∈ xsaveOffsets sse avx,
      loadByte s1' c (addrOff a i) =
        some (xsaveByte ((xsaveHw v).kerne c).fp ((xsaveHw v).kerne c).xmm
          (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
          i) :=
    xsaveWeiterleitung_gespeichert v c a sse avx s1' hs1 hles
  have hagree : ∀ i ∈ xsaveOffsets sse avx,
      ctxFalte bs ctxNull i =
        xsaveByte ((xsaveHw v).kerne c).fp ((xsaveHw v).kerne c).xmm
          (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
          i := by
    intro i hi
    exact ctxLade_geladen s1' c a
      (xsaveByte ((xsaveHw v).kerne c).fp ((xsaveHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c))
      (xsaveOffsets sse avx) ctxNull (xsaveOffsets_nodup sse avx)
      hloads bs hbs i hi
  have hx87id : ∀ t : Nat, t < 152 →
      (xsaveDekodiere (ctxFalte bs ctxNull)).x87img t = (v.x87 c) t := by
    intro t ht
    have hk := xsaveKongr_x87 (ctxFalte bs ctxNull)
      (xsaveByte ((xsaveHw v).kerne c).fp ((xsaveHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c))
      sse avx (fun i hi => hagree i hi) t ht
    rw [hk]
    exact xsaveRundlauf_x87 ((xsaveHw v).kerne c).fp
      ((xsaveHw v).kerne c).xmm (v.x87 c) (v.maske c)
      (kopfStandard sse avx) (v.ym.ober c) t ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have e1 := setXsaveKern_x87 (setXsaveTso v s1') c
      (if sse then
        ⟨(xsaveDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
       else ((xsaveHw (setXsaveTso v s1')).kerne c).fp)
      (if sse then (xsaveDekodiere (ctxFalte bs ctxNull)).xmm
       else ((xsaveHw (setXsaveTso v s1')).kerne c).xmm)
      (if avx then (xsaveDekodiere (ctxFalte bs ctxNull)).ymm
       else (setXsaveTso v s1').ym.ober c)
      (xsaveDekodiere (ctxFalte bs ctxNull)).x87img t
    rw [e1]
    exact hx87id t ht
  · have e2 := setXsaveKern_maske (setXsaveTso v s1') c
      (if sse then
        ⟨(xsaveDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
       else ((xsaveHw (setXsaveTso v s1')).kerne c).fp)
      (if sse then (xsaveDekodiere (ctxFalte bs ctxNull)).xmm
       else ((xsaveHw (setXsaveTso v s1')).kerne c).xmm)
      (if avx then (xsaveDekodiere (ctxFalte bs ctxNull)).ymm
       else (setXsaveTso v s1').ym.ober c)
      (xsaveDekodiere (ctxFalte bs ctxNull)).x87img
    rw [e2, setXsaveTso_maske]
  · intro hs
    have e3 := setXsaveKern_fp (setXsaveTso v s1') c
      (if sse then
        ⟨(xsaveDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
       else ((xsaveHw (setXsaveTso v s1')).kerne c).fp)
      (if sse then (xsaveDekodiere (ctxFalte bs ctxNull)).xmm
       else ((xsaveHw (setXsaveTso v s1')).kerne c).xmm)
      (if avx then (xsaveDekodiere (ctxFalte bs ctxNull)).ymm
       else (setXsaveTso v s1').ym.ober c)
      (xsaveDekodiere (ctxFalte bs ctxNull)).x87img
    rw [e3]
    have hksse : (if sse then
        ⟨(xsaveDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
        else ((xsaveHw (setXsaveTso v s1')).kerne c).fp) =
        ⟨(xsaveDekodiere (ctxFalte bs ctxNull)).mxcsr⟩ :=
      if_pos hs
    rw [hksse]
    show (xsaveDekodiere (ctxFalte bs ctxNull)).mxcsr = _
    have hk := xsaveKongr_mxcsr (ctxFalte bs ctxNull)
      (xsaveByte ((xsaveHw v).kerne c).fp ((xsaveHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c))
      sse avx hs (fun i hi => hagree i hi)
    rw [hk]
    exact (xsaveRundlauf_legacy ((xsaveHw v).kerne c).fp
      ((xsaveHw v).kerne c).xmm (v.x87 c) (v.maske c)
      (kopfStandard sse avx) (v.ym.ober c)).1
  · intro hs r
    have e4 := setXsaveKern_xmm (setXsaveTso v s1') c
      (if sse then
        ⟨(xsaveDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
       else ((xsaveHw (setXsaveTso v s1')).kerne c).fp)
      (if sse then (xsaveDekodiere (ctxFalte bs ctxNull)).xmm
       else ((xsaveHw (setXsaveTso v s1')).kerne c).xmm)
      (if avx then (xsaveDekodiere (ctxFalte bs ctxNull)).ymm
       else (setXsaveTso v s1').ym.ober c)
      (xsaveDekodiere (ctxFalte bs ctxNull)).x87img r
    rw [e4]
    have hxsse : (if sse then (xsaveDekodiere (ctxFalte bs ctxNull)).xmm
        else ((xsaveHw (setXsaveTso v s1')).kerne c).xmm) =
        (xsaveDekodiere (ctxFalte bs ctxNull)).xmm :=
      if_pos hs
    rw [hxsse]
    have hk := xsaveKongr_xmm (ctxFalte bs ctxNull)
      (xsaveByte ((xsaveHw v).kerne c).fp ((xsaveHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c))
      sse avx hs (fun i hi => hagree i hi) r
    rw [hk]
    exact (xsaveRundlauf_legacy ((xsaveHw v).kerne c).fp
      ((xsaveHw v).kerne c).xmm (v.x87 c) (v.maske c)
      (kopfStandard sse avx) (v.ym.ober c)).2 r
  · intro ha r
    have e5 := setXsaveKern_ober (setXsaveTso v s1') c
      (if sse then
        ⟨(xsaveDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
       else ((xsaveHw (setXsaveTso v s1')).kerne c).fp)
      (if sse then (xsaveDekodiere (ctxFalte bs ctxNull)).xmm
       else ((xsaveHw (setXsaveTso v s1')).kerne c).xmm)
      (if avx then (xsaveDekodiere (ctxFalte bs ctxNull)).ymm
       else (setXsaveTso v s1').ym.ober c)
      (xsaveDekodiere (ctxFalte bs ctxNull)).x87img r
    rw [e5]
    have hxavx : (if avx then (xsaveDekodiere (ctxFalte bs ctxNull)).ymm
        else (setXsaveTso v s1').ym.ober c) =
        (xsaveDekodiere (ctxFalte bs ctxNull)).ymm :=
      if_pos ha
    rw [hxavx]
    have hk := xsaveKongr_ymm (ctxFalte bs ctxNull)
      (xsaveByte ((xsaveHw v).kerne c).fp ((xsaveHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c))
      sse avx ha (fun i hi => hagree i hi) r
    rw [hk]
    exact xsaveRundlauf_ymm ((xsaveHw v).kerne c).fp
      ((xsaveHw v).kerne c).xmm (v.x87 c) (v.maske c)
      (kopfStandard sse avx) (v.ym.ober c) r

/-! ## 5. Fault gates: every class fires its outcome.

  Each gate below is one ordered row of the save/restore step:
  #NM first, then #UD (CPUID, LOCK, XCR0), then the empty-request
  refusal, then #GP (x87 bit, canonical, alignment), then
  #SS/#PF/#AC, then the permission refusal. Every premise is used
  by its `simp` (the gate it discharges). -/

/-- #NM has priority: a set TS bit faults, whatever else holds. -/
theorem xsaveSpeichern_fehlerNM (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h : f.nm = true) :
    xsaveSpeichern v c a xc sse avx f = .fehler .nm := by
  unfold xsaveSpeichern
  simp [h]

/-- #UD for a missing CPUID XSAVE bit. -/
theorem xsaveSpeichern_fehlerUD_ohne_cpuid (v : XsaveMaschine)
    (c : Nat) (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = false) :
    xsaveSpeichern v c a xc sse avx f = .fehler .ud := by
  unfold xsaveSpeichern
  simp [h1, h2]

/-- #UD for a LOCK prefix. -/
theorem xsaveSpeichern_fehlerUD_lock (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false) (h2 : f.lock = true) :
    xsaveSpeichern v c a xc sse avx f = .fehler .ud := by
  unfold xsaveSpeichern
  simp [h1, h2]

/-- #GP where the XCR0 x87 bit is clear. -/
theorem xsaveSpeichern_fehlerGP_ohne_x87 (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = false) :
    xsaveSpeichern v c a xc sse avx f = .fehler .gp := by
  unfold xsaveSpeichern
  simp [h1, h2, h3, h4]

/-- #UD where SSE is requested without XCR0 SSE readiness. -/
theorem xsaveSpeichern_fehlerUD_ohne_sse (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = false) :
    xsaveSpeichern v c a xc sse avx f = .fehler .ud := by
  unfold xsaveSpeichern
  simp [h1, h2, h3, h4, h5, h6]

/-- #UD where AVX is requested without XCR0 AVX readiness. -/
theorem xsaveSpeichern_fehlerUD_ohne_avx (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = false) (h6 : avx = true)
    (h7 : xcr0AvxBereit xc = false) :
    xsaveSpeichern v c a xc sse avx f = .fehler .ud := by
  unfold xsaveSpeichern
  simp [h1, h2, h3, h4, h5, h6, h7]

/-- An empty request is refused, never silently empty. -/
theorem xsaveSpeichern_verweigert_leer (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = false) (h6 : avx = false) :
    xsaveSpeichern v c a xc sse avx f = .verweigert := by
  unfold xsaveSpeichern
  simp [h1, h2, h3, h4, h5, h6]

/-- #GP on a non-canonical address. -/
theorem xsaveSpeichern_fehlerGP_nicht_xsaveKanonisch (v : XsaveMaschine)
    (c : Nat) (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : xsaveKanonisch a = false) :
    xsaveSpeichern v c a xc sse avx f = .fehler .gp := by
  unfold xsaveSpeichern
  simp [h1, h2, h3, h4, h5, h6, h7, h8]

/-- #GP on a misaligned area. -/
theorem xsaveSpeichern_fehlerGP_falsch_ausgerichtet (v : XsaveMaschine)
    (c : Nat) (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : xsaveKanonisch a = true) (h9 : xAusgerichtet a = false) :
    xsaveSpeichern v c a xc sse avx f = .fehler .gp := by
  unfold xsaveSpeichern
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- #SS fires ahead of the memory access. -/
theorem xsaveSpeichern_fehlerSS (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : xsaveKanonisch a = true) (h9 : xAusgerichtet a = true)
    (h10 : f.ss = true) :
    xsaveSpeichern v c a xc sse avx f = .fehler .ss := by
  unfold xsaveSpeichern
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-- #PF fires ahead of the memory access. -/
theorem xsaveSpeichern_fehlerPF (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : xsaveKanonisch a = true) (h9 : xAusgerichtet a = true)
    (h10 : f.ss = false) (h11 : f.pf = true) :
    xsaveSpeichern v c a xc sse avx f = .fehler .pf := by
  unfold xsaveSpeichern
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-- #AC fires last among the fault gates. -/
theorem xsaveSpeichern_fehlerAC (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : xsaveKanonisch a = true) (h9 : xAusgerichtet a = true)
    (h10 : f.ss = false) (h11 : f.pf = false)
    (h12 : f.ac = true) :
    xsaveSpeichern v c a xc sse avx f = .fehler .ac := by
  unfold xsaveSpeichern
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

/-- A missing write permission refuses the whole save. -/
theorem xsaveSpeichern_verweigert_ohne_schreibrecht (v : XsaveMaschine)
    (c : Nat) (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : xsaveKanonisch a = true) (h9 : xAusgerichtet a = true)
    (h10 : f.ss = false) (h11 : f.pf = false)
    (h12 : f.ac = false)
    (h13 : ctxAlle (xsaveHw v).mem.schreibbar a
      (xsaveOffsets sse avx) = false) :
    xsaveSpeichern v c a xc sse avx f = .verweigert := by
  rw [h5, h7] at h13
  unfold xsaveSpeichern
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

/-- #NM on the restore path. -/
theorem xsaveWiederherstellen_fehlerNM (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h : f.nm = true) :
    xsaveWiederherstellen v c a xc sse avx f = .fehler .nm := by
  unfold xsaveWiederherstellen
  simp [h]

/-- #UD on the restore path without XCR0 SSE readiness. -/
theorem xsaveWiederherstellen_fehlerUD_ohne_sse (v : XsaveMaschine)
    (c : Nat) (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = false) :
    xsaveWiederherstellen v c a xc sse avx f = .fehler .ud := by
  unfold xsaveWiederherstellen
  simp [h1, h2, h3, h4, h5, h6]

/-- #GP on the restore path for a misaligned area. -/
theorem xsaveWiederherstellen_fehlerGP_falsch_ausgerichtet
    (v : XsaveMaschine) (c : Nat) (a : Adresse) (xc : Xcr0Bild)
    (sse avx : Bool) (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : xsaveKanonisch a = true) (h9 : xAusgerichtet a = false) :
    xsaveWiederherstellen v c a xc sse avx f = .fehler .gp := by
  unfold xsaveWiederherstellen
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- #SS on the restore path. -/
theorem xsaveWiederherstellen_fehlerSS (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : xsaveKanonisch a = true) (h9 : xAusgerichtet a = true)
    (h10 : f.ss = true) :
    xsaveWiederherstellen v c a xc sse avx f = .fehler .ss := by
  unfold xsaveWiederherstellen
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-- An empty restore request is refused. -/
theorem xsaveWiederherstellen_verweigert_leer (v : XsaveMaschine)
    (c : Nat) (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = false) (h6 : avx = false) :
    xsaveWiederherstellen v c a xc sse avx f = .verweigert := by
  unfold xsaveWiederherstellen
  simp [h1, h2, h3, h4, h5, h6]

/-- A missing read permission refuses the whole restore. -/
theorem xsaveWiederherstellen_verweigert_ohne_leserecht
    (v : XsaveMaschine) (c : Nat) (a : Adresse) (xc : Xcr0Bild)
    (sse avx : Bool) (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : xsaveKanonisch a = true) (h9 : xAusgerichtet a = true)
    (h10 : f.ss = false) (h11 : f.pf = false)
    (h12 : f.ac = false)
    (h13 : ctxAlle (xsaveHw v).mem.lesbar a
      (xsaveOffsets sse avx) = false) :
    xsaveWiederherstellen v c a xc sse avx f = .verweigert := by
  rw [h5, h7] at h13
  unfold xsaveWiederherstellen
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

/-- A reserved MXCSR bit in the loaded image faults with #GP on
    restore (the accepted `ldmxcsrArchOk` refusal, lifted to the
    area restore). -/
theorem xsaveWiederherstellen_fehlerGP_reserviert (v : XsaveMaschine)
    (c : Nat) (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : xsaveKanonisch a = true) (h9 : xAusgerichtet a = true)
    (h10 : f.ss = false) (h11 : f.pf = false)
    (h12 : f.ac = false)
    (h13 : ctxAlle (xsaveHw v).mem.lesbar a
      (xsaveOffsets sse avx) = true)
    (bs : List (Nat × Byte))
    (h14 : ctxLadeAux (tsoAnsicht (xsaveHw v)) c a
      (xsaveOffsets sse avx) = some bs)
    (h15 : 65536 ≤ (mxcsrAusBytes
      (fun i => ctxFalte bs ctxNull (24 + i))).toNat) :
    xsaveWiederherstellen v c a xc sse avx f = .fehler .gp := by
  rw [h5, h7] at h13 h14
  unfold xsaveWiederherstellen
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  have hres : mxcsrReserviertFrei
      (mxcsrAusBytes (fun i => ctxFalte bs ctxNull (24 + i))) =
      false :=
    mxcsrReserviertFrei_verweigert _ h15
  simp [hres]

/-- AGREEMENT: the restore's reserved-bit #GP coincides with the
    accepted architectural load refusal `ldmxcsrArchOk`. -/
theorem xsaveRestore_stimmt_ldmxcsr_ueberein (p : MxcsrProfil)
    (w : MXCSR) (h : 65536 ≤ w.toNat) :
    ldmxcsrArchOk p w = false :=
  ldmxcsrArchOk_reserviert_verweigert p w h

/-! ## 6. FINIT: re-initialise the x87 image.

  `xsaveFinit` resets the acting core's opaque image to the reset
  constant. Everything else — control word, XMM/YMM files, masks,
  memory, buffers — is untouched, matching silicon FINIT, which
  affects only the x87 state (the FPU execution itself stays out
  of scope: only the stored image moves). -/

/-- FINIT: reset the acting core's opaque x87 image. -/
def xsaveFinit (v : XsaveMaschine) (c : Nat) : XsaveMaschine :=
  ⟨v.ym, fun d => if d = c then x87Reset else v.x87 d, v.maske⟩

/-- FINIT installs the reset image on the acting core. -/
theorem xsaveFinit_setzt_zurueck (v : XsaveMaschine) (c : Nat)
    (t : Nat) :
    ((xsaveFinit v c).x87 c) t = x87Reset t := by
  show ((if c = c then x87Reset else v.x87 c)) t = x87Reset t
  rw [if_pos rfl]

/-- FINIT keeps every other core's image. -/
theorem xsaveFinit_fremd (v : XsaveMaschine) (c d : Nat)
    (h : d ≠ c) (t : Nat) :
    ((xsaveFinit v c).x87 d) t = (v.x87 d) t := by
  show ((if d = c then x87Reset else v.x87 d)) t = (v.x87 d) t
  rw [if_neg h]

/-- FINIT preserves well-formedness (profiles untouched). -/
theorem xsaveFinit_wf (v : XsaveMaschine) (c : Nat)
    (hwf : XsaveWf v) : XsaveWf (xsaveFinit v c) :=
  hwf

/-- FINIT keeps the coherent machine (registers, memory,
    buffers all untouched). -/
theorem xsaveFinit_hw_still (v : XsaveMaschine) (c : Nat) :
    xsaveHw (xsaveFinit v c) = xsaveHw v := rfl

/-- FINIT keeps the masks. -/
theorem xsaveFinit_maske_still (v : XsaveMaschine) (c : Nat) :
    (xsaveFinit v c).maske = v.maske := rfl

/-- SAVE/RESTORE AFTER FINIT recovers the reset image: the
    identity theorem applied to the reinitialised state. -/
theorem xsaveFinit_rundlauf (v : XsaveMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : XsaveFehlerIn) (v1 v2 : XsaveMaschine)
    (hles : ctxAlle (xsaveHw (xsaveFinit v c)).mem.lesbar a
      (xsaveOffsets sse avx) = true)
    (h1 : xsaveSpeichern (xsaveFinit v c) c a xc sse avx f =
      .weiter v1)
    (h2 : xsaveWiederherstellen v1 c a xc sse avx f = .weiter v2) :
    ∀ t : Nat, t < 152 → (v2.x87 c) t = x87Reset t := by
  intro t ht
  have hr := (xsaveRundlauf_maschine (xsaveFinit v c) c a xc sse avx f
    v1 v2 hles h1 h2).1 t ht
  rw [hr]
  exact xsaveFinit_setzt_zurueck v c t

/-! ## 7. Family step relation and the TSO-leg embedding.

  The x87 image, mask and YMM upper file live beside `HwMaschine`
  (in `XsaveMaschine`, like the accepted `YmmMaschine` wrapper),
  so no `HwAdapter HwMaschine` plug can carry a save without
  inventing that state. Instead `XsaveSchritt` runs on the full
  machine: the checked save/restore/FINIT steps, the shared TSO
  legs with the EXACT coherent embedding, and outcome-tied
  refusals (never silent). -/

/-- Observable family events on the full machine. -/
inductive XsaveEreignis where
  | saveReq : Nat → Adresse → Xcr0Bild → Bool → Bool → XsaveEreignis
  | rstorReq : Nat → Adresse → Xcr0Bild → Bool → Bool → XsaveEreignis
  | finitReq : Nat → XsaveEreignis
  | leseBeob : Nat → Adresse → Byte → XsaveEreignis
  | schreibAusgabe : Nat → Adresse → Byte → XsaveEreignis
  | spülung : Nat → TSOEintrag → XsaveEreignis
  | verweigert : Nat → XsaveEreignis

/-- Project an outcome to a step successor. -/
def xsaveOpt (o : XsaveAusgang) : Option XsaveMaschine :=
  match o with
  | .weiter v' => some v'
  | _ => none

/-- Family step relation: checked requests plus the shared TSO
    legs plus outcome-tied refusals. The fault-input oracle `f`
    rides in the request (checked inputs, never assumed). -/
inductive XsaveSchritt : XsaveMaschine → XsaveMaschine → XsaveEreignis → Prop where
  | save {v v' : XsaveMaschine} (c : Nat) (a : Adresse)
      (xc : Xcr0Bild) (sse avx : Bool) (f : XsaveFehlerIn)
      (h : xsaveSpeichern v c a xc sse avx f = .weiter v') :
      XsaveSchritt v v' (.saveReq c a xc sse avx)
  | rstor {v v' : XsaveMaschine} (c : Nat) (a : Adresse)
      (xc : Xcr0Bild) (sse avx : Bool) (f : XsaveFehlerIn)
      (h : xsaveWiederherstellen v c a xc sse avx f = .weiter v') :
      XsaveSchritt v v' (.rstorReq c a xc sse avx)
  | finit {v : XsaveMaschine} (c : Nat) :
      XsaveSchritt v (xsaveFinit v c) (.finitReq c)
  | lade {v : XsaveMaschine} (c : Nat) (a : Adresse) (w : Byte)
      (h : loadByte (tsoAnsicht (xsaveHw v)) c a = some w) :
      XsaveSchritt v v (.leseBeob c a w)
  | gibAus {v : XsaveMaschine} (c : Nat) (a : Adresse) (w : Byte)
      (s' : TSOZustand)
      (h : issueByte (tsoAnsicht (xsaveHw v)) c a w = some s') :
      XsaveSchritt v (setXsaveTso v s') (.schreibAusgabe c a w)
  | spüle {v : XsaveMaschine} (c : Nat) (e : TSOEintrag)
      (s' : TSOZustand)
      (h : flushKern (tsoAnsicht (xsaveHw v)) c = some s')
      (hkopf : ((xsaveHw v).puffer c).head? = some e) :
      XsaveSchritt v (setXsaveTso v s') (.spülung c e)
  | fehlerSave {v : XsaveMaschine} (c : Nat) (a : Adresse)
      (xc : Xcr0Bild) (sse avx : Bool) (f : XsaveFehlerIn)
      (g : ArchFehler)
      (h : xsaveSpeichern v c a xc sse avx f = .fehler g) :
      XsaveSchritt v v (.verweigert c)
  | fehlerRstor {v : XsaveMaschine} (c : Nat) (a : Adresse)
      (xc : Xcr0Bild) (sse avx : Bool) (f : XsaveFehlerIn)
      (g : ArchFehler)
      (h : xsaveWiederherstellen v c a xc sse avx f = .fehler g) :
      XsaveSchritt v v (.verweigert c)
  | fehlerVerweigert {v : XsaveMaschine} (c : Nat) (a : Adresse)
      (xc : Xcr0Bild) (sse avx : Bool) (f : XsaveFehlerIn)
      (h : xsaveSpeichern v c a xc sse avx f = .verweigert) :
      XsaveSchritt v v (.verweigert c)

/-- (1) Every family step preserves well-formedness. -/
theorem xsaveSchritt_wf (v v' : XsaveMaschine) (e : XsaveEreignis)
    (h : XsaveSchritt v v' e) (hwf : XsaveWf v) : XsaveWf v' := by
  cases h with
  | save c a xc sse avx f h =>
    exact xsaveSpeichern_wf _ _ _ _ _ _ _ hwf _ h
  | rstor c a xc sse avx f h =>
    exact xsaveWiederherstellen_wf _ _ _ _ _ _ _ hwf _ h
  | finit c => exact xsaveFinit_wf _ _ hwf
  | lade c a w h => exact hwf
  | gibAus c a w s' h => exact setXsaveTso_wf _ _ hwf
  | spüle c e s' h hkopf => exact setXsaveTso_wf _ _ hwf
  | fehlerSave c a xc sse avx f g h => exact hwf
  | fehlerRstor c a xc sse avx f g h => exact hwf
  | fehlerVerweigert c a xc sse avx f h => exact hwf

/-- (2) The TSO observation leg IS the coherent TSO step. -/
theorem xsaveLade_ist_hw (v v' : XsaveMaschine) (c : Nat)
    (a : Adresse) (w : Byte)
    (h : XsaveSchritt v v' (.leseBeob c a w)) :
    HwSchritt (xsaveHw v) (xsaveHw v') (.leseBeob c a w) := by
  cases h with
  | lade c a w h => exact HwSchritt.lade c a w h

/-- (2) The TSO store-issue leg IS the coherent TSO step. -/
theorem xsaveGibAus_ist_hw (v v' : XsaveMaschine) (c : Nat)
    (a : Adresse) (w : Byte)
    (h : XsaveSchritt v v' (.schreibAusgabe c a w)) :
    ∃ s' : TSOZustand,
      issueByte (tsoAnsicht (xsaveHw v)) c a w = some s' ∧
      HwSchritt (xsaveHw v) (xsaveHw v') (.schreibAusgabe c a w) := by
  cases h with
  | gibAus c a w t ht =>
    exact ⟨t, ht, HwSchritt.gibAus c a w t ht⟩

/-- (2) The TSO drain leg IS the coherent TSO step. -/
theorem xsaveSpüle_ist_hw (v v' : XsaveMaschine) (c : Nat)
    (e : TSOEintrag)
    (h : XsaveSchritt v v' (.spülung c e)) :
    ∃ s' : TSOZustand,
      flushKern (tsoAnsicht (xsaveHw v)) c = some s' ∧
      HwSchritt (xsaveHw v) (xsaveHw v') (.spülung c e) := by
  cases h with
  | spüle c e t ht hkopf =>
    exact ⟨t, ht, HwSchritt.spüle c e t ht hkopf⟩

/-- BACKWARD embedding, exact: a drain step comes only from the
    coherent drain with the same head condition. -/
theorem xsaveSpüle_ist_hw_zurueck (v v' : XsaveMaschine) (c : Nat)
    (e : TSOEintrag)
    (h : XsaveSchritt v v' (.spülung c e)) :
    ∃ s' : TSOZustand,
      flushKern (tsoAnsicht (xsaveHw v)) c = some s' ∧
      ((xsaveHw v).puffer c).head? = some e ∧
      v' = setXsaveTso v s' := by
  cases h with
  | spüle c e s' h hkopf => exact ⟨s', h, hkopf, rfl⟩

/-! ## 8. Joint witness: two cores save, forward, drain; refusals;
    FINIT; the save/restore identity observed.

  Core 0 saves at `0x1000`, core 1 at `0x2000` (both 64-aligned
  and canonical). Memory starts zeroed; permissions cover exactly
  the two full areas (736 footprint entries spanning 832 bytes
  with SSE and AVX).
  Core 0 carries MXCSR `0x1F80`, XMM low halves `7`, the FINIT
  reset x87 image, mask `0xFFBF` and YMM upper low-halves `9`;
  core 1 carries `0x1FBF`, low halves `11`, the constant-`5` x87
  image and upper low-halves `13`. -/

/-- A folded issue leaves every other core's buffer alone. -/
theorem issueListe_anderer_kern (s s' : TSOZustand) (c : Nat)
    (l : List TSOEintrag) (d : Nat) (hne : d ≠ c)
    (h : issueListe s c l = some s') :
    s'.puffer d = s.puffer d := by
  induction l generalizing s s' with
  | nil =>
    simp only [issueListe] at h
    have e : s = s' := Option.some_inj.mp h
    rw [e]
  | cons e rest ih =>
    unfold issueListe at h
    cases h1 : issueByte s c e.addr e.wert with
    | none =>
      rw [h1] at h
      cases h
    | some s1 =>
      rw [h1] at h
      have hd : s1.puffer d = s.puffer d :=
        issue_anderer_kern s s1 c e.addr e.wert h1 hne
      rw [ih s1 s' h, hd]

/-- Save entries grow one per footprint offset. -/
theorem fxEintraegeAux_laenge (f : Nat → Byte) (a : Adresse)
    (os : List Nat) :
    (fxEintraegeAux f a os).length = os.length := by
  induction os with
  | nil => rfl
  | cons i rest ih =>
    simp only [fxEintraegeAux, List.length_cons, ih]

/-- Witness area base, core 0 (64-aligned, canonical). -/
def xsaveWitArea0 : Adresse := BitVec.ofNat 64 4096

/-- Witness area base, core 1. -/
def xsaveWitArea1 : Adresse := BitVec.ofNat 64 8192

/-- Witness area base, reserved-bit probe. -/
def xsaveWitAreaR : Adresse := BitVec.ofNat 64 12288

/-- Witness permission: exactly the two full 832-byte areas
    plus the reserved-bit probe area. -/
def xsaveWitOk (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + 832) ||
    decide (8192 ≤ a.toNat ∧ a.toNat < 8192 + 832) ||
    decide (12288 ≤ a.toNat ∧ a.toNat < 12288 + 832)

/-- Witness memory: zeroed bytes, footprint permissions. -/
def xsaveWitMem : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0, lesbar := xsaveWitOk,
    schreibbar := xsaveWitOk, ausfuehrbar := fun _ => false }

/-- Witness XMM file, core 0 (low halves 7). -/
def xsaveWitX0 : XmmDatei :=
  fun _ => vecJoin (BitVec.ofNat 64 7) (BitVec.ofNat 64 0)

/-- Witness XMM file, core 1 (low halves 11). -/
def xsaveWitX1 : XmmDatei :=
  fun _ => vecJoin (BitVec.ofNat 64 11) (BitVec.ofNat 64 0)

/-- Witness cores: distinct FP state per core. -/
def xsaveWitKern : Nat → HwKern
  | 0 => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0, xsaveWitX0, ⟨0x1F80⟩⟩
  | 1 => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0, xsaveWitX1, ⟨0x1FBF⟩⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness x87 images: core 0 starts from the FINIT reset image,
    every other core carries the constant-`5` image (nonzero, so
    forwarding is observable against zeroed memory). -/
def xsaveWitX87 : Nat → X87Bild
  | 0 => x87Reset
  | _ => fun _ => BitVec.ofNat 8 5

/-- Witness masks: the `0xFFBF` constant everywhere. -/
def xsaveWitMaske : Nat → BitVec 32 :=
  fun _ => BitVec.ofNat 32 0xFFBF

/-- Witness upper files: low halves `9` on core 0, `13` elsewhere. -/
def xsaveWitOber : Nat → YmmDatei
  | 0 => fun _ => vecJoin (BitVec.ofNat 64 9) (BitVec.ofNat 64 0)
  | _ => fun _ => vecJoin (BitVec.ofNat 64 13) (BitVec.ofNat 64 0)

/-- Witness start machine: shared memory, two saving cores, empty
    buffers, full silicon, baseline readiness. -/
def xsaveWitStart : XsaveMaschine :=
  ⟨⟨⟨xsaveWitMem, xsaveWitKern, fun _ => [], basisHw,
    fun _ => basisBereit⟩, xsaveWitOber⟩, xsaveWitX87, xsaveWitMaske⟩

/-- Witness XCR0: x87, SSE and AVX enabled. -/
def xsaveWitXc : Xcr0Bild := ⟨true, true, true⟩

/-- Witness fault inputs: no fault fires. -/
def xsaveWitF : XsaveFehlerIn :=
  ⟨false, true, false, false, false, false⟩

/-- The witness machine is well-formed. -/
theorem xsaveWitStart_wf : XsaveWf xsaveWitStart := by
  unfold XsaveWf
  intro c f _
  cases f <;> rfl

set_option maxRecDepth 10000 in
/-- Witness permissions cover the full footprint, both ways. -/
theorem xsaveWit_perm (a : Adresse)
    (h : a = xsaveWitArea0 ∨ a = xsaveWitArea1) :
    ctxAlle xsaveWitMem.schreibbar a (xsaveOffsets true true) = true ∧
      ctxAlle xsaveWitMem.lesbar a (xsaveOffsets true true) = true := by
  rcases h with rfl | rfl <;> decide

/-- Witness addresses are canonical. -/
theorem xsaveWit_xsaveKanonisch :
    xsaveKanonisch xsaveWitArea0 = true ∧
      xsaveKanonisch xsaveWitArea1 = true := by
  decide

/-- Witness addresses are save-aligned. -/
theorem xsaveWit_ausgerichtet :
    xAusgerichtet xsaveWitArea0 = true ∧
      xAusgerichtet xsaveWitArea1 = true ∧
      fxAusgerichtet xsaveWitArea0 = true := by
  decide

/-- Witness XCR0 enables SSE and AVX. -/
theorem xsaveWit_bereit :
    xcr0SseBereit xsaveWitXc = true ∧
      xcr0AvxBereit xsaveWitXc = true := by
  decide

/-- FINIT facts on the witness: reset installs, everything else
    stays, and core 0 already starts from reset. -/
theorem xsaveWit_finit :
    ((xsaveFinit xsaveWitStart 1).x87 1) 0 = x87Reset 0 ∧
      xsaveHw (xsaveFinit xsaveWitStart 1) = xsaveHw xsaveWitStart ∧
      (xsaveFinit xsaveWitStart 1).maske = xsaveWitStart.maske ∧
      (xsaveWitX87 0) 0 = x87Reset 0 := by
  exact ⟨xsaveFinit_setzt_zurueck _ _ _,
    xsaveFinit_hw_still _ _, xsaveFinit_maske_still _ _, rfl⟩

/-! ## 9. Observed saves: buffers, forwarding, foreign view.

  Outcomes carry machines (functions inside), so everything
  observed goes through first-order projections (`Option Nat`,
  `Option (Option Byte)`), exactly like the accepted lane-1247
  witness. Each `decide` below evaluates its save once; the
  kernel re-checks nothing across theorems. -/

/-- Project a buffer length out of a save outcome. -/
def witBuf (o : XsaveAusgang) (c : Nat) : Option Nat :=
  match o with
  | .weiter m => some ((xsaveHw m).puffer c).length
  | _ => none

/-- Project one TSO-view byte out of a save outcome. -/
def witByte (o : XsaveAusgang) (c : Nat)
    (a : Adresse) : Option (Option Byte) :=
  match o with
  | .weiter m => some (loadByte (tsoAnsicht (xsaveHw m)) c a)
  | _ => none

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Both cores buffer exactly their footprint entries: 476 with
    AVX alone (x87, mask, header, YMM), 480 with SSE alone
    (x87, mask, legacy, header). The 736-entry joint save is
    never evaluated in the kernel: it exceeds the kernel memory
    budget, so the two components are observed separately. -/
theorem wit_buf :
    witBuf (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc
      false true xsaveWitF) 0 = some 476 ∧
      witBuf (xsaveSpeichern xsaveWitStart 1 xsaveWitArea1 xsaveWitXc
        true false xsaveWitF) 1 = some 480 := by
  decide

/-- An empty request buffers nothing (refusal, observed). -/
theorem wit_empty :
    witBuf (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc
      false false xsaveWitF) 0 = none := by
  decide

/-- The machine after core 0 saves AVX, if reached. -/
def witV1 : XsaveMaschine :=
  match xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc false
      true xsaveWitF with
  | .weiter m => m
  | _ => xsaveWitStart

/-- The machine after core 1 saves SSE, if reached. -/
def witV1b : XsaveMaschine :=
  match xsaveSpeichern xsaveWitStart 1 xsaveWitArea1 xsaveWitXc true
      false xsaveWitF with
  | .weiter m => m
  | _ => xsaveWitStart

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Owner-only forwarding, core 0: mask `0xBF` and header
    `5` (XSTATE_BV bits 0 and 2 for the AVX-only request). -/
theorem wit_fwd0 :
    witByte (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc
        false true xsaveWitF) 0 (addrOff xsaveWitArea0 28) =
        some (some (BitVec.ofNat 8 191)) ∧
      witByte (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc
          false true xsaveWitF) 0 (addrOff xsaveWitArea0 512) =
          some (some (BitVec.ofNat 8 5)) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Owner-only forwarding, core 0 YMM and core 1 x87/MXCSR. -/
theorem wit_fwd1 :
    witByte (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc
        false true xsaveWitF) 0 (addrOff xsaveWitArea0 576) =
        some (some (BitVec.ofNat 8 9)) ∧
      witByte (xsaveSpeichern xsaveWitStart 1 xsaveWitArea1 xsaveWitXc
          true false xsaveWitF) 1 (addrOff xsaveWitArea1 0) =
          some (some (BitVec.ofNat 8 5)) ∧
      witByte (xsaveSpeichern xsaveWitStart 1 xsaveWitArea1 xsaveWitXc
          true false xsaveWitF) 1 (addrOff xsaveWitArea1 24) =
          some (some (BitVec.ofNat 8 191)) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- No foreign forwarding: core 0 still reads zero at core 1's
    MXCSR cell after core 1 saves. -/
theorem wit_fremd :
    witByte (xsaveSpeichern xsaveWitStart 1 xsaveWitArea1 xsaveWitXc
        true false xsaveWitF) 0 (addrOff xsaveWitArea1 24) =
        some (some (BitVec.ofNat 8 0)) := by
  decide

/-! ## 10. Observed restore, drain, reserved bit and refusals. -/

/-- Project the restored control word out of a restore outcome. -/
def witFpNach (o : XsaveAusgang) (c : Nat) : Option Nat :=
  match o with
  | .weiter m => some ((((xsaveHw m).kerne c).fp).mxcsr.toNat)
  | _ => none

/-- Project a restored XMM register out of a restore outcome. -/
def witXmmNach (o : XsaveAusgang) (c : Nat) (r : XmmReg) :
    Option Nat :=
  match o with
  | .weiter m => some ((((xsaveHw m).kerne c).xmm r).toNat)
  | _ => none

/-- Project a restored YMM upper half out of a restore outcome. -/
def witYmmNach (o : XsaveAusgang) (c : Nat) (r : XmmReg) :
    Option Nat :=
  match o with
  | .weiter m => some (((m.ym.ober c) r).toNat)
  | _ => none

/-- Project a restored opaque byte out of a restore outcome. -/
def witX87Nach (o : XsaveAusgang) (c t : Nat) : Option Byte :=
  match o with
  | .weiter m => some ((m.x87 c) t)
  | _ => none

/-- Outcome kind projection (outcomes carry functions, so no
    `DecidableEq`; kinds are plain numbers). -/
def xsaveWitArt (o : XsaveAusgang) : Nat :=
  match o with
  | .weiter _ => 0
  | .verweigert => 1
  | .fehler _ => 2

/-- Fault class projection: 10 NM, 11 UD, 12 GP, 13 SS, 14 PF,
    15 AC, 16 DE, 17 XM, 0 no fault. -/
def xsaveWitFehler (o : XsaveAusgang) : Nat :=
  match o with
  | .fehler .nm => 10
  | .fehler .ud => 11
  | .fehler .gp => 12
  | .fehler .ss => 13
  | .fehler .pf => 14
  | .fehler .ac => 15
  | .fehler .de => 16
  | .fehler .xm => 17
  | _ => 0

/-- Core 0 restores AVX after its save, if reached. -/
def witV2 : XsaveAusgang :=
  match xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc false
      true xsaveWitF with
  | .weiter m1 =>
    xsaveWiederherstellen m1 0 xsaveWitArea0 xsaveWitXc false true
      xsaveWitF
  | _ => .verweigert

/-- Core 1 restores SSE after its save, if reached. -/
def witV2b : XsaveAusgang :=
  match xsaveSpeichern xsaveWitStart 1 xsaveWitArea1 xsaveWitXc true
      false xsaveWitF with
  | .weiter m1 =>
    xsaveWiederherstellen m1 1 xsaveWitArea1 xsaveWitXc true false
      xsaveWitF
  | _ => .verweigert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- MACHINE ROUND TRIP, observed on AVX: the YMM upper half
    comes back `9` and the opaque byte comes back `0`, the FINIT
    reset value core 0 started from. -/
theorem wit_restore0 :
    witYmmNach witV2 0 .xmm0 = some 9 ∧
      witX87Nach witV2 0 0 = some (BitVec.ofNat 8 0) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- MACHINE ROUND TRIP, observed on SSE: the control word comes
    back `0x1FBF` and XMM0 comes back whole (`11` in the low
    word, zero above). -/
theorem wit_restore1 :
    witFpNach witV2b 1 = some 0x1FBF ∧
      witXmmNach witV2b 1 .xmm0 = some 11 := by
  decide

/-- Core 1 drains its oldest entry into shared memory. -/
def witNachFlush : Option Byte :=
  match xsaveSpeichern xsaveWitStart 1 xsaveWitArea1 xsaveWitXc true
      false xsaveWitF with
  | .weiter m =>
    match flushKern (tsoAnsicht (xsaveHw m)) 1 with
    | some s => some (s.mem.bytes (addrOff xsaveWitArea1 0))
    | none => none
  | _ => none

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- THE DRAIN CHANGES MEMORY: the cell starts zeroed and reads
    `5` (core 1's x87 byte) after one flush. -/
theorem wit_drain :
    witNachFlush = some (BitVec.ofNat 8 5) ∧
      xsaveWitMem.bytes (addrOff xsaveWitArea1 0) =
        BitVec.ofNat 8 0 := by
  decide

/-- Reserved-bit probe bytes: bit 18 set in the MXCSR image cell. -/
def xsaveWitMemRBytes (a : Adresse) : Byte :=
  if decide (a = addrOff xsaveWitAreaR 26) then BitVec.ofNat 8 4
  else BitVec.ofNat 8 0

/-- Reserved-bit probe memory. -/
def xsaveWitMemR : Speicher :=
  { bytes := xsaveWitMemRBytes, lesbar := xsaveWitOk,
    schreibbar := xsaveWitOk, ausfuehrbar := fun _ => false }

/-- Reserved-bit probe machine. -/
def xsaveWitStartR : XsaveMaschine :=
  { xsaveWitStart with ym :=
    ⟨{ xsaveWitStart.ym.hw with mem := xsaveWitMemR },
      xsaveWitStart.ym.ober⟩ }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- A reserved MXCSR image bit faults with #GP on restore. -/
theorem wit_gp_reserviert :
    xsaveWitFehler (xsaveWiederherstellen xsaveWitStartR 0 xsaveWitAreaR
      xsaveWitXc true false xsaveWitF) = 12 := by
  decide

set_option maxRecDepth 100000 in
/-- Planted refusals, observed: every fault class fires its
    outcome, the empty request and the permission failure refuse. -/
theorem wit_verweigert :
    xsaveWitFehler (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc
        true true ⟨true, true, false, false, false, false⟩) = 10 ∧
      xsaveWitFehler (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc
        true true ⟨false, false, false, false, false, false⟩) = 11 ∧
      xsaveWitFehler (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc
        true true ⟨false, true, true, false, false, false⟩) = 11 ∧
      xsaveWitFehler (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0
        ⟨true, false, false⟩ true true xsaveWitF) = 11 ∧
      xsaveWitFehler (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0
        ⟨true, true, false⟩ false true xsaveWitF) = 11 ∧
      xsaveWitFehler (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0
        ⟨false, true, true⟩ true true xsaveWitF) = 12 ∧
      xsaveWitArt (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc
        false false xsaveWitF) = 1 ∧
      xsaveWitFehler (xsaveSpeichern xsaveWitStart 0
        (BitVec.ofNat 64 (2 ^ 47)) xsaveWitXc true true
        xsaveWitF) = 12 ∧
      xsaveWitFehler (xsaveSpeichern xsaveWitStart 0
        (BitVec.ofNat 64 4104) xsaveWitXc true true xsaveWitF) = 12 ∧
      xsaveWitFehler (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc
        true true ⟨false, true, false, true, false, false⟩) = 13 ∧
      xsaveWitFehler (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc
        true true ⟨false, true, false, false, true, false⟩) = 14 ∧
      xsaveWitFehler (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc
        true true ⟨false, true, false, false, false, true⟩) = 15 ∧
      xsaveWitArt (xsaveSpeichern xsaveWitStart 0 (BitVec.ofNat 64 0)
        xsaveWitXc true true xsaveWitF) = 1 := by
  decide

/-! ## 11. Witness steps: FINIT, single TSO steps, refusals.

  Save/restore/refusal STEPS need outcome equalities
  (`save = .weiter v'`), which have no `DecidableEq` and are
  only attempted by `rfl` below. FINIT and single-TSO steps are
  definitional or single-issue and cost nothing. -/

/-- The witness TSO view. -/
def witTso0 : TSOZustand := tsoAnsicht (xsaveHw xsaveWitStart)

/-- Single-issue successor: one byte at the core-1 area. -/
def witS1 : TSOZustand :=
  ⟨xsaveWitMem, pufferSetze (fun _ => []) 0
    ((fun _ => []) 0 ++
      [⟨xsaveWitArea1, BitVec.ofNat 8 42⟩])⟩

/-- The single issue goes through (one permission check, one
    append: no footprint fold). -/
theorem wit_issue1 :
    issueByte witTso0 0 xsaveWitArea1 (BitVec.ofNat 8 42) =
      some witS1 := by
  rfl

/-- Single-issue step on the full machine. -/
theorem wit_schritt_gibAus :
    XsaveSchritt xsaveWitStart (setXsaveTso xsaveWitStart witS1)
      (.schreibAusgabe 0 xsaveWitArea1
        (BitVec.ofNat 8 42)) :=
  XsaveSchritt.gibAus 0 xsaveWitArea1 (BitVec.ofNat 8 42) witS1
    wit_issue1

/-- The issued byte forwards to its owner. -/
theorem wit_schritt_lade_wert :
    loadByte witS1 0 xsaveWitArea1 = some (BitVec.ofNat 8 42) := by
  decide

/-- Observation step on the full machine. -/
theorem wit_schritt_lade :
    XsaveSchritt (setXsaveTso xsaveWitStart witS1)
      (setXsaveTso xsaveWitStart witS1)
      (.leseBeob 0 xsaveWitArea1 (BitVec.ofNat 8 42)) :=
  XsaveSchritt.lade 0 xsaveWitArea1 (BitVec.ofNat 8 42)
    wit_schritt_lade_wert

/-- Single-flush successor: the byte lands in memory. -/
def witS2 : TSOZustand :=
  ⟨{ xsaveWitMem with bytes :=
      fun x => if x = xsaveWitArea1 then BitVec.ofNat 8 42
        else xsaveWitMem.bytes x },
    pufferSetze witS1.puffer 0 []⟩

/-- The single flush goes through. -/
theorem wit_flush1 :
    flushKern witS1 0 = some witS2 := by
  rfl

/-- Drain step on the full machine. -/
theorem wit_schritt_spüle :
    XsaveSchritt (setXsaveTso xsaveWitStart witS1)
      (setXsaveTso xsaveWitStart witS2)
      (.spülung 0 ⟨xsaveWitArea1, BitVec.ofNat 8 42⟩) :=
  XsaveSchritt.spüle 0 ⟨xsaveWitArea1, BitVec.ofNat 8 42⟩ witS2
    wit_flush1 (by rfl)

/-- FINIT steps on both cores (definitional). -/
theorem wit_schritt_finit :
    XsaveSchritt xsaveWitStart (xsaveFinit xsaveWitStart 0)
      (.finitReq 0) ∧
      XsaveSchritt xsaveWitStart (xsaveFinit xsaveWitStart 1)
        (.finitReq 1) :=
  ⟨XsaveSchritt.finit 0, XsaveSchritt.finit 1⟩

/-- The NM refusal as an outcome equality (gates only: cheap). -/
theorem wit_nm_gleich :
    xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc true true
      ⟨true, true, false, false, false, false⟩ =
      .fehler .nm := by
  rfl

/-- NM refusal step. -/
theorem wit_schritt_nm :
    XsaveSchritt xsaveWitStart xsaveWitStart (.verweigert 0) :=
  XsaveSchritt.fehlerSave 0 xsaveWitArea0 xsaveWitXc true true
    ⟨true, true, false, false, false, false⟩ .nm wit_nm_gleich

/-- The empty-request refusal as an outcome equality. -/
theorem wit_leer_gleich :
    xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc false
      false xsaveWitF = .verweigert := by
  rfl

/-- Empty-request refusal step. -/
theorem wit_schritt_leer :
    XsaveSchritt xsaveWitStart xsaveWitStart (.verweigert 0) :=
  XsaveSchritt.fehlerVerweigert 0 xsaveWitArea0 xsaveWitXc false false
    xsaveWitF wit_leer_gleich

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Core-1 save as an outcome equality (480-entry kernel
    evaluation through `rfl`). -/
theorem wit_h1b :
    xsaveSpeichern xsaveWitStart 1 xsaveWitArea1 xsaveWitXc true false
      xsaveWitF = .weiter witV1b := by
  rfl

/-! ## 12. Applied identity and the joint witness.

  With the outcome equalities available as `rfl` facts, the
  generic save/restore identity applies to the reached witness
  states directly, and the save/restore family steps stand
  beside the observed values. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Core-0 save as an outcome equality. -/
theorem wit_h1 :
    xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc false true
      xsaveWitF = .weiter witV1 := by
  rfl

/-- Core-0 restore target: the machine after restoring core 0. -/
def witM2 : XsaveMaschine :=
  match xsaveWiederherstellen witV1 0 xsaveWitArea0 xsaveWitXc false
      true xsaveWitF with
  | .weiter m => m
  | _ => xsaveWitStart

/-- Core-1 restore target: the machine after restoring core 1. -/
def witM2b : XsaveMaschine :=
  match xsaveWiederherstellen witV1b 1 xsaveWitArea1 xsaveWitXc true
      false xsaveWitF with
  | .weiter m => m
  | _ => xsaveWitStart

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Core-0 restore as an outcome equality. -/
theorem wit_h2 :
    xsaveWiederherstellen witV1 0 xsaveWitArea0 xsaveWitXc false true
      xsaveWitF = .weiter witM2 := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Core-1 restore as an outcome equality. -/
theorem wit_h2b :
    xsaveWiederherstellen witV1b 1 xsaveWitArea1 xsaveWitXc true false
      xsaveWitF = .weiter witM2b := by
  rfl

set_option maxRecDepth 100000 in
/-- APPLIED IDENTITY on SSE: the generic round trip recovers
    core 1's opaque image, control word and XMM file. -/
theorem wit_rundlauf_anwendung1 :
    (∀ t : Nat, t < 152 → (witM2b.x87 1) t =
      (xsaveWitStart.x87 1) t) ∧
      witM2b.maske 1 = xsaveWitStart.maske 1 ∧
      (((xsaveHw witM2b).kerne 1).fp).mxcsr =
        (((xsaveHw xsaveWitStart).kerne 1).fp).mxcsr ∧
      (∀ r : XmmReg, ((xsaveHw witM2b).kerne 1).xmm r =
        ((xsaveHw xsaveWitStart).kerne 1).xmm r) := by
  have hles : ctxAlle (xsaveHw xsaveWitStart).mem.lesbar xsaveWitArea1
      (xsaveOffsets true false) = true :=
    (xsaveWit_perm _ (Or.inr rfl)).2
  have hrr := xsaveRundlauf_maschine xsaveWitStart 1 xsaveWitArea1
    xsaveWitXc true false xsaveWitF witV1b witM2b hles wit_h1b wit_h2b
  exact ⟨hrr.1, hrr.2.1, hrr.2.2.1 rfl, hrr.2.2.2.1 rfl⟩

set_option maxRecDepth 100000 in
/-- APPLIED IDENTITY on AVX: the generic round trip recovers
    core 0's opaque image and YMM upper file. -/
theorem wit_rundlauf_anwendung0 :
    (∀ t : Nat, t < 152 → (witM2.x87 0) t =
      (xsaveWitStart.x87 0) t) ∧
      (∀ r : XmmReg, (witM2.ym.ober 0) r =
        (xsaveWitStart.ym.ober 0) r) := by
  have hles : ctxAlle (xsaveHw xsaveWitStart).mem.lesbar xsaveWitArea0
      (xsaveOffsets false true) = true :=
    (xsaveWit_perm _ (Or.inl rfl)).2
  have hrr := xsaveRundlauf_maschine xsaveWitStart 0 xsaveWitArea0
    xsaveWitXc false true xsaveWitF witV1 witM2 hles wit_h1 wit_h2
  exact ⟨hrr.1, fun r => hrr.2.2.2.2 rfl r⟩

/-- Save step on core 1 (reached). -/
theorem wit_schritt_save1 :
    XsaveSchritt xsaveWitStart witV1b
      (.saveReq 1 xsaveWitArea1 xsaveWitXc true false) :=
  XsaveSchritt.save 1 xsaveWitArea1 xsaveWitXc true false xsaveWitF
    wit_h1b

/-- Restore step on core 1 (reached). -/
theorem wit_schritt_rstor1 :
    XsaveSchritt witV1b witM2b
      (.rstorReq 1 xsaveWitArea1 xsaveWitXc true false) :=
  XsaveSchritt.rstor 1 xsaveWitArea1 xsaveWitXc true false xsaveWitF
    wit_h2b

/-- Save step on core 0 (reached). -/
theorem wit_schritt_save0 :
    XsaveSchritt xsaveWitStart witV1
      (.saveReq 0 xsaveWitArea0 xsaveWitXc false true) :=
  XsaveSchritt.save 0 xsaveWitArea0 xsaveWitXc false true xsaveWitF
    wit_h1

/-- Restore step on core 0 (reached). -/
theorem wit_schritt_rstor0 :
    XsaveSchritt witV1 witM2
      (.rstorReq 0 xsaveWitArea0 xsaveWitXc false true) :=
  XsaveSchritt.rstor 0 xsaveWitArea0 xsaveWitXc false true xsaveWitF
    wit_h2

/-- JOINT WITNESS for `xsaveRundlauf_maschine`: all premises
    instantiated jointly on a reached, non-degenerate two-core
    run. Two cores buffer full save images (476 AVX-only and 480
    SSE-only entries); each owner forwards its bytes while the
    other core reads zeros; one drain observably changes shared
    memory (0 becomes `5`); both save/restore round trips recover
    the enabled components through the machine (control word,
    XMM, opaque x87 image, YMM); every fault class fires its
    outcome and the empty/permission shapes refuse; FINIT
    installs reset and keeps everything else; the start machine
    is well-formed. Non-degenerate: two cores touch memory, a
    buffered store is visible by forwarding to its owner only,
    and a drain changes actual shared memory. -/
theorem xsaveRundlauf_maschine_zeuge :
    witBuf (xsaveSpeichern xsaveWitStart 0 xsaveWitArea0 xsaveWitXc
      false true xsaveWitF) 0 = some 476 ∧
      witBuf (xsaveSpeichern xsaveWitStart 1 xsaveWitArea1 xsaveWitXc
        true false xsaveWitF) 1 = some 480 ∧
      witYmmNach witV2 0 .xmm0 = some 9 ∧
      witX87Nach witV2 0 0 = some (BitVec.ofNat 8 0) ∧
      witFpNach witV2b 1 = some 0x1FBF ∧
      witXmmNach witV2b 1 .xmm0 = some 11 ∧
      witNachFlush = some (BitVec.ofNat 8 5) ∧
      xsaveWitFehler (xsaveWiederherstellen xsaveWitStartR 0 xsaveWitAreaR
        xsaveWitXc true false xsaveWitF) = 12 ∧
      XsaveWf xsaveWitStart ∧
      (∀ t : Nat, t < 152 → (witM2b.x87 1) t =
        (xsaveWitStart.x87 1) t) ∧
      (∀ r : XmmReg, (witM2.ym.ober 0) r =
        (xsaveWitStart.ym.ober 0) r) ∧
      XsaveSchritt xsaveWitStart witV1b
        (.saveReq 1 xsaveWitArea1 xsaveWitXc true false) ∧
      XsaveSchritt witV1b witM2b
        (.rstorReq 1 xsaveWitArea1 xsaveWitXc true false) ∧
      XsaveSchritt xsaveWitStart xsaveWitStart (.verweigert 0) := by
  exact ⟨wit_buf.1, wit_buf.2, wit_restore0.1, wit_restore0.2,
    wit_restore1.1, wit_restore1.2, wit_drain.1, wit_gp_reserviert,
    xsaveWitStart_wf, wit_rundlauf_anwendung1.1,
    wit_rundlauf_anwendung0.2, wit_schritt_save1,
    wit_schritt_rstor1, wit_schritt_nm⟩

/- CUTS:
    Proved here, over the coherent machine (`HwMaschine`/
    `HwSchritt`/`HwWf`, HardwareExecution §11) with the accepted
    TSO byte equations (`issueByte`/`loadByte`/`flushKern`,
    `issueListe`), the accepted footprint helpers (`ctxAlle`,
    `fxEintraegeAux`, `ctxLadeAux`, `ctxLade_geladen`,
    `ctxFalte`, `ctxNull`) and the accepted legacy image
    (`ctxByte`, `fxDekodiere`, `ctxOffsets`,
    `mxcsrReserviertFrei`, `ldmxcsrArchOk`, `xcr0SseBereit`,
    `xcr0AvxBereit`), the accepted YMM file (`YmmDatei`,
    `xmmSet`, `vecJoin`, `vLo`, `vHi`) and the accepted fault
    vocabulary (`ArchFehler`), all lifted unchanged:
    - full area image (`xsaveByte`: opaque x87 bytes 0-23/32-159,
      MXCSR 24-27, mask 28-31, XMM 160-415, header 512-575 with
      zero XCOMP_BV in the standard form, YMM 576-831) with
      decode (`xsaveDekodiere`) and per-component pure round
      trips (`xsaveRundlauf_x87/_maske/_kopf/_legacy/_ymm`);
    - RFBM-selective footprint (`xsaveOffsets`: x87/mask/header
      always, legacy iff SSE, YMM iff AVX) with `Nodup`
      (bound-proved: the 736-entry joint list exceeds the kernel
      memory budget, so no `decide` over it) and membership;
    - `XsaveMaschine` (YMM machine plus opaque per-core x87
      images and carried masks) with footprint-checked buffered
      save (`xsaveSpeichern`) and restore
      (`xsaveWiederherstellen`): buffer growth, memory silence,
      `XsaveWf` preservation, owner-only forwarding;
    - ordered fault gates as outcomes (NM > UD-CPUID/LOCK/XCR0
      > empty-request refusal > GP-x87/canonical/alignment >
      SS > PF > AC > permission refusal), the reserved-bit #GP
      with exact `ldmxcsrArchOk` agreement;
    - SAVE THEN RESTORE IS THE IDENTITY on the enabled
      components (`xsaveRundlauf_maschine`: opaque x87 always,
      MXCSR/XMM where SSE, YMM where AVX, masks untouched),
      both generic and applied to reached states;
    - FINIT (`xsaveFinit`: reset image, everything else kept)
      with the finit round-trip corollary;
    - the family step relation (`XsaveSchritt`) with `XsaveWf`
      preservation and the exact two-way coherent embedding of
      the TSO legs (no `HwAdapter` plug: x87/mask/YMM state
      lives beside `HwMaschine`, so no adapter over
      `HwMaschine` can carry a save without inventing state);
    - (4) a reached non-degenerate joint witness
      (`xsaveRundlauf_maschine_zeuge`): two buffered saves with
      owner-only forwarding, a memory-changing drain, applied
      and observed round trips, planted refusals, FINIT facts
      and well-formedness.
    Silicon provenance (Intel SDM 325462-093US Vol.1 Ch.13 and
    Vol.2A FXSAVE/FXRSTOR/XSAVE/XRSTOR/FINIT entries,
    clone-local extracts; provenance only, never a proof).
    Named silicon/timing assumptions: none beyond
    self-consistency of the lifted model; in particular no
    hardware correspondence, no timing, no serialization claim.
    NOT proved here, and not claimed:
    - No x87 FPU execution: the area bytes are an opaque
      preserved block; FINIT's exact architectural reset bytes
      are an opaque constant, not a silicon claim.
    - No MXCSR_MASK silicon semantics: the mask value is
      carried and written but its meaning (which bits are
      writable) is unchecked; restore ignores it (stated).
    - No header consistency: XSTATE_BV vs the request set and
      the compaction word are decoded, never enforced.
    - No RFBM computation (request flags are checked inputs),
      no XSS/supervisor states, no XSAVEOPT/XSAVES/XRSTORS,
      no compaction.
    - Fault inputs (TS bit, CPUID bits, LOCK, segment limits,
      paging, CPL/AC) are an oracle: classes and priority are
      modeled, their derivation is not.
    - No 57-bit canonical addresses (48-bit check only).
    - No 736-entry joint kernel evaluation (kernel memory
      wall): the joint set is proved generic, observed per
      enabled set (476 AVX-only, 480 SSE-only).
    - No per-access target-to-W/GX simulation, no whole-word
      atomicity beyond the accepted byte equations, no
      source/IR/ABI/loader/entry/budget link.
    - Handler bodies stay user logic; only the
      save-then-restore composition is proved.
    - `gabbro_ziel` axioms are untouched.
-/

#print axioms xsaveRundlauf_x87
#print axioms xsaveRundlauf_maske
#print axioms xsaveRundlauf_kopf
#print axioms xsaveRundlauf_legacy
#print axioms xsaveRundlauf_ymm
#print axioms xsaveOffsets_nodup
#print axioms xsaveSpeichern_puffer
#print axioms xsaveSpeichern_kein_speicher
#print axioms xsaveWeiterleitung_gespeichert
#print axioms xsaveRundlauf_maschine
#print axioms xsaveWiederherstellen_fehlerGP_reserviert
#print axioms xsaveRestore_stimmt_ldmxcsr_ueberein
#print axioms xsaveSpeichern_wf
#print axioms xsaveWiederherstellen_wf
#print axioms xsaveFinit_rundlauf
#print axioms xsaveSchritt_wf
#print axioms xsaveLade_ist_hw
#print axioms xsaveGibAus_ist_hw
#print axioms xsaveSpüle_ist_hw_zurueck
#print axioms xsaveRundlauf_maschine_zeuge

end Gabbro.Grammatik.X86
