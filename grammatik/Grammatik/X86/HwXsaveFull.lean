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
def vollOffsets (sse avx : Bool) : List Nat :=
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
theorem vollOffsets_klein (sse avx : Bool) (i : Nat)
    (h : i ∈ vollOffsets sse avx) : i < 832 := by
  unfold vollOffsets at h
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
theorem vollOffsets_nodup (sse avx : Bool) :
    (vollOffsets sse avx).Nodup := by
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
  unfold vollOffsets
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
theorem vollOffsets_x87_lo (t : Nat) (ht : t < 24) (sse avx : Bool) :
    t ∈ vollOffsets sse avx := by
  have h1 : t ∈ x87Offsets := by
    unfold x87Offsets
    exact List.mem_append.mpr
      (Or.inl (List.mem_range.mpr ht))
  unfold vollOffsets
  exact List.mem_append.mpr (Or.inl h1)

/-- x87 high offsets are in the footprint. -/
theorem vollOffsets_x87_hi (t : Nat) (ht : t < 128) (sse avx : Bool) :
    32 + t ∈ vollOffsets sse avx := by
  have h1 : 32 + t ∈ x87Offsets := by
    unfold x87Offsets
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
      ⟨t, List.mem_range.mpr ht, rfl⟩))
  unfold vollOffsets
  exact List.mem_append.mpr (Or.inl h1)

/-- Mask offsets are in the footprint. -/
theorem vollOffsets_maske (j : Nat) (hj : j < 4) (sse avx : Bool) :
    28 + j ∈ vollOffsets sse avx := by
  have h1 : 28 + j ∈ maskOffsets :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  unfold vollOffsets
  exact List.mem_append.mpr
    (Or.inr (List.mem_append.mpr (Or.inl h1)))

/-- MXCSR offsets are in the footprint where SSE is saved. -/
theorem vollOffsets_mxcsr (j : Nat) (hj : j < 4) (hs : sse = true)
    (avx : Bool) :
    24 + j ∈ vollOffsets sse avx := by
  have e : (if sse then ctxOffsets else []) = ctxOffsets :=
    if_pos hs
  have h1 : 24 + j ∈ (if sse then ctxOffsets else []) := by
    rw [e]
    exact ctxOffsets_mxcsr j hj
  unfold vollOffsets
  exact List.mem_append.mpr
    (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr
      (Or.inl h1)))))

/-- XMM slot offsets are in the footprint where SSE is saved. -/
theorem vollOffsets_xmm (n j : Nat) (hn : n < 16) (hj : j < 16)
    (hs : sse = true) (avx : Bool) :
    160 + 16 * n + j ∈ vollOffsets sse avx := by
  have e : (if sse then ctxOffsets else []) = ctxOffsets :=
    if_pos hs
  have h1 : 160 + 16 * n + j ∈ (if sse then ctxOffsets else []) := by
    rw [e]
    exact ctxOffsets_xmm n j hn hj
  unfold vollOffsets
  exact List.mem_append.mpr
    (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr
      (Or.inl h1)))))

/-- Header offsets are in the footprint. -/
theorem vollOffsets_kopf (t : Nat) (ht : t < 64) (sse avx : Bool) :
    512 + t ∈ vollOffsets sse avx := by
  have h1 : 512 + t ∈ kopfOffsets :=
    List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩
  unfold vollOffsets
  exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
    (List.mem_append.mpr (Or.inr (List.mem_append.mpr
      (Or.inl h1)))))))

/-- YMM slot offsets are in the footprint where AVX is saved. -/
theorem vollOffsets_ymm (n j : Nat) (hn : n < 16) (hj : j < 16)
    (sse : Bool) (ha : avx = true) :
    576 + 16 * n + j ∈ vollOffsets sse avx := by
  have e : (if avx then ymmOffsets else []) = ymmOffsets :=
    if_pos ha
  have h1 : 576 + 16 * n + j ∈ (if avx then ymmOffsets else []) := by
    rw [e]
    exact List.mem_map.mpr ⟨16 * n + j, List.mem_range.mpr (by omega),
      by omega⟩
  unfold vollOffsets
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
def vollLaenge : Nat := 832

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
def vollByte (k : FPKontext) (x : XmmDatei) (b : X87Bild)
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
theorem vollByte_x87_lo (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (t : Nat)
    (ht : t < 24) :
    vollByte k x b mm h y t = b t := by
  unfold vollByte
  rw [if_pos ht]

/-- Image at an x87 high offset is the opaque byte. -/
theorem vollByte_x87_hi (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (t : Nat)
    (ht : t < 128) :
    vollByte k x b mm h y (32 + t) = b (24 + t) := by
  unfold vollByte
  have e1 : ¬ (32 + t < 24) := by omega
  have e2 : ¬ (32 + t < 28) := by omega
  have e3 : ¬ (32 + t < 32) := by omega
  have e4 : 32 + t < 160 := by omega
  have e5 : 32 + t - 8 = 24 + t := by omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_pos e4, e5]

/-- Image at a mask offset is the mask byte. -/
theorem vollByte_maske (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (j : Nat)
    (hj : j < 4) :
    vollByte k x b mm h y (28 + j) = mxcsrByte mm j := by
  unfold vollByte
  have e1 : ¬ (28 + j < 24) := by omega
  have e2 : ¬ (28 + j < 28) := by omega
  have e3 : 28 + j < 32 := by omega
  have e4 : 28 + j - 28 = j := by omega
  rw [if_neg e1, if_neg e2, if_pos e3, e4]

/-- Image at an MXCSR offset is the control byte (legacy path). -/
theorem vollByte_mxcsr (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (j : Nat)
    (hj : j < 4) :
    vollByte k x b mm h y (24 + j) = mxcsrByte k.mxcsr j := by
  unfold vollByte
  have e1 : ¬ (24 + j < 24) := by omega
  have e2 : 24 + j < 28 := by omega
  rw [if_neg e1, if_pos e2]
  exact ctxByte_mxcsr k x j hj

/-- Image at an XMM low-half offset (legacy path). -/
theorem vollByte_xmm_lo (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (r : XmmReg)
    (j : Nat) (hj : j < 8) :
    vollByte k x b mm h y (160 + 16 * xmmIdx r + j) =
      wortByte (vLo (x r)) j := by
  have hn := xmmIdx_klein r
  unfold vollByte
  have e1 : ¬ (160 + 16 * xmmIdx r + j < 24) := by omega
  have e2 : ¬ (160 + 16 * xmmIdx r + j < 28) := by omega
  have e3 : ¬ (160 + 16 * xmmIdx r + j < 32) := by omega
  have e4 : ¬ (160 + 16 * xmmIdx r + j < 160) := by omega
  have e5 : 160 + 16 * xmmIdx r + j < 416 := by omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_pos e5]
  exact ctxByte_xmm_lo k x r j hj

/-- Image at an XMM high-half offset (legacy path). -/
theorem vollByte_xmm_hi (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (r : XmmReg)
    (j : Nat) (hj : j < 8) :
    vollByte k x b mm h y (168 + 16 * xmmIdx r + j) =
      wortByte (vHi (x r)) j := by
  have hn := xmmIdx_klein r
  unfold vollByte
  have e1 : ¬ (168 + 16 * xmmIdx r + j < 24) := by omega
  have e2 : ¬ (168 + 16 * xmmIdx r + j < 28) := by omega
  have e3 : ¬ (168 + 16 * xmmIdx r + j < 32) := by omega
  have e4 : ¬ (168 + 16 * xmmIdx r + j < 160) := by omega
  have e5 : 168 + 16 * xmmIdx r + j < 416 := by omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_pos e5]
  exact ctxByte_xmm_hi k x r j hj

/-- Image at a header offset is the header byte. -/
theorem vollByte_kopf (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (t : Nat)
    (ht : t < 64) :
    vollByte k x b mm h y (512 + t) = kopfByte h t := by
  unfold vollByte
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
theorem vollByte_ymm_lo (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (r : XmmReg)
    (j : Nat) (hj : j < 8) :
    vollByte k x b mm h y (576 + 16 * xmmIdx r + j) =
      wortByte (vLo (y r)) j := by
  have hn := xmmIdx_klein r
  unfold vollByte
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
theorem vollByte_ymm_hi (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (r : XmmReg)
    (j : Nat) (hj : j < 8) :
    vollByte k x b mm h y (584 + 16 * xmmIdx r + j) =
      wortByte (vHi (y r)) j := by
  have e : 584 + 16 * xmmIdx r + j = 576 + 16 * xmmIdx r + (8 + j) := by
    omega
  have hn := xmmIdx_klein r
  rw [e]
  unfold vollByte
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
structure VollBild where
  mxcsr : MXCSR
  xmm : XmmDatei
  x87img : X87Bild
  maske : BitVec 32
  kopf : XsaveKopf
  ymm : YmmDatei

/-- Decode a full area image. -/
def vollDekodiere (f : Nat → Byte) : VollBild :=
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
theorem vollRundlauf_x87 (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (t : Nat)
    (ht : t < 152) :
    (vollDekodiere (vollByte k x b mm h y)).x87img t = b t := by
  unfold vollDekodiere
  simp only
  by_cases hl : t < 24
  · rw [x87AreaOff_lo t hl]
    exact vollByte_x87_lo k x b mm h y t hl
  · rw [x87AreaOff_hi t hl]
    have ht24 : t - 24 < 128 := by omega
    have hrw := vollByte_x87_hi k x b mm h y (t - 24) ht24
    rw [hrw]
    have : 24 + (t - 24) = t := by omega
    rw [this]

/-- Mask round trip (the accepted MXCSR image lemmas, reused). -/
theorem vollRundlauf_maske (k : FPKontext) (x : XmmDatei)
    (b : X87Bild) (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) :
    (vollDekodiere (vollByte k x b mm h y)).maske = mm := by
  unfold vollDekodiere
  simp only
  have hkong := mxcsrAusBytes_kongr _ _
    (fun i hi => vollByte_maske k x b mm h y i hi)
  rw [hkong]
  exact mxcsr_rundlauf mm

/-- Header round trip: BV and compaction word decode back. -/
theorem vollRundlauf_kopf (k : FPKontext) (x : XmmDatei)
    (b : X87Bild) (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) :
    (vollDekodiere (vollByte k x b mm h y)).kopf = h := by
  have hbv : bytesWort (fun j : Fin 8 =>
      vollByte k x b mm h y (512 + j.val)) = h.bv := by
    have heq : (fun j : Fin 8 => vollByte k x b mm h y (512 + j.val)) =
        (fun j : Fin 8 => kopfByte h j.val) := by
      funext j
      have ht64 : j.val < 64 := by have h8 := j.isLt; omega
      exact vollByte_kopf k x b mm h y j.val ht64
    rw [heq]
    have heq2 : (fun j : Fin 8 => kopfByte h j.val) =
        (fun j : Fin 8 => wortByte h.bv j.val) := by
      funext j
      exact kopfByte_lo h j.val j.isLt
    rw [heq2]
    exact bytesWort_wortByte h.bv
  have hcomp : bytesWort (fun j : Fin 8 =>
      vollByte k x b mm h y (520 + j.val)) = h.comp := by
    have heq : (fun j : Fin 8 => vollByte k x b mm h y (520 + j.val)) =
        (fun j : Fin 8 => kopfByte h (8 + j.val)) := by
      funext j
      have e : 520 + j.val = 512 + (8 + j.val) := by omega
      have ht64 : 8 + j.val < 64 := by have h8 := j.isLt; omega
      rw [e]
      exact vollByte_kopf k x b mm h y (8 + j.val) ht64
    rw [heq]
    have heq2 : (fun j : Fin 8 => kopfByte h (8 + j.val)) =
        (fun j : Fin 8 => wortByte h.comp j.val) := by
      funext j
      exact kopfByte_hi h j.val j.isLt
    rw [heq2]
    exact bytesWort_wortByte h.comp
  unfold vollDekodiere
  simp only
  cases h with
  | mk bv comp =>
    simp only at hbv hcomp ⊢
    rw [hbv, hcomp]

/-- Legacy MXCSR/XMM round trip (the accepted pure identity). -/
theorem vollRundlauf_legacy (k : FPKontext) (x : XmmDatei)
    (b : X87Bild) (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) :
    (vollDekodiere (vollByte k x b mm h y)).mxcsr = k.mxcsr ∧
      ∀ r : XmmReg,
        (vollDekodiere (vollByte k x b mm h y)).xmm r = x r := by
  refine ⟨?_, ?_⟩
  · unfold vollDekodiere
    simp only
    have hkong := mxcsrAusBytes_kongr _ _
      (fun i hi => vollByte_mxcsr k x b mm h y i hi)
    rw [hkong]
    exact mxcsr_rundlauf k.mxcsr
  · intro r
    unfold vollDekodiere
    simp only
    have hlo : (fun j : Fin 8 => vollByte k x b mm h y
        (160 + 16 * xmmIdx r + j.val)) =
        (fun j : Fin 8 => wortByte (vLo (x r)) j.val) := by
      funext j
      exact vollByte_xmm_lo k x b mm h y r j.val j.isLt
    have hhi : (fun j : Fin 8 => vollByte k x b mm h y
        (168 + 16 * xmmIdx r + j.val)) =
        (fun j : Fin 8 => wortByte (vHi (x r)) j.val) := by
      funext j
      exact vollByte_xmm_hi k x b mm h y r j.val j.isLt
    rw [hlo, hhi, bytesWort_wortByte, bytesWort_wortByte]
    exact vecJoin_split (x r)

/-- YMM round trip: decoding the saved upper halves recovers them. -/
theorem vollRundlauf_ymm (k : FPKontext) (x : XmmDatei)
    (b : X87Bild) (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei)
    (r : XmmReg) :
    (vollDekodiere (vollByte k x b mm h y)).ymm r = y r := by
  unfold vollDekodiere
  simp only
  have hlo : (fun j : Fin 8 => vollByte k x b mm h y
      (576 + 16 * xmmIdx r + j.val)) =
      (fun j : Fin 8 => wortByte (vLo (y r)) j.val) := by
    funext j
    exact vollByte_ymm_lo k x b mm h y r j.val j.isLt
  have hhi : (fun j : Fin 8 => vollByte k x b mm h y
      (584 + 16 * xmmIdx r + j.val)) =
      (fun j : Fin 8 => wortByte (vHi (y r)) j.val) := by
    funext j
    exact vollByte_ymm_hi k x b mm h y r j.val j.isLt
  rw [hlo, hhi, bytesWort_wortByte, bytesWort_wortByte]
  exact vecJoin_split (y r)

/-- MXCSR decoding depends only on the footprint bytes
    where SSE is saved. -/
theorem vollKongr_mxcsr (f g : Nat → Byte) (sse avx : Bool)
    (hs : sse = true)
    (h : ∀ i ∈ vollOffsets sse avx, f i = g i) :
    (vollDekodiere f).mxcsr = (vollDekodiere g).mxcsr := by
  unfold vollDekodiere
  simp only
  apply mxcsrAusBytes_kongr
  intro i hi
  exact h (24 + i) (vollOffsets_mxcsr i hi hs avx)

/-- XMM decoding depends only on the footprint bytes
    where SSE is saved. -/
theorem vollKongr_xmm (f g : Nat → Byte) (sse avx : Bool)
    (hs : sse = true)
    (h : ∀ i ∈ vollOffsets sse avx, f i = g i) (r : XmmReg) :
    (vollDekodiere f).xmm r = (vollDekodiere g).xmm r := by
  unfold vollDekodiere
  simp only
  have hn := xmmIdx_klein r
  have hlo : (fun j : Fin 8 => f (160 + 16 * xmmIdx r + j.val)) =
      (fun j : Fin 8 => g (160 + 16 * xmmIdx r + j.val)) := by
    funext j
    have hj16 : j.val < 16 := by have h8 := j.isLt; omega
    exact h _ (vollOffsets_xmm (xmmIdx r) j.val hn hj16 hs avx)
  have hhi : (fun j : Fin 8 => f (168 + 16 * xmmIdx r + j.val)) =
      (fun j : Fin 8 => g (168 + 16 * xmmIdx r + j.val)) := by
    funext j
    have hj16 : 8 + j.val < 16 := by have := j.isLt; omega
    have e : 168 + 16 * xmmIdx r + j.val =
        160 + 16 * xmmIdx r + (8 + j.val) := by omega
    rw [e]
    exact h _ (vollOffsets_xmm (xmmIdx r) (8 + j.val) hn hj16 hs avx)
  rw [hlo, hhi]

/-- x87 decoding depends only on the footprint bytes (always saved). -/
theorem vollKongr_x87 (f g : Nat → Byte) (sse avx : Bool)
    (h : ∀ i ∈ vollOffsets sse avx, f i = g i) (t : Nat)
    (ht : t < 152) :
    (vollDekodiere f).x87img t = (vollDekodiere g).x87img t := by
  unfold vollDekodiere
  simp only
  by_cases hl : t < 24
  · rw [x87AreaOff_lo t hl]
    exact h t (vollOffsets_x87_lo t hl sse avx)
  · rw [x87AreaOff_hi t hl]
    exact h _ (vollOffsets_x87_hi (t - 24) (by omega) sse avx)

/-- Mask decoding depends only on the footprint bytes. -/
theorem vollKongr_maske (f g : Nat → Byte) (sse avx : Bool)
    (h : ∀ i ∈ vollOffsets sse avx, f i = g i) :
    (vollDekodiere f).maske = (vollDekodiere g).maske := by
  unfold vollDekodiere
  simp only
  apply mxcsrAusBytes_kongr
  intro i hi
  exact h (28 + i) (vollOffsets_maske i hi sse avx)

/-- Header decoding depends only on the footprint bytes. -/
theorem vollKongr_kopf (f g : Nat → Byte) (sse avx : Bool)
    (h : ∀ i ∈ vollOffsets sse avx, f i = g i) :
    (vollDekodiere f).kopf = (vollDekodiere g).kopf := by
  unfold vollDekodiere
  simp only
  have hbv : (fun j : Fin 8 => f (512 + j.val)) =
      (fun j : Fin 8 => g (512 + j.val)) := by
    funext j
    have ht64 : j.val < 64 := by have h8 := j.isLt; omega
    exact h _ (vollOffsets_kopf j.val ht64 sse avx)
  have hcomp : (fun j : Fin 8 => f (520 + j.val)) =
      (fun j : Fin 8 => g (520 + j.val)) := by
    funext j
    have e : 520 + j.val = 512 + (8 + j.val) := by omega
    have ht64 : 8 + j.val < 64 := by have h8 := j.isLt; omega
    rw [e]
    exact h _ (vollOffsets_kopf (8 + j.val) ht64 sse avx)
  rw [hbv, hcomp]

/-- YMM decoding depends only on the footprint bytes
    where AVX is saved. -/
theorem vollKongr_ymm (f g : Nat → Byte) (sse avx : Bool)
    (ha : avx = true)
    (h : ∀ i ∈ vollOffsets sse avx, f i = g i) (r : XmmReg) :
    (vollDekodiere f).ymm r = (vollDekodiere g).ymm r := by
  unfold vollDekodiere
  simp only
  have hn := xmmIdx_klein r
  have hlo : (fun j : Fin 8 => f (576 + 16 * xmmIdx r + j.val)) =
      (fun j : Fin 8 => g (576 + 16 * xmmIdx r + j.val)) := by
    funext j
    have hj16 : j.val < 16 := by have h8 := j.isLt; omega
    exact h _ (vollOffsets_ymm (xmmIdx r) j.val hn hj16 sse ha)
  have hhi : (fun j : Fin 8 => f (584 + 16 * xmmIdx r + j.val)) =
      (fun j : Fin 8 => g (584 + 16 * xmmIdx r + j.val)) := by
    funext j
    have hj16 : 8 + j.val < 16 := by have := j.isLt; omega
    have e : 584 + 16 * xmmIdx r + j.val =
        576 + 16 * xmmIdx r + (8 + j.val) := by omega
    rw [e]
    exact h _ (vollOffsets_ymm (xmmIdx r) (8 + j.val) hn hj16 sse ha)
  rw [hlo, hhi]

end Gabbro.Grammatik.X86
