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

/-! ## 3. Machine state, save entries, and the TSO bridge.

  The full machine pairs the coherent YMM machine (which carries
  XMM, YMM upper halves, registers and the TSO view) with the
  opaque per-core x87 image and the per-core MXCSR_MASK value (a
  fixed CPU constant, carried, never computed). -/

/-- Full XSAVE machine: coherent YMM machine plus per-core opaque
    x87 image and mask value. -/
structure VollMaschine where
  ym : YmmMaschine
  x87 : Nat → X87Bild
  maske : Nat → BitVec 32

/-- The coherent machine inside the full state. -/
def vollHw (v : VollMaschine) : HwMaschine := v.ym.hw

/-- Well-formedness is the coherent well-formedness. -/
def VollWf (v : VollMaschine) : Prop := HwWf v.ym.hw

/-- Memory/buffer update from a TSO successor: core data, x87
    images and masks are untouched. -/
def setVollTso (v : VollMaschine) (s : TSOZustand) : VollMaschine :=
  { v with ym := ⟨setTso v.ym.hw s, v.ym.ober⟩ }

/-- The TSO view of a memory/buffer update is the successor state. -/
theorem setVollTso_ansicht (v : VollMaschine) (s : TSOZustand) :
    tsoAnsicht (vollHw (setVollTso v s)) = s := by
  unfold vollHw setVollTso
  simp only
  exact setTso_ansicht v.ym.hw s

/-- A save changes no core data. -/
theorem setVollTso_kern (v : VollMaschine) (s : TSOZustand)
    (c : Nat) :
    (vollHw (setVollTso v s)).kerne c = (vollHw v).kerne c := rfl

/-- A save keeps the x87 images. -/
theorem setVollTso_x87 (v : VollMaschine) (s : TSOZustand) :
    (setVollTso v s).x87 = v.x87 := rfl

/-- A save keeps the masks. -/
theorem setVollTso_maske (v : VollMaschine) (s : TSOZustand) :
    (setVollTso v s).maske = v.maske := rfl

/-- A save keeps the YMM upper files. -/
theorem setVollTso_ober (v : VollMaschine) (s : TSOZustand) :
    (setVollTso v s).ym.ober = v.ym.ober := rfl

/-- Memory/buffer updates preserve well-formedness. -/
theorem setVollTso_wf (v : VollMaschine) (s : TSOZustand)
    (h : VollWf v) : VollWf (setVollTso v s) :=
  setTso_wf v.ym.hw s h

/-- Install restored components on core `c`: FP context, XMM file,
    YMM upper file and the opaque x87 image. Masks are never
    installed (silicon leaves MXCSR_MASK unchanged on restore). -/
def setVollKern (v : VollMaschine) (c : Nat) (k : FPKontext)
    (x : XmmDatei) (y : YmmDatei) (b : X87Bild) : VollMaschine :=
  ⟨⟨setKernDaten v.ym.hw c
      ⟨(v.ym.hw.kerne c).register, (v.ym.hw.kerne c).flags,
        (v.ym.hw.kerne c).rip, x, k⟩,
    fun d => if d = c then y else v.ym.ober d⟩,
   fun d => if d = c then b else v.x87 d, v.maske⟩

/-- Installed core answers the restored control word. -/
theorem setVollKern_fp (v : VollMaschine) (c : Nat) (k : FPKontext)
    (x : XmmDatei) (y : YmmDatei) (b : X87Bild) :
    (((vollHw (setVollKern v c k x y b)).kerne c).fp).mxcsr =
      k.mxcsr := by
  unfold vollHw setVollKern
  rw [setKernDaten_fp]

/-- Installed core answers the restored XMM file. -/
theorem setVollKern_xmm (v : VollMaschine) (c : Nat) (k : FPKontext)
    (x : XmmDatei) (y : YmmDatei) (b : X87Bild) (r : XmmReg) :
    ((vollHw (setVollKern v c k x y b)).kerne c).xmm r = x r := by
  unfold vollHw setVollKern
  rw [setKernDaten_xmm]

/-- Installed core answers the restored upper half. -/
theorem setVollKern_ober (v : VollMaschine) (c : Nat) (k : FPKontext)
    (x : XmmDatei) (y : YmmDatei) (b : X87Bild) (r : XmmReg) :
    ((setVollKern v c k x y b).ym.ober c) r = y r := by
  show ((if c = c then y else v.ym.ober c)) r = y r
  rw [if_pos rfl]

/-- Installed core answers the restored opaque byte. -/
theorem setVollKern_x87 (v : VollMaschine) (c : Nat) (k : FPKontext)
    (x : XmmDatei) (y : YmmDatei) (b : X87Bild) (t : Nat) :
    ((setVollKern v c k x y b).x87 c) t = b t := by
  show ((if c = c then b else v.x87 c)) t = b t
  rw [if_pos rfl]

/-- An install keeps the mask (silicon ignores it on restore). -/
theorem setVollKern_maske (v : VollMaschine) (c : Nat) (k : FPKontext)
    (x : XmmDatei) (y : YmmDatei) (b : X87Bild) :
    (setVollKern v c k x y b).maske = v.maske := rfl

/-- An install preserves well-formedness (profiles untouched). -/
theorem setVollKern_wf (v : VollMaschine) (c : Nat) (k : FPKontext)
    (x : XmmDatei) (y : YmmDatei) (b : X87Bild)
    (h : VollWf v) : VollWf (setVollKern v c k x y b) :=
  setKernDaten_wf v.ym.hw c _ h

/-- The save entries of a full state at area base `a`. -/
def vollEintraege (k : FPKontext) (x : XmmDatei) (b : X87Bild)
    (mm : BitVec 32) (h : XsaveKopf) (y : YmmDatei) (sse avx : Bool)
    (a : Adresse) : List TSOEintrag :=
  fxEintraegeAux (vollByte k x b mm h y) a (vollOffsets sse avx)

/-- Observed fault preconditions for one request. Each is a
    CHECKED input (oracle): its derivation (CR0.TS, CPUID
    FXSR/XSAVE, LOCK prefix, segment limits, paging, CPL/AC)
    belongs to the feature/paging apparatus, never assumed here.
    Priority in the step below is NM > UD > GP > SS > PF > AC. -/
structure VollFehlerIn where
  nm : Bool
  cpuidOk : Bool
  lock : Bool
  ss : Bool
  pf : Bool
  ac : Bool

/-- Machine-level outcomes: successor, refusal, or the
    architectural fault class (the accepted `ArchFehler`). -/
inductive VollAusgang where
  | weiter : VollMaschine → VollAusgang
  | verweigert : VollAusgang
  | fehler : ArchFehler → VollAusgang

/-- 48-bit canonical address check (low half or sign-extended
    high half; a non-canonical XSAVE address raises #GP). -/
def kanonisch (a : Adresse) : Bool :=
  decide (a.toNat < 2 ^ 47 ∨ 2 ^ 64 - 2 ^ 47 ≤ a.toNat)

/-- One full save on core `c` at area base `a`: fault gates in
    priority order, XCR0/request gates, canonical and alignment
    gates, the permission gate over the footprint, then the
    buffered byte-issue fold. -/
def vollSpeichern (v : VollMaschine) (c : Nat) (a : Adresse)
    (xc : Xcr0Bild) (sse avx : Bool) (f : VollFehlerIn) :
    VollAusgang :=
  if f.nm then .fehler .nm
  else if !f.cpuidOk || f.lock then .fehler .ud
  else if !xc.x87 then .fehler .gp
  else if sse && !xcr0SseBereit xc then .fehler .ud
  else if avx && !xcr0AvxBereit xc then .fehler .ud
  else if !sse && !avx then .verweigert
  else if !kanonisch a then .fehler .gp
  else if !xAusgerichtet a then .fehler .gp
  else if f.ss then .fehler .ss
  else if f.pf then .fehler .pf
  else if f.ac then .fehler .ac
  else if !ctxAlle (vollHw v).mem.schreibbar a
      (vollOffsets sse avx) then .verweigert
  else match issueListe (tsoAnsicht (vollHw v)) c
      (vollEintraege ((vollHw v).kerne c).fp ((vollHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
        sse avx a) with
  | none => .verweigert
  | some s' => .weiter (setVollTso v s')

/-- Success shape: a successful save is a successful issue fold. -/
theorem vollSpeichern_erfolg (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (m' : VollMaschine)
    (h : vollSpeichern v c a xc sse avx f = .weiter m') :
    ∃ s' : TSOZustand,
      issueListe (tsoAnsicht (vollHw v)) c
        (vollEintraege ((vollHw v).kerne c).fp ((vollHw v).kerne c).xmm
          (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
          sse avx a) = some s' ∧
      m' = setVollTso v s' := by
  unfold vollSpeichern at h
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
              cases hkan : (!kanonisch a) with
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
                        cases hp : (!ctxAlle (vollHw v).mem.schreibbar
                            a (vollOffsets sse avx)) with
                        | true =>
                          simp [hn, hc, hx, hsse, havx, hleer, hkan,
                            hal, hss, hpf, hac, hp] at h
                        | false =>
                          simp [hn, hc, hx, hsse, havx, hleer, hkan,
                            hal, hss, hpf, hac, hp] at h
                          cases hs2 : issueListe (tsoAnsicht (vollHw v))
                              c (vollEintraege ((vollHw v).kerne c).fp
                                ((vollHw v).kerne c).xmm (v.x87 c)
                                (v.maske c) (kopfStandard sse avx)
                                (v.ym.ober c) sse avx a) with
                          | none =>
                            rw [hs2] at h
                            cases h
                          | some s' =>
                            have hm : setVollTso v s' = m' := by
                              simpa [hs2] using h
                            exact ⟨s', rfl, hm.symm⟩

/-- SAVE GOES THROUGH THE TSO BUFFER: the acting core's buffer
    grows by exactly the footprint entries. -/
theorem vollSpeichern_puffer (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (m' : VollMaschine)
    (h : vollSpeichern v c a xc sse avx f = .weiter m') :
    (vollHw m').puffer c = (vollHw v).puffer c ++
      vollEintraege ((vollHw v).kerne c).fp ((vollHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
        sse avx a := by
  obtain ⟨s', hs, rfl⟩ := vollSpeichern_erfolg v c a xc sse avx f m' h
  exact issueListe_haengt_an (tsoAnsicht (vollHw v)) s' c _ hs

/-- A save changes no canonical byte (buffer only). -/
theorem vollSpeichern_kein_speicher (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (m' : VollMaschine)
    (h : vollSpeichern v c a xc sse avx f = .weiter m')
    (x : Adresse) :
    (vollHw m').mem.bytes x = (vollHw v).mem.bytes x := by
  obtain ⟨s', hs, rfl⟩ := vollSpeichern_erfolg v c a xc sse avx f m' h
  exact issueListe_kein_speicher (tsoAnsicht (vollHw v)) s' c _ hs x

/-- A save preserves well-formedness (profiles untouched). -/
theorem vollSpeichern_wf (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (hwf : VollWf v) (m' : VollMaschine)
    (h : vollSpeichern v c a xc sse avx f = .weiter m') :
    VollWf m' := by
  obtain ⟨s', _, rfl⟩ := vollSpeichern_erfolg v c a xc sse avx f m' h
  exact setVollTso_wf v s' hwf

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
theorem vollWeiterleitung_gespeichert (v : VollMaschine) (c : Nat)
    (a : Adresse) (sse avx : Bool) (s1' : TSOZustand)
    (hs : issueListe (tsoAnsicht (vollHw v)) c
      (vollEintraege ((vollHw v).kerne c).fp ((vollHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
        sse avx a) = some s1')
    (hles : ctxAlle (vollHw v).mem.lesbar a (vollOffsets sse avx)
      = true)
    (i : Nat) (hi : i ∈ vollOffsets sse avx) :
    loadByte s1' c (addrOff a i) =
      some (vollByte ((vollHw v).kerne c).fp ((vollHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
        i) := by
  have hbuf := issueListe_haengt_an (tsoAnsicht (vollHw v)) s1' c _ hs
  have hmem : s1'.mem = (tsoAnsicht (vollHw v)).mem :=
    issueListe_mem_still _ _ _ _ hs
  have hmemHw : s1'.mem = (vollHw v).mem := hmem
  have hlesbar : s1'.mem.lesbar (addrOff a i) = true := by
    rw [hmemHw]
    exact ctxAlle_holt (vollHw v).mem.lesbar a (vollOffsets sse avx)
      i hi hles
  have hneu : neuestens (s1'.puffer c) (addrOff a i) =
      some (vollByte ((vollHw v).kerne c).fp ((vollHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
        i) := by
    have he := neuestens_einmal832
      (vollByte ((vollHw v).kerne c).fp ((vollHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c))
      a (vollOffsets sse avx) i
      (fun j hj => vollOffsets_klein sse avx j hj)
      (vollOffsets_klein sse avx i hi) (vollOffsets_nodup sse avx) hi
    have hentries : vollEintraege ((vollHw v).kerne c).fp
        ((vollHw v).kerne c).xmm (v.x87 c) (v.maske c)
        (kopfStandard sse avx) (v.ym.ober c) sse avx a =
        fxEintraegeAux (vollByte ((vollHw v).kerne c).fp
          ((vollHw v).kerne c).xmm (v.x87 c) (v.maske c)
          (kopfStandard sse avx) (v.ym.ober c)) a
          (vollOffsets sse avx) := rfl
    rw [hbuf, hentries, neuestens_append, he]
  unfold loadByte
  rw [if_pos hlesbar, hneu]

/-! ## 4. Machine restore and the save/restore round trip.

  `vollWiederherstellen` loads the footprint through the TSO view
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
def vollWiederherstellen (v : VollMaschine) (c : Nat) (a : Adresse)
    (xc : Xcr0Bild) (sse avx : Bool) (f : VollFehlerIn) :
    VollAusgang :=
  if f.nm then .fehler .nm
  else if !f.cpuidOk || f.lock then .fehler .ud
  else if !xc.x87 then .fehler .gp
  else if sse && !xcr0SseBereit xc then .fehler .ud
  else if avx && !xcr0AvxBereit xc then .fehler .ud
  else if !sse && !avx then .verweigert
  else if !kanonisch a then .fehler .gp
  else if !xAusgerichtet a then .fehler .gp
  else if f.ss then .fehler .ss
  else if f.pf then .fehler .pf
  else if f.ac then .fehler .ac
  else if !ctxAlle (vollHw v).mem.lesbar a (vollOffsets sse avx) then
    .verweigert
  else match ctxLadeAux (tsoAnsicht (vollHw v)) c a
      (vollOffsets sse avx) with
  | none => .verweigert
  | some bs =>
    if !mxcsrReserviertFrei
        (mxcsrAusBytes (fun i => ctxFalte bs ctxNull (24 + i))) then
      .fehler .gp
    else .weiter (setVollKern v c
      (if sse then
        ⟨(vollDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
       else ((vollHw v).kerne c).fp)
      (if sse then (vollDekodiere (ctxFalte bs ctxNull)).xmm
       else ((vollHw v).kerne c).xmm)
      (if avx then (vollDekodiere (ctxFalte bs ctxNull)).ymm
       else v.ym.ober c)
      (vollDekodiere (ctxFalte bs ctxNull)).x87img)

/-- Success shape: a successful restore is a successful footprint
    load with a reserved-free control word where SSE is restored. -/
theorem vollWiederherstellen_erfolg (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (m' : VollMaschine)
    (h : vollWiederherstellen v c a xc sse avx f = .weiter m') :
    ∃ bs : List (Nat × Byte),
      ctxLadeAux (tsoAnsicht (vollHw v)) c a (vollOffsets sse avx) =
        some bs ∧
      m' = setVollKern v c
        (if sse then
          ⟨(vollDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
         else ((vollHw v).kerne c).fp)
        (if sse then (vollDekodiere (ctxFalte bs ctxNull)).xmm
         else ((vollHw v).kerne c).xmm)
        (if avx then (vollDekodiere (ctxFalte bs ctxNull)).ymm
         else v.ym.ober c)
        (vollDekodiere (ctxFalte bs ctxNull)).x87img := by
  unfold vollWiederherstellen at h
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
              cases hkan : (!kanonisch a) with
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
                        cases hp : (!ctxAlle (vollHw v).mem.lesbar
                            a (vollOffsets sse avx)) with
                        | true =>
                          simp [hn, hc, hx, hsse, havx, hleer, hkan,
                            hal, hss, hpf, hac, hp] at h
                        | false =>
                          simp [hn, hc, hx, hsse, havx, hleer, hkan,
                            hal, hss, hpf, hac, hp] at h
                          cases hbs : ctxLadeAux (tsoAnsicht (vollHw v))
                              c a (vollOffsets sse avx) with
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
theorem vollWiederherstellen_wf (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (hwf : VollWf v) (m' : VollMaschine)
    (h : vollWiederherstellen v c a xc sse avx f = .weiter m') :
    VollWf m' := by
  obtain ⟨bs, _, rfl⟩ := vollWiederherstellen_erfolg v c a xc sse avx
    f m' h
  exact setVollKern_wf v c _ _ _ _ hwf

/-- SAVE THEN RESTORE IS THE IDENTITY on the enabled components:
    restoring a just-saved area on the same core with the same
    request set recovers the opaque x87 image, the control word
    and every XMM register where SSE was saved, and every YMM
    upper half where AVX was saved. The mask is untouched by
    construction. Needs read permission beside the save's write
    permission (the restore observes through `loadByte`, which
    checks readability). -/
theorem vollRundlauf_maschine (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (v1 v2 : VollMaschine)
    (hles : ctxAlle (vollHw v).mem.lesbar a (vollOffsets sse avx)
      = true)
    (h1 : vollSpeichern v c a xc sse avx f = .weiter v1)
    (h2 : vollWiederherstellen v1 c a xc sse avx f = .weiter v2) :
    (∀ t : Nat, t < 152 → (v2.x87 c) t = (v.x87 c) t) ∧
      v2.maske c = v.maske c ∧
      (sse = true →
        (((vollHw v2).kerne c).fp).mxcsr =
          (((vollHw v).kerne c).fp).mxcsr) ∧
      (sse = true → ∀ r : XmmReg,
        ((vollHw v2).kerne c).xmm r =
          ((vollHw v).kerne c).xmm r) ∧
      (avx = true → ∀ r : XmmReg,
        (v2.ym.ober c) r = (v.ym.ober c) r) := by
  obtain ⟨s1', hs1, rfl⟩ := vollSpeichern_erfolg v c a xc sse avx f v1
    h1
  obtain ⟨bs, hbs, rfl⟩ := vollWiederherstellen_erfolg
    (setVollTso v s1') c a xc sse avx f v2 h2
  have hsicht : tsoAnsicht (vollHw (setVollTso v s1')) = s1' :=
    setVollTso_ansicht v s1'
  rw [hsicht] at hbs
  have hloads : ∀ i ∈ vollOffsets sse avx,
      loadByte s1' c (addrOff a i) =
        some (vollByte ((vollHw v).kerne c).fp ((vollHw v).kerne c).xmm
          (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
          i) :=
    vollWeiterleitung_gespeichert v c a sse avx s1' hs1 hles
  have hagree : ∀ i ∈ vollOffsets sse avx,
      ctxFalte bs ctxNull i =
        vollByte ((vollHw v).kerne c).fp ((vollHw v).kerne c).xmm
          (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c)
          i := by
    intro i hi
    exact ctxLade_geladen s1' c a
      (vollByte ((vollHw v).kerne c).fp ((vollHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c))
      (vollOffsets sse avx) ctxNull (vollOffsets_nodup sse avx)
      hloads bs hbs i hi
  have hx87id : ∀ t : Nat, t < 152 →
      (vollDekodiere (ctxFalte bs ctxNull)).x87img t = (v.x87 c) t := by
    intro t ht
    have hk := vollKongr_x87 (ctxFalte bs ctxNull)
      (vollByte ((vollHw v).kerne c).fp ((vollHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c))
      sse avx (fun i hi => hagree i hi) t ht
    rw [hk]
    exact vollRundlauf_x87 ((vollHw v).kerne c).fp
      ((vollHw v).kerne c).xmm (v.x87 c) (v.maske c)
      (kopfStandard sse avx) (v.ym.ober c) t ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have e1 := setVollKern_x87 (setVollTso v s1') c
      (if sse then
        ⟨(vollDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
       else ((vollHw (setVollTso v s1')).kerne c).fp)
      (if sse then (vollDekodiere (ctxFalte bs ctxNull)).xmm
       else ((vollHw (setVollTso v s1')).kerne c).xmm)
      (if avx then (vollDekodiere (ctxFalte bs ctxNull)).ymm
       else (setVollTso v s1').ym.ober c)
      (vollDekodiere (ctxFalte bs ctxNull)).x87img t
    rw [e1]
    exact hx87id t ht
  · have e2 := setVollKern_maske (setVollTso v s1') c
      (if sse then
        ⟨(vollDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
       else ((vollHw (setVollTso v s1')).kerne c).fp)
      (if sse then (vollDekodiere (ctxFalte bs ctxNull)).xmm
       else ((vollHw (setVollTso v s1')).kerne c).xmm)
      (if avx then (vollDekodiere (ctxFalte bs ctxNull)).ymm
       else (setVollTso v s1').ym.ober c)
      (vollDekodiere (ctxFalte bs ctxNull)).x87img
    rw [e2, setVollTso_maske]
  · intro hs
    have e3 := setVollKern_fp (setVollTso v s1') c
      (if sse then
        ⟨(vollDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
       else ((vollHw (setVollTso v s1')).kerne c).fp)
      (if sse then (vollDekodiere (ctxFalte bs ctxNull)).xmm
       else ((vollHw (setVollTso v s1')).kerne c).xmm)
      (if avx then (vollDekodiere (ctxFalte bs ctxNull)).ymm
       else (setVollTso v s1').ym.ober c)
      (vollDekodiere (ctxFalte bs ctxNull)).x87img
    rw [e3]
    have hksse : (if sse then
        ⟨(vollDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
        else ((vollHw (setVollTso v s1')).kerne c).fp) =
        ⟨(vollDekodiere (ctxFalte bs ctxNull)).mxcsr⟩ :=
      if_pos hs
    rw [hksse]
    show (vollDekodiere (ctxFalte bs ctxNull)).mxcsr = _
    have hk := vollKongr_mxcsr (ctxFalte bs ctxNull)
      (vollByte ((vollHw v).kerne c).fp ((vollHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c))
      sse avx hs (fun i hi => hagree i hi)
    rw [hk]
    exact (vollRundlauf_legacy ((vollHw v).kerne c).fp
      ((vollHw v).kerne c).xmm (v.x87 c) (v.maske c)
      (kopfStandard sse avx) (v.ym.ober c)).1
  · intro hs r
    have e4 := setVollKern_xmm (setVollTso v s1') c
      (if sse then
        ⟨(vollDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
       else ((vollHw (setVollTso v s1')).kerne c).fp)
      (if sse then (vollDekodiere (ctxFalte bs ctxNull)).xmm
       else ((vollHw (setVollTso v s1')).kerne c).xmm)
      (if avx then (vollDekodiere (ctxFalte bs ctxNull)).ymm
       else (setVollTso v s1').ym.ober c)
      (vollDekodiere (ctxFalte bs ctxNull)).x87img r
    rw [e4]
    have hxsse : (if sse then (vollDekodiere (ctxFalte bs ctxNull)).xmm
        else ((vollHw (setVollTso v s1')).kerne c).xmm) =
        (vollDekodiere (ctxFalte bs ctxNull)).xmm :=
      if_pos hs
    rw [hxsse]
    have hk := vollKongr_xmm (ctxFalte bs ctxNull)
      (vollByte ((vollHw v).kerne c).fp ((vollHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c))
      sse avx hs (fun i hi => hagree i hi) r
    rw [hk]
    exact (vollRundlauf_legacy ((vollHw v).kerne c).fp
      ((vollHw v).kerne c).xmm (v.x87 c) (v.maske c)
      (kopfStandard sse avx) (v.ym.ober c)).2 r
  · intro ha r
    have e5 := setVollKern_ober (setVollTso v s1') c
      (if sse then
        ⟨(vollDekodiere (ctxFalte bs ctxNull)).mxcsr⟩
       else ((vollHw (setVollTso v s1')).kerne c).fp)
      (if sse then (vollDekodiere (ctxFalte bs ctxNull)).xmm
       else ((vollHw (setVollTso v s1')).kerne c).xmm)
      (if avx then (vollDekodiere (ctxFalte bs ctxNull)).ymm
       else (setVollTso v s1').ym.ober c)
      (vollDekodiere (ctxFalte bs ctxNull)).x87img r
    rw [e5]
    have hxavx : (if avx then (vollDekodiere (ctxFalte bs ctxNull)).ymm
        else (setVollTso v s1').ym.ober c) =
        (vollDekodiere (ctxFalte bs ctxNull)).ymm :=
      if_pos ha
    rw [hxavx]
    have hk := vollKongr_ymm (ctxFalte bs ctxNull)
      (vollByte ((vollHw v).kerne c).fp ((vollHw v).kerne c).xmm
        (v.x87 c) (v.maske c) (kopfStandard sse avx) (v.ym.ober c))
      sse avx ha (fun i hi => hagree i hi) r
    rw [hk]
    exact vollRundlauf_ymm ((vollHw v).kerne c).fp
      ((vollHw v).kerne c).xmm (v.x87 c) (v.maske c)
      (kopfStandard sse avx) (v.ym.ober c) r

/-! ## 5. Fault gates: every class fires its outcome.

  Each gate below is one ordered row of the save/restore step:
  #NM first, then #UD (CPUID, LOCK, XCR0), then the empty-request
  refusal, then #GP (x87 bit, canonical, alignment), then
  #SS/#PF/#AC, then the permission refusal. Every premise is used
  by its `simp` (the gate it discharges). -/

/-- #NM has priority: a set TS bit faults, whatever else holds. -/
theorem vollSpeichern_fehlerNM (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h : f.nm = true) :
    vollSpeichern v c a xc sse avx f = .fehler .nm := by
  unfold vollSpeichern
  simp [h]

/-- #UD for a missing CPUID XSAVE bit. -/
theorem vollSpeichern_fehlerUD_ohne_cpuid (v : VollMaschine)
    (c : Nat) (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = false) :
    vollSpeichern v c a xc sse avx f = .fehler .ud := by
  unfold vollSpeichern
  simp [h1, h2]

/-- #UD for a LOCK prefix. -/
theorem vollSpeichern_fehlerUD_lock (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false) (h2 : f.lock = true) :
    vollSpeichern v c a xc sse avx f = .fehler .ud := by
  unfold vollSpeichern
  simp [h1, h2]

/-- #GP where the XCR0 x87 bit is clear. -/
theorem vollSpeichern_fehlerGP_ohne_x87 (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = false) :
    vollSpeichern v c a xc sse avx f = .fehler .gp := by
  unfold vollSpeichern
  simp [h1, h2, h3, h4]

/-- #UD where SSE is requested without XCR0 SSE readiness. -/
theorem vollSpeichern_fehlerUD_ohne_sse (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = false) :
    vollSpeichern v c a xc sse avx f = .fehler .ud := by
  unfold vollSpeichern
  simp [h1, h2, h3, h4, h5, h6]

/-- #UD where AVX is requested without XCR0 AVX readiness. -/
theorem vollSpeichern_fehlerUD_ohne_avx (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = false) (h6 : avx = true)
    (h7 : xcr0AvxBereit xc = false) :
    vollSpeichern v c a xc sse avx f = .fehler .ud := by
  unfold vollSpeichern
  simp [h1, h2, h3, h4, h5, h6, h7]

/-- An empty request is refused, never silently empty. -/
theorem vollSpeichern_verweigert_leer (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = false) (h6 : avx = false) :
    vollSpeichern v c a xc sse avx f = .verweigert := by
  unfold vollSpeichern
  simp [h1, h2, h3, h4, h5, h6]

/-- #GP on a non-canonical address. -/
theorem vollSpeichern_fehlerGP_nicht_kanonisch (v : VollMaschine)
    (c : Nat) (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : kanonisch a = false) :
    vollSpeichern v c a xc sse avx f = .fehler .gp := by
  unfold vollSpeichern
  simp [h1, h2, h3, h4, h5, h6, h7, h8]

/-- #GP on a misaligned area. -/
theorem vollSpeichern_fehlerGP_falsch_ausgerichtet (v : VollMaschine)
    (c : Nat) (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : kanonisch a = true) (h9 : xAusgerichtet a = false) :
    vollSpeichern v c a xc sse avx f = .fehler .gp := by
  unfold vollSpeichern
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- #SS fires ahead of the memory access. -/
theorem vollSpeichern_fehlerSS (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : kanonisch a = true) (h9 : xAusgerichtet a = true)
    (h10 : f.ss = true) :
    vollSpeichern v c a xc sse avx f = .fehler .ss := by
  unfold vollSpeichern
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-- #PF fires ahead of the memory access. -/
theorem vollSpeichern_fehlerPF (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : kanonisch a = true) (h9 : xAusgerichtet a = true)
    (h10 : f.ss = false) (h11 : f.pf = true) :
    vollSpeichern v c a xc sse avx f = .fehler .pf := by
  unfold vollSpeichern
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-- #AC fires last among the fault gates. -/
theorem vollSpeichern_fehlerAC (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : kanonisch a = true) (h9 : xAusgerichtet a = true)
    (h10 : f.ss = false) (h11 : f.pf = false)
    (h12 : f.ac = true) :
    vollSpeichern v c a xc sse avx f = .fehler .ac := by
  unfold vollSpeichern
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

/-- A missing write permission refuses the whole save. -/
theorem vollSpeichern_verweigert_ohne_schreibrecht (v : VollMaschine)
    (c : Nat) (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : kanonisch a = true) (h9 : xAusgerichtet a = true)
    (h10 : f.ss = false) (h11 : f.pf = false)
    (h12 : f.ac = false)
    (h13 : ctxAlle (vollHw v).mem.schreibbar a
      (vollOffsets sse avx) = false) :
    vollSpeichern v c a xc sse avx f = .verweigert := by
  rw [h5, h7] at h13
  unfold vollSpeichern
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

/-- #NM on the restore path. -/
theorem vollWiederherstellen_fehlerNM (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h : f.nm = true) :
    vollWiederherstellen v c a xc sse avx f = .fehler .nm := by
  unfold vollWiederherstellen
  simp [h]

/-- #UD on the restore path without XCR0 SSE readiness. -/
theorem vollWiederherstellen_fehlerUD_ohne_sse (v : VollMaschine)
    (c : Nat) (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = false) :
    vollWiederherstellen v c a xc sse avx f = .fehler .ud := by
  unfold vollWiederherstellen
  simp [h1, h2, h3, h4, h5, h6]

/-- #GP on the restore path for a misaligned area. -/
theorem vollWiederherstellen_fehlerGP_falsch_ausgerichtet
    (v : VollMaschine) (c : Nat) (a : Adresse) (xc : Xcr0Bild)
    (sse avx : Bool) (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : kanonisch a = true) (h9 : xAusgerichtet a = false) :
    vollWiederherstellen v c a xc sse avx f = .fehler .gp := by
  unfold vollWiederherstellen
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- #SS on the restore path. -/
theorem vollWiederherstellen_fehlerSS (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : kanonisch a = true) (h9 : xAusgerichtet a = true)
    (h10 : f.ss = true) :
    vollWiederherstellen v c a xc sse avx f = .fehler .ss := by
  unfold vollWiederherstellen
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-- An empty restore request is refused. -/
theorem vollWiederherstellen_verweigert_leer (v : VollMaschine)
    (c : Nat) (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = false) (h6 : avx = false) :
    vollWiederherstellen v c a xc sse avx f = .verweigert := by
  unfold vollWiederherstellen
  simp [h1, h2, h3, h4, h5, h6]

/-- A missing read permission refuses the whole restore. -/
theorem vollWiederherstellen_verweigert_ohne_leserecht
    (v : VollMaschine) (c : Nat) (a : Adresse) (xc : Xcr0Bild)
    (sse avx : Bool) (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : kanonisch a = true) (h9 : xAusgerichtet a = true)
    (h10 : f.ss = false) (h11 : f.pf = false)
    (h12 : f.ac = false)
    (h13 : ctxAlle (vollHw v).mem.lesbar a
      (vollOffsets sse avx) = false) :
    vollWiederherstellen v c a xc sse avx f = .verweigert := by
  rw [h5, h7] at h13
  unfold vollWiederherstellen
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

/-- A reserved MXCSR bit in the loaded image faults with #GP on
    restore (the accepted `ldmxcsrArchOk` refusal, lifted to the
    area restore). -/
theorem vollWiederherstellen_fehlerGP_reserviert (v : VollMaschine)
    (c : Nat) (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (h1 : f.nm = false)
    (h2 : f.cpuidOk = true) (h3 : f.lock = false)
    (h4 : xc.x87 = true) (h5 : sse = true)
    (h6 : xcr0SseBereit xc = true) (h7 : avx = false)
    (h8 : kanonisch a = true) (h9 : xAusgerichtet a = true)
    (h10 : f.ss = false) (h11 : f.pf = false)
    (h12 : f.ac = false)
    (h13 : ctxAlle (vollHw v).mem.lesbar a
      (vollOffsets sse avx) = true)
    (bs : List (Nat × Byte))
    (h14 : ctxLadeAux (tsoAnsicht (vollHw v)) c a
      (vollOffsets sse avx) = some bs)
    (h15 : 65536 ≤ (mxcsrAusBytes
      (fun i => ctxFalte bs ctxNull (24 + i))).toNat) :
    vollWiederherstellen v c a xc sse avx f = .fehler .gp := by
  rw [h5, h7] at h13 h14
  unfold vollWiederherstellen
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  have hres : mxcsrReserviertFrei
      (mxcsrAusBytes (fun i => ctxFalte bs ctxNull (24 + i))) =
      false :=
    mxcsrReserviertFrei_verweigert _ h15
  simp [hres]

/-- AGREEMENT: the restore's reserved-bit #GP coincides with the
    accepted architectural load refusal `ldmxcsrArchOk`. -/
theorem vollRestore_stimmt_ldmxcsr_ueberein (p : MxcsrProfil)
    (w : MXCSR) (h : 65536 ≤ w.toNat) :
    ldmxcsrArchOk p w = false :=
  ldmxcsrArchOk_reserviert_verweigert p w h

/-! ## 6. FINIT: re-initialise the x87 image.

  `vollFinit` resets the acting core's opaque image to the reset
  constant. Everything else — control word, XMM/YMM files, masks,
  memory, buffers — is untouched, matching silicon FINIT, which
  affects only the x87 state (the FPU execution itself stays out
  of scope: only the stored image moves). -/

/-- FINIT: reset the acting core's opaque x87 image. -/
def vollFinit (v : VollMaschine) (c : Nat) : VollMaschine :=
  ⟨v.ym, fun d => if d = c then x87Reset else v.x87 d, v.maske⟩

/-- FINIT installs the reset image on the acting core. -/
theorem vollFinit_setzt_zurueck (v : VollMaschine) (c : Nat)
    (t : Nat) :
    ((vollFinit v c).x87 c) t = x87Reset t := by
  show ((if c = c then x87Reset else v.x87 c)) t = x87Reset t
  rw [if_pos rfl]

/-- FINIT keeps every other core's image. -/
theorem vollFinit_fremd (v : VollMaschine) (c d : Nat)
    (h : d ≠ c) (t : Nat) :
    ((vollFinit v c).x87 d) t = (v.x87 d) t := by
  show ((if d = c then x87Reset else v.x87 d)) t = (v.x87 d) t
  rw [if_neg h]

/-- FINIT preserves well-formedness (profiles untouched). -/
theorem vollFinit_wf (v : VollMaschine) (c : Nat)
    (hwf : VollWf v) : VollWf (vollFinit v c) :=
  hwf

/-- FINIT keeps the coherent machine (registers, memory,
    buffers all untouched). -/
theorem vollFinit_hw_still (v : VollMaschine) (c : Nat) :
    vollHw (vollFinit v c) = vollHw v := rfl

/-- FINIT keeps the masks. -/
theorem vollFinit_maske_still (v : VollMaschine) (c : Nat) :
    (vollFinit v c).maske = v.maske := rfl

/-- SAVE/RESTORE AFTER FINIT recovers the reset image: the
    identity theorem applied to the reinitialised state. -/
theorem vollFinit_rundlauf (v : VollMaschine) (c : Nat)
    (a : Adresse) (xc : Xcr0Bild) (sse avx : Bool)
    (f : VollFehlerIn) (v1 v2 : VollMaschine)
    (hles : ctxAlle (vollHw (vollFinit v c)).mem.lesbar a
      (vollOffsets sse avx) = true)
    (h1 : vollSpeichern (vollFinit v c) c a xc sse avx f =
      .weiter v1)
    (h2 : vollWiederherstellen v1 c a xc sse avx f = .weiter v2) :
    ∀ t : Nat, t < 152 → (v2.x87 c) t = x87Reset t := by
  intro t ht
  have hr := (vollRundlauf_maschine (vollFinit v c) c a xc sse avx f
    v1 v2 hles h1 h2).1 t ht
  rw [hr]
  exact vollFinit_setzt_zurueck v c t

/-! ## 7. Family step relation and the TSO-leg embedding.

  The x87 image, mask and YMM upper file live beside `HwMaschine`
  (in `VollMaschine`, like the accepted `YmmMaschine` wrapper),
  so no `HwAdapter HwMaschine` plug can carry a save without
  inventing that state. Instead `VollSchritt` runs on the full
  machine: the checked save/restore/FINIT steps, the shared TSO
  legs with the EXACT coherent embedding, and outcome-tied
  refusals (never silent). -/

/-- Observable family events on the full machine. -/
inductive VollEreignis where
  | saveReq : Nat → Adresse → Xcr0Bild → Bool → Bool → VollEreignis
  | rstorReq : Nat → Adresse → Xcr0Bild → Bool → Bool → VollEreignis
  | finitReq : Nat → VollEreignis
  | leseBeob : Nat → Adresse → Byte → VollEreignis
  | schreibAusgabe : Nat → Adresse → Byte → VollEreignis
  | spülung : Nat → TSOEintrag → VollEreignis
  | verweigert : Nat → VollEreignis

/-- Project an outcome to a step successor. -/
def vollOpt (o : VollAusgang) : Option VollMaschine :=
  match o with
  | .weiter v' => some v'
  | _ => none

/-- Family step relation: checked requests plus the shared TSO
    legs plus outcome-tied refusals. The fault-input oracle `f`
    rides in the request (checked inputs, never assumed). -/
inductive VollSchritt : VollMaschine → VollMaschine → VollEreignis → Prop where
  | save {v v' : VollMaschine} (c : Nat) (a : Adresse)
      (xc : Xcr0Bild) (sse avx : Bool) (f : VollFehlerIn)
      (h : vollSpeichern v c a xc sse avx f = .weiter v') :
      VollSchritt v v' (.saveReq c a xc sse avx)
  | rstor {v v' : VollMaschine} (c : Nat) (a : Adresse)
      (xc : Xcr0Bild) (sse avx : Bool) (f : VollFehlerIn)
      (h : vollWiederherstellen v c a xc sse avx f = .weiter v') :
      VollSchritt v v' (.rstorReq c a xc sse avx)
  | finit {v : VollMaschine} (c : Nat) :
      VollSchritt v (vollFinit v c) (.finitReq c)
  | lade {v : VollMaschine} (c : Nat) (a : Adresse) (w : Byte)
      (h : loadByte (tsoAnsicht (vollHw v)) c a = some w) :
      VollSchritt v v (.leseBeob c a w)
  | gibAus {v : VollMaschine} (c : Nat) (a : Adresse) (w : Byte)
      (s' : TSOZustand)
      (h : issueByte (tsoAnsicht (vollHw v)) c a w = some s') :
      VollSchritt v (setVollTso v s') (.schreibAusgabe c a w)
  | spüle {v : VollMaschine} (c : Nat) (e : TSOEintrag)
      (s' : TSOZustand)
      (h : flushKern (tsoAnsicht (vollHw v)) c = some s')
      (hkopf : ((vollHw v).puffer c).head? = some e) :
      VollSchritt v (setVollTso v s') (.spülung c e)
  | fehlerSave {v : VollMaschine} (c : Nat) (a : Adresse)
      (xc : Xcr0Bild) (sse avx : Bool) (f : VollFehlerIn)
      (g : ArchFehler)
      (h : vollSpeichern v c a xc sse avx f = .fehler g) :
      VollSchritt v v (.verweigert c)
  | fehlerRstor {v : VollMaschine} (c : Nat) (a : Adresse)
      (xc : Xcr0Bild) (sse avx : Bool) (f : VollFehlerIn)
      (g : ArchFehler)
      (h : vollWiederherstellen v c a xc sse avx f = .fehler g) :
      VollSchritt v v (.verweigert c)
  | fehlerVerweigert {v : VollMaschine} (c : Nat) (a : Adresse)
      (xc : Xcr0Bild) (sse avx : Bool) (f : VollFehlerIn)
      (h : vollSpeichern v c a xc sse avx f = .verweigert) :
      VollSchritt v v (.verweigert c)

/-- (1) Every family step preserves well-formedness. -/
theorem vollSchritt_wf (v v' : VollMaschine) (e : VollEreignis)
    (h : VollSchritt v v' e) (hwf : VollWf v) : VollWf v' := by
  cases h with
  | save c a xc sse avx f h =>
    exact vollSpeichern_wf _ _ _ _ _ _ _ hwf _ h
  | rstor c a xc sse avx f h =>
    exact vollWiederherstellen_wf _ _ _ _ _ _ _ hwf _ h
  | finit c => exact vollFinit_wf _ _ hwf
  | lade c a w h => exact hwf
  | gibAus c a w s' h => exact setVollTso_wf _ _ hwf
  | spüle c e s' h hkopf => exact setVollTso_wf _ _ hwf
  | fehlerSave c a xc sse avx f g h => exact hwf
  | fehlerRstor c a xc sse avx f g h => exact hwf
  | fehlerVerweigert c a xc sse avx f h => exact hwf

/-- (2) The TSO observation leg IS the coherent TSO step. -/
theorem vollLade_ist_hw (v v' : VollMaschine) (c : Nat)
    (a : Adresse) (w : Byte)
    (h : VollSchritt v v' (.leseBeob c a w)) :
    HwSchritt (vollHw v) (vollHw v') (.leseBeob c a w) := by
  cases h with
  | lade c a w h => exact HwSchritt.lade c a w h

/-- (2) The TSO store-issue leg IS the coherent TSO step. -/
theorem vollGibAus_ist_hw (v v' : VollMaschine) (c : Nat)
    (a : Adresse) (w : Byte)
    (h : VollSchritt v v' (.schreibAusgabe c a w)) :
    ∃ s' : TSOZustand,
      issueByte (tsoAnsicht (vollHw v)) c a w = some s' ∧
      HwSchritt (vollHw v) (vollHw v') (.schreibAusgabe c a w) := by
  cases h with
  | gibAus c a w t ht =>
    exact ⟨t, ht, HwSchritt.gibAus c a w t ht⟩

/-- (2) The TSO drain leg IS the coherent TSO step. -/
theorem vollSpüle_ist_hw (v v' : VollMaschine) (c : Nat)
    (e : TSOEintrag)
    (h : VollSchritt v v' (.spülung c e)) :
    ∃ s' : TSOZustand,
      flushKern (tsoAnsicht (vollHw v)) c = some s' ∧
      HwSchritt (vollHw v) (vollHw v') (.spülung c e) := by
  cases h with
  | spüle c e t ht hkopf =>
    exact ⟨t, ht, HwSchritt.spüle c e t ht hkopf⟩

/-- BACKWARD embedding, exact: a drain step comes only from the
    coherent drain with the same head condition. -/
theorem vollSpüle_ist_hw_zurueck (v v' : VollMaschine) (c : Nat)
    (e : TSOEintrag)
    (h : VollSchritt v v' (.spülung c e)) :
    ∃ s' : TSOZustand,
      flushKern (tsoAnsicht (vollHw v)) c = some s' ∧
      ((vollHw v).puffer c).head? = some e ∧
      v' = setVollTso v s' := by
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
def vollWitArea0 : Adresse := BitVec.ofNat 64 4096

/-- Witness area base, core 1. -/
def vollWitArea1 : Adresse := BitVec.ofNat 64 8192

/-- Witness area base, reserved-bit probe. -/
def vollWitAreaR : Adresse := BitVec.ofNat 64 12288

/-- Witness permission: exactly the two full 832-byte areas. -/
def vollWitOk (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + 832) ||
    decide (8192 ≤ a.toNat ∧ a.toNat < 8192 + 832)

/-- Witness memory: zeroed bytes, footprint permissions. -/
def vollWitMem : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0, lesbar := vollWitOk,
    schreibbar := vollWitOk, ausfuehrbar := fun _ => false }

/-- Witness XMM file, core 0 (low halves 7). -/
def vollWitX0 : XmmDatei :=
  fun _ => vecJoin (BitVec.ofNat 64 7) (BitVec.ofNat 64 0)

/-- Witness XMM file, core 1 (low halves 11). -/
def vollWitX1 : XmmDatei :=
  fun _ => vecJoin (BitVec.ofNat 64 11) (BitVec.ofNat 64 0)

/-- Witness cores: distinct FP state per core. -/
def vollWitKern : Nat → HwKern
  | 0 => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0, vollWitX0, ⟨0x1F80⟩⟩
  | 1 => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0, vollWitX1, ⟨0x1FBF⟩⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness x87 images: core 0 starts from the FINIT reset image,
    every other core carries the constant-`5` image (nonzero, so
    forwarding is observable against zeroed memory). -/
def vollWitX87 : Nat → X87Bild
  | 0 => x87Reset
  | _ => fun _ => BitVec.ofNat 8 5

/-- Witness masks: the `0xFFBF` constant everywhere. -/
def vollWitMaske : Nat → BitVec 32 :=
  fun _ => BitVec.ofNat 32 0xFFBF

/-- Witness upper files: low halves `9` on core 0, `13` elsewhere. -/
def vollWitOber : Nat → YmmDatei
  | 0 => fun _ => vecJoin (BitVec.ofNat 64 9) (BitVec.ofNat 64 0)
  | _ => fun _ => vecJoin (BitVec.ofNat 64 13) (BitVec.ofNat 64 0)

/-- Witness start machine: shared memory, two saving cores, empty
    buffers, full silicon, baseline readiness. -/
def vollWitStart : VollMaschine :=
  ⟨⟨⟨vollWitMem, vollWitKern, fun _ => [], basisHw,
    fun _ => basisBereit⟩, vollWitOber⟩, vollWitX87, vollWitMaske⟩

/-- Witness XCR0: x87, SSE and AVX enabled. -/
def vollWitXc : Xcr0Bild := ⟨true, true, true⟩

/-- Witness fault inputs: no fault fires. -/
def vollWitF : VollFehlerIn :=
  ⟨false, true, false, false, false, false⟩

/-- The witness machine is well-formed. -/
theorem vollWitStart_wf : VollWf vollWitStart := by
  unfold VollWf
  intro c f _
  cases f <;> rfl

set_option maxRecDepth 10000 in
/-- Witness permissions cover the full footprint, both ways. -/
theorem vollWit_perm (a : Adresse)
    (h : a = vollWitArea0 ∨ a = vollWitArea1) :
    ctxAlle vollWitMem.schreibbar a (vollOffsets true true) = true ∧
      ctxAlle vollWitMem.lesbar a (vollOffsets true true) = true := by
  rcases h with rfl | rfl <;> decide

/-- Witness addresses are canonical. -/
theorem vollWit_kanonisch :
    kanonisch vollWitArea0 = true ∧
      kanonisch vollWitArea1 = true := by
  decide

/-- Witness addresses are save-aligned. -/
theorem vollWit_ausgerichtet :
    xAusgerichtet vollWitArea0 = true ∧
      xAusgerichtet vollWitArea1 = true ∧
      fxAusgerichtet vollWitArea0 = true := by
  decide

/-- Witness XCR0 enables SSE and AVX. -/
theorem vollWit_bereit :
    xcr0SseBereit vollWitXc = true ∧
      xcr0AvxBereit vollWitXc = true := by
  decide

/-- FINIT facts on the witness: reset installs, everything else
    stays, and core 0 already starts from reset. -/
theorem vollWit_finit :
    ((vollFinit vollWitStart 1).x87 1) 0 = x87Reset 0 ∧
      vollHw (vollFinit vollWitStart 1) = vollHw vollWitStart ∧
      (vollFinit vollWitStart 1).maske = vollWitStart.maske ∧
      (vollWitX87 0) 0 = x87Reset 0 := by
  exact ⟨vollFinit_setzt_zurueck _ _ _,
    vollFinit_hw_still _ _, vollFinit_maske_still _ _, rfl⟩

end Gabbro.Grammatik.X86
