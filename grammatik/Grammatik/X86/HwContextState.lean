/-
  File:      Grammatik/X86/HwContextState.lean
  Subject:   Extended FP/vector context state across interrupts and
             context switches on the coherent multicore machine.

  Lane 1247: model FXSAVE/FXRSTOR (legacy 512-byte area: MXCSR/XMM0-15
  plus preserved zero bytes; x87 state has no model in this tree and
  stays an opaque preserved region) and XSAVE/XRSTOR for the
  XCR0-enabled components, as footprint-checked memory accesses on the
  coherent machine (`HwMaschine`/`HwSchritt`, HardwareExecution.lean
  section 11). Reuses `issueByte`/`loadByte`/`flushKern` (TSO),
  `mxcsrReserviertFrei`/`ldmxcsrArchOk` (FpControlHardwareForms),
  `xcr0SseBereit`/`Xcr0Bild` (VectorHardwareProfile) and
  `asyncSchritt`/`asyncMasch` (HwInterrupts) unchanged, never copied.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.HwInterrupts
import Grammatik.X86.FpControlHardwareForms
import Grammatik.X86.VectorHardwareProfile

namespace Gabbro.Grammatik.X86

/-- Snapshot of one core's saved FP/vector state: control word plus
    the full XMM file. x87 state has no model here (opaque region). -/
structure CtxBild where
  mxcsr : MXCSR
  xmm : XmmDatei
  deriving Inhabited

/-! ## 1. Legacy area layout (SDM 325462-093US Vol.2A FXSAVE64 Table 1-42,
    clone-local extract offsets 56665-56698; provenance only).

    Selected 64-bit map: MXCSR at bytes 24-27, MXCSR_MASK at 28-31,
    x87 data at 32-159, XMM0-15 at 160-415 (16 bytes each), reserved
    at 416-463, software-available at 464-511 (the processor never
    writes them: extract offset 56486). Modelled footprint below is
    exactly bytes 24-27 (MXCSR) and 160-415 (XMM0-15); everything else
    is outside the footprint (see CUTS). Alignment: 16-byte operand
    for FXSAVE/FXRSTOR (misaligned destination operand raises #GP:
    offset 56533), 64-byte operand for XSAVE/XRSTOR (offset 15150). -/

/-- FXSAVE area size in bytes (the legacy region). -/
def fxLaenge : Nat := 512

/-- FXSAVE/FXRSTOR operand alignment: 16 bytes. -/
def fxAusricht : Nat := 16

/-- XSAVE/XRSTOR operand alignment: 64 bytes. -/
def xAusricht : Nat := 64

/-- 16-byte alignment check (FXSAVE/FXRSTOR fault gate). -/
def fxAusgerichtet (a : Adresse) : Bool := decide (a.toNat % 16 = 0)

/-- 64-byte alignment check (XSAVE/XRSTOR fault gate). -/
def xAusgerichtet (a : Adresse) : Bool := decide (a.toNat % 64 = 0)

/-- XMM register number in the area (XMM0 at 160, stride 16). -/
def xmmIdx : XmmReg → Nat
  | .xmm0 => 0 | .xmm1 => 1 | .xmm2 => 2 | .xmm3 => 3
  | .xmm4 => 4 | .xmm5 => 5 | .xmm6 => 6 | .xmm7 => 7
  | .xmm8 => 8 | .xmm9 => 9 | .xmm10 => 10 | .xmm11 => 11
  | .xmm12 => 12 | .xmm13 => 13 | .xmm14 => 14 | .xmm15 => 15

/-- Inverse lookup: area slot number to register, if any. -/
def xmmVonIdx : Nat → Option XmmReg
  | 0 => some .xmm0 | 1 => some .xmm1 | 2 => some .xmm2 | 3 => some .xmm3
  | 4 => some .xmm4 | 5 => some .xmm5 | 6 => some .xmm6 | 7 => some .xmm7
  | 8 => some .xmm8 | 9 => some .xmm9 | 10 => some .xmm10 | 11 => some .xmm11
  | 12 => some .xmm12 | 13 => some .xmm13 | 14 => some .xmm14 | 15 => some .xmm15
  | _ => none

/-- Lookup inverts numbering on every register. -/
theorem xmmVonIdx_idx (r : XmmReg) : xmmVonIdx (xmmIdx r) = some r := by
  cases r <;> rfl

/-- Every register number fits the area (16 slots). -/
theorem xmmIdx_klein (r : XmmReg) : xmmIdx r < 16 := by
  cases r <;> decide

/-- One MXCSR image byte: little-endian byte `i` of the zero-extended
    control word (`wortByte`, reused unchanged). -/
def mxcsrByte (w : MXCSR) (i : Nat) : Byte :=
  wortByte (BitVec.ofNat 64 w.toNat) i

/-- Reassemble the control word from four little-endian image bytes. -/
def mxcsrAusBytes (f : Nat → Byte) : MXCSR :=
  BitVec.ofNat 32 ((f 0).toNat + (f 1).toNat * 256 +
    (f 2).toNat * 65536 + (f 3).toNat * 16777216)

/-- MXCSR image round trip (same shape as `bytesWort_wortByte`). -/
theorem mxcsr_rundlauf (w : MXCSR) :
    mxcsrAusBytes (mxcsrByte w) = w := by
  apply BitVec.eq_of_toNat_eq
  unfold mxcsrAusBytes mxcsrByte wortByte
  simp only [BitVec.toNat_ofNat]
  have hw := w.isLt
  omega

/-- Reassembly depends only on the four footprint bytes. -/
theorem mxcsrAusBytes_kongr (f g : Nat → Byte)
    (h : ∀ i, i < 4 → f i = g i) :
    mxcsrAusBytes f = mxcsrAusBytes g := by
  unfold mxcsrAusBytes
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  rw [h0, h1, h2, h3]

/-- The 512-byte area image of a context: MXCSR at 24-27, XMM slot
    bytes at 160-415 (low half then high half via `vLo`/`vHi`,
    reassembled with `vecJoin`); every other offset reads zero
    (x87/mask/reserved/available regions are outside the footprint). -/
def ctxByte (k : FPKontext) (x : XmmDatei) : Nat → Byte := fun i =>
  if i < 24 then BitVec.ofNat 8 0
  else if i < 28 then mxcsrByte k.mxcsr (i - 24)
  else if i < 160 then BitVec.ofNat 8 0
  else if i < 416 then
    match xmmVonIdx ((i - 160) / 16) with
    | some r =>
      if (i - 160) % 16 < 8 then wortByte (vLo (x r)) ((i - 160) % 16)
      else wortByte (vHi (x r)) ((i - 160) % 16 - 8)
    | none => BitVec.ofNat 8 0
  else BitVec.ofNat 8 0

/-- Image at an MXCSR footprint offset is the control byte. -/
theorem ctxByte_mxcsr (k : FPKontext) (x : XmmDatei) (j : Nat)
    (hj : j < 4) :
    ctxByte k x (24 + j) = mxcsrByte k.mxcsr j := by
  unfold ctxByte
  have e1 : ¬ (24 + j < 24) := by omega
  have e2 : 24 + j < 28 := by omega
  have e3 : 24 + j - 24 = j := by omega
  rw [if_neg e1, if_pos e2, e3]

/-- Image at an XMM footprint offset, low half. -/
theorem ctxByte_xmm_lo (k : FPKontext) (x : XmmDatei) (r : XmmReg)
    (j : Nat) (hj : j < 8) :
    ctxByte k x (160 + 16 * xmmIdx r + j) = wortByte (vLo (x r)) j := by
  have hn := xmmIdx_klein r
  have hj16 : j < 16 := by omega
  unfold ctxByte
  have e1 : ¬ (160 + 16 * xmmIdx r + j < 24) := by omega
  have e2 : ¬ (160 + 16 * xmmIdx r + j < 28) := by omega
  have e3 : ¬ (160 + 16 * xmmIdx r + j < 160) := by omega
  have e4 : 160 + 16 * xmmIdx r + j < 416 := by omega
  have e5 : (160 + 16 * xmmIdx r + j - 160) / 16 = xmmIdx r := by omega
  have e6 : (160 + 16 * xmmIdx r + j - 160) % 16 = j := by omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_pos e4, e5, e6]
  simp [xmmVonIdx_idx, hj]

/-- Image at an XMM footprint offset, high half. -/
theorem ctxByte_xmm_hi (k : FPKontext) (x : XmmDatei) (r : XmmReg)
    (j : Nat) (hj : j < 8) :
    ctxByte k x (168 + 16 * xmmIdx r + j) = wortByte (vHi (x r)) j := by
  have e : 168 + 16 * xmmIdx r + j = 160 + 16 * xmmIdx r + (8 + j) := by
    omega
  have hn := xmmIdx_klein r
  rw [e]
  unfold ctxByte
  have e1 : ¬ (160 + 16 * xmmIdx r + (8 + j) < 24) := by omega
  have e2 : ¬ (160 + 16 * xmmIdx r + (8 + j) < 28) := by omega
  have e3 : ¬ (160 + 16 * xmmIdx r + (8 + j) < 160) := by omega
  have e4 : 160 + 16 * xmmIdx r + (8 + j) < 416 := by omega
  have e5 : (160 + 16 * xmmIdx r + (8 + j) - 160) / 16 = xmmIdx r := by
    omega
  have e6 : (160 + 16 * xmmIdx r + (8 + j) - 160) % 16 = 8 + j := by omega
  have e7 : ¬ (8 + j < 8) := by omega
  have e8 : 8 + j - 8 = j := by omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_pos e4, e5, e6]
  simp [xmmVonIdx_idx, e7, e8]

/-- Decode an area image back to a context: MXCSR from 24-27, each
    XMM from its 16-byte slot (low half then high half). -/
def fxDekodiere (f : Nat → Byte) : CtxBild :=
  ⟨mxcsrAusBytes (fun i => f (24 + i)),
   fun r => vecJoin
     (bytesWort (fun j : Fin 8 => f (160 + 16 * xmmIdx r + j.val)))
     (bytesWort (fun j : Fin 8 => f (168 + 16 * xmmIdx r + j.val)))⟩

/-- PURE IDENTITY: decoding the saved image recovers the control word
    and every XMM register. -/
theorem ctxRundlauf_pur (k : FPKontext) (x : XmmDatei) :
    (fxDekodiere (ctxByte k x)).mxcsr = k.mxcsr ∧
      ∀ r : XmmReg, (fxDekodiere (ctxByte k x)).xmm r = x r := by
  refine ⟨?_, ?_⟩
  · unfold fxDekodiere
    simp only
    have h := mxcsrAusBytes_kongr _ _
      (fun i hi => ctxByte_mxcsr k x i hi)
    rw [h]
    exact mxcsr_rundlauf k.mxcsr
  · intro r
    unfold fxDekodiere
    simp only
    have hn := xmmIdx_klein r
    have hlo : (fun j : Fin 8 => ctxByte k x (160 + 16 * xmmIdx r + j.val)) =
        (fun j : Fin 8 => wortByte (vLo (x r)) j.val) := by
      funext j
      exact ctxByte_xmm_lo k x r j.val j.isLt
    have hhi : (fun j : Fin 8 => ctxByte k x (168 + 16 * xmmIdx r + j.val)) =
        (fun j : Fin 8 => wortByte (vHi (x r)) j.val) := by
      funext j
      exact ctxByte_xmm_hi k x r j.val j.isLt
    rw [hlo, hhi, bytesWort_wortByte, bytesWort_wortByte]
    exact vecJoin_split (x r)

/-! ## 2. Footprint and the TSO bridge.

    The modelled footprint is 260 bytes: offsets 24-27 (MXCSR) and
    160-415 (XMM slots). Entries are built by a cons-recursion over an
    explicit offset list, so the forwarding proofs below induct
    directly on it. -/

/-- Modelled footprint offsets: 24-27 then 160-415. -/
def ctxOffsets : List Nat :=
  (List.range 4).map (24 + ·) ++ (List.range 256).map (160 + ·)

/-- Every footprint offset fits well inside the area. -/
theorem ctxOffsets_klein (i : Nat) (h : i ∈ ctxOffsets) : i < 512 := by
  unfold ctxOffsets at h
  simp only [List.mem_append, List.mem_map, List.mem_range] at h
  rcases h with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;> omega

set_option maxRecDepth 10000 in
/-- The footprint has no duplicate offset (elaboration-only depth
    budget, same pattern as the model file's kernel `decide`s). -/
theorem ctxOffsets_nodup : ctxOffsets.Nodup := by decide

/-- MXCSR offsets are in the footprint. -/
theorem ctxOffsets_mxcsr (j : Nat) (hj : j < 4) : 24 + j ∈ ctxOffsets := by
  unfold ctxOffsets
  simp only [List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl ⟨j, hj, rfl⟩

/-- XMM slot offsets are in the footprint. -/
theorem ctxOffsets_xmm (n j : Nat) (hn : n < 16) (hj : j < 16) :
    160 + 16 * n + j ∈ ctxOffsets := by
  unfold ctxOffsets
  simp only [List.mem_append, List.mem_map, List.mem_range]
  exact Or.inr ⟨16 * n + j, by omega, by omega⟩

/-- Footprint addresses stay distinct: `addrOff` is injective below
    512 (same shape as `addrOff_inj8`, reused idea, wider bound). -/
theorem addrOff_inj512 {a : Adresse} {i j : Nat}
    (hi : i < 512) (hj : j < 512)
    (h : addrOff a i = addrOff a j) : i = j := by
  unfold addrOff at h
  have h2 := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_add,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h2
  have ha := a.isLt
  omega

/-- Save entries over an offset list: one buffered byte per offset. -/
def fxEintraegeAux (f : Nat → Byte) (a : Adresse) : List Nat → List TSOEintrag
  | [] => []
  | i :: rest => ⟨addrOff a i, f i⟩ :: fxEintraegeAux f a rest

/-- The save entries of a context at area base `a`. -/
def fxEintraege (k : FPKontext) (x : XmmDatei) (a : Adresse) :
    List TSOEintrag :=
  fxEintraegeAux (ctxByte k x) a ctxOffsets

/-- The youngest match in an appended list comes from the suffix when
    the suffix matches, else from the prefix. -/
theorem neuestens_append (l1 l2 : List TSOEintrag) (a : Adresse) :
    neuestens (l1 ++ l2) a =
      match neuestens l2 a with
      | some v => some v
      | none => neuestens l1 a := by
  induction l1 with
  | nil =>
    cases h : neuestens l2 a <;> simp [h, neuestens]
  | cons e t ih =>
    have h1 : (e :: t) ++ l2 = e :: (t ++ l2) := rfl
    rw [h1]
    simp only [neuestens]
    rw [ih]
    cases h2 : neuestens l2 a <;> cases ht : neuestens t a <;> simp_all

/-- An offset outside the list never matches the entries. -/
theorem neuestens_nicht_enthalten (f : Nat → Byte) (a : Adresse)
    (os : List Nat) (k : Nat)
    (hk : k < 512) (hb : ∀ i ∈ os, i < 512)
    (h : ∀ i ∈ os, i ≠ k) :
    neuestens (fxEintraegeAux f a os) (addrOff a k) = none := by
  induction os with
  | nil => rfl
  | cons i rest ih =>
    have hi : i ≠ k := h i (by simp)
    have hni : addrOff a i ≠ addrOff a k := by
      intro he
      exact hi (addrOff_inj512 (hb i (by simp)) hk he)
    have ihr := ih (fun j hj => hb j (by simp [hj]))
      (fun j hj => h j (by simp [hj]))
    simp only [fxEintraegeAux, neuestens, ihr]
    simp [hni]

/-- Point update of a byte image at one offset. -/
def ctxAktual (g : Nat → Byte) (k : Nat) (v : Byte) : Nat → Byte :=
  fun i => if i = k then v else g i

/-- Fold loaded pairs over a base image, newer pairs shadowing. -/
def ctxFalte : List (Nat × Byte) → (Nat → Byte) → (Nat → Byte)
  | [], g => g
  | p :: rest, g => ctxFalte rest (ctxAktual g p.1 p.2)

/-- Folding pairs whose keys all differ from `j` keeps whatever
    value the accumulator already holds at `j`. -/
theorem ctxFalte_behaelt_allg (bs : List (Nat × Byte)) (g : Nat → Byte)
    (j : Nat) (b : Byte)
    (hg : g j = b) (h : ∀ p ∈ bs, p.1 ≠ j) :
    ctxFalte bs g j = b := by
  induction bs generalizing g with
  | nil =>
    unfold ctxFalte
    exact hg
  | cons p rest ih =>
    have hp : p.1 ≠ j := h p (by simp)
    unfold ctxFalte
    apply ih
    · unfold ctxAktual
      have hne : ¬ (j = p.1) := fun he => hp he.symm
      rw [if_neg hne]
      exact hg
    · exact fun q hq => h q (by simp [hq])

/-- Folding pairs whose keys all differ from `j` keeps the value at
    `j` installed by an earlier update. -/
theorem ctxFalte_behaelt (bs : List (Nat × Byte)) (base : Nat → Byte)
    (j : Nat) (b : Byte)
    (h : ∀ p ∈ bs, p.1 ≠ j) :
    ctxFalte bs (ctxAktual base j b) j = b :=
  ctxFalte_behaelt_allg bs _ j b (by unfold ctxAktual; simp) h

/-- Load the footprint offsets through the TSO view (forwarding
    included): one `(offset, byte)` pair per offset, head-first. -/
def ctxLadeAux (s : TSOZustand) (c : Nat) (a : Adresse) :
    List Nat → Option (List (Nat × Byte))
  | [] => some []
  | i :: rest =>
    match ctxLadeAux s c a rest with
    | none => none
    | some bs =>
      match loadByte s c (addrOff a i) with
      | none => none
      | some b => some ((i, b) :: bs)

/-- Loaded pair keys lie inside the requested offsets. -/
theorem ctxLadeAux_keys (s : TSOZustand) (c : Nat) (a : Adresse)
    (os : List Nat) (bs : List (Nat × Byte))
    (hbs : ctxLadeAux s c a os = some bs) :
    ∀ p ∈ bs, p.1 ∈ os := by
  induction os generalizing bs with
  | nil =>
    simp only [ctxLadeAux] at hbs
    cases hbs
    simp
  | cons j rest ih =>
    simp only [ctxLadeAux] at hbs
    cases hrec : ctxLadeAux s c a rest with
    | none => simp [hrec] at hbs
    | some bs' =>
      cases hld : loadByte s c (addrOff a j) with
      | none => simp [hrec, hld] at hbs
      | some b =>
        simp [hrec, hld] at hbs
        subst hbs
        intro p hp
        have hmem : p = (j, b) ∨ p ∈ bs' := by simpa using hp
        rcases hmem with rfl | hmem'
        · simp
        · have h2 := ih bs' hrec p hmem'
          simp [h2]

/-- A successful footprint load folds back to the loaded image on
    every footprint offset. -/
theorem ctxLade_geladen (s : TSOZustand) (c : Nat) (a : Adresse)
    (f : Nat → Byte) (os : List Nat) :
    ∀ (base : Nat → Byte) (hnd : os.Nodup),
    ∀ (hl : ∀ i ∈ os, loadByte s c (addrOff a i) = some (f i)),
    ∀ (bs : List (Nat × Byte)),
    ctxLadeAux s c a os = some bs → ∀ (i : Nat), i ∈ os →
      ctxFalte bs base i = f i := by
  induction os with
  | nil =>
    intro base _hnd _hl bs hbs i hi
    simp at hi
  | cons j rest ih =>
    intro base hnd hl bs hbs i hi
    have hndj : j ∉ rest := (List.nodup_cons.mp hnd).1
    have hndr : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hjl := hl j (by simp)
    have hrest : ∀ k ∈ rest, loadByte s c (addrOff a k) = some (f k) :=
      fun k hk => hl k (by simp [hk])
    simp only [ctxLadeAux] at hbs
    cases hrec : ctxLadeAux s c a rest with
    | none => simp [hrec] at hbs
    | some bs' =>
      cases hld : loadByte s c (addrOff a j) with
      | none => simp [hrec, hld] at hbs
      | some b =>
        simp [hrec, hld] at hbs
        subst hbs
        have hbj : b = f j := Option.some_inj.mp (hld.symm.trans hjl)
        have hkeys := ctxLadeAux_keys s c a rest bs' hrec
        have hmem : i = j ∨ i ∈ rest := by simpa using hi
        rcases hmem with heq | hir
        · unfold ctxFalte
          rw [heq, hbj]
          exact ctxFalte_behaelt bs' base j (f j)
            (fun p hp => fun heq2 => hndj (heq2 ▸ hkeys p hp))
        · unfold ctxFalte
          exact ih (ctxAktual base j b) hndr hrest bs' hrec i hir

end Gabbro.Grammatik.X86
