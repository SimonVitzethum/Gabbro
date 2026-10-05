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

/-- A footprint offset reads its own entry byte (younger entries for
    other offsets do not shadow it). -/
theorem neuestens_einmal (f : Nat → Byte) (a : Adresse)
    (os : List Nat) (k : Nat) :
    ∀ (hb : ∀ j ∈ os, j < 512) (hk512 : k < 512),
    ∀ (hnd : os.Nodup) (hm : k ∈ os),
    neuestens (fxEintraegeAux f a os) (addrOff a k) = some (f k) := by
  induction os with
  | nil =>
    intro _hb _hk512 _hnd hm
    simp at hm
  | cons i rest ih =>
    intro hb hk512 hnd hm
    have hni : i ∉ rest := (List.nodup_cons.mp hnd).1
    have hmem : k = i ∨ k ∈ rest := by simpa using hm
    rcases hmem with heq | hmr
    · have hmiss : ∀ j ∈ rest, j ≠ k :=
        fun j hj hjeq => hni (heq ▸ (hjeq ▸ hj))
      have hnone := neuestens_nicht_enthalten f a rest k hk512
        (fun j hj => hb j (by simp [hj])) hmiss
      simp only [fxEintraegeAux, neuestens, hnone]
      rw [if_pos (by rw [heq]), heq]
    · have ihr := ih (fun j hj => hb j (by simp [hj])) hk512
        ((List.nodup_cons.mp hnd).2) hmr
      simp only [fxEintraegeAux, neuestens, ihr]

/-- Decoding depends only on the footprint bytes. -/
theorem fxDekodiere_kongr (f g : Nat → Byte)
    (h : ∀ i ∈ ctxOffsets, f i = g i) :
    (fxDekodiere f).mxcsr = (fxDekodiere g).mxcsr ∧
      ∀ r : XmmReg, (fxDekodiere f).xmm r = (fxDekodiere g).xmm r := by
  refine ⟨?_, ?_⟩
  · unfold fxDekodiere
    simp only
    apply mxcsrAusBytes_kongr
    intro i hi
    exact h (24 + i) (ctxOffsets_mxcsr i hi)
  · intro r
    unfold fxDekodiere
    simp only
    have hn := xmmIdx_klein r
    have hlo : (fun j : Fin 8 => f (160 + 16 * xmmIdx r + j.val)) =
        (fun j : Fin 8 => g (160 + 16 * xmmIdx r + j.val)) := by
      funext j
      have hj16 : j.val < 16 := by have h8 := j.isLt; omega
      exact h _ (ctxOffsets_xmm (xmmIdx r) j.val hn hj16)
    have hhi : (fun j : Fin 8 => f (168 + 16 * xmmIdx r + j.val)) =
        (fun j : Fin 8 => g (168 + 16 * xmmIdx r + j.val)) := by
      funext j
      have hj16 : 8 + j.val < 16 := by have := j.isLt; omega
      have e : 168 + 16 * xmmIdx r + j.val =
          160 + 16 * xmmIdx r + (8 + j.val) := by omega
      rw [e]
      exact h _ (ctxOffsets_xmm (xmmIdx r) (8 + j.val) hn hj16)
    rw [hlo, hhi]

/-- Permission fold over the footprint: every accessed byte must pass. -/
def ctxAlle (p : Adresse → Bool) (a : Adresse) : List Nat → Bool
  | [] => true
  | i :: rest => p (addrOff a i) && ctxAlle p a rest

/-- An issue fold changes no memory at all (only buffers grow). -/
theorem issueListe_mem_still (s s' : TSOZustand) (c : Nat)
    (l : List TSOEintrag) (h : issueListe s c l = some s') :
    s'.mem = s.mem := by
  induction l generalizing s s' with
  | nil =>
    simp [issueListe] at h
    subst h
    rfl
  | cons e rest ih =>
    unfold issueListe at h
    cases h1 : issueByte s c e.addr e.wert with
    | none => rw [h1] at h; cases h
    | some s1 =>
      rw [h1] at h
      have hm : s1.mem = s.mem := by
        unfold issueByte at h1
        by_cases hc : s.mem.schreibbar e.addr = true
        · rw [if_pos hc] at h1
          cases h1
          rfl
        · rw [if_neg hc] at h1
          cases h1
      rw [ih s1 s' h]
      exact hm

/-- The permission fold yields each offset's permission. -/
theorem ctxAlle_holt (p : Adresse → Bool) (a : Adresse) (os : List Nat)
    (i : Nat) (hi : i ∈ os) (h : ctxAlle p a os = true) :
    p (addrOff a i) = true := by
  induction os with
  | nil => simp at hi
  | cons j rest ih =>
    unfold ctxAlle at h
    simp only [Bool.and_eq_true] at h
    have hmem : i = j ∨ i ∈ rest := by simpa using hi
    rcases hmem with rfl | hir
    · exact h.1
    · exact ih hir h.2

/-- `setTso` keeps every core's data. -/
theorem setTso_kerne (m : HwMaschine) (s : TSOZustand) (c : Nat) :
    (setTso m s).kerne c = m.kerne c := rfl

/-- Re-embedded core answers the installed control word. -/
theorem setKernDaten_fp (m : HwMaschine) (c : Nat) (k : HwKern) :
    ((setKernDaten m c k).kerne c).fp = k.fp := by
  unfold setKernDaten
  simp

/-- Re-embedded core answers the installed XMM file. -/
theorem setKernDaten_xmm (m : HwMaschine) (c : Nat) (k : HwKern) :
    ((setKernDaten m c k).kerne c).xmm = k.xmm := by
  unfold setKernDaten
  simp

/-- FORWARDING AT SAVE: after a successful save, every footprint
    offset loads the saved image byte through the owner's buffer. -/
theorem ctxWeiterleitung_gespeichert (m : HwMaschine) (c : Nat)
    (a : Adresse) (s1' : TSOZustand)
    (hs : issueListe (tsoAnsicht m) c
      (fxEintraege (m.kerne c).fp (m.kerne c).xmm a) = some s1')
    (hles : ctxAlle m.mem.lesbar a ctxOffsets = true)
    (i : Nat) (hi : i ∈ ctxOffsets) :
    loadByte s1' c (addrOff a i) =
      some (ctxByte (m.kerne c).fp (m.kerne c).xmm i) := by
  have hbuf := issueListe_haengt_an (tsoAnsicht m) s1' c _ hs
  have hmem : s1'.mem = (tsoAnsicht m).mem :=
    issueListe_mem_still _ _ _ _ hs
  have hlesbar : s1'.mem.lesbar (addrOff a i) = true := by
    rw [hmem]
    exact ctxAlle_holt m.mem.lesbar a ctxOffsets i hi hles
  have hneu : neuestens (s1'.puffer c) (addrOff a i) =
      some (ctxByte (m.kerne c).fp (m.kerne c).xmm i) := by
    have he := neuestens_einmal (ctxByte (m.kerne c).fp (m.kerne c).xmm)
      a ctxOffsets i (fun j hj => ctxOffsets_klein j hj)
      (ctxOffsets_klein i hi) ctxOffsets_nodup hi
    have hentries : fxEintraege (m.kerne c).fp (m.kerne c).xmm a =
        fxEintraegeAux (ctxByte (m.kerne c).fp (m.kerne c).xmm) a
          ctxOffsets := rfl
    rw [hbuf, hentries, neuestens_append, he]
  unfold loadByte
  rw [if_pos hlesbar, hneu]

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

/-! ## 3. Machine save: footprint-checked buffered store.

    `ctxSpeichern` reads the acting core's FP/vector state and issues
    one buffered byte per footprint offset through `issueListe`
    (never a canonical word effect). Misalignment is `.fehlerGP`;
    a missing write permission is `.verweigert`. -/

/-- Machine-level context outcomes: successor, refusal, #GP, #UD. -/
inductive CtxAusgang where
  | weiter : HwMaschine → CtxAusgang
  | verweigert : CtxAusgang
  | fehlerGP : CtxAusgang
  | fehlerUD : CtxAusgang

/-- One context save on core `c` at area base `a`: alignment gate,
    write-permission gate over the footprint, then the buffered
    byte-issue fold. -/
def ctxSpeichern (m : HwMaschine) (c : Nat) (a : Adresse) : CtxAusgang :=
  if !fxAusgerichtet a then .fehlerGP
  else if !ctxAlle m.mem.schreibbar a ctxOffsets then .verweigert
  else match issueListe (tsoAnsicht m) c
      (fxEintraege (m.kerne c).fp (m.kerne c).xmm a) with
  | none => .verweigert
  | some s' => .weiter (setTso m s')

/-- Success shape: a successful save is a successful issue fold. -/
theorem ctxSpeichern_erfolg (m : HwMaschine) (c : Nat) (a : Adresse)
    (m' : HwMaschine)
    (h : ctxSpeichern m c a = .weiter m') :
    ∃ s' : TSOZustand,
      issueListe (tsoAnsicht m) c
        (fxEintraege (m.kerne c).fp (m.kerne c).xmm a) = some s' ∧
      m' = setTso m s' := by
  unfold ctxSpeichern at h
  cases ha : fxAusgerichtet a with
  | false =>
    simp [ha] at h
  | true =>
    cases hp : ctxAlle m.mem.schreibbar a ctxOffsets with
    | false =>
      simp [ha, hp] at h
    | true =>
      simp [ha, hp] at h
      cases hs : issueListe (tsoAnsicht m) c
          (fxEintraege (m.kerne c).fp (m.kerne c).xmm a) with
      | none =>
        rw [hs] at h
        cases h
      | some s' =>
        -- NOTE: `cases hs : e` generalizes the goal over `e`, so the
        -- goal here reads `some s'` where the statement has the fold.
        have hm : setTso m s' = m' := by simpa [hs] using h
        exact ⟨s', rfl, hm.symm⟩

/-- SAVE GOES THROUGH THE TSO BUFFER: the acting core's buffer grows
    by exactly the footprint entries. -/
theorem ctxSpeichern_puffer (m : HwMaschine) (c : Nat) (a : Adresse)
    (m' : HwMaschine)
    (h : ctxSpeichern m c a = .weiter m') :
    m'.puffer c = m.puffer c ++
      fxEintraege (m.kerne c).fp (m.kerne c).xmm a := by
  obtain ⟨s', hs, rfl⟩ := ctxSpeichern_erfolg m c a m' h
  exact issueListe_haengt_an (tsoAnsicht m) s' c _ hs

/-- A save changes no canonical byte (buffer only). -/
theorem ctxSpeichern_kein_speicher (m : HwMaschine) (c : Nat)
    (a : Adresse) (m' : HwMaschine)
    (h : ctxSpeichern m c a = .weiter m') (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x := by
  obtain ⟨s', hs, rfl⟩ := ctxSpeichern_erfolg m c a m' h
  exact issueListe_kein_speicher (tsoAnsicht m) s' c _ hs x

/-- A save preserves well-formedness (profiles untouched). -/
theorem ctxSpeichern_wf (m : HwMaschine) (c : Nat) (a : Adresse)
    (hwf : HwWf m) (m' : HwMaschine)
    (h : ctxSpeichern m c a = .weiter m') : HwWf m' := by
  obtain ⟨s', _, rfl⟩ := ctxSpeichern_erfolg m c a m' h
  exact setTso_wf m s' hwf

/-- Misaligned save area faults with #GP (SDM: a misaligned operand
    raises #GP; extract offset 56533). -/
theorem ctxSpeichern_fehlerGP_falsch_ausgerichtet (m : HwMaschine)
    (c : Nat) (a : Adresse)
    (h : fxAusgerichtet a = false) :
    ctxSpeichern m c a = .fehlerGP := by
  unfold ctxSpeichern
  simp [h]

/-- A missing write permission refuses the whole save. -/
theorem ctxSpeichern_verweigert_ohne_schreibrecht (m : HwMaschine)
    (c : Nat) (a : Adresse)
    (h1 : fxAusgerichtet a = true)
    (h2 : ctxAlle m.mem.schreibbar a ctxOffsets = false) :
    ctxSpeichern m c a = .verweigert := by
  unfold ctxSpeichern
  simp [h1, h2]

/-! ## 4. Machine restore and the save/restore round trip.

    `ctxWiederherstellen` loads the footprint through the TSO view
    (forwarding included), reassembles the control word and the XMM
    file, and installs them on the acting core, keeping
    registers/flags/RIP. A set reserved MXCSR bit (SDM: writing a 1
    in a reserved bit from the image raises #GP; extract offset 56379)
    faults with `.fehlerGP`. -/

/-- The zero base image a restore folds loaded bytes over. -/
def ctxNull : Nat → Byte := fun _ => BitVec.ofNat 8 0

/-- One context restore on core `c` from area base `a`. -/
def ctxWiederherstellen (m : HwMaschine) (c : Nat)
    (a : Adresse) : CtxAusgang :=
  if !fxAusgerichtet a then .fehlerGP
  else if !ctxAlle m.mem.lesbar a ctxOffsets then .verweigert
  else match ctxLadeAux (tsoAnsicht m) c a ctxOffsets with
  | none => .verweigert
  | some bs =>
    if !mxcsrReserviertFrei
        (mxcsrAusBytes (fun i => ctxFalte bs ctxNull (24 + i))) then
      .fehlerGP
    else .weiter (setKernDaten m c ⟨(m.kerne c).register,
      (m.kerne c).flags, (m.kerne c).rip,
      (fxDekodiere (ctxFalte bs ctxNull)).xmm,
      ⟨mxcsrAusBytes (fun i => ctxFalte bs ctxNull (24 + i))⟩⟩)

/-- Success shape: a successful restore is a successful footprint
    load with a reserved-free control word. -/
theorem ctxWiederherstellen_erfolg (m : HwMaschine) (c : Nat)
    (a : Adresse) (m' : HwMaschine)
    (h : ctxWiederherstellen m c a = .weiter m') :
    ∃ bs : List (Nat × Byte),
      ctxLadeAux (tsoAnsicht m) c a ctxOffsets = some bs ∧
      m' = setKernDaten m c ⟨(m.kerne c).register,
        (m.kerne c).flags, (m.kerne c).rip,
        (fxDekodiere (ctxFalte bs ctxNull)).xmm,
        ⟨mxcsrAusBytes
          (fun i => ctxFalte bs ctxNull (24 + i))⟩⟩ := by
  unfold ctxWiederherstellen at h
  cases ha : fxAusgerichtet a with
  | false =>
    simp [ha] at h
  | true =>
    cases hp : ctxAlle m.mem.lesbar a ctxOffsets with
    | false =>
      simp [ha, hp] at h
    | true =>
      simp [ha, hp] at h
      cases hbs : ctxLadeAux (tsoAnsicht m) c a ctxOffsets with
      | none =>
        rw [hbs] at h
        cases h
      | some bs =>
        -- NOTE: `cases hbs : e` generalizes the goal over `e`.
        cases hw : mxcsrReserviertFrei
            (mxcsrAusBytes (fun i => ctxFalte bs ctxNull (24 + i))) with
        | false =>
          simp [hbs, hw] at h
        | true =>
          simp [hbs, hw] at h
          cases h
          exact ⟨bs, rfl, rfl⟩

/-- SAVE THEN RESTORE IS THE IDENTITY on the saved components:
    restoring a just-saved area on the same core recovers the control
    word and every XMM register. Needs read permission beside the
    save's write permission (the restore observes through `loadByte`,
    which checks readability). -/
theorem ctxRundlauf_maschine (m : HwMaschine) (c : Nat) (a : Adresse)
    (m1 m2 : HwMaschine)
    (hles : ctxAlle m.mem.lesbar a ctxOffsets = true)
    (h1 : ctxSpeichern m c a = .weiter m1)
    (h2 : ctxWiederherstellen m1 c a = .weiter m2) :
    (m2.kerne c).fp = (m.kerne c).fp ∧
      ∀ r : XmmReg, (m2.kerne c).xmm r = (m.kerne c).xmm r := by
  obtain ⟨s1', hs1, rfl⟩ := ctxSpeichern_erfolg m c a m1 h1
  obtain ⟨bs, hbs, rfl⟩ :=
    ctxWiederherstellen_erfolg (setTso m s1') c a m2 h2
  have hsicht : tsoAnsicht (setTso m s1') = s1' := setTso_ansicht m s1'
  rw [hsicht] at hbs
  have hloads : ∀ i ∈ ctxOffsets,
      loadByte s1' c (addrOff a i) =
        some (ctxByte (m.kerne c).fp (m.kerne c).xmm i) := by
    intro i hi
    exact ctxWeiterleitung_gespeichert m c a s1' hs1 hles i hi
  have hagree : ∀ i ∈ ctxOffsets,
      ctxFalte bs ctxNull i =
        ctxByte (m.kerne c).fp (m.kerne c).xmm i := by
    intro i hi
    exact ctxLade_geladen s1' c a (ctxByte (m.kerne c).fp (m.kerne c).xmm)
      ctxOffsets ctxNull ctxOffsets_nodup hloads bs hbs i hi
  have hkong := fxDekodiere_kongr (ctxFalte bs ctxNull)
    (ctxByte (m.kerne c).fp (m.kerne c).xmm)
    (fun i hi => hagree i hi)
  have hpure := ctxRundlauf_pur (m.kerne c).fp (m.kerne c).xmm
  have hw : mxcsrAusBytes (fun i => ctxFalte bs ctxNull (24 + i)) =
      ((m.kerne c).fp).mxcsr := by
    have e1 : mxcsrAusBytes (fun i => ctxFalte bs ctxNull (24 + i)) =
        (fxDekodiere (ctxFalte bs ctxNull)).mxcsr := rfl
    rw [e1, hkong.1]
    exact hpure.1
  refine ⟨?_, ?_⟩
  · have hfp : ((setKernDaten (setTso m s1') c
        ⟨((setTso m s1').kerne c).register,
          ((setTso m s1').kerne c).flags, ((setTso m s1').kerne c).rip,
          (fxDekodiere (ctxFalte bs ctxNull)).xmm,
          ⟨mxcsrAusBytes
            (fun i => ctxFalte bs ctxNull (24 + i))⟩⟩).kerne c).fp =
        ⟨mxcsrAusBytes (fun i => ctxFalte bs ctxNull (24 + i))⟩ :=
      setKernDaten_fp _ _ _
    rw [hfp, hw]
  · intro r
    have hxmm : ((setKernDaten (setTso m s1') c
        ⟨((setTso m s1').kerne c).register,
          ((setTso m s1').kerne c).flags, ((setTso m s1').kerne c).rip,
          (fxDekodiere (ctxFalte bs ctxNull)).xmm,
          ⟨mxcsrAusBytes
            (fun i => ctxFalte bs ctxNull (24 + i))⟩⟩).kerne c).xmm r =
        (fxDekodiere (ctxFalte bs ctxNull)).xmm r := by
      rw [setKernDaten_xmm]
    rw [hxmm, hkong.2 r]
    exact hpure.2 r

/-- A restore preserves well-formedness (profiles untouched). -/
theorem ctxWiederherstellen_wf (m : HwMaschine) (c : Nat) (a : Adresse)
    (hwf : HwWf m) (m' : HwMaschine)
    (h : ctxWiederherstellen m c a = .weiter m') : HwWf m' := by
  obtain ⟨bs, _, rfl⟩ := ctxWiederherstellen_erfolg m c a m' h
  exact setKernDaten_wf m c _ hwf

/-- Misaligned restore area faults with #GP. -/
theorem ctxWiederherstellen_fehlerGP_falsch_ausgerichtet
    (m : HwMaschine) (c : Nat) (a : Adresse)
    (h : fxAusgerichtet a = false) :
    ctxWiederherstellen m c a = .fehlerGP := by
  unfold ctxWiederherstellen
  simp [h]

/-- A missing read permission refuses the whole restore. -/
theorem ctxWiederherstellen_verweigert_ohne_leserecht (m : HwMaschine)
    (c : Nat) (a : Adresse)
    (h1 : fxAusgerichtet a = true)
    (h2 : ctxAlle m.mem.lesbar a ctxOffsets = false) :
    ctxWiederherstellen m c a = .verweigert := by
  unfold ctxWiederherstellen
  simp [h1, h2]

/-- A reserved MXCSR bit in the image faults with #GP on restore
    (SDM FXRSTOR/LDMXCSR: attempting to set reserved MXCSR bits
    raises #GP; extract offsets 56403, 62467). This is the accepted
    `ldmxcsrArchOk` refusal, lifted to the area restore. -/
theorem ctxWiederherstellen_fehlerGP_reserviert (m : HwMaschine)
    (c : Nat) (a : Adresse)
    (h1 : fxAusgerichtet a = true)
    (h2 : ctxAlle m.mem.lesbar a ctxOffsets = true)
    (bs : List (Nat × Byte))
    (h3 : ctxLadeAux (tsoAnsicht m) c a ctxOffsets = some bs)
    (h4 : 65536 ≤ (mxcsrAusBytes
      (fun i => ctxFalte bs ctxNull (24 + i))).toNat) :
    ctxWiederherstellen m c a = .fehlerGP := by
  unfold ctxWiederherstellen
  simp [h1, h2, h3]
  have hres : mxcsrReserviertFrei
      (mxcsrAusBytes (fun i => ctxFalte bs ctxNull (24 + i))) = false :=
    mxcsrReserviertFrei_verweigert _ h4
  simp [hres]

/-- AGREEMENT: the restore's reserved-bit #GP coincides with the
    accepted architectural load refusal `ldmxcsrArchOk`. -/
theorem ctxRestore_stimmt_ldmxcsr_ueberein (p : MxcsrProfil) (w : MXCSR)
    (h : 65536 ≤ w.toNat) :
    ldmxcsrArchOk p w = false :=
  ldmxcsrArchOk_reserviert_verweigert p w h

/-! ## 5. XSAVE/XRSTOR for the XCR0-enabled components.

    RFBM is XCR0 AND the request mask (SDM XSAVE: component `i` is
    saved iff RFBM[i] = 1; MXCSR/MXCSR_MASK belong to component 1
    (SSE); extract offsets 13928, 13956). The tree models the SSE
    family (MXCSR + XMM0-15); readiness reuses `xcr0SseBereit`
    unchanged. XSAVE/XRSTOR run the SAME legacy image path where the
    XCR0 side is ready and SSE is requested, need 64-byte alignment
    (misaligned XSAVE operand raises #GP; extract offset 13950), and
    refuse with #UD where XCR0 SSE readiness is missing (mirroring
    `stepVectorHw_ohne_xcr0`) or with `.verweigert` where the request
    names no modelled component (no silent no-op). The XSAVE header
    and the extended region are outside the footprint (see CUTS). -/

/-- One XSAVE on core `c` at area base `a`: XCR0 gate, request gate,
    64-byte alignment gate, then the shared save path. -/
def ctxXSave (m : HwMaschine) (c : Nat) (a : Adresse)
    (x : Xcr0Bild) (frageSse : Bool) : CtxAusgang :=
  if !xcr0SseBereit x then .fehlerUD
  else if !frageSse then .verweigert
  else if !xAusgerichtet a then .fehlerGP
  else ctxSpeichern m c a

/-- One XRSTOR: the same gates, then the shared restore path
    (including its reserved-bit #GP). -/
def ctxXRstor (m : HwMaschine) (c : Nat) (a : Adresse)
    (x : Xcr0Bild) (frageSse : Bool) : CtxAusgang :=
  if !xcr0SseBereit x then .fehlerUD
  else if !frageSse then .verweigert
  else if !xAusgerichtet a then .fehlerGP
  else ctxWiederherstellen m c a

/-- A successful XSAVE is a successful shared save. -/
theorem ctxXSave_weiter (m : HwMaschine) (c : Nat) (a : Adresse)
    (x : Xcr0Bild) (frageSse : Bool) (m' : HwMaschine)
    (h : ctxXSave m c a x frageSse = .weiter m') :
    ctxSpeichern m c a = .weiter m' := by
  unfold ctxXSave at h
  cases hx' : xcr0SseBereit x with
  | false => simp [hx'] at h
  | true =>
    cases hq' : frageSse with
    | false => simp [hx', hq'] at h
    | true =>
      cases hal' : xAusgerichtet a with
      | false => simp [hx', hq', hal'] at h
      | true =>
        simp [hx', hq', hal'] at h
        exact h

/-- A successful XRSTOR is a successful shared restore. -/
theorem ctxXRstor_weiter (m : HwMaschine) (c : Nat) (a : Adresse)
    (x : Xcr0Bild) (frageSse : Bool) (m' : HwMaschine)
    (h : ctxXRstor m c a x frageSse = .weiter m') :
    ctxWiederherstellen m c a = .weiter m' := by
  unfold ctxXRstor at h
  cases hx' : xcr0SseBereit x with
  | false => simp [hx'] at h
  | true =>
    cases hq' : frageSse with
    | false => simp [hx', hq'] at h
    | true =>
      cases hal' : xAusgerichtet a with
      | false => simp [hx', hq', hal'] at h
      | true =>
        simp [hx', hq', hal'] at h
        exact h

/-- SHARED LAYOUT: under admitted gates XSAVE is the FXSAVE path
    (same legacy bytes for the enabled SSE component). -/
theorem ctxXSave_ist_fxSave (m : HwMaschine) (c : Nat) (a : Adresse)
    (x : Xcr0Bild) (frageSse : Bool)
    (hx : xcr0SseBereit x = true) (hq : frageSse = true)
    (hxa : xAusgerichtet a = true) :
    ctxXSave m c a x frageSse = ctxSpeichern m c a := by
  unfold ctxXSave
  simp [hx, hq, hxa]

/-- SHARED LAYOUT, restore direction. -/
theorem ctxXRstor_ist_fxRstor (m : HwMaschine) (c : Nat) (a : Adresse)
    (x : Xcr0Bild) (frageSse : Bool)
    (hx : xcr0SseBereit x = true) (hq : frageSse = true)
    (hxa : xAusgerichtet a = true) :
    ctxXRstor m c a x frageSse = ctxWiederherstellen m c a := by
  unfold ctxXRstor
  simp [hx, hq, hxa]

/-- 64-byte alignment implies the 16-byte legacy alignment. -/
theorem xAusgerichtet_impliziert_fxAusgerichtet (a : Adresse)
    (h : xAusgerichtet a = true) :
    fxAusgerichtet a = true := by
  have h64 : a.toNat % 64 = 0 := of_decide_eq_true h
  have h16 : a.toNat % 16 = 0 := by omega
  show decide (a.toNat % 16 = 0) = true
  simp [h16]

/-- Without XCR0 SSE readiness XSAVE faults with #UD. -/
theorem ctxXSave_fehlerUD_ohne_xcr0 (m : HwMaschine) (c : Nat)
    (a : Adresse) (x : Xcr0Bild) (frageSse : Bool)
    (h : xcr0SseBereit x = false) :
    ctxXSave m c a x frageSse = .fehlerUD := by
  unfold ctxXSave
  simp [h]

/-- Without XCR0 SSE readiness XRSTOR faults with #UD. -/
theorem ctxXRstor_fehlerUD_ohne_xcr0 (m : HwMaschine) (c : Nat)
    (a : Adresse) (x : Xcr0Bild) (frageSse : Bool)
    (h : xcr0SseBereit x = false) :
    ctxXRstor m c a x frageSse = .fehlerUD := by
  unfold ctxXRstor
  simp [h]

/-- A request naming no modelled component is refused, never
    silently empty. -/
theorem ctxXSave_verweigert_ohne_anfrage (m : HwMaschine) (c : Nat)
    (a : Adresse) (x : Xcr0Bild)
    (hx : xcr0SseBereit x = true) (hq : frageSse = false) :
    ctxXSave m c a x frageSse = .verweigert := by
  unfold ctxXSave
  simp [hx, hq]

/-- Misaligned XSAVE area faults with #GP. -/
theorem ctxXSave_fehlerGP_falsch_ausgerichtet (m : HwMaschine)
    (c : Nat) (a : Adresse) (x : Xcr0Bild) (frageSse : Bool)
    (hx : xcr0SseBereit x = true) (hq : frageSse = true)
    (h : xAusgerichtet a = false) :
    ctxXSave m c a x frageSse = .fehlerGP := by
  unfold ctxXSave
  simp [hx, hq, h]

/-- XSAVE preserves well-formedness (shared path). -/
theorem ctxXSave_wf (m : HwMaschine) (c : Nat) (a : Adresse)
    (x : Xcr0Bild) (frageSse : Bool)
    (hwf : HwWf m) (m' : HwMaschine)
    (h : ctxXSave m c a x frageSse = .weiter m') : HwWf m' :=
  ctxSpeichern_wf m c a hwf m' (ctxXSave_weiter m c a x frageSse m' h)

/-- XRSTOR preserves well-formedness (shared path). -/
theorem ctxXRstor_wf (m : HwMaschine) (c : Nat) (a : Adresse)
    (x : Xcr0Bild) (frageSse : Bool)
    (hwf : HwWf m) (m' : HwMaschine)
    (h : ctxXRstor m c a x frageSse = .weiter m') : HwWf m' :=
  ctxWiederherstellen_wf m c a hwf m'
    (ctxXRstor_weiter m c a x frageSse m' h)

/-- XSAVE goes through the TSO buffer (shared path). -/
theorem ctxXSave_puffer (m : HwMaschine) (c : Nat) (a : Adresse)
    (x : Xcr0Bild) (frageSse : Bool) (m' : HwMaschine)
    (h : ctxXSave m c a x frageSse = .weiter m') :
    m'.puffer c = m.puffer c ++
      fxEintraege (m.kerne c).fp (m.kerne c).xmm a :=
  ctxSpeichern_puffer m c a m' (ctxXSave_weiter m c a x frageSse m' h)

/-- XSAVE/RESTORE ROUND TRIP under one admitted XCR0 mask. -/
theorem ctxXRundlauf_maschine (m : HwMaschine) (c : Nat) (a : Adresse)
    (x : Xcr0Bild) (frageSse : Bool) (m1 m2 : HwMaschine)
    (hles : ctxAlle m.mem.lesbar a ctxOffsets = true)
    (h1 : ctxXSave m c a x frageSse = .weiter m1)
    (h2 : ctxXRstor m1 c a x frageSse = .weiter m2) :
    (m2.kerne c).fp = (m.kerne c).fp ∧
      ∀ r : XmmReg, (m2.kerne c).xmm r = (m.kerne c).xmm r :=
  ctxRundlauf_maschine m c a m1 m2 hles
    (ctxXSave_weiter m c a x frageSse m1 h1)
    (ctxXRstor_weiter m1 c a x frageSse m2 h2)

/-! ## 6. Handlers and context switches preserve FP/vector state.

    Delivery (`asyncMasch`, HwInterrupts) copies the interrupted
    core's XMM file and FP context untouched into the handler-entry
    machine; buffers are untouched too (`asyncMasch_puffer_still`).
    A handler that saves the entry image and restores it before exit
    therefore recovers the interrupted state exactly (pure identity
    from §1); what the handler runs between save and restore is user
    logic outside this model (see CUTS). The same holds for an OS
    context switch: the outgoing image decodes back to the outgoing
    state, so switching images is lossless both ways. -/

/-- Delivery keeps the interrupted core's control word. -/
theorem asyncMasch_fp_still (m : HwMaschine) (c : Nat) (g : IdtTor)
    (q : LieferAnfrage) (rsp : Wort) (m2 : Speicher) :
    ((asyncMasch m c g q rsp m2).kerne c).fp = (m.kerne c).fp := by
  simp [asyncMasch]

/-- Delivery keeps the interrupted core's XMM file. -/
theorem asyncMasch_xmm_still (m : HwMaschine) (c : Nat) (g : IdtTor)
    (q : LieferAnfrage) (rsp : Wort) (m2 : Speicher) (r : XmmReg) :
    ((asyncMasch m c g q rsp m2).kerne c).xmm r =
      (m.kerne c).xmm r := by
  simp [asyncMasch]

/-- HANDLER PRESERVATION: delivering an interrupt and then saving
    and restoring the entry image recovers the interrupted core's
    FP/vector state exactly. -/
theorem handlerErhaeltKontext (m : HwMaschine) (c : Nat) (g : IdtTor)
    (q : LieferAnfrage) (rsp : Wort) (m2 : Speicher) :
    (fxDekodiere (ctxByte ((asyncMasch m c g q rsp m2).kerne c).fp
      ((asyncMasch m c g q rsp m2).kerne c).xmm)).mxcsr =
      ((m.kerne c).fp).mxcsr ∧
    ∀ r : XmmReg, (fxDekodiere (ctxByte
      ((asyncMasch m c g q rsp m2).kerne c).fp
      ((asyncMasch m c g q rsp m2).kerne c).xmm)).xmm r =
      ((m.kerne c).xmm) r := by
  have hfp0 : ((asyncMasch m c g q rsp m2).kerne c).fp =
      (m.kerne c).fp :=
    asyncMasch_fp_still m c g q rsp m2
  have hxx : ((asyncMasch m c g q rsp m2).kerne c).xmm =
      (m.kerne c).xmm :=
    funext (fun r => asyncMasch_xmm_still m c g q rsp m2 r)
  rw [hfp0, hxx]
  exact ctxRundlauf_pur (m.kerne c).fp (m.kerne c).xmm

/-- CONTEXT SWITCH: the outgoing image decodes back to the outgoing
    state and an incoming image decodes to the incoming state, so
    switching images is lossless both ways. Installing the decoded
    state on a core is the restore path (§4). -/
theorem wechselStelltHer (kAlt kNeu : FPKontext)
    (xAlt xNeu : XmmDatei) :
    (fxDekodiere (ctxByte kAlt xAlt)).mxcsr = kAlt.mxcsr ∧
    (∀ r : XmmReg, (fxDekodiere (ctxByte kAlt xAlt)).xmm r = xAlt r) ∧
    (fxDekodiere (ctxByte kNeu xNeu)).mxcsr = kNeu.mxcsr ∧
    (∀ r : XmmReg, (fxDekodiere (ctxByte kNeu xNeu)).xmm r = xNeu r) := by
  exact ⟨(ctxRundlauf_pur kAlt xAlt).1, (ctxRundlauf_pur kAlt xAlt).2,
    (ctxRundlauf_pur kNeu xNeu).1, (ctxRundlauf_pur kNeu xNeu).2⟩

/-! ## 7. Family events, step relation, and the `HwAdapter` plug.

    `CtxSchritt` runs the four request shapes through their checked
    computable steps and carries the shared TSO byte legs unchanged;
    refusals are self-loops tied to computed refusal outcomes (never
    silent). `adapterContext` instantiates the §11 `HwAdapter`
    interface for the request events. -/

/-- Observable family events on the coherent machine. -/
inductive CtxEreignis where
  | fxsaveReq : Nat → Adresse → CtxEreignis
  | fxrstorReq : Nat → Adresse → CtxEreignis
  | xsaveReq : Nat → Adresse → Xcr0Bild → Bool → CtxEreignis
  | xrstorReq : Nat → Adresse → Xcr0Bild → Bool → CtxEreignis
  | leseBeob : Nat → Adresse → Byte → CtxEreignis
  | schreibAusgabe : Nat → Adresse → Byte → CtxEreignis
  | spülung : Nat → TSOEintrag → CtxEreignis
  | verweigert : Nat → CtxEreignis
  deriving DecidableEq, Repr

/-- Project an outcome to an adapter successor. -/
def ctxOpt (o : CtxAusgang) : Option HwMaschine :=
  match o with
  | .weiter m' => some m'
  | _ => none

/-- Family step relation: checked requests plus the shared TSO legs
    plus outcome-tied refusals. -/
inductive CtxSchritt : HwMaschine → HwMaschine → CtxEreignis → Prop where
  | fxsave {m m' : HwMaschine} (c : Nat) (a : Adresse)
      (h : ctxSpeichern m c a = .weiter m') :
      CtxSchritt m m' (.fxsaveReq c a)
  | fxrstor {m m' : HwMaschine} (c : Nat) (a : Adresse)
      (h : ctxWiederherstellen m c a = .weiter m') :
      CtxSchritt m m' (.fxrstorReq c a)
  | xsave {m m' : HwMaschine} (c : Nat) (a : Adresse)
      (x : Xcr0Bild) (q : Bool)
      (h : ctxXSave m c a x q = .weiter m') :
      CtxSchritt m m' (.xsaveReq c a x q)
  | xrstor {m m' : HwMaschine} (c : Nat) (a : Adresse)
      (x : Xcr0Bild) (q : Bool)
      (h : ctxXRstor m c a x q = .weiter m') :
      CtxSchritt m m' (.xrstorReq c a x q)
  | lade {m : HwMaschine} (c : Nat) (a : Adresse) (v : Byte)
      (h : loadByte (tsoAnsicht m) c a = some v) :
      CtxSchritt m m (.leseBeob c a v)
  | gibAus {m : HwMaschine} (c : Nat) (a : Adresse) (v : Byte)
      (s' : TSOZustand)
      (h : issueByte (tsoAnsicht m) c a v = some s') :
      CtxSchritt m (setTso m s') (.schreibAusgabe c a v)
  | spüle {m : HwMaschine} (c : Nat) (e : TSOEintrag)
      (s' : TSOZustand)
      (h : flushKern (tsoAnsicht m) c = some s')
      (hkopf : (m.puffer c).head? = some e) :
      CtxSchritt m (setTso m s') (.spülung c e)
  | fehlerGPsave {m : HwMaschine} (c : Nat) (a : Adresse)
      (h : ctxSpeichern m c a = .fehlerGP) :
      CtxSchritt m m (.verweigert c)
  | fehlerUDxsave {m : HwMaschine} (c : Nat) (a : Adresse)
      (x : Xcr0Bild) (q : Bool)
      (h : ctxXSave m c a x q = .fehlerUD) :
      CtxSchritt m m (.verweigert c)
  | fehlerVerweigert {m : HwMaschine} (c : Nat) (a : Adresse)
      (h : ctxSpeichern m c a = .verweigert) :
      CtxSchritt m m (.verweigert c)

/-- (1) Every family step preserves well-formedness. -/
theorem ctxSchritt_wf (m m' : HwMaschine) (e : CtxEreignis)
    (h : CtxSchritt m m' e) (hwf : HwWf m) : HwWf m' := by
  cases h with
  | fxsave c a h => exact ctxSpeichern_wf _ _ _ hwf _ h
  | fxrstor c a h => exact ctxWiederherstellen_wf _ _ _ hwf _ h
  | xsave c a x q h => exact ctxXSave_wf _ _ _ _ _ hwf _ h
  | xrstor c a x q h => exact ctxXRstor_wf _ _ _ _ _ hwf _ h
  | lade c a v h => exact hwf
  | gibAus c a v s' h => exact setTso_wf _ s' hwf
  | spüle c e s' h hkopf => exact setTso_wf _ s' hwf
  | fehlerGPsave c a h => exact hwf
  | fehlerUDxsave c a x q h => exact hwf
  | fehlerVerweigert c a h => exact hwf

/-- (2) The TSO observation leg IS the coherent TSO step. -/
theorem ctxLade_ist_hw (m m' : HwMaschine) (c : Nat) (a : Adresse)
    (v : Byte)
    (h : CtxSchritt m m' (.leseBeob c a v)) :
    HwSchritt m m' (.leseBeob c a v) := by
  cases h with
  | lade c a v h => exact HwSchritt.lade c a v h

/-- (2) The TSO store-issue leg IS the coherent TSO step. -/
theorem ctxGibAus_ist_hw (m m' : HwMaschine) (c : Nat) (a : Adresse)
    (v : Byte)
    (h : CtxSchritt m m' (.schreibAusgabe c a v)) :
    HwSchritt m m' (.schreibAusgabe c a v) := by
  cases h with
  | gibAus c a v s' h => exact HwSchritt.gibAus c a v s' h

/-- (2) The TSO drain leg IS the coherent TSO step. -/
theorem ctxSpüle_ist_hw (m m' : HwMaschine) (c : Nat)
    (e : TSOEintrag)
    (h : CtxSchritt m m' (.spülung c e)) :
    ∃ s' : TSOZustand, HwSchritt m m' (.spülung c e) := by
  cases h with
  | spüle c e s' h hkopf => exact ⟨s', HwSchritt.spüle c e s' h hkopf⟩

/-- The lane-1247 producer plug over the §11 `HwAdapter` interface:
    the four request events ride the checked steps; anything else
    (observations, mismatched cores, refusals) admits nothing. -/
def adapterContext : HwAdapter CtxEreignis :=
  ⟨fun m c ev => match ev with
  | .fxsaveReq c' a =>
    if c = c' then ctxOpt (ctxSpeichern m c a) else none
  | .fxrstorReq c' a =>
    if c = c' then ctxOpt (ctxWiederherstellen m c a) else none
  | .xsaveReq c' a x q =>
    if c = c' then ctxOpt (ctxXSave m c a x q) else none
  | .xrstorReq c' a x q =>
    if c = c' then ctxOpt (ctxXRstor m c a x q) else none
  | _ => none⟩

/-- The adapter runs the save request where the core agrees. -/
theorem adapterContext_fxsave (m : HwMaschine) (c : Nat) (a : Adresse) :
    adapterContext.schritt m c (.fxsaveReq c a) =
      ctxOpt (ctxSpeichern m c a) := by
  simp [adapterContext]

/-- The adapter refuses a mismatched core. -/
theorem adapterContext_fxsave_fremd (m : HwMaschine) (c c' : Nat)
    (a : Adresse) (h : c ≠ c') :
    adapterContext.schritt m c (.fxsaveReq c' a) = none := by
  simp [adapterContext, h]

/-- The adapter admits no observation step. -/
theorem adapterContext_ohne_beob (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte) :
    adapterContext.schritt m c (.leseBeob c a v) = none := by
  rfl

/-- Adapter success preserves well-formedness (save leg). -/
theorem adapterContext_fxsave_wf (m : HwMaschine) (c : Nat)
    (a : Adresse) (hwf : HwWf m) (m' : HwMaschine)
    (h : adapterContext.schritt m c (.fxsaveReq c a) = some m') :
    HwWf m' := by
  have h1 : ctxOpt (ctxSpeichern m c a) = some m' := by
    simpa [adapterContext] using h
  cases ho : ctxSpeichern m c a with
  | weiter m2 =>
    have h2 : m2 = m' := Option.some_inj.mp (by simpa [ho, ctxOpt] using h1)
    rw [←h2]
    exact ctxSpeichern_wf m c a hwf m2 ho
  | verweigert => simp [ho, ctxOpt] at h1
  | fehlerGP => simp [ho, ctxOpt] at h1
  | fehlerUD => simp [ho, ctxOpt] at h1

/-- Adapter success preserves well-formedness (restore leg). -/
theorem adapterContext_fxrstor_wf (m : HwMaschine) (c : Nat)
    (a : Adresse) (hwf : HwWf m) (m' : HwMaschine)
    (h : adapterContext.schritt m c (.fxrstorReq c a) = some m') :
    HwWf m' := by
  have h1 : ctxOpt (ctxWiederherstellen m c a) = some m' := by
    simpa [adapterContext] using h
  cases ho : ctxWiederherstellen m c a with
  | weiter m2 =>
    have h2 : m2 = m' := Option.some_inj.mp (by simpa [ho, ctxOpt] using h1)
    rw [←h2]
    exact ctxWiederherstellen_wf m c a hwf m2 ho
  | verweigert => simp [ho, ctxOpt] at h1
  | fehlerGP => simp [ho, ctxOpt] at h1
  | fehlerUD => simp [ho, ctxOpt] at h1

/-! ## 8. Joint witness: two cores save, forward, drain; refusals;
    interrupt FP preservation.

    Core 0 saves at `0x1000`, core 1 at `0x2000` (both 16- and
    64-aligned). Memory starts zeroed; permissions cover exactly the
    two save footprints plus the reserved-bit probe area. Core 0
    carries MXCSR `0x1F80` (low byte `0x80`) and XMM low halves `7`;
    core 1 carries `0x1FBF` (sticky bits set, still profile-valid:
    `mxcsr_sticky_egal_gueltig`) and low halves `11`. -/

/-- Witness area base, core 0 (16- and 64-aligned). -/
def ctxArea0 : Adresse := BitVec.ofNat 64 4096

/-- Witness area base, core 1. -/
def ctxArea1 : Adresse := BitVec.ofNat 64 8192

/-- Witness area base, reserved-bit probe. -/
def ctxAreaR : Adresse := BitVec.ofNat 64 12288

/-- Witness permission: exactly the footprint ranges. -/
def ctxWitOk (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + 416) ||
  decide (8192 ≤ a.toNat ∧ a.toNat < 8192 + 416) ||
  decide (12288 ≤ a.toNat ∧ a.toNat < 12288 + 416)

/-- Witness memory: zeroed bytes, footprint permissions, no execute. -/
def ctxWitMem : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0, lesbar := ctxWitOk,
    schreibbar := ctxWitOk, ausfuehrbar := fun _ => false }

/-- Witness control word, core 0: reset. -/
def ctxWitK0 : FPKontext := ⟨0x1F80⟩

/-- Witness control word, core 1: sticky-set, still valid. -/
def ctxWitK1 : FPKontext := ⟨0x1FBF⟩

/-- Witness XMM file, core 0 (low halves 7). -/
def ctxWitX0 : XmmDatei :=
  fun _ => vecJoin (BitVec.ofNat 64 7) (BitVec.ofNat 64 0)

/-- Witness XMM file, core 1 (low halves 11). -/
def ctxWitX1 : XmmDatei :=
  fun _ => vecJoin (BitVec.ofNat 64 11) (BitVec.ofNat 64 0)

/-- Witness cores: distinct FP/vector state per core. -/
def ctxWitKern : Nat → HwKern
  | 0 => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0, ctxWitX0, ctxWitK0⟩
  | 1 => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0, ctxWitX1, ctxWitK1⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two saving cores, empty
    buffers, full silicon, baseline readiness. -/
def ctxWitStart : HwMaschine :=
  ⟨ctxWitMem, ctxWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed. -/
theorem ctxWitStart_wf : HwWf ctxWitStart := by
  intro c f _
  cases f <;> rfl

/-- Area bases are save-aligned. -/
theorem ctxWit_ausgerichtet :
    fxAusgerichtet ctxArea0 = true ∧ fxAusgerichtet ctxArea1 = true ∧
      xAusgerichtet ctxArea0 = true := by
  decide

/-- A misaligned base is refused alignment. -/
theorem ctxWit_schief :
    fxAusgerichtet (BitVec.ofNat 64 4104) = false ∧
      xAusgerichtet (BitVec.ofNat 64 4104) = false := by
  decide

/-- Project a buffer length out of a save outcome. -/
def ctxWitBuf (o : CtxAusgang) (c : Nat) : Option Nat :=
  match o with
  | .weiter m => some (m.puffer c).length
  | _ => none

/-- Project one TSO-view byte out of a save outcome. -/
def ctxWitByte (o : CtxAusgang) (c : Nat)
    (a : Adresse) : Option (Option Byte) :=
  match o with
  | .weiter m => some (loadByte (tsoAnsicht m) c a)
  | _ => none

set_option maxRecDepth 100000 in
/-- Both cores buffer exactly the 260 footprint entries
    (elaboration-only depth budget for the kernel `decide`). -/
theorem ctxWit_buf :
    ctxWitBuf (ctxSpeichern ctxWitStart 0 ctxArea0) 0 = some 260 ∧
      ctxWitBuf (ctxSpeichern ctxWitStart 1 ctxArea1) 1 = some 260 := by
  decide

set_option maxRecDepth 100000 in
/-- Owner-only forwarding: core 0 reads its MXCSR low byte `0x80`,
    core 1 still reads the zeroed cell. -/
theorem ctxWit_fwd :
    ctxWitByte (ctxSpeichern ctxWitStart 0 ctxArea0) 0
        (addrOff ctxArea0 24) =
        some (some (BitVec.ofNat 8 128)) ∧
      ctxWitByte (ctxSpeichern ctxWitStart 0 ctxArea0) 1
        (addrOff ctxArea0 24) =
        some (some (BitVec.ofNat 8 0)) := by
  decide

set_option maxRecDepth 100000 in
/-- The XMM slot byte forwards to its owner. -/
theorem ctxWit_xmm_fwd :
    ctxWitByte (ctxSpeichern ctxWitStart 0 ctxArea0) 0
        (addrOff ctxArea0 160) =
        some (some (BitVec.ofNat 8 7)) := by
  decide

/-- The machine after core 0 saves, if reached. -/
def ctxWitM1 : Option HwMaschine :=
  match ctxSpeichern ctxWitStart 0 ctxArea0 with
  | .weiter m => some m
  | _ => none

/-- Core 0 drains its oldest entry (the MXCSR low byte). -/
def ctxWitFlush1 : Option TSOZustand :=
  match ctxWitM1 with
  | some m => flushKern (tsoAnsicht m) 0
  | none => none

/-- Project a shared-memory byte out of a drained state. -/
def ctxWitFlushByte (o : Option TSOZustand)
    (a : Adresse) : Option Byte :=
  match o with
  | some s => some (s.mem.bytes a)
  | none => none

set_option maxRecDepth 100000 in
/-- THE DRAIN CHANGES MEMORY: the cell starts zeroed and reads
    `0x80` after one flush. -/
theorem ctxWit_spülung_aendert :
    ctxWitMem.bytes (addrOff ctxArea0 24) = BitVec.ofNat 8 0 ∧
      ctxWitFlushByte ctxWitFlush1 (addrOff ctxArea0 24) =
        some (BitVec.ofNat 8 128) := by
  decide

/-- Project the restored control word out of a restore outcome. -/
def ctxWitFpNach (o : CtxAusgang) : Option Nat :=
  match o with
  | .weiter m => some (((m.kerne 0).fp).mxcsr.toNat)
  | _ => none

/-- Restore chained onto the save: the control word comes back. -/
def ctxWitRestored : Option Nat :=
  match ctxWitM1 with
  | some m1 => ctxWitFpNach (ctxWiederherstellen m1 0 ctxArea0)
  | none => none

set_option maxRecDepth 100000 in
/-- MACHINE ROUND TRIP, observed: `0x1F80` saved and restored. -/
theorem ctxWit_restore : ctxWitRestored = some 8064 := by
  decide

/-- Outcome kind projection (outcomes carry functions, so no
    `DecidableEq`; kinds are plain numbers). -/
def ctxWitArt (o : CtxAusgang) : Nat :=
  match o with
  | .weiter _ => 0
  | .verweigert => 1
  | .fehlerGP => 2
  | .fehlerUD => 3

set_option maxRecDepth 100000 in
/-- Planted refusals, observed: misaligned save is #GP, a request
    with no modelled component is refused, XSAVE without XCR0 SSE
    readiness is #UD, misaligned XSAVE is #GP. -/
theorem ctxWit_verweigert :
    ctxWitArt (ctxSpeichern ctxWitStart 0 (BitVec.ofNat 64 4104)) = 2 ∧
      ctxWitArt (ctxXSave ctxWitStart 0 ctxArea0 ⟨true, true, false⟩
        false) = 1 ∧
      ctxWitArt (ctxXSave ctxWitStart 0 ctxArea0 ⟨true, false, false⟩
        true) = 3 ∧
      ctxWitArt (ctxXSave ctxWitStart 0 (BitVec.ofNat 64 4104)
        ⟨true, true, false⟩ true) = 2 := by
  decide

/-- Reserved-bit probe bytes: bit 18 set in the MXCSR image cell. -/
def ctxWitMemRBytes (a : Adresse) : Byte :=
  if decide (a = addrOff ctxAreaR 26) then BitVec.ofNat 8 4
  else BitVec.ofNat 8 0

/-- Reserved-bit probe memory. -/
def ctxWitMemR : Speicher :=
  { bytes := ctxWitMemRBytes, lesbar := ctxWitOk,
    schreibbar := ctxWitOk, ausfuehrbar := fun _ => false }

/-- Reserved-bit probe machine. -/
def ctxWitStartR : HwMaschine :=
  { ctxWitStart with mem := ctxWitMemR }

set_option maxRecDepth 100000 in
/-- A reserved MXCSR image bit faults with #GP on restore. -/
theorem ctxWit_gp_reserviert :
    ctxWitArt (ctxWiederherstellen ctxWitStartR 0 ctxAreaR) = 2 := by
  decide

/-- Project the delivered control word out of a delivery outcome. -/
def ctxWitIntFp (o : Option (HwMaschine × Bool × Bool)) :
    Option Nat :=
  match o with
  | some (m, _, _) => some (((m.kerne 0).fp).mxcsr.toNat)
  | none => none

/-- INTERRUPT DELIVERY preserves the core's control word (NMI under
    IF=false over the accepted IDT image, reused from HwInterrupts). -/
theorem ctxWit_int_fp :
    ctxWitIntFp
      (asyncSchritt intWitStart 0 witNmi witSteuerNmi) =
      some 8064 := by
  decide

end Gabbro.Grammatik.X86
