/-
  File:      Grammatik/X86/VectorIntegerFetchedSteps.lean
  Subject:   Fetched packed-integer steps with a dispatch-slot interface.

  Lane 1110: fetched packed-integer execution for the accepted `IntVecOp`
  rows (lane 686) on the common machine discipline (`FpZustand`, `geholt`,
  `laengeOk`, `ausfuehrbarN`), with a saturate-not-mask shift interface, a
  checked shared-store gate, and an explicit dispatch-slot API for the
  718-repair and 724 consumers. No unaccepted module is imported.
-/
import Grammatik.X86.VectorIntegerHardwareForms
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.IntegerHardwareForms
import Grammatik.X86.ScalarFloatHardwareForms
import Grammatik.X86.LockedInstructionExecution
import Grammatik.X86.IndirectControlHardwareForms
import Grammatik.X86.FpControlHardwareForms
import Grammatik.X86.CpuFeatureHardwareForms
import Grammatik.X86.ArchitecturalFlags
import Grammatik.X86.MemoryTypeHardwareExecution
import Grammatik.X86.ConcurrentIntegerExecution
import Grammatik.X86.AddressedHardwareExecution

namespace Gabbro.Grammatik.X86

/-- Shared-store gate: a vector store to a shared address is refused
    until the 6B TSO bridge rules it; every other row is unaffected.
    `geteilt` marks a shared target address (established outside this
    file, never assumed here). -/
def vecGeteiltFrei (geteilt : Bool) : IntVecOp → Bool
  | .movdqaSt _ _ _ => !geteilt
  | .movdquSt _ _ _ => !geteilt
  | _ => true

/-- Fetched packed-integer step: decode the ACTUAL fetched bytes, check
    the shared-store gate, then run the accepted selected step. A forged
    `IntVecDec` cannot inject an instruction. -/
def vecFetched (t : FpZustand) (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (k : KontrollBild) (geteilt : Bool) :
    Option FpZustand :=
  match fetchIntVec t (geholt t.kern) with
  | none => none
  | some (d, _) =>
    match vecGeteiltFrei geteilt d.op with
    | true => stepIntVec d t hw b cpu k
    | false => none

/-- A private target never trips the shared-store gate, on any row. -/
theorem vecGeteiltFrei_privat (op : IntVecOp) :
    vecGeteiltFrei false op = true := by
  cases op <;> rfl

/-- A shared aligned store is refused by the gate. -/
theorem vecGeteiltFrei_versperrt_a (base : Register) (src : XmmReg)
    (disp : BitVec 32) :
    vecGeteiltFrei true (.movdqaSt base src disp) = false := rfl

/-- A shared unaligned store is refused by the gate. -/
theorem vecGeteiltFrei_versperrt_u (base : Register) (src : XmmReg)
    (disp : BitVec 32) :
    vecGeteiltFrei true (.movdquSt base src disp) = false := rfl

/-- FETCHED STEP AGREEMENT: a fetched selected form over a private
    target steps through the fetched wrapper, on every `IntVecOp` row.
    The fetch premise ties the step to ACTUAL bytes; the gate premise
    ties it to a private target. -/
theorem vecFetched_schritt (t t' : FpZustand) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild)
    (d : IntVecDec) (rest : List Byte) (geteilt : Bool)
    (hf : fetchIntVec t (geholt t.kern) = some (d, rest))
    (hs : stepIntVec d t hw b cpu k = some t')
    (hpriv : geteilt = false) :
    vecFetched t hw b cpu k geteilt = some t' := by
  unfold vecFetched
  simp only [hf, hpriv, vecGeteiltFrei_privat]
  exact hs

/-- WITNESS for `vecFetched_schritt`: the pinned fetched PADDB row
    steps through the wrapper. All premises are instantiated jointly:
    actual code bytes (`intVec_fetch_pin`), the accepted row equation,
    and a private target. -/
theorem vecFetched_schritt_zeuge :
    vecFetched ivCodeT basisHw ivBereit basisCpu basisKontrolle false =
      some { ivCodeT with kern := { ivCodeT.kern with rip := ripNach ivCodeT.kern.rip 5 }, xmm := xmmSet ivCodeT.xmm .xmm0 (vecAdd .b8 (ivCodeT.xmm .xmm0) (ivCodeT.xmm .xmm1)) } := by
  have hf := intVec_fetch_pin
  have hs := stepIntVec_paddb
    (⟨.paddbRR .xmm0 .xmm1, 5⟩ : IntVecDec) ivCodeT
    basisHw ivBereit basisCpu basisKontrolle .xmm0 .xmm1
    (by decide) iv_gate rfl
  exact vecFetched_schritt _ _ _ _ _ _ _ _ _ hf hs rfl

/-- Shift-count reading for the fetched packed shifts: saturating
    ONLY. There is deliberately no masked-count constructor: a consumer
    that unifies these rows with masked-count scalar semantics has no
    constructor to case on and fails with a loud type error at this
    interface, never a silent semantic swap. -/
inductive VecShiftLesart where
  | satt : VecShiftLesart
  deriving DecidableEq, Repr

/-- SATURATE, NOT MASK, AT THE INTERFACE: under the only available
    count reading, an over-width count zeroes both shift directions.
    The lane evaluators are reused from lane 686, never forked. -/
theorem vecFetched_shift_satt (lesart : VecShiftLesart) (v : Vektor)
    (c : Nat) (hc : 63 < c) :
    vecShlQ v c = 0 ∧ vecShrQ v c = 0 := by
  cases lesart
  exact ⟨vecShlQ_satt_null v c hc, vecShrQ_satt_null v c hc⟩

/-- MASKED-COUNT READING, REFUSED (planted probe): count 64 does
    not wrap to a zero shift. The nonzero pattern is zeroed by the
    saturating reading, never preserved as masked semantics would. -/
theorem vecFetched_maskiert_verweigert :
    vecShlQ (BitVec.ofNat 128 0xFF) 64 ≠ BitVec.ofNat 128 0xFF ∧
      vecShrQ (BitVec.ofNat 128 0xFF00) 64 ≠
        BitVec.ofNat 128 0xFF00 := by
  have h := vecShlQ_satt_vs_maske
  constructor
  · rw [h.1]
    decide
  · rw [h.2]
    decide

/-- DIVERGENCE PRESERVED THROUGH FETCHING: a fetched imm8 packed
    shift with an over-width count zeroes every 64-bit lane. The length
    guard comes from the fetch discipline itself; the hardware gate is
    recovered from the successful selected step, never assumed. -/
theorem vecFetched_satt_erhalten (t t' : FpZustand) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild)
    (d : IntVecDec) (rest : List Byte) (dst : XmmReg) (imm : Nat)
    (hf : fetchIntVec t (geholt t.kern) = some (d, rest))
    (hop : d.op = .psllqImm dst imm)
    (hc : 63 < imm)
    (hfet : vecFetched t hw b cpu k false = some t') :
    ∀ i : Nat, laneNat .b64 (t'.xmm dst) i = 0 := by
  have hok : laengeOk d.laenge = true :=
    (fetchIntVec_erfolg t (geholt t.kern) d rest hf).2.2.1
  have hstep : stepIntVec d t hw b cpu k = some t' := by
    unfold vecFetched at hfet
    simp only [hf, vecGeteiltFrei_privat] at hfet
    exact hfet
  have hgate : vektorLegacyZugelassen hw b cpu k = true := by
    cases hg : vektorLegacyZugelassen hw b cpu k with
    | true => rfl
    | false =>
      have hnone := stepIntVec_profil_verweigert d t hw b cpu k hok hg
      rw [hnone] at hstep
      cases hstep
  have heq := stepIntVec_psllqImm d t hw b cpu k dst imm hok hgate hop
  rw [heq] at hstep
  cases hstep
  intro i
  show laneNat .b64 ((xmmSet t.xmm dst (vecShlQ (t.xmm dst) imm)) dst) i = 0
  rw [xmmSet_gleich]
  exact laneNat_shlQ_satt _ _ _ hc

/-- Saturating-count code bytes: the 6-byte PSLLQ-imm8 encoding
    with count 64 (`REX 64, 102, 15, 115, ModRM /6 at xmm4, imm 64`),
    then zeros. -/
def vecSattCodeBytes (a : Adresse) : Byte :=
  if a.toNat = 0 then natByte 64
  else if a.toNat = 1 then natByte 102
  else if a.toNat = 2 then natByte 15
  else if a.toNat = 3 then natByte 115
  else if a.toNat = 4 then natByte 244
  else if a.toNat = 5 then natByte 64
  else BitVec.ofNat 8 0

/-- Saturating-count code memory: the code bytes, fully executable. -/
def vecSattCodeMem : Speicher :=
  { vecZeugenSpeicher with bytes := vecSattCodeBytes, ausfuehrbar := fun _ => true }

/-- Saturating-count fetch state: RIP zero over the code memory, the
    nonzero 686 joint pattern `ivX4` in xmm4, legacy admission on. -/
def vecSattT : FpZustand :=
  ⟨{ register := fun _ => 0, flags := ⟨false, false, none, false, false, false⟩, rip := 0, speicher := vecSattCodeMem }, ivXmm0, kontextReset⟩

/-- FETCHED PIN for the saturating row: actual code bytes fetch to
    the PSLLQ-imm8 count-64 row with nine trailing bytes of rest. -/
theorem vecSatt_fetch_pin :
    fetchIntVec vecSattT (geholt vecSattT.kern) =
      some ((⟨.psllqImm .xmm4 64, 6⟩ : IntVecDec),
        List.replicate 9 (BitVec.ofNat 8 0)) := by
  decide

/-- WITNESS for `vecFetched_satt_erhalten`: the fetched count-64
    shift zeroes every lane of the nonzero operand. All premises are
    instantiated jointly: actual code bytes, the imm8 row at count 64,
    the over-width fact, and the fetched step through the wrapper. -/
theorem vecFetched_satt_erhalten_zeuge (i : Nat) :
    ∃ t' : FpZustand,
      vecFetched vecSattT basisHw ivBereit basisCpu basisKontrolle
          false = some t' ∧
        laneNat .b64 (t'.xmm .xmm4) i = 0 := by
  have hf := vecSatt_fetch_pin
  have hnull : vecShlQ (vecSattT.xmm .xmm4) 64 = 0 := by
    have hx : vecSattT.xmm .xmm4 = ivX4 := rfl
    rw [hx]
    exact vecShlQ_satt_null _ _ (by decide)
  have hs : stepIntVec (⟨.psllqImm .xmm4 64, 6⟩ : IntVecDec) vecSattT
      basisHw ivBereit basisCpu basisKontrolle =
      some { vecSattT with kern := { vecSattT.kern with rip := ripNach vecSattT.kern.rip 6 }, xmm := xmmSet vecSattT.xmm .xmm4 0 } := by
    have heq := stepIntVec_psllqImm
      (⟨.psllqImm .xmm4 64, 6⟩ : IntVecDec) vecSattT
      basisHw ivBereit basisCpu basisKontrolle .xmm4 64
      (by decide) iv_gate rfl
    rw [hnull] at heq
    exact heq
  have hfet : vecFetched vecSattT basisHw ivBereit basisCpu
      basisKontrolle false =
      some { vecSattT with kern := { vecSattT.kern with rip := ripNach vecSattT.kern.rip 6 }, xmm := xmmSet vecSattT.xmm .xmm4 0 } :=
    vecFetched_schritt _ _ _ _ _ _ _ _ _ hf hs rfl
  refine ⟨_, hfet, ?_⟩
  exact vecFetched_satt_erhalten vecSattT _ basisHw ivBereit basisCpu
    basisKontrolle _ _ .xmm4 64 hf rfl (by decide) hfet i

/-- Dispatch slot tag: one slot per byte family. `pilot` is the
    accepted pilot decoder, `ext` the accepted unified dispatcher, then
    one slot per producer decoder module in task order (575 after the
    pilot because `decodeComboIV` chains it there; the rest in the
    order 666, 668, 662, 680, 682, 688, 692), and `intVec` for the
    selected packed-integer rows. The 694 MMIO module shares the unified
    byte dispatch (`fetchExt` over `decodeExt`), so its byte slot
    coincides with `ext`; its profile side is pinned separately by
    `vecSlot_mmio`. -/
inductive VecSlotTag where
  | pilot : VecSlotTag
  | ext : VecSlotTag
  | intHw : VecSlotTag
  | fpHw : VecSlotTag
  | lock : VecSlotTag
  | ind : VecSlotTag
  | mxcsr : VecSlotTag
  | cpuFeat : VecSlotTag
  | flags : VecSlotTag
  | intVec : VecSlotTag
  deriving DecidableEq, Repr

/-- Slot discriminator over actual bytes: the first matching family in
    slot order wins; `none` is refused by every family. The 692 flag
    adapters match single-byte lists only. Cross-family shadowing beyond
    the pinned rows stays OPEN (see CUTS). -/
def vecSlotVon (bs : List Byte) : Option VecSlotTag :=
  match decode bs with
  | some _ => some .pilot
  | none =>
    match decodeExt bs with
    | some _ => some .ext
    | none =>
      match decodeIntHw bs with
      | some _ => some .intHw
      | none =>
        match fpHwDecode bs with
        | some _ => some .fpHw
        | none =>
          match decodeLockExt bs with
          | some _ => some .lock
          | none =>
            match decodeIndirekt bs with
            | some _ => some .ind
            | none =>
              match mxcsrDecode bs with
              | some _ => some .mxcsr
              | none =>
                match decodeCpuFeature bs with
                | some _ => some .cpuFeat
                | none =>
                  match pushfqByte bs, popfqByte bs with
                  | some _, _ => some .flags
                  | _, some _ => some .flags
                  | none, none =>
                    match decodeIntVec bs with
                    | some _ => some .intVec
                    | none => none

/-- The pilot decoder refuses the PADDB bytes. -/
theorem vecSlot_pilot_weist_paddb_zurueck :
    decode (encodeIntVec (.paddbRR .xmm0 .xmm1)) = none := by
  decide

/-- The 666 integer decoder refuses the PADDB bytes. -/
theorem vecSlot_intHw_weist_paddb_zurueck :
    decodeIntHw (encodeIntVec (.paddbRR .xmm0 .xmm1)) = none := by
  decide

/-- The 668 scalar-float decoder refuses the PADDB bytes. -/
theorem vecSlot_fpHw_weist_paddb_zurueck :
    fpHwDecode (encodeIntVec (.paddbRR .xmm0 .xmm1)) = none := by
  decide

/-- The 662 combined lock decoder refuses the PADDB bytes. -/
theorem vecSlot_lock_weist_paddb_zurueck :
    decodeLockExt (encodeIntVec (.paddbRR .xmm0 .xmm1)) = none := by
  decide

/-- The 680 indirect decoder refuses the PADDB bytes. -/
theorem vecSlot_ind_weist_paddb_zurueck :
    decodeIndirekt (encodeIntVec (.paddbRR .xmm0 .xmm1)) = none := by
  decide

/-- The 682 MXCSR decoder refuses the PADDB bytes. -/
theorem vecSlot_mxcsr_weist_paddb_zurueck :
    mxcsrDecode (encodeIntVec (.paddbRR .xmm0 .xmm1)) = none := by
  decide

/-- The 688 CPU-feature decoder refuses the PADDB bytes. -/
theorem vecSlot_cpuFeat_weist_paddb_zurueck :
    decodeCpuFeature (encodeIntVec (.paddbRR .xmm0 .xmm1)) = none := by
  decide

/-- The 692 flag adapters refuse the PADDB bytes (multi-byte lists
    match neither single-byte adapter, by shape). -/
theorem vecSlot_flags_weist_paddb_zurueck :
    pushfqByte (encodeIntVec (.paddbRR .xmm0 .xmm1)) = none ∧
      popfqByte (encodeIntVec (.paddbRR .xmm0 .xmm1)) = none :=
  ⟨rfl, rfl⟩

/-- The 694 MMIO side: the unified dispatcher refuses the vector
    load bytes (so the UC device path never sees them), and the empty
    UC profile covers nothing (WB is the default everywhere). -/
theorem vecSlot_mmio :
    decodeExt (encodeIntVec (.movdquLd .xmm0 .rax 0)) = none ∧
      ∀ (a : Adresse) (n : Nat), istUc [] a n = false :=
  ⟨intVec_ext_weist_movdquLd_zurueck, fun a n => istUc_leer a n⟩

/-- SLOT INTERFACE INHABITATION: the canonical PADDB bytes classify to
    the packed-integer slot. Every earlier family refuses them (pilot,
    the accepted unified dispatcher, all nine producer decoders, both
    flag adapters); the selected decoder accepts them. -/
theorem vecFetched_slot_schnittstelle :
    vecSlotVon (encodeIntVec (.paddbRR .xmm0 .xmm1)) = some .intVec := by
  have hround : decodeIntVec (encodeIntVec (.paddbRR .xmm0 .xmm1)) =
      some ((⟨.paddbRR .xmm0 .xmm1, 5⟩ : IntVecDec), []) := by
    simpa using roundtrip_paddb .xmm0 .xmm1 []
  have hflags := vecSlot_flags_weist_paddb_zurueck
  unfold vecSlotVon
  simp only [vecSlot_pilot_weist_paddb_zurueck,
    intVec_ext_weist_paddb_zurueck, vecSlot_intHw_weist_paddb_zurueck,
    vecSlot_fpHw_weist_paddb_zurueck, vecSlot_lock_weist_paddb_zurueck,
    vecSlot_ind_weist_paddb_zurueck, vecSlot_mxcsr_weist_paddb_zurueck,
    vecSlot_cpuFeat_weist_paddb_zurueck, hflags.1, hflags.2, hround]

/-- WITNESS for `vecFetched_slot_schnittstelle`, from the producer
    side: the canonical 688 CPUID bytes classify to the CPU-feature
    slot, never to the packed-integer slot. Every earlier family
    refuses them; the producer decoder accepts them. -/
theorem vecFetched_slot_schnittstelle_zeuge :
    vecSlotVon (cpuEncode .cpuid) = some .cpuFeat := by
  have hpilot : decode (cpuEncode .cpuid) = none := by decide
  have hext : decodeExt (cpuEncode .cpuid) = none := by decide
  have hintHw : decodeIntHw (cpuEncode .cpuid) = none := by decide
  have hfpHw : fpHwDecode (cpuEncode .cpuid) = none := by decide
  have hlock : decodeLockExt (cpuEncode .cpuid) = none := by decide
  have hind : decodeIndirekt (cpuEncode .cpuid) = none := by decide
  have hmxcsr : mxcsrDecode (cpuEncode .cpuid) = none := by decide
  have hpush : pushfqByte (cpuEncode .cpuid) = none := by decide
  have hpop : popfqByte (cpuEncode .cpuid) = none := by decide
  have hcpu : decodeCpuFeature (cpuEncode .cpuid) =
      some (.cpuid, []) := by
    simpa using decodeCpu_cpuid []
  unfold vecSlotVon
  rw [hpilot, hext, hintHw, hfpHw, hlock, hind, hmxcsr, hpush, hpop, hcpu]

/-- SHARED STORE, REFUSED (planted probe): a fetched unaligned
    vector store to a shared address is refused by the checked gate,
    even where fetch and decoding succeed. -/
theorem vecFetched_geteilt_u_verweigert (t : FpZustand) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild)
    (d : IntVecDec) (rest : List Byte) (base : Register) (src : XmmReg)
    (disp : BitVec 32)
    (hf : fetchIntVec t (geholt t.kern) = some (d, rest))
    (hstore : d.op = .movdquSt base src disp) :
    vecFetched t hw b cpu k true = none := by
  unfold vecFetched
  simp only [hf, hstore, vecGeteiltFrei_versperrt_u]

/-- SHARED STORE, REFUSED (planted probe): the aligned twin. -/
theorem vecFetched_geteilt_a_verweigert (t : FpZustand) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild)
    (d : IntVecDec) (rest : List Byte) (base : Register) (src : XmmReg)
    (disp : BitVec 32)
    (hf : fetchIntVec t (geholt t.kern) = some (d, rest))
    (hstore : d.op = .movdqaSt base src disp) :
    vecFetched t hw b cpu k true = none := by
  unfold vecFetched
  simp only [hf, hstore, vecGeteiltFrei_versperrt_a]

/-- 129TH-BIT DEPENDENCE, REFUSED (planted probe): left-shift
    results are a function of the 128-bit word value alone. Two equal
    words never shift apart, so no bit beyond 127 influences any packed
    shift left. -/
theorem vecFetched_bit129_shl_verweigert :
    ¬ ∃ (v w : Vektor) (c : Nat),
      v = w ∧ vecShlQ v c ≠ vecShlQ w c := by
  intro h
  obtain ⟨v, w, c, heq, hne⟩ := h
  subst heq
  exact hne rfl

/-- 129TH-BIT DEPENDENCE, REFUSED (planted probe): the right-shift
    twin. -/
theorem vecFetched_bit129_shr_verweigert :
    ¬ ∃ (v w : Vektor) (c : Nat),
      v = w ∧ vecShrQ v c ≠ vecShrQ w c := by
  intro h
  obtain ⟨v, w, c, heq, hne⟩ := h
  subst heq
  exact hne rfl

/-- The 730 address discipline for the vector memory rows: every
    row addresses through the accepted `effAddr` of the pre-state
    register file -- no second address model -- so the accepted
    prestate-aliasing transfers to all four load/store rows. -/
theorem vecFetched_adresse_prestate (s1 s2 : Zustand) (base : Register)
    (disp : BitVec 32)
    (h : s1.register base = s2.register base) :
    effAddr s1 base disp = effAddr s2 base disp :=
  effAddr_prestate s1 s2 base disp h

/-- The 720 no-single-event discipline for the vector memory rows: the
    witness 128-bit store factors into the two ordered canonical
    64-bit chunk writes with the torn intermediate state standing --
    never one atomic 16-byte event. -/
theorem vecFetched_zwei_chunks :
    ∃ m1 : Speicher,
      write64 ivT3.kern.speicher (effAddr ivT3.kern .rax 16)
          (vLo (ivT3.xmm .xmm3)) = some m1 ∧
        write64 m1 (vecHiAddr (effAddr ivT3.kern .rax 16))
          (vHi (ivT3.xmm .xmm3)) = some ivM4 :=
  vecWrite_aufgeteilt _ _ _ _ ivHwr

/-- JOINT WITNESS (non-degenerate): a fetched packed row agrees
    through the wrapper, while the lane-shift and memory rows of the
    accepted joint sequence run with an observably memory-changing
    store. The run reaches its steps and changes memory (byte 18); the
    frame byte, the sentinel register and the flags stay put in 686. -/
theorem vecFetched_joint_zeuge :
    ∃ t' : FpZustand,
      vecFetched ivCodeT basisHw ivBereit basisCpu basisKontrolle
          false = some t' ∧
        stepIntVec (⟨.psllqImm .xmm3 8, 6⟩ : IntVecDec) ivT2 basisHw
          ivBereit basisCpu basisKontrolle = some ivT3 ∧
        stepIntVec (⟨.movdqaSt .rax .xmm3 16, 9⟩ : IntVecDec) ivT3
          basisHw ivBereit basisCpu basisKontrolle = some ivT4 ∧
        ivT4.kern.speicher.bytes (natAdresse 18) ≠
          ivT0.kern.speicher.bytes (natAdresse 18) := by
  refine ⟨_, vecFetched_schritt_zeuge, ivS3, ivS4, ?_⟩
  decide

/- CUTS: what is not proved here.

   - Legacy YMM upper bits (`MAXVL-1:128` unmodified) stay unmodelled,
     as in lane 686: no YMM state exists in `FpZustand`.
   - No 128-bit single-copy atomicity is claimed anywhere: every
     load/store factors into the two ordered canonical 64-bit chunk
     accesses (`vecFetched_zwei_chunks`); the torn intermediate stands.
   - Shared vector stores are refused by the checked gate
     (`vecGeteiltFrei`) until the 6B TSO bridge rules them. Per-access
     TSO granularity, GX refinement and global visibility stay OPEN.
   - The 730 canonicality adapter (`kanonisch48`, `fussZugelassen`) is
     not re-proved for the vector rows: addresses reuse the accepted
     `effAddr` (no second address model, `vecFetched_adresse_prestate`),
     permissions stay per-byte data facts as in 686.
   - Dispatch-slot disjointness holds for the pinned canonical bytes
     only. The discriminator order (pilot, ext, nine producers,
     intVec) documents priority; shadowing-freedom over ALL byte
     strings, and producer rows beyond the pinned CPUID bytes, stay
     OPEN. The 694 MMIO byte slot coincides with `ext` (shared unified
     dispatch); only its profile side is pinned (`vecSlot_mmio`).
   - Masked-count scalar semantics is not unified with these rows by
     construction (`VecShiftLesart` has no masked constructor); the
     refusal is pinned (`vecFetched_maskiert_verweigert`).
   - Source correspondence, budget transfer, progress, call-log
     effects and `simdFreigabe` stay open, as in 686.
   - Unaccepted lanes 718/724 are not imported; this module is their
     consumption point, not their proof.
-/

#print axioms vecFetched
#print axioms vecGeteiltFrei
#print axioms vecSlotVon
#print axioms vecFetched_schritt
#print axioms vecFetched_satt_erhalten
#print axioms vecFetched_slot_schnittstelle
#print axioms vecFetched_joint_zeuge
#print axioms vecFetched_schritt_zeuge
#print axioms vecFetched_satt_erhalten_zeuge
#print axioms vecFetched_slot_schnittstelle_zeuge
#print axioms vecFetched_maskiert_verweigert
#print axioms vecFetched_geteilt_u_verweigert
#print axioms vecFetched_geteilt_a_verweigert
#print axioms vecFetched_bit129_shl_verweigert
#print axioms vecFetched_bit129_shr_verweigert
#print axioms vecFetched_zwei_chunks
#print axioms vecFetched_adresse_prestate

end Gabbro.Grammatik.X86
