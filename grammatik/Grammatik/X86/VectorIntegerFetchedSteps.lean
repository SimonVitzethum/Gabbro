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

end Gabbro.Grammatik.X86
