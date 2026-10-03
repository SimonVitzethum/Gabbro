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

end Gabbro.Grammatik.X86
