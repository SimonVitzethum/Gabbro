/-
  File:      Grammatik/X86/HwBildInstanzen.lean
  Subject:   Loaded image: per-family reached fetch instances.

  Lane 1205: follow-up of lane 1179 (`HwBildFamilien.lean`), whose
  obstruction theorems are universal implications and whose reached
  fetch instances exist only for narrow. Here six small loaded images
  (muldiv, shift, setcc, cmov, fp, vec; one family row each) stand on
  `hwBildStart`-style machines, each with a concrete `fetchExt`
  success, a Hw register step with exact evaluator agreement, a
  memory-changing TSO issue/drain stage, and planted refusals for a
  non-executable mapping. Every accepted definition is reused
  unchanged; nothing is redefined here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.Byteschritt
import Grammatik.X86.Bild
import Grammatik.X86.LoadedExecution
import Grammatik.X86.HardwareExecution
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.HwLoadedImage
import Grammatik.X86.HwBildFamilien
import Grammatik.X86.MulDiv
import Grammatik.X86.ShiftCodec
import Grammatik.X86.ControlCodec
import Grammatik.X86.ScalarFloat
import Grammatik.X86.VectorCodec

namespace Gabbro.Grammatik.X86

/-! ## Shared data address: every instance maps data at 0x2000. -/

/-- Shared data cell address in every instance image. -/
def instAdr : Adresse := BitVec.ofNat 64 0x102000

/-! ## Muldiv instance: `mul rax, rcx` over its own loaded image. -/

/-- Muldiv image bytes: the 3-byte MUL row then eight data zeroes. -/
def instDatei_muldiv : List Byte :=
  mulDivEncode (.mulRax .rcx) ++ List.replicate 8 (natByte 0)

/-- Muldiv code section: execute-only, exactly the 3 row bytes. -/
def instCode_muldiv : Abschnitt :=
  { dateiOff := 0, dateiLen := 3, vaddr := 0x1000, memLen := 3,
    lesbar := false, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Muldiv data section: eight bytes, readable and writable. -/
def instDaten_muldiv : Abschnitt :=
  { dateiOff := 3, dateiLen := 8, vaddr := 0x2000, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 4096 }

/-- The muldiv image: biased base 0x100000, entry at the code base. -/
def instBild_muldiv : Bild :=
  { datei := instDatei_muldiv
    abschnitte := [instCode_muldiv, instDaten_muldiv]
    reloks := []
    eintraege := [0x101000]
    modus := .param 0x100000 }

/-- Muldiv core-0 registers: 6 in rax, 7 in rcx. -/
def instReg_muldiv : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 6
  else if q = Register.rcx then BitVec.ofNat 64 7
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Muldiv cores: core 0 fetches at the code base, core 1 idles on data. -/
def instKern_muldiv : Nat → HwKern
  | 0 => ⟨instReg_muldiv, zeugeFlags, BitVec.ofNat 64 0x101000,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0x102000, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Muldiv start machine: loaded image memory, two cores, empty buffers. -/
def instStart_muldiv : HwMaschine :=
  ⟨geladen instBild_muldiv 0x100000, instKern_muldiv, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- ACCEPTANCE: the muldiv image validates under profile 48. -/
theorem inst_wohlgeformt_muldiv :
    wohlgeformt .p48 instBild_muldiv = true := by
  decide

/-- The muldiv machine is well-formed: full silicon admits all. -/
theorem instStart_wf_muldiv : HwWf instStart_muldiv := by
  apply hwWf_aus_zugelassen
  intro c f
  cases f with
  | skalar64 => rfl
  | skalar32 => rfl
  | sseDoppel =>
    show merkmalZugelassen basisHw basisBereit .sseDoppel = true
    decide
  | paketInt128 =>
    show merkmalZugelassen basisHw basisBereit .paketInt128 = true
    decide

/-- FETCH: core 0 fetches the MUL row whole from its loaded image. -/
theorem inst_fetch_muldiv :
    fetchExt (projFp instStart_muldiv 0)
      (geholt (projZustand instStart_muldiv 0)) =
      some (.muldiv ⟨.mulRax .rcx, 3⟩, []) := by
  decide

/-- STEP: the MUL step advances RIP past the 3-byte row. -/
theorem inst_rip_muldiv :
    hwRipOut (hwByteschrittReg instStart_muldiv 0) 0 =
      some (BitVec.ofNat 64 0x101003) := by
  decide

/-- STEP: 6 times 7 lands in rax, the high word in rdx is zero. -/
theorem inst_wert_muldiv :
    hwRegOut (hwByteschrittReg instStart_muldiv 0) 0 .rax =
        some (BitVec.ofNat 64 42) ∧
      hwRegOut (hwByteschrittReg instStart_muldiv 0) 0 .rdx =
        some (BitVec.ofNat 64 0) := by
  decide

/-- STEP: the register-only MUL leaves shared memory alone. -/
theorem inst_mem_still_muldiv :
    hwMemOut (hwByteschrittReg instStart_muldiv 0) instAdr =
      some (BitVec.ofNat 8 0) := by
  decide

/-- STEP: the register-only MUL issues no buffer entry. -/
theorem inst_puffer_leer_muldiv :
    hwBufOut (hwByteschrittReg instStart_muldiv 0) 0 = some 0 := by
  decide

/-- The MUL successor state over the core projection. -/
def instT_muldiv : FpZustand :=
  { projFp instStart_muldiv 0 with kern :=
    { (projFp instStart_muldiv 0).kern with
      register :=
        regSet
          (regSet (projFp instStart_muldiv 0).kern.register Register.rax
            (mulLow .b64 ((projFp instStart_muldiv 0).kern.register Register.rax)
              ((projFp instStart_muldiv 0).kern.register Register.rcx)))
          Register.rdx
          (mulHighU .b64 ((projFp instStart_muldiv 0).kern.register Register.rax)
            ((projFp instStart_muldiv 0).kern.register Register.rcx)),
      rip := ripNach (projFp instStart_muldiv 0).kern.rip 3,
      flags :=
        mulFlagsU (projFp instStart_muldiv 0).kern.flags
          ((projFp instStart_muldiv 0).kern.register Register.rax)
          ((projFp instStart_muldiv 0).kern.register Register.rcx) } }

/-- AGREEMENT: the MUL step IS the accepted evaluator on the projection. -/
theorem inst_schritt_muldiv :
    stepExt (.muldiv ⟨.mulRax .rcx, 3⟩) (projFp instStart_muldiv 0)
        (instStart_muldiv.bereit 0) = .weiter instT_muldiv := by
  apply stepExt_muldiv_ok
  have hok : laengeOk 3 = true := by decide
  have h := md_mul_erfolg ⟨.mulRax .rcx, 3⟩
    (projFp instStart_muldiv 0).kern .rcx hok rfl
  exact h

/-- The MUL successor keeps the shared loaded memory. -/
theorem inst_mem_muldiv : instT_muldiv.kern.speicher = instStart_muldiv.mem := by
  rfl

/-- HW STEP: the fetched MUL row is a coherent `reg` machine step. -/
theorem inst_reg_muldiv :
    HwSchritt instStart_muldiv (setKernVonFp instStart_muldiv 0 instT_muldiv)
      (.regAusf 0 (.muldiv ⟨.mulRax .rcx, 3⟩)) :=
  .reg 0 _ _ inst_schritt_muldiv inst_mem_muldiv

/-- Core 0 issues byte 42 at the data cell. -/
def instTso1_muldiv : Option TSOZustand :=
  issueByte (tsoAnsicht instStart_muldiv) 0 instAdr (BitVec.ofNat 8 42)

/-- Core 0 observes its own byte (forwarding). -/
def instLoadEigen_muldiv : Option (Option Byte) :=
  match instTso1_muldiv with
  | some s => some (loadByte s 0 instAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def instLoadFremd_muldiv : Option (Option Byte) :=
  match instTso1_muldiv with
  | some s => some (loadByte s 1 instAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def instTso2_muldiv : Option TSOZustand :=
  match instTso1_muldiv with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def instNachFlush_muldiv : Option (Option Byte) :=
  match instTso2_muldiv with
  | some s => some (some (s.mem.bytes instAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def instFremdNachFlush_muldiv : Option (Option Byte) :=
  match instTso2_muldiv with
  | some s => some (loadByte s 1 instAdr)
  | none => none

/-- The data cell starts zeroed: the run really changes memory. -/
theorem inst_anfang_null_muldiv :
    instStart_muldiv.mem.bytes instAdr = BitVec.ofNat 8 0 := by
  decide

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem inst_weiterleitung_muldiv :
    instLoadEigen_muldiv = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem inst_fremd_alt_muldiv :
    instLoadFremd_muldiv = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem inst_spuelung_aendert_speicher_muldiv :
    instNachFlush_muldiv = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem inst_fremd_neu_muldiv :
    instFremdNachFlush_muldiv = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- Core 1 refuses: its RIP points at non-executable loaded memory. -/
theorem inst_kern1_verweigert_muldiv :
    hwByteschrittReg instStart_muldiv 1 = .verweigert := by
  apply hwBild_ohne_exec_verweigert
  decide

/-- The dark image: same bytes, code section not executable. -/
def instBildDunkel_muldiv : Bild :=
  { instBild_muldiv with
    abschnitte := [{ instCode_muldiv with ausfuehrbar := false },
      instDaten_muldiv] }

/-- The dark machine: same cores over the non-executable mapping. -/
def instDunkel_muldiv : HwMaschine :=
  { instStart_muldiv with mem := geladen instBildDunkel_muldiv 0x100000 }

/-- PLANTED REFUSAL: on the non-executable mapping the fetch refuses. -/
theorem inst_dunkel_fetch_muldiv :
    fetchExt (projFp instDunkel_muldiv 0)
      (geholt (projZustand instDunkel_muldiv 0)) = none := by
  decide

/-- PLANTED REFUSAL: on the non-executable mapping the Hw step refuses. -/
theorem inst_dunkel_verweigert_muldiv :
    hwByteschrittReg instDunkel_muldiv 0 = .verweigert :=
  hwByteschrittReg_verweigert _ _ inst_dunkel_fetch_muldiv

/-- JOINT WITNESS (muldiv): accepted image, fetched MUL row, register
    step with RDX:RAX = 6 * 7, owner-only forwarding, drain changing
    shared memory 0 to 42 observed from both cores, with the
    data-section and dark-mapping refusals beside it. -/
theorem inst_zeuge_muldiv :
    wohlgeformt .p48 instBild_muldiv = true ∧
      HwWf instStart_muldiv ∧
      fetchExt (projFp instStart_muldiv 0)
        (geholt (projZustand instStart_muldiv 0)) =
        some (.muldiv ⟨.mulRax .rcx, 3⟩, []) ∧
      hwRipOut (hwByteschrittReg instStart_muldiv 0) 0 =
        some (BitVec.ofNat 64 0x101003) ∧
      hwRegOut (hwByteschrittReg instStart_muldiv 0) 0 .rax =
        some (BitVec.ofNat 64 42) ∧
      hwMemOut (hwByteschrittReg instStart_muldiv 0) instAdr =
        some (BitVec.ofNat 8 0) ∧
      instLoadEigen_muldiv = some (some (BitVec.ofNat 8 42)) ∧
      instLoadFremd_muldiv = some (some (BitVec.ofNat 8 0)) ∧
      instNachFlush_muldiv = some (some (BitVec.ofNat 8 42)) ∧
      instFremdNachFlush_muldiv = some (some (BitVec.ofNat 8 42)) ∧
      hwByteschrittReg instStart_muldiv 1 = .verweigert ∧
      hwByteschrittReg instDunkel_muldiv 0 = .verweigert := by
  refine ⟨inst_wohlgeformt_muldiv, instStart_wf_muldiv, inst_fetch_muldiv,
    inst_rip_muldiv, inst_wert_muldiv.1, inst_mem_still_muldiv,
    inst_weiterleitung_muldiv, inst_fremd_alt_muldiv,
    inst_spuelung_aendert_speicher_muldiv, inst_fremd_neu_muldiv,
    inst_kern1_verweigert_muldiv, inst_dunkel_verweigert_muldiv⟩
