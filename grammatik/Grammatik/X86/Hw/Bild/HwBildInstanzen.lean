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
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Speicher.Speicher
import Grammatik.X86.TSO.Kern.TSO
import Grammatik.X86.Kern.Byteschritt
import Grammatik.X86.Kern.Bild
import Grammatik.X86.Laden.LoadedExecution
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Grundlage.ExtendedExecution
import Grammatik.X86.Hw.Bild.HwLoadedImage
import Grammatik.X86.Hw.Bild.HwBildFamilien
import Grammatik.X86.Befehle.Arithmetik.MulDiv
import Grammatik.X86.Befehle.Arithmetik.ShiftCodec
import Grammatik.X86.Befehle.Kontrolle.ControlCodec
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat
import Grammatik.X86.Befehle.Vektor.VectorCodec

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

/-- The muldiv witness proposition: accepted image, fetched row,
    register step, TSO leg and refusals, as one conjunction. -/
def instZeugeProp_muldiv : Prop :=
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
      hwByteschrittReg instDunkel_muldiv 0 = .verweigert

/-- JOINT WITNESS (muldiv): accepted image, fetched MUL row, register
    step with RDX:RAX = 6 * 7, owner-only forwarding, drain changing
    shared memory 0 to 42 observed from both cores, with the
    data-section and dark-mapping refusals beside it. -/
theorem inst_zeuge_muldiv : instZeugeProp_muldiv := by
  unfold instZeugeProp_muldiv
  refine ⟨inst_wohlgeformt_muldiv, instStart_wf_muldiv, inst_fetch_muldiv,
    inst_rip_muldiv, inst_wert_muldiv.1, inst_mem_still_muldiv,
    inst_weiterleitung_muldiv, inst_fremd_alt_muldiv,
    inst_spuelung_aendert_speicher_muldiv, inst_fremd_neu_muldiv,
    inst_kern1_verweigert_muldiv, inst_dunkel_verweigert_muldiv⟩

/-! ## Shift instance: `shl rax, 1` over its own loaded image. -/

/-- Shift image bytes: the 4-byte SHL row then eight data zeroes. -/
def instDatei_shift : List Byte :=
  encodeShift (.imm .shl .rax 1) ++ List.replicate 8 (natByte 0)

/-- Shift code section: execute-only, exactly the 4 row bytes. -/
def instCode_shift : Abschnitt :=
  { dateiOff := 0, dateiLen := 4, vaddr := 0x1000, memLen := 4,
    lesbar := false, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Shift data section: eight bytes, readable and writable. -/
def instDaten_shift : Abschnitt :=
  { dateiOff := 4, dateiLen := 8, vaddr := 0x2000, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 4096 }

/-- The shift image: biased base 0x100000, entry at the code base. -/
def instBild_shift : Bild :=
  { datei := instDatei_shift
    abschnitte := [instCode_shift, instDaten_shift]
    reloks := []
    eintraege := [0x101000]
    modus := .param 0x100000 }

/-- Shift core-0 registers: 21 in rax. -/
def instReg_shift : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 21
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Shift cores: core 0 fetches at the code base, core 1 idles on data. -/
def instKern_shift : Nat → HwKern
  | 0 => ⟨instReg_shift, zeugeFlags, BitVec.ofNat 64 0x101000,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0x102000, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Shift start machine: loaded image memory, two cores, empty buffers. -/
def instStart_shift : HwMaschine :=
  ⟨geladen instBild_shift 0x100000, instKern_shift, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- ACCEPTANCE: the shift image validates under profile 48. -/
theorem inst_wohlgeformt_shift :
    wohlgeformt .p48 instBild_shift = true := by
  decide

/-- The shift machine is well-formed: full silicon admits all. -/
theorem instStart_wf_shift : HwWf instStart_shift := by
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

/-- FETCH: core 0 fetches the SHL row whole from its loaded image. -/
theorem inst_fetch_shift :
    fetchExt (projFp instStart_shift 0)
      (geholt (projZustand instStart_shift 0)) =
      some (.shift ⟨.imm .shl .rax 1, 4⟩, []) := by
  decide

/-- STEP: the SHL step advances RIP past the 4-byte row. -/
theorem inst_rip_shift :
    hwRipOut (hwByteschrittReg instStart_shift 0) 0 =
      some (BitVec.ofNat 64 0x101004) := by
  decide

/-- STEP: 21 shifted left once is 42 in rax. -/
theorem inst_wert_shift :
    hwRegOut (hwByteschrittReg instStart_shift 0) 0 .rax =
      some (BitVec.ofNat 64 42) := by
  decide

/-- STEP: the register-only SHL leaves shared memory alone. -/
theorem inst_mem_still_shift :
    hwMemOut (hwByteschrittReg instStart_shift 0) instAdr =
      some (BitVec.ofNat 8 0) := by
  decide

/-- STEP: the register-only SHL issues no buffer entry. -/
theorem inst_puffer_leer_shift :
    hwBufOut (hwByteschrittReg instStart_shift 0) 0 = some 0 := by
  decide

/-- The SHL successor state over the core projection. -/
def instKernNach_shift : Zustand :=
  schrittRegister (projFp instStart_shift 0).kern
    (ripNach (projFp instStart_shift 0).kern.rip 4)
    (shiftFlags (shiftNachweis (.imm .shl .rax 1)
      (projFp instStart_shift 0).kern))
    (shiftDst (.imm .shl .rax 1))
    (shiftNachweis (.imm .shl .rax 1)
      (projFp instStart_shift 0).kern).ergebnis

/-- The SHL successor state over the core projection. -/
def instT_shift : FpZustand :=
  { projFp instStart_shift 0 with kern := instKernNach_shift }

/-- AGREEMENT: the SHL step IS the accepted evaluator on the projection. -/
theorem inst_schritt_shift :
    stepExt (.shift ⟨.imm .shl .rax 1, 4⟩) (projFp instStart_shift 0)
        (instStart_shift.bereit 0) = .weiter instT_shift := by
  apply stepExt_shift
  have hlen : (⟨.imm .shl .rax 1, 4⟩ : ShiftDecodiert).laenge ==
      shiftLaenge (⟨.imm .shl .rax 1, 4⟩ : ShiftDecodiert).befehl := by
    decide
  have h0 : schiebeZaehler .b64
      (shiftZaehler (.imm .shl .rax 1)
        (projFp instStart_shift 0).kern) ≠ 0 := by
    decide
  have h := shiftSchritt_weiter ⟨.imm .shl .rax 1, 4⟩
    (projFp instStart_shift 0).kern hlen h0
  exact h

/-- The SHL successor keeps the shared loaded memory. -/
theorem inst_mem_shift : instT_shift.kern.speicher = instStart_shift.mem := by
  rfl

/-- HW STEP: the fetched SHL row is a coherent `reg` machine step. -/
theorem inst_reg_shift :
    HwSchritt instStart_shift (setKernVonFp instStart_shift 0 instT_shift)
      (.regAusf 0 (.shift ⟨.imm .shl .rax 1, 4⟩)) :=
  .reg 0 _ _ inst_schritt_shift inst_mem_shift

/-- Core 0 issues byte 42 at the data cell. -/
def instTso1_shift : Option TSOZustand :=
  issueByte (tsoAnsicht instStart_shift) 0 instAdr (BitVec.ofNat 8 42)

/-- Core 0 observes its own byte (forwarding). -/
def instLoadEigen_shift : Option (Option Byte) :=
  match instTso1_shift with
  | some s => some (loadByte s 0 instAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def instLoadFremd_shift : Option (Option Byte) :=
  match instTso1_shift with
  | some s => some (loadByte s 1 instAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def instTso2_shift : Option TSOZustand :=
  match instTso1_shift with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def instNachFlush_shift : Option (Option Byte) :=
  match instTso2_shift with
  | some s => some (some (s.mem.bytes instAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def instFremdNachFlush_shift : Option (Option Byte) :=
  match instTso2_shift with
  | some s => some (loadByte s 1 instAdr)
  | none => none

/-- The data cell starts zeroed: the run really changes memory. -/
theorem inst_anfang_null_shift :
    instStart_shift.mem.bytes instAdr = BitVec.ofNat 8 0 := by
  decide

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem inst_weiterleitung_shift :
    instLoadEigen_shift = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem inst_fremd_alt_shift :
    instLoadFremd_shift = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem inst_spuelung_aendert_speicher_shift :
    instNachFlush_shift = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem inst_fremd_neu_shift :
    instFremdNachFlush_shift = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- Core 1 refuses: its RIP points at non-executable loaded memory. -/
theorem inst_kern1_verweigert_shift :
    hwByteschrittReg instStart_shift 1 = .verweigert := by
  apply hwBild_ohne_exec_verweigert
  decide

/-- The dark image: same bytes, code section not executable. -/
def instBildDunkel_shift : Bild :=
  { instBild_shift with
    abschnitte := [{ instCode_shift with ausfuehrbar := false },
      instDaten_shift] }

/-- The dark machine: same cores over the non-executable mapping. -/
def instDunkel_shift : HwMaschine :=
  { instStart_shift with mem := geladen instBildDunkel_shift 0x100000 }

/-- PLANTED REFUSAL: on the non-executable mapping the fetch refuses. -/
theorem inst_dunkel_fetch_shift :
    fetchExt (projFp instDunkel_shift 0)
      (geholt (projZustand instDunkel_shift 0)) = none := by
  decide

/-- PLANTED REFUSAL: on the non-executable mapping the Hw step refuses. -/
theorem inst_dunkel_verweigert_shift :
    hwByteschrittReg instDunkel_shift 0 = .verweigert :=
  hwByteschrittReg_verweigert _ _ inst_dunkel_fetch_shift

/-- The shift witness proposition: accepted image, fetched row,
    register step, TSO leg and refusals, as one conjunction. -/
def instZeugeProp_shift : Prop :=
  wohlgeformt .p48 instBild_shift = true ∧
      HwWf instStart_shift ∧
      fetchExt (projFp instStart_shift 0)
        (geholt (projZustand instStart_shift 0)) =
        some (.shift ⟨.imm .shl .rax 1, 4⟩, []) ∧
      hwRipOut (hwByteschrittReg instStart_shift 0) 0 =
        some (BitVec.ofNat 64 0x101004) ∧
      hwRegOut (hwByteschrittReg instStart_shift 0) 0 .rax =
        some (BitVec.ofNat 64 42) ∧
      hwMemOut (hwByteschrittReg instStart_shift 0) instAdr =
        some (BitVec.ofNat 8 0) ∧
      instLoadEigen_shift = some (some (BitVec.ofNat 8 42)) ∧
      instLoadFremd_shift = some (some (BitVec.ofNat 8 0)) ∧
      instNachFlush_shift = some (some (BitVec.ofNat 8 42)) ∧
      instFremdNachFlush_shift = some (some (BitVec.ofNat 8 42)) ∧
      hwByteschrittReg instStart_shift 1 = .verweigert ∧
      hwByteschrittReg instDunkel_shift 0 = .verweigert

/-- JOINT WITNESS (shift): accepted image, fetched SHL row, register
    step with rax = 21 << 1, owner-only forwarding, drain changing
    shared memory 0 to 42 observed from both cores, with the
    data-section and dark-mapping refusals beside it. -/
theorem inst_zeuge_shift : instZeugeProp_shift := by
  unfold instZeugeProp_shift
  refine ⟨inst_wohlgeformt_shift, instStart_wf_shift, inst_fetch_shift,
    inst_rip_shift, inst_wert_shift, inst_mem_still_shift,
    inst_weiterleitung_shift, inst_fremd_alt_shift,
    inst_spuelung_aendert_speicher_shift, inst_fremd_neu_shift,
    inst_kern1_verweigert_shift, inst_dunkel_verweigert_shift⟩

/-! ## Setcc instance: `sete rax` over its own loaded image. -/

/-- Setcc image bytes: the 4-byte SETcc row then eight data zeroes. -/
def instDatei_setcc : List Byte :=
  encodeSetCC .e .rax ++ List.replicate 8 (natByte 0)

/-- Setcc code section: execute-only, exactly the 4 row bytes. -/
def instCode_setcc : Abschnitt :=
  { dateiOff := 0, dateiLen := 4, vaddr := 0x1000, memLen := 4,
    lesbar := false, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Setcc data section: eight bytes, readable and writable. -/
def instDaten_setcc : Abschnitt :=
  { dateiOff := 4, dateiLen := 8, vaddr := 0x2000, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 4096 }

/-- The setcc image: biased base 0x100000, entry at the code base. -/
def instBild_setcc : Bild :=
  { datei := instDatei_setcc
    abschnitte := [instCode_setcc, instDaten_setcc]
    reloks := []
    eintraege := [0x101000]
    modus := .param 0x100000 }

/-- Setcc core-0 registers: 10 in rax. -/
def instReg_setcc : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 10
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Setcc cores: core 0 fetches with the zero flag set, core 1 idles. -/
def instKern_setcc : Nat → HwKern
  | 0 => ⟨instReg_setcc, zeugeFlagsGleich, BitVec.ofNat 64 0x101000,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0x102000, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Setcc start machine: loaded image memory, two cores, empty buffers. -/
def instStart_setcc : HwMaschine :=
  ⟨geladen instBild_setcc 0x100000, instKern_setcc, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- ACCEPTANCE: the setcc image validates under profile 48. -/
theorem inst_wohlgeformt_setcc :
    wohlgeformt .p48 instBild_setcc = true := by
  decide

/-- The setcc machine is well-formed: full silicon admits all. -/
theorem instStart_wf_setcc : HwWf instStart_setcc := by
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

/-- FETCH: core 0 fetches the SETcc row whole from its loaded image. -/
theorem inst_fetch_setcc :
    fetchExt (projFp instStart_setcc 0)
      (geholt (projZustand instStart_setcc 0)) =
      some (.setcc .e .rax 4, []) := by
  decide

/-- STEP: the SETcc step advances RIP past the 4-byte row. -/
theorem inst_rip_setcc :
    hwRipOut (hwByteschrittReg instStart_setcc 0) 0 =
      some (BitVec.ofNat 64 0x101004) := by
  decide

/-- STEP: with the zero flag set, the low byte of rax becomes 1. -/
theorem inst_wert_setcc :
    hwRegOut (hwByteschrittReg instStart_setcc 0) 0 .rax =
      some (BitVec.ofNat 64 1) := by
  decide

/-- STEP: the register-only SETcc leaves shared memory alone. -/
theorem inst_mem_still_setcc :
    hwMemOut (hwByteschrittReg instStart_setcc 0) instAdr =
      some (BitVec.ofNat 8 0) := by
  decide

/-- STEP: the register-only SETcc issues no buffer entry. -/
theorem inst_puffer_leer_setcc :
    hwBufOut (hwByteschrittReg instStart_setcc 0) 0 = some 0 := by
  decide

/-- The SETcc successor core over the core projection. -/
def instKernNach_setcc : Zustand :=
  { setCCAnwenden (projFp instStart_setcc 0).kern .rax .e with
    rip := ripNach (projFp instStart_setcc 0).kern.rip 4 }

/-- The SETcc successor state over the core projection. -/
def instT_setcc : FpZustand :=
  { projFp instStart_setcc 0 with kern := instKernNach_setcc }

/-- AGREEMENT: the SETcc step IS the accepted evaluator on the projection. -/
theorem inst_schritt_setcc :
    stepExt (.setcc .e .rax 4) (projFp instStart_setcc 0)
        (instStart_setcc.bereit 0) = .weiter instT_setcc := by
  apply stepExt_setcc
  have hok : laengeOk 4 = true := by decide
  have h : setccSchrittBytes 4 (projFp instStart_setcc 0).kern .rax .e =
      some instKernNach_setcc := by
    unfold setccSchrittBytes instKernNach_setcc
    rw [hok]
  exact h

/-- The SETcc successor keeps the shared loaded memory. -/
theorem inst_mem_setcc : instT_setcc.kern.speicher = instStart_setcc.mem := by
  rfl

/-- HW STEP: the fetched SETcc row is a coherent `reg` machine step. -/
theorem inst_reg_setcc :
    HwSchritt instStart_setcc (setKernVonFp instStart_setcc 0 instT_setcc)
      (.regAusf 0 (.setcc .e .rax 4)) :=
  .reg 0 _ _ inst_schritt_setcc inst_mem_setcc

/-- Core 0 issues byte 42 at the data cell. -/
def instTso1_setcc : Option TSOZustand :=
  issueByte (tsoAnsicht instStart_setcc) 0 instAdr (BitVec.ofNat 8 42)

/-- Core 0 observes its own byte (forwarding). -/
def instLoadEigen_setcc : Option (Option Byte) :=
  match instTso1_setcc with
  | some s => some (loadByte s 0 instAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def instLoadFremd_setcc : Option (Option Byte) :=
  match instTso1_setcc with
  | some s => some (loadByte s 1 instAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def instTso2_setcc : Option TSOZustand :=
  match instTso1_setcc with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def instNachFlush_setcc : Option (Option Byte) :=
  match instTso2_setcc with
  | some s => some (some (s.mem.bytes instAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def instFremdNachFlush_setcc : Option (Option Byte) :=
  match instTso2_setcc with
  | some s => some (loadByte s 1 instAdr)
  | none => none

/-- The data cell starts zeroed: the run really changes memory. -/
theorem inst_anfang_null_setcc :
    instStart_setcc.mem.bytes instAdr = BitVec.ofNat 8 0 := by
  decide

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem inst_weiterleitung_setcc :
    instLoadEigen_setcc = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem inst_fremd_alt_setcc :
    instLoadFremd_setcc = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem inst_spuelung_aendert_speicher_setcc :
    instNachFlush_setcc = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem inst_fremd_neu_setcc :
    instFremdNachFlush_setcc = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- Core 1 refuses: its RIP points at non-executable loaded memory. -/
theorem inst_kern1_verweigert_setcc :
    hwByteschrittReg instStart_setcc 1 = .verweigert := by
  apply hwBild_ohne_exec_verweigert
  decide

/-- The dark image: same bytes, code section not executable. -/
def instBildDunkel_setcc : Bild :=
  { instBild_setcc with
    abschnitte := [{ instCode_setcc with ausfuehrbar := false },
      instDaten_setcc] }

/-- The dark machine: same cores over the non-executable mapping. -/
def instDunkel_setcc : HwMaschine :=
  { instStart_setcc with mem := geladen instBildDunkel_setcc 0x100000 }

/-- PLANTED REFUSAL: on the non-executable mapping the fetch refuses. -/
theorem inst_dunkel_fetch_setcc :
    fetchExt (projFp instDunkel_setcc 0)
      (geholt (projZustand instDunkel_setcc 0)) = none := by
  decide

/-- PLANTED REFUSAL: on the non-executable mapping the Hw step refuses. -/
theorem inst_dunkel_verweigert_setcc :
    hwByteschrittReg instDunkel_setcc 0 = .verweigert :=
  hwByteschrittReg_verweigert _ _ inst_dunkel_fetch_setcc

/-- The setcc witness proposition: accepted image, fetched row,
    register step, TSO leg and refusals, as one conjunction. -/
def instZeugeProp_setcc : Prop :=
  wohlgeformt .p48 instBild_setcc = true ∧
      HwWf instStart_setcc ∧
      fetchExt (projFp instStart_setcc 0)
        (geholt (projZustand instStart_setcc 0)) =
        some (.setcc .e .rax 4, []) ∧
      hwRipOut (hwByteschrittReg instStart_setcc 0) 0 =
        some (BitVec.ofNat 64 0x101004) ∧
      hwRegOut (hwByteschrittReg instStart_setcc 0) 0 .rax =
        some (BitVec.ofNat 64 1) ∧
      hwMemOut (hwByteschrittReg instStart_setcc 0) instAdr =
        some (BitVec.ofNat 8 0) ∧
      instLoadEigen_setcc = some (some (BitVec.ofNat 8 42)) ∧
      instLoadFremd_setcc = some (some (BitVec.ofNat 8 0)) ∧
      instNachFlush_setcc = some (some (BitVec.ofNat 8 42)) ∧
      instFremdNachFlush_setcc = some (some (BitVec.ofNat 8 42)) ∧
      hwByteschrittReg instStart_setcc 1 = .verweigert ∧
      hwByteschrittReg instDunkel_setcc 0 = .verweigert

/-- JOINT WITNESS (setcc): accepted image, fetched SETcc row, taken
    step with al = 1, owner-only forwarding, drain changing shared
    memory 0 to 42 observed from both cores, with the data-section
    and dark-mapping refusals beside it. -/
theorem inst_zeuge_setcc : instZeugeProp_setcc := by
  unfold instZeugeProp_setcc
  refine ⟨inst_wohlgeformt_setcc, instStart_wf_setcc, inst_fetch_setcc,
    inst_rip_setcc, inst_wert_setcc, inst_mem_still_setcc,
    inst_weiterleitung_setcc, inst_fremd_alt_setcc,
    inst_spuelung_aendert_speicher_setcc, inst_fremd_neu_setcc,
    inst_kern1_verweigert_setcc, inst_dunkel_verweigert_setcc⟩

/-! ## Cmov instance: `cmove rax, rcx` over its own loaded image. -/

/-- Cmov image bytes: the 4-byte CMOV row then eight data zeroes. -/
def instDatei_cmov : List Byte :=
  encodeCmov .e .rax .rcx ++ List.replicate 8 (natByte 0)

/-- Cmov code section: execute-only, exactly the 4 row bytes. -/
def instCode_cmov : Abschnitt :=
  { dateiOff := 0, dateiLen := 4, vaddr := 0x1000, memLen := 4,
    lesbar := false, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Cmov data section: eight bytes, readable and writable. -/
def instDaten_cmov : Abschnitt :=
  { dateiOff := 4, dateiLen := 8, vaddr := 0x2000, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 4096 }

/-- The cmov image: biased base 0x100000, entry at the code base. -/
def instBild_cmov : Bild :=
  { datei := instDatei_cmov
    abschnitte := [instCode_cmov, instDaten_cmov]
    reloks := []
    eintraege := [0x101000]
    modus := .param 0x100000 }

/-- Cmov core-0 registers: 5 in rax, 9 in rcx. -/
def instReg_cmov : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 5
  else if q = Register.rcx then BitVec.ofNat 64 9
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Cmov cores: core 0 fetches with the zero flag set, core 1 idles. -/
def instKern_cmov : Nat → HwKern
  | 0 => ⟨instReg_cmov, zeugeFlagsGleich, BitVec.ofNat 64 0x101000,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0x102000, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Cmov start machine: loaded image memory, two cores, empty buffers. -/
def instStart_cmov : HwMaschine :=
  ⟨geladen instBild_cmov 0x100000, instKern_cmov, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- ACCEPTANCE: the cmov image validates under profile 48. -/
theorem inst_wohlgeformt_cmov :
    wohlgeformt .p48 instBild_cmov = true := by
  decide

/-- The cmov machine is well-formed: full silicon admits all. -/
theorem instStart_wf_cmov : HwWf instStart_cmov := by
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

/-- FETCH: core 0 fetches the CMOV row whole from its loaded image. -/
theorem inst_fetch_cmov :
    fetchExt (projFp instStart_cmov 0)
      (geholt (projZustand instStart_cmov 0)) =
      some (.cmov .e .rax .rcx 4, []) := by
  decide

/-- STEP: the CMOV step advances RIP past the 4-byte row. -/
theorem inst_rip_cmov :
    hwRipOut (hwByteschrittReg instStart_cmov 0) 0 =
      some (BitVec.ofNat 64 0x101004) := by
  decide

/-- STEP: with the zero flag set, rax takes the rcx value 9. -/
theorem inst_wert_cmov :
    hwRegOut (hwByteschrittReg instStart_cmov 0) 0 .rax =
      some (BitVec.ofNat 64 9) := by
  decide

/-- STEP: the register-only CMOV leaves shared memory alone. -/
theorem inst_mem_still_cmov :
    hwMemOut (hwByteschrittReg instStart_cmov 0) instAdr =
      some (BitVec.ofNat 8 0) := by
  decide

/-- STEP: the register-only CMOV issues no buffer entry. -/
theorem inst_puffer_leer_cmov :
    hwBufOut (hwByteschrittReg instStart_cmov 0) 0 = some 0 := by
  decide

/-- The CMOV successor core over the core projection. -/
def instKernNach_cmov : Zustand :=
  { cmovAnwenden (projFp instStart_cmov 0).kern .rax .rcx .e with
    rip := ripNach (projFp instStart_cmov 0).kern.rip 4 }

/-- The CMOV successor state over the core projection. -/
def instT_cmov : FpZustand :=
  { projFp instStart_cmov 0 with kern := instKernNach_cmov }

/-- AGREEMENT: the CMOV step IS the accepted evaluator on the projection. -/
theorem inst_schritt_cmov :
    stepExt (.cmov .e .rax .rcx 4) (projFp instStart_cmov 0)
        (instStart_cmov.bereit 0) = .weiter instT_cmov := by
  apply stepExt_cmov
  have hok : laengeOk 4 = true := by decide
  have h : cmovSchrittBytes 4 (projFp instStart_cmov 0).kern
      .rax .rcx .e = some instKernNach_cmov := by
    unfold cmovSchrittBytes instKernNach_cmov
    rw [hok]
  exact h

/-- The CMOV successor keeps the shared loaded memory. -/
theorem inst_mem_cmov : instT_cmov.kern.speicher = instStart_cmov.mem := by
  rfl

/-- HW STEP: the fetched CMOV row is a coherent `reg` machine step. -/
theorem inst_reg_cmov :
    HwSchritt instStart_cmov (setKernVonFp instStart_cmov 0 instT_cmov)
      (.regAusf 0 (.cmov .e .rax .rcx 4)) :=
  .reg 0 _ _ inst_schritt_cmov inst_mem_cmov

/-- Core 0 issues byte 42 at the data cell. -/
def instTso1_cmov : Option TSOZustand :=
  issueByte (tsoAnsicht instStart_cmov) 0 instAdr (BitVec.ofNat 8 42)

/-- Core 0 observes its own byte (forwarding). -/
def instLoadEigen_cmov : Option (Option Byte) :=
  match instTso1_cmov with
  | some s => some (loadByte s 0 instAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def instLoadFremd_cmov : Option (Option Byte) :=
  match instTso1_cmov with
  | some s => some (loadByte s 1 instAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def instTso2_cmov : Option TSOZustand :=
  match instTso1_cmov with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def instNachFlush_cmov : Option (Option Byte) :=
  match instTso2_cmov with
  | some s => some (some (s.mem.bytes instAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def instFremdNachFlush_cmov : Option (Option Byte) :=
  match instTso2_cmov with
  | some s => some (loadByte s 1 instAdr)
  | none => none

/-- The data cell starts zeroed: the run really changes memory. -/
theorem inst_anfang_null_cmov :
    instStart_cmov.mem.bytes instAdr = BitVec.ofNat 8 0 := by
  decide

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem inst_weiterleitung_cmov :
    instLoadEigen_cmov = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem inst_fremd_alt_cmov :
    instLoadFremd_cmov = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem inst_spuelung_aendert_speicher_cmov :
    instNachFlush_cmov = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem inst_fremd_neu_cmov :
    instFremdNachFlush_cmov = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- Core 1 refuses: its RIP points at non-executable loaded memory. -/
theorem inst_kern1_verweigert_cmov :
    hwByteschrittReg instStart_cmov 1 = .verweigert := by
  apply hwBild_ohne_exec_verweigert
  decide

/-- The dark image: same bytes, code section not executable. -/
def instBildDunkel_cmov : Bild :=
  { instBild_cmov with
    abschnitte := [{ instCode_cmov with ausfuehrbar := false },
      instDaten_cmov] }

/-- The dark machine: same cores over the non-executable mapping. -/
def instDunkel_cmov : HwMaschine :=
  { instStart_cmov with mem := geladen instBildDunkel_cmov 0x100000 }

/-- PLANTED REFUSAL: on the non-executable mapping the fetch refuses. -/
theorem inst_dunkel_fetch_cmov :
    fetchExt (projFp instDunkel_cmov 0)
      (geholt (projZustand instDunkel_cmov 0)) = none := by
  decide

/-- PLANTED REFUSAL: on the non-executable mapping the Hw step refuses. -/
theorem inst_dunkel_verweigert_cmov :
    hwByteschrittReg instDunkel_cmov 0 = .verweigert :=
  hwByteschrittReg_verweigert _ _ inst_dunkel_fetch_cmov

/-- The cmov witness proposition: accepted image, fetched row,
    register step, TSO leg and refusals, as one conjunction. -/
def instZeugeProp_cmov : Prop :=
  wohlgeformt .p48 instBild_cmov = true ∧
      HwWf instStart_cmov ∧
      fetchExt (projFp instStart_cmov 0)
        (geholt (projZustand instStart_cmov 0)) =
        some (.cmov .e .rax .rcx 4, []) ∧
      hwRipOut (hwByteschrittReg instStart_cmov 0) 0 =
        some (BitVec.ofNat 64 0x101004) ∧
      hwRegOut (hwByteschrittReg instStart_cmov 0) 0 .rax =
        some (BitVec.ofNat 64 9) ∧
      hwMemOut (hwByteschrittReg instStart_cmov 0) instAdr =
        some (BitVec.ofNat 8 0) ∧
      instLoadEigen_cmov = some (some (BitVec.ofNat 8 42)) ∧
      instLoadFremd_cmov = some (some (BitVec.ofNat 8 0)) ∧
      instNachFlush_cmov = some (some (BitVec.ofNat 8 42)) ∧
      instFremdNachFlush_cmov = some (some (BitVec.ofNat 8 42)) ∧
      hwByteschrittReg instStart_cmov 1 = .verweigert ∧
      hwByteschrittReg instDunkel_cmov 0 = .verweigert

/-- JOINT WITNESS (cmov): accepted image, fetched CMOV row, taken step
    with rax = 9, owner-only forwarding, drain changing shared memory
    0 to 42 observed from both cores, with the data-section and
    dark-mapping refusals beside it. -/
theorem inst_zeuge_cmov : instZeugeProp_cmov := by
  unfold instZeugeProp_cmov
  refine ⟨inst_wohlgeformt_cmov, instStart_wf_cmov, inst_fetch_cmov,
    inst_rip_cmov, inst_wert_cmov, inst_mem_still_cmov,
    inst_weiterleitung_cmov, inst_fremd_alt_cmov,
    inst_spuelung_aendert_speicher_cmov, inst_fremd_neu_cmov,
    inst_kern1_verweigert_cmov, inst_dunkel_verweigert_cmov⟩

/-! ## FP instance: `movsd xmm0, xmm1` over its own loaded image. -/

/-- FP image bytes: the 4-byte MOVSD row then eight data zeroes. -/
def instDatei_fp : List Byte :=
  fpEncodeMovsdRR .xmm0 .xmm1 ++ List.replicate 8 (natByte 0)

/-- FP code section: execute-only, exactly the 4 row bytes. -/
def instCode_fp : Abschnitt :=
  { dateiOff := 0, dateiLen := 4, vaddr := 0x1000, memLen := 4,
    lesbar := false, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- FP data section: eight bytes, readable and writable. -/
def instDaten_fp : Abschnitt :=
  { dateiOff := 4, dateiLen := 8, vaddr := 0x2000, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 4096 }

/-- The fp image: biased base 0x100000, entry at the code base. -/
def instBild_fp : Bild :=
  { datei := instDatei_fp
    abschnitte := [instCode_fp, instDaten_fp]
    reloks := []
    eintraege := [0x101000]
    modus := .param 0x100000 }

/-- FP core-0 XMM: the value as low double-word in xmm1. -/
def instXmm_fp : XmmDatei := fun q =>
  if q = .xmm1 then vecJoin (BitVec.ofNat 64 7) (BitVec.ofNat 64 0)
  else (BitVec.ofNat 128 0)

/-- FP cores: core 0 fetches at the code base, core 1 idles on data. -/
def instKern_fp : Nat → HwKern
  | 0 => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0x101000, instXmm_fp, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0x102000, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- FP start machine: loaded image memory, two cores, empty buffers. -/
def instStart_fp : HwMaschine :=
  ⟨geladen instBild_fp 0x100000, instKern_fp, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- ACCEPTANCE: the fp image validates under profile 48. -/
theorem inst_wohlgeformt_fp :
    wohlgeformt .p48 instBild_fp = true := by
  decide

/-- The fp machine is well-formed: full silicon admits all. -/
theorem instStart_wf_fp : HwWf instStart_fp := by
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

/-- FETCH: core 0 fetches the MOVSD row whole from its loaded image. -/
theorem inst_fetch_fp :
    fetchExt (projFp instStart_fp 0)
      (geholt (projZustand instStart_fp 0)) =
      some (.fp ⟨.movsdRR .xmm0 .xmm1, 4⟩, []) := by
  decide

/-- STEP: the MOVSD step advances RIP past the 4-byte row. -/
theorem inst_rip_fp :
    hwRipOut (hwByteschrittReg instStart_fp 0) 0 =
      some (BitVec.ofNat 64 0x101004) := by
  decide

/-- STEP: the low double-word 7 lands in xmm0. -/
theorem inst_wert_fp :
    hwXmmTiefOut (hwByteschrittReg instStart_fp 0) 0 .xmm0 =
      some (BitVec.ofNat 64 7) := by
  decide

/-- STEP: the register-only MOVSD leaves shared memory alone. -/
theorem inst_mem_still_fp :
    hwMemOut (hwByteschrittReg instStart_fp 0) instAdr =
      some (BitVec.ofNat 8 0) := by
  decide

/-- STEP: the register-only MOVSD issues no buffer entry. -/
theorem inst_puffer_leer_fp :
    hwBufOut (hwByteschrittReg instStart_fp 0) 0 = some 0 := by
  decide

/-- The MOVSD successor state over the core projection. -/
def instT_fp : FpZustand :=
  { projFp instStart_fp 0 with
    kern := { (projFp instStart_fp 0).kern with
      rip := ripNach (projFp instStart_fp 0).kern.rip 4 }
    xmm := xmmSchreibeTief (projFp instStart_fp 0).xmm .xmm0
      (xmmTief (projFp instStart_fp 0).xmm .xmm1) }

/-- AGREEMENT: the MOVSD step IS the accepted evaluator on the projection. -/
theorem inst_schritt_fp :
    stepExt (.fp ⟨.movsdRR .xmm0 .xmm1, 4⟩) (projFp instStart_fp 0)
        (instStart_fp.bereit 0) = .weiter instT_fp := by
  apply stepExt_fp
  have hok : laengeOk 4 = true := by decide
  have h := fpSchritt_movsdRR ⟨.movsdRR .xmm0 .xmm1, 4⟩
    (projFp instStart_fp 0) .xmm0 .xmm1 hok rfl rfl
  exact h

/-- The MOVSD successor keeps the shared loaded memory. -/
theorem inst_mem_fp : instT_fp.kern.speicher = instStart_fp.mem := by
  rfl

/-- HW STEP: the fetched MOVSD row is a coherent `reg` machine step. -/
theorem inst_reg_fp :
    HwSchritt instStart_fp (setKernVonFp instStart_fp 0 instT_fp)
      (.regAusf 0 (.fp ⟨.movsdRR .xmm0 .xmm1, 4⟩)) :=
  .reg 0 _ _ inst_schritt_fp inst_mem_fp

/-- Core 0 issues byte 42 at the data cell. -/
def instTso1_fp : Option TSOZustand :=
  issueByte (tsoAnsicht instStart_fp) 0 instAdr (BitVec.ofNat 8 42)

/-- Core 0 observes its own byte (forwarding). -/
def instLoadEigen_fp : Option (Option Byte) :=
  match instTso1_fp with
  | some s => some (loadByte s 0 instAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def instLoadFremd_fp : Option (Option Byte) :=
  match instTso1_fp with
  | some s => some (loadByte s 1 instAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def instTso2_fp : Option TSOZustand :=
  match instTso1_fp with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def instNachFlush_fp : Option (Option Byte) :=
  match instTso2_fp with
  | some s => some (some (s.mem.bytes instAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def instFremdNachFlush_fp : Option (Option Byte) :=
  match instTso2_fp with
  | some s => some (loadByte s 1 instAdr)
  | none => none

/-- The data cell starts zeroed: the run really changes memory. -/
theorem inst_anfang_null_fp :
    instStart_fp.mem.bytes instAdr = BitVec.ofNat 8 0 := by
  decide

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem inst_weiterleitung_fp :
    instLoadEigen_fp = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem inst_fremd_alt_fp :
    instLoadFremd_fp = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem inst_spuelung_aendert_speicher_fp :
    instNachFlush_fp = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem inst_fremd_neu_fp :
    instFremdNachFlush_fp = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- Core 1 refuses: its RIP points at non-executable loaded memory. -/
theorem inst_kern1_verweigert_fp :
    hwByteschrittReg instStart_fp 1 = .verweigert := by
  apply hwBild_ohne_exec_verweigert
  decide

/-- The dark image: same bytes, code section not executable. -/
def instBildDunkel_fp : Bild :=
  { instBild_fp with
    abschnitte := [{ instCode_fp with ausfuehrbar := false },
      instDaten_fp] }

/-- The dark machine: same cores over the non-executable mapping. -/
def instDunkel_fp : HwMaschine :=
  { instStart_fp with mem := geladen instBildDunkel_fp 0x100000 }

/-- PLANTED REFUSAL: on the non-executable mapping the fetch refuses. -/
theorem inst_dunkel_fetch_fp :
    fetchExt (projFp instDunkel_fp 0)
      (geholt (projZustand instDunkel_fp 0)) = none := by
  decide

/-- PLANTED REFUSAL: on the non-executable mapping the Hw step refuses. -/
theorem inst_dunkel_verweigert_fp :
    hwByteschrittReg instDunkel_fp 0 = .verweigert :=
  hwByteschrittReg_verweigert _ _ inst_dunkel_fetch_fp

/-- The fp witness proposition: accepted image, fetched row,
    register step, TSO leg and refusals, as one conjunction. -/
def instZeugeProp_fp : Prop :=
  wohlgeformt .p48 instBild_fp = true ∧
      HwWf instStart_fp ∧
      fetchExt (projFp instStart_fp 0)
        (geholt (projZustand instStart_fp 0)) =
        some (.fp ⟨.movsdRR .xmm0 .xmm1, 4⟩, []) ∧
      hwRipOut (hwByteschrittReg instStart_fp 0) 0 =
        some (BitVec.ofNat 64 0x101004) ∧
      hwXmmTiefOut (hwByteschrittReg instStart_fp 0) 0 .xmm0 =
        some (BitVec.ofNat 64 7) ∧
      hwMemOut (hwByteschrittReg instStart_fp 0) instAdr =
        some (BitVec.ofNat 8 0) ∧
      instLoadEigen_fp = some (some (BitVec.ofNat 8 42)) ∧
      instLoadFremd_fp = some (some (BitVec.ofNat 8 0)) ∧
      instNachFlush_fp = some (some (BitVec.ofNat 8 42)) ∧
      instFremdNachFlush_fp = some (some (BitVec.ofNat 8 42)) ∧
      hwByteschrittReg instStart_fp 1 = .verweigert ∧
      hwByteschrittReg instDunkel_fp 0 = .verweigert

/-- JOINT WITNESS (fp): accepted image, fetched MOVSD row, register
    step moving the low double-word, owner-only forwarding, drain
    changing shared memory 0 to 42 observed from both cores, with the
    data-section and dark-mapping refusals beside it. The family's own
    store form (`movsdSpeichere`) is NOT stepped here: it writes
    canonical memory and must use the TSO issue path, never `reg`. -/
theorem inst_zeuge_fp : instZeugeProp_fp := by
  unfold instZeugeProp_fp
  refine ⟨inst_wohlgeformt_fp, instStart_wf_fp, inst_fetch_fp,
    inst_rip_fp, inst_wert_fp, inst_mem_still_fp,
    inst_weiterleitung_fp, inst_fremd_alt_fp,
    inst_spuelung_aendert_speicher_fp, inst_fremd_neu_fp,
    inst_kern1_verweigert_fp, inst_dunkel_verweigert_fp⟩

/-! ## Vec instance: `pxor xmm0, xmm1` over its own loaded image. -/

/-- Vec image bytes: the 5-byte PXOR row then eight data zeroes. -/
def instDatei_vec : List Byte :=
  encodeVector (.pxorRR .xmm0 .xmm1) ++ List.replicate 8 (natByte 0)

/-- Vec code section: execute-only, exactly the 5 row bytes. -/
def instCode_vec : Abschnitt :=
  { dateiOff := 0, dateiLen := 5, vaddr := 0x1000, memLen := 5,
    lesbar := false, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Vec data section: eight bytes, readable and writable. -/
def instDaten_vec : Abschnitt :=
  { dateiOff := 5, dateiLen := 8, vaddr := 0x2000, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 4096 }

/-- The vec image: biased base 0x100000, entry at the code base. -/
def instBild_vec : Bild :=
  { datei := instDatei_vec
    abschnitte := [instCode_vec, instDaten_vec]
    reloks := []
    eintraege := [0x101000]
    modus := .param 0x100000 }

/-- Vec core-0 XMM: all ones in xmm0, the value 7 low in xmm1. -/
def instXmm_vec : XmmDatei := fun q =>
  if q = .xmm0 then vecJoin (BitVec.ofNat 64 18446744073709551615)
      (BitVec.ofNat 64 18446744073709551615)
  else if q = .xmm1 then vecJoin (BitVec.ofNat 64 7) (BitVec.ofNat 64 0)
  else (BitVec.ofNat 128 0)

/-- Vec cores: core 0 fetches at the code base, core 1 idles on data. -/
def instKern_vec : Nat → HwKern
  | 0 => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0x101000, instXmm_vec, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0x102000, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Vec start machine: loaded image memory, two cores, empty buffers. -/
def instStart_vec : HwMaschine :=
  ⟨geladen instBild_vec 0x100000, instKern_vec, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- ACCEPTANCE: the vec image validates under profile 48. -/
theorem inst_wohlgeformt_vec :
    wohlgeformt .p48 instBild_vec = true := by
  decide

/-- The vec machine is well-formed: full silicon admits all. -/
theorem instStart_wf_vec : HwWf instStart_vec := by
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

/-- FETCH: core 0 fetches the PXOR row whole from its loaded image. -/
theorem inst_fetch_vec :
    fetchExt (projFp instStart_vec 0)
      (geholt (projZustand instStart_vec 0)) =
      some (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩, []) := by
  decide

/-- STEP: the PXOR step advances RIP past the 5-byte row. -/
theorem inst_rip_vec :
    hwRipOut (hwByteschrittReg instStart_vec 0) 0 =
      some (BitVec.ofNat 64 0x101005) := by
  decide

/-- STEP: the low lane holds ones xor 7. -/
theorem inst_wert_vec :
    hwXmmTiefOut (hwByteschrittReg instStart_vec 0) 0 .xmm0 =
      some (BitVec.ofNat 64 18446744073709551608) := by
  decide

/-- STEP: the register-only PXOR leaves shared memory alone. -/
theorem inst_mem_still_vec :
    hwMemOut (hwByteschrittReg instStart_vec 0) instAdr =
      some (BitVec.ofNat 8 0) := by
  decide

/-- STEP: the register-only PXOR issues no buffer entry. -/
theorem inst_puffer_leer_vec :
    hwBufOut (hwByteschrittReg instStart_vec 0) 0 = some 0 := by
  decide

/-- The PXOR successor state over the core projection. -/
def instT_vec : FpZustand :=
  { projFp instStart_vec 0 with
    kern := { (projFp instStart_vec 0).kern with
      rip := ripNach (projFp instStart_vec 0).kern.rip 5 }
    xmm := xmmSet (projFp instStart_vec 0).xmm .xmm0
      (vecXor .b64 ((projFp instStart_vec 0).xmm .xmm0)
        ((projFp instStart_vec 0).xmm .xmm1)) }

/-- AGREEMENT: the PXOR step IS the accepted evaluator on the projection. -/
theorem inst_schritt_vec :
    stepExt (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩) (projFp instStart_vec 0)
        (instStart_vec.bereit 0) = .weiter instT_vec := by
  apply stepExt_vec
  have hok : laengeOk 5 = true := by decide
  have h := stepVector_pxor ⟨.pxorRR .xmm0 .xmm1, 5⟩
    (projFp instStart_vec 0) (instStart_vec.bereit 0)
    .xmm0 .xmm1 hok rfl rfl
  exact h

/-- The PXOR successor keeps the shared loaded memory. -/
theorem inst_mem_vec : instT_vec.kern.speicher = instStart_vec.mem := by
  rfl

/-- HW STEP: the fetched PXOR row is a coherent `reg` machine step. -/
theorem inst_reg_vec :
    HwSchritt instStart_vec (setKernVonFp instStart_vec 0 instT_vec)
      (.regAusf 0 (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩)) :=
  .reg 0 _ _ inst_schritt_vec inst_mem_vec

/-- Core 0 issues byte 42 at the data cell. -/
def instTso1_vec : Option TSOZustand :=
  issueByte (tsoAnsicht instStart_vec) 0 instAdr (BitVec.ofNat 8 42)

/-- Core 0 observes its own byte (forwarding). -/
def instLoadEigen_vec : Option (Option Byte) :=
  match instTso1_vec with
  | some s => some (loadByte s 0 instAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def instLoadFremd_vec : Option (Option Byte) :=
  match instTso1_vec with
  | some s => some (loadByte s 1 instAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def instTso2_vec : Option TSOZustand :=
  match instTso1_vec with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def instNachFlush_vec : Option (Option Byte) :=
  match instTso2_vec with
  | some s => some (some (s.mem.bytes instAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def instFremdNachFlush_vec : Option (Option Byte) :=
  match instTso2_vec with
  | some s => some (loadByte s 1 instAdr)
  | none => none

/-- The data cell starts zeroed: the run really changes memory. -/
theorem inst_anfang_null_vec :
    instStart_vec.mem.bytes instAdr = BitVec.ofNat 8 0 := by
  decide

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem inst_weiterleitung_vec :
    instLoadEigen_vec = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem inst_fremd_alt_vec :
    instLoadFremd_vec = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem inst_spuelung_aendert_speicher_vec :
    instNachFlush_vec = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem inst_fremd_neu_vec :
    instFremdNachFlush_vec = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- Core 1 refuses: its RIP points at non-executable loaded memory. -/
theorem inst_kern1_verweigert_vec :
    hwByteschrittReg instStart_vec 1 = .verweigert := by
  apply hwBild_ohne_exec_verweigert
  decide

/-- The dark image: same bytes, code section not executable. -/
def instBildDunkel_vec : Bild :=
  { instBild_vec with
    abschnitte := [{ instCode_vec with ausfuehrbar := false },
      instDaten_vec] }

/-- The dark machine: same cores over the non-executable mapping. -/
def instDunkel_vec : HwMaschine :=
  { instStart_vec with mem := geladen instBildDunkel_vec 0x100000 }

/-- PLANTED REFUSAL: on the non-executable mapping the fetch refuses. -/
theorem inst_dunkel_fetch_vec :
    fetchExt (projFp instDunkel_vec 0)
      (geholt (projZustand instDunkel_vec 0)) = none := by
  decide

/-- PLANTED REFUSAL: on the non-executable mapping the Hw step refuses. -/
theorem inst_dunkel_verweigert_vec :
    hwByteschrittReg instDunkel_vec 0 = .verweigert :=
  hwByteschrittReg_verweigert _ _ inst_dunkel_fetch_vec

/-- The vec witness proposition: accepted image, fetched row,
    register step, TSO leg and refusals, as one conjunction. -/
def instZeugeProp_vec : Prop :=
  wohlgeformt .p48 instBild_vec = true ∧
      HwWf instStart_vec ∧
      fetchExt (projFp instStart_vec 0)
        (geholt (projZustand instStart_vec 0)) =
        some (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩, []) ∧
      hwRipOut (hwByteschrittReg instStart_vec 0) 0 =
        some (BitVec.ofNat 64 0x101005) ∧
      hwXmmTiefOut (hwByteschrittReg instStart_vec 0) 0 .xmm0 =
        some (BitVec.ofNat 64 18446744073709551608) ∧
      hwMemOut (hwByteschrittReg instStart_vec 0) instAdr =
        some (BitVec.ofNat 8 0) ∧
      instLoadEigen_vec = some (some (BitVec.ofNat 8 42)) ∧
      instLoadFremd_vec = some (some (BitVec.ofNat 8 0)) ∧
      instNachFlush_vec = some (some (BitVec.ofNat 8 42)) ∧
      instFremdNachFlush_vec = some (some (BitVec.ofNat 8 42)) ∧
      hwByteschrittReg instStart_vec 1 = .verweigert ∧
      hwByteschrittReg instDunkel_vec 0 = .verweigert

/-- JOINT WITNESS (vec): accepted image, fetched PXOR row, register
    step xoring the low lane, owner-only forwarding, drain changing
    shared memory 0 to 42 observed from both cores, with the
    data-section and dark-mapping refusals beside it. -/
theorem inst_zeuge_vec : instZeugeProp_vec := by
  unfold instZeugeProp_vec
  refine ⟨inst_wohlgeformt_vec, instStart_wf_vec, inst_fetch_vec,
    inst_rip_vec, inst_wert_vec, inst_mem_still_vec,
    inst_weiterleitung_vec, inst_fremd_alt_vec,
    inst_spuelung_aendert_speicher_vec, inst_fremd_neu_vec,
    inst_kern1_verweigert_vec, inst_dunkel_verweigert_vec⟩

/-! ## The instances adapter and the joint witness. -/

/-- The instances adapter: the accepted register-path plug, reused by
    name (never duplicated). Memory forms must use the issue/drain
    path; halt is an outcome, never a successor. -/
def adapterInstanzen : HwAdapter ExtInstr := adapterInteger666

/-- ADAPTER AGREEMENT: the adapter admits exactly what the accepted
    unified evaluator accepts on the core projection. -/
theorem adapterInstanzen_vereinbarung (m : HwMaschine) (c : Nat)
    (i : ExtInstr) (t' : FpZustand)
    (h : stepExt i (projFp m c) (m.bereit c) = .weiter t') :
    adapterInstanzen.schritt m c i = some (setKernVonFp m c t') := by
  unfold adapterInstanzen adapterInteger666
  simp [h]

/-- ADAPTER REFUSAL: what the evaluator refuses, the adapter refuses. -/
theorem adapterInstanzen_verweigert (m : HwMaschine) (c : Nat)
    (i : ExtInstr)
    (h : stepExt i (projFp m c) (m.bereit c) = .verweigert) :
    adapterInstanzen.schritt m c i = none := by
  unfold adapterInstanzen adapterInteger666
  simp [h]

/-- ADAPTER HALT REFUSAL: the divide trap has no successor state. -/
theorem adapterInstanzen_halt_verweigert (m : HwMaschine) (c : Nat)
    (i : ExtInstr)
    (h : stepExt i (projFp m c) (m.bereit c) = .halt) :
    adapterInstanzen.schritt m c i = none := by
  unfold adapterInstanzen adapterInteger666
  simp [h]

/-- WELL-FORMEDNESS SURVIVES: every Hw step of an instance machine
    keeps the checked core/control profile (lifts `hwSchritt_wf`). -/
theorem instSchritt_wf (m m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt m m' e) (hwf : HwWf m) : HwWf m' :=
  hwSchritt_wf m m' e h hwf

/-- THE JOINT WITNESS: all six per-family witnesses hold together --
    six accepted loaded images, six fetched rows with their register
    steps, six owner-only forwarding legs with drains changing actual
    shared memory 0 to 42 observed from both cores, and twelve
    planted refusals beside them. Non-degenerate: every drain changes
    ACTUAL shared loaded memory on a two-core machine. -/
theorem instAlle_zeuge :
    instZeugeProp_muldiv ∧ instZeugeProp_shift ∧ instZeugeProp_setcc ∧
      instZeugeProp_cmov ∧ instZeugeProp_fp ∧ instZeugeProp_vec :=
  ⟨inst_zeuge_muldiv, inst_zeuge_shift, inst_zeuge_setcc,
    inst_zeuge_cmov, inst_zeuge_fp, inst_zeuge_vec⟩

/- CUTS:
   Proved here, reusing every accepted definition unchanged (no second
   decoder, evaluator, loader, adapter or ISA model):
   - six small loaded images (muldiv 3 bytes, shift/setcc/cmov/fp
     4 bytes, vec 5 bytes; execute-only code, rw data, profile 48
     acceptance by decision) on `hwBildStart`-style two-core machines
     with empty buffers and full silicon;
   - six concrete `fetchExt` successes (each pinned row fetched whole,
     rest `[]`) and six Hw register steps with exact evaluator
     agreement (`md_mul_erfolg`, `shiftSchritt_weiter`,
     `setccSchrittBytes`/`cmovSchrittBytes` applications,
     `fpSchritt_movsdRR`, `stepVector_pxor`, lifted through the
     `stepExt_*` selection lemmas, never redefined);
   - six `HwSchritt.reg` embeddings with the memory-unchanged gate
     discharged by reflexivity, plus register-path memory/buffer
     silence (`hwMemOut`/`hwBufOut` observations);
   - six memory-changing TSO stages: byte-42 issue, owner-only
     forwarding, foreign observation of zero, drain installing 42 in
     ACTUAL shared memory observed from both cores;
   - the reused register-path adapter (`adapterInstanzen`) with
     admission/refusal/halt agreement, and well-formedness survival;
   - per-family joint witnesses and the six-way joint witness
     (`instAlle_zeuge`).
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are the accepted canonical
     subsets with self-consistency only, not x86 truth.
     Silicon/timing assumptions: none beyond the accepted lemmas
     reused by name (MUL flag snapshot keeps incoming SF/ZF/PF for
     architecturally undefined bits, as documented in `MulDiv.lean`).
   - The six pinned rows are register-only; the family's own store
     forms (e.g. `movsdSpeichere`) write canonical memory and must use
     the TSO issue path, never the `reg` plug. The memory change in
     each witness comes from the TSO issue/drain stage, proved to
     change actual shared bytes.
   - No per-access target-to-W/GX simulation and no whole-word
     atomicity beyond the reused guards; no source/IR/ABI/loader/
     entry/budget link; no LOCK RMW path; `verweigert` is the absence
     of a transition, never normal program termination.
   - The full bridge to W/GX is not claimed.
-/

#print axioms inst_fetch_muldiv
#print axioms inst_reg_muldiv
#print axioms inst_zeuge_muldiv
#print axioms inst_fetch_shift
#print axioms inst_reg_shift
#print axioms inst_zeuge_shift
#print axioms inst_fetch_setcc
#print axioms inst_reg_setcc
#print axioms inst_zeuge_setcc
#print axioms inst_fetch_cmov
#print axioms inst_reg_cmov
#print axioms inst_zeuge_cmov
#print axioms inst_fetch_fp
#print axioms inst_reg_fp
#print axioms inst_zeuge_fp
#print axioms inst_fetch_vec
#print axioms inst_reg_vec
#print axioms inst_zeuge_vec
#print axioms adapterInstanzen_vereinbarung
#print axioms adapterInstanzen_verweigert
#print axioms adapterInstanzen_halt_verweigert
#print axioms instSchritt_wf
#print axioms instAlle_zeuge

end Gabbro.Grammatik.X86
