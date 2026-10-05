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
