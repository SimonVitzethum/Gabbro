/-
  File:      Grammatik/X86/Ausfuehrung.lean
  Subject:   Executable pilot transitions over the canonical x86 vocabulary.

  Lane 272 (wave A): single-step semantics for the canonical `Befehl`
  constructors, reusing the shared arithmetic (`Wort.lean`: add64/sub64/xor64,
  bedingung) and byte-memory (`Speicher.lean`: read64/write64) helpers. The
  decode length is checked data (1..15); RIP advances before relative control
  flow; displacements are sign-extended int32. MOV preserves flags; CMP writes
  no operand. Failed memory access is explicit `none`; no invented halt.
  No whole-binary, source or concurrency claim is made here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- Decode-length guard: validated decoding data, never trusted metadata. -/
def laengeOk (l : Nat) : Bool := decide (1 ≤ l ∧ l ≤ 15)

/-- Address after the decoded instruction. -/
def ripNach (rip : Adresse) (l : Nat) : Adresse := rip + BitVec.ofNat 64 l

/-- Sign extension of a 32-bit displacement to a full word. -/
def dispWort (d : BitVec 32) : Wort := sext .b32 (BitVec.ofNat 64 d.toNat)

/-- Base-plus-displacement effective address. -/
def effAddr (s : Zustand) (base : Register) (disp : BitVec 32) : Adresse :=
  s.register base + dispWort disp

/-- Register-file update: `dst` holds `v`, every other register is kept. -/
def regSet (r : Register → Wort) (dst : Register) (v : Wort) :
    Register → Wort :=
  fun q => if q = dst then v else r q

/-- Register write with new RIP and flags; memory is untouched. -/
def schrittRegister (s : Zustand) (nach : Adresse) (f : Flags) (dst : Register)
    (v : Wort) : Zustand :=
  { s with register := regSet s.register dst v, rip := nach, flags := f }

/-- Single pilot step; `none` is an explicit refusal (bad length or failed
    memory access). Grows one instruction form per commit. -/
def schritt (d : Decodiert) (s : Zustand) : Option Zustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    let nach := ripNach s.rip d.laenge
    match d.befehl with
    | .movImm64 dst v => some (schrittRegister s nach s.flags dst v)
    | .movReg64 dst src =>
      some (schrittRegister s nach s.flags dst (s.register src))
    | _ => none

/- CUTS:
   Only the two MOV forms step so far; every other constructor is an explicit
   refusal (`none`). No decoder, encoder, TSO bridge, source correspondence,
   ABI/loader, cost transfer or final-image claim is proved here.
-/

#print axioms schritt

end Gabbro.Grammatik.X86
