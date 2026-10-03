/-
  File:      Grammatik/X86/JumpTableCert.lean
  Subject:   Jump-table certificates for indirect JMP through validated tables.

  Lane 769 (hardware completion): an indirect `JMP r/m64` (`FF /4`) whose
  target word is read from a validator-tracked jump table. Every table entry
  is a decoded instruction start or a listed entry, the target is never a
  forged number (M140 shape), and the admitted bytes execute through the
  accepted fetched step. See CUTS for scope.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- Manual provenance for every form claimed here. -/
def jtHandbuch : String :=
  "Intel SDM 325462-093US Vol.2A Ch.3 JMP (FF /4 JMP r/m64, p.3-504); " ++
  "Vol.1 s.3.3.7.1 canonical addressing. Local snapshot " ++
  ".tmp/HARDWARE-REFERENCES (intel-instruction-reference.txt)."

/-- Slot address of entry `i`: base plus eight bytes per entry. -/
def tabSlot (basis : Adresse) (i : Nat) : Adresse :=
  basis + BitVec.ofNat 64 (8 * i)

/-- Table entry read: the 8-byte word at the slot, if readable. -/
def tabEintrag (speicher : Speicher) (basis : Adresse) (i : Nat) :
    Option Wort :=
  read64 speicher (tabSlot basis i)

/- CUTS:
   Proved here so far: provenance string, slot arithmetic, entry read.
   NOT proved here, and not claimed: everything else (see task).
-/

#print axioms jtHandbuch
#print axioms tabSlot
#print axioms tabEintrag

end Gabbro.Grammatik.X86
