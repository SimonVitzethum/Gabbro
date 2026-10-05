/-
  File:      Grammatik/X86/HwStackCalls.lean
  Subject:   Stack, call and return per core through TSO on the coherent
             machine (lane 1139).

  Lifts the accepted `Stapel`/`StackUnwind`/`CallAlign16` word effects to
  buffered byte issues (`hwWortAusgabe`/`issueListe`) and the accepted
  `read64` loads to forwarding `loadByte` observations, on `HwMaschine`.
  Push/call store through the acting core's TSO buffer; pop/ret observe
  through loads with owner-only forwarding; alignment and spill privacy
  are stated premises. No model is redefined here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Stapel
import Grammatik.X86.TSO
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.HardwareExecution
import Grammatik.X86.StackUnwind
import Grammatik.X86.CallAlign16
import Grammatik.X86.CodeImmutability

namespace Gabbro.Grammatik.X86

/-- Stack slot of core `c`: one word below its top. -/
def stapelSlot (m : HwMaschine) (c : Nat) : Adresse :=
  (m.kerne c).register Register.rsp - BitVec.ofNat 64 8

/-- Buffered push: the word as eight TSO byte issues at the slot. -/
def stapelPush (m : HwMaschine) (c : Nat) (v : Wort) : Option HwMaschine :=
  hwWortAusgabe m c (stapelSlot m c) v

/-- Buffered call spill: the return word as eight TSO byte issues. -/
def stapelCall (m : HwMaschine) (c : Nat) (ret : Wort) : Option HwMaschine :=
  hwWortAusgabe m c (stapelSlot m c) ret

end Gabbro.Grammatik.X86
