/-
  File:      Grammatik/X86/RegisterInterference.lean
  Subject:   Canonical register reads/writes and fail-closed interference
             certificates for the actual pilot instructions.

  Lane 427 (continuous reserve): reusable facts over the canonical
  `Befehl`/`Zustand`/`schritt` vocabulary only (`Typen`, `Ausfuehrung`,
  `Zugriffe`). No second IR, no invented liveness: interference edges
  and live sets are DECLARED inputs the future accepted IR supplies
  with validation; this file checks them fail-closed. Actual source
  allocation refinement stays OPEN.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Zugriffe

namespace Gabbro.Grammatik.X86

/-- Canonical register reads of one pilot instruction, pre-state view.
    Stack forms read `rsp`; `call` reads `rsp`; memory address bases read. -/
def regLiest : Befehl → List Register
  | .movImm64 _ _ => []
  | .movReg64 _ src => [src]
  | .addReg64 dst src => [dst, src]
  | .subReg64 dst src => [dst, src]
  | .xorReg64 dst src => [dst, src]
  | .cmpReg64 lhs rhs => [lhs, rhs]
  | .load64 _ base _ => [base]
  | .store64 base src _ => [base, src]
  | .jump32 _ => []
  | .jumpIf32 _ _ => []
  | .push64 src => [src, .rsp]
  | .pop64 _ => [.rsp]
  | .call32 _ => [.rsp]
  | .ret => [.rsp]

/-- Canonical register writes of one pilot instruction.
    `cmp`/jumps write none; stack forms write `rsp`. -/
def regSchreibt : Befehl → List Register
  | .movImm64 dst _ => [dst]
  | .movReg64 dst _ => [dst]
  | .addReg64 dst _ => [dst]
  | .subReg64 dst _ => [dst]
  | .xorReg64 dst _ => [dst]
  | .cmpReg64 _ _ => []
  | .load64 dst _ _ => [dst]
  | .store64 _ _ _ => []
  | .jump32 _ => []
  | .jumpIf32 _ _ => []
  | .push64 _ => [.rsp]
  | .pop64 dst => [dst, .rsp]
  | .call32 _ => [.rsp]
  | .ret => [.rsp]

/- CUTS:
    Skeleton only: reads/writes defined; checks and proofs follow.
-/

#print axioms regLiest
#print axioms regSchreibt

end Gabbro.Grammatik.X86
