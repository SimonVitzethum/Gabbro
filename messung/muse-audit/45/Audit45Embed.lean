-- Audit 45 probe A: `contrAtomVonPC` is `id` on the SAME type.
-- Pattern (d): the name and docstring suggest an embedding of plain PC
-- positions into contract positions, but the Lean states an endofunction
-- `ContrAtom D -> ContrAtom D` proved by `id`. No PCAtom appears.
-- Demonstration: `rfl` unfolding and one entry atom the "embedding"
-- cannot come from a three-case PC atom (there is no PCAtom argument).
import Grammatik.VertragOrtB

namespace GabbroAudit45A

open Gabbro.Grammatik

-- The "embedding" is definitionally the identity: no content moves.
example (D : Deklaration) (a : ContrAtom D) :
    contrAtomVonPC a = a := rfl

-- Entry atoms are already in the target type, so the map proves nothing
-- about plain PC positions: any contract atom is a fixed point.
example (D : Deklaration) (f : D.Fn) :
    contrAtomVonPC (ContrAtom.eintritt (D := D) f)
      = ContrAtom.eintritt (D := D) f := rfl

#print axioms Gabbro.Grammatik.contrAtomVonPC

/-
CUTS:
- No claim about `PCAtom` (Maschine.lean) is made here; the point is that
  `contrAtomVonPC` cannot state one since it never mentions `PCAtom`.
-/
