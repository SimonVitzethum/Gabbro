/-
  GAP-21 `space` (G-SPACE) -- LESESTELLE probe, p21 (odd).
  Registry: messung/SYNTAX-PARSER-ENTWURF.md, twenty-first LESESTELLE row.
  EBNF (dokumente/SYNTAX.md, section 3): space = "normal" | "mmio" | "dma"
    | "code" | "boot" | "port" | ident.
  ptrty = "ptr" "<" space "," rights ">" typeexpr.

  MAPPING RULE (tree vs token). `space` has no constructor: the address space
  is a DECLARATION attribute feeding the barrier choice, and the emitter's
  concern. The parser resolves the spelling against the six fixed sides (or a
  declared `ident` side), checks the carrier declaration, and erases it from
  the term: `ptr<dma, rw> T` is `Ty.ptr n true` with the carrier number `n`.
  Only the `retires … from space` use names the space in a term, and even
  there the constructor keeps mark, stage and assumption (`Stmt.retires`);
  the space itself is discharged at elaboration against the declaration.

  MINIMAL PARSE WITNESS. Surface `ptr<dma, rw> T` vs `ptr<normal, rw> T`:
  same `Ty.ptr` shape, different barrier owed by the declaration fact. The
  model below is the barrier choice over the six sides.
-/
import Grammatik.Syntax

namespace P21.Gap21Space

/-- The six fixed sides plus a declared side. -/
inductive Space where
  | normal | mmio | dma | code | boot | port | named (s : String)
  deriving DecidableEq, Repr

/-- Barrier choice follows from the space: the declaration fact the tree forgets. -/
def barrierOwed : Space → Bool
  | .normal => false
  | .mmio => true
  | .dma => true
  | .code => false
  | .boot => true
  | .port => true
  | .named _ => true

-- Surface `ptr<dma, rw> T`: a barrier is owed.
example : barrierOwed .dma = true := rfl
-- Surface `ptr<normal, rw> T`: same `Ty.ptr` shape, no barrier owed.
example : barrierOwed .normal = false := rfl
-- Surface `ptr<code, x> F`: code space rides the `fnptr`, no barrier.
example : barrierOwed .code = false := rfl

-- Carrier links: the pointer is carrier number plus right; `retires` keeps
-- mark, stage and assumption while the space is discharged at elaboration.
open Gabbro.Grammatik in
#check @Ty.ptr
open Gabbro.Grammatik in
#check @Stmt.retires

end P21.Gap21Space
