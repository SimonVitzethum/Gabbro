/-
  File:      Grammatik/CParser/CProben.lean
  Subject:   A2: the REFUSALS of `parseC`, each on a short text.

  A parser that guesses is worse than one that stops, and a pin a parser
  can satisfy by accepting anything is no pin. Every probe below is a
  form the emitter DOES write somewhere in the corpus (the census
  `instrumente/pruefe-cformen.py` names them all) and `parseC` does not
  read: the answer is `none`.
-/
import Grammatik.CParser.CParse

namespace Gabbro.Grammatik.CParser

open Gabbro.Grammatik

/-! ## 8. Probes: the refusals, each on a short text

    Every one of these is a form the emitter DOES write somewhere in the
    corpus (the census names them) and this parser does not read. It says
    `none` -- it does not guess.

    The texts are `List Char` built from SHORT literals: one long literal
    would cost the kernel gigabytes (the cost note at `lexC`). -/

set_option maxRecDepth 10000

/-- The prelude every emitted unit carries. -/
def vorspann : List Char :=
  "#include <stdint.h>\n".toList ++ "#include <stdbool.h>\n".toList ++
  "#include <stdatomic.h>\n".toList ++ "#include <math.h>\n".toList ++
  "_Static_assert((-1 >> 1) == -1, \"arithmetic right shift\");\n".toList ++
  "_Static_assert((int)0xFFFFFFFFu == -1, \"modular conversion\");\n".toList

/-- The smallest text of the subset: one function that returns nothing. -/
theorem parseC_leer :
    parseC (vorspann ++ "static void f(void) {\n".toList ++ "    return;\n".toList ++
      "}\n".toList) = some [{ params := [], locals := [], body := .ret none }] := rfl

/-- WITHOUT the two `_Static_assert` pins the same unit is refused: the
    pins are what A3 leans on, so a text that lacks them is not a text
    this parser will speak for. -/
theorem parseC_ohnePin :
    parseC ("static void f(void) {\n".toList ++ "    return;\n".toList ++ "}\n".toList) = none := rfl

/-- `if` -- 122 occurrences in 40 corpus programs, and no form here. -/
theorem parseC_kein_if :
    parseC (vorspann ++ "static void f(uint32_t x) {\n".toList ++
      "    if (x) return;\n".toList ++ "}\n".toList) = none := rfl

/-- Arithmetic: a `+` carries a C computation type this parser does not
    infer, so it refuses instead of guessing one. -/
theorem parseC_keine_rechnung :
    parseC (vorspann ++ "static uint32_t f(uint32_t x) {\n".toList ++
      "    return x + 1;\n".toList ++ "}\n".toList) = none := rfl

/-- A local declaration (`T x = e;`): the C local number of a local that
    is no parameter is pinned by nothing this parser reads. -/
theorem parseC_kein_let :
    parseC (vorspann ++ "static uint32_t f(uint32_t x) {\n".toList ++
      "    uint32_t y = x;\n".toList ++ "    return y;\n".toList ++ "}\n".toList) = none := rfl

/-- A volatile register access -- a named assumption of the plan, never a
    form of this parser. -/
theorem parseC_kein_volatile :
    parseC (vorspann ++ "static uint32_t f(uint32_t x) {\n".toList ++
      "    return *(volatile uint32_t *)(x);\n".toList ++ "}\n".toList) = none := rfl

/-- A function declared and never defined leaves a hole in the unit. -/
theorem parseC_loch :
    parseC (vorspann ++ "static void f(void) __attribute__((unused));\n".toList) = none := rfl

#print axioms Gabbro.Grammatik.CParser.parseC_leer
#print axioms Gabbro.Grammatik.CParser.parseC_ohnePin
#print axioms Gabbro.Grammatik.CParser.parseC_kein_if
#print axioms Gabbro.Grammatik.CParser.parseC_keine_rechnung
#print axioms Gabbro.Grammatik.CParser.parseC_kein_let
#print axioms Gabbro.Grammatik.CParser.parseC_kein_volatile
#print axioms Gabbro.Grammatik.CParser.parseC_loch

end Gabbro.Grammatik.CParser
