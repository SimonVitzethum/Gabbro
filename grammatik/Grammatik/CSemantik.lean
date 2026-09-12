/-
  File:      Grammatik/CSemantik.lean
  Subject:   A formal semantics for five emitted C forms (measurement lane).

  The emitter writes a C subset (census: 64 forms, `zaehle-c-formen.py`;
  allowed/never lists and UB inventory in `BEWEIS.md` section 1a/2).
  No formal semantics of that subset exists; emitter correctness cannot
  even be stated without one. This file MEASURES the cost on the five
  most-used forms before the full semantics is planned:

    A  `uint32_t` arithmetic with explicit width (binary + - * / % ops)
    B  array indexing with a checked index (`t->slots[i]`)
    C  assignment to a struct field of a table slot (`t->slots[i].f = v;`)
    D  `if` / `else`
    E  the admitted counting `for` (`for (uint32_t x = lo; x < hi; x++)`)

  Memory model: objects are maps from (table, index, field) to machine
  integers of the declared width -- the same shape as Gabbro's `Speicher`,
  so correspondence is direct. Each C undefined / implementation-defined
  behaviour the five forms can trigger is an INVENTORIED predicate, and
  the semantics gets STUCK (returns `none`) there -- so "no UB" is
  "the semantics makes progress".
-/
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

/-! ## 0. Widths and ranges: the integer types the five forms need -/

/-- The integer widths the emitter uses (`uint{8,16,32,64}_t`,
    `int{8,16,32,64}_t`; `BEWEIS.md` section 1a type row). -/
inductive CWidth where
  | w8 | w16 | w32 | w64
  deriving DecidableEq, Repr

/-- Bits per width. -/
def CWidth.bits : CWidth → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64

/-- Lower bound of the range: `0` unsigned, `-2^(w-1)` signed. -/
def cLo (sgn : Bool) (w : CWidth) : Int :=
  if sgn then -(2 ^ (w.bits - 1) : Int) else 0

/-- Upper bound of the range: `2^w - 1` unsigned, `2^(w-1) - 1` signed. -/
def cHi (sgn : Bool) (w : CWidth) : Int :=
  if sgn then (2 ^ (w.bits - 1) : Int) - 1 else (2 ^ w.bits : Int) - 1
