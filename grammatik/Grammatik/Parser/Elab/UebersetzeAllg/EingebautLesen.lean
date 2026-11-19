module

public import Grammatik.Parser.Elab.Uebersetze
import all Grammatik.Parser.Elab.Uebersetze.Eingebaut
import all Grammatik.Parser.Elab.Uebersetze.Teil4Index
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil4
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil8
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

/-
  C13 reading-side fixtures (`_zeuge`): the surface forms of the closed integer builtins, of `count`, of `sizeof`
  and of the numeric `aligned` read by the exporter (`uSeite`, `uSichert`, `uSpTy`), generic in nothing but the
  context they name:
  * every builtin at the declared storage width of a parameter, a static, a field read through a pointer, a field
    read at a table, an arena element, a conversion `T(e)` and an alias of a word type (`uSpeicherBreite`);
  * the refusals: an unknown width (a parameter without a bare word type, a literal, a field without a declared
    width), and `old`/`result` inside a builtin or a count body (`seiteAltErg`);
  * `count` as a NUMBER at the `+ - *` layer of a comparison over each of its domains (`slots of`, `descendants of`,
    `elems of`), with a guarded read and a read of a static inside the body, and the refusals (an unmodelled
    domain, an unheld guard);
  * `sizeof` of a type name, a parameter and a field, `aligned` with a positive constant and its refusals.
  Every fixture is reduced with the canonical reader equations.
-/

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

namespace EingebautLesen

-- Use the actual recursive reader equations rather than asking definitional
-- equality to unfold their well-founded and mutual implementations.
attribute [local cbv_eval] uRechne.eq_def uSichert.eq_def uZSeite.eq_def
  seiteAltErg.eq_def ensAltErg.eq_def
attribute [local cbv_opaque] uFloatLimit

/-- The empty context the fixtures extend. -/
def lb : UCtx :=
  { names := [], kinds := [], types := [], tabs := [], locks := [], held := [], res := none, fname := "f", alias := [], lits := [] }

/-- Four numeric parameters `a b n z`: `a`, `b` and `n` are bare bytes, `z` has no declared storage width. -/
def cw : UCtx :=
  { lb with names := ["a", "b", "n", "z"], kinds := [.int, .int, .int, .int], types := [.int 0 255, .int 0 255, .int 0 7, .int 0 255], bits := [8, 8, 8, 0] }

/-- A table `T` of four slots with a byte field `v` of declared storage width `8` and a field `w` without one. -/
def tt : UTab :=
  { name := "T", count := 4, cols := [("v", (0, 255)), ("w", (0, 100))], breiten := [("v", 8)] }

/-- An arena `A` of three halfwords. -/
def aa : UTab :=
  { name := "A", count := 3, cols := [("wert", (0, 65535))], arena := true, breiten := [("wert", 16)] }

/-- A static byte `G`. -/
def gg : UGlob := { name := "G", ty := .int 0 255, init := 0, breite := 8 }

/-- The context of a function with a pointer parameter `p` to `T` and the unit's table, arena and static. -/
def ct : UCtx :=
  { lb with names := ["p"], kinds := [.ptr (.table 0 (true, true))], types := [.ptr (.table 0 (true, true))], tabs := [tt, aa], globs := [gg] }

/-! ## The builtins at a declared storage width -/

/-! ## Refusals: the width is never guessed -/

/-! ## `count` as a number -/

/-- The table `T` of the count fixtures, with an index binder `x` read as `T.slots[x].v`. -/
def feldLesen : SExpr := .field (.index (.field (.variable "T") "slots") (.variable "x")) "v"

def zaehleSlots : SExpr := .ext .count ["x", "slots"] [.variable "T", .bin ">" feldLesen (.lit 10)]

def zaehleSlotsU : USide := .zaehle "T" "x" (.cmp ">" (.tab "T" "v" (.param "x")) (.lit 10))

/-- The tree domains: the table of the edge, the binder, the declared edge field, whether the walk is reversed, the
    outer seed (an index parameter) and the body. -/
def baumU : UTab := { name := "T", count := 3, cols := [("next", (0, 0))], opts := [("next", 0)], kanten := [("child", "next")] }

def baumCtx : UCtx :=
  { lb with names := ["root"], kinds := [.index 0], types := [.index 3], tabs := [baumU] }

/-- The array domain: the binder is an INDEX into `0 ..< n` (LANGUAGE section 6); the body reads the element. -/
def feldCtx : UCtx :=
  { lb with names := ["data"], kinds := [.wert], types := [.arr (.int 0 255) 2] }

/-! ## `sizeof` and `aligned` -/

/-- Ordinary boolean expressions reuse the contract quantifier elaborator. -/
def existsExpression : SExpr :=
  .ext .any ["x", "slots"] [.variable "T", .bin ">" feldLesen (.lit 10)]

end EingebautLesen

end Gabbro.Grammatik.Parser.UebersetzeAllg
