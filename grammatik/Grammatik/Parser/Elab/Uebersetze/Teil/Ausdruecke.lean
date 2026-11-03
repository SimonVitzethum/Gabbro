module
public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
public import Grammatik.Parser.Profil.Platzierung
public import Grammatik.Kern.Syntax.Typen.Reason
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000
/-- An index into a table: a literal or an index parameter. -/
inductive UIdx
  | lit : Int → UIdx
  | param : String → UIdx
  deriving DecidableEq, Repr
/-- C13: the closed integer builtins of the source (`+%`, `-%`, `*%`, `<<%`, `+|`, `clz`, `ctz`, `log2_floor`,
    `popcount`, `rotl`, `rotr`, `bswap`). The storage width `W` rides with the use (`USide.ib1/ib2`), read from the
    declaration, never from an interval. -/
inductive UBi
  | addW | subW | mulW | shlW | addS | clz | ctz | log2Floor | popcount | rotl | rotr | bswap
  deriving DecidableEq, Repr
/-- An option value over the table `T` (the number rides with the type): `None`, `Some(i)`, a variable, or the
    read of an option field through a pointer (`slot`) or at a table (`tab`). -/
inductive UOpt
  | nichts : UOpt
  | etwas : UIdx → UOpt
  | var : String → UOpt
  | slot : String → String → UIdx → UOpt
  | tab : String → String → UIdx → UOpt
  /-- An option static (`static mut frei : option index into T`). -/
  | glob : String → UOpt
  deriving DecidableEq, Repr
mutual
/-- One side of an `ensures` comparison: a literal, a numeric
    parameter, a slot read through a pointer parameter (`slot`)
    or at a table (`tab`), the entry value (`alt`), or the
    function result (`erg`). -/
inductive USide
  | lit : Int → USide
  | param : String → USide
  | slot : String → String → UIdx → USide
  | tab : String → String → UIdx → USide
  | old : String → String → UIdx → USide
  /-- A number static (`ANHALTEN`, `LIMIT`): `Expr.glob`. -/
  | glob : String → USide
  | erg : USide
  /-- Integer arithmetic (`+`, `-`, `*`): the range of the result is computed by the
      lowering, exactly as `Expr.add`/`sub`/`mul` carry it in their type. -/
  | add : USide → USide → USide
  | sub : USide → USide → USide
  | mul : USide → USide → USide
  /-- An integer conversion `T(e)` to the target range `lo .. hi` of the type `T`: the widening
      `Expr.weiter`. The lowering checks that the operand's range fits (as M1 does). -/
  | conv : Int → Int → USide → USide
  /-- `&`, `|`, `^` over non-negative ranges (M137): `Expr.band`/`bor`/`bxor`. -/
  | band : USide → USide → USide
  | bor : USide → USide → USide
  | bxor : USide → USide → USide
  /-- `/`, `%` (`Expr.div`/`rem`, or the signed `sdiv`/`srem` when a range is negative), `<<`, `>>`
      (`Expr.shl`/`shr`) and the unary minus (`Expr.neg`). The lowering reads the ranges (M102, M137). -/
  | div : USide → USide → USide
  | rem : USide → USide → USide
  | shl : USide → USide → USide
  | shr : USide → USide → USide
  | neg : USide → USide
  /-- `r->f` through a reference local `r` into an open table (`Expr.slotRef`). -/
  | refSlot : String → String → USide
  /-- Aggregate values (`Ty.arr`, `Ty.str`, 2026-10-25): `a[i]` (an element or a byte), `lenof(a)`, a string
      literal (its bytes), the array literal `[]` and `[a, rest…]`, and the array `a` with the element at `i`
      replaced by `v` (`a[i] = v`). Their types are the lowering's (`lowWertE`). -/
  | idx : USide → USide → USide
  | len : USide → USide
  | text : List Int → USide
  | arrNil : USide
  | arrCons : USide → USide → USide
  | upd : USide → USide → USide → USide
  /-- A constant literal at its declared type (`const T : [u32; N] = [..]` at a use: its folded elements). -/
  | typed : Ty → USide → USide
  /-- A number narrowed to `lo .. hi` where the guard of the branch it stands in says so (`Expr.eng`; the
      fallback is unreachable there): the binder of an `update` body. -/
  | eng : USide → Int → Int → USide
  /-- C13: a closed integer builtin with one operand / two operands, at the declared storage width `W` in bits
      (`0` where the operation carries none, `+|`). The lowering checks the operand ranges, the zero-excluding
      scans, the shift amount and the full-word rotates before it builds a G term. -/
  | ib1 : UBi → Nat → USide → USide
  | ib2 : UBi → Nat → USide → USide → USide
  /-- C13: `count x in D : p` as a NUMBER (`Expr.count`, range `0 .. n`, `n` the cardinality of the domain). The
      domain `slots of T` (the table and the binder; the body reads `x` as an index into `T`), a tree domain
      `descendants of s` / `ancestors of s` (the table, the binder, the edge field, whether the walk is reversed,
      the outer seed, the body: the membership is the checked `reaches` filter, exactly as `UEns.filtered`), and
      `elems of a` (the array value, the binder, the body: the binder is an INDEX into the exact index domain of
      the array, LANGUAGE section 6). -/
  | zaehle : String → String → UEns → USide
  | zaehleBaum : String → String → String → Bool → UIdx → UEns → USide
  | zaehleFeld : USide → String → UEns → USide
  /-- A product value: the declaration number, whether the source order differs from the
      declaration order, and the fields in SOURCE order with their expected types. The lowering
      elaborates every field and reorders into declaration order (`uRecordValues`); projections
      and replacements resolve names against the nominal schema, never run-time strings. -/
  | product : Nat → Bool → List (Ty × USide) → USide
  | field : USide → String → USide
  | replace : USide → String → USide → USide
  /-- Typed tagged payloads use the same value tree as arguments and array elements. -/
  | truth : Bool → USide
  | taggedEmpty : List (Option Ty) → Nat → USide
  | taggedValue : List (Option Ty) → Nat → USide → USide
  /-- A truth-valued expression reuses the canonical predicate tree. -/
  | predicate : UEns → USide
  /-- Scalar introductions retain their complete declared type. -/
  | option : Nat → UOpt → USide
  | absent : Int → USide
  | present : Int → USide → USide
  | reason : Nat → Nat → USide
  | function : Nat → String → USide
  deriving DecidableEq, Repr
/-- One `ensures` predicate: a comparison, truth values, or a
    boolean combination (the `tr_ensures` fragment). -/
inductive UEns
  | cmp : String → USide → USide → UEns
  | tru : UEns
  | fls : UEns
  | and : UEns → UEns → UEns
  | or : UEns → UEns → UEns
  | not : UEns → UEns
  /-- A `bool` slot read through a pointer parameter / at a table (`p.slots[i].f`, `T.slots[i].f`):
      the truth value itself, not a number. -/
  | slotB : String → String → UIdx → UEns
  | tabB : String → String → UIdx → UEns
  /-- A `bool` static read as a truth value. -/
  | globB : String → UEns
  /-- A `bool` parameter or local read as a truth value (`Expr.var`). -/
  | var : String → UEns
  /-- `forall x in slots of T : p` / `exists x in slots of T : p` (`Expr.forallSlots`/`existsSlots`): the
      table, the binder (an index into `T` inside `p`) and the body. -/
  | alle : String → String → UEns → UEns
  | einige : String → String → UEns → UEns
  /-- `result` of a function with a `bool` result, in its `ensures` (`Expr.var` of the head of `ErgCtx`). -/
  | ergB : UEns
  /-- `o.is_some()` (`Expr.istSome`): the option value and the number of the table it indexes. -/
  | istSome : UOpt → Nat → UEns
  /-- A named ordinary lock; lowering must prove possession in the actual resource list. -/
  | held : String → UEns
  /-- Source implication retains its identity until the guarded G lowering. -/
  | imp : UEns → UEns → UEns
  /-- An explicit relation keeps its table and edge identities through typed lowering. -/
  | reach : String → String → UIdx → UIdx → UEns
  | member : String → UIdx → UEns
  /-- A finite tree filter: universal/existential, table, binder, edge, reverse, outer seed, body. -/
  | filtered : Bool → String → String → String → Bool → UIdx → UEns → UEns
  /-- Universal/existential iteration over the exact index domain of a fixed array. -/
  | arrayElements : Bool → USide → String → UEns → UEns
  deriving DecidableEq, Repr
end
end
/-- A value of a tagged type over the declaration `T`: a case with its payload (`Expr.case`), or a variable. -/
inductive USVal
  | fall : Nat → Option USide → USVal
  | var : String → USVal
  /-- A field of a tagged type, read through a pointer (`slot`) or at a table (`tab`). -/
  | slot : String → String → UIdx → USVal
  | tab : String → String → UIdx → USVal
  deriving DecidableEq, Repr
/-- A value of a reason type `R`: a case `R::C` (its position) or a variable. -/
inductive UGrund
  | fall : Nat → UGrund
  | var : String → UGrund
  deriving DecidableEq, Repr
/-- A call argument: a pointer variable passed through
    (`var`), a fresh `rw`-to-`r` pointer to a table with the
    callee's rights (`freshPtr`, the pass-a-fresh-pointer idiom
    of the hand translation), or a value (`wert`: a literal, a
    numeric parameter or a slot read). -/
inductive UArg
  | var : String → UArg
  | freshPtr : String → DataCapTy → UArg
  | val : USide → UArg
  /-- A truth value for a `bool` parameter. -/
  | bval : UEns → UArg
  /-- An option value for an `option index into T` parameter. -/
  | oval : UOpt → UArg
  /-- A reason value for a parameter of a reason type. -/
  | gval : UGrund → UArg
  /-- `&f` for a parameter of a pointer type: the function (`Expr.fnref`; that it conforms is the lowering's). -/
  | fnref : String → UArg
  deriving DecidableEq, Repr
/-- The trailing return: nothing, or a value (a literal, a
    numeric parameter or a slot read). -/
inductive URet
  | empty : URet
  | val : USide → URet
  /-- A `bool` result: a truth value. -/
  | bool : UEns → URet
  /-- An `option index into T` result. -/
  | opt : UOpt → URet
  /-- `return R::C;` at a function with the reason channel `R`: the position of the case `C` (`retWhy`). -/
  | why : Nat → URet
  /-- A tagged value as the result. -/
  | sum : USVal → URet
  /-- A reason value as the result of a function of reason type (not its channel). -/
  | grund : UGrund → URet
  /-- An aggregate value as the result (`UFn.resTy`). -/
  | wert : USide → URet
  /-- No trailing return: the body ends in a terminal `if`/`else` (`UStmt.ifEnde`, `Endblock.ite`). -/
  | keins : URet
  deriving DecidableEq, Repr
end Gabbro.Grammatik.Parser.Uebersetze
