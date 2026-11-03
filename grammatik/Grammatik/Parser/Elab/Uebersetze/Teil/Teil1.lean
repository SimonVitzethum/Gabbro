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
/-- One body statement: a slot write through a pointer (`assign`)
    or at a table (`assignTab`), or a direct call. -/
inductive UStmt
  | assign : String → String → UIdx → USide → UStmt
  | assignTab : String → String → UIdx → USide → UStmt
  /-- The same two writes into a `bool` field: the right side is a truth value. -/
  | assignB : String → String → UIdx → UEns → UStmt
  | assignTabB : String → String → UIdx → UEns → UStmt
  /-- `X = v;` at a `static mut` (`Stmt.assignGlob`), the value a number or a truth value. -/
  | assignGlob : String → USide → UStmt
  | assignGlobB : String → UEns → UStmt
  /-- `A = v publishes nothing;` at an `atomic` (`Stmt.publish` with the empty payload). -/
  | storeAtom : String → USide → UStmt
  | storeAtomB : String → UEns → UStmt
  | call : String → List UArg → UStmt
  /-- `locks L { ... }` is written FLAT: `sperrtAuf L`, the block's statements, `zu` (the
      elaborator writes them balanced, the lowering reads them back as one block). A nested
      constructor would make `UStmt` a nested inductive, and the derived `DecidableEq`/`Repr` the
      pins use would go. -/
  | lockBeg : String → UStmt
  | blkEnd : UStmt
  /-- `let x [: T] = v;` of a number: binds `x` for the rest of the block (flat, like the locks
      markers). `T`'s range is the annotation the value must fit; the type the binding carries is the
      COMPUTED range of `v`, which the lowering reads (`Block.bind`). -/
  | bind : String → Option (Int × Int) → USide → UStmt
  /-- `let x : bool = v;` (or an untyped truth value): binds a truth value (`Block.bind` at `Ty.bool`). -/
  | bindB : String → UEns → UStmt
  /-- `let mut x : T = v;`: the binding carries the DECLARED range `lo .. hi` (the value is widened to it),
      so a later `x = w;` may store any value of that range. -/
  | bindMut : String → Int → Int → USide → UStmt
  /-- `x = v;` at a `let mut` local (`Stmt.assignVar`), a number or a truth value. -/
  | setVar : String → USide → UStmt
  /-- `let x [: option index into T] = o;`: an option value, `T` its table number. -/
  | bindOpt : String → Nat → UOpt → UStmt
  /-- `p.slots[i].f = o;` and `T.slots[i].f = o;` at an option field. -/
  | assignOpt : String → String → UIdx → UOpt → UStmt
  | assignTabOpt : String → String → UIdx → UOpt → UStmt
  /-- `match o { Some(k) => { .. } None => { .. } }` (`Stmt.onOption`): `matchBeg T o k`, the `Some` arm's statements
      with its ender (the binder `k` an index into `T`), `ifElse`, the `None` arm's statements with its ender,
      `blkEnd`. -/
  | matchBeg : Nat → UOpt → String → UStmt
  /-- `start { f, g };`: the spawn and the join are thread-machine steps, not G statements (the roots travel as
      `UProg.gestartet`); the statement leaves no term. -/
  | startS : UStmt
  /-- `let i = alloc A (v) else { .. };` (`Block.arenaAlloc`, sugar over `narrow`): `allocBeg i A v`, the
      statements of the full-arena branch with its ender, `blkEnd`; the rest reads `i` as an index into `A`. -/
  | allocBeg : String → String → USide → UStmt
  /-- `let i = alloc A (v);` without `else` (`Block.arenaAllocRequired`, sugar over
      `narrowRequired`): `allocReqBeg i A v`; the rest reads `i` as an index into `A`.
      A full arena is `Logik.kapazitaet`, excluded by the caller's capacity duty
      (`KoerperGutS/SA`); there is no failure continuation. -/
  | allocReqBeg : String → String → USide → UStmt
  /-- `let x = v;` of a tagged value, `T` the position of its declaration. -/
  | bindSum : String → Nat → USVal → UStmt
  /-- `match m { C => { .. } .. }` over a tagged value (`Stmt.onTag`): `matchTagBeg T m binders`, one arm per case in
      declaration order (each its statements with its ender; `binders` names the payload variable of a case with
      a payload, empty otherwise), separated by `ifElse`, closed by `blkEnd`. -/
  | matchTagBeg : Nat → String → List String → UStmt
  /-- `let x = f(..) else (e) { .. };` (`Block.bindCallElse`): `bindElse x f args e`, the statements of the
      `else` branch (an end block, `e` bound as the reason) with its ender, `blkEnd`. -/
  | bindElse : String → String → List UArg → String → UStmt
  /-- `match e { C0 => { .. } C1 => { .. } }` over a reason (`Stmt.onWhy`): `matchWhyBeg e`, then one arm per case in
      declaration order (each its statements with its ender), separated by `ifElse`, closed by `blkEnd`. -/
  | matchWhyBeg : String → UStmt
  /-- `let y = g(..) else (e) { .. };` at a foreign body with a reason channel (`Block.bindAxiomElse`,
      `Endblock.bindAxiomElse`): like `bindElse`. -/
  | bindAxElse : String → String → List UArg → String → UStmt
  /-- `let x = f(..);` (`Block.bindCall`): the callee's value, bound at the callee's result type. -/
  | bindCall : String → String → List UArg → UStmt
  /-- `f(..);` at an `extern fn` (a foreign body, `D.Ax`): `Stmt.axiomCall` for an answer-less one, else the
      binding `bindAxiom` of an unnamed answer. -/
  | axCall : String → List UArg → UStmt
  /-- `let x = f(..);` at an `extern fn` with an answer (`Block.bindAxiom`, `Endblock.bindAxiom`). -/
  | bindAx : String → String → List UArg → UStmt
  /-- `retry L until p bounded n ops .. on_exceeded h { .. }` (`Stmt.retry`): `retryBeg n p`, the pass's statements
      with the ender (`leave`/`next` or none), `ifElse`, the overflow block (the handler's call), `blkEnd`. -/
  | retryBeg : Nat → UEns → UStmt
  /-- `forever L per_pass bounded n ops .. progress a { .. }` (`Stmt.forever`): `foreverBeg k` (the position of
      the assumption `a`), the pass's statements with the ender, `blkEnd`. -/
  | foreverBeg : Nat → UStmt
  /-- `narrow x to lo .. hi else { .. }` (`Block.narrow`): `narrowBeg x lo hi`, the statements of the `else`
      branch with its ender (`ret`/`leave`/`next`), `blkEnd`; the rest of the block reads `x` at `lo .. hi`. -/
  | narrowBeg : String → Int → Int → UStmt
  | setVarB : String → UEns → UStmt
  /-- `if c { … } else { … }` is flat too: `wennAuf c`, the then-statements, `sonst`, the else-statements,
      `zu` (an `else if` is an `if` in the else part; an absent `else` is an empty one). -/
  | ifBeg : UEns → UStmt
  | ifElse : UStmt
  /-- `traverse i over slots of T [invariant p] { … }`: `schleifeAuf binder table invariant`, the body, `zu`.
      The binder is an index into `T` inside the body, and `leave`/`next` name it. -/
  | loopBeg : String → String → UEns → UStmt
  /-- `return [v];` inside a block (`Stmt.ret`; the trailing return of a body stays `URet`). -/
  | ret : URet → UStmt
  /-- `leave i;` / `next i;`: exit / end the pass of the innermost `traverse` (`Stmt.leave`/`Stmt.next`). -/
  | leave : String → UStmt
  | next : String → UStmt
  /-- `let x = d.R;` through a device handle `d` (`Block.regRead`): binder, device, register. -/
  | regRead : String → String → String → UStmt
  /-- `let x = d.R else (e) { .. }` at a register with `requires p else A::B` (`Block.regReadElse`):
      `regReadElse x D R`, the statements of the `else` branch with its ender, `blkEnd`; the reason `e` is not
      in scope there (the model's `else` branch is an end block over the outer scope). -/
  | regReadElse : String → String → String → UStmt
  /-- `d.R = v;` (`Stmt.regWrite`): device, register, value. -/
  | regWrite : String → String → USide → UStmt
  /-- `d.R = p;` at a truth-valued register: device, register, predicate. -/
  | regWriteB : String → String → UEns → UStmt
  /-- `transition T.slots[i].f : A -> B;` (`Stmt.shift`): table, field, index, the state, the stage numbers. -/
  | shiftTab : String → String → UIdx → String → Int → Int → UStmt
  /-- `let p [: fn(..)] = &f;` (`Block.bind` of `Expr.fnref`): binder, function, the signature number of the
      pointer's type (`f`'s own without a written type). -/
  | bindFnref : String → String → Nat → UStmt
  /-- `p(..);` through a function pointer (`Stmt.callInd`): the pointer, the function it points at, the arguments. -/
  | callInd : String → String → List UArg → UStmt
  /-- `let y = p(..);` (`Block.bindCallInd`): binder, pointer, function, arguments. -/
  | bindCallInd : String → String → String → List UArg → UStmt
  /-- `let x = A awaits { p, q };` (`Block.awaits`): binder, atomic; the payload is the declared one. -/
  | awaitBind : String → String → UStmt
  /-- `r->f = v;` through a reference local `r` into an open table (`Stmt.assignSlotRef`). -/
  | assignRef : String → String → USide → UStmt
  /-- `let x [: T] = v;` of an aggregate value (`Block.bind`): `T` the declared type the value is fitted to. -/
  | bindW : String → Option Ty → USide → UStmt
  /-- `X = o;` at an option static (`Stmt.assignGlob` at `Ty.opt`). -/
  | assignGlobO : String → UOpt → UStmt
  /-- `let x = A exchange update(v) { … } …;` (`Block.exchange`): binder, static, update binder, the guarded values
      and the last value of the body (`if c₁ { return e₁ } … return e`, the new value `Expr.wenn c₁ e₁ (… e)`, read
      with `v` the old value). -/
  | tausch : String → String → String → List (UEns × USide) → USide → UStmt
  /-- `if c { … } else { … }` as the last statement of a block whose two arms both end (`Endblock.ite`); the arms
      and markers as at `ifBeg`. -/
  | ifEnde : UEns → UStmt
  /-- An array traversal binds its actual element under the private finite index. -/
  | arrayLoopBeg : String → USide → UEns → UStmt
  /-- `reset A at i count n;` at a zero-initialized static array (C18): the static as
      written and the two evaluated operands. The lowering refuses it until the checked
      range-store expansion and page-return bridge are proved; `reset A;` keeps its counter store.
      constructor positions keep their names. -/
  | resetRange : String → USide → USide → UStmt
  /-- Optional-result axiom binding; the continuation retains its scope for a void answer. -/
  | bindOptBeg : String → String → List UArg → UStmt
  /-- Optional-result axiom binding with an end-block reason continuation. -/
  | bindOptElseBeg : String → String → List UArg → String → UStmt
  /-- IEEE introductions retain their rational literal or operation and checked result bounds. -/
  | floatLit : String → (Int × Int) → (Int × Int) → (Int × Int) → UStmt
  | float : String → GleitOp → USide → USide → (Int × Int) → (Int × Int) → UStmt
  /-- Required narrowing `narrow x to lo .. hi` with no `else` (C15, from
      `SAnw.trimReq`): `narrowReqBeg x lo hi`; the rest of the block reads `x`
      at `lo .. hi`. Out of range is `Logik.kapazitaet` under the caller's
      capacity duty (`Block/Endblock.narrowRequired`); there is no failure
      continuation and no `blkEnd`. Appended at the end, so earlier
      constructor positions keep their names. -/
  | narrowReqBeg : String → Int → Int → UStmt
  /-- Shared discard-call handler marker: foreign callee or local function pointer. -/
  | axCallElseBeg : String → List UArg → String → UStmt
  /-- `retires m;`: explicit discharge of one held linear mark. -/
  | retires : String → UStmt
  deriving DecidableEq, Repr
/-- One elaborated table: slot count and one integer range per
    slot field (the `TableModel` of `lean_g.rs`). -/
structure UTab where
  name : String
  count : Int
  cols : List (String × (Int × Int))
  /-- The names of the `bool` fields. A bool field keeps its place in `felder` (with the
      placeholder range `0 .. 1`, so every field index is the position it always was); its
      TYPE is `Ty.bool`, and it is never read or written as a number. -/
  bools : List String := []
  /-- The table of an `arena A capacity lo .. hi of T;` (`ArenaForm.tab`): `count` is `hi`, the one field is
      `wert`, and the counter is the static `A#used` (`ArenaForm.zaehl`). -/
  arena : Bool := false
  /-- The option fields (`n : option index into T`): the field name and the number of the table `T`. Like a bool
      field an option field keeps its place in `cols` (placeholder range `0 .. 1`); its TYPE is `Ty.opt` of the
      count of `T`. -/
  opts : List (String × Nat) := []
  /-- `table T .. shared`: the carrier is reachable from more than one thread (`D.geteilt`); a shared table
      has a guard (the elaborator refuses one without). -/
  shared : Bool := false
  /-- `table T from p`: the table is OPEN and `p` is its provider (`Deklaration.offen`/`anbieter`); its count is 0. -/
  von : Option String := none
  /-- `table T owner m`: the owner mark guarding the table (`Deklaration.eigner`/`braucht`); `none` without one. -/
  owner : Option String := none
  /-- The aggregate fields (`[T; N]`, `string max N`): the field name and its type. Like a bool field an aggregate
      field keeps its place in `cols` (placeholder range `0 .. 0`); its TYPE is the aggregate. -/
  werte : List (String × Ty) := []
  /-- The wrapping fields (`f : u32 wrapping`): the field name and its modulus `2^w`. -/
  wraps : List (String × Int) := []
  /-- The fields of a tagged type: the field name and the type's name as written, then (`uSumTabs`) its position;
      such a field is an aggregate field (`werte`) of `Ty.sum`. -/
  sumNamen : List (String × String) := []
  sumFelder : List (String × Nat) := []
  /-- `tree { parent p, child c, sibling s }`: the role and the field of each edge. -/
  kanten : List (String × String) := []
  /-- The `index into T` fields: the field and the name of `T` (their range is set by `uIdxTabs`). -/
  idxNamen : List (String × String) := []
  /-- C13: the declared STORAGE width in bits of each field written as a bare unsigned word (`u8` .. `u64`, with or
      without a range, or an alias of one): what a builtin over a read of the field names its width from. A field
      of any other type has no entry. -/
  breiten : List (String × Nat) := []
  space : Nat := 0
  deriving DecidableEq, Repr
/-- One elaborated lock: rank and the guarded table names (the
    `LockModel` of `lean_g.rs`; the `held` budget travels
    nowhere, like `costs`). -/
structure ULock where
  name : String
  rank : Int
  guard : List String
  /-- `masks irqs`: taking the lock masks interrupts (`D.maskiert`, lane 255). -/
  masks : Bool := false
  /-- `invariant p`: the lock invariant over the carriers it protects (`SperrInv.inv`, re-established at every
      release -- a duty of the user, not owed at a `return`). -/
  inv : Option UEns := none
  deriving DecidableEq, Repr
/-- The type of a static: ONE value, an integer range, `bool`, or an aggregate (`Ty.arr`, `Ty.str`). -/
inductive GTy
  | int : Int → Int → GTy
  | bool : GTy
  | wert : Ty → GTy
  deriving DecidableEq, Repr
def GTy.toTy : GTy → Ty
  | .int lo hi => .int lo hi
  | .bool => .bool
  | .wert τ => τ
/-- A constant initial value of an aggregate static: zero memory (`= 0`), a number, a truth value, the bytes of a
    string, or an array literal (`nil`/`cons`, element by element). -/
inductive UKonst
  | null : UKonst
  | zahl : Int → UKonst
  | wahr : Bool → UKonst
  | text : List Int → UKonst
  | nil : UKonst
  | cons : UKonst → UKonst → UKonst
  /-- A case of a tagged type: its position and its payload (`null` without one). -/
  | fall : Nat → UKonst → UKonst
  /-- A product constant: the declaration number and every field constant in order. -/
  | product : Nat → List UKonst → UKonst
  deriving DecidableEq, Repr
/-- One elaborated static (`static [mut] n : T = init;`): `init` is its `sp0` value (a numeral, `0`/`1` for a
    `bool`). `var` is `mut`: only a `mut` static is written. -/
structure UGlob where
  name : String
  ty : GTy
  init : Int
  /-- The initial value of an aggregate static (`GTy.wert`). -/
  initK : UKonst := .null
  /-- An option static (`option index into T`): the name of `T` as written, and its number once the tables are read
      (`uOptGlobs`; its type is then `Ty.opt` of the count of `T`). -/
  optName : Option String := none
  optNum : Option Nat := none
  /-- A static of a tagged type: the name of the type as written, and its position once the types are read
      (`uSumGlobs`; its type is then `Ty.sum` of the specification). -/
  sumName : Option String := none
  sumNum : Option Nat := none
  var : Bool := false
  /-- An `atomic` item (`Deklaration.atomar`): read and stored without a lock, ordered by the machine. -/
  atomic : Bool := false
  /-- Reachable from more than one thread (`D.ggeteilt`): `static .. shared;` (which then has a guard), and every
      `atomic` (an atomic exists to be shared: its accesses are ordered by the machine, A10). -/
  shared : Bool := false
  /-- The payload of an atomic (`atomic A : T publishes { p, q }`, `D.nutzlast`): the names of statics, in the
      written order. -/
  nutzlast : List String := []
  /-- C13: the declared STORAGE width in bits of a static of a bare unsigned word type (`0`: none). -/
  breite : Nat := 0
  /-- Source placement; consumed only after image-layout correspondence is available. -/
  placement : Option ProfilBindung.PlatzEintrag := none
  deriving DecidableEq, Repr
/-- A source reason declaration, retaining its resolved descriptor for the channel migration. -/
structure UWhy where
  name : String
  cases : List String
  /-- Absent only in manually supplied intermediate fixtures; never synthesized by source export. -/
  descriptor : Option ReasonSpec := none
  deriving DecidableEq, Repr
/-- One ordered tagged schema. Source collection retains `STyp`; model admission resolves
    payloads to the current kernel's representation. No case or payload is discarded. -/
structure USum (Payload : Type := Ty) where
  name : String
  cases : List (String × Option Payload)
  deriving DecidableEq, Repr
/-- The complete ordered payload schema, independent of its resolution stage. -/
def USum.spec {Payload : Type} (s : USum Payload) : List (Option Payload) := s.cases.map (·.2)
/-- One invariant (`table T { .. invariant I cost .. runs .. : p; }` or `group G over { T, U } { invariant I .. }`,
    `D.Inv`): its name, its carriers -- tables and statics, by name (`D.traeger`) -- and its predicate over no parameter (`Programm.invariante`,
    read under the guards of its carriers, `invSicht`). -/
structure UInv where
  name : String
  traeger : List String
  pred : UEns
  deriving DecidableEq, Repr
end Gabbro.Grammatik.Parser.Uebersetze
