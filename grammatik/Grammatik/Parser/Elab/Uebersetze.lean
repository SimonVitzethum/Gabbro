/-
  File:      Grammatik/Parser/Uebersetze.lean
  Subject:   T3 PART 4: from the parsed surface tree to the G program.

  The Lean parser covers the whole surface (lanes 135/154/157);
  the Rust exporter `gabbro lean-g` (lane 144,
  `crates/gabbro-check/src/lean_g.rs`) turns a checked unit into
  the G program term `gP : Programm gD` (see
  `grammatik/Grammatik/Export104.lean`). This file closes the
  loop in Lean: an elaborator from the parsed surface tree
  (`SItemTief` list) to the same declaration/program shape the
  exporter produces.

  Two stages, like the exporter (collect, then translate):

  * surface to U: `elabU` maps the fragment `lean_g.rs`
    exports -- tables, locks with `Held`, `impl` fns with
    pointer/index/range params, comparison contracts over slot
    reads/`old`/`result`/literals, straight-line bodies of slot
    writes, direct calls, trailing return -- to plain data
    (`UProg`). Every other form is an explicit `.error`
    (the `Except String` channel; no new diagnostic codes).
  * U to G: `lowerU` assembles the `Programm gD` term over the
    exporter's declaration universe `G104_referenz.gD`.

  The 104 instance: `tt104` (token literal), `items104` (parse
  result literal), `uExp104` (elaboration result literal), with
  one kernel check per stage (`u104lex`, `u104parse`,
  `u104elab`) plus the lowering pin (`u104lower : ... = ...
  := rfl`, proof irrelevance covering the proof terms), the
  data agreement (`u104data`, same shape as `export104_data`)
  and the fragment/footprint checks on the Lean-parsed program
  (`u104fragment`, `u104fuss`).
-/
import Grammatik.Korpus.Programme.Export104
import Grammatik.Parser.Item.ElementTief

namespace Gabbro.Grammatik.Parser.Uebersetze

set_option maxRecDepth 100000

/-- An index into a table: a literal or an index parameter. -/
inductive UIdx
  | lit : Int → UIdx
  | param : String → UIdx
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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
  | freshPtr : String → Bool → UArg
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
  deriving DecidableEq, Repr

/-- A `reason` declaration: its name and the names of its cases in order (`Ty.why` of their number). -/
structure UWhy where
  name : String
  cases : List String
  deriving DecidableEq, Repr

/-- A `tagged type` declaration: its cases in order, each with the range of its payload or none
    (`Ty.sum` of their specifications). -/
structure USum where
  name : String
  cases : List (String × Option (Int × Int))
  deriving DecidableEq, Repr

/-- The specification of a tagged type: the payload range of each case (`Ty.sum cs`). -/
def USum.spec (s : USum) : List (Option (Int × Int)) := s.cases.map (·.2)

/-- One `state S { transition t { f : A -> B } .. }` (`D.erlaubt`): its stages, numbered 0, 1, 2, .. in the order
    they are first written, and the allowed pairs (one per `transition` line, as stage numbers). The field it
    governs is the field a `transition T.slots[i].f : A -> B;` statement is applied to (Simon, 2026-10-21). -/
structure UZustand where
  name : String
  stufen : List String
  paare : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- One invariant (`table T { .. invariant I cost .. runs .. : p; }` or `group G over { T, U } { invariant I .. }`,
    `D.Inv`): its name, its carrier tables (`D.traeger`) and its predicate over no parameter (`Programm.invariante`,
    read under the guards of its carriers, `invSicht`). -/
structure UInv where
  name : String
  traeger : List String
  pred : UEns
  deriving DecidableEq, Repr

/-- One device register (`device D .. { reg R : T @off class K .. }`, `D.Reg`): its device and name, the range
    of its type (`D.rtyp`, always an integer range: `regdecl` reads an `intty`), its class (`D.rklasse`), the
    register its writes carry the other bits from (`mirrors R from M` names `M` at `R`, `D.spiegel`), the
    carriers its answer rests on (`depends { .. }`, `D.rtraeger`: table or static names), and its promise: a
    `requires p` WITHOUT `else` is the device's promise about every value read (`D.rzusage`, `zusage`); a
    `requires p else A::B` makes the read fallible instead (`Block.regReadElse`, `pruefung`), and then the
    device promises nothing. Both predicates name the register itself as their one variable. -/
structure UReg where
  dev : String
  name : String
  lo : Int
  hi : Int
  klasse : Regklasse
  spiegel : Option String := none
  traeger : List String := []
  zusage : Option UEns := none
  pruefung : Option UEns := none
  /-- A truth-valued register (`reg R : bool`): `Ty.bool`, the promise read at `0`/`1`. -/
  bool : Bool := false
  deriving DecidableEq, Repr

/-- The type of a register: a truth value, or its integer range. -/
def UReg.ty (g : UReg) : Ty := bif g.bool then .bool else .int g.lo g.hi

/-- A parameter kind: a pointer to a table, an index into one,
    or a plain integer range (kept beside the `Ty` so an index
    parameter stays recognizable after `Ty.index` unfolds it to
    `.int 0 (n - 1)`). -/
inductive UParamArt
  | ptr : Nat → Bool → UParamArt
  | index : Nat → UParamArt
  | int : UParamArt
  /-- A truth value: a `bool` parameter or a `let` of a truth value (`Ty.bool` in the context). -/
  | bool : UParamArt
  /-- An `option index into T` parameter or local, `T` the table number (`Ty.opt` of its count). -/
  | opt : Nat → UParamArt
  /-- A reason (`Ty.why n`): the reason bound by `let .. else (e) { .. }`, `n` the position of its declaration. -/
  | why : Nat → UParamArt
  /-- A value of a tagged type (`Ty.sum`), `n` the position of its declaration. -/
  | sum : Nat → UParamArt
  /-- A function pointer `fnptr n` (`Ty.fnptr n`): a parameter or `let` of a pointer type (`n` its signature
      number, behind the functions'), or `let p = &f;` (`n` the number of `f`, its own signature). -/
  | fnptr : Nat → UParamArt
  /-- A reference into the open table number `n` (`Ty.ref n`): a local bound to a provider's answer. -/
  | ref : Nat → UParamArt
  /-- An aggregate value (`Ty.arr`, `Ty.str`): its type stands beside the kind. -/
  | wert : UParamArt
  deriving DecidableEq, Repr

/-- The kind of a local bound to a register read. -/
def UReg.art (g : UReg) : UParamArt := bif g.bool then .bool else .int


/-- The elaboration context of one function body or contract:
    parameter names, kinds and types in order, the tables and
    locks, the held lock names, the optional result range and
    the function name (for errors). -/
structure UCtx where
  names : List String
  kinds : List UParamArt
  types : List Ty
  tabs : List UTab
  locks : List ULock
  held : List String
  res : Option (Int × Int)
  resBool : Bool := false
  fname : String
  /-- The declared STORAGE width in bits of each parameter (`0` when it is not a bare unsigned word
      `u8`/`u16`/`u32`/`u64`, optionally with a range): what `~p` reads. -/
  bits : List Nat := []
  /-- The unit's type aliases: `T(e)` and `T::max` name a type. -/
  alias : List (String × (Int × Int))
  /-- The unit's `const N : T = v;` -- inlined as a number at every use (`tr_typed`). -/
  lits : List (String × Int)
  /-- The binders of the enclosing `traverse` loops, innermost first (`leave i`/`next i` name the first). -/
  loops : List String := []
  /-- The unit's statics. -/
  globs : List UGlob := []
  /-- The names of the `let mut` locals in scope (a later binding of the same name takes it out). -/
  muts : List String := []
  /-- The unit's `assume` items (`D.Annahme`, beside the memory model's `a10`), in order. -/
  annahmen : List String := []
  /-- The result is `option index into T`: the number and the count of `T`. -/
  resOpt : Option (Nat × Int) := none
  /-- The unit's `reason` declarations, in order. -/
  whys : List UWhy := []
  /-- The reason channel of the function (`-> T or R`): the position of `R` and its number of cases. -/
  kanal : Option (Nat × Nat) := none
  /-- The unit's `tagged type` declarations, in order. -/
  sums : List USum := []
  /-- The result is a tagged type: its position and its specification. -/
  resSum : Option (Nat × List (Option (Int × Int))) := none
  /-- The result is a reason (`-> R`): the position of `R` among the unit's reasons and its number of cases. -/
  resWhy : Option (Nat × Nat) := none
  /-- The result is an aggregate value (`Ty.arr`, `Ty.str`): its type. -/
  resTy : Option Ty := none
  /-- The unit's `spec fn`s (name, parameter names, predicate): inlined at every use in a contract (SUGAR, `M130`). -/
  specs : List (String × List String × SExpr) := []
  /-- The unit's constant arrays (`const T : [u32; N] = [..]`): their folded literal at every use. -/
  arrKonst : List (String × USide) := []
  /-- The unit's device registers. -/
  regs : List UReg := []
  /-- The unit's `state` items. -/
  zustaende : List UZustand := []
  /-- The device handles in scope: a parameter `d : D` (or `d : ptr<space, rights> D`) and its device `D`.
      A handle is no value of the model (a register is outside the world, `D.Reg`): it is erased from the
      parameters and only names the device of `d.R`. -/
  griffe : List (String × String) := []
  /-- The unit's function-pointer types by text (`UProg.ptrKeys`) and their first signature number (the number
      of functions); their heads stand in the head list under the names `fn#j` (`elabZeigerTyp`). -/
  zeiger : List String := []
  zeigerBasis : Nat := 0

/-- One elaborated function: parameters with their `Ty`,
    the optional result range, the held lock names, the written
    table names, the `ensures` list and the body (the
    `CheckedFn` of `lean_g.rs`). -/
structure UFn where
  name : String
  params : List (String × Ty)
  kinds : List UParamArt
  res : Option (Int × Int)
  /-- The result is `bool` (then `res` is `none`). -/
  resBool : Bool := false
  /-- The result is `option index into T`: the number and the count of `T` (then `res` is `none`). -/
  resOpt : Option (Nat × Int) := none
  /-- The result is a tagged type: its position and its specification (then `res` is `none`). -/
  resSum : Option (Nat × List (Option (Int × Int))) := none
  /-- The result is a reason (`-> R`): the position of `R` among the unit's reasons and its number of cases. -/
  resWhy : Option (Nat × Nat) := none
  /-- The result is an aggregate value: its type (then `res` is `none`). -/
  resTy : Option Ty := none
  /-- The number of reasons of the channel `-> T or R` (`Signatur.gruende`), 0 without a channel. -/
  gruende : Nat := 0
  held : List String
  puts : List String
  /-- The statics it writes (`effects { writes X }`). -/
  gputs : List String := []
  gives : List UEns
  /-- The `requires` predicates beside `Held(..)` (`Programm.requires`, their conjunction). -/
  needs : List UEns := []
  body : List UStmt
  ret : URet
  /-- The lock floor (`Signatur.boden`): filled after elaboration by `uMitBoden` with the rule `floorOf`. -/
  boden : Option Int := none
  deriving DecidableEq, Repr

/-- The kind of a value of type `τ` that is no pointer, index, option, sum or reason: an aggregate or a number. -/
def uArtVon : Ty → UParamArt
  | .arr _ _ | .str _ => .wert
  | _ => .int

/-- The scope after a `let x` of a number with the computed range `w`: `x` is the first name (it
    shadows a parameter), `Block.bind` puts its type first in the context. -/
def UFn.mitBindung (f : UFn) (x : String) (w : Int × Int) : UFn :=
  { f with params := (x, .int w.1 w.2) :: f.params, kinds := .int :: f.kinds }

/-- The scope after a `let x` of a truth value. -/
def UFn.mitBindungB (f : UFn) (x : String) : UFn :=
  { f with params := (x, Ty.bool) :: f.params, kinds := .bool :: f.kinds }

/-- The scope after `let x = v` of a value of type `τ` (a number or a truth value). -/
def UFn.mitTy (f : UFn) (x : String) : Ty → UFn
  | .int lo hi => f.mitBindung x (lo, hi)
  | .bool => f.mitBindungB x
  | .why n => { f with params := (x, Ty.why n) :: f.params, kinds := .why 0 :: f.kinds }
  | .ref n => { f with params := (x, Ty.ref n) :: f.params, kinds := .ref n :: f.kinds }
  -- every other type is bound too, so that the positions of the names stay those of the context
  | τ => { f with params := (x, τ) :: f.params, kinds := uArtVon τ :: f.kinds }

/-- The scope after `let x` of a tagged value of the type at `num` with the specification `cs`. -/
def UFn.mitSum (f : UFn) (x : String) (num : Nat) (cs : List (Option (Int × Int))) : UFn :=
  { f with params := (x, Ty.sum cs) :: f.params, kinds := .sum num :: f.kinds }

/-- The scope after `let x` of an option value over the table `num` of `cnt` slots. -/
def UFn.mitOpt (f : UFn) (x : String) (num : Nat) (cnt : Int) : UFn :=
  { f with params := (x, Ty.opt cnt) :: f.params, kinds := .opt num :: f.kinds }

/-- The scope inside `traverse b over slots of T`: `b` is an index into table number `num` of `cnt` slots. -/
def UFn.mitIndex (f : UFn) (b : String) (num : Nat) (cnt : Int) : UFn :=
  { f with params := (b, .index cnt) :: f.params, kinds := .index num :: f.kinds }

/-- The scope after `let p = &f;`: `p` a pointer to function number `n`. -/
def UFn.mitFnptr (f : UFn) (p : String) (n : Nat) : UFn :=
  { f with params := (p, Ty.fnptr n) :: f.params, kinds := .fnptr n :: f.kinds }

/-- The result type of an elaborated function: `bool`, an integer range, or none. -/
def UFn.ergTy (f : UFn) : Option Ty :=
  if let some τ := f.resTy then some τ else
  if f.resBool then some Ty.bool else
  match f.resOpt with
  | some (_, n) => some (Ty.opt n)
  | none =>
    match f.resSum with
    | some (_, cs) => some (Ty.sum cs)
    | none =>
      match f.resWhy with
      | some (_, n) => some (Ty.why n)
      | none => f.res.map fun r => .int r.1 r.2

/-- One foreign body (`extern fn`, `= asm { .. }`, `D.Ax`): its parameters, its answer (`none`, a number, a truth
    value or `never`) and what it writes (`effects { writes .. }`: `D.aschreibt`/`D.agschreibt`). -/
structure UAx where
  name : String
  params : List Ty
  kinds : List UParamArt
  res : Option Ty
  /-- The number of reasons of its channel (`D.agruende`), 0 without one. -/
  gruende : Nat := 0
  /-- The tables it writes. -/
  puts : List String := []
  /-- The statics it writes. -/
  gputs : List String := []
  deriving DecidableEq, Repr

/-- The elaborated program: tables, locks, functions. -/
structure UProg where
  tabs : List UTab
  locks : List ULock
  fns : List UFn
  /-- The foreign bodies (`extern fn`). -/
  axs : List UAx := []
  /-- The `assume` items, in order (`D.Annahme`). -/
  annahmen : List String := []
  /-- The `reason` declarations, in order. -/
  whys : List UWhy := []
  /-- The `tagged type` declarations, in order. -/
  sums : List USum := []
  /-- The roots of every `start { .. };` of a body, each once, in body order: the threads created at run time
      (`Einheit.gestartet`; the checker Bool judges them as pool routines, they stand twice in `Einheit.ws`). -/
  gestartet : List String := []
  /-- The dispatch roots of the unit's `entry` items (function names, each a parameterless function of
      the unit): thread roots of the goal's runtime premise (`Einheit.starts`). -/
  roots : List String := []
  /-- The functions entered by HARDWARE: the dispatch roots of the `entry` items that carry a `via`
      word (`Programm.unterbricht`, `Kontext::unterbricht` of the checker). Each is also a root. -/
  hands : List String := []
  /-- The statics (`Deklaration.Glob`). -/
  globs : List UGlob := []
  /-- The device registers (`Deklaration.Reg`), in declaration order. -/
  regs : List UReg := []
  /-- The invariants (`Deklaration.Inv`): table invariants in table order, then group invariants. -/
  invs : List UInv := []
  /-- The `state` items, in order. -/
  zustaende : List UZustand := []
  /-- The governed fields: table, field and the state whose `transition` statements are applied to it. -/
  regiert : List (String × String × String) := []
  /-- The function-pointer TYPES of the unit (`fn(..) -> T effects { .. } costs <= e ops`), each once by its
      text: their signatures stand behind the functions' (`sigAt`: number `fns.length + j`), and a function
      that conforms to one may be its value (`Deklaration.passt`, 2026-10-21). Bodies stay empty. -/
  ptrs : List UFn := []
  /-- The texts of `ptrs`, in the same order (the key a parameter or `let` type is found by). -/
  ptrKeys : List String := []
  deriving DecidableEq, Repr

/-- The members: a single module wrapper is unwrapped, a bare
    list passes through (104 wraps everything in
    `module beispiel::referenz`). -/
def uFlach : Nat → List SItemTief → List SItemTief
  | 0, ms => ms
  | _ + 1, [] => []
  | f + 1, .modT _ b :: rest => uFlach f b ++ uFlach f rest
  | f + 1, it :: rest => it :: uFlach f rest

/-- The members of a unit: every module wrapper is opened, so the items of nested modules stand in one
    list (`lean_g.rs` resolves names by their last segment as well). The fuel is one unit per item
    visited; a unit past it keeps its module wrapper and is then refused loudly by `uRestFehler`. -/
def uMembers (ms : List SItemTief) : List SItemTief := uFlach 100000 ms

/-- A bound of a range type: a numeral, a negated numeral, a constant (the `alias` list carries the unit's
    constants as `(name, (v, v))`) or `+ - *` over these (`in 0 .. NSLOTS - 1`). -/
def uSchranke (alias : List (String × (Int × Int))) : SExpr → Option Int
  | .lit n => some (Int.ofNat n)
  | .variable c =>
    (alias.find? (fun p => strEq p.1 c)).bind fun p => if p.2.1 == p.2.2 then some p.2.1 else none
  | .un "-" a => (uSchranke alias a).map (fun v => -v)
  | .un "-()" a => (uSchranke alias a).map (fun v => -v)
  | .bin op a b =>
    match uSchranke alias a, uSchranke alias b with
    | some x, some y =>
      if strEq op "+" then some (x + y)
      else if strEq op "-" then some (x - y)
      else if strEq op "*" then some (x * y)
      else none
    | _, _ => none
  | _ => none

/-- The constant scope: `const N : u32 = v;` travels as
    (`N`, `v`); any other `const` form has no G form
    (`LG005`: a count must be a numeral). -/
def uConsts : List SItemTief → List (String × Int)
  | [] => []
  | .constT n _ (.one (.lit v)) :: rest =>
    (n, Int.ofNat v) :: uConsts rest
  | _ :: rest => uConsts rest

/-- Lookup in an association list, with an explicit error. -/
def uSuch (was : String) (xs : List (String × α)) (n : String) : Except String α :=
  match xs with
  | [] => .error (was ++ " unknown: " ++ n)
  | (m, v) :: rest => if strEq m n then .ok v else uSuch was rest n

/-- The built-in integer types as ranges: `uN` is `0 .. 2^N - 1`, `iN` is `-2^(N-1) .. 2^(N-1) - 1`,
    N = 1 .. 64 (the width sugar of the surface, `beispiele/73`). A literal table and not a
    computation on names: the chain instances evaluate the elaborator in the kernel, and the
    kernel must never decode a `String` (`Lexer.lean`, O13). A user `type` of the same name
    comes FIRST (`uTypName`). -/
def eingebauteInt : List (String × (Int × Int)) :=
  [
  ("u1", (0, 1)), ("u2", (0, 3)), ("u3", (0, 7)), ("u4", (0, 15)), ("u5", (0, 31)),
  ("u6", (0, 63)), ("u7", (0, 127)), ("u8", (0, 255)), ("u9", (0, 511)), ("u10", (0, 1023)),
  ("u11", (0, 2047)), ("u12", (0, 4095)), ("u13", (0, 8191)), ("u14", (0, 16383)),
  ("u15", (0, 32767)), ("u16", (0, 65535)), ("u17", (0, 131071)), ("u18", (0, 262143)),
  ("u19", (0, 524287)), ("u20", (0, 1048575)), ("u21", (0, 2097151)), ("u22", (0, 4194303)),
  ("u23", (0, 8388607)), ("u24", (0, 16777215)), ("u25", (0, 33554431)), ("u26", (0, 67108863)),
  ("u27", (0, 134217727)), ("u28", (0, 268435455)), ("u29", (0, 536870911)),
  ("u30", (0, 1073741823)), ("u31", (0, 2147483647)), ("u32", (0, 4294967295)),
  ("u33", (0, 8589934591)), ("u34", (0, 17179869183)), ("u35", (0, 34359738367)),
  ("u36", (0, 68719476735)), ("u37", (0, 137438953471)), ("u38", (0, 274877906943)),
  ("u39", (0, 549755813887)), ("u40", (0, 1099511627775)), ("u41", (0, 2199023255551)),
  ("u42", (0, 4398046511103)), ("u43", (0, 8796093022207)), ("u44", (0, 17592186044415)),
  ("u45", (0, 35184372088831)), ("u46", (0, 70368744177663)), ("u47", (0, 140737488355327)),
  ("u48", (0, 281474976710655)), ("u49", (0, 562949953421311)), ("u50", (0, 1125899906842623)),
  ("u51", (0, 2251799813685247)), ("u52", (0, 4503599627370495)), ("u53", (0, 9007199254740991)),
  ("u54", (0, 18014398509481983)), ("u55", (0, 36028797018963967)),
  ("u56", (0, 72057594037927935)), ("u57", (0, 144115188075855871)),
  ("u58", (0, 288230376151711743)), ("u59", (0, 576460752303423487)),
  ("u60", (0, 1152921504606846975)), ("u61", (0, 2305843009213693951)),
  ("u62", (0, 4611686018427387903)), ("u63", (0, 9223372036854775807)),
  ("u64", (0, 18446744073709551615)), ("i1", (-1, 0)), ("i2", (-2, 1)), ("i3", (-4, 3)),
  ("i4", (-8, 7)), ("i5", (-16, 15)), ("i6", (-32, 31)), ("i7", (-64, 63)), ("i8", (-128, 127)),
  ("i9", (-256, 255)), ("i10", (-512, 511)), ("i11", (-1024, 1023)), ("i12", (-2048, 2047)),
  ("i13", (-4096, 4095)), ("i14", (-8192, 8191)), ("i15", (-16384, 16383)),
  ("i16", (-32768, 32767)), ("i17", (-65536, 65535)), ("i18", (-131072, 131071)),
  ("i19", (-262144, 262143)), ("i20", (-524288, 524287)), ("i21", (-1048576, 1048575)),
  ("i22", (-2097152, 2097151)), ("i23", (-4194304, 4194303)), ("i24", (-8388608, 8388607)),
  ("i25", (-16777216, 16777215)), ("i26", (-33554432, 33554431)), ("i27", (-67108864, 67108863)),
  ("i28", (-134217728, 134217727)), ("i29", (-268435456, 268435455)),
  ("i30", (-536870912, 536870911)), ("i31", (-1073741824, 1073741823)),
  ("i32", (-2147483648, 2147483647)), ("i33", (-4294967296, 4294967295)),
  ("i34", (-8589934592, 8589934591)), ("i35", (-17179869184, 17179869183)),
  ("i36", (-34359738368, 34359738367)), ("i37", (-68719476736, 68719476735)),
  ("i38", (-137438953472, 137438953471)), ("i39", (-274877906944, 274877906943)),
  ("i40", (-549755813888, 549755813887)), ("i41", (-1099511627776, 1099511627775)),
  ("i42", (-2199023255552, 2199023255551)), ("i43", (-4398046511104, 4398046511103)),
  ("i44", (-8796093022208, 8796093022207)), ("i45", (-17592186044416, 17592186044415)),
  ("i46", (-35184372088832, 35184372088831)), ("i47", (-70368744177664, 70368744177663)),
  ("i48", (-140737488355328, 140737488355327)), ("i49", (-281474976710656, 281474976710655)),
  ("i50", (-562949953421312, 562949953421311)), ("i51", (-1125899906842624, 1125899906842623)),
  ("i52", (-2251799813685248, 2251799813685247)), ("i53", (-4503599627370496, 4503599627370495)),
  ("i54", (-9007199254740992, 9007199254740991)),
  ("i55", (-18014398509481984, 18014398509481983)),
  ("i56", (-36028797018963968, 36028797018963967)),
  ("i57", (-72057594037927936, 72057594037927935)),
  ("i58", (-144115188075855872, 144115188075855871)),
  ("i59", (-288230376151711744, 288230376151711743)),
  ("i60", (-576460752303423488, 576460752303423487)),
  ("i61", (-1152921504606846976, 1152921504606846975)),
  ("i62", (-2305843009213693952, 2305843009213693951)),
  ("i63", (-4611686018427387904, 4611686018427387903)),
  ("i64", (-9223372036854775808, 9223372036854775807))
  ]

/-- A type name as a range: the unit's own aliases, then the built-in widths. -/
def uTypName (alias : List (String × (Int × Int))) (a : String) : Except String (Int × Int) :=
  match uSuch "type" alias a with
  | .ok r => .ok r
  | .error e =>
    match eingebauteInt.find? (fun x => strEq x.1 a) with
    | .some (_, r) => .ok r
    | .none => .error e

/-- The type-alias scope: `type A = u32 in lo .. hi;` travels
    as (`A`, (`lo`, `hi`)); any other `type` body has no G form
    (`LG002`: a range where G needs a `Ty`). -/
def uAliase (consts : List (String × Int)) : List SItemTief → List (String × (Int × Int))
  | [] => []
  | .typeT _ n _ _ (.some (.range _ lo hi o)) :: rest =>
    let ks := consts.map (fun c => (c.1, (c.2, c.2)))
    match uSchranke ks lo, uSchranke ks hi with
    | some a, some b => (n, (a, if o then b - 1 else b)) :: uAliase consts rest
    | _, _ => uAliase consts rest
  -- `[opaque] type A = u64;`: the range of the word (opacity is a rule of the checker; the value is the number)
  | .typeT _ n _ _ (.some (.atom w)) :: rest =>
    match uTypName [] w with
    | .ok r => (n, r) :: uAliase consts rest
    | .error _ => uAliase consts rest
  | _ :: rest => uAliase consts rest

/-! ## Compile-time constants

    `const N : T = e;` where `e` is an expression over literals, earlier constants, `+ - * / % & | ^ << >>`,
    a limit word `T::max`/`T::min` and calls of `const fn`s (a single trailing `return e`). The value is
    computed in EXACT integers and travels as a number, like every constant (`tr_typed`). Because the
    emitted C evaluates the same expression in the declared type, EVERY intermediate value must lie in the
    range of that type -- an overflow is the checker's `M104`, and the elaborator refuses instead of
    guessing a wrap. Anything else (an array constant, a call of a non-const function, a value outside
    its type) makes the constant UNKNOWN: a use of it is then an error ("name unknown"). -/

/-- A `const fn` for the evaluator: parameter names with their ranges, the result range and the
    returned expression. -/
structure UKonstFn where
  name : String
  params : List (String × (Int × Int))
  erg : Int × Int
  rumpf : SExpr

/-- The range of a declared parameter/result type of a `const fn`: a builtin word or a literal range. -/
def uKonstBereich : STyp → Option (Int × Int)
  | .atom a => (uTypName [] a).toOption
  | .range _ lo hi o =>
    match uSchranke [] lo, uSchranke [] hi with
    | some a, some b => some (a, if o then b - 1 else b)
    | _, _ => none
  | _ => none

/-- The `const fn`s of a unit that the evaluator can run. -/
def uKonstFns : List SItemTief → List UKonstFn
  | [] => []
  | .fnT { art := "const", name, params, res := some r, fehler := .none, klauseln := _ }
      (.block [] (.some (.ret (.some e)))) :: rest =>
    match uKonstBereich r, params.mapM (fun (n, ty) => (uKonstBereich ty).map (fun b => (n, b))) with
    | some rb, some ps => { name, params := ps, erg := rb, rumpf := e } :: uKonstFns rest
    | _, _ => uKonstFns rest
  | _ :: rest => uKonstFns rest

/-- The values of a call bound to the parameters, each inside its parameter's range. -/
def uKonstBinde : List (String × (Int × Int)) → List Int → Option (List (String × Int))
  | [], [] => some []
  | (n, (pl, ph)) :: ps, v :: vs =>
    if pl ≤ v ∧ v ≤ ph then (uKonstBinde ps vs).map (fun r => (n, v) :: r) else none
  | _, _ => none

/-- The constant value of an expression, or `none`: every value stays in `lo .. hi`. Structural in the
    FUEL (so that the kernel can run it: a well-founded definition here made every probe run away). -/
def uKonstWert (lo hi : Int) (fns : List UKonstFn) (env : List (String × Int)) :
    Nat → SExpr → Option Int
  | 0, _ => none
  | f + 1, e =>
    let ok : Int → Option Int := fun v => if lo ≤ v ∧ v ≤ hi then some v else none
    match e with
    | .lit n => ok (Int.ofNat n)
    | .variable x =>
      match env.find? (fun q => strEq q.1 x) with
      | some q => ok q.2
      | none => none
    | .field (.variable ty) m =>
      match uTypName [] ty with
      | .ok (l, h) =>
        if strEq m "max" then ok h else if strEq m "min" then ok l else none
      | .error _ => none
    | .bin op a b =>
      match uKonstWert lo hi fns env f a, uKonstWert lo hi fns env f b with
      | some x, some y =>
        if strEq op "+" then ok (x + y)
        else if strEq op "-" then ok (x - y)
        else if strEq op "*" then ok (x * y)
        else if strEq op "/" then (if 0 < y then ok (x / y) else none)
        else if strEq op "%" then (if 0 < y then ok (x % y) else none)
        else if strEq op "&" then
          (if 0 ≤ x ∧ 0 ≤ y then ok (Int.ofNat (x.toNat &&& y.toNat)) else none)
        else if strEq op "|" then
          (if 0 ≤ x ∧ 0 ≤ y then ok (Int.ofNat (x.toNat ||| y.toNat)) else none)
        else if strEq op "^" then
          (if 0 ≤ x ∧ 0 ≤ y then ok (Int.ofNat (x.toNat ^^^ y.toNat)) else none)
        else if strEq op "<<" then
          (if 0 ≤ x ∧ 0 ≤ y ∧ y < 64 then ok (x * 2 ^ y.toNat) else none)
        else if strEq op ">>" then
          (if 0 ≤ x ∧ 0 ≤ y ∧ y < 64 then ok (x / 2 ^ y.toNat) else none)
        else none
      | _, _ => none
    | .call g args =>
      match fns.find? (fun k => strEq k.name g) with
      | none => none
      | some k =>
        match args.mapM (fun a => uKonstWert lo hi fns env f a) with
        | none => none
        | some vals =>
          match uKonstBinde k.params vals with
          | none => none
          | some binds =>
            match uKonstWert k.erg.1 k.erg.2 fns binds f k.rumpf with
            | some v => ok v
            | none => none
    | _ => none

/-- The constant scope of a unit: in source order, each constant may use the ones before it. A literal
    keeps the old rule (any declared type); any other expression needs a builtin-word type and the
    evaluator above. -/
def uConstsRech (fns : List UKonstFn) : List SItemTief → List (String × Int) → List (String × Int)
  | [], acc => acc
  | .constT n _ (.one (.lit v)) :: rest, acc =>
    uConstsRech fns rest (acc ++ [(n, Int.ofNat v)])
  | .constT n (.atom w) (.one e) :: rest, acc =>
    match uTypName [] w with
    | .ok (lo, hi) =>
      match uKonstWert lo hi fns acc 64 e with
      | some v => uConstsRech fns rest (acc ++ [(n, v)])
      | none => uConstsRech fns rest acc
    | .error _ => uConstsRech fns rest acc
  | _ :: rest, acc => uConstsRech fns rest acc

/-- A table by name: its number (position, what `ptr` names)
    and its slot count (what `index` names). -/
def uTabNrAux : List UTab → Nat → String → Except String (Nat × Int)
  | [], _, n => .error ("table unknown: " ++ n)
  | t :: rest, k, n =>
    if strEq t.name n then .ok (k, t.count)
    else uTabNrAux rest (k + 1) n

def uTabNr (tabs : List UTab) (n : String) : Except String (Nat × Int) :=
  uTabNrAux tabs 0 n

/-- A surface type as text, for a refusal that names what it refuses. -/
def sTypText : STyp → String
  | .atom a => a
  | .path ps => ".".intercalate ps
  | .ptr r w t => "ptr<" ++ r ++ ", " ++ w ++ "> " ++ sTypText t
  | .index o t => (if o then "option " else "") ++ "index into " ++ t
  | .range b _ _ _ => sTypText b ++ " in .."
  | .array t _ => "[" ++ sTypText t ++ "; ..]"
  | .wrap t => "wrap " ++ sTypText t
  | .embed b n _ => sTypText b ++ " embed " ++ n
  | .raw n => "raw " ++ n
  | .str _ => "string"
  | .entry n _ => "entry " ++ n

/-- A surface type as G sees it: a pointer to a table, an index
    into one, or an integer range (the `ParamTy`/`int_range` of
    `lean_g.rs`). Named address spaces other than `normal`,
    rights other than `r`/`rw`, the optional index and every
    other shape are explicit errors. -/
def uTyp (alias : List (String × (Int × Int))) (tabs : List UTab) : STyp → Except String Ty
  | .atom a =>
    match uTypName alias a with
    | .ok (lo, hi) => .ok (.int lo hi)
    | .error e => .error e
  | .range _ lo hi o =>
    match uSchranke alias lo, uSchranke alias hi with
    | some a, some b => .ok (.int a (if o then b - 1 else b))
    | _, _ => .error "type without G form"
  | .index false t =>
    match uTabNr tabs t with
    | .ok (_, c) => .ok (.index c)
    | .error e => .error e
  | .ptr raum rechte (.atom t) =>
    if !strEq raum "normal" then .error "space without G form"
    else if strEq rechte "rw" || strEq rechte "own" then
      match uTabNr tabs t with
      | .ok (num, _) => .ok (.ptr num true)
      | .error e => .error e
    else if strEq rechte "r" then
      match uTabNr tabs t with
      | .ok (num, _) => .ok (.ptr num false)
      | .error e => .error e
    else .error "pointer right without G form"
  | .array t n =>
    match uTyp alias tabs t, uSchranke alias n with
    | .ok τ, some k => if 0 ≤ k then .ok (.arr τ k.toNat) else .error "array of a negative length"
    | .error e, _ => .error e
    | _, none => .error "array length without G form"
  | .str n =>
    match uSchranke alias n with
    | some k => if 0 ≤ k then .ok (.str k.toNat) else .error "string of a negative maximum"
    | none => .error "string maximum without G form"
  | t => .error ("type without G form: " ++ sTypText t)

/-- A slot field type as an integer range (the field loop of
    `read_table`; `wrapping` and everything else are explicit
    errors). -/
def uFeldTyp (alias : List (String × (Int × Int))) : STyp → Except String (Int × Int)
  | .atom a => uTypName alias a
  | .range _ lo hi o =>
    match uSchranke alias lo, uSchranke alias hi with
    | some a, some b => .ok (a, if o then b - 1 else b)
    | _, _ => .error "field type without G form"
  | t => .error ("field type without G form: " ++ sTypText t)

mutual
/-- A constant row folded at its element type: numbers by the constant evaluator, nested rows element by element. -/
def uKonstZeile (alias : List (String × (Int × Int))) (fns : List UKonstFn) (consts : List (String × Int)) :
    Ty → SKonstWert → Option USide
  | .int lo hi, .one e => (uKonstWert lo hi fns consts 64 e).map USide.lit
  | .arr τ _, .rows ks => uKonstZeilen alias fns consts τ ks
  | _, _ => none
def uKonstZeilen (alias : List (String × (Int × Int))) (fns : List UKonstFn) (consts : List (String × Int)) :
    Ty → List SKonstWert → Option USide
  | _, [] => some .arrNil
  | τ, k :: ks =>
    match uKonstZeile alias fns consts τ k, uKonstZeilen alias fns consts τ ks with
    | some a, some r => some (.arrCons a r)
    | _, _ => none
end

/-- The constant arrays of a unit (`const T : [u32; N] = [..]`): each as its folded literal at its type. -/
def uKonstArrays (alias : List (String × (Int × Int))) (fns : List UKonstFn) (consts : List (String × Int))
    (ms : List SItemTief) : List (String × USide) :=
  ms.filterMap fun
    | .constT n t@(.array _ _) v =>
      match uTyp alias [] t with
      | .ok τ => (uKonstZeile alias fns consts τ v).map fun l => (n, .typed τ l)
      | .error _ => none
    | _ => none

/-- A count: a literal or a named constant (the `numeral` of
    `lean_g.rs`). -/
def uAnzahl (consts : List (String × Int)) : SExpr → Except String Int
  | .lit v => .ok (Int.ofNat v)
  | .variable c => uSuch "const" consts c
  | _ => .error "count without G form"

/-- The kind of a slot field. -/
inductive UFeldArt
  | zahl : UFeldArt
  | bool : UFeldArt
  /-- `option index into T`: the number of `T`. -/
  | opt : Nat → UFeldArt
  /-- An aggregate value (`[T; N]`, `string max N`): its type. -/
  | wert : Ty → UFeldArt
  /-- `u32 wrapping`: a number field whose writes are taken modulo `m` (SUGAR over `rem`, SYNTAX.md). -/
  | wrap : Int → UFeldArt
  /-- A field of a tagged type, its name as written (read with the types, `uSumTabs`). -/
  | summe : String → UFeldArt
  /-- `index into T`: a number in `0 ..< count T`, the name of `T` as written (its count is read with the tables). -/
  | idx : String → UFeldArt

/-- One slot field: no bit position, no `offset_into`, no `where`, no `reserved` (all without G
    form, like the refused arms of `read_table`). `by ops` is a writer discipline the CHECKER holds
    and has no meaning in the model -- the exporter reads the field as written (`lean_g.rs`) -- so it
    travels. A `bool` or option field is recorded as such (the second component). -/
def uFeld (alias : List (String × (Int × Int))) (tnames : List String) :
    SFeld → Except String ((String × (Int × Int)) × UFeldArt)
  | { fname, ftyp, pos := .none, bezug := .none, wo := .none,
      reserviert := false, byOps := _ } =>
    match ftyp with
    | .atom "bool" => .ok ((fname, (0, 1)), UFeldArt.bool)
    | .index true tn =>
      match tnames.findIdx? (fun x => strEq x tn) with
      | .some num => .ok ((fname, (0, 1)), UFeldArt.opt num)
      | .none => .error ("table unknown: " ++ tn)
    | .array _ _ | .str _ =>
      match uTyp alias [] ftyp with
      | .ok τ => .ok ((fname, (0, 0)), UFeldArt.wert τ)
      | .error e => .error e
    | .atom a =>
      match uFeldTyp alias (.atom a) with
      | .ok r => .ok ((fname, r), UFeldArt.zahl)
      | .error _ => .ok ((fname, (0, 0)), UFeldArt.summe a)
    | .index false tn =>
      if tnames.any (strEq · tn) then .ok ((fname, (0, 0)), UFeldArt.idx tn) else .error ("table unknown: " ++ tn)
    | .wrap t =>
      match uFeldTyp alias t with
      | .ok (0, hi) => .ok ((fname, (0, hi)), UFeldArt.wrap (hi + 1))
      | .ok _ => .error "wrapping field of a range that does not start at 0 without G form"
      | .error e => .error e
    | _ =>
      match uFeldTyp alias ftyp with
      | .ok r => .ok ((fname, r), UFeldArt.zahl)
      | .error e => .error e
  | _ => .error "slot field without G form"

def uFelder : List (String × (Int × Int)) → List String → List SFeld →
    Except String (List ((String × (Int × Int)) × UFeldArt))
  | _, _, [] => .error "table without fields"
  | alias, tnames, [f] => (uFeld alias tnames f).map ([·])
  | alias, tnames, f :: rest =>
    match uFeld alias tnames f, uFelder alias tnames rest with
    | .ok p, .ok ps => .ok (p :: ps)
    | .error e, _ | _, .error e => .error e

/-- A table of `count` slots with its fields, its invariants and its tree edges. -/
def uTabelleSlots (consts : List (String × Int)) (alias : List (String × (Int × Int))) (tnames : List String)
    (n : String) (cnt : SExpr) (sh : Bool) (fds : List SFeld) (invs : List STabTeil) (kanten : List (String × String)) :
    Except String UTab :=
  if !invs.all (fun p => match p with | .tInv _ => true | _ => false) then .error "table without G form" else
  match uAnzahl consts cnt with
  | .error e => .error e
  | .ok c =>
    -- `Self` in a field type is the table itself
    let fds := fds.map fun fd => match fd.ftyp with
      | .index o t => if strEq t "Self" then { fd with ftyp := .index o n } else fd
      | _ => fd
    match uFelder alias tnames fds with
    | .error e => .error e
    | .ok fs =>
      .ok { name := n, count := c, cols := fs.map (·.1),
            bools := (fs.filter (fun p => match p.2 with | .bool => true | _ => false)).map (·.1.1),
            opts := fs.filterMap (fun p => match p.2 with | .opt num => some (p.1.1, num) | _ => none),
            werte := fs.filterMap (fun p => match p.2 with | .wert τ => some (p.1.1, τ) | _ => none),
            wraps := fs.filterMap (fun p => match p.2 with | .wrap m => some (p.1.1, m) | _ => none),
            sumNamen := fs.filterMap (fun p => match p.2 with | .summe a => some (p.1.1, a) | _ => none),
            idxNamen := fs.filterMap (fun p => match p.2 with | .idx tn => some (p.1.1, tn) | _ => none),
            kanten := kanten, shared := sh }

/-- One table: `count` and one integer range per slot field.
/// Invariants, `ops`, tree edges, the occupancy mark, an
    `owner` mark, a `backed`/`shared` flag and a missing slot
    are explicit errors (the refused arms of `read_table`). -/
def uTabelle (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (tnames : List String) : SItemTief → Except String UTab
  | .tableT n .none (.some cnt) .none .none sh parts =>
    -- `tree { parent p, child c }` names the fields `reaches … via` and the tree domains read; it adds no carrier
    match parts.filter (fun p => match p with | .tTree _ => false | _ => true) with
    | .tSlot fds :: invs => uTabelleSlots consts alias tnames n cnt sh fds invs
        (parts.flatMap (fun p => match p with | .tTree ks => ks | _ => []))
    | _ => .error "table without G form"
  | .tableT n (.some p) .none .none .none sh (.tSlot fds :: invs) =>
    if !invs.all (fun p => match p with | .tInv _ => true | _ => false) then .error "table without G form" else
    match uFelder alias tnames fds with
    | .error e => .error e
    | .ok fs =>
      if fs.all (fun p => match p.2 with | .zahl => true | _ => false) then
        .ok { name := n, count := 0, cols := fs.map (·.1), shared := sh, von := some p }
      else .error "open table with a field other than a number without G form"
  | _ => .error "table without G form"

/-- A `protects` carrier: a table name, a field of exactly one table (the guard loop of `read_lock`), or
    a static (`gbraucht`, the lock guards that static). -/
def uTraegerTab (globs : List UGlob) : List UTab → String → Except String String
  | [], c =>
    if globs.any (fun g => strEq g.name c) then .ok c
    else .error ("guard unknown: " ++ c)
  | t :: rest, c =>
    if strEq t.name c then (if t.arena then .error "arena under a lock without G form" else .ok t.name)
    else if t.cols.any (fun (f, _) => strEq f c) then .ok t.name
    else uTraegerTab globs rest c

def uSchutzAux (globs : List UGlob) : List UTab → List SExpr → Except String (List String)
  | _, [] => .ok []
  | tabs, .variable c :: rest =>
    match uTraegerTab globs tabs c with
    | .error e => .error e
    | .ok t =>
      match uSchutzAux globs tabs rest with
      | .error e => .error e
      | .ok ts => .ok (t :: ts)
  | _, _ :: _ => .error "guard carrier without G form"

/-- One lock: a numeric rank and the guarded tables. Masking
    and the shared hold have no G form; the `held` budget is
    ignored like `costs` (both travel nowhere). -/
def uSperre (globs : List UGlob) (tabs : List UTab) : SItemTief → Except String ULock
  | .lockT n ps (.lit rk) _ .none m _ =>
    match (match m with
        | .none => .ok false
        | .some w => if strEq w "irqs" then .ok true else .error "lock masks something but irqs: no G form"
        : Except String Bool) with
    | .error e => .error e
    | .ok masks =>
      match uSchutzAux globs tabs ps with
      | .error e => .error e
      | .ok ts =>
        -- the `invariant` is read once the predicates can be (`uSperrInvs`)
        .ok { name := n, rank := Int.ofNat rk, guard := ts, masks }
  | .lockT n .. => .error ("lock without G form: " ++ n)
  | _ => .error "lock without G form"

/-- A parameter position by name (the `param_index` of
    `lean_g.rs`; unknown names are `LG005` errors). -/
def uParamNrAux : List String → Nat → String → Except String Nat
  | [], _, p => .error ("name unknown: " ++ p)
  | q :: rest, k, p =>
    if strEq q p then .ok k else uParamNrAux rest (k + 1) p

def uParamNr (ctx : UCtx) (p : String) : Except String Nat :=
  uParamNrAux ctx.names 0 p

/-- The kind of the parameter at a position. -/
def uArtBei : List UParamArt → Nat → Except String UParamArt
  | [], _ => .error "parameter outside"
  | a :: _, 0 => .ok a
  | _ :: rest, n + 1 => uArtBei rest n

/-- The open table a local reference `r` points into (`some n` for a local of kind `ref n`). -/
def uRefLokal (ctx : UCtx) (r : String) : Option Nat :=
  match uParamNr ctx r with
  | .error _ => none
  | .ok j =>
    match uArtBei ctx.kinds j with
    | .ok (.ref n) => some n
    | _ => none

/-- Every guard of the table is held (the `holds_guards` of
    `lean_g.rs`: the generation-time half of the guard
    proof). -/
def uHaeltWaechter (ctx : UCtx) (t : String) : Except String Unit :=
  let bedarf : List String :=
    ctx.locks.filterMap (fun l => if l.guard.any (strEq · t) then some l.name else none)
  if bedarf.all (fun b => ctx.held.any (strEq · b)) then .ok ()
  else .error "access without held guard"

/-- The slot count of a table by name. -/
def uAnzahlTab (tabs : List UTab) (t : String) : Except String Int :=
  match tabs.find? (fun x => strEq x.name t) with
  | .some x => .ok x.count
  | .none => .error ("table unknown: " ++ t)

/-- Two tables of the same slot count: an index into one is an index into the other (`Ty.index` is the
    count, as in the model). -/
def uGleicheAnzahl (tabs : List UTab) (m n : Nat) : Bool :=
  match tabs[m]?, tabs[n]? with
  | some a, some b => a.count == b.count
  | _, _ => false

/-- An index into a table: a literal inside `count`, or an
    index parameter for a table of the same count (the `tr_index` of
    `lean_g.rs`). -/
def uIndex (ctx : UCtx) (t : String) (num : Nat) : SExpr → Except String UIdx
  | .lit v =>
    match uAnzahlTab ctx.tabs t with
    | .error e => .error e
    | .ok c =>
      if Int.ofNat v < c then .ok (.lit (Int.ofNat v))
      else .error "index outside count"
  | .variable p =>
    match uParamNr ctx p with
    | .error e => .error e
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.index m) =>
        if m == num || uGleicheAnzahl ctx.tabs m num then .ok (.param p) else .error "index of foreign table"
      | .ok .int => .ok (.param p)
      | _ => .error "index without G form"
  | _ => .error "index without G form"

/-- A slot read `p.slots[i].f` / `T.slots[i].f`: the basis
    (pointer parameter or table name), the table, the field and
    the index (the `slot_access` of `lean_g.rs`). -/
inductive UBasis
  | thru : String → UBasis
  | tabelle : String → UBasis
  deriving DecidableEq, Repr

def uZugriff (ctx : UCtx) : SExpr →
    Except String (UBasis × String × String × UIdx)
  | .index (.variable b) idx =>
    match ctx.tabs.find? (fun x => strEq x.name b) with
    | .some tb =>
      if !tb.arena then .error "place without G form"
      else
        match uHaeltWaechter ctx tb.name with
        | .error e => .error e
        | .ok _ =>
          match uTabNrAux ctx.tabs 0 tb.name with
          | .error e => .error e
          | .ok (num, _) =>
            match uIndex ctx tb.name num idx with
            | .error e => .error e
            | .ok ix => .ok (.tabelle b, tb.name, "wert", ix)
    | .none => .error "place without G form"
  | .field (.index (.field (.variable b) s) idx) f =>
    if !strEq s "slots" then .error "place without G form"
    else
      match uParamNr ctx b with
      | .ok j =>
        match uArtBei ctx.kinds j with
        | .ok (.ptr num _) =>
          match ctx.tabs[num]? with
          | .none => .error "pointer table unknown"
          | .some tb =>
            if tb.arena then .error "place without G form"
            else if !(tb.cols.any (fun (g, _) => strEq g f)) then
              .error "field unknown"
            else match uHaeltWaechter ctx tb.name with
              | .error e => .error e
              | .ok _ =>
                match uIndex ctx tb.name num idx with
                | .error e => .error e
                | .ok ix => .ok (.thru b, tb.name, f, ix)
        | _ => .error "place without G form"
      | .error _ =>
        match ctx.tabs.find? (fun x => strEq x.name b) with
        | .none => .error ("name unknown: " ++ b)
        | .some tb =>
          if tb.arena then .error "place without G form"
          else if !(tb.cols.any (fun (g, _) => strEq g f)) then
            .error "field unknown"
          else match uHaeltWaechter ctx tb.name with
            | .error e => .error e
            | .ok _ =>
              match uTabNrAux ctx.tabs 0 tb.name with
              | .error e => .error e
              | .ok (num, _) =>
                match uIndex ctx tb.name num idx with
                | .error e => .error e
                | .ok ix => .ok (.tabelle b, tb.name, f, ix)
  | _ => .error "place without G form"

/-- The field `f` of the table `tb` is a `bool` field. -/
def uBoolFeld (ctx : UCtx) (tb f : String) : Bool :=
  match ctx.tabs.find? (fun x => strEq x.name tb) with
  | .some x => x.bools.any (fun g => strEq g f)
  | .none => false

/-- The option field `f` of the table `tb`: the number of the table its values index. -/
def uOptFeld (ctx : UCtx) (tb f : String) : Option Nat :=
  match ctx.tabs.find? (fun x => strEq x.name tb) with
  | .some x => (x.opts.find? (fun p => strEq p.1 f)).map (·.2)
  | .none => none

/-- A limit word `T::max` / `T::min` of a type word (an alias or a built-in width), as its number
    (the `grenzwort` of `tr_typed`: it travels as a literal). -/
def uGrenzwort (ctx : UCtx) : SExpr → Option Int
  | .field (.variable t) f =>
    match uTypName ctx.alias t with
    | .ok (lo, hi) =>
      if strEq f "max" then some hi
      else if strEq f "min" then some lo
      else none
    | .error _ => none
  | _ => none

/-- An error of the place reader that names a premise of the model (the read is outside the table, or the guard
    is not held), not a missing form: it must reach the verdict, not be masked by the leaf's own message. -/
def uPraemisse (e : String) : Bool :=
  strEq e "index outside count" || strEq e "access without held guard"

/-- `a[i]` reads a CARRIER (a table's or an arena's slot, `T.slots[i]`, `p.slots[i]`, `A[i]`), not an aggregate value. -/
def uTraegerIndex (ctx : UCtx) : SExpr → Bool
  | .field _ f => strEq f "slots"
  | .variable n => ctx.tabs.any (fun t => strEq t.name n)
  | _ => false

/-- The arithmetic layer shared by body values and `ensures` sides: `+ - *`, `& | ^` and the
    integer conversion `T(e)`; every other form is a LEAF, handled by `blatt`. -/
def uRechne (ctx : UCtx) (blatt : SExpr → Except String USide) : SExpr → Except String USide
  | .bin op a b =>
    if strEq op "+" || strEq op "-" || strEq op "*" || strEq op "&" || strEq op "|" || strEq op "^"
        || strEq op "/" || strEq op "%" || strEq op "<<" || strEq op ">>" then
      match uRechne ctx blatt a with
      | .error e => .error e
      | .ok x =>
        match uRechne ctx blatt b with
        | .error e => .error e
        | .ok y =>
          if strEq op "+" then .ok (.add x y)
          else if strEq op "-" then .ok (.sub x y)
          else if strEq op "*" then .ok (.mul x y)
          else if strEq op "&" then .ok (.band x y)
          else if strEq op "|" then .ok (.bor x y)
          else if strEq op "^" then .ok (.bxor x y)
          else if strEq op "/" then .ok (.div x y)
          else if strEq op "%" then .ok (.rem x y)
          else if strEq op "<<" then .ok (.shl x y)
          else .ok (.shr x y)
    else blatt (.bin op a b)
  | .un "-" (.lit v) => .ok (.lit (-(Int.ofNat v)))
  | .un "-" a =>
    match uRechne ctx blatt a with
    | .error e => .error e
    | .ok x => .ok (.neg x)
  | .un "-()" a =>
    match uRechne ctx blatt a with
    | .error e => .error e
    | .ok x => .ok (.neg x)
  | .un "~" (.variable p) =>
    -- `~p` is `p ^ (2^w - 1)` over the parameter's declared STORAGE width `w` (what the checker reads);
    -- for any other operand the width is not known here, so the form is refused.
    match uParamNr ctx p with
    | .error _ => blatt (.un "~" (.variable p))
    | .ok j =>
      match ctx.bits[j]?, uArtBei ctx.kinds j with
      | .some w, .ok .int =>
        if 0 < w then .ok (.bxor (.param p) (.lit ((2 : Int) ^ w - 1)))
        else .error "complement of unknown width"
      | _, _ => .error "complement of unknown width"
  | .call f [a] =>
    match uTypName ctx.alias f with
    | .ok (lo, hi) =>
      match uRechne ctx blatt a with
      | .error e => .error e
      | .ok x => .ok (.conv lo hi x)
    | .error _ => blatt (.call f [a])
  | .built "lenof" [a] =>
    match uRechne ctx blatt a with
    | .error e => .error e
    | .ok x => .ok (.len x)
  | .ext .text [t] [] => .ok (.text (t.toUTF8.toList.map (fun b => Int.ofNat b.toNat)))
  | .index a i =>
    if uTraegerIndex ctx a then blatt (.index a i) else
    match uRechne ctx blatt a with
    | .error e => .error e
    | .ok x =>
      match uRechne ctx blatt i with
      | .error e => .error e
      | .ok y => .ok (.idx x y)
  | e => blatt e

/-- A name that is no parameter and no constant: a number static (`Expr.glob`), or an unknown name. -/
def uGlobLies (ctx : UCtx) (p : String) : Except String USide :=
  match ctx.globs.find? (fun g => strEq g.name p) with
  | .some g =>
    match g.ty with
    | .bool => .error "bool static as a number"
    | _ => .ok (.glob p)
  | .none => .error ("name unknown: " ++ p)

/-- One side of an `ensures` comparison (the `tr_side` of
    `lean_g.rs`): literals, numeric parameters, named constants, limit words, slot reads,
    `old` and `result` travel, with the arithmetic layer of `uRechne`; a pointer parameter in a
    comparison and everything else are explicit errors. -/
def uSeiteBlatt (ctx : UCtx) : SExpr → Except String USide
  | .lit v => .ok (.lit (Int.ofNat v))
  | .variable p =>
    match uParamNr ctx p with
    | .error _ =>
      match ctx.lits.find? (fun k => strEq k.1 p) with
      | .some k => .ok (.lit k.2)
      | .none =>
        match ctx.arrKonst.find? (fun k => strEq k.1 p) with
        | .some k => .ok k.2
        | .none => uGlobLies ctx p
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.ptr _ _) => .error "pointer in a compare without G form"
      | .ok .bool => .error "truth value as a number"
      | .ok _ => .ok (.param p)
      | .error e => .error e
  | .res =>
    match ctx.res with
    | .some _ => .ok .erg
    | .none => .error "result without result"
  | .old o =>
    match uZugriff ctx o with
    | .error e => .error e
    | .ok (.thru b, _, f, ix) => .ok (.old b f ix)
    | .ok (.tabelle b, _, f, ix) => .ok (.old b f ix)
  | e =>
    match uGrenzwort ctx e with
    | .some v => .ok (.lit v)
    | .none =>
      match uZugriff ctx e with
      | .error x => .error (if uPraemisse x then x else "compare side without G form")
      | .ok (.thru b, tb, f, ix) =>
        if uBoolFeld ctx tb f then .error "bool field as a number"
        else if (uOptFeld ctx tb f).isSome then .error "option field as a number" else .ok (.slot b f ix)
      | .ok (.tabelle b, tb, f, ix) =>
        if uBoolFeld ctx tb f then .error "bool field as a number"
        else if (uOptFeld ctx tb f).isSome then .error "option field as a number" else .ok (.tab b f ix)

def uSeite (ctx : UCtx) : SExpr → Except String USide :=
  uRechne ctx (uSeiteBlatt ctx)

/-- A comparison operator with G form (`==`, `!=`, `<`, `<=`,
    `>`, `>=`; G folds all but `lt`/`le`/`eq`). -/
def uIstVgl : String → Bool
  | "==" => true
  | "!=" => true
  | "<" => true
  | "<=" => true
  | ">" => true
  | ">=" => true
  | _ => false

/-- An option value read off an expression, with the number of its table: an option variable or the read of
    an option field. -/
def uOptEin (ctx : UCtx) : SExpr → Except String (UOpt × Nat)
  | .variable p =>
    match uParamNr ctx p with
    | .error e =>
      match ctx.globs.find? (fun g => strEq g.name p) with
      | .some gl =>
        match gl.optNum with
        | .some m => .ok (.glob p, m)
        | .none => .error e
      | .none => .error e
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.opt m) => .ok (.var p, m)
      | _ => .error "match without G form"
  | e =>
    match uZugriff ctx e with
    | .error x => .error x
    | .ok (b, tb, f, ix) =>
      match uOptFeld ctx tb f with
      | .none => .error "match without G form"
      | .some m =>
        match b with
        | .thru p => .ok (.slot p f ix, m)
        | .tabelle t => .ok (.tab t f ix, m)

/-- One `ensures` predicate (the `tr_ensures` of `lean_g.rs`). -/
def uSichert (ctx : UCtx) : SExpr → Except String UEns
  | .bin op l r =>
    if uIstVgl op then
      match uSeite ctx l with
      | .error e => .error e
      | .ok a =>
        match uSeite ctx r with
        | .error e => .error e
        | .ok b => .ok (.cmp op a b)
    else if strEq op "&&" then
      match uSichert ctx l with
      | .error e => .error e
      | .ok a =>
        match uSichert ctx r with
        | .error e => .error e
        | .ok b => .ok (.and a b)
    else if strEq op "||" then
      match uSichert ctx l with
      | .error e => .error e
      | .ok a =>
        match uSichert ctx r with
        | .error e => .error e
        | .ok b => .ok (.or a b)
    else .error "operator without G form"
  | .un "!" q =>
    match uSichert ctx q with
    | .error e => .error e
    | .ok a => .ok (.not a)
  | .ext k [x, dk] [.variable tn, body] =>
    if !(k == XKind.all || k == XKind.any) then .error "ensures clause without G form"
    else if !strEq dk "slots" then .error "quantifier domain without G form"
    else
      match uTabNr ctx.tabs tn with
      | .error e => .error e
      | .ok (num, c) =>
        match uSichert { ctx with names := x :: ctx.names, kinds := .index num :: ctx.kinds,
                                  types := Ty.index c :: ctx.types, bits := 0 :: ctx.bits } body with
        | .error e => .error e
        | .ok b => .ok (if k == XKind.all then .alle tn x b else .einige tn x b)
  | .tru => .ok .tru
  | .fls => .ok .fls
  | .res => if ctx.resBool then .ok .ergB else .error "ensures clause without G form"
  | .variable g =>
    match (match uParamNr ctx g with
        | .ok j =>
          match uArtBei ctx.kinds j with
          | .ok .bool => some true
          | _ => some false
        | .error _ => none : Option Bool) with
    | some true => .ok (.var g)
    | some false => .error "number as a truth value"
    | none =>
    match ctx.globs.find? (fun x => strEq x.name g) with
    | .some gl =>
      match gl.ty with
      | .bool => .ok (.globB g)
      | _ => .error "number static as a truth value"
    | .none => .error "ensures clause without G form"
  | .ext .call [] [.field o "is_some"] =>
    match uOptEin ctx o with
    | .error x => .error x
    | .ok (v, m) => .ok (.istSome v m)
  | e =>
    match uZugriff ctx e with
    | .error x => .error (if uPraemisse x then x else "ensures clause without G form")
    | .ok (.thru b, tb, f, ix) =>
      if uBoolFeld ctx tb f then .ok (.slotB b f ix) else .error "ensures clause without G form"
    | .ok (.tabelle b, tb, f, ix) =>
      if uBoolFeld ctx tb f then .ok (.tabB b f ix) else .error "ensures clause without G form"

/-- `old(..)` or `result` inside a side. -/
def seiteAltErg : USide → Bool
  | .old .. | .erg => true
  | .add a b | .sub a b | .mul a b | .band a b | .bor a b | .bxor a b | .div a b | .rem a b | .shl a b | .shr a b =>
    seiteAltErg a || seiteAltErg b
  | .conv _ _ a | .neg a => seiteAltErg a
  | _ => false

/-- `old(..)` or `result` inside a predicate. -/
def ensAltErg : UEns → Bool
  | .cmp _ a b => seiteAltErg a || seiteAltErg b
  | .and a b | .or a b => ensAltErg a || ensAltErg b
  | .not a => ensAltErg a
  | .alle _ _ b | .einige _ _ b => ensAltErg b
  | .ergB => true
  | _ => false

/-- A truth value in a BODY (a returned or stored `bool`): the predicate forms of an `ensures`,
    without `old` and `result`. -/
def uBool (ctx : UCtx) (e : SExpr) : Except String UEns :=
  match uSichert { ctx with res := none, resBool := false } e with
  | .error x => .error x
  | .ok v => if ensAltErg v then .error "old or result in a body" else .ok v

/-- A leaf of a body value: a literal, a numeric parameter, a named constant, a limit word or a
    slot read. -/
def uWertBlatt (ctx : UCtx) : SExpr → Except String USide
  | .lit v => .ok (.lit (Int.ofNat v))
  | .variable p =>
    match uParamNr ctx p with
    | .error _ =>
      match ctx.lits.find? (fun k => strEq k.1 p) with
      | .some k => .ok (.lit k.2)
      | .none =>
        match ctx.arrKonst.find? (fun k => strEq k.1 p) with
        | .some k => .ok k.2
        | .none => uGlobLies ctx p
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.ptr _ _) => .error "pointer as value without G form"
      | .ok .bool => .error "truth value as a number"
      | .ok (.ref _) => .error "reference as a number"
      | .ok _ => .ok (.param p)
      | .error e => .error e
  | .arrow (.variable r) f =>
    match uRefLokal ctx r with
    | .some _ => .ok (.refSlot r f)
    | .none => .error "value without G form"
  | e =>
    match uGrenzwort ctx e with
    | .some v => .ok (.lit v)
    | .none =>
      match uZugriff ctx e with
      | .error x => .error (if uPraemisse x then x else "value without G form")
      | .ok (.thru b, tb, f, ix) =>
        if uBoolFeld ctx tb f then .error "bool field as a number"
        else if (uOptFeld ctx tb f).isSome then .error "option field as a number" else .ok (.slot b f ix)
      | .ok (.tabelle b, tb, f, ix) =>
        if uBoolFeld ctx tb f then .error "bool field as a number"
        else if (uOptFeld ctx tb f).isSome then .error "option field as a number" else .ok (.tab b f ix)

/-- A value in a body (the `tr_value` of `lean_g.rs` at `in_ensures := false`: `result` and
    `old` have no G form here), with the arithmetic layer of `uRechne`. -/
def uWertBody (ctx : UCtx) : SExpr → Except String USide :=
  uRechne ctx (uWertBlatt ctx)

/-- Sequence: the first error wins (like the exporter's
    straight-line `?`). -/
def uSeq : List (Except String α) → Except String (List α)
  | [] => .ok []
  | .error e :: _ => .error e
  | .ok x :: rest =>
    match uSeq rest with
    | .error e => .error e
    | .ok xs => .ok (x :: xs)

/-- One function head: name, parameters (names, kinds, types),
    the optional result range and the held lock names (pass one
    of `collect` in `lean_g.rs`). -/
structure UFnKopf where
  name : String
  names : List String
  kinds : List UParamArt
  types : List Ty
  res : Option (Int × Int)
  resBool : Bool := false
  resOpt : Option (Nat × Int) := none
  /-- The reason channel: the position of `R` among the unit's reasons and its number of cases. -/
  kanal : Option (Nat × Nat) := none
  /-- The result is a tagged type: its position and its specification. -/
  resSum : Option (Nat × List (Option (Int × Int))) := none
  /-- The result is a reason (`-> R`): the position of `R` among the unit's reasons and its number of cases. -/
  resWhy : Option (Nat × Nat) := none
  bits : List Nat := []
  held : List String
  /-- The statics it writes. -/
  gputs : List String := []
  /-- A foreign body (`extern fn`): called as `D.Ax`, never as a function of the unit. -/
  ext : Bool := false
  /-- The answer of a foreign body is `never` (the call does not return). -/
  resNever : Bool := false
  /-- The device handles among the declared parameters: the position in the WRITTEN parameter list, the
      name and the device. They are erased from `names`/`kinds`/`types`; a call drops their arguments. -/
  griffe : List (Nat × String × String) := []
  /-- The answer of a foreign body is a reference into the open table number `n` (`-> index into T`). -/
  resRef : Option Nat := none
  /-- The result is an aggregate value: its type. -/
  resTy : Option Ty := none
  /-- The tables a foreign body writes (`ext`). -/
  puts : List String := []

/-- The kind and the type of the value a call of a function of the unit binds: a truth value, a number, a
    reason. -/
def uWertArt (k : UFnKopf) : Option (UParamArt × Ty) :=
  if let some τ := k.resTy then some (UParamArt.wert, τ) else
  if k.resBool then some (UParamArt.bool, Ty.bool)
  else match k.res with
    | some r => some (UParamArt.int, Ty.int r.1 r.2)
    | none => k.resWhy.map (fun (k, n) => (UParamArt.why k, Ty.why n))

/-- The answer type of a foreign body. -/
def UFnKopf.axErg (k : UFnKopf) : Option Ty :=
  if let some n := k.resRef then some (Ty.ref n)
  else if k.resNever then some Ty.never
  else if k.resBool then some Ty.bool
  else k.res.map fun r => Ty.int r.1 r.2

/-- The storage width of a declared parameter type: a bare unsigned word, with or without a range
    (`u8 in 0 .. 15` is stored in 8 bits); `0` for everything else. -/
def uParamBreite : STyp → Nat
  | .atom a | .range (.atom a) _ _ _ =>
    if strEq a "u8" then 8 else if strEq a "u16" then 16
    else if strEq a "u32" then 32 else if strEq a "u64" then 64 else 0
  | _ => 0

/-- A parameter with its kind (the `param_ty` of `lean_g.rs`). -/
def uParam (alias : List (String × (Int × Int))) (tabs : List UTab) (sums : List USum := [])
    (whys : List UWhy := []) (zeiger : List String := []) (zb : Nat := 0) :
    String × STyp → Except String (String × Ty × UParamArt)
  | (n, .raw r) =>
    match zeiger.findIdx? (strEq · r) with
    | .some j => .ok (n, Ty.fnptr (zb + j), .fnptr (zb + j))
    | .none =>
      match uTyp alias tabs (.raw r) with
      | .error e => .error e
      | .ok ty => .ok (n, ty, .int)
  | (n, .ptr raum rechte (.atom t)) =>
    if !strEq raum "normal" then .error "space without G form"
    else if strEq rechte "rw" || strEq rechte "own" then
      match uTabNr tabs t with
      | .error e => .error e
      | .ok (num, _) => .ok (n, .ptr num true, .ptr num true)
    else if strEq rechte "r" then
      match uTabNr tabs t with
      | .error e => .error e
      | .ok (num, _) => .ok (n, .ptr num false, .ptr num false)
    else .error "pointer right without G form"
  | (n, .index false t) =>
    match uTabNr tabs t with
    | .error e => .error e
    | .ok (num, c) => .ok (n, .index c, .index num)
  | (n, .atom "bool") => .ok (n, .bool, .bool)
  | (n, .index true t) =>
    match uTabNr tabs t with
    | .error e => .error e
    | .ok (num, c) => .ok (n, .opt c, .opt num)
  | (n, .atom a) =>
    match sums.findIdx? (fun s => strEq s.name a) with
    | .some k =>
      match sums[k]? with
      | .some s => .ok (n, Ty.sum s.spec, UParamArt.sum k)
      | .none => .error ("type unknown: " ++ a)
    | .none =>
      match whys.findIdx? (fun w => strEq w.name a) with
      | .some k =>
        match whys[k]? with
        | .some w => .ok (n, Ty.why w.cases.length, UParamArt.why k)
        | .none => .error ("reason unknown: " ++ a)
      | .none =>
      match uTyp alias tabs (.atom a) with
      | .error e => .error e
      | .ok ty => .ok (n, ty, .int)
  | (n, t) =>
    match uTyp alias tabs t with
    | .error e => .error e
    | .ok ty => .ok (n, ty, uArtVon ty)

/-- A result range (the `int_range` of `lean_g.rs` on the
    result type). -/
def uErgBereich (alias : List (String × (Int × Int))) : STyp →
    Except String (Int × Int)
  | .atom a => uTypName alias a
  | .range _ lo hi o =>
    match uSchranke alias lo, uSchranke alias hi with
    | some a, some b => .ok (a, if o then b - 1 else b)
    | _, _ => .error "result without G form"
  | t => .error ("result without G form: " ++ sTypText t)

/-- `requires Held(L)`: exactly the signature-held locks (the
    requires loop of `check_fn`; every other requires-clause is
    an explicit error). -/
def uGehaltenAux : List ULock → List SExpr → Except String (List String)
  | _, [] => .ok []
  | locks, .variable l :: rest =>
    match locks.find? (fun x => strEq x.name l) with
    | .none => .error ("lock unknown: " ++ l)
    | .some _ =>
      match uGehaltenAux locks rest with
      | .error e => .error e
      | .ok ls => .ok (l :: ls)
  | _, _ :: _ => .error "requires clause without G form"

def uGehalten (locks : List ULock) : List SKlausel →
    Except String (List String)
  | [] => .ok []
  | .needs (.call "Held" args) :: rest =>
    match uGehaltenAux locks args with
    | .error e => .error e
    | .ok ls =>
      match uGehalten locks rest with
      | .error e => .error e
      | .ok ms => .ok (ls ++ ms)
  | .needs _ :: rest => uGehalten locks rest
  | _ :: rest => uGehalten locks rest

/-- A name position in a list (for `writes` through a
    parameter). -/
def uStelle : List String → String → Except String Nat
  | [], p => .error ("name unknown: " ++ p)
  | q :: rest, p =>
    if strEq q p then .ok 0
    else
      match uStelle rest p with
      | .error e => .error e
      | .ok k => .ok (k + 1)

/-- The table a `writes` place names (the `write_table` of
    `lean_g.rs`): `writes k.slots` through a pointer parameter,
    or `writes T.slots` at a table. -/
def uSchreibtOrt (kopf : UFnKopf) (tabs : List UTab) : SExpr →
    Except String String
  | .field (.variable b) s =>
    if !strEq s "slots" then .error "writes clause without G form"
    else
      match uStelle kopf.names b with
      | .ok j =>
        match uArtBei kopf.kinds j with
        | .ok (.ptr num _) =>
          match tabs[num]? with
          | .some tb => .ok tb.name
          | .none => .error "pointer table unknown"
        | _ => .error "writes clause without G form"
      | .error _ =>
        match tabs.find? (fun x => strEq x.name b) with
        | .some tb => .ok tb.name
        | .none => .error ("name unknown: " ++ b)
  | _ => .error "writes clause without G form"

/-- The effect arms: `locks L` names held locks, `writes`
    names written tables, `reads`/`pure`/`diverges` are no form
    (ignored, like `lean_g.rs`); every other arm is an explicit
    error. -/
structure UEffekte where
  locks : List String
  puts : List String
  gputs : List String := []

/-- A written name is a static when it is no parameter and no table. -/
def uIstGlobName (kopf : UFnKopf) (tabs : List UTab) (globs : List UGlob) (g : String) : Bool :=
  !(kopf.names.any (strEq · g)) && !(tabs.any (fun x => strEq x.name g)) && globs.any (fun x => strEq x.name g)

/-- A place through a device handle (`d`, `d.R`, `d.R.F`): a register is outside the world, so `writes d`
    names no carrier (the class decides the access, `Stmt.regWrite`). -/
def uIstGriffOrt (kopf : UFnKopf) : SExpr → Bool
  | .variable h => kopf.griffe.any (fun g => strEq g.2.1 h)
  | .field o _ => uIstGriffOrt kopf o
  | _ => false

def uEffekteAux (kopf : UFnKopf) (tabs : List UTab) (locks : List ULock) (globs : List UGlob) :
    List SEffekt → Except String UEffekte
  | [] => .ok { locks := [], puts := [] }
  | .locks false (.variable l) :: rest =>
    match locks.find? (fun x => strEq x.name l) with
    | .none => .error ("lock unknown: " ++ l)
    | .some _ =>
      match uEffekteAux kopf tabs locks globs rest with
      | .error e => .error e
      | .ok r => .ok { r with locks := l :: r.locks }
  | .writes o :: rest =>
    if uIstGriffOrt kopf o then uEffekteAux kopf tabs locks globs rest else
    match (match o with
        | .variable a => if tabs.any (fun x => x.arena && strEq x.name a) then some a else none
        | _ => none : Option String) with
    | some a =>
      match uEffekteAux kopf tabs locks globs rest with
      | .error e => .error e
      | .ok r => .ok { r with puts := a :: r.puts, gputs := (a ++ "#used") :: r.gputs }
    | none =>
    match (match o with
        | .variable g => if uIstGlobName kopf tabs globs g then some g else none
        | _ => none : Option String) with
    | some g =>
      match uEffekteAux kopf tabs locks globs rest with
      | .error e => .error e
      | .ok r => .ok { r with gputs := g :: r.gputs }
    | none =>
    match uSchreibtOrt kopf tabs o with
    | .error e => .error e
    | .ok t =>
      match uEffekteAux kopf tabs locks globs rest with
      | .error e => .error e
      | .ok r => .ok { r with puts := t :: r.puts }
  | .reads _ :: rest => uEffekteAux kopf tabs locks globs rest
  | .pure :: rest => uEffekteAux kopf tabs locks globs rest
  | .loops :: rest => uEffekteAux kopf tabs locks globs rest
  | _ :: _ => .error "effect without G form"

def uEffekte (kopf : UFnKopf) (tabs : List UTab) (locks : List ULock) (globs : List UGlob) :
    List SKlausel → Except String UEffekte
  | ks =>
    let es := uWirkungen ks
    -- An omitted `effects` is DERIVED by the checker (lane 191); here it is read as the empty
    -- set. That is never more permissive than the derived one: a body that writes a table or
    -- takes a lock is refused by the lowering (`hw : V.schreibt t = true` has no proof).
    uEffekteAux kopf tabs locks globs es
where
  uWirkungen : List SKlausel → List SEffekt
    | [] => []
    | .effs es :: rest => es ++ uWirkungen rest
    | _ :: rest => uWirkungen rest
  uHatWirkung : List SKlausel → Bool
    | [] => false
    | .effs _ :: _ => true
    | _ :: rest => uHatWirkung rest

/-- Clauses without G counterpart (the refused row of `check_fn`): `refines`, `maintains`, `decreases`,
    `by`, `advances`, `retires`. `costs`, `section` and `payload` travel nowhere and are ignored, like in
    `lean_g.rs`; so is `deadline <= n ops arch X falsifier p` (with its `arch` word): the date is owed to the
    machine and discharged by a probe, so the clause is dropped like `costs` (lane 255 of the exporter). -/
def uOhneKlauselForm : List SKlausel → Except String Unit
  | [] => .ok ()
  | .drops _ :: _ => .error "clause without G form"
  | .moves _ _ :: _ => .error "clause without G form"
  | .quits _ :: _ => .error "clause without G form"
  | _ :: rest => uOhneKlauselForm rest

/-- Deduplicate while keeping order (the `seen` loop of
    `check_fn`). -/
def uEindeutigAux : List String → List String → List String
  | [], _ => []
  | x :: rest, seen =>
    if seen.any (strEq · x) then uEindeutigAux rest seen
    else x :: uEindeutigAux rest (x :: seen)

def uEindeutig (xs : List String) : List String :=
  uEindeutigAux xs []

/-- A device handle type: `D` or `ptr<space, rights> D` for a device `D` of the unit. -/
def uGriffTyp (devs : List String) : STyp → Option String
  | .atom d => if devs.any (strEq · d) then some d else none
  | .ptr _ _ (.atom d) => if devs.any (strEq · d) then some d else none
  | _ => none

/-- The device handles of a written parameter list: position, name, device. -/
def uGriffe (devs : List String) : Nat → List (String × STyp) → List (Nat × String × String)
  | _, [] => []
  | k, (n, ty) :: rest =>
    match uGriffTyp devs ty with
    | some d => (k, n, d) :: uGriffe devs (k + 1) rest
    | none => uGriffe devs (k + 1) rest

/-- The written parameters without the device handles (a handle is no value of the model). -/
def uOhneGriffe (devs : List String) (ps : List (String × STyp)) : List (String × STyp) :=
  ps.filter (fun p => (uGriffTyp devs p.2).isNone)

/-- Pass one: the head of an `impl` function (non-`impl`,
    bodiless and clause-carrying forms are explicit errors).
    Returns the head and the written tables. -/
def elabKopf (_consts : List (String × Int))
    (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (whys : List UWhy) (sums : List USum := [])
    (sig : FnSig) (devs : List String := []) (zeiger : List String := []) (zb : Nat := 0) :
    Except String (UFnKopf × List String) :=
  match sig with
  | { art, name, params := params0, res, fehler, klauseln } =>
    let params := uOhneGriffe devs params0
    -- a `fn` without a kind word and with a body is an implemented function, like `impl fn` (the checker's
    -- `None | Some(Impl)`)
    if !(strEq art "impl" || strEq art "") then .error "fn is not impl"
    else
      match uOhneKlauselForm klauseln with
      | .error e => .error e
      | .ok _ =>
        match uSeq (params.map (uParam alias tabs sums whys zeiger zb)) with
        | .error e => .error e
        | .ok ps =>
          let names := ps.map (·.1)
          let types := ps.map (·.2.1)
          let kinds := ps.map (·.2.2)
          match uGehalten locks klauseln with
          | .error e => .error e
          | .ok held =>
            match (match fehler with
                | .none => .ok none
                | .some r =>
                  match whys.findIdx? (fun w => strEq w.name r) with
                  | .none => .error ("reason unknown: " ++ r)
                  | .some k =>
                    match whys[k]? with
                    | .some w => if w.cases.isEmpty then .error "reason without cases" else .ok (some (k, w.cases.length))
                    | .none => .error ("reason unknown: " ++ r) : Except String (Option (Nat × Nat))) with
            | .error e => .error e
            | .ok kn =>
            let kopf : UFnKopf :=
              { name, names, kinds, types, res := .none,
                bits := params.map (fun p => uParamBreite p.2),
                held := uEindeutig held, kanal := kn, griffe := uGriffe devs 0 params0 }
            match uEffekte kopf tabs locks globs klauseln with
            | .error e => .error e
            | .ok eff =>
              -- A `locks L` effect needs no `requires Held(L)`: a `locks L { .. }` statement acquires
              -- it inside the body, and an access whose guard is not held is refused by the LOWERING
              -- (`access without held guard`), so nothing is claimed here.
              let puts := uEindeutig eff.puts
              let kopf := { kopf with gputs := uEindeutig eff.gputs }
              match res with
              | .none => .ok (kopf, puts)
              | .some (.atom "bool") =>
                .ok ({ kopf with resBool := true }, puts)
              | .some (.atom "never") =>
                .ok ({ kopf with resTy := some Ty.never }, puts)
              | .some (.index true tn) =>
                match uTabNr tabs tn with
                | .error e => .error e
                | .ok (num, c) => .ok ({ kopf with resOpt := some (num, c) }, puts)
              | .some (.atom a) =>
                match sums.findIdx? (fun s => strEq s.name a) with
                | .some k =>
                  match sums[k]? with
                  | .some s => .ok ({ kopf with resSum := some (k, s.spec) }, puts)
                  | .none => .error ("type unknown: " ++ a)
                | .none =>
                  match whys.findIdx? (fun w => strEq w.name a) with
                  | .some k =>
                    match whys[k]? with
                    | .some w => .ok ({ kopf with resWhy := some (k, w.cases.length) }, puts)
                    | .none => .error ("reason unknown: " ++ a)
                  | .none =>
                  match uErgBereich alias (.atom a) with
                  | .error e => .error e
                  | .ok r => .ok ({ kopf with res := .some r }, puts)
              | .some t =>
                match t with
                | .array _ _ | .str _ =>
                  match uTyp alias tabs t with
                  | .error e => .error e
                  | .ok τ => .ok ({ kopf with resTy := .some τ }, puts)
                | _ =>
                match uErgBereich alias t with
                | .error e => .error e
                | .ok r =>
                  .ok ({ kopf with res := .some r }, puts)

/-- An option value of the table `num`: `None`, `Some(i)`, or what `uOptEin` reads (its table must be `num`). -/
def uOpt (ctx : UCtx) (num : Nat) : SExpr → Except String UOpt
  | .call "None" [] => .ok .nichts
  | .call "Some" [a] =>
    match ctx.tabs[num]? with
    | .none => .error "option table unknown"
    | .some tb =>
      match uIndex ctx tb.name num a with
      | .error e => .error e
      | .ok ix => .ok (.etwas ix)
  | e =>
    match uOptEin ctx e with
    | .error x => .error x
    | .ok (o, m) => if m == num then .ok o else .error "option of a foreign table"

/-- A tagged value read off an expression, with the position of its type: a variable, a payload-free case or a
    case with a payload. -/
def uSValEin (ctx : UCtx) : SExpr → Except String (USVal × Nat)
  | .variable v =>
    match uParamNr ctx v with
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.sum s) => .ok (.var v, s)
      | _ => .error "tagged value without G form"
    | .error _ =>
      match ctx.sums.findIdx? (fun s => s.cases.any (fun c => strEq c.1 v && c.2.isNone)) with
      | .none => .error ("name unknown: " ++ v)
      | .some k =>
        match ctx.sums[k]? with
        | .none => .error "tagged type unknown"
        | .some s =>
          match s.cases.findIdx? (fun c => strEq c.1 v) with
          | .some i => .ok (.fall i .none, k)
          | .none => .error ("name unknown: " ++ v)
  | .call c [a] =>
    match ctx.sums.findIdx? (fun s => s.cases.any (fun x => strEq x.1 c && x.2.isSome)) with
    | .none => .error "tagged value without G form"
    | .some k =>
      match ctx.sums[k]? with
      | .none => .error "tagged type unknown"
      | .some s =>
        match s.cases.findIdx? (fun x => strEq x.1 c) with
        | .none => .error "tagged value without G form"
        | .some i =>
          match uWertBody ctx a with
          | .error e => .error e
          | .ok sd => .ok (.fall i (.some sd), k)
  | _ => .error "tagged value without G form"

/-- A tagged value of the type at `sidx`. -/
def uSVal (ctx : UCtx) (sidx : Nat) (e : SExpr) : Except String USVal :=
  match uSValEin ctx e with
  | .error x => .error x
  | .ok (v, k) => if k == sidx then .ok v else .error "tagged value of a foreign type"

/-- One call argument against the callee's parameter kind (the
    `tr_arg` of `lean_g.rs`): a pointer variable through, a
    fresh pointer where the rights differ, an index literal or
    parameter, a value otherwise. -/
def uArg (ctx : UCtx) (tabs : List UTab) : UParamArt → SExpr →
    Except String UArg
  | .ptr num w, .variable p =>
    match uParamNr ctx p with
    | .error e => .error e
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.ptr num2 w2) =>
        if num == num2 then
          if w == w2 then .ok (.var p)
          else
            match tabs[num]? with
            | .some tb => .ok (.freshPtr tb.name w)
            | .none => .error "pointer table unknown"
        else .error "argument of foreign table"
      | _ => .error "pointer argument without G form"
  | .ptr num w, .fnref t =>
    match tabs[num]? with
    | .some tb => if strEq tb.name t then .ok (.freshPtr tb.name w) else .error "argument of foreign table"
    | .none => .error "pointer table unknown"
  | .index num, a =>
    match tabs[num]? with
    | .none => .error "index table unknown"
    | .some tb =>
      match uIndex ctx tb.name num a with
      | .error e => .error e
      | .ok (.lit v) => .ok (.val (.lit v))
      | .ok (.param p) => .ok (.val (.param p))
  | .int, a =>
    match uWertBody ctx a with
    | .error e => .error e
    | .ok s => .ok (.val s)
  | .bool, a =>
    match uBool ctx a with
    | .error e => .error e
    | .ok b => .ok (.bval b)
  | .opt num, a =>
    match uOpt ctx num a with
    | .error e => .error e
    | .ok o => .ok (.oval o)
  | .why k, .why r c =>
    match ctx.whys[k]? with
    | .some w =>
      if !strEq w.name r then .error "argument of a foreign reason"
      else
        match w.cases.findIdx? (fun x => strEq x c) with
        | .some i => .ok (.gval (.fall i))
        | .none => .error ("reason case unknown: " ++ c)
    | .none => .error "reason unknown"
  | .why k, .variable p =>
    match uParamNr ctx p with
    | .error e => .error e
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.why k') => if k' == k then .ok (.gval (.var p)) else .error "argument of a foreign reason"
      | _ => .error "argument without G form"
  | .fnptr m, .variable p =>
    match uParamNr ctx p with
    | .error e => .error e
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.fnptr m2) =>
        if m == m2 then .ok (.var p) else .error "function pointer of another type as an argument"
      | _ => .error "pointer argument without G form"
  | .fnptr _, .fnref f => .ok (.fnref f)
  | _, _ => .error "argument without G form"

def uArgs (ctx : UCtx) (tabs : List UTab) : List UParamArt → List SExpr →
    Except String (List UArg)
  | [], [] => .ok []
  | k :: ks, a :: rest =>
    match uArg ctx tabs k a with
    | .error e => .error e
    | .ok x =>
      match uArgs ctx tabs ks rest with
      | .error e => .error e
      | .ok xs => .ok (x :: xs)
  | _, _ => .error "argument count without G form"

/-- `a[i] = v` on an aggregate held by the static at the root of `a`: the static and its new value, the element at
    `i` replaced (`USide.upd`) at every level (`M[i][j] = v` replaces row `i` of `M` by the row with element `j`
    replaced). -/
def uElemSchreib (ctx : UCtx) : SExpr → SExpr → USide → Except String (String × USide)
  | .variable g, i, v =>
    match uWertBody ctx i with
    | .error x => .error x
    | .ok y => .ok (g, .upd (.glob g) y v)
  | .index a j, i, v =>
    match uWertBody ctx (.index a j), uWertBody ctx i with
    | .ok cur, .ok y => uElemSchreib ctx a j (.upd cur y v)
    | .error x, _ | _, .error x => .error x
  | _, _, _ => .error "element write without G form"

/-- `X = v;` where `X` is a static (the place reader found no slot): only a `mut` static is written. -/
def uGlobSchreib (ctx : UCtx) (ziel wert : SExpr) (e : String) : Except String UStmt :=
  match ziel with
  | .variable g =>
    match ctx.globs.find? (fun x => strEq x.name g) with
    | .none => .error e
    | .some gl =>
      if !gl.var then .error "write to an immutable static"
      else if gl.atomic then .error "plain write to an atomic: every store is a publish"
      else
        match gl.ty, gl.optNum with
        | _, .some num =>
          match uOpt ctx num wert with
          | .error x => .error x
          | .ok o => .ok (.assignGlobO g o)
        | .bool, _ =>
          match uBool ctx wert with
          | .error x => .error x
          | .ok v => .ok (.assignGlobB g v)
        | _, _ =>
          match uWertBody ctx wert with
          | .error x => .error x
          | .ok v => .ok (.assignGlob g v)
  | .index a i =>
    match uWertBody ctx wert with
    | .error x => .error x
    | .ok v =>
      match uElemSchreib ctx a i v with
      | .error x => .error x
      | .ok (g, w) =>
        match ctx.globs.find? (fun x => strEq x.name g) with
        | .some gl =>
          if !gl.var then .error "write to an immutable static"
          else if gl.atomic then .error "plain write to an atomic: every store is a publish"
          else .ok (.assignGlob g w)
        | .none => .error e
  | _ => .error e

/-- The words of a raw payload, as character lists (split at blanks and commas). -/
def uWoerter : List Char → List Char → List (List Char)
  | [], acc => if acc.isEmpty then [] else [acc.reverse]
  | c :: cs, acc =>
    if c == ' ' || c == ',' then (if acc.isEmpty then uWoerter cs [] else acc.reverse :: uWoerter cs [])
    else uWoerter cs (c :: acc)

/-- The names of a payload as the statement reader keeps it (raw words: `p , q `, or `nothing`). -/
def uNutzNamen (p : String) : List (List Char) :=
  if strEq p "nothing" then [] else uWoerter p.toList []

/-- A payload as written names exactly the declared list. -/
def uNamenGleich : List (List Char) → List String → Bool
  | [], [] => true
  | a :: as, b :: bs => a == b.toList && uNamenGleich as bs
  | _, _ => false

/-- `A = v publishes { p, q };` (or `nothing`): the store of an atomic with exactly its declared payload
    (`Stmt.publish`, the payload `D.nutzlast A`). -/
def uAtomSchreib (ctx : UCtx) (ziel wert : SExpr) (p : String) : Except String UStmt :=
  match ziel with
  | .variable g =>
    match ctx.globs.find? (fun x => strEq x.name g) with
    | .none => .error "publishes without an atomic without G form"
    | .some gl =>
      if !gl.atomic then .error "publishes without an atomic without G form"
      else if !uNamenGleich (uNutzNamen p) gl.nutzlast then .error "publishes a payload other than the declared one"
      else
        match gl.ty with
        | .bool =>
          match uBool ctx wert with
          | .error x => .error x
          | .ok v => .ok (.storeAtomB g v)
        | _ =>
          match uWertBody ctx wert with
          | .error x => .error x
          | .ok v => .ok (.storeAtom g v)
  | _ => .error "publishes without an atomic without G form"

/-- The arguments of a call without those at the callee's device handles; each of those must be a handle of
    the same device in the caller (a handle is no value of the model: the register is named by the device). -/
def uOhneGriffArgs (ctx : UCtx) (gs : List (Nat × String × String)) : Nat → List SExpr →
    Except String (List SExpr)
  | _, [] => .ok []
  | k, a :: rest =>
    match gs.find? (fun g => g.1 == k) with
    | none =>
      match uOhneGriffArgs ctx gs (k + 1) rest with
      | .error e => .error e
      | .ok xs => .ok (a :: xs)
    | some (_, _, d) =>
      match a with
      | .variable h =>
        if ctx.griffe.any (fun p => strEq p.1 h && strEq p.2 d) then uOhneGriffArgs ctx gs (k + 1) rest
        else .error "device argument without G form"
      | _ => .error "device argument without G form"

/-- A register place through a device handle in scope: `d.R` (`some` of the register, or of an error for an
    unknown register); `d.R.F` (a register field) has no G form; anything else is no register place. -/
def uRegOrt (ctx : UCtx) : SExpr → Option (Except String UReg)
  | .field (.variable h) r =>
    if ctx.names.any (strEq · h) then none else
    match ctx.griffe.find? (fun p => strEq p.1 h) with
    | none => none
    | some (_, d) =>
      some (match ctx.regs.find? (fun g => strEq g.dev d && strEq g.name r) with
        | some g => .ok g
        | none => .error ("register unknown: " ++ r))
  | .field (.field (.variable h) _) _ =>
    if ctx.names.any (strEq · h) then none
    else if ctx.griffe.any (fun p => strEq p.1 h) then some (.error "register field without G form")
    else none
  | _ => none

/-- A direct call: the callee and its arguments against the callee's parameter kinds. The callee's required
    locks must be held (`RufPasst.hh`); an extra lock of the caller must rank below the callee's floor
    (`RufPasst.hx`), which the lowering decides (`floorUeberB`). -/
def uRuf (ctx : UCtx) (tabs : List UTab) (koepfe : List UFnKopf) (c : String) (args : List SExpr) :
    Except String (UFnKopf × List UArg) :=
  match koepfe.find? (fun k => strEq k.name c) with
  | .none => .error ("call unknown: " ++ c)
  | .some callee =>
    if !(callee.held.all (fun l => ctx.held.any (strEq · l))) then .error "call without held guard"
    else
      match uOhneGriffArgs ctx callee.griffe 0 args with
      | .error e => .error e
      | .ok args' =>
        match uArgs ctx tabs callee.kinds args' with
        | .error e => .error e
        | .ok xs => .ok (callee, xs)

/-- The scope after `let e` of a reason (`Ty.why n`, `n` the number of cases). -/
def UFn.mitWhy (f : UFn) (x : String) (num n : Nat) : UFn :=
  { f with params := (x, Ty.why n) :: f.params, kinds := .why num :: f.kinds }

/-- The value written into a wrapping field: `(v + m) % m` (the `+ m` keeps a difference that went below zero by
    at most `m` non-negative); any other field takes `v` as it is. -/
def uWrap (ctx : UCtx) (tb f : String) (v : USide) : USide :=
  match (ctx.tabs.find? (fun t => strEq t.name tb)).bind (fun t => t.wraps.find? (fun p => strEq p.1 f)) with
  | some (_, m) => .rem (.add v (.lit m)) (.lit m)
  | none => v

/-- `place = v;` at a slot or a static (the place reader decides which). -/
def uSetzePlatz (ctx : UCtx) (ziel wert : SExpr) : Except String UStmt :=
  match uZugriff ctx ziel with
  | .error e => uGlobSchreib ctx ziel wert e
  | .ok (.thru b, tb, f, ix) =>
    match uStelle ctx.names b with
    | .error e => .error e
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.ptr _ true) =>
        if (uOptFeld ctx tb f).isSome then
          match uOptFeld ctx tb f with
          | .none => .error "option field without G form"
          | .some num =>
            match uOpt ctx num wert with
            | .error e => .error e
            | .ok v => .ok (.assignOpt b f ix v)
        else
        if uBoolFeld ctx tb f then
          match uBool ctx wert with
          | .error e => .error e
          | .ok v => .ok (.assignB b f ix v)
        else
          match uWertBody ctx wert with
          | .error e => .error e
          | .ok v => .ok (.assign b f ix (uWrap ctx tb f v))
      | _ => .error "write through a read pointer"
  | .ok (.tabelle b, tb, f, ix) =>
    if (uOptFeld ctx tb f).isSome then
      match uOptFeld ctx tb f with
      | .none => .error "option field without G form"
      | .some num =>
        match uOpt ctx num wert with
        | .error e => .error e
        | .ok v => .ok (.assignTabOpt b f ix v)
    else
    if uBoolFeld ctx tb f then
      match uBool ctx wert with
      | .error e => .error e
      | .ok v => .ok (.assignTabB b f ix v)
    else
      match uWertBody ctx wert with
      | .error e => .error e
      | .ok v => .ok (.assignTab b f ix (uWrap ctx tb f v))

/-- `x = v;` at a `let mut` local. -/
def uSetzeLokal (ctx : UCtx) (x : String) (wert : SExpr) : Except String UStmt :=
  match uParamNr ctx x with
  | .error e => .error e
  | .ok j =>
    match uArtBei ctx.kinds j with
    | .ok .int =>
      match uWertBody ctx wert with
      | .error e => .error e
      | .ok v => .ok (.setVar x v)
    | .ok .bool =>
      match uBool ctx wert with
      | .error e => .error e
      | .ok v => .ok (.setVarB x v)
    | _ => .error "assignment to a pointer or an index"

/-- The binary operator of a compound assignment `x op= v` (the surface has `+= -= &= |=`). -/
def uOpBasis : String → Option String
  | "+=" => some "+"
  | "-=" => some "-"
  | "&=" => some "&"
  | "|=" => some "|"
  | _ => none

/-- An assignment, plain or compound (`p op= v` is `p = p op v`): a `let mut` local, a slot or a static. -/
def uSetze (ctx : UCtx) (ziel : SExpr) (op : String) (wert : SExpr) : Except String UStmt :=
  match (if strEq op "=" then some wert else (uOpBasis op).map fun b => SExpr.bin b ziel wert) with
  | none => .error "stmt without G form"
  | some w =>
    match ziel with
    | .variable x => if ctx.muts.any (strEq · x) then uSetzeLokal ctx x w else uSetzePlatz ctx ziel w
    | .arrow (.variable r) f =>
      match uRefLokal ctx r with
      | .some _ =>
        match uWertBody ctx w with
        | .error e => .error e
        | .ok v => .ok (.assignRef r f v)
      | .none => uSetzePlatz ctx ziel w
    | _ => uSetzePlatz ctx ziel w

/-- A call through a local function pointer `p` (bound by `let p = &f;`): `some` of the head of the function it
    points at; `none` when `p` is no such local. -/
def uFnZeiger (ctx : UCtx) (koepfe : List UFnKopf) (p : String) : Option (Except String UFnKopf) :=
  match uParamNr ctx p with
  | .error _ => none
  | .ok j =>
    match uArtBei ctx.kinds j with
    | .ok (.fnptr n) =>
      if n < ctx.zeigerBasis then
        some (match koepfe[n]? with
          | some k => .ok k
          | none => .error "function pointer to no function")
      else
        -- a pointer of a declared pointer type: the head of the type (`fn#j`)
        some (match koepfe.find? (fun (k : UFnKopf) => strEq k.name ("fn#" ++ toString (n - ctx.zeigerBasis))) with
          | some k => .ok k
          | none => .error "function pointer of no type")
    | _ => none

/-- The state that declares the transition `von -> nach` (by stage names): exactly one, with the stage numbers. -/
def uZustandVon (zs : List UZustand) (von nach : String) : Except String (String × Nat × Nat) :=
  let treffer := zs.filterMap fun z =>
    match z.stufen.findIdx? (strEq · von), z.stufen.findIdx? (strEq · nach) with
    | some a, some c => if z.paare.contains (a, c) then some (z.name, a, c) else none
    | _, _ => none
  match treffer with
  | [x] => .ok x
  | [] => .error "transition not declared by a state"
  | _ => .error "transition declared by two states"

/-- The kind word of a statement, named in a refusal. -/
def anwArt : SAnw → String
  | .bind .. => "let" | .bindElse .. => "let else" | .bindLib .. => "library let" | .set .. => "assignment"
  | .shift .. => "shift" | .call .. => "call" | .lcall .. => "library call" | .cond .. => "if"
  | .elsif .. => "else if" | .cases .. => "match" | .arm .. => "match arm" | .each .. => "traverse"
  | .retry .. => "retry" | .loop .. => "loop" | .waive .. => "waive" | .trim .. => "trim" | .locks .. => "locks"
  | .watch .. => "watch" | .leave .. => "leave" | .next .. => "next" | .emit .. => "emit" | .await .. => "await"
  | .swap .. => "exchange" | .step .. => "step" | .ret .. => "return" | .alloc .. => "alloc" | .reset .. => "reset"
  | .grow .. => "grow" | .free .. => "free" | .child .. => "child" | .start .. => "start" | .other w => w
  | .block .. => "block" | .allocVon .. => "alloc from a provider"

/-- One body statement: an assignment or a direct call (the
    `tr_stmt` of `lean_g.rs`; mid-body `return` and every other statement are explicit errors). -/
def uAnw1 (ctx : UCtx) (tabs : List UTab) (koepfe : List UFnKopf) :
    SAnw → Except String UStmt
  | .set ziel op wert =>
    match uRegOrt ctx ziel with
    | some (.error e) => .error e
    | some (.ok rg) =>
      if !strEq op "=" then .error "compound register write without G form"
      else if rg.bool then
        match uBool ctx wert with
        | .error e => .error e
        | .ok b => .ok (.regWriteB rg.dev rg.name b)
      else
        match uWertBody ctx wert with
        | .error e => .error e
        | .ok s => .ok (.regWrite rg.dev rg.name s)
    | none => uSetze ctx ziel op wert
  | .emit ziel wert p => uAtomSchreib ctx ziel wert p
  | .shift z von nach =>
    match uZugriff ctx z with
    | .error e => .error e
    | .ok (.thru .., _, _, _) => .error "transition through a pointer without G form"
    | .ok (.tabelle _, tb, f, ix) =>
      match uZustandVon ctx.zustaende von nach with
      | .error e => .error e
      | .ok (s, a, c) => .ok (.shiftTab tb f ix s (Int.ofNat a) (Int.ofNat c))
  | .reset a .none =>
    if ctx.tabs.any (fun x => x.arena && strEq x.name a) then .ok (.assignGlob (a ++ "#used") (.lit 0))
    else .error ("arena unknown: " ++ a)
  | .call c args =>
    match uFnZeiger ctx koepfe c with
    | some (.error e) => .error e
    | some (.ok ziel) =>
      match uRuf ctx tabs koepfe ziel.name args with
      | .error e => .error e
      | .ok (callee, xs) =>
        if callee.kanal.isSome then .error "call of a function with a reason channel needs `let .. else`"
        else .ok (.callInd c callee.name xs)
    | none =>
    match uRuf ctx tabs koepfe c args with
    | .error e => .error e
    | .ok (callee, xs) =>
      if callee.kanal.isSome then .error "call of a function with a reason channel needs `let .. else`"
      else .ok (if callee.ext then .axCall c xs else .call c xs)
  | .start _ =>
    if ctx.held.isEmpty then .ok .startS else .error "start under a held lock: the start step has an empty held list"
  | s => .error ("stmt without G form: " ++ anwArt s)

/-- A written binder type at a read of the static `A` (`awaits`, `exchange`): it must be `A`'s own type. -/
def uBinderTyp (ctx : UCtx) (wo : String) : Option STyp → GTy → Except String Unit
  | .none, _ => .ok ()
  | .some (.atom "bool"), .bool => .ok ()
  | .some t, .int lo hi =>
    match uErgBereich ctx.alias t with
    | .ok (l, h) => if l == lo && h == hi then .ok () else .error (wo ++ " binder typed other than its static")
    | .error err => .error err
  | .some _, _ => .error (wo ++ " binder typed other than its static")

/-- The names in braces at the head of `ts` (`{ p, q }`), and what follows. -/
def uKlammerNamen : List Token → Option (List String × List Token)
  | .zeichen "{" :: ts =>
    let innen := ts.takeWhile (fun t => t != .zeichen "}")
    match ts.dropWhile (fun t => t != .zeichen "}") with
    | .zeichen "}" :: rest =>
      if innen.all (fun t => match t with | .ident _ => true | .zeichen "," => true | _ => false) then
        some (innen.filterMap (fun t => match t with | .ident n => some n | _ => none), rest)
      else none
    | _ => none
  | _ => none

/-- The clauses behind an exchange: `[publishes nothing | publishes { … }] [awaits { … }]`. The payload names
    (empty for `nothing` or no clause) and the `awaits` names, if any. -/
def uTauschKlauseln : List Token → Except String (List String × Option (List String))
  | ts =>
    let (pub, ts1) : List String × List Token := match ts with
      | .wort "publishes" :: .wort "nothing" :: r => ([], r)
      | .wort "publishes" :: r => (match uKlammerNamen r with | some (ns, r') => (ns, r') | none => ([], .wort "publishes" :: r))
      | r => ([], r)
    match ts1 with
    | [] => .ok (pub, none)
    | .wort "awaits" :: r =>
      match uKlammerNamen r with
      | some (ns, []) => .ok (pub, some ns)
      | _ => .error "exchange clause without G form"
    | _ => .error "exchange clause without G form"

/-- The value an arm of an `update` body returns: `{ return e; }`. -/
def uArmWert : SAnw → Option SExpr
  | .block [] (some (.ret (some e))) => some e
  | _ => none

/-- An `update` body as guarded values and a last value: `if c₁ { return e₁; } else if … else { return e; }`, or
    `if c₁ { return e₁; } … return e;`. Fuel for the chain. -/
def uZweige : Nat → SAnw → Option (List (SExpr × SExpr) × SExpr)
  | 0, _ => none
  | _ + 1, .block [] (some (.ret (some e))) => some ([], e)
  | f + 1, .block (.cond c t ei els :: rest) ende =>
    match uArmWert t with
    | none => none
    | some e1 =>
      let weiter : Option SAnw := match ei, els with
        | .elsif c2 b2 :: ei', _ => some (.block (.cond c2 b2 ei' els :: rest) ende)
        | [], some b => if rest.isEmpty && ende.isNone then some b else none
        | [], none => some (.block rest ende)
        | _, _ => none
      match weiter.bind (uZweige f) with
      | some (zs, s) => some ((c, e1) :: zs, s)
      | none => none
  | _ + 1, _ => none

/-- `old(A)` in the predicate of a compare-exchange is the old value of `A`, the local `#alt`. Fuel for the depth. -/
def uAltErsetze (a : String) : Nat → SExpr → SExpr
  | 0, e => e
  | _ + 1, .old (.variable b) => if strEq a b then .variable "#alt" else .old (.variable b)
  | f + 1, .un o e => .un o (uAltErsetze a f e)
  | f + 1, .bin o x y => .bin o (uAltErsetze a f x) (uAltErsetze a f y)
  | f + 1, .call n args => .call n (args.map (uAltErsetze a f))
  | _ + 1, e => e

/-- What a guard says about the local `v`: a lower and an upper bound, from comparisons with literals under `and`
    (and their negations, `pos = false`, under `or`); anything else says nothing. -/
def uGrenzen (v : String) : Bool → UEns → Option Int × Option Int
  | pos, .cmp op (.param x) (.lit k) =>
    if !strEq x v then (none, none) else uGrenzeCmp pos op k
  | pos, .cmp op (.lit k) (.param x) =>
    if !strEq x v then (none, none) else uGrenzeCmp pos (uDreh op) k
  | true, .and a b => uGrenzenUnd (uGrenzen v true a) (uGrenzen v true b)
  | false, .or a b => uGrenzenUnd (uGrenzen v false a) (uGrenzen v false b)
  | pos, .not a => uGrenzen v (!pos) a
  | _, _ => (none, none)
where
  /-- `x op k` (or its negation) as bounds of `x`. -/
  uGrenzeCmp (pos : Bool) (op : String) (k : Int) : Option Int × Option Int :=
    if pos then
      if strEq op "<" then (none, some (k - 1)) else if strEq op "<=" then (none, some k)
      else if strEq op ">" then (some (k + 1), none) else if strEq op ">=" then (some k, none)
      else if strEq op "==" then (some k, some k) else (none, none)
    else
      if strEq op "<" then (some k, none) else if strEq op "<=" then (some (k + 1), none)
      else if strEq op ">" then (none, some k) else if strEq op ">=" then (none, some (k - 1))
      else if strEq op "!=" then (some k, some k) else (none, none)
  /-- `k op x` read as `x op' k`. -/
  uDreh (op : String) : String :=
    if strEq op "<" then ">" else if strEq op "<=" then ">=" else if strEq op ">" then "<"
    else if strEq op ">=" then "<=" else op
  /-- Both bounds hold: the tighter of each. -/
  uGrenzenUnd (a b : Option Int × Option Int) : Option Int × Option Int :=
    (match a.1, b.1 with | some x, some y => some (max x y) | some x, none => some x | none, y => y,
     match a.2, b.2 with | some x, some y => some (min x y) | some x, none => some x | none, y => y)

/-- Every read of the local `v` in `s` narrowed to `lo .. hi` (`USide.eng`). -/
def uSideEng (v : String) (lo hi : Int) : USide → USide
  | .param p => if strEq p v then .eng (.param p) lo hi else .param p
  | .add a b => .add (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .sub a b => .sub (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .mul a b => .mul (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .conv l h a => .conv l h (uSideEng v lo hi a)
  | .band a b => .band (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .bor a b => .bor (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .bxor a b => .bxor (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .div a b => .div (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .rem a b => .rem (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .shl a b => .shl (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .shr a b => .shr (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .neg a => .neg (uSideEng v lo hi a)
  | s => s

/-- The value of an `update` arm with `v` narrowed by the arm's guard (`pos` the arm's own condition, `negs` the
    conditions of the arms before it, all false there), inside the static's range `slo .. shi`. -/
def uArmEng (v : String) (slo shi : Int) (pos : Option UEns) (negs : List UEns) (s : USide) : USide :=
  let gs := (match pos with | some c => [uGrenzen v true c] | none => []) ++ negs.map (uGrenzen v false)
  let lo := gs.foldl (fun acc g => match g.1 with | some x => max acc x | none => acc) slo
  let hi := gs.foldl (fun acc g => match g.2 with | some x => min acc x | none => acc) shi
  if lo == slo && hi == shi then s else if lo ≤ hi then uSideEng v lo hi s else s

/-- An exchange as read from its tail: the update binder, the guarded values, the last value, the payload, the
    `awaits` names, and whether it is the compare form (whose binder is the success, a truth value). -/
structure UTausch where
  v : String
  zweige : List (SExpr × SExpr)
  sonst : SExpr
  pub : List String
  aw : Option (List String)
  vergleich : Option SExpr

/-- The tail of an exchange (`exchstmt` of SYNTAX.md): `update(v) [bounded n ops] [on_exceeded k] { … } [clauses]`,
    or `e when p returns r [clauses]` (compare-exchange: the new value `e` if `p` holds of the old value, else the
    old value; the binder is `p`, Rust `kosten.rs`). The bound and the exit belong to the lowering (G takes the
    exchange as one atomic step, A10). -/
def uTauschSchwanz (a k : String) : Except String UTausch :=
  match lex k with
  | .error _ => .error "exchange without G form"
  | .ok toks0 =>
    let toks := toks0.filter (fun t => match t with | .ende => false | _ => true)
    let fuel := 8 * toks.length + 30
    match toks with
    | .wort "update" :: .zeichen "(" :: .ident v :: .zeichen ")" :: rest =>
      match rest.dropWhile (fun t => t != .zeichen "{") with
      | .zeichen "{" :: innen =>
        match parseBlock fuel (.zeichen "{" :: innen) with
        | .ok (b, kl) =>
          match uZweige 64 b, uTauschKlauseln kl with
          | some (zs, s), .ok (pub, aw) => .ok ⟨v, zs, s, pub, aw, none⟩
          | none, _ => .error "exchange update body other than guarded values without G form"
          | _, .error err => .error err
        | .error _ =>
          -- an expression body `{ e }`
          match parseOr fuel innen with
          | .error _ => .error "exchange update body without G form"
          | .ok (e, .zeichen "}" :: kl) =>
            match uTauschKlauseln kl with
            | .error err => .error err
            | .ok (pub, aw) => .ok ⟨v, [], e, pub, aw, none⟩
          | .ok (_, _) => .error "exchange update body other than one value without G form"
      | _ => .error "exchange update without a body"
    | _ =>
      match parseOr fuel toks with
      | .ok (neu, .wort "when" :: r1) =>
        match parseOr fuel r1 with
        | .ok (p, .wort "returns" :: .ident _ :: kl) =>
          match uTauschKlauseln kl with
          | .error err => .error err
          | .ok (pub, aw) =>
            let p' := uAltErsetze a 64 p
            .ok ⟨"#alt", [(p', neu)], .variable "#alt", pub, aw, some p'⟩
        | _ => .error "exchange compare form without G form"
      | _ => .error "exchange without G form"

/-- The context after `let x [: T]`: the annotated range (when there is one) and the context in which the
    rest of the block reads `x` as a numeric parameter that shadows any earlier name. -/
def uBindKopf (ctx : UCtx) (x : String) : Option STyp → Except String (Option (Int × Int) × UCtx)
  | .none =>
    .ok (.none, { ctx with names := x :: ctx.names, kinds := .int :: ctx.kinds,
                           types := .int 0 0 :: ctx.types, bits := 0 :: ctx.bits })
  | .some ty =>
    match uErgBereich ctx.alias ty with
    | .error e => .error e
    | .ok (lo, hi) =>
      .ok (.some (lo, hi), { ctx with names := x :: ctx.names, kinds := .int :: ctx.kinds,
                                      types := .int lo hi :: ctx.types,
                                      bits := uParamBreite ty :: ctx.bits })

/-- The context after a local `x` of kind `k` and type `ty`. -/
def uMitLokal (ctx : UCtx) (x : String) (k : UParamArt) (ty : Ty) (muts : List String) : UCtx :=
  { ctx with names := x :: ctx.names, kinds := k :: ctx.kinds, types := ty :: ctx.types, bits := 0 :: ctx.bits, muts := muts }

/-- The words that start a section of a `retry`/`forever` header. -/
def uSchleifenWort (s : String) : Bool :=
  strEq s "until" || strEq s "bounded" || strEq s "per_pass" || strEq s "progress" ||
    strEq s "on_exceeded" || strEq s "effects" || strEq s "leaves"

/-- A loop header split into its sections: the key word (empty for the leading label) and the tokens up to
    the next key word at brace depth zero. -/
def uKopfAbschnitte : List Token → Nat → String → List Token → List (String × List Token) →
    List (String × List Token)
  | [], _, k, acc, out => out ++ [(k, acc.reverse)]
  | t :: rest, d, k, acc, out =>
    match t with
    | .zeichen "{" => uKopfAbschnitte rest (d + 1) k (t :: acc) out
    | .zeichen "}" => uKopfAbschnitte rest (d - 1) k (t :: acc) out
    | .wort w =>
      if d == 0 && uSchleifenWort w then uKopfAbschnitte rest d w [] (out ++ [(k, acc.reverse)])
      else uKopfAbschnitte rest d k (t :: acc) out
    | .ident w =>
      if d == 0 && uSchleifenWort w then uKopfAbschnitte rest d w [] (out ++ [(k, acc.reverse)])
      else uKopfAbschnitte rest d k (t :: acc) out
    | _ => uKopfAbschnitte rest d k (t :: acc) out

/-- The tokens of a section by key word. -/
def uAbschnitt (secs : List (String × List Token)) (k : String) : Option (List Token) :=
  (secs.find? (fun s => strEq s.1 k)).map (·.2)

/-- A loop header's sections (the raw header of `SAnw.retry`/`SAnw.loop` read again by the lexer). -/
def uSchleifenKopf2 (h : String) : Except String (List (String × List Token)) :=
  match lex h with
  | .error _ => .error "loop header without G form"
  | .ok toks0 => .ok (uKopfAbschnitte (toks0.filter (fun k => match k with | .ende => false | _ => true)) 0 "" [] [])

/-- A name section: one word. -/
def uEinName : Option (List Token) → Option String
  | some [.ident n] => some n
  | some [.wort n] => some n
  | _ => none

/-- `bounded N ops`. -/
def uOpsZahl (ctx : UCtx) : Option (List Token) → Option Nat
  | some [.num n, .wort _] => some n
  | some [.num n, .ident _] => some n
  | some [.ident c, .wort _] => (ctx.lits.find? (fun k => strEq k.1 c)).bind fun k => if 0 ≤ k.2 then some k.2.toNat else none
  | _ => none

/-- The header of a `retry`: the label, the pass bound, the predicate, the handler. `progress` must name an
    `assume` item. -/
def uRetryKopf (ctx : UCtx) (h : String) : Except String (String × Nat × UEns × String) :=
  match uSchleifenKopf2 h with
  | .error e => .error e
  | .ok secs =>
    match uAbschnitt secs "until", uOpsZahl ctx (uAbschnitt secs "bounded"), uEinName (uAbschnitt secs "progress"),
        uEinName (uAbschnitt secs "on_exceeded") with
    | some pt, some n, some a, some y =>
      if !(ctx.annahmen.any (strEq · a)) then .error ("assumption unknown: " ++ a)
      else
        match parseTop (pt ++ [Token.ende]) with
        | .error _ => .error "retry condition without G form"
        | .ok p =>
          match uBool ctx p with
          | .error e => .error e
          | .ok pv => .ok ((match uAbschnitt secs "" with | some [.ident l] => l | some [.wort l] => l | _ => ""), n, pv, y)
    | none, _, _, _ => .error "retry without until without G form"
    | _, _, _, _ => .error "retry header without G form"

/-- The header of a `forever`: the label and the position of the assumption `progress` names. -/
def uForeverKopf (ctx : UCtx) (h : String) : Except String (String × Nat) :=
  match uSchleifenKopf2 h with
  | .error e => .error e
  | .ok secs =>
    match uAbschnitt secs "leaves" with
    | some _ => .error "forever leaves without G form"
    | none =>
      match uEinName (uAbschnitt secs "progress") with
      | none => .error "forever without progress without G form"
      | some a =>
        match ctx.annahmen.findIdx? (fun x => strEq x a) with
        | none => .error ("assumption unknown: " ++ a)
        | some k => .ok ((match uAbschnitt secs "" with | some [.ident l] => l | some [.wort l] => l | _ => ""), k)

/-- The value of a bound of a narrowed range: a numeral, a negated numeral or a named constant. -/
def uNarrowWert (ctx : UCtx) : List Token → Option Int
  | [.num n] => some (Int.ofNat n)
  | [.zeichen "-", .num n] => some (-(Int.ofNat n))
  | [.ident c] => (ctx.lits.find? (fun k => strEq k.1 c)).map (·.2)
  | [.wort c] => (ctx.lits.find? (fun k => strEq k.1 c)).map (·.2)
  | _ => none

/-- A range text `lo .. hi` / `lo ..< hi` split at the dots: the left tokens, whether the upper bound is
    exclusive, the right tokens. -/
def uTeileBereich : List Token → List Token → Option (List Token × Bool × List Token)
  | _, [] => none
  | acc, .zeichen ".." :: rest => some (acc.reverse, false, rest)
  | acc, .zeichen "..<" :: rest => some (acc.reverse, true, rest)
  | acc, t :: rest => uTeileBereich (t :: acc) rest

/-- The target range of `narrow x to T else ..`: a range (`lo .. hi`, `lo ..< hi`) or a type word. -/
def uNarrowBereich (ctx : UCtx) (t : String) : Except String (Int × Int) :=
  match lex t with
  | .error _ => .error "narrow range without G form"
  | .ok toks0 =>
    let toks := toks0.filter (fun k => match k with | .ende => false | _ => true)
    match uTeileBereich [] toks with
    | some (l, ex, r) =>
      match uNarrowWert ctx l, uNarrowWert ctx r with
      | some a, some b => .ok (a, if ex then b - 1 else b)
      | _, _ => .error "narrow bound without G form"
    | none =>
      match toks with
      | [.ident n] => uTypName ctx.alias n
      | [.wort n] => uTypName ctx.alias n
      | _ => .error "narrow range without G form"

/-- The binding the rest of the block reads after a narrowing: `x` at the narrowed range. -/
def uNarrowKopf (ctx : UCtx) (x : String) (t : String) : Except String (Int × Int × UCtx) :=
  match uParamNr ctx x with
  | .error e => .error e
  | .ok j =>
    match uArtBei ctx.kinds j with
    | .ok .int =>
      match uNarrowBereich ctx t with
      | .error e => .error e
      | .ok (lo, hi) =>
        .ok (lo, hi, uMitLokal ctx x UParamArt.int (Ty.int lo hi) (ctx.muts.filter (fun m => !strEq m x)))
    | _ => .error "narrow of a non-number"

/-- `let [mut] x [: T] = v;`: a number (the binding carries the computed range of `v`, or with `mut` the
    declared one) or a truth value; the statement and the context for the rest of the block. -/
def uBindWertAllg (ctx : UCtx) (mu : Bool) (x : String) (t : Option STyp) (e : SExpr) :
    Except String (UStmt × UCtx) :=
  let muts : List String := if mu then x :: ctx.muts else ctx.muts.filter (fun m => !strEq m x)
  let boolCtx : UCtx := { ctx with names := x :: ctx.names, kinds := UParamArt.bool :: ctx.kinds,
                                   types := Ty.bool :: ctx.types, bits := 0 :: ctx.bits, muts := muts }
  match t with
  | .some (.atom "bool") =>
    match uBool ctx e with
    | .error err => .error err
    | .ok b => .ok (.bindB x b, boolCtx)
  | .some (.index true tn) =>
    if mu then .error "let mut of an option without G form"
    else
      match uTabNr ctx.tabs tn with
      | .error err => .error err
      | .ok (num, c) =>
        match uOpt ctx num e with
        | .error err => .error err
        | .ok o => .ok (.bindOpt x num o, uMitLokal ctx x (UParamArt.opt num) (Ty.opt c) muts)
  | .none =>
    match uWertBody ctx e with
    | .ok sd =>
      if mu then .error "let mut without a type"
      else
        match uBindKopf ctx x .none with
        | .error err => .error err
        | .ok (d, ctx') => .ok (.bind x d sd, { ctx' with muts := muts })
    | .error err =>
      match uBool ctx e with
      | .ok b => .ok (.bindB x b, boolCtx)
      | .error _ =>
        match uOptEin ctx e with
        | .error _ =>
          match uSValEin ctx e with
          | .error _ => .error err
          | .ok (sv, k) =>
            match ctx.sums[k]? with
            | .none => .error err
            | .some sm => .ok (.bindSum x k sv, uMitLokal ctx x (UParamArt.sum k) (Ty.sum sm.spec) muts)
        | .ok (o, num) =>
          match ctx.tabs[num]? with
          | .none => .error err
          | .some tb => .ok (.bindOpt x num o, uMitLokal ctx x (UParamArt.opt num) (Ty.opt tb.count) muts)
  | .some ty@(.array _ _) | .some ty@(.str _) =>
    if mu then .error "let mut of an aggregate without G form"
    else
      match uTyp ctx.alias ctx.tabs ty with
      | .error err => .error err
      | .ok τ =>
        match uWertBody ctx e with
        | .error err => .error err
        | .ok sd => .ok (.bindW x (some τ) sd, uMitLokal ctx x UParamArt.wert τ muts)
  | .some ty =>
    match uWertBody ctx e with
    | .error err => .error err
    | .ok sd =>
      match uBindKopf ctx x (.some ty) with
      | .error err => .error err
      | .ok (d, ctx') =>
        if mu then
          match d with
          | .some (lo, hi) => .ok (.bindMut x lo hi sd, { ctx' with muts := muts })
          | .none => .error "let mut without a type"
        else .ok (.bind x d sd, { ctx' with muts := muts })

/-- `let [mut] x [: T] = v;` where `v` may be a call of a function of the unit: its value is bound at the
    callee's result type (`Block.bindCall`; a range annotation must contain the result range). -/
def uBindWert (ctx : UCtx) (tabs : List UTab) (koepfe : List UFnKopf) (mu : Bool) (x : String)
    (t : Option STyp) (e : SExpr) : Except String (UStmt × UCtx) :=
  match uRegOrt ctx e with
  | some (.error err) => .error err
  | some (.ok rg) =>
    if mu || t.isSome then .error "let of a register with a type without G form"
    else if rg.pruefung.isSome then .error "fallible register read needs `let .. else`"
    else .ok (.regRead x rg.dev rg.name,
      uMitLokal ctx x rg.art rg.ty (ctx.muts.filter (fun m => !strEq m x)))
  | none =>
  match (match t with | .some (.atom a) => ctx.sums.findIdx? (fun (s : USum) => strEq s.name a) | _ => none : Option Nat) with
  | .some k =>
    if mu then .error "let mut of a tagged value without G form"
    else
      match ctx.sums[k]? with
      | .none => .error "tagged type unknown"
      | .some sm =>
        match uSVal ctx k e with
        | .error err => .error err
        | .ok sv =>
          .ok (.bindSum x k sv, uMitLokal ctx x (UParamArt.sum k) (Ty.sum sm.spec) (ctx.muts.filter (fun m => !strEq m x)))
  | .none =>
  match (match e with
      | .fnref f =>
        if (uParamNr ctx f).toOption.isSome || ctx.tabs.any (fun tb => strEq tb.name f) then none
        else
          match koepfe.findIdx? (fun (k : UFnKopf) => strEq k.name f) with
          | none => none
          | some n =>
            some (match koepfe[n]? with
              | some k =>
                if k.ext then .error "address of a foreign fn without G form"
                else if mu then .error "let mut of a function pointer without G form"
                else
                  -- The type of the pointer: the one written (`let p : fn(..) = &f;`, a pointer type of the
                  -- unit, number `zeigerBasis + j`), else `f`'s own signature (number `n`). That `f` conforms
                  -- to a written type is the lowering's decision (`Deklaration.passt`).
                  match (match t with
                      | .none => .ok n
                      | .some (.raw r) =>
                        match ctx.zeiger.findIdx? (strEq · r) with
                        | .some j => .ok (ctx.zeigerBasis + j)
                        | .none => .error "let of a function pointer with a type that is no pointer type"
                      | .some _ => .error "let of a function pointer with a type that is no pointer type" :
                      Except String Nat) with
                  | .error err => .error err
                  | .ok m =>
                    .ok (.bindFnref x f m, uMitLokal ctx x (UParamArt.fnptr m) (Ty.fnptr m)
                      (ctx.muts.filter (fun m => !strEq m x)))
              | none => .error ("function unknown: " ++ f))
      | .call c args =>
        match uFnZeiger ctx koepfe c with
        | none => none
        | some (.error err) => some (.error err)
        | some (.ok ziel) =>
          some (if mu || t.isSome then .error "let of an indirect call with a type without G form" else
            match uRuf ctx tabs koepfe ziel.name args with
            | .error err => .error err
            | .ok (callee, xs) =>
              let muts : List String := ctx.muts.filter (fun m => !strEq m x)
              if callee.kanal.isSome then .error "call of a function with a reason channel needs `let .. else`"
              else if callee.resBool then
                .ok (.bindCallInd x c callee.name xs, uMitLokal ctx x UParamArt.bool Ty.bool muts)
              else match callee.res with
                | some (lo, hi) => .ok (.bindCallInd x c callee.name xs, uMitLokal ctx x UParamArt.int (Ty.int lo hi) muts)
                | none =>
                  match callee.resWhy with
                  | some (k, n) => .ok (.bindCallInd x c callee.name xs, uMitLokal ctx x (UParamArt.why k) (Ty.why n) muts)
                  | none => .error "call without a value")
      | _ => none : Option (Except String (UStmt × UCtx))) with
  | some r => r
  | none =>
  match e with
  | .call c args =>
    match koepfe.find? (fun (k : UFnKopf) => strEq k.name c) with
    | .none => uBindWertAllg ctx mu x t e
    | .some _ =>
      if mu then .error "let mut of a call without G form"
      else
        match uRuf ctx tabs koepfe c args with
        | .error err => .error err
        | .ok (callee, xs) =>
          let muts : List String := ctx.muts.filter (fun m => !strEq m x)
          if callee.kanal.isSome then .error "call of a function with a reason channel needs `let .. else`"
          else
          if callee.ext then
            match callee.axErg with
            | .none => .error "call without a value"
            | .some Ty.bool => .ok (.bindAx x c xs, uMitLokal ctx x UParamArt.bool Ty.bool muts)
            | .some (Ty.int lo hi) => .ok (.bindAx x c xs, uMitLokal ctx x UParamArt.int (Ty.int lo hi) muts)
            | .some (Ty.ref n) => .ok (.bindAx x c xs, uMitLokal ctx x (UParamArt.ref n) (Ty.ref n) muts)
            | .some _ => .error "answer of a foreign fn without G form"
          else
          match callee.resBool, callee.res with
          | true, _ =>
            match t with
            | .some (.atom "bool") =>
              .ok (.bindCall x c xs, uMitLokal ctx x UParamArt.bool (Ty.bool) muts)
            | .none =>
              .ok (.bindCall x c xs, uMitLokal ctx x UParamArt.bool (Ty.bool) muts)
            | .some _ => .error "let of a truth value with a number type"
          | false, .some (lo, hi) =>
            match (match t with
                | .none => .ok true
                | .some ty =>
                  match uErgBereich ctx.alias ty with
                  | .error err => .error err
                  | .ok (a, b) => .ok (decide (a ≤ lo) && decide (hi ≤ b)) : Except String Bool) with
            | .error err => .error err
            | .ok false => .error "let: value outside the annotated range"
            | .ok true =>
              .ok (.bindCall x c xs, uMitLokal ctx x UParamArt.int (Ty.int lo hi) muts)
          | false, .none =>
            match callee.resWhy, t with
            | .some (k, n), .none => .ok (.bindCall x c xs, uMitLokal ctx x (UParamArt.why k) (Ty.why n) muts)
            | _, _ => .error "call without a value"
  | _ => uBindWertAllg ctx mu x t e

/-- `return R::C` through the reason channel. -/
def uEndeKanal (ctx : UCtx) (r c : String) : Except String URet :=
  match ctx.kanal, ctx.whys.findIdx? (fun w => strEq w.name r) with
  | .some (k, _), .some j =>
    if k != j then .error "return of a foreign reason"
    else
      match ctx.whys[j]? with
      | .some w =>
        match w.cases.findIdx? (fun x => strEq x c) with
        | .some i => .ok (.why i)
        | .none => .error ("reason case unknown: " ++ c)
      | .none => .error ("reason unknown: " ++ r)
  | .none, _ => .error "return of a reason without a reason channel"
  | _, .none => .error ("reason unknown: " ++ r)

/-- The trailing return (the `check_body`/`tr_body` of
    `lean_g.rs`): a result falls off nowhere, and a missing
    result returns nowhere. -/
def uEnde (ctx : UCtx) : Option SEnde → Except String URet
  | .none =>
    -- a `-> never` function ends in a call that does not return: its `never` answer is the result
    if ctx.resTy == some Ty.never then .ok (.wert (.param "#ax")) else
    match ctx.res with
    | .some _ => .error "fn with a result falls off"
    | .none => if ctx.resBool || ctx.resOpt.isSome || ctx.resSum.isSome || ctx.resTy.isSome then .error "fn with a result falls off" else .ok .empty
  | .some (.ret .none) =>
    match ctx.res with
    | .some _ => .error "return without value with result"
    | .none => if ctx.resBool || ctx.resOpt.isSome || ctx.resSum.isSome || ctx.resTy.isSome then .error "return without value with result" else .ok .empty
  | .some (.ret (.some (.why r c))) =>
    match ctx.resWhy, ctx.whys.findIdx? (fun w => strEq w.name r) with
    | .some (k, _), .some j =>
      -- a function of reason type `R` returns the VALUE `R::C` (its channel, if any, names another reason)
      if k == j && ctx.kanal.map (·.1) != some j then
        match ctx.whys[j]? with
        | .some w =>
          match w.cases.findIdx? (fun x => strEq x c) with
          | .some i => .ok (.grund (.fall i))
          | .none => .error ("reason case unknown: " ++ c)
        | .none => .error ("reason unknown: " ++ r)
      else uEndeKanal ctx r c
    | _, _ => uEndeKanal ctx r c
  | .some (.ret (.some v)) =>
    if ctx.resTy.isSome then
      match uWertBody ctx v with
      | .error e => .error e
      | .ok w => .ok (.wert w)
    else
    match ctx.resWhy with
    | .some (k, _) =>
      match v with
      | .variable p =>
        match uParamNr ctx p with
        | .error e => .error e
        | .ok j =>
          match uArtBei ctx.kinds j with
          | .ok (.why k') => if k' == k then .ok (.grund (.var p)) else .error "return of a foreign reason"
          | _ => .error "return of a non-reason for a reason result"
      | _ => .error "reason result without G form"
    | .none =>
    match ctx.resSum with
    | .some (sidx, _) =>
      match uSVal ctx sidx v with
      | .error e => .error e
      | .ok sv => .ok (.sum sv)
    | .none =>
    match ctx.resOpt with
    | .some (num, _) =>
      match uOpt ctx num v with
      | .error e => .error e
      | .ok o => .ok (.opt o)
    | .none =>
    if ctx.resBool then
      match uBool ctx v with
      | .error e => .error e
      | .ok b => .ok (.bool b)
    else
    match ctx.res with
    | .none => .error "return with value without result"
    | .some _ =>
      match uWertBody ctx v with
      | .error e => .error e
      | .ok s => .ok (.val s)
  | .some _ => .error "block end without G form"

/-- The ender of a nested block as a statement: `return [v]` (against the function's result), or
    `leave i`/`next i` naming the innermost `traverse` binder. -/
def uEndeStmt (ctx : UCtx) : Option SEnde → Except String (List UStmt)
  | .none => .ok []
  | .some (.ret v) =>
    match uEnde ctx (.some (.ret v)) with
    | .error e => .error e
    | .ok r => .ok [UStmt.ret r]
  | .some (.leave m) =>
    if ctx.loops.head? == some m then .ok [UStmt.leave m]
    else .error "leave outside the innermost loop"
  | .some (.next m) =>
    if ctx.loops.head? == some m then .ok [UStmt.next m]
    else .error "next outside the innermost loop"

/-- The header of `traverse b over slots of S by unvisited [touches …] [invariant p]`: the table (named
    directly or through a pointer parameter), the invariant over the OUTER context (the binder is not in
    scope there), and the context of the body, where the binder is an index into the table and the
    innermost loop label. Other domains, `of e` and `by consuming` have no G form. -/
def uSchleifenKopf (ctx : UCtx) (b : String) (o : Option SExpr) (k : String) (s : SExpr) (m : String)
    (inv : Option SExpr) : Except String (String × UEns × UCtx) :=
  if o.isSome then .error "traverse of without G form"
  else if !strEq k "slots" then .error "traverse domain without G form"
  else if !strEq m "unvisited" then .error "traverse by consuming without G form"
  else
    match (match s with
        | .variable tn =>
          match ctx.tabs.findIdx? (fun x => strEq x.name tn) with
          | .some num => .ok (tn, num)
          | .none =>
            match uParamNr ctx tn with
            | .error e => .error e
            | .ok j =>
              match uArtBei ctx.kinds j with
              | .ok (.ptr num _) =>
                match ctx.tabs[num]? with
                | .some tb => .ok (tb.name, num)
                | .none => .error "pointer table unknown"
              | _ => .error "traverse domain without G form"
        | _ => .error "traverse domain without G form" : Except String (String × Nat)) with
    | .error e => .error e
    | .ok (tab, num) =>
      match (match inv with
          | .none => .ok UEns.tru
          | .some p => uBool ctx p : Except String UEns) with
      | .error e => .error e
      | .ok iv =>
        let cnt : Int := match ctx.tabs[num]? with | .some tb => tb.count | .none => 0
        .ok (tab, iv, { ctx with names := b :: ctx.names, kinds := .index num :: ctx.kinds,
                                 types := .index cnt :: ctx.types, bits := 0 :: ctx.bits,
                                 loops := b :: ctx.loops })

/-- The body of an arm. -/
def uArmBody : SAnw → SAnw
  | .arm _ _ b => b
  | x => x

/-- The arm bodies of a reason match in the order of the reason's cases: exactly one arm per case. -/
def uWhyArme (cases : List String) (arms : List SAnw) : Option (List SAnw) :=
  if arms.length != cases.length then none
  else
    cases.mapM fun c =>
      (arms.find? (fun a => match a with | .arm n .none _ => strEq n c | _ => false)).map uArmBody

/-- The lists joined with the arm separator `ifElse`. -/
def uMitTrenner : List (List UStmt) → List UStmt
  | [] => []
  | [a] => a
  | a :: rest => a ++ [UStmt.ifElse] ++ uMitTrenner rest

/-- A field of a tagged type as a value, and the position of its type. -/
def uSumPlatz (ctx : UCtx) (e : SExpr) : Except String (USVal × Nat) :=
  match uZugriff ctx e with
  | .error x => .error x
  | .ok (b, tb, f, ix) =>
    match (ctx.tabs.find? (fun t => strEq t.name tb)).bind (fun t => t.sumFelder.find? (fun p => strEq p.1 f)) with
    | none => .error "match without G form"
    | some (_, k) =>
      match b with
      | .thru p => .ok (.slot p f ix, k)
      | .tabelle t => .ok (.tab t f ix, k)


/-- The statement ends the function on every path, looking through the last statement of each arm: an `if` with an
    `else`, or a `match` (every arm of a `match` the model accepts is there: `Arms`/`GrundArms` are indexed by the
    cases, an option match has both). Only then does a body without a trailing return get `URet.keins`. -/
def uEndetTief : Nat → SAnw → Bool
  | 0, _ => false
  | f + 1, .cond _ t ei els =>
    let arm : SAnw → Bool := fun b => match b with
      | .block ss e => e.isSome || (match ss.getLast? with | some s => uEndetTief f s | none => false)
      | _ => false
    arm t &&
      (match ei with
       | .elsif c2 b2 :: ei' => uEndetTief f (.cond c2 b2 ei' els)
       | [] => (match els with | some b => arm b | none => false)
       | _ => false)
  | f + 1, .cases _ arms =>
    !arms.isEmpty && arms.all (fun a => match a with
      | .arm _ _ (.block ss e) => e.isSome || (match ss.getLast? with | some s => uEndetTief f s | none => false)
      | _ => false)
  | _ + 1, _ => false

/-- The statement ends its block on every path: an `if` with an `else` whose arms end in a `return`, `leave` or
    `next` (an `else if` chain is the `if` in the `else`). Fuel for the chain. -/
def uEndetS : Nat → SAnw → Bool
  | 0, _ => false
  | f + 1, .cond _ (.block _ e) ei els =>
    let armEndet : SAnw → Bool := fun b => match b with
      | .block _ e' => e'.isSome
      | _ => false
    e.isSome &&
      (match ei with
       | .elsif c2 b2 :: ei' => uEndetS f (.cond c2 b2 ei' els)
       | [] => (match els with | some b => armEndet b | none => false)
       | _ => false)
  | _ + 1, _ => false

/-- A run of body statements as a flat list. A `let` extends the context for the rest of the run;
    `locks L { ... }` elaborates its body with `L` HELD (guards, calls) and the bindings made inside it
    end with it; a shared hold, a `return` inside the block and every other lock expression are refused.
    Structural in a fuel (one unit per statement and per block). -/
def uAnwReihe (tabs : List UTab) (koepfe : List UFnKopf) :
    Nat → UCtx → List SAnw → Except String (List UStmt × UCtx)
  | 0, _, _ => .error "nesting without G form"
  | _ + 1, ctx, [] => .ok ([], ctx)
  | f + 1, ctx, .bind mu x t e :: rest =>
    match uBindWert ctx tabs koepfe mu x t e with
    | .error err => .error err
    | .ok (st, ctx') =>
      match uAnwReihe tabs koepfe f ctx' rest with
      | .error err => .error err
      | .ok (xs, cE) => .ok (st :: xs, cE)
  | f + 1, ctx, .cases scrut arms :: rest =>
    match (match scrut with
        | .variable e =>
          match uParamNr ctx e with
          | .ok j =>
            match uArtBei ctx.kinds j with
            | .ok (.why num) => some (e, 0, num)
            | .ok (.sum num) => some (e, 1, num)
            | _ => none
          | .error _ =>
            (ctx.globs.find? (fun g => strEq g.name e)).bind fun g => g.sumNum.map fun num => (e, 1, num)
        | _ =>
          -- a field of a tagged type: bound to the hidden local `#m` first (`uSumPlatz`)
          match uSumPlatz ctx scrut with
          | .ok (_, num) => some ("#m", 1, num)
          | .error _ => none : Option (String × Nat × Nat)) with
    | .some (e, 1, num) =>
      -- a field of a tagged type is bound to `#m` first; the arms and the rest see it
      let (ctxM, vor) : UCtx × List UStmt :=
        match (if strEq e "#m" then (uSumPlatz ctx scrut).toOption else none), ctx.sums[num]? with
        | some (sv, _), some sm =>
          (uMitLokal ctx "#m" (UParamArt.sum num) (Ty.sum sm.spec) ctx.muts, [UStmt.bindSum "#m" num sv])
        | _, _ => (ctx, [])
      match ctxM.sums[num]? with
      | .none => .error "tagged type unknown"
      | .some sm =>
        if arms.length != sm.cases.length then .error "match arms without G form"
        else
        match uSeq (sm.cases.map fun (cn, pl) =>
            match arms.find? (fun a => match a with | .arm n _ _ => strEq n cn | _ => false) with
            | .some (.arm _ bnd (.block ss en)) =>
              match (match pl, bnd with
                  | .none, .none => some (ctxM, "")
                  | .some (lo, hi), .some k =>
                    some (uMitLokal ctxM k UParamArt.int (Ty.int lo hi) (ctxM.muts.filter (fun m => !strEq m k)), k)
                  | _, _ => none : Option (UCtx × String)) with
              | .none => .error "match arm payload without G form"
              | .some (cx, k) =>
                match uAnwReihe tabs koepfe f cx ss with
                | .error err => .error err
                | .ok (bd, ctxB) =>
                  match uEndeStmt ctxB en with
                  | .error err => .error err
                  | .ok endS => .ok (k, bd ++ endS)
            | _ => .error "match arms without G form") with
        | .error err => .error err
        | .ok arme =>
          match uAnwReihe tabs koepfe f ctxM rest with
          | .error err => .error err
          | .ok (ys, cE) =>
            .ok (vor ++ [UStmt.matchTagBeg num e (arme.map (·.1))] ++ uMitTrenner (arme.map (·.2)) ++ [UStmt.blkEnd] ++ ys, cE)
    | .some (e, _, num) =>
      match ctx.whys[num]? with
      | .none => .error "reason unknown"
      | .some w =>
        match uWhyArme w.cases arms with
        | .none => .error "match arms without G form"
        | .some bodies =>
          match uSeq (bodies.map fun b =>
              match b with
              | .block ss en =>
                match uAnwReihe tabs koepfe f ctx ss with
                | .error err => .error err
                | .ok (bd, ctxB) =>
                  match uEndeStmt ctxB en with
                  | .error err => .error err
                  | .ok endS => .ok (bd ++ endS)
              | _ => .error "match arm without a block") with
          | .error err => .error err
          | .ok arme =>
            match uAnwReihe tabs koepfe f ctx rest with
            | .error err => .error err
            | .ok (ys, cE) => .ok ([UStmt.matchWhyBeg e] ++ uMitTrenner arme ++ [UStmt.blkEnd] ++ ys, cE)
    | .none =>
    match uOptEin ctx scrut with
    | .error err => .error (if uPraemisse err then err else "stmt without G form")
    | .ok (o, num) =>
      match ctx.tabs[num]?, (match arms with
          | [.arm "Some" (.some k) sb, .arm "None" .none nb] => some (k, sb, nb)
          | [.arm "None" .none nb, .arm "Some" (.some k) sb] => some (k, sb, nb)
          | _ => none) with
      | .some tb, .some (k, .block sss se, .block nss ne) =>
        match uAnwReihe tabs koepfe f (uMitLokal ctx k (UParamArt.index num) (Ty.index tb.count)
            (ctx.muts.filter (fun m => !strEq m k))) sss with
        | .error err => .error err
        | .ok (sbody, ctxS) =>
          match uEndeStmt ctxS se with
          | .error err => .error err
          | .ok sEnd =>
            match uAnwReihe tabs koepfe f ctx nss with
            | .error err => .error err
            | .ok (nbody, ctxN) =>
              match uEndeStmt ctxN ne with
              | .error err => .error err
              | .ok nEnd =>
                match uAnwReihe tabs koepfe f ctx rest with
                | .error err => .error err
                | .ok (ys, cE) =>
                  .ok ([UStmt.matchBeg num o k] ++ sbody ++ sEnd ++ [UStmt.ifElse] ++ nbody ++ nEnd ++ [UStmt.blkEnd] ++ ys, cE)
      | _, _ => .error "match arms without G form"
  | f + 1, ctx, .await x ty (.variable a) pl :: rest =>
    match ctx.globs.find? (fun g => strEq g.name a) with
    | .none => .error "awaits without an atomic without G form"
    | .some gl =>
      if !gl.atomic then .error "awaits without an atomic without G form"
      else if !uNamenGleich (uNutzNamen pl) gl.nutzlast then .error "awaits a payload other than the declared one"
      else match uBinderTyp ctx "awaits" ty gl.ty with
      | .error err => .error err
      | .ok () =>
        let muts := ctx.muts.filter (fun m => !strEq m x)
        let ctx' := match gl.ty with
          | .bool => uMitLokal ctx x UParamArt.bool Ty.bool muts
          | .int lo hi => uMitLokal ctx x UParamArt.int (Ty.int lo hi) muts
          | .wert τ => uMitLokal ctx x UParamArt.wert τ muts
        match uAnwReihe tabs koepfe f ctx' rest with
        | .error err => .error err
        | .ok (xs, cE) => .ok (UStmt.awaitBind x a :: xs, cE)
  | f + 1, ctx, .swap x ty (.variable a) k :: rest =>
    match ctx.globs.find? (fun g => strEq g.name a) with
    | .none => .error ("exchange of an unknown static: " ++ a)
    | .some gl =>
      match gl.ty with
      | .int lo hi =>
        match uTauschSchwanz a k with
        | .error err => .error err
        | .ok ⟨v, zweige, sonst, pub, aw, vergleich⟩ =>
          match uBinderTyp ctx "exchange" ty gl.ty with
          | .error err => .error err
          | .ok () =>
            if !uNamenGleich (pub.map String.toList) gl.nutzlast then
              .error "exchange publishes a payload other than the declared one"
            else if (aw.map (fun ns => !gl.atomic || !uNamenGleich (ns.map String.toList) gl.nutzlast)).getD false then
              .error "exchange awaits a payload other than the declared one"
            else
            let ctxV := uMitLokal ctx v UParamArt.int (Ty.int lo hi) (ctx.muts.filter (fun m => !strEq m v))
            match uSeq (zweige.map (fun (c, e) =>
                match uBool ctxV c, uWertBody ctxV e with
                | .ok c', .ok e' => .ok (c', e')
                | .error err, _ | _, .error err => .error err)), uWertBody ctxV sonst with
            | .error err, _ | _, .error err => .error err
            | .ok zs0, .ok neu0 =>
              -- each arm reads `v` narrowed by its guard and the negated guards before it
              let zs := (List.range zs0.length).zip zs0 |>.map (fun (i, (c, e)) =>
                (c, uArmEng v lo hi (some c) ((zs0.take i).map (·.1)) e))
              let neu := uArmEng v lo hi none (zs0.map (·.1)) neu0
              -- `awaits` at an exchange: the acquiring read of `Block.awaits` (its value unused) in front
              let vor := if aw.isSome then [UStmt.awaitBind "#awaits" a] else []
              match vergleich with
              | none =>
                let ctx' := uMitLokal ctx x UParamArt.int (Ty.int lo hi) (ctx.muts.filter (fun m => !strEq m x))
                match uAnwReihe tabs koepfe f ctx' rest with
                | .error err => .error err
                | .ok (xs, cE) => .ok (vor ++ UStmt.tausch x a v zs neu :: xs, cE)
              | some p =>
                -- compare-exchange: the old value is `#alt`, the binder `x` is the success `p`
                match uBool ctxV p with
                | .error err => .error err
                | .ok pv =>
                  let ctx' := uMitLokal ctxV x UParamArt.bool Ty.bool (ctx.muts.filter (fun m => !strEq m x))
                  match uAnwReihe tabs koepfe f ctx' rest with
                  | .error err => .error err
                  | .ok (xs, cE) => .ok (vor ++ UStmt.tausch v a v zs neu :: UStmt.bindB x pv :: xs, cE)
      | _ => .error "exchange of a static that is not a number without G form"
  | f + 1, ctx, .ret v :: rest =>
    match uEnde ctx (some (.ret v)) with
    | .error err => .error err
    | .ok r =>
      match uAnwReihe tabs koepfe f ctx rest with
      | .error err => .error err
      | .ok (xs, cE) => .ok (UStmt.ret r :: xs, cE)
  | f + 1, ctx, .bindElse y t (.field a r) _ (.block ss en) :: rest =>
    match uRegOrt ctx (.field a r) with
    | none => .error "let else without G form"
    | some (.error err) => .error err
    | some (.ok rg) =>
      if t.isSome then .error "let else with a type without G form"
      else if rg.pruefung.isNone then .error "let else of a register read without a promise to check"
      else
        match uAnwReihe tabs koepfe f ctx ss with
        | .error err => .error err
        | .ok (ebody, ctxEB) =>
          match uEndeStmt ctxEB en with
          | .error err => .error err
          | .ok endS =>
            match uAnwReihe tabs koepfe f (uMitLokal ctx y rg.art rg.ty
                (ctx.muts.filter (fun m => !strEq m y))) rest with
            | .error err => .error err
            | .ok (ys, cE) => .ok ([UStmt.regReadElse y rg.dev rg.name] ++ ebody ++ endS ++ [UStmt.blkEnd] ++ ys, cE)
  | f + 1, ctx, .bindElse y t (.call c args) e (.block ss en) :: rest =>
    if t.isSome then .error "let else with a type without G form"
    else
      match uRuf ctx tabs koepfe c args with
      | .error err => .error err
      | .ok (callee, xs) =>
        match callee.kanal with
        | .none => .error "let else of a call without a reason channel"
        | .some (num, cnt) =>
          if callee.ext then
            match callee.res with
            | .none => .error "let else of a call without a value"
            | .some r =>
              match uAnwReihe tabs koepfe f (uMitLokal ctx e (UParamArt.why num) (Ty.why cnt)
                  (ctx.muts.filter (fun m => !strEq m e))) ss with
              | .error err => .error err
              | .ok (ebody, ctxEB) =>
                match uEndeStmt ctxEB en with
                | .error err => .error err
                | .ok endS =>
                  match uAnwReihe tabs koepfe f (uMitLokal ctx y UParamArt.int (Ty.int r.1 r.2)
                      (ctx.muts.filter (fun m => !strEq m y))) rest with
                  | .error err => .error err
                  | .ok (ys, cE) => .ok ([UStmt.bindAxElse y c xs e] ++ ebody ++ endS ++ [UStmt.blkEnd] ++ ys, cE)
          else
            match uWertArt callee with
            | .none => .error "let else of a call without a value"
            | .some (k, ty) =>
              match uAnwReihe tabs koepfe f (uMitLokal ctx e (UParamArt.why num) (Ty.why cnt)
                  (ctx.muts.filter (fun m => !strEq m e))) ss with
              | .error err => .error err
              | .ok (ebody, ctxEB) =>
                match uEndeStmt ctxEB en with
                | .error err => .error err
                | .ok endS =>
                  match uAnwReihe tabs koepfe f (uMitLokal ctx y k ty (ctx.muts.filter (fun m => !strEq m y))) rest with
                  | .error err => .error err
                  | .ok (ys, cE) => .ok ([UStmt.bindElse y c xs e] ++ ebody ++ endS ++ [UStmt.blkEnd] ++ ys, cE)
  | f + 1, ctx, .bindElse .. :: _ => .error "let else without G form"
  | f + 1, ctx, .alloc mu x t an v (.some (.block ss e)) :: rest =>
    if mu || t.isSome then .error "alloc binding without G form"
    else
      match ctx.tabs.findIdx? (fun y => y.arena && strEq y.name an) with
      | .none => .error ("arena unknown: " ++ an)
      | .some num =>
        match ctx.tabs[num]? with
        | .none => .error "arena unknown"
        | .some tb =>
          match uWertBody ctx v with
          | .error err => .error err
          | .ok sv =>
            match uAnwReihe tabs koepfe f ctx ss with
            | .error err => .error err
            | .ok (body, ctxB) =>
              match (match e with
                  | .none => .error "alloc else falls through"
                  | .some _ => uEndeStmt ctxB e : Except String (List UStmt)) with
              | .error err => .error err
              | .ok endS =>
                match uAnwReihe tabs koepfe f (uMitLokal ctx x (UParamArt.index num) (Ty.index tb.count)
                    (ctx.muts.filter (fun m => !strEq m x))) rest with
                | .error err => .error err
                | .ok (xs, cE) => .ok ([UStmt.allocBeg x an sv] ++ body ++ endS ++ [UStmt.blkEnd] ++ xs, cE)
  | f + 1, ctx, .alloc .. :: _ => .error "alloc without else without G form"
  | f + 1, ctx, .allocVon mu x t tn :: rest =>
    -- `let r = alloc T;` is the call of `T`'s provider (`Block.alloc`, Zucker.lean): `let r = p();`
    match ctx.tabs.find? (fun y => strEq y.name tn) with
    | .some { von := .some p, .. } => uAnwReihe tabs koepfe f ctx (.bind mu x t (.call p []) :: rest)
    | _ => .error ("alloc of a table without provider: " ++ tn)
  | f + 1, ctx, .retry h (.block ss e) :: rest =>
    match uRetryKopf ctx h with
    | .error err => .error err
    | .ok (lab, cnt, bis, ueb) =>
      match uAnwReihe tabs koepfe f { ctx with loops := lab :: ctx.loops } ss with
      | .error err => .error err
      | .ok (body, ctxB) =>
        match uEndeStmt ctxB e with
        | .error err => .error err
        | .ok endS =>
          match uRuf ctx tabs koepfe ueb [] with
          | .error err => .error err
          | .ok (callee, xs) =>
            if !callee.ext then .error "on_exceeded names no foreign body"
            else
              match uAnwReihe tabs koepfe f ctx rest with
              | .error err => .error err
              | .ok (ys, cE) =>
                .ok ([UStmt.retryBeg cnt bis] ++ body ++ endS ++ [UStmt.ifElse, UStmt.axCall ueb xs, UStmt.blkEnd] ++ ys, cE)
  | f + 1, ctx, .loop h (.block ss e) :: rest =>
    match uForeverKopf ctx h with
    | .error err => .error err
    | .ok (lab, k) =>
      match uAnwReihe tabs koepfe f { ctx with loops := lab :: ctx.loops } ss with
      | .error err => .error err
      | .ok (body, ctxB) =>
        match uEndeStmt ctxB e with
        | .error err => .error err
        | .ok endS =>
          match uAnwReihe tabs koepfe f ctx rest with
          | .error err => .error err
          | .ok (ys, cE) => .ok ([UStmt.foreverBeg k] ++ body ++ endS ++ [UStmt.blkEnd] ++ ys, cE)
  | f + 1, ctx, .trim (.variable x) t (.block ss e) :: rest =>
    match uNarrowKopf ctx x t with
    | .error err => .error err
    | .ok (lo, hi, ctx') =>
      match uAnwReihe tabs koepfe f ctx ss with
      | .error err => .error err
      | .ok (body, ctxB) =>
        match (match e with
            | .none => .error "narrow else falls through"
            | .some _ => uEndeStmt ctxB e : Except String (List UStmt)) with
        | .error err => .error err
        | .ok endS =>
          match uAnwReihe tabs koepfe f ctx' rest with
          | .error err => .error err
          | .ok (xs, cE) => .ok ([UStmt.narrowBeg x lo hi] ++ body ++ endS ++ [UStmt.blkEnd] ++ xs, cE)
  | f + 1, ctx, .locks g lk (.block ss .none) :: rest =>
    if g then .error "shared lock without G form"
    else
      match lk with
      | .variable l =>
        match ctx.locks.find? (fun x => strEq x.name l) with
        | .none => .error ("lock unknown: " ++ l)
        | .some _ =>
          match uAnwReihe tabs koepfe f { ctx with held := l :: ctx.held } ss with
          | .error e => .error e
          | .ok (body, _) =>
            match uAnwReihe tabs koepfe f ctx rest with
            | .error e => .error e
            | .ok (xs, cE) => .ok ([UStmt.lockBeg l] ++ body ++ [UStmt.blkEnd] ++ xs, cE)
      | _ => .error "lock expression without G form"
  | f + 1, ctx, .cond c (.block ss e) ei els :: rest =>
    match uBool ctx c with
    | .error err => .error err
    | .ok cv =>
      match uAnwReihe tabs koepfe f ctx ss with
      | .error err => .error err
      | .ok (body, ctxB) =>
        match uEndeStmt ctxB e with
        | .error err => .error err
        | .ok endS =>
          let ifElse : Option SAnw :=
            match ei with
            | .elsif c2 b2 :: ei' => some (.block [.cond c2 b2 ei' els] .none)
            | _ => els
          match (match ifElse with
              | .none => .ok []
              | .some (.block ss2 e2) =>
                match uAnwReihe tabs koepfe f ctx ss2 with
                | .error err => .error err
                | .ok (b2, ctx2) =>
                  match uEndeStmt ctx2 e2 with
                  | .error err => .error err
                  | .ok end2 => .ok (b2 ++ end2)
              | .some _ => .error "else without block" : Except String (List UStmt)) with
          | .error err => .error err
          | .ok elseS =>
            match uAnwReihe tabs koepfe f ctx rest with
            | .error err => .error err
            | .ok (xs, cE) =>
              let kopf := if rest.isEmpty && uEndetS 64 (.cond c (.block ss e) ei els) then UStmt.ifEnde cv
                else UStmt.ifBeg cv
              .ok ([kopf] ++ body ++ endS ++ [UStmt.ifElse] ++ elseS ++ [UStmt.blkEnd] ++ xs, cE)
  | f + 1, ctx, .each bnd o k s m _ inv (.block ss e) :: rest =>
    match uSchleifenKopf ctx bnd o k s m inv with
    | .error err => .error err
    | .ok (tab, inv, ctxS) =>
      match uAnwReihe tabs koepfe f ctxS ss with
      | .error err => .error err
      | .ok (body, ctxB) =>
        match uEndeStmt ctxB e with
        | .error err => .error err
        | .ok endS =>
          match uAnwReihe tabs koepfe f ctx rest with
          | .error err => .error err
          | .ok (xs, cE) =>
            .ok ([UStmt.loopBeg bnd tab inv] ++ body ++ endS ++ [UStmt.blkEnd] ++ xs, cE)
  | f + 1, ctx, s :: rest =>
    match uAnw1 ctx tabs koepfe s with
    | .error e => .error e
    | .ok st =>
      match uAnwReihe tabs koepfe f ctx rest with
      | .error e => .error e
      | .ok (xs, cE) => .ok (st :: xs, cE)

/-- The substitution of the parameters of a `spec fn` by the arguments of a use. A quantifier binder hides the
    parameter of its name in its body (the last operand). Structural in a fuel (an expression is far shallower). -/
def sErsetze (σ : List (String × SExpr)) : Nat → SExpr → SExpr
  | 0, e => e
  | n + 1, e =>
    match e with
    | .variable x => match σ.find? (fun p => strEq p.1 x) with
      | some p => p.2
      | none => e
    | .field a f => .field (sErsetze σ n a) f
    | .index a i => .index (sErsetze σ n a) (sErsetze σ n i)
    | .arrow a f => .arrow (sErsetze σ n a) f
    | .un o a => .un o (sErsetze σ n a)
    | .bin o a b => .bin o (sErsetze σ n a) (sErsetze σ n b)
    | .call f as => .call f (as.map (sErsetze σ n))
    | .built f as => .built f (as.map (sErsetze σ n))
    | .old a => .old (sErsetze σ n a)
    | .ext k ns xs =>
      if k == XKind.all || k == XKind.any || k == XKind.count then
        let σ' := σ.filter (fun p => !(ns.head?.any (strEq p.1 ·)))
        .ext k ns ((xs.dropLast.map (sErsetze σ n)) ++ (xs.getLast?.map (sErsetze σ' n)).toList)
      else .ext k ns (xs.map (sErsetze σ n))
    | e => e

/-- Every use `g(a…)` of a `spec fn` `g` replaced by its predicate over the arguments (SUGAR, `M130`), also inside
    the predicates it brings. Structural in a fuel. -/
def uSpecEin (specs : List (String × List String × SExpr)) : Nat → SExpr → SExpr
  | 0, e => e
  | n + 1, e =>
    match e with
    | .call f as =>
      let as' := as.map (uSpecEin specs n)
      match specs.find? (fun p => strEq p.1 f) with
      | some (_, ps, body) =>
        if ps.length == as'.length then uSpecEin specs n (sErsetze (ps.zip as') 1000 body) else .call f as'
      | none => .call f as'
    | .field a f => .field (uSpecEin specs n a) f
    | .index a i => .index (uSpecEin specs n a) (uSpecEin specs n i)
    | .arrow a f => .arrow (uSpecEin specs n a) f
    | .un o a => .un o (uSpecEin specs n a)
    | .bin o a b => .bin o (uSpecEin specs n a) (uSpecEin specs n b)
    | .built f as => .built f (as.map (uSpecEin specs n))
    | .old a => .old (uSpecEin specs n a)
    | .ext k ns xs => .ext k ns (xs.map (uSpecEin specs n))
    | e => e

/-- The contract clauses with every `spec fn` inlined: `refines g` is `ensures g(params)` (`M131`/`M132`),
    `maintains` documents (the owed invariants are derived from `effects`), `by induction over` names a scheme
    and carries no term. Without `spec fn`s the clauses stay as they are. -/
def uSpecKlauseln (ctx : UCtx) (params : List String) (ks : List SKlausel) : Except String (List SKlausel) :=
  let ein := uSpecEin ctx.specs 1000
  ks.foldr (fun k acc => match acc with
    | .error e => .error e
    | .ok r =>
      match k with
      | .needs e => .ok (.needs (ein e) :: r)
      | .gives e => .ok (.gives (ein e) :: r)
      | .refs [g] =>
        match ctx.specs.find? (fun p => strEq p.1 g) with
        | some (_, ps, _) =>
          if ps.length == params.length then .ok (.gives (ein (.call g (params.map .variable))) :: r)
          else .error "refines a spec fn of another arity"
        | none => .error ("refines unknown spec fn " ++ g)
      | .refs _ => .error "refines without one spec fn"
      | .keeps _ | .induc _ => .ok r
      | k => .ok (k :: r)) (.ok [])

/-- Pass two: contracts and body of one function. -/
def elabFn (ctx : UCtx) (koepfe : List UFnKopf) (klauseln0 : List SKlausel)
    (koerper : SAnw) : Except String (List UEns × List UEns × List UStmt × URet) :=
  match (if ctx.specs.isEmpty then .ok klauseln0 else uSpecKlauseln ctx ctx.names klauseln0) with
  | .error e => .error e
  | .ok klauseln =>
  match uSeq ((klauseln.filterMap (fun
    | .gives e => some (uSichert ctx e)
    | _ => none))) with
  | .error e => .error e
  | .ok gives =>
    match uSeq ((klauseln.filterMap (fun
      | .needs (.call "Held" _) => none
      | .needs e => some (uBool ctx e)
      | _ => none))) with
    | .error e => .error e
    | .ok needs =>
    match koerper with
    | .block ss ende =>
      match uAnwReihe ctx.tabs koepfe 1000000 ctx ss with
      | .error e => .error e
      | .ok (body, ctxE) =>
        match uEnde ctxE ende with
        | .error e =>
          if ende.isNone && (match ss.getLast? with | some s => uEndetTief 64 s | none => false) then
            .ok (gives, needs, body, .keins)
          else .error e
        | .ok r => .ok (gives, needs, body, r)
    | _ => .error "fn body without G form"

/-- The context of a function from its head. -/
def uCtxVon (alias : List (String × (Int × Int))) (lits : List (String × Int))
    (tabs : List UTab) (locks : List ULock) (globs : List UGlob) (kopf : UFnKopf)
    (fname : String) (annahmen : List String := []) (whys : List UWhy := []) (sums : List USum := [])
    (regs : List UReg := []) (zustaende : List UZustand := [])
    (specs : List (String × List String × SExpr) := []) (arrKonst : List (String × USide) := []) : UCtx :=
  { names := kopf.names, kinds := kopf.kinds,
    types := kopf.types, tabs := tabs, locks := locks,
    held := kopf.held, res := kopf.res, resBool := kopf.resBool, resOpt := kopf.resOpt,
    fname, bits := kopf.bits, alias, lits, globs, annahmen, whys, kanal := kopf.kanal, sums,
    resSum := kopf.resSum, resWhy := kopf.resWhy, resTy := kopf.resTy, regs, griffe := kopf.griffe.map (·.2),
    zustaende, specs, arrKonst }

/-- One whole function: head (pass one) plus contracts and
    body (pass two). -/
def elabUFunktion (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (koepfe : List UFnKopf) (sig : FnSig)
    (koerper : SAnw) (annahmen : List String := []) (whys : List UWhy := []) (sums : List USum := [])
    (devs : List String := []) (regs : List UReg := []) (zustaende : List UZustand := [])
    (zeiger : List String := []) (zb : Nat := 0) (specs : List (String × List String × SExpr) := [])
    (arrKonst : List (String × USide) := []) :
    Except String UFn :=
  match elabKopf consts alias tabs locks globs whys sums sig devs zeiger zb with
  | .error e => .error e
  | .ok (kopf, schreibt) =>
    let ctx := { uCtxVon alias consts tabs locks globs kopf sig.name annahmen whys sums regs zustaende specs arrKonst with
                 zeiger := zeiger, zeigerBasis := zb }
    match elabFn ctx koepfe sig.klauseln koerper with
    | .error e => .error e
    | .ok (gives, needs, body, r) =>
      .ok { name := sig.name,
            params := kopf.names.zip kopf.types,
            kinds := kopf.kinds,
            res := kopf.res, resBool := kopf.resBool, resOpt := kopf.resOpt, resSum := kopf.resSum,
            resWhy := kopf.resWhy, resTy := kopf.resTy,
            gruende := (kopf.kanal.map (·.2)).getD 0, held := kopf.held,
            puts := schreibt, gputs := kopf.gputs, gives, needs, body, ret := r }

/-- The payload of an `atomic` item: statics named bare (a table payload, `T.slots`, has no form: `D.nutzlast`
    lists statics). -/
def uNutzItem : List SExpr → Except String (List String)
  | [] => .ok []
  | .variable g :: rest =>
    match uNutzItem rest with
    | .error e => .error e
    | .ok gs => .ok (g :: gs)
  | _ :: _ => .error "payload of a table without G form"

mutual
/-- The initial value of a static of a tagged type: a payload-free case, or a case with a numeral payload. -/
def uSumKonst (consts : List (String × Int)) (sm : USum) : SKonstWert → Except String UKonst
  | .one (.variable c) =>
    match sm.cases.findIdx? (fun x => strEq x.1 c) with
    | some i => .ok (.fall i .null)
    | none => .error ("case unknown: " ++ c)
  | .one (.call c [e]) =>
    match sm.cases.findIdx? (fun x => strEq x.1 c), (sm.cases.find? (fun x => strEq x.1 c)).bind (·.2) with
    | some i, some (lo, hi) =>
      match uKonstWert lo hi [] consts 64 e with
      | some z => .ok (.fall i (.zahl z))
      | none => .error "static initialiser without G form"
    | _, _ => .error "static initialiser without G form"
  | _ => .error "static initialiser without G form"

/-- The statics of a tagged type with their type, read once the `tagged type`s are known. -/
def uSumGlobs (consts : List (String × Int)) (sums : List USum) (ms : List SItemTief) :
    List UGlob → Except String (List UGlob)
  | [] => .ok []
  | g :: rest =>
    match uSumGlobs consts sums ms rest, g.sumName with
    | .error e, _ => .error e
    | .ok gs, none => .ok (g :: gs)
    | .ok gs, some a =>
      match sums.findIdx? (fun sm => strEq sm.name a), sums.find? (fun sm => strEq sm.name a) with
      | some k, some sm =>
        match ms.findSome? (fun m => match m with | .globT _ n _ v .. => if strEq n g.name then some v else none | _ => none) with
        | some v =>
          match uSumKonst consts sm v with
          | .ok kv => .ok ({ g with ty := .wert (.sum sm.spec), initK := kv, sumNum := some k } :: gs)
          | .error e => .error e
        | none => .error ("static unknown: " ++ g.name)
      | _, _ => .error ("type unknown: " ++ a)

/-- The tables with their fields of a tagged type typed (`werte`) and numbered (`sumFelder`). -/
def uSumTabs (sums : List USum) : List UTab → Except String (List UTab)
  | [] => .ok []
  | t :: rest =>
    match uSumTabs sums rest,
        uSeq (t.sumNamen.map fun (f, a) =>
          match sums.findIdx? (fun sm => strEq sm.name a), sums.find? (fun sm => strEq sm.name a) with
          | some k, some sm => .ok (f, k, sm.spec)
          | _, _ => .error ("type unknown: " ++ a)) with
    | .ok ts, .ok fs =>
      .ok ({ t with werte := t.werte ++ fs.map (fun (f, _, sp) => (f, Ty.sum sp)),
                    sumFelder := fs.map (fun (f, k, _) => (f, k)) } :: ts)
    | .error e, _ | _, .error e => .error e

/-- The range of a column: an `index into T` field reads `0 .. count T - 1`. -/
def uIdxSpalte (tabs : List UTab) (t : UTab) (c : String × (Int × Int)) : String × (Int × Int) :=
  match t.idxNamen.find? (fun p => strEq p.1 c.1) with
  | some (_, tn) =>
    match tabs.find? (fun x => strEq x.name tn) with
    | some x => (c.1, (0, x.count - 1))
    | none => c
  | none => c

/-- The `index into T` fields with their range `0 .. count T - 1`. -/
def uIdxTabs (tabs : List UTab) : List UTab :=
  tabs.map fun t => { t with cols := t.cols.map (uIdxSpalte tabs t) }

/-- The option statics with the number and count of their table. -/
def uOptGlobs (tabs : List UTab) : List UGlob → Except String (List UGlob)
  | [] => .ok []
  | g :: rest =>
    match uOptGlobs tabs rest, g.optName with
    | .error e, _ => .error e
    | .ok gs, none => .ok (g :: gs)
    | .ok gs, some tn =>
      match uTabNr tabs tn with
      | .ok (num, c) => .ok ({ g with ty := .wert (.opt c), optNum := some num } :: gs)
      | .error e => .error e

/-- The initial value of an aggregate static: `0` is zero memory, a numeral or constant a number, a string literal
    its bytes, a row literal its elements. -/
def uKonst (consts : List (String × Int)) : SKonstWert → Except String UKonst
  | .one (.lit 0) => .ok .null
  | .one (.call "None" []) => .ok .null
  | .one (.lit k) => .ok (.zahl (Int.ofNat k))
  | .one (.un "-" (.lit k)) => .ok (.zahl (-(Int.ofNat k)))
  | .one .tru => .ok (.wahr true)
  | .one .fls => .ok (.wahr false)
  | .one (.variable c) =>
    match uSuch "const" consts c with
    | .error e => .error e
    | .ok z => .ok (.zahl z)
  | .one (.ext .text [t] []) => .ok (.text (t.toUTF8.toList.map (fun b => Int.ofNat b.toNat)))
  | .one _ => .error "static initialiser without G form"
  | .rows ks => uKonstReihe consts ks
def uKonstReihe (consts : List (String × Int)) : List SKonstWert → Except String UKonst
  | [] => .ok .nil
  | k :: ks =>
    match uKonst consts k, uKonstReihe consts ks with
    | .ok a, .ok r => .ok (.cons a r)
    | .error e, _ | _, .error e => .error e
end

/-- The statics of the unit: ONE value each, an integer range or `bool`, with a numeral (or `true`/`false`)
    as the initial value; a placement, an alignment or a `shared` word has no `Glob` form. -/
def uGlobs (consts : List (String × Int)) (alias : List (String × (Int × Int))) :
    List SItemTief → Except String (List UGlob)
  | [] => .ok []
  | .globT m n t v al sec sh :: rest =>
    if al.isSome || sec.isSome then .error "static placement without G form"
    else
      match (match t with
          | .atom "bool" =>
            match v with
            | .one .tru => .ok (GTy.bool, (1 : Int))
            | .one .fls => .ok (GTy.bool, (0 : Int))
            | _ => .error "static initialiser without G form"
          | .array _ _ | .str _ =>
            match uTyp alias [] t with
            | .error e => .error e
            | .ok τ => .ok (GTy.wert τ, (0 : Int))
          -- the count of `T` is read with the tables (`uOptGlobs`)
          | .index true _ => .ok (GTy.wert (.opt 0), (0 : Int))
          -- a name that is no integer type may be a tagged type, read with the types (`uSumGlobs`)
          | .atom a =>
            match uErgBereich alias (.atom a) with
            | .error _ => .ok (GTy.wert (.sum []), (0 : Int))
            | .ok (lo, hi) =>
              match (match v with
                  | .one (.lit k) => .ok (Int.ofNat k)
                  | .one (.un "-" (.lit k)) => .ok (-(Int.ofNat k))
                  | .one (.variable c) => uSuch "const" consts c
                  | _ => .error "static initialiser without G form" : Except String Int) with
              | .error e => .error e
              | .ok z =>
                if lo ≤ z ∧ z ≤ hi then .ok (GTy.int lo hi, z)
                else .error "static initialiser outside its range"
          | _ =>
            match uErgBereich alias t with
            | .error e => .error e
            | .ok (lo, hi) =>
              match (match v with
                  | .one (.lit k) => .ok (Int.ofNat k)
                  | .one (.un "-" (.lit k)) => .ok (-(Int.ofNat k))
                  | .one (.variable c) => uSuch "const" consts c
                  | _ => .error "static initialiser without G form" : Except String Int) with
              | .error e => .error e
              | .ok z =>
                if lo ≤ z ∧ z ≤ hi then .ok (GTy.int lo hi, z)
                else .error "static initialiser outside its range" : Except String (GTy × Int)) with
      | .error e => .error e
      | .ok (ty, z) =>
        match (match ty, t with
            | .wert (.sum _), _ => .ok .null
            | .wert _, _ => uKonst consts v
            | _, _ => .ok .null : Except String UKonst) with
        | .error e => .error e
        | .ok k =>
        match uGlobs consts alias rest with
        | .error e => .error e
        | .ok gs => .ok ({ name := n, ty, init := z, initK := k, var := m, shared := sh,
                           optName := match t with | .index true tn => some tn | _ => none,
                           sumName := match ty, t with | .wert (.sum _), .atom a => some a | _, _ => none } :: gs)
  | .atomT n t pub _ obs :: rest =>
    if obs.isSome then .error "atomic observed by a device without G form"
    else
      match uNutzItem (pub.getD []) with
      | .error e => .error e
      | .ok nl =>
        match (match t with
            | .atom "bool" => .ok GTy.bool
            | _ =>
              match uErgBereich alias t with
              | .error e => .error e
              | .ok (lo, hi) =>
                if lo ≤ 0 ∧ 0 ≤ hi then .ok (GTy.int lo hi)
                else .error "atomic starts at zero outside its range" : Except String GTy) with
        | .error e => .error e
        | .ok ty =>
          match uGlobs consts alias rest with
          | .error e => .error e
          | .ok gs => .ok ({ name := n, ty, init := 0, var := true, atomic := true, shared := true,
                             nutzlast := nl } :: gs)
  | _ :: rest => uGlobs consts alias rest

/-- The arenas of a unit as the PAIR the specification names (`ArenaZucker`): a table of `hi` slots with the one
    field `wert`, and the counter static `A#used` over `0 .. hi` starting at zero. A dynamic ceiling and a
    placement have no form here. -/
def uArenen (consts : List (String × Int)) (alias : List (String × (Int × Int))) :
    List SItemTief → Except String (List UTab × List UGlob)
  | [] => .ok ([], [])
  | .arenaT n _ hi mx t pb :: rest =>
    match mx, pb with
    | .some _, _ => .error "arena with a dynamic ceiling without G form"
    | _, .some _ => .error "arena placement without G form"
    | .none, .none =>
      match uAnzahl consts hi with
      | .error e => .error e
      | .ok h =>
        match uFeldTyp alias t with
        | .error e => .error e
        | .ok r =>
          match uArenen consts alias rest with
          | .error e => .error e
          | .ok (ts, gs) =>
            if 0 < h then
              .ok ({ name := n, count := h, cols := [("wert", r)], arena := true } :: ts,
                   { name := n ++ "#used", ty := GTy.int 0 h, init := 0, var := true } :: gs)
            else .error "arena of no slots"
  | _ :: rest => uArenen consts alias rest

/-- Items outside the fragment: everything but constants,
    type aliases, statics, tables, locks and functions is an explicit
    error (the refused rows of `collect`). -/
def uRestFehler : List SItemTief → Except String Unit
  | [] => .ok ()
  | .constT _ _ _ :: rest => uRestFehler rest
  | .typeT _ _ _ _ _ :: rest => uRestFehler rest
  | .tableT _ _ _ _ _ _ _ :: rest => uRestFehler rest
  | .lockT _ _ _ _ _ _ _ :: rest => uRestFehler rest
  | .globT .. :: rest => uRestFehler rest
  | .atomT .. :: rest => uRestFehler rest
  | .arenaT .. :: rest => uRestFehler rest
  | .protoT .. :: rest => uRestFehler rest
  | .assumT .. :: rest => uRestFehler rest
  | .whyT .. :: rest => uRestFehler rest
  | .callT .. :: rest => uRestFehler rest
  | .varT .. :: rest => uRestFehler rest
  | .goalT .. :: rest => uRestFehler rest
  | .fnT _ _ :: rest => uRestFehler rest
  | .entryT _ :: rest => uRestFehler rest
  | .concT _ :: rest => uRestFehler rest
  | .devT .. :: rest => uRestFehler rest
  | .groupT .. :: rest => uRestFehler rest
  | .stateT .. :: rest => uRestFehler rest
  | .specT .. :: rest => uRestFehler rest
  | .asmT .. :: rest => uRestFehler rest
  -- `axiom f(..) effects { .. } falsifier p;`: a foreign body under a named hardware assumption; a `requires` has no
  -- G form yet (the model's foreign bodies carry no caller duty)
  | .axiomT _ _ _ .none _ _ :: rest => uRestFehler rest
  | _ :: _ => .error "item without G form"

/-- A start names one parameterless function of the unit (`check_starts` of `lean_g.rs`). -/
def uStart (fns : List UFn) (quelle d : String) : Except String String :=
  match fns.find? (fun f => strEq f.name d) with
  | .some f =>
    if f.params.isEmpty then .ok d
    else .error (quelle ++ " names a function with parameters: no start-argument form: " ++ d)
  | .none => .error (quelle ++ " names an unknown function: " ++ d)

/-- A start argument is a value of its parameter's type: a literal in the range, `true`/`false`, `None`. -/
def uStartArg (tabs : List UTab) : Ty → SExpr → Bool
  | .int lo hi, .lit n => decide (lo ≤ (n : Int) ∧ (n : Int) ≤ hi)
  | .int lo hi, .un "-" (.lit n) => decide (lo ≤ -(n : Int) ∧ -(n : Int) ≤ hi)
  | .bool, .tru => true
  | .bool, .fls => true
  | .opt _, .call "None" [] => true
  -- `&T` for a `ptr<…> T` parameter (`Expr.ptrOf`): the one pointer to the carrier the type names
  | .ptr n _, .fnref t => match tabs[n]? with
    | .some tb => strEq tb.name t
    | .none => false
  | _, _ => false

/-- A `concurrent` member: a function of the unit, started with one value per parameter
    (`concurrent { m::f(a, b) }`, the model's start with its arguments). -/
def uStartMit (tabs : List UTab) (fns : List UFn) (d : String) (args : List SExpr) : Except String String :=
  match fns.find? (fun f => strEq f.name d) with
  | .some f =>
    if f.params.length != args.length then
      .error ("concurrent member with " ++ toString args.length ++ " arguments for " ++
        toString f.params.length ++ " parameters: " ++ d)
    else if (f.params.zip args).all (fun (p, a) => uStartArg tabs p.2 a) then .ok d
    else .error ("concurrent member with an argument outside its parameter's type: " ++ d)
  | .none => .error ("concurrent member names an unknown function: " ++ d)

/-- The roots of the `concurrent` items, in order (their members come first, as in `check_starts`). -/
def uNebenWurzeln (tabs : List UTab) (fns : List UFn) : List SItemTief → Except String (List String)
  | [] => .ok []
  | .concT ps :: rest => do
    let here ← uSeq (ps.map fun (p, args) => match p.getLast? with
      | .some d => uStartMit tabs fns d args
      | .none => .error "empty path in concurrent")
    let more ← uNebenWurzeln tabs fns rest
    pure (here ++ more)
  | _ :: rest => uNebenWurzeln tabs fns rest

/-- The dispatch roots of the `entry` items: ONE dispatch target that names a parameterless function of
    the unit. Everything else about the entry (vector, registers, stack) is the
    hardware side and stays with the checker. -/
def uEingangsWurzeln (fns : List UFn) : List SItemTief → Except String (List String)
  | [] => .ok []
  | .entryT e :: rest =>
    match e.dispatch.getLast? with
    | .some d => do
      let w ← uStart fns "dispatch" d
      let ws ← uEingangsWurzeln fns rest
      pure (w :: ws)
    | .none => .error "entry without a dispatch: no G form"
  | _ :: rest => uEingangsWurzeln fns rest

/-- The handlers: the dispatch targets of the entries that carry a `via` word. -/
def uHandler : List SItemTief → List String
  | [] => []
  | .entryT e :: rest =>
    match e.via, e.dispatch.getLast? with
    | .some _, .some d => d :: uHandler rest
    | _, _ => uHandler rest
  | _ :: rest => uHandler rest

/-- The thread roots: `concurrent` members, then entry dispatch roots. -/
def uWurzeln (tabs : List UTab) (fns : List UFn) (ms : List SItemTief) : Except String (List String) := do
  let a ← uNebenWurzeln tabs fns ms
  let b ← uEingangsWurzeln fns ms
  pure (a ++ b)

/-- The clauses an `extern fn` may carry: `effects { pure | diverges | reads .. }` and `costs`; a `requires`,
    an `ensures` or a write has no form (`D.Ax` carries no contract here). -/
def uAxKlauseln (kopf : UFnKopf) (tabs : List UTab) (globs : List UGlob) :
    List SKlausel → Except String UFnKopf
  | [] => .ok kopf
  | .effs es :: rest =>
    if es.all (fun e => match e with | .pure => true | .loops => true | .reads _ => true | .writes _ => true | _ => false) then
      match uEffekteAux kopf tabs [] globs es with
      | .error e => .error e
      | .ok eff =>
        uAxKlauseln { kopf with puts := uEindeutig (kopf.puts ++ eff.puts),
                                 gputs := uEindeutig (kopf.gputs ++ eff.gputs) } tabs globs rest
    else .error "foreign fn effect without G form"
  | .cost _ :: rest => uAxKlauseln kopf tabs globs rest
  | .arch _ :: rest => uAxKlauseln kopf tabs globs rest
  -- `deadline <= n ops arch X falsifier p`: a named hardware outcome outside the goal (`Spec.lean`, NOT CLAIMED:
  -- time bounds), the same as at an implemented function
  | .limit _ :: rest => uAxKlauseln kopf tabs globs rest
  | _ :: _ => .error "foreign fn clause without G form"

/-- The head of an `extern fn`: a foreign body, `D.Ax` -- its parameters and its answer. -/
def uAxKopf (alias : List (String × (Int × Int))) (tabs : List UTab) (whys : List UWhy)
    (name : String) (params : List (String × STyp)) (res : Option STyp) (fehler : Option String) :
    Except String UFnKopf :=
  match uSeq (params.map (uParam alias tabs [] whys)) with
  | .error e => .error e
  | .ok ps =>
    match (match fehler with
        | .none => .ok none
        | .some r =>
          match whys.findIdx? (fun (w : UWhy) => strEq w.name r) with
          | .none => .error ("reason unknown: " ++ r)
          | .some k =>
            match whys[k]? with
            | .some w => if w.cases.isEmpty then .error "reason without cases" else .ok (some (k, w.cases.length))
            | .none => .error ("reason unknown: " ++ r) : Except String (Option (Nat × Nat))) with
    | .error e => .error e
    | .ok kn =>
      let base : UFnKopf :=
        { name, names := ps.map (·.1), kinds := ps.map (·.2.2), types := ps.map (·.2.1), res := .none,
          bits := params.map (fun p => uParamBreite p.2), held := [], ext := true, kanal := kn }
      match res with
      | .none => if kn.isSome then .error "foreign fn with a reason channel and no answer without G form" else .ok base
      | .some (.atom "never") => .ok { base with resNever := true }
      | .some (.atom "bool") => if kn.isSome then .error "fallible foreign fn with a non-number answer without G form" else .ok { base with resBool := true }
      | .some (.index false tn) =>
        match tabs.findIdx? (fun (y : UTab) => strEq y.name tn && y.von.isSome) with
        | .some num => if kn.isSome then .error "fallible provider without G form" else .ok { base with resRef := some num }
        | .none => .error "foreign answer `index into` a table that is not open without G form"
      | .some t =>
        match uErgBereich alias t with
        | .error e => .error e
        | .ok r => .ok { base with res := .some r }

/-- The head of an `extern fn`: a foreign body, `D.Ax` -- its parameters and its answer. -/
def elabAxKopf (alias : List (String × (Int × Int))) (tabs : List UTab) (whys : List UWhy) (globs : List UGlob)
    (asm : Bool) : FnSig → Except String UFnKopf
  | { art, name, params, res, fehler, klauseln } =>
    -- `extern`, `raw`, `prim` and `= asm`: a foreign body (SYNTAX.md); a body-less `divergent fn` is one whose
    -- answer is `never`
    if !(asm || strEq art "extern" || strEq art "raw" || strEq art "prim" || strEq art "divergent") then
      .error "foreign fn without G form"
    else if strEq art "divergent" && res.isSome then .error "divergent fn with a result without G form"
    else
      match uAxKopf alias tabs whys name params (if strEq art "divergent" then some (.atom "never") else res) fehler with
      | .error e => .error e
      | .ok kopf => uAxKlauseln kopf tabs globs klauseln

/-- The head of a `syscall` gate (a foreign body too): the ABI half (`abi`, `number`, the registers) is the stub's,
    a precondition, a postcondition or a write has no form. -/
def elabGateKopf (alias : List (String × (Int × Int))) (tabs : List UTab) (whys : List UWhy) (sc : SSyscall) :
    Except String UFnKopf :=
  if !(sc.gate.pre.isEmpty && sc.gate.post.isEmpty) then .error "foreign fn clause without G form"
  else if !(sc.gate.uses.all (fun e => match e with | .pure => true | .loops => true | .reads _ => true | _ => false))
  then .error "foreign fn effect without G form"
  else uAxKopf alias tabs whys sc.name sc.params sc.res sc.fail

/-- The roots of the `start { .. };` statements of a body, in order (`fuel` bounds the nesting). -/
def uStartNamen : Nat → SAnw → List String
  | 0, _ => []
  | _ + 1, .start ns => ns
  | f + 1, .block ss _ => ss.flatMap (uStartNamen f)
  | f + 1, .cond _ b ei els => uStartNamen f b ++ ei.flatMap (uStartNamen f) ++ (els.map (uStartNamen f)).getD []
  | f + 1, .elsif _ b => uStartNamen f b
  | f + 1, .each _ _ _ _ _ _ _ b => uStartNamen f b
  | f + 1, .retry _ b => uStartNamen f b
  | f + 1, .loop _ b => uStartNamen f b
  | f + 1, .locks _ _ b => uStartNamen f b
  | f + 1, .trim _ _ b => uStartNamen f b
  | f + 1, .cases _ arms => arms.flatMap (uStartNamen f)
  | f + 1, .arm _ _ b => uStartNamen f b
  | _, _ => []

/-- Each root once, in order. -/
def uOhneDoppelte (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.any (fun y => strEq y x) then acc else acc ++ [x]) []

/-- The numeral a token list is. -/
def uZahlTok : List Token → Option Int
  | [.num n] => some (Int.ofNat n)
  | [.zeichen "-", .num n] => some (-(Int.ofNat n))
  | _ => none

/-- A payload type: a type word, or `T in lo .. hi`. -/
def uNutzTyp (alias : List (String × (Int × Int))) : List Token → Except String (Int × Int)
  | [.ident n] => uTypName alias n
  | [.wort n] => uTypName alias n
  | ts =>
    match uTeileBereich [] ts with
    | some (_ :: .wort "in" :: lo, ex, hi) =>
      match uZahlTok lo, uZahlTok hi with
      | some a, some b => .ok (a, if ex then b - 1 else b)
      | _, _ => .error "payload range without G form"
    | _ => .error "payload type without G form"

/-- The tokens up to the closing parenthesis, and the rest behind it. -/
def uBisKlammer : List Token → List Token → Option (List Token × List Token)
  | _, [] => none
  | acc, .zeichen ")" :: rest => some (acc.reverse, rest)
  | acc, t :: rest => uBisKlammer (t :: acc) rest

/-- The cases of a tagged type from its tokens (`Leer , Kurz ( u32 in 0 .. 100 )`), `fuel` bounds the length. -/
def uSumFaelle (alias : List (String × (Int × Int))) :
    Nat → List Token → Except String (List (String × Option (Int × Int)))
  | 0, _ => .error "tagged type too long"
  | _, [] => .ok []
  | f + 1, .ident n :: .zeichen "," :: rest =>
    match uSumFaelle alias f rest with
    | .error e => .error e
    | .ok r => .ok ((n, none) :: r)
  | _ + 1, [.ident n] => .ok [(n, none)]
  | f + 1, .ident n :: .zeichen "(" :: rest =>
    match uBisKlammer [] rest with
    | none => .error "tagged case without G form"
    | some (ty, rest2) =>
      match uNutzTyp alias ty with
      | .error e => .error e
      | .ok r =>
        match rest2 with
        | [] => .ok [(n, some r)]
        | .zeichen "," :: rest3 =>
          match uSumFaelle alias f rest3 with
          | .error e => .error e
          | .ok more => .ok ((n, some r) :: more)
        | _ => .error "tagged case without G form"
  | _ + 1, _ => .error "tagged case without G form"

/-- The `tagged type` items of a unit. -/
def uSums (alias : List (String × (Int × Int))) : List SItemTief → Except String (List USum)
  | [] => .ok []
  | .typeT ["tagged"] n _ _ (.some (.raw txt)) :: rest =>
    match lex txt with
    | .error _ => .error "tagged type without G form"
    | .ok toks0 =>
      let toks := toks0.filter (fun k => match k with | .ende => false | _ => true)
      match toks with
      | .zeichen "{" :: inner =>
        match inner.reverse with
        | .zeichen "}" :: rev =>
          match uSumFaelle alias 10000 rev.reverse with
          | .error e => .error e
          | .ok cs =>
            if cs.isEmpty then .error "tagged type without cases"
            else
              match uSums alias rest with
              | .error e => .error e
              | .ok r => .ok ({ name := n, cases := cs } :: r)
        | _ => .error "tagged type without G form"
      | _ => .error "tagged type without G form"
  | _ :: rest => uSums alias rest

/-- The `reason` items of a unit: the names of their cases in order; a reason that is not `exhaustive` has no
    G form (`Ty.why n` has exactly `n` reasons). -/
def uWhys : List SItemTief → Except String (List UWhy)
  | [] => .ok []
  | .whyT n cs ex :: rest =>
    if !ex then .error "reason that is not exhaustive without G form"
    else
      match uWhys rest with
      | .error e => .error e
      | .ok r => .ok ({ name := n, cases := cs.map (·.1) } :: r)
  | _ :: rest => uWhys rest

/-! ## States -/

/-- The stage names of a `state`, in the order they are first written. -/
def uStufenNamen : List (SExpr × SExpr × SExpr) → List String → Except String (List String)
  | [], acc => .ok acc
  | (_, .variable a, .variable c) :: rest, acc =>
    let acc1 := if acc.any (strEq · a) then acc else acc ++ [a]
    let acc2 := if acc1.any (strEq · c) then acc1 else acc1 ++ [c]
    uStufenNamen rest acc2
  | _ :: _, _ => .error "state stage without G form"

/-- One `state` item: stages 0, 1, 2, .. in written order, one allowed pair per transition line. A
    `requires` or an `effects` at a state transition has no form here. -/
def uZustand (n : String) (ts : List STrans) : Except String UZustand :=
  if !ts.all (fun tr => tr.voraus.isNone && tr.wirkung.isEmpty) then .error "state transition clause without G form"
  else
    let schritte := ts.flatMap (·.schritte)
    match uStufenNamen schritte [] with
    | .error e => .error e
    | .ok stufen =>
      let nr : SExpr → Nat := fun e => match e with
        | .variable a => (stufen.findIdx? (strEq · a)).getD 0
        | _ => 0
      .ok { name := n, stufen, paare := schritte.map fun (_, a, c) => (nr a, nr c) }

/-- The governed fields: each `transition` statement of a body names its table, field and state; a field
    governed by two states is refused. -/
def uRegiert (fns : List UFn) : Except String (List (String × String × String)) :=
  let alle := fns.flatMap fun f => f.body.filterMap fun st => match st with
    | .shiftTab tb fld _ s _ _ => some (tb, fld, s)
    | _ => none
  let eins := alle.foldl (fun acc x => if acc.any (fun y => strEq y.1 x.1 && strEq y.2.1 x.2.1 && strEq y.2.2 x.2.2)
    then acc else acc ++ [x]) []
  if eins.all (fun x => eins.all (fun y => !(strEq x.1 y.1 && strEq x.2.1 y.2.1) || strEq x.2.2 y.2.2)) then .ok eins
  else .error "a field governed by two states"

/-! ## Invariants -/

/-- The predicate of an invariant over its carriers: no parameter, the guards of the carriers held. -/
def uInv (consts : List (String × Int)) (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (traeger : List String) (g : SGruppenInv) : Except String UInv :=
  if !traeger.all (fun c => tabs.any (fun t => strEq t.name c && !t.arena)) then .error "invariant carrier without G form"
  else
    let held := (locks.filter (fun l => l.guard.any (fun c => traeger.any (strEq · c)))).map (·.name)
    let ctx : UCtx := { names := [], kinds := [], types := [], tabs, locks, held, res := none, fname := g.name,
                        alias, lits := consts, globs }
    match uBool ctx g.pred with
    | .error e => .error e
    | .ok p => .ok { name := g.name, traeger, pred := p }

/-- The `invariant p` of each lock, read with the lock held: the predicate names the protected carriers and
    constants only (`N275`). -/
def uSperrInvs (consts : List (String × Int)) (alias : List (String × (Int × Int))) (globs : List UGlob)
    (tabs : List UTab) (ms : List SItemTief) (locks : List ULock) : Except String (List ULock) :=
  uSeq (locks.map fun l =>
    match ms.findSome? (fun m => match m with | .lockT n _ _ _ _ _ p => if strEq n l.name then some p else none | _ => none) with
    | some (some e) =>
      let ctx : UCtx := { names := [], kinds := [], types := [], tabs, locks, held := [l.name], res := none,
                          fname := l.name, alias, lits := consts, globs }
      match uBool ctx e with
      | .error x => .error x
      | .ok p => .ok { l with inv := some p }
    | _ => .ok l)

/-- The invariants of the unit: those of each table, in table order, then those of each `group`. -/
def uInvs (consts : List (String × Int)) (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (ms : List SItemTief) : Except String (List UInv) :=
  let ausTab := ms.flatMap fun it => match it with
    | .tableT n _ _ _ _ _ parts => parts.filterMap fun p => match p with
      | .tInv g => some (uInv consts alias tabs locks globs [n] g)
      | _ => none
    | _ => []
  let ausGruppe := ms.flatMap fun it => match it with
    | .groupT _ ts gs => gs.map (uInv consts alias tabs locks globs ts)
    | _ => []
  uSeq (ausTab ++ ausGruppe)

/-- `U003`: a function that writes a carrier of an invariant holds (by `requires Held(..)`) every lock that
    guards a carrier of it -- it owes the invariant at its `return` and reads all of them there. -/
def uU003 (locks : List ULock) (fns : List UFn) (invs : List UInv) : Bool :=
  invs.all fun i => fns.all fun f =>
    !(f.puts.any (fun t => i.traeger.any (strEq · t))) ||
    (locks.filter (fun l => l.guard.any (fun c => i.traeger.any (strEq · c)))).all
      (fun l => f.held.any (strEq · l.name))

/-! ## Device registers -/

/-- The register class word (`regklasse`). -/
def uRegKlasse (k : String) : Except String Regklasse :=
  if strEq k "r" then .ok .r else if strEq k "w" then .ok .w else if strEq k "rw" then .ok .rw
  else if strEq k "w1c" then .ok .w1c else if strEq k "rc" then .ok .rc
  else .error ("register class without G form: " ++ k)

/-- A side of a register predicate at the value `v` (the register's own name reads `v`). -/
def uZSeite (v : Int) : USide → Option Int
  | .lit k => some k
  | .param _ => some v
  | .add a b => (uZSeite v a).bind fun x => (uZSeite v b).map (x + ·)
  | .sub a b => (uZSeite v a).bind fun x => (uZSeite v b).map (x - ·)
  | .mul a b => (uZSeite v a).bind fun x => (uZSeite v b).map (x * ·)
  | .neg a => (uZSeite v a).map (- ·)
  | _ => none

/-- A comparison of two numbers by its operator word. -/
def uVergleich (op : String) (x y : Int) : Option Bool :=
  if strEq op "==" then some (decide (x = y)) else if strEq op "!=" then some (!decide (x = y))
  else if strEq op "<" then some (decide (x < y)) else if strEq op "<=" then some (decide (x ≤ y))
  else if strEq op ">" then some (decide (y < x)) else if strEq op ">=" then some (decide (y ≤ x))
  else none

/-- A register predicate at the value `v` (`none`: a form the promise does not evaluate). -/
def uZEns (v : Int) : UEns → Option Bool
  | .cmp op a b => (uZSeite v a).bind fun x => (uZSeite v b).bind fun y => uVergleich op x y
  | .tru => some true
  | .fls => some false
  | .and a b => (uZEns v a).bind fun x => (uZEns v b).map (x && ·)
  | .or a b => (uZEns v a).bind fun x => (uZEns v b).map (x || ·)
  | .not a => (uZEns v a).map (!·)
  | _ => none

/-- The device's promise of a register at a read value: `true` without a promise. -/
def UReg.zusageBei (g : UReg) (v : Int) : Bool :=
  match g.zusage with
  | none => true
  | some p => (uZEns v p).getD true

/-- The context of a register predicate: the register's own name is its one (numeric) variable. -/
def uRegCtx (alias : List (String × (Int × Int))) (lits : List (String × Int)) (n : String) (lo hi : Int) :
    UCtx :=
  { names := [n], kinds := [.int], types := [.int lo hi], tabs := [], locks := [], held := [], res := none,
    fname := n, alias, lits }

/-- One `reg` of a device: an integer type (an EMPTY range `lo > hi` included: the declaration stands, a read
    answers nothing -- the checker's `N314`), a class without stages, no bit fields, a promise (or, with
    `else`, a check at the binding) that evaluates, and `depends` carriers that are tables or statics of the
    unit, named bare. -/
def uReg (alias : List (String × (Int × Int))) (lits : List (String × Int)) (tabs : List UTab)
    (globs : List UGlob) (dev : String) (rg : SReg) : Except String UReg :=
  if !rg.stage.isEmpty then .error "register class per stage without G form"
  else if !rg.felder.isEmpty then .error "register fields without G form"
  else
    match (match rg.rtyp with
        | .atom "bool" => .ok (0, 1, true)
        | t => (uErgBereich alias t).map fun (lo, hi) => (lo, hi, false) : Except String (Int × Int × Bool)) with
    | .error e => .error e
    | .ok (lo, hi, istB) =>
      match uRegKlasse rg.klasse with
      | .error e => .error e
      | .ok k =>
        match uSeq (rg.abhaengt.map fun c => match c with
            | [n] =>
              if tabs.any (fun x => strEq x.name n) || globs.any (fun x => strEq x.name n) then .ok n
              else .error ("depends names no carrier: " ++ n)
            | _ => .error "depends on a field without G form") with
        | .error e => .error e
        | .ok ts =>
          match (match rg.voraus with
              | none => .ok none
              | some p =>
                match uBool (uRegCtx alias lits rg.name lo hi) p with
                | .error e => .error e
                | .ok q => if (uZEns lo q).isSome then .ok (some q) else .error "register promise without G form"
              : Except String (Option UEns)) with
          | .error e => .error e
          | .ok pr =>
            match rg.elseF with
            | some _ => .ok { dev, name := rg.name, lo, hi, klasse := k, traeger := ts, pruefung := pr, bool := istB }
            | none => .ok { dev, name := rg.name, lo, hi, klasse := k, traeger := ts, zusage := pr, bool := istB }

/-- `mirrors W from M` of a device: `M` at `W`. -/
def uSpiegelPaare : List SGerTeil → Except String (List (String × String))
  | [] => .ok []
  | .copy (.variable w) (.variable m) :: rest =>
    match uSpiegelPaare rest with
    | .error e => .error e
    | .ok ps => .ok ((w, m) :: ps)
  | .copy .. :: _ => .error "mirrors without G form"
  | _ :: rest => uSpiegelPaare rest

/-- The registers of one device, in order: banks and transitions have no G form here (a `bank` is sugar for
    indexed registers; a device `transition` has no statement that invokes it in the language). -/
def uGeraet (alias : List (String × (Int × Int))) (lits : List (String × Int)) (tabs : List UTab)
    (globs : List UGlob) (dev : String) (teile : List SGerTeil) : Except String (List UReg) :=
  match uSpiegelPaare teile with
  | .error e => .error e
  | .ok ms =>
    match uSeq (teile.filterMap fun p => match p with
        | .reg rg => some (uReg alias lits tabs globs dev rg)
        | .bank _ => some (.error "register bank without G form")
        | .trans _ => some (.error "device transition without G form")
        | .copy .. => none) with
    | .error e => .error e
    | .ok regs =>
      if ms.all (fun (w, m) => regs.any (fun g => strEq g.name w) && regs.any (fun g => strEq g.name m)) then
        .ok (regs.map fun g =>
          { g with spiegel := (ms.find? (fun p => strEq p.1 g.name)).map (·.2) })
      else .error "mirrors names no register of the device"

/-- The registers of the unit: every `device` item in order. -/
def uRegs (alias : List (String × (Int × Int))) (lits : List (String × Int)) (tabs : List UTab)
    (globs : List UGlob) : List SItemTief → Except String (List UReg)
  | [] => .ok []
  | .devT n _ _ teile :: rest =>
    match uGeraet alias lits tabs globs n teile with
    | .error e => .error e
    | .ok rs =>
      match uRegs alias lits tabs globs rest with
      | .error e => .error e
      | .ok more => .ok (rs ++ more)
  | _ :: rest => uRegs alias lits tabs globs rest

/-! ## Lock floors (`Signatur.boden`)

    The floor of a function is the lowest rank of any lock taken on a path from it (its own `locks L` blocks
    and, through its calls, the callees'); a function that takes none has the floor `hoch`, above every rank
    of the unit. A unit without locks has no floors.
    The floor is DATA of the elaborated function (`UFn.boden`), filled by the post-pass `uMitBoden` after
    elaboration; the declaration reads it (`mkSig`). This is the rule of the exporter (`resolve_floors`):
    an extra lock held across a call ranks below the callee's floor (`RufPasst.hx`), so every lock the callee
    takes ranks above everything held (`H006` across the call boundary). -/

/-- The rank of a lock by name. -/
def lockRank (u : UProg) (n : String) : Option Int :=
  (u.locks.find? (fun l => l.name == n)).map (·.rank)

def optMin : Option Int → Option Int → Option Int
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

/-- The lowest rank a function takes directly (its `locks L { .. }` blocks). -/
def directFloor (u : UProg) (f : UFn) : Option Int :=
  f.body.foldl (fun acc st => match st with
    | .lockBeg n => optMin acc (lockRank u n)
    | _ => acc) none

/-- The functions a function calls directly: a call statement, a call bound by `let`, and a call bound by
    `let .. else (e) { .. }` (`bindElse`). -/
def callNames (f : UFn) : List String :=
  f.body.filterMap fun st => match st with
    | .call c _ => some c
    | .bindCall _ c _ => some c
    | .bindElse _ c _ _ => some c
    | .callInd _ c _ => some c
    | .bindCallInd _ _ c _ => some c
    | _ => none

/-- One round of the floor relation: the direct floor and the floors of the callees found so far. -/
def floorStep (u : UProg) (cur : List (String × Option Int)) : List (String × Option Int) :=
  u.fns.map fun f =>
    (f.name, (callNames f).foldl
      (fun acc c => optMin acc (((cur ++ u.ptrs.map (fun p => (p.name, p.boden))).find? (fun p => p.1 == c)).bind
        (·.2))) (directFloor u f))

/-- `n` rounds (a path through the call graph is at most as long as the number of functions). -/
def floorsN (u : UProg) : Nat → List (String × Option Int)
  | 0 => u.fns.map fun f => (f.name, directFloor u f)
  | n + 1 => floorStep u (floorsN u n)

/-- The floor of a function: `none` in a unit without locks, else the lowest rank on any path from it, or
    one above the highest rank of the unit when the paths take no lock. -/
def floorOf (u : UProg) (f : UFn) : Option Int :=
  if u.locks.isEmpty then none
  else some (match ((floorsN u u.fns.length).find? (fun p => p.1 == f.name)).bind (·.2) with
    | some c => c
    | none => (u.locks.map (·.rank)).foldl max 0 + 1)

/-- The post-pass: every function carries its floor (`UFn.boden`). -/
def uMitBoden (u : UProg) : UProg :=
  { u with fns := u.fns.map fun f => { f with boden := floorOf u f } }


/-! ## Function-pointer types (2026-10-21)

  A `fn(..) [-> T] effects { .. } costs <= e ops` type of the unit is read once by its text (the type reader keeps
  it raw, `STyp.raw`) into a head like a function's and a signature with an empty body (`UProg.ptrs`). Its number
  stands behind the functions'; a function conforms to it by `Deklaration.passt` (`passtAt`, decided). The model
  has no contract on a signature: a `requires` (`Held(..)` included) or an `ensures` is refused by name (TODO O43);
  `costs` travels nowhere, as at a function. No lock crosses an indirect call (a `locks` effect at the type is
  refused, as `N036` does): the floor of the type is one above the highest rank of the unit. -/

/-- The parameters of a pointer type up to `)`: `[name :] type`, comma separated (an unnamed one is `p<k>`). -/
def uZeigerParams : Nat → Nat → List Token → Except String (List (String × STyp) × List Token)
  | 0, _, _ => .error "out of fuel"
  | _ + 1, _, .zeichen ")" :: r => .ok ([], r)
  | f + 1, k, toks =>
    let (n, toks') : String × List Token := match toks with
      | t :: .zeichen ":" :: r => match nameText t with
        | some n => (n, r)
        | none => ("p" ++ toString k, toks)
      | _ => ("p" ++ toString k, toks)
    match parseTyp f toks' with
    | .error e => .error e
    | .ok (ty, .zeichen "," :: r) =>
      match uZeigerParams f (k + 1) r with
      | .error e => .error e
      | .ok (ps, r') => .ok ((n, ty) :: ps, r')
    | .ok (ty, .zeichen ")" :: r) => .ok ([(n, ty)], r)
    | .ok _ => .error "pointer type parameters without G form"

/-- A contract on a pointer type: refused (the model's signatures carry none, TODO O43; `N589` in the checker).
    `requires Held(..)` is refused too: no lock crosses an indirect call. -/
def uZeigerVertrag : List SKlausel → Except String Unit
  | [] => .ok ()
  | .needs .tru :: rest => uZeigerVertrag rest
  | .gives .tru :: rest => uZeigerVertrag rest
  | .needs _ :: _ => .error "contract on a function-pointer type without G form"
  | .gives _ :: _ => .error "contract on a function-pointer type without G form"
  | _ :: rest => uZeigerVertrag rest

/-- The text of a pointer type as a function head (`FnSig`, art `impl`, no name). -/
def uZeigerSig (raw : String) : Except String FnSig :=
  match lex raw with
  | .error _ => .error "pointer type unreadable"
  | .ok (.wort "fn" :: .zeichen "(" :: r) =>
    match uZeigerParams 10000 0 r with
    | .error e => .error e
    | .ok (ps, r1) =>
      match parseErgebnis 10000 r1 with
      | .error e => .error e
      | .ok (_, some _, _) => .error "pointer type with a reason channel without G form"
      | .ok (erg, none, r2) =>
        match parseKlauseln 10000 r2 with
        | .error e => .error e
        | .ok (ks, r3) =>
          if !(r3.all (fun t => match t with | .ende => true | _ => false)) then .error "pointer type without G form"
          else .ok { art := "impl", name := "", params := ps, res := erg, fehler := none, klauseln := ks }
  | .ok _ => .error "pointer type without G form"

/-- The texts of the pointer types a surface type list names (`fn (` raw types). -/
def uZeigerTexte : List STyp → List String
  | [] => []
  | .raw r :: rest => if r.startsWith "fn (" then r :: uZeigerTexte rest else uZeigerTexte rest
  | _ :: rest => uZeigerTexte rest

/-- The pointer types written at a `let` of a body. -/
def uZeigerAnw : Nat → SAnw → List String
  | 0, _ => []
  | f + 1, a => match a with
    | .bind _ _ (some t) _ => uZeigerTexte [t]
    | .bindElse _ (some t) _ _ b => uZeigerTexte [t] ++ uZeigerAnw f b
    | .bindElse _ none _ _ b => uZeigerAnw f b
    | .cond _ t es e => uZeigerAnw f t ++ (es.flatMap (uZeigerAnw f)) ++ (match e with | some b => uZeigerAnw f b | none => [])
    | .elsif _ b => uZeigerAnw f b
    | .cases _ as => as.flatMap (uZeigerAnw f)
    | .arm _ _ b => uZeigerAnw f b
    | .each _ _ _ _ _ _ _ b => uZeigerAnw f b
    | .retry _ b => uZeigerAnw f b
    | .loop _ b => uZeigerAnw f b
    | .waive _ b => uZeigerAnw f b
    | .trim _ _ b => uZeigerAnw f b
    | .locks _ _ b => uZeigerAnw f b
    | .watch _ b => uZeigerAnw f b
    | .alloc _ _ _ _ _ (some b) => uZeigerAnw f b
    | .grow _ _ b => uZeigerAnw f b
    | .child b => uZeigerAnw f b
    | .block as _ => as.flatMap (uZeigerAnw f)
    | _ => []

/-- A pointer type of the unit as a head (named `fn#j`) and an elaborated signature with an empty body. -/
def elabZeigerTyp (consts : List (String × Int)) (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (whys : List UWhy) (sums : List USum) (zeiger : List String)
    (zb j : Nat) (raw : String) : Except String (UFnKopf × UFn) :=
  match uZeigerSig raw with
  | .error e => .error e
  | .ok sig =>
    match uZeigerVertrag sig.klauseln with
    | .error e => .error e
    | .ok _ =>
      match elabKopf consts alias tabs locks globs whys sums sig [] zeiger zb with
      | .error e => .error e
      | .ok (kopf0, schreibt) =>
        let name := "fn#" ++ toString j
        let kopf := { kopf0 with name := name }
        let genommen := (uEffekte kopf tabs locks globs sig.klauseln).toOption.map (·.locks) |>.getD []
        if !genommen.isEmpty then .error "locks at a function-pointer type do not cross an indirect call" else
        -- No lock crosses an indirect call: the floor is one above the highest rank of the unit, so a
        -- conforming function takes no lock (`SigPasst.boden`), and a caller may hold any.
        let boden : Option Int := if locks.isEmpty then none else some ((locks.map (·.rank)).foldl max 0 + 1)
        .ok (kopf, { name := name, params := kopf.names.zip kopf.types, kinds := kopf.kinds,
                     res := kopf.res, resBool := kopf.resBool, resOpt := kopf.resOpt, resSum := kopf.resSum,
                     gruende := 0, held := kopf.held, puts := schreibt, gputs := kopf.gputs, gives := [], needs := [],
                     body := [], ret := .empty, boden := boden })

/-- The names a unit declares as memory: tables, arenas, statics, atomics. -/
def uSpeicherNamen (ms : List SItemTief) : List String :=
  ms.filterMap fun
    | .tableT n .. => some n
    | .arenaT n .. => some n
    | .globT _ n .. => some n
    | .atomT n .. => some n
    | _ => none

/-- The writes of a clause list that name no memory of the unit. -/
def uFremdeSchreibe (mem : List String) (ks : List SKlausel) : List String :=
  ks.flatMap fun
    | .effs es => es.filterMap fun
      | .writes (.variable n) => if mem.any (strEq · n) then none else some n
      | _ => none
    | _ => []

/-- The clause list without the writes of the sinks. -/
def uKlauselnOhne (senken : List String) (ks : List SKlausel) : List SKlausel :=
  ks.map fun
    | .effs es => .effs (es.filter fun
      | .writes (.variable n) => !(senken.any (strEq · n))
      | _ => true)
    | k => k

/-- **Sinks** (`writes ausgabe` at an `extern fn`): a name that is no memory of the unit, written by a foreign body,
    is what lies behind it outside the program -- no carrier of G; the call itself is the trace event
    (`Ereignis.fremd`). Such a name may stand in the `writes` of the foreign bodies and of the functions that call
    them; it is dropped there. A name no foreign body declares stays and is refused as an unknown carrier. -/
def uOhneSenken (ms : List SItemTief) : List SItemTief :=
  let mem := uSpeicherNamen ms
  let senken := ms.flatMap fun
    | .protoT sig => uFremdeSchreibe mem sig.klauseln
    | .asmT sig _ => uFremdeSchreibe mem sig.klauseln
    | .axiomT _ _ _ _ effs _ => uFremdeSchreibe mem [.effs effs]
    | _ => []
  if senken.isEmpty then ms else
  ms.map fun
    | .fnT sig b => .fnT { sig with klauseln := uKlauselnOhne senken sig.klauseln } b
    | .protoT sig => .protoT { sig with klauseln := uKlauselnOhne senken sig.klauseln }
    | .asmT sig c => .asmT { sig with klauseln := uKlauselnOhne senken sig.klauseln } c
    | .axiomT n ps r q effs k =>
      .axiomT n ps r q (match uKlauselnOhne senken [.effs effs] with | [.effs es] => es | _ => effs) k
    | m => m

/-- The signature of a foreign body item and whether it is `= asm { .. }`: `extern`/`raw`/`prim`/`divergent` declarations,
    `asm` bodies, and `axiom` items without a `requires` (read as an `extern fn` with their effects). -/
def uFremdSig : SItemTief → Option (FnSig × Bool)
  | .protoT sig => some (sig, false)
  | .asmT sig _ => some (sig, true)
  | .axiomT n ps res .none effs _ =>
    some ({ art := "extern", name := n, params := ps, res, fehler := .none, klauseln := [.effs effs] }, false)
  | _ => none

/-- The elaborator: a parsed surface tree to the exported
    fragment (tables, locks, `impl` functions). -/
def elabU : List SItemTief → Except String UProg
  | items =>
    let ms0 := uMembers items
    let consts := uConstsRech (uKonstFns ms0) ms0 []
    let alias := uAliase consts ms0 ++ consts.map (fun c => (c.1, (c.2, c.2)))
    match uRestFehler ms0 with
    | .error e => .error e
    | .ok _ =>
    let ms := uOhneSenken ms0
    match uGlobs consts alias ms with
    | .error e => .error e
    | .ok globs0 =>
    let tnames := ms.filterMap (fun | .tableT n _ _ _ _ _ _ => some n | _ => none)
    match uSeq ((ms.filter (fun
        | .tableT _ _ _ _ _ _ _ => true | _ => false)).map (uTabelle consts alias tnames)) with
    | .error e => .error e
    | .ok tabs0 =>
    match uArenen consts alias ms with
    | .error e => .error e
    | .ok (arTabs, arGlobs) =>
    let tabs := uIdxTabs (tabs0 ++ arTabs)
    match uOptGlobs tabs (globs0 ++ arGlobs) with
    | .error e => .error e
    | .ok globs =>
    match uSeq ((ms.filter (fun
        | .lockT _ _ _ _ _ _ _ => true | _ => false)).map (uSperre globs tabs)) with
    | .error e => .error e
    | .ok locks0 =>
    match uSperrInvs consts alias globs tabs ms locks0 with
    | .error e => .error e
    | .ok locks =>
    let bewacht : String → Bool := fun c => locks.any (fun l => l.guard.any (strEq · c))
    if !tabs.all (fun t => !t.shared || bewacht t.name) then .error "shared table without a guard" else
    if !globs.all (fun g => !g.shared || g.atomic || bewacht g.name) then .error "shared static without a guard" else
    if !globs.all (fun g => g.nutzlast.all (fun n => globs.any (fun h => strEq h.name n))) then
      .error "payload names no static" else
    let fnItems := ms.filterMap (fun
      | .fnT sig koerper => if strEq sig.art "const" then none else some (sig, koerper)
      | _ => none)
    match uWhys ms with
    | .error e => .error e
    | .ok whys =>
    match uSums alias ms with
    | .error e => .error e
    | .ok sums =>
    match uSumGlobs consts sums ms globs with
    | .error e => .error e
    | .ok globs =>
    match uSumTabs sums tabs with
    | .error e => .error e
    | .ok tabs =>
    match uRegs alias consts tabs globs ms with
    | .error e => .error e
    | .ok regs =>
    match uInvs consts alias tabs locks globs ms with
    | .error e => .error e
    | .ok invs =>
    match uSeq (ms.filterMap (fun | .stateT n ts => some (uZustand n ts) | _ => none)) with
    | .error e => .error e
    | .ok zustaende =>
    let devs := ms.filterMap (fun | .devT n _ _ _ => some n | _ => none)
    let zeiger := uOhneDoppelte (fnItems.flatMap (fun (s, b) => uZeigerTexte (s.params.map (·.2)) ++ uZeigerAnw 100000 b))
    let zb := fnItems.length
    match uSeq ((List.range zeiger.length).zip zeiger |>.map (fun (j, r) =>
        elabZeigerTyp consts alias tabs locks globs whys sums zeiger zb j r)) with
    | .error e => .error e
    | .ok zeigerPaare =>
    match uSeq (fnItems.map (fun (s, _) => elabKopf consts alias tabs locks globs whys sums s devs zeiger zb)) with
    | .error e => .error e
    | .ok [] => .error "unit without a fn"
    | .ok kopfPaare =>
    match uSeq ((ms.filterMap uFremdSig).map (fun (sig, asm) => elabAxKopf alias tabs whys globs asm sig)) with
    | .error e => .error e
    | .ok axKoepfe0 =>
    match uSeq ((ms.filterMap (fun | .callT sc => some sc | _ => none)).map (elabGateKopf alias tabs whys)) with
    | .error e => .error e
    | .ok gateKoepfe =>
    let axKoepfe := axKoepfe0 ++ gateKoepfe
    let koepfe := kopfPaare.map (·.1) ++ axKoepfe ++ zeigerPaare.map (·.1)
    let annahmen := ms.filterMap (fun | .assumT n _ _ _ => some n | _ => none)
    match uSeq (fnItems.map (fun (s, b) =>
        elabUFunktion consts alias tabs locks globs koepfe s b annahmen whys sums devs regs zustaende zeiger zb
          (ms.filterMap (fun | .specT sg body => some (sg.name, sg.params.map (·.1), body) | _ => none))
          (uKonstArrays alias (uKonstFns ms) consts ms))) with
    | .error e => .error e
    | .ok fns =>
    match uWurzeln tabs fns ms with
    | .error e => .error e
    | .ok roots =>
    match uSeq ((uOhneDoppelte (fnItems.flatMap (fun (_, b) => uStartNamen 100000 b))).map
        (fun d => uStart fns "start" d)) with
    | .error e => .error e
    | .ok gestartet =>
      if !uU003 locks (fns ++ zeigerPaare.map (·.2)) invs then .error "a writer of an invariant's carrier does not hold all its locks" else
      match uRegiert fns with
      | .error e => .error e
      | .ok regiert =>
      let u : UProg :=
        { tabs := tabs, locks := locks, fns := fns, roots := roots, hands := uHandler ms, globs := globs,
          gestartet := gestartet,
          axs := axKoepfe.map (fun k => { name := k.name, params := k.types, kinds := k.kinds, res := k.axErg,
                                          gruende := (k.kanal.map (·.2)).getD 0, puts := k.puts, gputs := k.gputs }),
          annahmen := annahmen, whys := whys, sums := sums, regs := regs, invs := invs,
          zustaende := zustaende, regiert := regiert, ptrs := zeigerPaare.map (·.2), ptrKeys := zeiger }
      .ok (uMitBoden u)

/-! ## Lowering: from U to the exporter's declaration universe -/

/-- The body context of `einzahlen`: its parameters. -/
abbrev UCtxEin := G104_referenz.gCtx_einzahlen

/-- The held resources of `einzahlen`. -/
abbrev ULEin := G104_referenz.gL_einzahlen

/-- The `ensures` type of `einzahlen`. -/
abbrev UEnsEin :=
  Expr G104_referenz.gD (ErgCtx (G104_referenz.gD.params G104_referenz.g_einzahlen) (G104_referenz.gD.erg G104_referenz.g_einzahlen))
    (vertragVon G104_referenz.gD G104_referenz.g_einzahlen).ende .bool

/-- The body type of `einzahlen`. -/
abbrev UKoerpEin :=
  Endblock G104_referenz.gD (vertragVon G104_referenz.gD G104_referenz.g_einzahlen) false G104_referenz.gCtx_einzahlen G104_referenz.gL_einzahlen

/-- A parameter variable of `einzahlen` by position and type
    (positions are the known signature; anything else is an
    explicit error). -/
def varNumEin : (j : Nat) → (τ : Ty) → Except String (Var UCtxEin τ)
  | 0, .ptr 0 true => .ok .here
  | 1, .int 0 1 => .ok (.there .here)
  | 2, .int 0 10 => .ok (.there (.there .here))
  | _, _ => .error "parameter without G form"

/-- An index into `Konto` in `einzahlen`: the `i` parameter or
    a literal inside `count` (the `tr_index` of `lean_g.rs`,
    with the range check as an explicit error). -/
def lowerIdxEin : UIdx →
    Except String (Expr G104_referenz.gD UCtxEin ULEin (.index (G104_referenz.gD.count G104_referenz.GTab.Konto)))
  | .param "i" => .ok (Expr.var (Var.there Var.here))
  | .lit n =>
    if h1 : 0 ≤ n then
      if h2 : n ≤ 1 then .ok (Expr.widen h1 h2 (Expr.lit n))
      else .error "index outside count"
    else .error "index outside count"
  | _ => .error "index without G form"

/-- The field range recorded for (`Konto`, `stand`) must be
    the exporter's `(0, 100)`; otherwise the G term below
    would ascribe the wrong type silently. -/
def uFeldWeite (tabs : List UTab) (t f : String) (lo hi : Int) :
    Except String Unit :=
  match tabs.find? (fun x => strEq x.name t) with
  | .none => .error ("table unknown: " ++ t)
  | .some tb =>
    match tb.cols.find? (fun (g, _) => strEq g f) with
    | .none => .error "field unknown"
    | .some (_, (a, b)) =>
      if a == lo && b == hi then .ok () else .error "field range foreign"
/-- One side in `einzahlen`, with its range (the `tr_side` of
    `lean_g.rs`; a pointer parameter in a comparison is an
    explicit error). -/
structure USeiteT where
  range : Int × Int
  term : Expr G104_referenz.gD UCtxEin ULEin (.int range.1 range.2)

def lowerSeiteEin (tabs : List UTab) (names : List String)
    (types : List Ty) : USide → Except String USeiteT
  | .glob _ => .error "static without G form in the 104 lowering"
  | .refSlot .. => .error "reference without G form in the 104 lowering"
  | .idx .. | .len _ | .text _ | .arrNil | .arrCons .. | .upd .. | .typed .. => .error "aggregate without G form in the 104 lowering"
  | .eng .. => .error "narrowing without G form in the 104 lowering"
  | .lit n => .ok { range := (n, n), term := Expr.lit n }
  | .param p =>
    match uStelle ["k", "i", "b"] p with
    | .error e => .error e
    | .ok j =>
      match names[j]?, types[j]? with
      | .some q, .some (Ty.int lo hi) =>
        if !strEq q p then .error "parameter swapped"
        else
          match varNumEin j (.int lo hi) with
          | .error e => .error e
          | .ok v => .ok { range := (lo, hi), term := Expr.var v }
      | _, _ => .error "parameter without G form"
  | .slot b f ix =>
    if !(strEq b "k" && strEq f "stand") then .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEin ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100),
                term := Expr.thru (Expr.var Var.here)
                  G104_referenz.GTab.Konto rfl
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_einzahlen_Konto }
  | .tab b f ix =>
    if !(strEq b "Konto" && strEq f "stand") then .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEin ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100),
                term := Expr.slot G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_einzahlen_Konto }
  | .old b f ix =>
    if !((strEq b "k" || strEq b "Konto") && strEq f "stand") then
      .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEin ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100),
                term := Expr.oldS G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_einzahlen_Konto }
  | .erg => .error "result in a body"
  | .add .. | .sub .. | .mul .. | .conv .. | .band .. | .bor .. | .bxor .. | .div .. | .rem .. | .shl .. | .shr .. | .neg .. =>
    .error "arithmetic without G form in the 104 lowering"
/-- One comparison in `einzahlen` (the `tr_cmp` of `lean_g.rs`;
    G folds all but `lt`/`le`/`eq`). -/
def lowerVglEin (tabs : List UTab) (names : List String)
    (types : List Ty) : String → USide → USide → Except String UEnsEin
  | op, a, b =>
    match lowerSeiteEin tabs names types a with
    | .error e => .error e
    | .ok s1 =>
      match lowerSeiteEin tabs names types b with
      | .error e => .error e
      | .ok s2 =>
        match op with
        | "==" => .ok (Expr.eq s1.term s2.term)
        | "!=" => .ok (Expr.not (Expr.eq s1.term s2.term))
        | "<" => .ok (Expr.lt s1.term s2.term)
        | "<=" => .ok (Expr.le s1.term s2.term)
        | ">" => .ok (Expr.lt s2.term s1.term)
        | ">=" => .ok (Expr.le s2.term s1.term)
        | _ => .error "operator without G form"

/-- One `ensures` predicate in `einzahlen`. -/
def lowerSichertEin (tabs : List UTab) (names : List String)
    (types : List Ty) : UEns → Except String UEnsEin
  | .globB _ | .var _ | .ergB => .error "static without G form in the 104 lowering"
  | .alle .. | .einige .. => .error "quantifier without G form in the 104 lowering"
  | .cmp op a b => lowerVglEin tabs names types op a b
  | .tru => .ok Expr.tru
  | .fls => .ok Expr.fls
  | .and a b =>
    match lowerSichertEin tabs names types a with
    | .error e => .error e
    | .ok x =>
      match lowerSichertEin tabs names types b with
      | .error e => .error e
      | .ok y => .ok (Expr.and x y)
  | .or a b =>
    match lowerSichertEin tabs names types a with
    | .error e => .error e
    | .ok x =>
      match lowerSichertEin tabs names types b with
      | .error e => .error e
      | .ok y => .ok (Expr.or x y)
  | .not a =>
    match lowerSichertEin tabs names types a with
    | .error e => .error e
    | .ok x => .ok (Expr.not x)
  | .slotB .. | .tabB .. => .error "bool place without G form in the 104 lowering"
  | .istSome .. => .error "option test without G form in the 104 lowering"

/-- The `ensures` conjunction in `einzahlen` (empty is `.tru`,
    like the exporter's conjunction). -/
def lowerSichertListeEin (tabs : List UTab) (names : List String)
    (types : List Ty) : List UEns → Except String UEnsEin
  | [] => .ok Expr.tru
  | e :: rest =>
    match lowerSichertEin tabs names types e with
    | .error err => .error err
    | .ok x =>
      match lowerSichertListeEin tabs names types rest with
      | .error err => .error err
      | .ok y =>
        match y with
        | Expr.tru => .ok x
        | _ => .ok (Expr.and x y)

/-- A value at an expected range in `einzahlen` (the
    `tr_value`/`fit` of `lean_g.rs`: literals widen with their
    proofs from the data, parameters widen from their recorded
    range, slot reads widen from the field range). -/
def lowerWertEin (tabs : List UTab) (names : List String)
    (types : List Ty) (lo hi : Int) : USide →
    Except String (Expr G104_referenz.gD UCtxEin ULEin (.int lo hi))
  | .lit n =>
    if h1 : lo ≤ n then
      if h2 : n ≤ hi then .ok (Expr.widen h1 h2 (Expr.lit n))
      else .error "literal outside"
    else .error "literal outside"
  | .param p =>
    match uStelle ["k", "i", "b"] p with
    | .error e => .error e
    | .ok j =>
      match names[j]?, types[j]? with
      | .some q, .some (Ty.int a b) =>
        if !strEq q p then .error "parameter swapped"
        else
          match varNumEin j (.int a b) with
          | .error e => .error e
          | .ok v =>
            if h1 : lo ≤ a then
              if h2 : b ≤ hi then .ok (Expr.widen h1 h2 (Expr.var v))
              else .error "parameter outside"
            else .error "parameter outside"
      | _, _ => .error "parameter without G form"
  | s =>
    match lowerSeiteEin tabs names types s with
    | .error e => .error e
    | .ok t =>
      if h1 : lo ≤ t.range.1 then
        if h2 : t.range.2 ≤ hi then .ok (Expr.widen h1 h2 t.term)
        else .error "value outside"
      else .error "value outside"

/-- The statement type of `einzahlen` (all straight-line steps
    keep the held resources). -/
abbrev UStmtEin :=
  Stmt G104_referenz.gD (vertragVon G104_referenz.gD G104_referenz.g_einzahlen) false UCtxEin ULEin ULEin

/-- A slot write in `einzahlen` (the assignment arm of
    `tr_stmt`; through a pointer it needs the `rw` right). -/
def lowerAssignEin (tabs : List UTab) (names : List String)
    (types : List Ty) : String → String → UIdx → USide →
    Except String UStmtEin
  | b, f, ix, v =>
    if !((strEq b "k" || strEq b "Konto") && strEq f "stand") then
      .error "write place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerWertEin tabs names types 0 100 v with
        | .error e => .error e
        | .ok w =>
          match lowerIdxEin ix with
          | .error e => .error e
          | .ok i =>
            if strEq b "k" then
              .ok (Stmt.assignThru (Expr.var Var.here)
                G104_referenz.GTab.Konto rfl
                G104_referenz.GKontoFeld.stand i w (by decide)
                G104_referenz.gDarf_einzahlen_Konto)
            else
              .ok (Stmt.assignSlot G104_referenz.GTab.Konto
                G104_referenz.GKontoFeld.stand i w
                (by decide) G104_referenz.gDarf_einzahlen_Konto)

/-- The arguments of a `lies` call in `einzahlen`: the fresh
    `rw`-to-`r` pointer and the index (the `tr_arg` of
    `lean_g.rs` for this pair; any other shape is an explicit
    error). -/
def lowerArgsLies (tabs : List UTab) (names : List String)
    (types : List Ty) : List UArg →
    Except String (Args G104_referenz.gD UCtxEin ULEin (G104_referenz.gD.params G104_referenz.g_lies))
  | [.freshPtr "Konto" false, .val (.param "i")] =>
    match names[1]?, types[1]? with
    | .some q, .some (Ty.int 0 1) =>
      if !strEq q "i" then .error "argument swapped"
      else
        match tabs.find? (fun x => strEq x.name "Konto") with
        | .none => .error "table unknown: Konto"
        | .some tb =>
          if tb.count != 2 then .error "count foreign"
          else
            .ok (Args.cons (Expr.ptrOf G104_referenz.GTab.Konto 0 rfl false)
              (Args.cons (Expr.var (Var.there Var.here)) Args.nil))
    | _, _ => .error "argument without G form"
  | _ => .error "argument without G form"

/-- Straight-line steps after a `lies` call: assignments and
    the return only (a second call has no `RufPasst` proof in
    this lowering -- an explicit error). -/
def lowerNachLies (tabs : List UTab) (names : List String)
    (types : List Ty) : List UStmt → URet →
    Except String
      (Endblock G104_referenz.gD (vertragVon G104_referenz.gD G104_referenz.g_einzahlen) false UCtxEin
        (nach G104_referenz.gD G104_referenz.g_lies ULEin))
  | .assignGlob .. :: _, _ | .assignGlobB .. :: _, _ | .storeAtom .. :: _, _ | .storeAtomB .. :: _, _ =>
    .error "static without G form in the 104 lowering"
  | .assignRef .. :: _, _ => .error "reference without G form in the 104 lowering"
  | .bindW .. :: _, _ | .assignGlobO .. :: _, _ | [], .wert _ => .error "aggregate without G form in the 104 lowering"
  | .tausch .. :: _, _ => .error "exchange without G form in the 104 lowering"
  | .ifEnde .. :: _, _ | [], .keins => .error "terminal if without G form in the 104 lowering"
  | [], .empty => .ok (.ret .empty (List.Perm.refl _))
  | [], .bool _ | [], .opt _ | [], .why _ | [], .sum _ | [], .grund _ => .error "truth value returned without result"
  | [], .val _ => .error "return with value without result"
  | .assign b f ix v :: rest, r =>
    match lowerAssignEin tabs names types b f ix v with
    | .error e => .error e
    | .ok s =>
      match lowerNachLies tabs names types rest r with
      | .error e => .error e
      | .ok t => .ok (.cons s t)
  | .assignTab b f ix v :: rest, r =>
    match lowerAssignEin tabs names types b f ix v with
    | .error e => .error e
    | .ok s =>
      match lowerNachLies tabs names types rest r with
      | .error e => .error e
      | .ok t => .ok (.cons s t)
  | .assignB .. :: _, _ | .assignTabB .. :: _, _ | .lockBeg _ :: _, _ | .blkEnd :: _, _ | .bind .. :: _, _ | .bindCall .. :: _, _ | .axCall .. :: _, _ | .bindAx .. :: _, _ | .narrowBeg .. :: _, _ | .retryBeg .. :: _, _ | .foreverBeg .. :: _, _ | .bindOpt .. :: _, _ | .assignOpt .. :: _, _ | .assignTabOpt .. :: _, _ | .matchBeg .. :: _, _ | .startS :: _, _ | .allocBeg .. :: _, _ | .bindElse .. :: _, _ | .matchWhyBeg .. :: _, _ | .bindSum .. :: _, _ | .matchTagBeg .. :: _, _ | .bindAxElse .. :: _, _ | .bindB .. :: _, _ | .bindMut .. :: _, _ | .setVar .. :: _, _ | .setVarB .. :: _, _ | .ifBeg _ :: _, _ | .ifElse :: _, _
    | .loopBeg .. :: _, _ | .ret _ :: _, _ | .leave _ :: _, _ | .next _ :: _, _
    | .regRead .. :: _, _ | .regReadElse .. :: _, _ | .regWrite .. :: _, _ | .regWriteB .. :: _, _ | .awaitBind .. :: _, _
    | .bindFnref .. :: _, _ | .callInd .. :: _, _ | .bindCallInd .. :: _, _ | .shiftTab .. :: _, _ =>
    .error "statement without G form in the 104 lowering"
  | .call _ _ :: _, _ => .error "call after call without G form"

/-- The body of `einzahlen`: straight-line writes, at most
    one direct `lies` call, and the trailing return (the
    `tr_body` of `lean_g.rs`). -/
def lowerSaetzeEin (tabs : List UTab) (names : List String)
    (types : List Ty) : List UStmt → URet → Except String UKoerpEin
  | .assignGlob .. :: _, _ | .assignGlobB .. :: _, _ | .storeAtom .. :: _, _ | .storeAtomB .. :: _, _ =>
    .error "static without G form in the 104 lowering"
  | .assignRef .. :: _, _ => .error "reference without G form in the 104 lowering"
  | .bindW .. :: _, _ | .assignGlobO .. :: _, _ | [], .wert _ => .error "aggregate without G form in the 104 lowering"
  | .tausch .. :: _, _ => .error "exchange without G form in the 104 lowering"
  | .ifEnde .. :: _, _ | [], .keins => .error "terminal if without G form in the 104 lowering"
  | [], .empty => .ok (.ret .empty (List.Perm.refl _))
  | [], .bool _ | [], .opt _ | [], .why _ | [], .sum _ | [], .grund _ => .error "truth value returned without result"
  | [], .val _ => .error "return with value without result"
  | .assign b f ix v :: rest, r =>
    match lowerAssignEin tabs names types b f ix v with
    | .error e => .error e
    | .ok s =>
      match lowerSaetzeEin tabs names types rest r with
      | .error e => .error e
      | .ok t => .ok (.cons s t)
  | .assignTab b f ix v :: rest, r =>
    match lowerAssignEin tabs names types b f ix v with
    | .error e => .error e
    | .ok s =>
      match lowerSaetzeEin tabs names types rest r with
      | .error e => .error e
      | .ok t => .ok (.cons s t)
  | .call "lies" args :: rest, r =>
    match lowerArgsLies tabs names types args with
    | .error e => .error e
    | .ok a =>
      match lowerNachLies tabs names types rest r with
      | .error e => .error e
      | .ok t =>
        .ok (.cons (.call G104_referenz.g_lies a G104_referenz.gHp_einzahlen_lies rfl) t)
  | .assignB .. :: _, _ | .assignTabB .. :: _, _ | .lockBeg _ :: _, _ | .blkEnd :: _, _ | .bind .. :: _, _ | .bindCall .. :: _, _ | .axCall .. :: _, _ | .bindAx .. :: _, _ | .narrowBeg .. :: _, _ | .retryBeg .. :: _, _ | .foreverBeg .. :: _, _ | .bindOpt .. :: _, _ | .assignOpt .. :: _, _ | .assignTabOpt .. :: _, _ | .matchBeg .. :: _, _ | .startS :: _, _ | .allocBeg .. :: _, _ | .bindElse .. :: _, _ | .matchWhyBeg .. :: _, _ | .bindSum .. :: _, _ | .matchTagBeg .. :: _, _ | .bindAxElse .. :: _, _ | .bindB .. :: _, _ | .bindMut .. :: _, _ | .setVar .. :: _, _ | .setVarB .. :: _, _ | .ifBeg _ :: _, _ | .ifElse :: _, _
    | .loopBeg .. :: _, _ | .ret _ :: _, _ | .leave _ :: _, _ | .next _ :: _, _
    | .regRead .. :: _, _ | .regReadElse .. :: _, _ | .regWrite .. :: _, _ | .regWriteB .. :: _, _ | .awaitBind .. :: _, _
    | .bindFnref .. :: _, _ | .callInd .. :: _, _ | .bindCallInd .. :: _, _ | .shiftTab .. :: _, _ =>
    .error "statement without G form in the 104 lowering"
  | .call _ _ :: _, _ => .error "call without G form"

/-! ## Lowering `lies` -/

/-- The body context of `lies`: its parameters. -/
abbrev UCtxLies := G104_referenz.gCtx_lies

/-- The held resources of `lies`. -/
abbrev ULLies := G104_referenz.gL_lies

/-- The `ensures` context of `lies`: the result first. -/
abbrev UCtxEnsLies :=
  ErgCtx (G104_referenz.gD.params G104_referenz.g_lies)
    (G104_referenz.gD.erg G104_referenz.g_lies)

/-- The `ensures` type of `lies`. -/
abbrev UEnsLies :=
  Expr G104_referenz.gD UCtxEnsLies
    (vertragVon G104_referenz.gD G104_referenz.g_lies).ende .bool

/-- The body type of `lies`. -/
abbrev UKoerpLies :=
  Endblock G104_referenz.gD (vertragVon G104_referenz.gD G104_referenz.g_lies)
    false G104_referenz.gCtx_lies G104_referenz.gL_lies

/-- A parameter variable of `lies` by position and type. -/
def varNumLies : (j : Nat) → (τ : Ty) → Except String (Var UCtxLies τ)
  | 0, .ptr 0 false => .ok Var.here
  | 1, .int 0 1 => .ok (Var.there Var.here)
  | _, _ => .error "parameter without G form"

/-- A variable of the `lies` `ensures` context: the result or
    a parameter (positions are the known signature). -/
def varEnsLies : (j : Nat) → (τ : Ty) →
    Except String (Var UCtxEnsLies τ)
  | 0, .int 0 100 => .ok Var.here
  | 1, .ptr 0 false => .ok (Var.there Var.here)
  | 2, .int 0 1 => .ok (Var.there (Var.there Var.here))
  | _, _ => .error "parameter without G form"

/-- One side in the `lies` body, with its range. -/
structure USeiteL where
  range : Int × Int
  term : Expr G104_referenz.gD UCtxLies ULLies (.int range.1 range.2)

/-- An index into `Konto` in `lies`. -/
def lowerIdxLies : UIdx →
    Except String
      (Expr G104_referenz.gD UCtxLies ULLies
        (.index (G104_referenz.gD.count G104_referenz.GTab.Konto)))
  | .param "i" => .ok (Expr.var (Var.there Var.here))
  | .lit n =>
    if h1 : 0 ≤ n then
      if h2 : n ≤ 1 then .ok (Expr.widen h1 h2 (Expr.lit n))
      else .error "index outside count"
    else .error "index outside count"
  | _ => .error "index without G form"

def lowerSeiteLies (tabs : List UTab) (names : List String)
    (types : List Ty) : USide → Except String USeiteL
  | .lit n => .ok { range := (n, n), term := Expr.lit n }
  | .param p =>
    match uStelle ["k", "i"] p with
    | .error e => .error e
    | .ok j =>
      match names[j]?, types[j]? with
      | .some q, .some (Ty.int lo hi) =>
        if !strEq q p then .error "parameter swapped"
        else
          match varNumLies j (.int lo hi) with
          | .error e => .error e
          | .ok v => .ok { range := (lo, hi), term := Expr.var v }
      | _, _ => .error "parameter without G form"
  | .slot b f ix =>
    if !(strEq b "k" && strEq f "stand") then .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100),
                term := Expr.thru (Expr.var Var.here)
                  G104_referenz.GTab.Konto rfl
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | .tab b f ix =>
    if !(strEq b "Konto" && strEq f "stand") then .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100),
                term := Expr.slot G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | _ => .error "side in a body without G form"

/-- One side in the `lies` `ensures`, with its range (`result`
    travels here; the recorded result range must be the
    exporter's `(0, 100)`). -/
structure USeiteE where
  range : Int × Int
  term : Expr G104_referenz.gD UCtxEnsLies ULLies (.int range.1 range.2)

def lowerSeiteEnsLies (tabs : List UTab) (names : List String)
    (types : List Ty) (res : Option (Int × Int)) :
    USide → Except String USeiteE
  | .glob _ => .error "static without G form in the 104 lowering"
  | .refSlot .. => .error "reference without G form in the 104 lowering"
  | .idx .. | .len _ | .text _ | .arrNil | .arrCons .. | .upd .. | .typed .. => .error "aggregate without G form in the 104 lowering"
  | .eng .. => .error "narrowing without G form in the 104 lowering"
  | .lit n => .ok { range := (n, n), term := Expr.lit n }
  | .param p =>
    match uStelle ["k", "i"] p with
    | .error e => .error e
    | .ok j =>
      match names[j]?, types[j]? with
      | .some q, .some (Ty.int lo hi) =>
        if !strEq q p then .error "parameter swapped"
        else
          match varEnsLies (j + 1) (.int lo hi) with
          | .error e => .error e
          | .ok v => .ok { range := (lo, hi), term := Expr.var v }
      | _, _ => .error "parameter without G form"
  | .slot b f ix =>
    if !(strEq b "k" && strEq f "stand") then .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEnsLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100),
                term := Expr.thru (Expr.var (Var.there Var.here))
                  G104_referenz.GTab.Konto rfl
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | .tab b f ix =>
    if !(strEq b "Konto" && strEq f "stand") then .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEnsLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100),
                term := Expr.slot G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | .old b f ix =>
    if !((strEq b "k" || strEq b "Konto") && strEq f "stand") then
      .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEnsLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100),
                term := Expr.oldS G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | .erg =>
    match res with
    | .some (0, 100) => .ok { range := (0, 100), term := Expr.var Var.here }
    | _ => .error "result range foreign"
  | .add .. | .sub .. | .mul .. | .conv .. | .band .. | .bor .. | .bxor .. | .div .. | .rem .. | .shl .. | .shr .. | .neg .. =>
    .error "arithmetic without G form in the 104 lowering"
where
  lowerIdxEnsLies : UIdx →
    Except String
      (Expr G104_referenz.gD UCtxEnsLies ULLies
        (.index (G104_referenz.gD.count G104_referenz.GTab.Konto)))
    | .param "i" => .ok (Expr.var (Var.there (Var.there Var.here)))
    | .lit n =>
      if h1 : 0 ≤ n then
        if h2 : n ≤ 1 then .ok (Expr.widen h1 h2 (Expr.lit n))
        else .error "index outside count"
      else .error "index outside count"
    | _ => .error "index without G form"

/-- One comparison and one `ensures` predicate in `lies`. -/
def lowerVglLies (tabs : List UTab) (names : List String)
    (types : List Ty) (res : Option (Int × Int)) :
    String → USide → USide → Except String UEnsLies
  | op, a, b =>
    match lowerSeiteEnsLies tabs names types res a with
    | .error e => .error e
    | .ok s1 =>
      match lowerSeiteEnsLies tabs names types res b with
      | .error e => .error e
      | .ok s2 =>
        match op with
        | "==" => .ok (Expr.eq s1.term s2.term)
        | "!=" => .ok (Expr.not (Expr.eq s1.term s2.term))
        | "<" => .ok (Expr.lt s1.term s2.term)
        | "<=" => .ok (Expr.le s1.term s2.term)
        | ">" => .ok (Expr.lt s2.term s1.term)
        | ">=" => .ok (Expr.le s2.term s1.term)
        | _ => .error "operator without G form"

def lowerSichertLies (tabs : List UTab) (names : List String)
    (types : List Ty) (res : Option (Int × Int)) :
    UEns → Except String UEnsLies
  | .globB _ | .var _ | .ergB => .error "static without G form in the 104 lowering"
  | .alle .. | .einige .. => .error "quantifier without G form in the 104 lowering"
  | .cmp op a b => lowerVglLies tabs names types res op a b
  | .tru => .ok Expr.tru
  | .fls => .ok Expr.fls
  | .and a b =>
    match lowerSichertLies tabs names types res a with
    | .error e => .error e
    | .ok x =>
      match lowerSichertLies tabs names types res b with
      | .error e => .error e
      | .ok y => .ok (Expr.and x y)
  | .or a b =>
    match lowerSichertLies tabs names types res a with
    | .error e => .error e
    | .ok x =>
      match lowerSichertLies tabs names types res b with
      | .error e => .error e
      | .ok y => .ok (Expr.or x y)
  | .not a =>
    match lowerSichertLies tabs names types res a with
    | .error e => .error e
    | .ok x => .ok (Expr.not x)
  | .slotB .. | .tabB .. => .error "bool place without G form in the 104 lowering"
  | .istSome .. => .error "option test without G form in the 104 lowering"

def lowerSichertListeLies (tabs : List UTab) (names : List String)
    (types : List Ty) (res : Option (Int × Int)) :
    List UEns → Except String UEnsLies
  | [] => .ok Expr.tru
  | e :: rest =>
    match lowerSichertLies tabs names types res e with
    | .error err => .error err
    | .ok x =>
      match lowerSichertListeLies tabs names types res rest with
      | .error err => .error err
      | .ok y =>
        match y with
        | Expr.tru => .ok x
        | _ => .ok (Expr.and x y)

/-- A value at an expected range in the `lies` body. -/
def lowerWertLies (tabs : List UTab) (names : List String)
    (types : List Ty) (lo hi : Int) : USide →
    Except String (Expr G104_referenz.gD UCtxLies ULLies (.int lo hi))
  | .lit n =>
    if h1 : lo ≤ n then
      if h2 : n ≤ hi then .ok (Expr.widen h1 h2 (Expr.lit n))
      else .error "literal outside"
    else .error "literal outside"
  | .param p =>
    match uStelle ["k", "i"] p with
    | .error e => .error e
    | .ok j =>
      match names[j]?, types[j]? with
      | .some q, .some (Ty.int a b) =>
        if !strEq q p then .error "parameter swapped"
        else
          match varNumLies j (Ty.int a b) with
          | .error e => .error e
          | .ok v =>
            if h1 : lo ≤ a then
              if h2 : b ≤ hi then .ok (Expr.widen h1 h2 (Expr.var v))
              else .error "parameter outside"
            else .error "parameter outside"
      | _, _ => .error "parameter without G form"
  | s =>
    match lowerSeiteLies tabs names types s with
    | .error e => .error e
    | .ok t =>
      if h1 : lo ≤ t.range.1 then
        if h2 : t.range.2 ≤ hi then .ok (Expr.widen h1 h2 t.term)
        else .error "value outside"
      else .error "value outside"

/-- The body of `lies`: empty with a trailing value return
    (a read-only function; statements have no lowered proofs
    here -- an explicit error). A same-range slot read returns
    bare (the no-op arm of the exporter's `fit`); every other
    value widens. -/
def lowerSaetzeLies (tabs : List UTab) (names : List String)
    (types : List Ty) : List UStmt → URet → Except String UKoerpLies
  | [], .val (.slot b f ix) =>
    if !(strEq b "k" && strEq f "stand") then
      .error "return without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxLies ix with
        | .error e => .error e
        | .ok i =>
          .ok (Endblock.ret
            (ErgExpr.val (Expr.thru (Expr.var Var.here)
              G104_referenz.GTab.Konto rfl
              G104_referenz.GKontoFeld.stand i
              G104_referenz.gDarf_lies_Konto))
            (List.Perm.refl _))
  | [], .val (.tab b f ix) =>
    if !(strEq b "Konto" && strEq f "stand") then
      .error "return without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxLies ix with
        | .error e => .error e
        | .ok i =>
          .ok (Endblock.ret
            (ErgExpr.val (Expr.slot G104_referenz.GTab.Konto
              G104_referenz.GKontoFeld.stand i
              G104_referenz.gDarf_lies_Konto))
            (List.Perm.refl _))
  | [], .val s =>
    match lowerWertLies tabs names types 0 100 s with
    | .error e => .error e
    | .ok v => .ok (Endblock.ret (ErgExpr.val v) (List.Perm.refl _))
  | _, _ => .error "lies body without G form"

/-! ## Program assembly -/

/-- Assemble the lowered pieces to a program (same shape as
    `gP`: no contract content in `requires`, per-function
    `ensures` and bodies). -/
def uProgBaue (e1 : UEnsEin) (e2 : UEnsLies) (b1 : UKoerpEin)
    (b2 : UKoerpLies) : Programm G104_referenz.gD where
  invariante := fun i => nomatch i
  requires := fun _ => Expr.tru
  ensures
    | G104_referenz.GFn.einzahlen => e1
    | G104_referenz.GFn.lies => e2
  rumpf
    | G104_referenz.GFn.einzahlen => b1
    | G104_referenz.GFn.lies => b2

/-- The lowered program: the two functions assembled to the
    exporter's `gP`/`gFs` (signatures stay in `gD`; the
    elaborated signature data is checked against `gD` entry by
    entry, so a divergent `UFn` is an explicit error). -/
def lowerProg : UProg →
    Except String
      (Programm G104_referenz.gD × List G104_referenz.GFn)
  | { tabs := [tab], locks := [lock], fns := [fe, fl], roots := [], hands := [], globs := [], axs := [], annahmen := [], gestartet := [], whys := [], sums := [], regs := [], invs := [], zustaende := [], regiert := [], ptrs := [], ptrKeys := [] } =>
    if !(strEq tab.name "Konto" && strEq lock.name "M" &&
        strEq fe.name "einzahlen" && strEq fl.name "lies") then
      .error "program shape without G form"
    else if !(decide (fe.params.map (·.2) =
        G104_referenz.gD.params G104_referenz.g_einzahlen)) then
      .error "signature of einzahlen foreign"
    else if !(decide (fl.params.map (·.2) =
        G104_referenz.gD.params G104_referenz.g_lies)) then
      .error "signature of lies foreign"
    else if !(decide (fe.res = none)) then
      .error "result of einzahlen foreign"
    else if !(decide (fl.res = some (0, 100))) then
      .error "result of lies foreign"
    else if !(fe.held == ["M"] && fl.held == ["M"]) then
      .error "held set foreign"
    else if !(fe.puts == ["Konto"] && fl.puts == []) then
      .error "write set foreign"
    else
      let pnamenEin := fe.params.map (·.1)
      let ptypenEin := fe.params.map (·.2)
      match lowerSichertListeEin [tab] pnamenEin ptypenEin fe.gives with
      | .error e => .error e
      | .ok e1 =>
        let pnamenLies := fl.params.map (·.1)
        let ptypenLies := fl.params.map (·.2)
        match lowerSichertListeLies [tab] pnamenLies ptypenLies
            fl.res fl.gives with
        | .error e => .error e
        | .ok e2 =>
          match lowerSaetzeEin [tab] pnamenEin ptypenEin
              fe.body fe.ret with
          | .error e => .error e
          | .ok b1 =>
            match lowerSaetzeLies [tab] pnamenLies ptypenLies
                fl.body fl.ret with
            | .error e => .error e
            | .ok b2 =>
              .ok (uProgBaue e1 e2 b1 b2,
                [G104_referenz.GFn.einzahlen, G104_referenz.GFn.lies])
  | _ => .error "program shape without G form"

/-! ## The 104 instance: tokens -/

/-- The token list of `beispiele/104-referenz.gab` (comment-free;
    `u104lex` checks it against the lexer). -/
def tt104 : List Token :=
  [.wort "module", .ident "beispiel", .zeichen "::", .ident "referenz",
   .zeichen "{",
   .wort "const", .ident "NKONTO", .zeichen ":", .wort "u32",
   .zeichen "=", .num 2, .zeichen ";",
   .wort "type", .ident "Betrag", .zeichen "=",
   .wort "u32", .wort "in", .num 0, .zeichen "..", .num 10,
   .zeichen ";",
   .wort "type", .ident "Stand", .zeichen "=",
   .wort "u32", .wort "in", .num 0, .zeichen "..", .num 100,
   .zeichen ";",
   .wort "table", .ident "Konto", .wort "count", .ident "NKONTO",
   .zeichen "{", .wort "slot", .zeichen "{", .ident "stand",
   .zeichen ":", .ident "Stand", .zeichen ",", .zeichen "}",
   .zeichen "}",
   .wort "lock", .ident "M", .wort "protects", .zeichen "{",
   .ident "stand", .zeichen "}", .wort "rank", .num 0,
   .wort "held", .zeichen "<=", .num 50, .wort "ops", .zeichen ";",
   .wort "impl", .wort "fn", .ident "einzahlen", .zeichen "(",
   .ident "k", .zeichen ":", .wort "ptr", .zeichen "<",
   .wort "normal", .zeichen ",", .wort "rw", .zeichen ">",
   .ident "Konto", .zeichen ",",
   .ident "i", .zeichen ":", .wort "index", .wort "into",
   .ident "Konto", .zeichen ",",
   .ident "b", .zeichen ":", .ident "Betrag", .zeichen ")",
   .wort "requires", .ident "Held", .zeichen "(", .ident "M",
   .zeichen ")",
   .wort "ensures", .wort "old", .zeichen "(", .ident "k",
   .zeichen ".", .wort "slots", .zeichen "[", .ident "i",
   .zeichen "]", .zeichen ".", .ident "stand", .zeichen ")",
   .zeichen "<=", .ident "k", .zeichen ".", .wort "slots",
   .zeichen "[", .ident "i", .zeichen "]", .zeichen ".",
   .ident "stand",
   .wort "effects", .zeichen "{", .wort "reads", .ident "k",
   .zeichen ".", .wort "slots", .zeichen ",", .wort "writes",
   .ident "k", .zeichen ".", .wort "slots", .zeichen ",",
   .wort "locks", .ident "M", .zeichen "}",
   .wort "costs", .zeichen "<=", .num 16, .wort "ops",
   .zeichen "{", .ident "k", .zeichen ".", .wort "slots",
   .zeichen "[", .ident "i", .zeichen "]", .zeichen ".",
   .ident "stand", .zeichen "=", .num 100, .zeichen ";",
   .ident "lies", .zeichen "(", .ident "k", .zeichen ",",
   .ident "i", .zeichen ")", .zeichen ";", .zeichen "}",
   .wort "impl", .wort "fn", .ident "lies", .zeichen "(",
   .ident "k", .zeichen ":", .wort "ptr", .zeichen "<",
   .wort "normal", .zeichen ",", .wort "r", .zeichen ">",
   .ident "Konto", .zeichen ",",
   .ident "i", .zeichen ":", .wort "index", .wort "into",
   .ident "Konto", .zeichen ")", .zeichen "->", .ident "Stand",
   .wort "requires", .ident "Held", .zeichen "(", .ident "M",
   .zeichen ")",
   .wort "ensures", .wort "result", .zeichen "==", .ident "k",
   .zeichen ".", .wort "slots", .zeichen "[", .ident "i",
   .zeichen "]", .zeichen ".", .ident "stand",
   .wort "effects", .zeichen "{", .wort "reads", .ident "k",
   .zeichen ".", .wort "slots", .zeichen ",", .wort "locks",
   .ident "M", .zeichen "}",
   .wort "costs", .zeichen "<=", .num 8, .wort "ops",
   .zeichen "{", .wort "return", .ident "k", .zeichen ".",
   .wort "slots", .zeichen "[", .ident "i", .zeichen "]",
   .zeichen ".", .ident "stand", .zeichen ";", .zeichen "}",
   .zeichen "}", .ende]

/-- The comment-free 104 source text, pinned as CHARACTERS in short
    pieces. One 669-byte `String` literal costs the kernel 8,96 GB and
    55 s here (measured 2026-09-15); the pieces cost a fraction of it, and
    `lex_ofList` carries the pin to the `String` without running Lean 4.33's
    UTF-8 decoder at all. See O13 and `Parser/Lexer.lean`. -/
def srcZeilen104K : List (List Char) :=
  ["module beispiel::referenz { const NKONTO ".toList,
   ": u32 = 2; type Betrag = u32 in 0 .. 10; ".toList,
   "type Stand = u32 in 0 .. 100; table ".toList,
   "Konto count NKONTO { slot { stand : ".toList,
   "Stand, } } lock M protects { stand } ".toList,
   "rank 0 held <= 50 ops; impl fn ".toList,
   "einzahlen(k : ptr<normal, rw> Konto, i : ".toList,
   "index into Konto, b : Betrag) requires ".toList,
   "Held(M) ensures old(k.slots[i].stand) <= ".toList,
   "k.slots[i].stand effects { reads ".toList,
   "k.slots, writes k.slots, locks M } costs ".toList,
   "<= 16 ops { k.slots[i].stand = 100; ".toList,
   "lies(k, i); } impl fn lies(k : ".toList,
   "ptr<normal, r> Konto, i : index into ".toList,
   "Konto) -> Stand requires Held(M) ensures ".toList,
   "result == k.slots[i].stand effects { ".toList,
   "reads k.slots, locks M } costs <= 8 ops ".toList,
   "{ return k.slots[i].stand; } }".toList]

/-- The same text as characters. -/
def srcQuelle104K : List Char := srcZeilen104K.flatten

set_option maxHeartbeats 3200000 in
/-- The comment-free 104 text lexes to `tt104`, over the characters. -/
theorem u104lexL : lexL srcQuelle104K = .ok tt104 := by
  decide

/-- The same, about the `String` -- a rewrite, not a reduction (O13). -/
theorem u104lex : lex (String.ofList srcQuelle104K) = .ok tt104 := by
  rw [lex_ofList]
  exact u104lexL

/-! ## The 104 instance: parse tree -/

/-- The slot read `k.slots[i].stand` shared by every 104
    contract and body (see `sonde04`/`sonde05`). -/
def uStand104 : SExpr :=
  .field (.index (.field (.variable "k") "slots") (.variable "i")) "stand"

/-- The parsed surface tree of `beispiele/104-referenz.gab`
    (`u104parse` checks it against the reader). -/
def items104 : List SItemTief :=
  [.modT "beispiel::referenz" [
    .constT "NKONTO" (.atom "u32") (.one (.lit 2)),
    .typeT [] "Betrag" [] []
      (.some (.range (.atom "u32") (.lit 0) (.lit 10) false)),
    .typeT [] "Stand" [] []
      (.some (.range (.atom "u32") (.lit 0) (.lit 100) false)),
    .tableT "Konto" .none (.some (.variable "NKONTO")) .none .none false
      [.tSlot [{ fname := "stand", ftyp := .atom "Stand",
                  pos := .none, bezug := .none, wo := .none,
                  reserviert := false, byOps := false }]],
    .lockT "M" [.variable "stand"] (.lit 0)
      (.some (.lit 50)) .none .none .none,
    .fnT
      { art := "impl", name := "einzahlen",
        params := [("k", .ptr "normal" "rw" (.atom "Konto")),
          ("i", .index false "Konto"), ("b", .atom "Betrag")],
        res := .none, fehler := .none,
        klauseln := [.needs (.call "Held" [.variable "M"]),
          .gives (.bin "<=" (.old uStand104) uStand104),
          .effs [.reads (.field (.variable "k") "slots"),
            .writes (.field (.variable "k") "slots"),
            .locks false (.variable "M")],
          .cost (.lit 16)] }
      (.block [.set uStand104 "=" (.lit 100),
        .call "lies" [.variable "k", .variable "i"]] .none),
    .fnT
      { art := "impl", name := "lies",
        params := [("k", .ptr "normal" "r" (.atom "Konto")),
          ("i", .index false "Konto")],
        res := .some (.atom "Stand"), fehler := .none,
        klauseln := [.needs (.call "Held" [.variable "M"]),
          .gives (.bin "==" .res uStand104),
          .effs [.reads (.field (.variable "k") "slots"),
            .locks false (.variable "M")],
          .cost (.lit 8)] }
      (.block [] (.some (.ret (.some uStand104))))]]

theorem u104parse : beqTopTief (parseTopTief tt104) (.ok items104) = true := by
  decide

/-! ## The 104 instance: elaboration -/

/-- The elaborated 104 program (`u104elab` checks it against
    the elaborator). -/
def uExp104 : UProg :=
  { tabs := [{ name := "Konto", count := 2,
                   cols := [("stand", (0, 100))] }],
    locks := [{ name := "M", rank := 0, guard := ["Konto"] }],
    fns := [
      { name := "einzahlen",
        params := [("k", .ptr 0 true), ("i", .index 2),
          ("b", .int 0 10)],
        kinds := [.ptr 0 true, .index 0, .int],
        res := .none,
        held := ["M"], puts := ["Konto"],
        gives := [.cmp "<="
          (.old "k" "stand" (.param "i"))
          (.slot "k" "stand" (.param "i"))],
        body := [.assign "k" "stand" (.param "i") (.lit 100),
          .call "lies" [.freshPtr "Konto" false,
            .val (.param "i")]],
        ret := .empty, boden := some 1 },
      { name := "lies",
        params := [("k", .ptr 0 false), ("i", .index 2)],
        kinds := [.ptr 0 false, .index 0],
        res := .some (0, 100),
        held := ["M"], puts := [],
        gives := [.cmp "==" .erg
          (.slot "k" "stand" (.param "i"))],
        body := [],
        ret := .val (.slot "k" "stand" (.param "i")), boden := some 1 }] }

/-! ## Shape equality on U (Bool pins, like `beqTopTief`) -/

def beqIntPair : Int × Int → Int × Int → Bool
  | (a, b), (c, d) => a == c && b == d

def beqOptIntPair : Option (Int × Int) → Option (Int × Int) → Bool
  | none, none => true
  | some a, some b => beqIntPair a b
  | _, _ => false

def beqOptIntPairList : List (Option (Int × Int)) →
    List (Option (Int × Int)) → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqOptIntPair x y && beqOptIntPairList xs ys
  | _, _ => false

/-- Shape equality on `Ty` as a `Bool` (kernel evaluation,
    no nested `decide`). -/
def beqTy : Ty → Ty → Bool
  | .int a b, .int c d => a == c && b == d
  | .bool, .bool => true
  | .opt n, .opt m => n == m
  | .sum cs, .sum ds => beqOptIntPairList cs ds
  | .why n, .why m => n == m
  | .never, .never => true
  | .fl a b, .fl c d => beqIntPair a c && beqIntPair b d
  | .fnptr n, .fnptr m => n == m
  | .ptr t w, .ptr s v => t == s && w == v
  | _, _ => false

def beqUIdx : UIdx → UIdx → Bool
  | .lit a, .lit b => a == b
  | .param a, .param b => strEq a b
  | _, _ => false

def beqUSide : USide → USide → Bool
  | .lit a, .lit b => a == b
  | .param a, .param b => strEq a b
  | .slot a f x, .slot b g y =>
    strEq a b && strEq f g && beqUIdx x y
  | .tab a f x, .tab b g y =>
    strEq a b && strEq f g && beqUIdx x y
  | .old a f x, .old b g y =>
    strEq a b && strEq f g && beqUIdx x y
  | .erg, .erg => true
  | .glob a, .glob b => strEq a b
  | .add a b, .add c d | .sub a b, .sub c d | .mul a b, .mul c d
  | .band a b, .band c d | .bor a b, .bor c d | .bxor a b, .bxor c d
  | .div a b, .div c d | .rem a b, .rem c d | .shl a b, .shl c d | .shr a b, .shr c d =>
    beqUSide a c && beqUSide b d
  | .neg a, .neg b => beqUSide a b
  | .conv l h a, .conv l' h' b => l == l' && h == h' && beqUSide a b
  | _, _ => false

def beqUEns : UEns → UEns → Bool
  | .cmp o a b, .cmp p c d =>
    strEq o p && beqUSide a c && beqUSide b d
  | .tru, .tru => true
  | .fls, .fls => true
  | .and a b, .and c d => beqUEns a c && beqUEns b d
  | .or a b, .or c d => beqUEns a c && beqUEns b d
  | .not a, .not b => beqUEns a b
  | .slotB a f x, .slotB b g y | .tabB a f x, .tabB b g y =>
    strEq a b && strEq f g && beqUIdx x y
  | .globB a, .globB b => strEq a b
  | .alle t x p, .alle s y q | .einige t x p, .einige s y q => strEq t s && strEq x y && beqUEns p q
  | .ergB, .ergB => true
  | .istSome o m, .istSome p n => o == p && m == n
  | _, _ => false

def beqUEnsList : List UEns → List UEns → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUEns x y && beqUEnsList xs ys
  | _, _ => false

def beqUArg : UArg → UArg → Bool
  | .var a, .var b => strEq a b
  | .freshPtr a w, .freshPtr b v => strEq a b && w == v
  | .val a, .val b => beqUSide a b
  | .fnref a, .fnref b => strEq a b
  | _, _ => false

def beqUArgList : List UArg → List UArg → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUArg x y && beqUArgList xs ys
  | _, _ => false

def beqURet : URet → URet → Bool
  | .empty, .empty => true
  | .val a, .val b => beqUSide a b
  | .bool a, .bool b => beqUEns a b
  | _, _ => false

def beqUStmt : UStmt → UStmt → Bool
  | .assign a f x s, .assign b g y t =>
    strEq a b && strEq f g && beqUIdx x y && beqUSide s t
  | .assignTab a f x s, .assignTab b g y t =>
    strEq a b && strEq f g && beqUIdx x y && beqUSide s t
  | .assignB a f x s, .assignB b g y t | .assignTabB a f x s, .assignTabB b g y t =>
    strEq a b && strEq f g && beqUIdx x y && beqUEns s t
  | .assignGlob a s, .assignGlob b t => strEq a b && beqUSide s t
  | .assignGlobB a s, .assignGlobB b t => strEq a b && beqUEns s t
  | .storeAtom a s, .storeAtom b t => strEq a b && beqUSide s t
  | .storeAtomB a s, .storeAtomB b t => strEq a b && beqUEns s t
  | .call a xs, .call b ys => strEq a b && beqUArgList xs ys
  | .lockBeg a, .lockBeg b => strEq a b
  | .blkEnd, .blkEnd => true
  | .bind a d s, .bind b e t => strEq a b && beqOptIntPair d e && beqUSide s t
  | .ifBeg a, .ifBeg b => beqUEns a b
  | .ifElse, .ifElse => true
  | .loopBeg a t i, .loopBeg b u j => strEq a b && strEq t u && beqUEns i j
  | .ret a, .ret b => beqURet a b
  | .leave a, .leave b | .next a, .next b => strEq a b
  | .regRead a d r, .regRead b e s | .regReadElse a d r, .regReadElse b e s =>
    strEq a b && strEq d e && strEq r s
  | .regWrite d r v, .regWrite e s w => strEq d e && strEq r s && beqUSide v w
  | .regWriteB d r v, .regWriteB e s w => strEq d e && strEq r s && beqUEns v w
  | .shiftTab a f x s v w, .shiftTab b g y z v' w' =>
    strEq a b && strEq f g && beqUIdx x y && strEq s z && v == v' && w == w'
  | .awaitBind a g, .awaitBind b h => strEq a b && strEq g h
  | .bindFnref a g n, .bindFnref b h m => strEq a b && strEq g h && n == m
  | .callInd p f xs, .callInd q g ys => strEq p q && strEq f g && beqUArgList xs ys
  | .bindCallInd a p f xs, .bindCallInd b q g ys => strEq a b && strEq p q && strEq f g && beqUArgList xs ys
  | _, _ => false

def beqUStmtList : List UStmt → List UStmt → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUStmt x y && beqUStmtList xs ys
  | _, _ => false

def beqUParamArt : UParamArt → UParamArt → Bool
  | .ptr a w, .ptr b v => a == b && w == v
  | .index a, .index b => a == b
  | .int, .int => true
  | _, _ => false

def beqUParamArtList : List UParamArt → List UParamArt → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUParamArt x y && beqUParamArtList xs ys
  | _, _ => false

def beqTyParam : String × Ty → String × Ty → Bool
  | (a, x), (b, y) => strEq a b && beqTy x y

def beqTyParamList : List (String × Ty) → List (String × Ty) → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqTyParam x y && beqTyParamList xs ys
  | _, _ => false

def beqFeld : String × (Int × Int) → String × (Int × Int) → Bool
  | (a, x), (b, y) => strEq a b && beqIntPair x y

def beqFeldList : List (String × (Int × Int)) →
    List (String × (Int × Int)) → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqFeld x y && beqFeldList xs ys
  | _, _ => false

def beqStrList : List String → List String → Bool
  | [], [] => true
  | x :: xs, y :: ys => strEq x y && beqStrList xs ys
  | _, _ => false

def beqOptWeite : Option (Int × Int) → Option (Int × Int) → Bool
  | none, none => true
  | some a, some b => beqIntPair a b
  | _, _ => false

def beqUTab : UTab → UTab → Bool
  | a, b => strEq a.name b.name && a.count == b.count &&
    beqFeldList a.cols b.cols && beqStrList a.bools b.bools

def beqUTabList : List UTab → List UTab → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUTab x y && beqUTabList xs ys
  | _, _ => false

def beqULock : ULock → ULock → Bool
  | a, b => strEq a.name b.name && a.rank == b.rank &&
    beqStrList a.guard b.guard && a.masks == b.masks

def beqULockList : List ULock → List ULock → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqULock x y && beqULockList xs ys
  | _, _ => false

def beqUGlob : UGlob → UGlob → Bool
  | a, b => strEq a.name b.name && decide (a.ty = b.ty) && a.init == b.init && a.var == b.var && a.atomic == b.atomic

def beqUGlobList : List UGlob → List UGlob → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUGlob x y && beqUGlobList xs ys
  | _, _ => false

def beqUFn : UFn → UFn → Bool
  | a, b => strEq a.name b.name &&
    beqTyParamList a.params b.params &&
    beqUParamArtList a.kinds b.kinds &&
    beqOptWeite a.res b.res && a.resBool == b.resBool &&
    beqStrList a.held b.held && beqStrList a.puts b.puts && beqStrList a.gputs b.gputs &&
    beqUEnsList a.gives b.gives &&
    beqUStmtList a.body b.body && beqURet a.ret b.ret && a.boden == b.boden &&
    beqUEnsList a.needs b.needs

def beqUFnList : List UFn → List UFn → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUFn x y && beqUFnList xs ys
  | _, _ => false

def beqUProg : UProg → UProg → Bool
  | a, b => beqUTabList a.tabs b.tabs &&
    beqULockList a.locks b.locks && beqUFnList a.fns b.fns &&
    beqStrList a.roots b.roots && beqStrList a.hands b.hands && beqUGlobList a.globs b.globs &&
    decide (a.regs = b.regs)

/-- Shape equality on elaboration outcomes, as a `Bool`. -/
def beqElabU : Except String UProg → Except String UProg → Bool
  | .ok a, .ok b => beqUProg a b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

theorem u104elab : beqElabU (elabU items104) (.ok uExp104) = true := by
  decide

/-! ## The 104 instance: lowering pin, data, checks -/

/-- The lowered 104 program is the exporter's `gP`/`gFs`
    (definitional: proof irrelevance covers the proof terms). -/
theorem u104lower :
    lowerProg uExp104 =
      .ok (G104_referenz.gP, G104_referenz.gFs) := rfl

/-- Projections of the elaborated program (the left column of
    the data agreement below). -/
def uAnzahl104 (u : UProg) : Int :=
  match u.tabs with
  | [t] => t.count
  | _ => -1

def uWeite104 (u : UProg) : Int × Int :=
  match u.tabs with
  | [{ name := _, count := _, cols := [(_, w)], bools := _, arena := _, opts := _, shared := _, von := _, werte := _, wraps := _, sumNamen := _, sumFelder := _, kanten := _, idxNamen := _ }] => w
  | _ => (-1, -1)

def uRang104 (u : UProg) : Int :=
  match u.locks with
  | [l] => l.rank
  | _ => -1

def uFn104 (u : UProg) (n : String) : Option UFn :=
  u.fns.find? (fun f => strEq f.name n)

def uParams104 (u : UProg) (n : String) : List Ty :=
  match uFn104 u n with
  | .some f => f.params.map (·.2)
  | .none => []

def uHeld104 (u : UProg) (n : String) : List String :=
  match uFn104 u n with
  | .some f => f.held
  | .none => []

def uSchreibt104 (u : UProg) (n : String) : List String :=
  match uFn104 u n with
  | .some f => f.puts
  | .none => []

/-- Declaration data agreement, construct by construct: the
    elaborated data agrees with the exporter's `gD` (via
    `u104lower`) and with the hand translation's `r4D` -- same
    shape as `export104_data`. -/
theorem u104data :
    uAnzahl104 uExp104 = 2 ∧
    r4D.count () = 2 ∧
    uWeite104 uExp104 = (0, 100) ∧
    r4D.typ () () = .int 0 100 ∧
    uRang104 uExp104 = 0 ∧
    r4D.rang () = 0 ∧
    uParams104 uExp104 "einzahlen" = [.ptr 0 true, .index 2, .int 0 10] ∧
    r4D.params r4Ein = [.ptr 0 true, .index 2, .int 0 10] ∧
    uParams104 uExp104 "lies" = [.ptr 0 false, .index 2] ∧
    r4D.params r4Lies = [.ptr 0 false, .index 2] ∧
    uHeld104 uExp104 "einzahlen" = ["M"] ∧
    r4D.haelt r4Ein = [()] ∧
    uSchreibt104 uExp104 "einzahlen" = ["Konto"] ∧
    r4D.schreibt r4Ein () = true ∧
    uSchreibt104 uExp104 "lies" = [] ∧
    r4D.schreibt r4Lies () = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩

/-- The fragment check on the Lean-parsed program. -/
theorem u104fragment :
    (match lowerProg uExp104 with
     | .ok (P, fs) => programmImFragmentG P fs
     | .error _ => false) = true := by
  decide

/-- The footprint check on the Lean-parsed program. -/
theorem u104fuss :
    (match lowerProg uExp104 with
     | .ok (P, fs) => fussOrtGB P fs
     | .error _ => false) = true := by
  decide

end Gabbro.Grammatik.Parser.Uebersetze

/-
  CUTS: what is not proved here, and every deliberate
  difference against `crates/gabbro-check/src/lean_g.rs`.

  1. No single whole-pipeline `decide`: `lex` + `parseTopTief`
     + `elabU` + `lowerProg` in one kernel evaluation exceeds
     the heartbeat budget (the lane-135 finding), and
     `Except String UProg` has no `DecidableEq` instance for a
     propositional pin. The loop closes in stages instead,
     each with its own kernel check: `u104lex` (source to
     tokens), `u104parse` (tokens to `items104`, a `beqTopTief`
     pin like `tEnd`), `u104elab` (surface to `uExp104`, a
     `beqElabU` pin), `u104lower` (U to `(gP, gFs)` by `rfl`,
     proof irrelevance covering the proof terms). Chaining
     them is prose, as in `Export104.lean` (whose equality
     across declaration types is not even statable).
  2. `beqTy`/`beqUIdx`/`beqUSide`/`beqUEns`/`beqUArg`/
     `beqUStmt`/`beqURet`/`beqUTab`/`beqULock`/`beqUFn`/
     `beqUProg`/`beqElabU` are not proved sound or complete
     (the same cut as `beqSItemTief` in `ElementTief.lean`).
  3. The lowering targets the exporter's declaration universe
     `G104_referenz.gD` only: any table but `Konto`, any lock
     but `M`, any field but `stand`, any function but
     `einzahlen`/`lies` is an explicit error. The surface to U
     stage (`elabU`) is generic over the fragment; the proof
     carrying lowerers (`varNumEin`, `varNumLies`,
     `varEnsLies`, the `darf`/`RufPasst` witnesses) are keyed
     to the known signatures.
  4. Lowering restrictions beyond `elabU` (each an explicit
     error): at most one call per body and none after a call
     (no second `RufPasst` proof); `lies` bodies are empty
     with a value return (a statement in a read-only function
     has no lowered guard proof here); calls only to `lies`
     from `einzahlen` (the one named `RufPasst` proof);
     the `lies` return of a same-range slot read is direct
     (the no-op arm of the exporter's `fit`), every other
     value widens through `weiter`.
  5. Against `lean_g.rs`, deliberately: bare-word types are
     refused (no full-range rule; 104 needs none); slot
     extras (`@bitpos`, `offset_into`, `where`, `reserved`,
     `by ops`) are refused where the exporter ignores some;
     `use` items and nested modules are refused; an index
     literal is range-checked against `count`. Mirrored
     exactly: the refused clause rows, the one-directional
     `locks`-without-`Held` refusal, writes deduplication,
     the `rw`-to-`r` fresh pointer, the fall-off rule, and
     ignoring `reads`/`costs`/`section`/`payload`.
  6. The `u104fragment`/`u104fuss` match form carries a
     `false` error branch; `u104lower` shows it dead for 104.
  7. Corpus text is quoted comment-free (comments lex away,
     the probe precedent); `u104lex` runs at 3200000
     heartbeats, `u104parse`/`u104elab`/`u104fragment`/
     `u104fuss` at default.
-/

#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104lex
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104parse
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104elab
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104lower
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104data
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104fragment
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104fuss
