module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Ausdruecke
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000
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
      capacity duty (`Block/Endblock.narrowRequired`); no failure continuation or `blkEnd`.
      Appended at the end, so earlier constructor positions keep their names. -/
  | narrowReqBeg : String → Int → Int → UStmt
  /-- Shared discard-call handler marker: foreign callee or local function pointer. -/
  | axCallElseBeg : String → List UArg → String → UStmt
  /-- `retires m;`: explicit discharge of one held linear mark. -/
  | retires : String → UStmt
  | callIndElseBeg : String → String → List UArg → String → UStmt
  /-- Explicit linear retirement in generated check consumers. No payload or runtime effect. -/
  | retireMark : String → UStmt
  /-- One named invariant scope, closed by `blkEnd`. Source metadata duties stay gated. -/
  | breakingBeg : String → UStmt
  /-- Current-state traversal: candidate, table, predecessor, member, edge, invariant,
      state-reading measure and the source mutation sub-contract. -/
  | consumeLoopBeg : String → String → String → UEns → UEns → UEns → USide → String → UStmt
  /-- Integer-to-float introduction, retaining the operand and declared result bounds. -/
  | floatOf : String → USide → (Int × Int) → (Int × Int) → UStmt
  /-- `advances a -> b;`: adjacent labels in one declared linear order. -/
  | advances : String → String → UStmt
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
  deriving Repr

-- Decide the nested constant tree and its product-field lists together.
mutual
def UKonst.decEq (a b : UKonst) : Decidable (a = b) := by
  cases a <;> cases b <;> try (refine isFalse ?_; intro h; cases h; done)
  case null.null => exact isTrue rfl
  case zahl.zahl a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [UKonst.zahl.injEq])
  case wahr.wahr a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [UKonst.wahr.injEq])
  case text.text a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [UKonst.text.injEq])
  case nil.nil => exact isTrue rfl
  case cons.cons a0 a1 b0 b1 =>
    letI := UKonst.decEq a0 b0
    letI := UKonst.decEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [UKonst.cons.injEq])
  case fall.fall a0 a1 b0 b1 =>
    letI := UKonst.decEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [UKonst.fall.injEq])
  case product.product a0 a1 b0 b1 =>
    letI := UKonst.decFields a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [UKonst.product.injEq])
termination_by sizeOf a

def UKonst.decFields : (a b : List UKonst) → Decidable (a = b)
  | [], [] => isTrue rfl
  | a :: as, b :: bs => by
      letI := UKonst.decEq a b
      letI := UKonst.decFields as bs
      exact decidable_of_iff (a = b ∧ as = bs) (by simp only [List.cons.injEq])
  | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
termination_by a _ => sizeOf a
end

instance : DecidableEq UKonst := UKonst.decEq

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
