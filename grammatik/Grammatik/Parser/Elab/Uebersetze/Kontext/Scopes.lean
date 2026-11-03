module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil1
public import Grammatik.Parser.Elab.Uebersetze.Records.Schema
public import Grammatik.Parser.Elab.Uebersetze.MeasureSource
public import Grammatik.Parser.Elab.Uebersetze.Transition.Data
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Data

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

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
  | ptr : DataCapTy → UParamArt
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
  spaces : List String := []
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
  resSum : Option (Nat × List (Option Ty)) := none
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
  /-- Complete nominal record schemas, shared by construction and named field resolution. -/
  records : List URecord := []
  /-- Resolved named value types, separate from runtime local types. -/
  namedTypes : List (String × Ty) := []
  /-- Owner identities used by local capability type annotations. -/
  eigner : List String := []
  /-- Untyped numeric locals whose actual range is deferred to G lowering. A surface
      fold must not mistake their placeholder type for a proved singleton interval. -/
  unknownRanges : List String := []

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
  resSum : Option (Nat × List (Option Ty)) := none
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
  /-- The original entry-parameter measure; absence is the empty tuple, never an inferred measure. -/
  decreases : Option UMeasure := none
  /-- Checked scalar constants in the declaration's entry scope. -/
  measureConstants : List (String × Int) := []
  /-- The unit's type aliases in the declaration's entry scope: what a conversion `T(e)`
      in `decreases` resolves against (the same table `uRechne` reads as `ctx.alias`). -/
  measureTypes : List (String × (Int × Int)) := []
  /-- The linear marks the function consumes (`effects { consumes m }`, C16). -/
  nimmt : List String := []
  /-- The linear marks the function produces (`effects { allocs m }`, C16). -/
  gibt : List String := []
  /-- The owner marks the function borrows for the call (`effects { borrows m }`, C12):
      call-scoped loans (`OwnerFlow.loans`) -- the callee holds them during the
      call, the caller gets them back on normal return. -/
  leiht : List String := []
  /-- The owner marks the function hands over for the call (`effects { moves m }`, C09):
      linear handoffs (`OwnerMove` handbacks) -- the callee holds the same nominal
      identity during the call and hands it back on every returning channel. -/
  bewegt : List String := []
  /-- The owner marks the function mints (`effects { mints m }`, C09): checked
      mint outputs (`OwnerFlow.mints`) -- the minter holds the fresh owner from
      its start frame and returns it, never ordinary production. -/
  praegt : List String := []
  /-- Private typed reporter metadata, consumed only by ghost replay. -/
  checkReturn : Option UCheckReturn := none
  deriving DecidableEq, Repr

/-- The kind of a value of type `τ` that is no pointer, index, option, sum or reason: an aggregate or a number. -/
def uArtVon : Ty → UParamArt
  | .arr _ _ | .str _ | .prod .. => .wert
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
def UFn.mitSum (f : UFn) (x : String) (num : Nat) (cs : List (Option Ty)) : UFn :=
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
  /-- The resolved `assume` index witnessing a hardware origin (`none` for
      software items and while unresolved; a dangling index reads as `none`). -/
  beleg : Option Nat := none
  /-- Explicit software origin, resolved from an entrust service binding. -/
  software : Bool := false
  names : List String := []
  needs : List UEns := []
  gives : List UEns := []
  deriving DecidableEq, Repr

deriving instance DecidableEq for Except

/-- Exact admitted source descriptor; typed admission resolves both names again. -/
structure UGuest where
  name : String
  code : String
  arch : String
  service : String
  deriving DecidableEq, Repr

/-- The elaborated program and its original-source export admission. -/
structure UProg where
  tabs : List UTab
  locks : List ULock
  fns : List UFn
  /-- The foreign bodies (`extern fn`). -/
  axs : List UAx := []
  guests : List UGuest := []
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
  /-- Original-source duty check, consumed by the actual new lowering branches. -/
  exportGate : Except String Unit := .ok ()
  /-- The unit’s nominal record schemas (`uTypes`), shared by construction and named
      field resolution. Populated by the source export; empty until connected. -/
  records : List URecord := []
  /-- The unit's declared checks (C16): elaborated records of every `check` item,
      with each `can_fail` body lowered into its generated Boolean producer in
      `fns` (named by the check's `probe` field). -/
  checks : List UCheck := []
  /-- The declaration's mark table (C16): the names of the `linear`-flagged type items in
      declaration order, then every check's Duty (`dutyName`), deduplicated. Every `nimmt`/`gibt`
      of every function must name a member (`uMarkenPruef`). -/
  marken : List String := []
  spaces : List String := ["normal"]
  /-- The unit's declared owner namespace (C12): the `linear` type names and the
      tables' `owner` marks, deduplicated, in declaration order. `own@m` in a
      pointer's rights resolves against it; the `D.Marke` correspondence itself
      (`ownerNr`/`eigner` over a nontrivial `Marke`) waits for the C09 signature
      flow. -/
  eigner : List String := []
  /-- Declared linear mark orders; an absent or empty order has one stage. -/
  markOrders : List (String × List String) := []
  deriving DecidableEq, Repr

/-- The declared labels of one nominal mark, in source order. -/
def markStages (u : UProg) (m : Fin u.marken.length) : List String :=
  ((u.markOrders.find? (fun p => strEq p.1 (u.marken.get m))).map Prod.snd).getD []

/-- Unstaged marks (including generated Duties) have one stage. -/
def markStageCount (u : UProg) (m : Fin u.marken.length) : Nat :=
  max 1 (markStages u m).length

end Gabbro.Grammatik.Parser.Uebersetze
