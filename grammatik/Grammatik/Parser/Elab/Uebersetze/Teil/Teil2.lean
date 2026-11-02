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
  deriving DecidableEq, Repr

deriving instance DecidableEq for Except

/-- The elaborated program and its original-source export admission. -/
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
  deriving DecidableEq, Repr

/-- The members: a single module wrapper is unwrapped, a bare
    list passes through (104 wraps everything in
    `module beispiel::referenz`); a `pub` mark is dropped (visibility is
    checked before, `Parser/Namen/Oeffentlich.lean`). -/
def uFlach : Nat → List SItemTief → List SItemTief
  | 0, ms => ms
  | _ + 1, [] => []
  | f + 1, .modT _ b :: rest => uFlach f b ++ uFlach f rest
  | f + 1, .pubT it :: rest => uFlach f [it] ++ uFlach f rest
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

/-- C13: the storage width in bits of a builtin unsigned word name (`0` for every other name). -/
def uAtomBreite (a : String) : Nat :=
  if strEq a "u8" then 8 else if strEq a "u16" then 16
  else if strEq a "u32" then 32 else if strEq a "u64" then 64 else 0

/-- C13: the declared storage width of every `type A = uN [in lo .. hi];` alias, as the entries `A#bits` of the alias
    scope (`#` never occurs in a source name, so they shadow nothing): `(A#bits, (W, W))`. The width of a type
    name is the width the declaration chose, never the width its range happens to fit. -/
def uAliasBreiten : List SItemTief → List (String × (Int × Int))
  | [] => []
  | .typeT _ n _ _ (.some (.range (.atom w) _ _ _)) :: rest =>
    if 0 < uAtomBreite w then (n ++ "#bits", ((uAtomBreite w : Int), (uAtomBreite w : Int))) :: uAliasBreiten rest
    else uAliasBreiten rest
  | .typeT _ n _ _ (.some (.atom w)) :: rest =>
    if 0 < uAtomBreite w then (n ++ "#bits", ((uAtomBreite w : Int), (uAtomBreite w : Int))) :: uAliasBreiten rest
    else uAliasBreiten rest
  | _ :: rest => uAliasBreiten rest

/-! ## Compile-time constants

    `const N : T = e;` where `e` is an expression over literals, earlier constants, `+ - * / % & | ^ << >>`,
    a limit word `T::max`/`T::min` and calls of `const fn`s (a single trailing `return e`). The value is
    computed in EXACT integers and travels as a number, like every constant (`tr_typed`). Because the
    emitted C evaluates the same expression in the declared type, EVERY intermediate value must lie in the
    range of that type -- an overflow is the checker's `M104`, and the elaborator refuses instead of
    guessing a wrap. Anything else (an array constant, a call of a non-const function, a value outside
    its type) makes the constant UNKNOWN: a use of it is then an error ("name unknown"). -/

/-- A constant function retains its source signature and statement body. -/
structure UKonstFn where
  name : String
  params : List (String × Ty)
  erg : Ty
  rumpf : SAnw
  signature : FnSig

/-- Bind integer arguments only when their checked parameter types admit them. -/
def uKonstBinde : List (String × Ty) → List Int → Option (List (String × Int))
  | [], [] => some []
  | (n, .int pl ph) :: ps, v :: vs =>
    if pl ≤ v ∧ v ≤ ph then (uKonstBinde ps vs).map (fun r => (n, v) :: r) else none
  | _, _ => none

end Gabbro.Grammatik.Parser.Uebersetze
