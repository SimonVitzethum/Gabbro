module

public import Grammatik.Parser.Lex.TafelScopes
public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Elab.Uebersetze.Kontext.SyntaxEquality
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
-- Preserve the elaboration depth of Scopes/Teil5Rest, where these declarations lived.
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
  resSum : Option (Nat × List (Option Ty)) := none
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
  nimmt : List String := []
  gibt : List String := []
  /-- Call-scoped owner loans (`borrows m`, C12). -/
  leiht : List String := []
  /-- Linear owner handoffs (`moves m`, C09). -/
  bewegt : List String := []
  /-- Checked owner mints (`mints m`, C09). -/
  praegt : List String := []
  /-- The named `assume` witnessing a hardware origin (the generated core
      query's `assume` clause; `none` for software items and while unresolved). -/
  annahme : Option String := none
  /-- Written C08 clauses; lowered in the binding parameter/result context. -/
  clauses : List SKlausel := []
  deriving DecidableEq

end Gabbro.Grammatik.Parser.Uebersetze
