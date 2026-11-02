module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil3
public import Grammatik.Parser.Elab.Uebersetze.Eingebaut

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- Resolve an index against its declared table; do not erase a foreign table identity. -/
def uExportIndex (ctx : UCtx) (table : String) (number : Nat) (source : SExpr) : Except String UIdx :=
  match source with
  | .variable name => do
      let position ← uParamNr ctx name
      match ← uArtBei ctx.kinds position with
      | .index other =>
          if other = number then uIndex ctx table number source
          else .error "source export: index belongs to another table"
      | _ => uIndex ctx table number source
  | .index (.field (.variable other) "slots") index =>
      if other = table then uIndex ctx table number index
      else .error "source export: index belongs to another table"
  | _ => uIndex ctx table number source


/-- Membership tests accept ordinary integer values, including values outside the domain.
    Nominal indices still keep their table identity; access/reach keep uExportIndex bounds. -/
def uMemberIndex (ctx : UCtx) (table : String) (number : Nat) : SExpr → Except String UIdx
  | .lit value => .ok (.lit (Int.ofNat value))
  | .un "-" (.lit value) => .ok (.lit (-(Int.ofNat value)))
  | .variable name =>
    match uParamNr ctx name with
    | .error _ =>
      match ctx.lits.find? (fun constant => strEq constant.1 name) with
      | some constant => .ok (.lit constant.2)
      | none => .error "source export: membership value lacks a checked numeric origin"
    | .ok position =>
      match uArtBei ctx.kinds position with
      | .ok .int => .ok (.param name)
      | .ok (.index origin) =>
          if origin == number then .ok (.param name)
          else .error "source export: index belongs to another table"
      | _ => .error "source export: membership value is not an integer index"
  | value => uExportIndex ctx table number value

/-- One source-inaccessible, iterator carrier without fields per represented array length. -/
def uArrayCarrierName (count : Nat) : String := "#array-elements:" ++ toString count

/-- The source domain retains the array's real type. Local/parameter values and certified
    constants are supported; a stateful array expression needs an explicit source binding. -/
def uArrayDomain (ctx : UCtx) : SExpr → Except String (USide × Ty × Nat)
  | .variable name =>
    match uParamNr ctx name with
    | .ok position =>
      match ctx.types[position]? with
      | some (.arr element count) => .ok (.param name, element, count)
      | _ => .error "source export: elems domain is not a fixed array value"
    | .error _ =>
      match ctx.arrKonst.find? (fun entry => strEq entry.1 name) with
      | some (_, value@(.typed (.arr element count) _)) => .ok (value, element, count)
      | _ => .error "source export: elems domain requires an immutable array binding"
  | _ => .error "source export: elems domain requires an immutable array binding"

/-- Whether a new finite array domain occurs anywhere in a predicate. -/
def uArrayExpr : Nat → SExpr → Bool
  | 0, _ => true
  | fuel + 1, expression =>
    match expression with
    | .ext .all [_, "elems"] [_, _] | .ext .any [_, "elems"] [_, _] |
      .ext .mem ["elems"] [_, _] => true
    | .ext _ _ values => values.any (uArrayExpr fuel)
    | .bin _ a b | .index a b => uArrayExpr fuel a || uArrayExpr fuel b
    | .un _ a | .field a _ | .arrow a _ | .old a => uArrayExpr fuel a
    | .call _ values | .built _ values => values.any (uArrayExpr fuel)
    | _ => false

/-- Inspect the same nested statements covered by the original-source metadata gate. -/
def uArrayBody : Nat → SAnw → Bool
  | 0, _ => true
  | fuel + 1, statement =>
    match statement with
    | .each _ _ kind _ _ _ invariant body => kind == "elems" ||
        invariant.any (uArrayExpr fuel) || uArrayBody fuel body
    | .block statements ending => statements.any (uArrayBody fuel) ||
        (match ending with | some (.ret value) => value.any (uArrayExpr fuel) | _ => false)
    | .bind _ _ _ value | .ret (some value) => uArrayExpr fuel value
    | .bindElse _ _ value _ body => uArrayExpr fuel value || uArrayBody fuel body
    | .cond condition yes branches no => uArrayExpr fuel condition || uArrayBody fuel yes ||
        branches.any (uArrayBody fuel) || no.any (uArrayBody fuel)
    | .elsif condition body => uArrayExpr fuel condition || uArrayBody fuel body
    | .cases value branches => uArrayExpr fuel value || branches.any (uArrayBody fuel)
    | .arm _ _ body | .waive _ body | .trim _ _ body | .locks _ _ body | .watch _ body => uArrayBody fuel body
    | .set a _ b => uArrayExpr fuel a || uArrayExpr fuel b
    | .call _ arguments => arguments.any (uArrayExpr fuel)
    | _ => false

/-- Exact declared lengths, evaluated in the already certified alias/constant scope. -/
def uArrayTypeCounts (types : List (String × (Int × Int))) : STyp → List Nat
  | .array element count =>
    (match uSchranke types count with | some value => if 0 ≤ value then [value.toNat] else [] | none => []) ++
      uArrayTypeCounts types element
  | .ptr _ _ element | .range element _ _ _ | .wrap element | .embed element _ _ => uArrayTypeCounts types element
  | _ => []

def uArrayBodyTypes : Nat → SAnw → List STyp
  | 0, _ => []
  | fuel + 1, statement =>
    match statement with
    | .bind _ _ annotation _ | .bindLib _ _ annotation _ => annotation.toList
    | .bindElse _ annotation _ _ body => annotation.toList ++ uArrayBodyTypes fuel body
    | .cond _ yes branches no => uArrayBodyTypes fuel yes ++ branches.flatMap (uArrayBodyTypes fuel) ++
        no.toList.flatMap (uArrayBodyTypes fuel)
    | .elsif _ body | .arm _ _ body | .waive _ body | .trim _ _ body | .locks _ _ body | .watch _ body =>
        uArrayBodyTypes fuel body
    | .cases _ branches => branches.flatMap (uArrayBodyTypes fuel)
    | .each _ _ _ _ _ _ _ body => uArrayBodyTypes fuel body
    | .block statements _ => statements.flatMap (uArrayBodyTypes fuel)
    | _ => []

def uArraySignatureTypes (signature : FnSig) : List STyp := signature.params.map (·.2) ++ signature.res.toList

def uArrayItemTypes : SItemTief → List STyp
  | .fnT signature body => uArraySignatureTypes signature ++ uArrayBodyTypes 10000 body
  | .protoT signature => uArraySignatureTypes signature
  | .constT _ ty _ | .globT _ _ ty _ _ _ _ => [ty]
  | .typeT _ _ _ _ body => body.toList
  | .tableT _ _ _ _ _ _ parts => parts.flatMap fun
      | .tSlot fields => fields.map (·.ftyp)
      | _ => []
  | _ => []

/-- Existing units keep exactly their declaration universe. New array forms reuse a finite
    carrier with no fields, so the carrier adds no mutable program data or provider assumption. -/
def uArrayCarriers (types : List (String × (Int × Int))) (items : List SItemTief) : List UTab :=
  if items.any (fun
      | .fnT signature body => uArrayBody 10000 body || signature.klauseln.any (fun
          | .needs predicate | .gives predicate => uArrayExpr 10000 predicate
          | _ => false)
      | _ => false) then
    let counts := (items.flatMap uArrayItemTypes).flatMap (uArrayTypeCounts types)
    let unique := counts.foldl (fun result count => if result.contains count then result else result ++ [count]) []
    unique.map (fun count => {name := uArrayCarrierName count, count := Int.ofNat count, cols := []})
  else []

/-- The table identity of a source index. A coincidentally equal count is insufficient. -/
def uIndexOrigin (ctx : UCtx) : SExpr → Except String (String × Nat × UIdx)
  | .variable name => do
      let position ← uParamNr ctx name
      match ← uArtBei ctx.kinds position with
      | .index number =>
          match ctx.tabs[number]? with
          | some table => .ok (table.name, number, .param name)
          | none => .error "source export: index table is not declared"
      | _ => .error "source export: reach requires a declared table index"
  | .index (.field (.variable table) "slots") index => do
      let (number, _) ← uTabNr ctx.tabs table
      pure (table, number, ← uExportIndex ctx table number index)
  | _ => .error "source export: reach requires a declared table index"


/-- A tree domain follows one declared child edge. Branching and undeclared roles are refused. -/
def uTreeDomain (ctx : UCtx) (source : SExpr) : Except String (String × Nat × UIdx × String) := do
  let (table, number, seed) ← uIndexOrigin ctx source
  match ctx.tabs[number]? with
  | none => .error "source export: tree table is not declared"
  | some declared =>
      match declared.kanten with
      | [("child", field)] =>
          if declared.opts.any (fun pair => pair.1 == field && pair.2 == number) then
            pure (table, number, seed, field)
          else .error "source export: tree edge must be option index into Self"
      | _ => .error "source export: tree domain requires one declared child edge"

/-- Explicit reachability retains both index origins and its named edge. -/
def uReachExport (ctx : UCtx) (field : String) (a b : SExpr) : Except String UEns := do
  let (table, number, _) ← match uIndexOrigin ctx a with
    | .ok origin => .ok origin
    | .error _ => uIndexOrigin ctx b
  pure (.reach table field (← uExportIndex ctx table number a) (← uExportIndex ctx table number b))


end Gabbro.Grammatik.Parser.Uebersetze
