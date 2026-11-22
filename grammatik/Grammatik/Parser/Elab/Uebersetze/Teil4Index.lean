module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmen
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll
public import Grammatik.Logik.Fortschritt.KostenG
public import Grammatik.Logik.Vertraege.AxiomVertrag
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
public import Grammatik.Parser.Elab.Uebersetze.Eingebaut
public import Grammatik.Parser.Elab.Uebersetze.Records.Records
public import Grammatik.Korpus.Programme.Export104

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
      .ext .mem ["elems"] [_, _] | .ext .count [_, "elems"] [_, _] => true
    | .ext _ _ values => values.any (uArrayExpr fuel)
    | .bin _ a b | .index a b => uArrayExpr fuel a || uArrayExpr fuel b
    | .un _ a | .field a _ | .arrow a _ | .old a => uArrayExpr fuel a
    | .call _ values | .built _ values => values.any (uArrayExpr fuel)
    | _ => false
termination_by structural fuel => fuel

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
    | .callIndElse pointer arguments _ body => uArrayExpr fuel pointer ||
        arguments.any (uArrayExpr fuel) || uArrayBody fuel body
    | .callElse _ arguments _ body => arguments.any (uArrayExpr fuel) || uArrayBody fuel body
    | .call _ arguments => arguments.any (uArrayExpr fuel)
    | _ => false
termination_by structural fuel => fuel

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
    | .callIndElse _ _ _ body | .callElse _ _ _ body | .each _ _ _ _ _ _ _ body => uArrayBodyTypes fuel body
    | .block statements _ => statements.flatMap (uArrayBodyTypes fuel)
    | _ => []
termination_by structural fuel => fuel

def uArraySignatureTypes (signature : FnSig) : List STyp := signature.params.map (·.2) ++ signature.res.toList

def uArrayItemTypes : SItemTief → List STyp
  | .fnT signature body => uArraySignatureTypes signature ++ uArrayBodyTypes 10000 body
  | .protoT signature => uArraySignatureTypes signature
  | .constT _ ty _ | .globT _ _ ty _ _ _ _ => [ty]
  | .typeT _ _ _ _ body => body.toList
  | .tableT _ _ _ _ _ _ parts _ => parts.flatMap fun
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


/-- The length operand of a full slice names the same lexical value.
    Restricting it to a resolved local avoids duplicating a memory read. -/
def uFullLocalSlice (ctx : UCtx) (first : Int) : USide → SExpr → Bool
  | .param name, .built "lenof" [.variable last] =>
    first == 0 && strEq name last &&
      match uValueType ctx (.param name) with
      | some (.arr ..) | some (.str ..) => true
      | _ => false
  | _, _ => false

/-- Expand a fixed number of array elements using the ordinary typed
    expression reader. The start and array operands are lexical locals. -/
def uLocalArraySpan (array start : USide) (element : Ty) : Nat → Nat → USide
  | _, 0 => .typed (.arr element 0) .arrNil
  | offset, count + 1 =>
    .arrCons (.idx array (.add start (.lit offset))) (uLocalArraySpan array start element (offset + 1) count)

def uSliceConstants (ctx : UCtx) : List (String × (Int × Int)) :=
  (ctx.lits.filter fun entry => !ctx.names.any (strEq · entry.1)).map
    (fun (name, value) => (name, (value, value)))

/-- Bounds must come from a resolved binding, never from an untyped
    local's placeholder range awaiting dependent lowering. -/
def uSliceLocalType (ctx : UCtx) (name : String) : Option Ty :=
  if ctx.unknownRanges.contains name then none else uValueType ctx (.param name)

/-- The dynamic endpoint form `array[start .. start + N]` fixes the
    number of selected elements statically. The same lexical start
    must be used at both endpoints, and its complete interval must fit. -/
def uFixedLocalArrayExtent (ctx : UCtx) (blatt : SExpr → Except String USide) :
    USide → SExpr → SExpr → Option (Ty × Nat × USide)
  | .param array, .variable start, .bin "+" (.variable lastStart) amount => do
    if !strEq start lastStart then none else
      let some (.arr element length) := uSliceLocalType ctx array | none
      let some (.int lo hi) := uSliceLocalType ctx start | none
      let some count := uSchranke (uSliceConstants ctx) amount | none
      if 0 ≤ count ∧ 0 ≤ lo ∧ hi + count ≤ length then
        if blatt (.variable start) = .ok (.param start) then
          some (element, count.toNat, .param start)
        else none
      else none
  | _, _, _ => none

def uFixedLocalArraySlice (ctx : UCtx) (blatt : SExpr → Except String USide)
    (array : USide) (first last : SExpr) : Option USide :=
  (uFixedLocalArrayExtent ctx blatt array first last).map
    (fun (element, count, start) => uLocalArraySpan array start element 0 count)

def uSliceIntegerConstant (ctx : UCtx) (source : SExpr) : Option (Int × Int × USide) :=
  (uSchranke (uSliceConstants ctx) source).map (fun value => (value, value, .lit value))

/-- Compute the interval of a constant or an expression of resolved
    lexical integers. Addition and subtraction keep the ordinary G term
    and observe no carrier. -/
def uSliceInteger (ctx : UCtx) (blatt : SExpr → Except String USide) :
    SExpr → Option (Int × Int × USide)
  | .variable name =>
    match uSliceLocalType ctx name with
    | some (.int lo hi) =>
      if blatt (.variable name) = .ok (.param name) then some (lo, hi, .param name)
      else none
    | _ => if ctx.unknownRanges.contains name then none else uSliceIntegerConstant ctx (.variable name)
  | .bin op a b =>
    let constant := uSliceIntegerConstant ctx (.bin op a b)
    if constant.isSome then constant else
      match uSliceInteger ctx blatt a, uSliceInteger ctx blatt b with
      | some (loA, hiA, left), some (loB, hiB, right) =>
        if strEq op "+" then some (loA + loB, hiA + hiB, .add left right)
        else if strEq op "-" then some (loA - hiB, hiA - loB, .sub left right)
        else none
      | _, _ => none
  | source => uSliceIntegerConstant ctx source
termination_by source => sizeOf source
decreasing_by all_goals simp_wf <;> omega

/-- Independently ranged endpoints must fit within the guaranteed
    current length. Their difference gives the next length interval. -/
def uRelativeSlice (ctx : UCtx) (blatt : SExpr → Except String USide) (minimum : Int)
    (first last : SExpr) : Option (USide × USide × Int) := do
  let (firstLo, firstHi, begin) ← uSliceInteger ctx blatt first
  let (lastLo, lastHi, finish) ← uSliceInteger ctx blatt last
  if 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ minimum then
    some (begin, .sub finish begin, lastLo - firstHi)
  else none

/-- The offset is always relative to the original carrier.
    A subslice only adds to this offset and replaces its visible length. -/
structure USliceView where
  carrier : USide
  offset : USide
  length : USide
  minimum : Int

def uSliceView (ctx : UCtx) (blatt : SExpr → Except String USide) :
    SExpr → Option USliceView
  | .built "#slice" [.variable array, first, last] => do
    let some (.arr _ capacity) := uSliceLocalType ctx array | none
    if blatt (.variable array) = .ok (.param array) then
      let (begin, length, minimum) ←
        match uFixedLocalArrayExtent ctx blatt (.param array) first last with
        | some (_, count, start) => some (start, .lit (Int.ofNat count), (count : Int))
        | none => uRelativeSlice ctx blatt capacity first last
      some ⟨.param array, begin, length, minimum⟩
    else none
  | .built "#slice" [.ext .text [text] [], first, last] => do
    let bytes := text.toUTF8.toList
    let (begin, length, minimum) ← uRelativeSlice ctx blatt bytes.length first last
    some ⟨.text (bytes.map (fun byte => Int.ofNat byte.toNat)), begin, length, minimum⟩
  | .built "#slice" [base, first, last] => do
    let view ← uSliceView ctx blatt base
    let (begin, length, minimum) ← uRelativeSlice ctx blatt view.minimum first last
    some ⟨view.carrier, .add view.offset begin, length, minimum⟩
  | _ => none
termination_by source => sizeOf source
decreasing_by all_goals simp_wf <;> omega

/-- A slice projection performs one read of the original carrier, even
    when the source contains several consecutive slice operations. -/
def uSliceObservation (ctx : UCtx) (blatt : SExpr → Except String USide)
    (index : Option SExpr) (source : SExpr) : Option USide := do
  let view ← uSliceView ctx blatt source
  match index with
  | none => some view.length
  | some atIndex => do
    let (lo, hi, offset) ← uSliceInteger ctx blatt atIndex
    if 0 ≤ lo ∧ hi < view.minimum then
      some (.idx view.carrier (.add view.offset offset))
    else none

end Gabbro.Grammatik.Parser.Uebersetze
