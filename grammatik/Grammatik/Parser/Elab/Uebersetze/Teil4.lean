module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

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
    | .bind _ _ annotation _ | .bindLib _ _ annotation _ _ => annotation.toList
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
