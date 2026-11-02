module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil9

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Fold temporaries cannot be written as source identifiers. The counter is shared by
    every operand, including operands inside a traversal body. -/
def foldName (n : Nat) (suffix : String) : String := "#fold:" ++ toString n ++ ":" ++ suffix

def isFold : XKind → Bool
  | .foldAdd | .foldMin | .foldMax => true
  | _ => false

/-- Integer interval calculation reuses the elaborated value tree. Unknown values stay
    refused; no guessed range can license a fold. -/
def foldRange (ctx : UCtx) : USide → Option (Int × Int)
  | .lit n => some (n, n)
  | .param name => do
    if ctx.unknownRanges.contains name then none else do
      let position ← ctx.names.findIdx? (strEq · name)
      let .int lo hi ← ctx.types[position]? | none
      some (lo, hi)
  | .tab table field _ => do
    let table ← ctx.tabs.find? (fun tab => strEq tab.name table)
    let field ← table.cols.find? (fun column => strEq column.1 field)
    if table.bools.contains field.1 || (table.werte.any (fun entry => entry.1 == field.1)) then none
    else some field.2
  | .idx array _ => do
    let .arr (.int lo hi) _ ← uValueType ctx array | none
    some (lo, hi)
  | .glob name => do
    let global ← ctx.globs.find? (fun global => strEq global.name name)
    let .int lo hi := global.ty | none
    some (lo, hi)
  | .typed (.int lo hi) _ | .conv lo hi _ | .eng _ lo hi => some (lo, hi)
  | .neg value => do
    let (lo, hi) ← foldRange ctx value
    some (-hi, -lo)
  | .add a b => do
    let x ← foldRange ctx a
    let y ← foldRange ctx b
    some (x.1 + y.1, x.2 + y.2)
  | .sub a b => do
    let x ← foldRange ctx a
    let y ← foldRange ctx b
    some (x.1 - y.2, x.2 - y.1)
  | .mul a b => do
    let x ← foldRange ctx a
    let y ← foldRange ctx b
    some (min (min (x.1*y.1) (x.1*y.2)) (min (x.2*y.1) (x.2*y.2)),
          max (max (x.1*y.1) (x.1*y.2)) (max (x.2*y.1) (x.2*y.2)))
  | _ => none

/-- The ordinary exporter defers untyped number intervals until G lowering. Carry a
    computed interval when available, and mark the others explicitly as unknown. -/
def foldBindingContext (before after : UCtx) (statement : UStmt) : UCtx :=
  let name := after.names.headD ""
  let unknown := before.unknownRanges.filter (fun previous => previous != name)
  match statement with
  | .bind _ none value =>
    match foldRange before value with
    | some (lo, hi) => {after with types := .int lo hi :: after.types.drop 1, unknownRanges := unknown}
    | none => {after with unknownRanges := name :: unknown}
  | _ => {after with unknownRanges := unknown}

/-- A filtered sum may select zero through capacity elements, including when all
    element bounds have the same sign. -/
def foldSumRange (capacity : Int) (element : Int × Int) : Int × Int :=
  (capacity * min 0 element.1, capacity * max 0 element.2)

/-- The initial accumulator is in the zero-prefix interval. -/
theorem foldSumRange_zero (element : Int × Int) :
    (foldSumRange 0 element).1 ≤ 0 ∧ 0 ≤ (foldSumRange 0 element).2 := by
  simp [foldSumRange]

/-- Each selected slot extends the prefix interval by exactly one element. This
    is why the generated non-wrapping addition needs no modular arithmetic. -/
theorem foldSumRange_step (used lo hi accumulator value : Int)
    (previous : (foldSumRange used (lo, hi)).1 ≤ accumulator ∧
      accumulator ≤ (foldSumRange used (lo, hi)).2)
    (element : lo ≤ value ∧ value ≤ hi) :
    (foldSumRange (used + 1) (lo, hi)).1 ≤ accumulator + value ∧
      accumulator + value ≤ (foldSumRange (used + 1) (lo, hi)).2 := by
  simp only [foldSumRange, Int.add_mul, Int.one_mul] at *
  omega

/-- The default numeric result is a machine integer, never an unbounded or wrapping
    integer. An explicit surrounding type is checked again by the ordinary exporter. -/
def foldFitsMachine (range : Int × Int) : Bool :=
  (-(2^63 : Int) ≤ range.1 && range.2 < (2^63 : Int)) ||
    (0 ≤ range.1 && range.2 < (2^64 : Int))

/-- Short table indexing in the new surface forms denotes the same existing slot read. -/
def foldPlaces : Nat → SExpr → SExpr
  | 0, e => e
  | n + 1, .field (.index (.variable table) index) field =>
    .field (.index (.field (.variable table) "slots") (foldPlaces n index)) field
  | n + 1, .field e field => .field (foldPlaces n e) field
  | n + 1, .index e index => .index (foldPlaces n e) (foldPlaces n index)
  | n + 1, .un op e => .un op (foldPlaces n e)
  | n + 1, .bin op a b => .bin op (foldPlaces n a) (foldPlaces n b)
  | n + 1, .call name args => .call name (args.map (foldPlaces n))
  | n + 1, .ext kind names args => .ext kind names (args.map (foldPlaces n))
  | _ + 1, e => e

/-- Reject a second table even in a nested operand. Local/constant names are allowed;
    the ordinary readers still check the type, guard and purity of every operand. -/
def foldOneTable (ctx : UCtx) (table : String) : Nat → SExpr → Bool
  | 0, _ => false
  | _ + 1, .variable name => !ctx.tabs.any (fun t => t.name == name && name != table)
  | n + 1, .field e _ | n + 1, .arrow e _ | n + 1, .un _ e | n + 1, .old e =>
    foldOneTable ctx table n e
  | n + 1, .index a b | n + 1, .bin _ a b => foldOneTable ctx table n a && foldOneTable ctx table n b
  | n + 1, .call _ args | n + 1, .built _ args | n + 1, .ext _ _ args =>
    args.all (foldOneTable ctx table n)
  | _ + 1, _ => true

/-- The G model has IEEE operations, but this source exporter has no float value
    reader yet. Name that boundary instead of treating a float as an integer. -/
def foldHasFloat (ctx : UCtx) : Nat → SExpr → Bool
  | 0, _ => false
  | _ + 1, .float _ => true
  | _ + 1, .variable name =>
    match (ctx.names.findIdx? (strEq · name)).bind (ctx.types[·]?) with
    | some (.fl ..) => true
    | _ => false
  | n + 1, .bin _ a b | n + 1, .index a b => foldHasFloat ctx n a || foldHasFloat ctx n b
  | n + 1, e@(.field base _) =>
    foldHasFloat ctx n base || (match uZugriff ctx (foldPlaces n e) with
      | .ok (_, table, field, _) =>
        (ctx.tabs.find? (fun tab => tab.name == table)).any fun tab =>
          tab.werte.any (fun entry => entry.1 == field && (match entry.2 with | .fl .. => true | _ => false))
      | _ => false)
  | n + 1, .un _ e => foldHasFloat ctx n e
  | n + 1, .call _ args | n + 1, .built _ args => args.any (foldHasFloat ctx n)
  | _ + 1, _ => false

/-- Generated code contains only the pre-existing binding, traversal, branch and
    assignment forms. Min/max track occupancy independently of their fallback. -/
def foldCode (kind : XKind) (header : UStmt) (acc seen value : String)
    (range : Int × Int) (predicate : UEns) (body empty : USide) : List UStmt :=
  let storage := (min 0 range.1, max 0 range.2)
  let step := if kind == .foldAdd then
      [UStmt.setVar acc (.eng (.add (.param acc) (.param value)) range.1 range.2)]
    else
      [UStmt.ifBeg (.or (.not (.var seen))
         (.cmp (if kind == .foldMin then "<" else ">") (.param value) (.param acc))),
       .setVar acc (.param value), .setVarB seen .tru, .ifElse, .blkEnd]
  [UStmt.bindMut acc storage.1 storage.2 (.lit 0)] ++
    (if kind == .foldAdd then [] else [UStmt.bindB seen .fls]) ++
    [header, .ifBeg predicate, .bind value none body] ++ step ++
    [UStmt.ifElse, .blkEnd, .blkEnd] ++
    (if kind == .foldAdd then [] else
      [UStmt.ifBeg (.not (.var seen)), .setVar acc empty, .ifElse, .blkEnd]) ++
    [UStmt.bind (acc ++ ":result") none (.eng (.param acc) range.1 range.2)]

/-- Expand one fold in its lexical context. No new machine-G form is introduced.
    The total `eng` in an add step has an unreachable out-of-range branch: at most
    capacity slots contribute, each once, and the accumulator starts at zero. -/
def expandFold (ctx : UCtx) (serial : Nat) (kind : XKind) (names : List String)
    (operands : List SExpr) : Except String (List UStmt × UCtx × SExpr) := do
  let [binder, domain] := names | throw "fold: malformed domain"
  let subject :: filter :: expression :: fallback := operands | throw "fold: malformed operands"
  let (header, inner, membership) ← uLoopExport ctx binder none domain subject "unvisited" "" none
  let table ← match header with
    | .loopBeg _ table _ => pure table
    | .arrayLoopBeg _ _ _ => do
      let (_, _, count) ← uArrayDomain ctx subject
      pure (uArrayCarrierName count)
    | _ => throw "fold: domain must enumerate one table"
  let (number, capacity) ← uTabNr ctx.tabs table
  let some declaration := ctx.tabs[number]? | throw "fold: unknown table"
  if declaration.von.isSome || capacity < 0 then throw "fold: finite table capacity required"
  if !(foldOneTable ctx table 1000 filter && foldOneTable ctx table 1000 expression) then
    throw "fold: operands may read only the domain table"
  if foldHasFloat inner 1000 expression then
    throw "fold: IEEE float value export is not available"
  let predicate ← uBool inner (foldPlaces 1000 filter)
  let predicate := match membership with | none => predicate | some member => UEns.and member predicate
  let body ← uWertBody inner (foldPlaces 1000 expression)
  let some element := foldRange inner body | throw "fold: numeric operand has no exported integer range"
  let empty ← match kind, fallback with
    | .foldAdd, [] => pure (USide.lit 0)
    | .foldMin, [value] | .foldMax, [value] => uWertBody ctx value
    | .foldAdd, _ => throw "fold add: else is not allowed"
    | _, _ => throw "fold min/max: else is required"
  let some emptyRange := foldRange ctx empty | throw "fold: fallback has no exported integer range"
  let range := if kind == .foldAdd then foldSumRange capacity element
    else (min element.1 emptyRange.1, max element.2 emptyRange.2)
  if !foldFitsMachine range then throw "fold: result range does not fit its integer type; narrow the operand first"
  let acc := foldName serial "acc"
  let code := foldCode kind header acc (foldName serial "seen") (foldName serial "value")
    range predicate body empty
  let result := acc ++ ":result"
  let context := uMitLokal ctx result .int (.int range.1 range.2) ctx.muts
  pure (code, context, .variable result)

end Gabbro.Grammatik.Parser.Uebersetze
