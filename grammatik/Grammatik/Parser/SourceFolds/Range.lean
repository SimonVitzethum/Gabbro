module

public import Grammatik.Parser.Spec.Items

@[expose] public section
namespace Gabbro.Grammatik.Parser.SourceFolds

/-- A range fold descriptor: operator, binder, bounds, filter, value, empty case,
    accumulator type, and the iterated array with its length. -/
structure FoldDesc where
  kind : XKind
  binder : String
  lo hi filter value : SExpr
  empty : Option SExpr
  accTy : STyp
  array : String
  count : SExpr

def isFoldKind : XKind → Bool
  | .foldAdd | .foldMin | .foldMax | .foldAnd | .foldOr => true
  | _ => false

def matchFoldNode : SExpr → Option (XKind × String × List SExpr)
  | .ext k (binder :: "range" :: _) args =>
    if isFoldKind k then some (k, binder, args) else none
  | _ => none

/-- A range fold node, by the same shape the parser produces. -/
def isRangeFold (e : SExpr) : Bool := (matchFoldNode e).isSome

mutual
def hasRangeFold : SExpr → Bool
  | .lit _ | .float _ | .tru | .fls | .variable _ | .fnref _ | .res | .why .. => false
  | .field x _ | .arrow x _ | .un _ x | .old x => hasRangeFold x
  | .index a b | .bin _ a b => hasRangeFold a || hasRangeFold b
  | .call _ args | .built _ args => hasRangeFoldList args
  | .ext _ _ args => hasRangeFoldList args
def hasRangeFoldList : List SExpr → Bool
  | [] => false
  | e :: es => hasRangeFold e || hasRangeFoldList es
end

mutual
def hasRangeFoldAnw : SAnw → Bool
  | .bind _ _ _ e | .bindQ _ _ _ e | .bindAxiomOpt _ _ e => hasRangeFold e
  | .set a _ b | .emit a b _ => hasRangeFold a || hasRangeFold b
  | .shift e _ _ | .trimReq e _ => hasRangeFold e
  | .call _ args | .callQ _ args => hasRangeFoldList args
  | .cond c a bs o => hasRangeFold c || hasRangeFoldAnw a ||
      hasRangeFoldAnwList bs || (o.map hasRangeFoldAnw).getD false
  | .elsif c a => hasRangeFold c || hasRangeFoldAnw a
  | .watch _ a | .child a => hasRangeFoldAnw a
  | .cases g arms => hasRangeFold g || hasRangeFoldAnwList arms
  | .arm _ _ a => hasRangeFoldAnw a
  | .each _ s _ subj _ _ inv body =>
      (s.map hasRangeFold).getD false || hasRangeFold subj ||
      (inv.map hasRangeFold).getD false || hasRangeFoldAnw body
  | .retry _ a | .loop _ a | .trim _ _ a => hasRangeFoldAnw a
  | .locks _ e a => hasRangeFold e || hasRangeFoldAnw a
  | .leave _ | .next _ | .start _ | .other _ => false
  | .await _ _ e _ | .swap _ _ e _ | .free e => hasRangeFold e
  | .ret e => (e.map hasRangeFold).getD false
  | .alloc _ _ _ _ e o => hasRangeFold e || (o.map hasRangeFoldAnw).getD false
  | .allocVon _ _ _ _ => false
  | .reset _ r => ((r.map fun p => hasRangeFold p.1 || hasRangeFold p.2).getD false)
  | .grow _ e a => hasRangeFold e || hasRangeFoldAnw a
  | .block ss e => hasRangeFoldAnwList ss || hasRangeFoldEnde e
  | .bindLib _ _ _ c | .lcall c => hasRangeFoldList c.args
  | .step _ _ => false
  | .bindElse _ _ e _ a | .bindAxiomOptElse _ _ e _ _ a =>
      hasRangeFold e || hasRangeFoldAnw a
  | .genericCall _ _ args | .callElse _ args _ _ => hasRangeFoldList args
def hasRangeFoldAnwList : List SAnw → Bool
  | [] => false
  | a :: as => hasRangeFoldAnw a || hasRangeFoldAnwList as
def hasRangeFoldEnde : Option SEnde → Bool
  | none => false
  | some (.ret e) => (e.map hasRangeFold).getD false
  | some _ => false
end

/-- A range fold obtains its finite domain from an indexed array, never from a
    generated table or an unchecked numeric bound. -/
private def indexedArrays (binder : String) : Nat → SExpr → Except String (List String)
  | 0, _ => .error "fold range: operand nesting limit"
  | n + 1, .index (.variable array) (.variable index) =>
    pure (if strEq index binder then [array] else [])
  | n + 1, .field e _ | n + 1, .arrow e _ | n + 1, .un _ e | n + 1, .old e =>
    indexedArrays binder n e
  | n + 1, .index a b | n + 1, .bin _ a b => do
    return (← indexedArrays binder n a) ++ (← indexedArrays binder n b)
  | n + 1, .call _ args | n + 1, .built _ args | n + 1, .ext _ _ args => do
    return (← args.mapM (indexedArrays binder n)).flatten
  | _ + 1, _ => pure []

/-- Pre-order tags for every fold node: the index names the generated bindings,
    so no name supply threads through the expansion. -/
mutual
def tagFoldNodes : SExpr → Nat → List (SExpr × Nat) × Nat
  | e, next =>
    match e with
    | .ext _ _ args =>
      if isRangeFold e then
        let (inner, next') := tagFoldNodesList args (next + 1)
        (((e, next) :: inner), next')
      else tagFoldNodesList args next
    | .field x _, next | .arrow x _, next | .un _ x, next | .old x, next =>
      tagFoldNodes x next
    | .index a b, next | .bin _ a b, next =>
      let (left, mid) := tagFoldNodes a next
      let (right, done) := tagFoldNodes b mid
      (left ++ right, done)
    | .call _ args, next | .built _ args, next =>
      tagFoldNodesList args next
    | _, next => ([], next)
def tagFoldNodesList : List SExpr → Nat → List (SExpr × Nat) × Nat
  | [], next => ([], next)
  | e :: es, next =>
    let (head, mid) := tagFoldNodes e next
    let (tail, done) := tagFoldNodesList es mid
    (head ++ tail, done)
end

def lookupTag (tags : List (SExpr × Nat)) (node : SExpr) : Option Nat :=
  tags.find? (fun p => beqSExpr p.1 node) |>.map Prod.snd

def hasDuplicateTags : List (SExpr × Nat) → Bool
  | [] => false
  | (n, _) :: rest => rest.any (fun p => beqSExpr p.1 n) || hasDuplicateTags rest

def reservedNames (count : Nat) : List String :=
  (List.range count).flatMap fun i =>
    ["$rangeFold$acc$" ++ toString i, "$rangeFold$value$" ++ toString i,
      "$rangeFold$result$" ++ toString i]

def isIntElem : STyp → Bool
  | .atom word => istIntWort word || istZuckerBreite word
  | .range .. => true
  | _ => false

/-- The static bounds of a range fold node, when the node has the full shape. -/
def boundArgs : SExpr → Option (SExpr × SExpr)
  | .ext _ _ (lo :: hi :: _) => some (lo, hi)
  | _ => none

/-- Static bounds never carry folds; they are evaluated nowhere. -/
def checkBoundsFree (lo hi : SExpr) : Except String Unit :=
  if hasRangeFold lo || hasRangeFold hi then .error "fold range: bounds must be fold-free"
  else .ok ()

theorem checkBoundsFree_ok {lo hi : SExpr} (h : checkBoundsFree lo hi = .ok ()) :
    hasRangeFold lo = false ∧ hasRangeFold hi = false := by
  unfold checkBoundsFree at h
  cases h1 : hasRangeFold lo with
  | true => simp [h1] at h
  | false =>
    cases h2 : hasRangeFold hi with
    | true => simp [h1, h2] at h
    | false =>
      simp [h1, h2] at h
      exact ⟨h1, h2⟩

/-- Validate one range fold node: operator shape, literal lower bound, upper bound
    against the array length, a single indexed array variable, and the
    accumulator type. A top-level fold takes the declared result type; a nested
    fold derives its own (sums accumulate in `u64`, extrema keep the element
    type, logic folds are Boolean), since expression positions carry no
    ascription. -/
def parseFoldNode (source : List SItemTief) (locals : Spec.Locals)
    (expected : Option STyp) (chain : List String) (node : SExpr) :
    Except String FoldDesc := do
  let (kind, binder, args) ← match matchFoldNode node with
    | none => throw "fold range: not a range fold"
    | some triple => pure triple
  let (lo, hi, filter, value, empty) ← match kind, args with
    | .foldAdd, [lo, hi, filter, value] | .foldAnd, [lo, hi, filter, value] |
      .foldOr, [lo, hi, filter, value] => pure (lo, hi, filter, value, none)
    | .foldMin, [lo, hi, filter, value, empty] | .foldMax, [lo, hi, filter, value, empty] =>
      pure (lo, hi, filter, value, some empty)
    | _, _ => throw "fold range: malformed operands"
  if chain.any (strEq · binder) then throw "fold range: nested binder shadows its range binder"
  let loNat ← match lo with
    | .lit n => pure n
    | _ => throw "fold range: lower bound must be a literal"
  if hasRangeFold lo || hasRangeFold hi then throw "fold range: bounds must be fold-free"
  let arrays ← indexedArrays binder 1000 value
  let some array := arrays.head? | throw "fold range: indexed array required"
  if !(arrays.all (strEq array)) then throw "fold range: exactly one indexed array required"
  if strEq array binder then throw "fold range: binder shadows its array"
  let some (.array elemTy count) := Spec.inferType source locals 128 (.variable array)
    | throw "fold range: array type required"
  match hi with
  | .lit m =>
    match count with
    | .lit n =>
      if loNat > m then throw "fold range: lower bound exceeds the upper bound"
      if m > n then throw "fold range: upper bound exceeds the array length"
    | _ =>
      if !beqSExpr hi count then throw "fold range: upper bound must equal the array length"
  | _ =>
    if !beqSExpr hi count then throw "fold range: upper bound must equal the array length"
  match empty with
  | some emp =>
    if (Oeffentlich.namenA [] emp).any (strEq · binder) then
      throw "fold range: empty value must not use the range binder"
  | none => pure ()
  let accTy ← match kind, expected with
    | .foldAdd, some ty =>
      match ty with
      | .atom word =>
        if istIntWort word || istZuckerBreite word then pure ty
        else throw "fold range: explicit integer result required"
      | _ => throw "fold range: explicit integer result required"
    | .foldMin, some ty | .foldMax, some ty =>
      match ty with
      | .atom word =>
        if istIntWort word || istZuckerBreite word then
          match empty with
          | some _ => pure ty
          | none => throw "fold range: min/max requires an else value"
        else throw "fold range: explicit integer result required"
      | _ => throw "fold range: explicit integer result required"
    | .foldAnd, some ty | .foldOr, some ty =>
      match ty with
      | .atom "bool" => pure ty
      | _ => throw "fold range: boolean result required"
    | .foldAdd, none =>
      if isIntElem elemTy then pure (.atom "u64")
      else throw "fold range: nested add requires integer elements"
    | .foldMin, none | .foldMax, none =>
      if isIntElem elemTy then
        match empty with
        | some _ => pure elemTy
        | none => throw "fold range: min/max requires an else value"
      else throw "fold range: nested min/max requires integer elements"
    | .foldAnd, none => pure (.atom "bool")
    | .foldOr, none => pure (.atom "bool")
    | _, _ => throw "fold range: unsupported fold operator"
  pure ⟨kind, binder, lo, hi, filter, value, empty, accTy, array, count⟩

/-- The per-element combination for one operator. -/
def combineStmts (d : FoldDesc) (acc element : String) : List SAnw :=
  let accVar := SExpr.variable acc
  let elemVar := SExpr.variable element
  match d.kind with
  | .foldAdd => [.set accVar "+=" elemVar]
  | .foldMin => [.cond (.bin "<" elemVar accVar)
      (.block [.set accVar "=" elemVar] none) [] none]
  | .foldMax => [.cond (.bin ">" elemVar accVar)
      (.block [.set accVar "=" elemVar] none) [] none]
  | .foldAnd => [.cond elemVar
      (.block [] none) [] (some (.block [.set accVar "=" (.fls)] none))]
  | _ => [.cond elemVar
      (.block [.set accVar "=" (.tru)] none) [] none]

/-- Bound tests for a generalized range; each trivial bound contributes no test. -/
def boundTests (lo hi count : SExpr) (binder : String) : List SExpr :=
  let lower := if beqSExpr lo (.lit 0) then .tru else .bin "<=" lo (.variable binder)
  let upper := if beqSExpr hi count then .tru else .bin "<" (.variable binder) hi
  [lower, upper].filter (fun t => !beqSExpr t .tru)

/-- The effective filter: the written predicate with the bound tests. -/
def effFilter (tests : List SExpr) (filter' : SExpr) : SExpr :=
  tests.foldl (fun cur t =>
    if beqSExpr cur .tru then t else .bin "&&" cur t) filter'

def accName (idx : Nat) : String := "$rangeFold$acc$" ++ toString idx

def valueName (idx : Nat) : String := "$rangeFold$value$" ++ toString idx

def resultName (idx : Nat) : String := "$rangeFold$result$" ++ toString idx

def foldInit (kind : XKind) (empty' : Option SExpr) : SExpr :=
  match kind, empty' with
  | .foldAdd, _ => .lit 0
  | .foldAnd, _ => .tru
  | .foldOr, _ => .fls
  | _, some emp' => emp'
  | _, none => .lit 0

/-- One loop over the descriptor's array; the per-iteration prelude and the
    element combination run under the effective filter. -/
def buildLoopStmts (d : FoldDesc) (acc element : String) (filter' value' : SExpr)
    (preF preV : List SAnw) (tests : List SExpr) : List SAnw :=
  let elemBind := SAnw.bind false element none value'
  let step := combineStmts d acc element
  let eff := effFilter tests filter'
  let body :=
    if beqSExpr eff .tru then preV ++ [elemBind] ++ step
    else [.cond eff (.block (preV ++ [elemBind] ++ step) none) [] none]
  [SAnw.each d.binder none "elems" (.variable d.array) "unvisited" "" none
    (.block (preF ++ body) none)]

/-- The generated statements before the final binding or return: the empty-value
    prelude, the accumulator binding and the loop. -/
def buildFoldPrefix (d : FoldDesc) (idx : Nat) (filter' value' : SExpr)
    (sF sV sE : List SAnw) (empty' : Option SExpr) (tests : List SExpr) : List SAnw :=
  let acc := accName idx
  let element := valueName idx
  let loop := buildLoopStmts d acc element filter' value' sF sV tests
  let accBind := SAnw.bind true acc (some d.accTy) (foldInit d.kind empty')
  sE ++ [accBind] ++ loop

/-- One validated fold together with its bound tests: parsing, tag lookup and
    bound checks, without expanding any nested fold. -/
def parseAndCheck (source : List SItemTief) (locals : Spec.Locals)
    (chain : List String) (tags : List (SExpr × Nat)) (expected : Option STyp)
    (node : SExpr) : Except String (FoldDesc × Nat × List SExpr) := do
  let lohi := boundArgs node
  match lohi with
  | some (lo, hi) => checkBoundsFree lo hi
  | none => pure ()
  let d ← parseFoldNode source locals expected chain node
  let some idx := lookupTag tags node | throw "fold range: untagged node"
  let tests := match lohi with
    | some (lo, hi) => boundTests lo hi d.count d.binder
    | none => []
  pure (d, idx, tests)

/-- Expand a range fold expression: the node becomes a generated loop over the
    same array, nested folds become nested loops with their own accumulators.
    Fuel bounds the nesting depth. -/
def expandNested : Nat → List SItemTief → Spec.Locals → List String →
    List (SExpr × Nat) → SExpr → Except String (SExpr × List SAnw)
  | 0, _, _, _, _, e =>
    if hasRangeFold e then .error "fold range: nested fold depth exceeded"
    else .ok (e, [])
  | fuel + 1, source, locals, chain, tags =>
    fun e =>
    match matchFoldNode e with
    | some _ => do
      let (d, idx, tests) ← parseAndCheck source locals chain tags none e
      let (filter', sF) ← expandNested fuel source locals (d.binder :: chain) tags d.filter
      let (value', sV) ← expandNested fuel source locals (d.binder :: chain) tags d.value
      let (empty', sE) ← match d.empty with
        | none => pure (none, [])
        | some emp => do
          let (emp', se) ← expandNested fuel source locals (d.binder :: chain) tags emp
          pure (some emp', se)
      let tmp := resultName idx
      let prefix := buildFoldPrefix d idx filter' value' sF sV sE empty' tests
      pure (SExpr.variable tmp, prefix ++ [SAnw.bind false tmp none (.variable (accName idx))])
    | none =>
      match e with
      | .field x f => do
        let (x', s) ← expandNested fuel source locals chain tags x
        pure (.field x' f, s)
      | .arrow x f => do
        let (x', s) ← expandNested fuel source locals chain tags x
        pure (.arrow x' f, s)
      | .un o x => do
        let (x', s) ← expandNested fuel source locals chain tags x
        pure (.un o x', s)
      | .old x => do
        let (x', s) ← expandNested fuel source locals chain tags x
        pure (.old x', s)
      | .index a b => do
        let (a', sa) ← expandNested fuel source locals chain tags a
        let (b', sb) ← expandNested fuel source locals chain tags b
        pure (.index a' b', sa ++ sb)
      | .bin o a b => do
        let (a', sa) ← expandNested fuel source locals chain tags a
        let (b', sb) ← expandNested fuel source locals chain tags b
        pure (.bin o a' b', sa ++ sb)
      | .call f args => do
        let pairs ← args.mapM (expandNested fuel source locals chain tags)
        pure (.call f (pairs.map Prod.fst), (pairs.map Prod.snd).flatten)
      | .built f args => do
        let pairs ← args.mapM (expandNested fuel source locals chain tags)
        pure (.built f (pairs.map Prod.fst), (pairs.map Prod.snd).flatten)
      | .ext k ns args => do
        let pairs ← args.mapM (expandNested fuel source locals chain tags)
        pure (.ext k ns (pairs.map Prod.fst), (pairs.map Prod.snd).flatten)
      | e => pure (e, [])

/-- `return add/min/max/and/or i in lo ..< hi [where filter] [: value] [else empty]`
    over one indexed array is ordinary traversal: the value is evaluated once
    per selected slot with the same effects, contracts and costs as the written
    body. Bounds other than `0 ..< length` become filter tests; nested folds
    become nested loops. The result type is explicit; the accumulator starts
    from zero, the empty value, or the logic identity. -/
def returnFold (source : List SItemTief) (locals : Spec.Locals)
    (result : Option STyp) : SAnw → Except String SAnw
  | .ret (some e) =>
    match matchFoldNode e with
    | none => pure (.ret (some e))
    | some _ => do
      let some _ := result | throw "fold range: explicit result required"
      let tags := (tagFoldNodes e 0).1
      if hasDuplicateTags tags then throw "fold range: duplicate nested fold"
      let (d, idx, tests) ← parseAndCheck source locals [] tags result e
      let used := d.binder :: locals.map Prod.fst ++
        Oeffentlich.namenA [] d.value ++ Oeffentlich.namenA [] d.filter ++
        (match d.empty with | none => [] | some emp => Oeffentlich.namenA [] emp) ++
        (Spec.functionHeads source).map (·.name)
      if (reservedNames tags.length).any (used.contains ·) then
        throw "fold: generated binding collision"
      let (filter', sF) ← expandNested 32 source locals [d.binder] tags d.filter
      let (value', sV) ← expandNested 32 source locals [d.binder] tags d.value
      let (empty', sE) ← match d.empty with
        | none => pure (none, [])
        | some emp => do
          let (emp', se) ← expandNested 32 source locals [d.binder] tags emp
          pure (some emp', se)
      let acc := accName idx
      let prefix := buildFoldPrefix d idx filter' value' sF sV sE empty' tests
      pure (.block prefix (some (.ret (some (.variable acc)))))
  | statement => pure statement

/-- Range folds in any other position refuse instead of reaching another fold path. -/
private def expression (expr : SExpr) : Except String SExpr :=
  match expr with
  | .ext .foldAdd (_ :: "range" :: _) _ | .ext .foldMin (_ :: "range" :: _) _ |
    .ext .foldMax (_ :: "range" :: _) _ | .ext .foldAnd (_ :: "range" :: _) _ |
    .ext .foldOr (_ :: "range" :: _) _ =>
    .error "fold range: range folds are only supported as a direct return"
  | expr => .ok expr

/-- Reuse the shared lexical visitor before generic checks and before spec resolution.
    Symbolic N is compared to the symbolic array length; instantiation substitutes
    both through the existing constant-parameter machinery. -/
def prepare (source : List SItemTief) : Except String (List SItemTief) :=
  let walk : Spec.Walk := { source, instantiate := false, resolveSpecs := false,
    statementRewrite := returnFold source,
    exprRewrite := fun _ _ e => expression e }
  source.mapM (walk.item 100000)

/-- The parser shape is recognized as a range fold node. -/
theorem matchFoldNode_add_zeuge :
    matchFoldNode (.ext .foldAdd ["i", "range"]
      [.lit 0, .lit 2, .tru, .variable "x"]) =
      some (.foldAdd, "i", [.lit 0, .lit 2, .tru, .variable "x"]) := rfl

theorem isRangeFold_add_zeuge :
    isRangeFold (.ext .foldAdd ["i", "range"]
      [.lit 0, .lit 2, .tru, .variable "x"]) = true := rfl

theorem isRangeFold_plain_zeuge : isRangeFold (.variable "x") = false := rfl

/-- Bound tests vanish for the trivial `0 ..< length` range. -/
theorem boundTests_trivial_zeuge :
    boundTests (.lit 0) (.lit 2) (.lit 2) "i" = [] ∧
    effFilter (boundTests (.lit 0) (.lit 2) (.lit 2) "i") .tru = .tru := ⟨rfl, rfl⟩

/-- A nonzero lower bound and a short upper bound become filter tests. -/
theorem boundTests_general_zeuge :
    boundTests (.lit 2) (.lit 3) (.lit 4) "i" =
      [.bin "<=" (.lit 2) (.variable "i"), .bin "<" (.variable "i") (.lit 3)] ∧
    effFilter (boundTests (.lit 2) (.lit 3) (.lit 4) "i") .tru =
      .bin "&&" (.bin "<=" (.lit 2) (.variable "i")) (.bin "<" (.variable "i") (.lit 3)) := by
  exact ⟨rfl, rfl⟩

theorem foldInit_add_zeuge : foldInit .foldAdd none = .lit 0 := rfl

theorem foldInit_and_zeuge : foldInit .foldAnd none = .tru := rfl

theorem reservedNames_one_zeuge :
    reservedNames 1 =
      ["$rangeFold$acc$0", "$rangeFold$value$0", "$rangeFold$result$0"] := rfl

theorem tagFoldNodes_single_zeuge :
    (tagFoldNodes (.ext .foldAdd ["i", "range"]
      [.lit 0, .lit 2, .tru, .variable "x"]) 0).1 =
      [((.ext .foldAdd ["i", "range"]
        [.lit 0, .lit 2, .tru, .variable "x"]), 0)] := rfl

theorem boundArgs_fold_zeuge :
    boundArgs (.ext .foldAdd ["i", "range"]
      [.lit 0, .lit 2, .tru, .variable "x"]) =
      some (.lit 0, .lit 2) := rfl

theorem boundArgs_plain_zeuge : boundArgs (.variable "x") = none := rfl

/-- A non-indexed value has no indexed array. -/
theorem parseFoldNode_no_array_zeuge :
    parseFoldNode [] [] (some (.atom "u16")) []
      (.ext .foldAdd ["i", "range"] [.lit 0, .lit 2, .tru, .variable "x"]) =
      .error "fold range: indexed array required" := rfl

end Gabbro.Grammatik.Parser.SourceFolds
