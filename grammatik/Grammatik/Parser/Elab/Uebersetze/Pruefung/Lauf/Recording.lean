module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.FloorCode

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Private identities are never callable by source spelling. A return site
    has one reporter, with the exact types of its actual sample arguments. -/
def reportFnName (check : String) (point : Nat) : String :=
  check ++ "#report#" ++ toString point

/-- Only an unavailable local is absent. A present but ill-typed measured
    expression is an error, never an invented zero sample. -/
def checkPlaceAbsent (ctx : UCtx) : SExpr → Bool
  | .variable n => !ctx.names.contains n && !(ctx.globs.any (fun g => strEq g.name n))
  | .field (.variable b) _ => !ctx.names.contains b &&
      !(ctx.tabs.any (fun t => strEq t.name b))
  | _ => false

/-- A sample's source expression and its actual copyable parameter type.
    Numeric intervals reuse the canonical fold interval calculation; G lowering
    independently checks the argument against this generated type. -/
def checkSampleType (ctx : UCtx) (expr : SExpr) : Except String Ty :=
  match uWertBody ctx expr with
  | .ok value => match foldRange ctx value with
    | some (lo, hi) => .ok (.int lo hi)
    | none =>
      match uValueType ctx value with
      | some (.int lo hi) =>
        if (match value with | .param name => ctx.unknownRanges.contains name | _ => false) then
          .error "check sample interval is unresolved"
        else .ok (.int lo hi)
      | some .bool => .ok .bool
      | _ =>
        match uZugriff ctx expr with
        | .ok (_, table, field, _) =>
          match (ctx.tabs.find? (fun t => strEq t.name table)).bind
              (fun t => t.cols.find? (fun entry => strEq entry.1 field)) with
          | some (_, (lo, hi)) => .ok (.int lo hi)
          | none => .error "check sample field type is unresolved"
        | .error _ => do
          let _ ← uBool ctx expr
          pure .bool
  | .error _ => do
    let _ ← uBool ctx expr
    pure .bool

/-- Replace measured places by their captured locals before evaluating floors.
    Quantifier-bound names hide matching source places, as in `sErsetze`. -/
def checkSampleSubstitute (bindings : List (SExpr × SExpr)) : Nat → SExpr → SExpr
  | 0, expr => expr
  | fuel + 1, expr =>
    match bindings.find? (fun pair => beqSExpr pair.1 expr) with
    | some pair => pair.2
    | none =>
      let recur := checkSampleSubstitute bindings fuel
      match expr with
      | .field subject field => .field (recur subject) field
      | .index subject index => .index (recur subject) (recur index)
      | .arrow subject field => .arrow (recur subject) field
      | .un op subject => .un op (recur subject)
      | .bin op left right => .bin op (recur left) (recur right)
      | .call name args => .call name (args.map recur)
      | .built name args => .built name (args.map recur)
      | .old subject => .old (recur subject)
      | .ext kind names args =>
        if kind == XKind.all || kind == XKind.any || kind == XKind.count then
          let inner := bindings.filter fun pair => match uMessOrt pair.1 with
            | .ok (.variable n) | .ok (.feld n _) | .ok (.stelle n _ _) =>
              !names.contains n
            | .error _ => false
          .ext kind names (args.dropLast.map recur ++
            (args.getLast?.map (checkSampleSubstitute inner fuel)).toList)
        else .ext kind names (args.map recur)
      | other => other
termination_by structural fuel => fuel

/-- A source-indexed private call that captures actual arguments. Floors are
    separate Bool arguments, evaluated even for a false written verdict; the
    reporter returns their conjunction with that verdict. Ghost replay reads
    those same arguments, never recomputes expressions against a later world. -/
def recordCheckReturn (ctx : UCtx) (c : SCheck) (point : Nat) (value : SExpr) :
    Except String (SAnw × UFn × UFnKopf) := do
  let places ← c.misst.mapM uMessOrt
  let samples ← (c.misst.zip places).mapM fun (expr, place) => do
    if checkPlaceAbsent ctx expr then pure (messOrtName place, none)
    else pure (messOrtName place, some (expr, ← checkSampleType ctx expr))
  let present := samples.filterMap fun (_, capture) => capture
  let sampleParams := present.zipIdx.map fun ((_, ty), i) => ("s" ++ toString i, ty)
  let floorParams := c.boden.zipIdx.map fun (_, i) => ("f" ++ toString i, Ty.bool)
  let params := sampleParams ++ floorParams ++ [("v", Ty.bool)]
  let floorNames := floorParams.map (fun pair => UEns.var pair.1)
  let answer := floorNames.foldl UEns.and (.var "v")
  let (_, slots) := samples.foldl (fun (state : Nat × List (String × Option Nat)) sample =>
    match sample.2 with
    | none => (state.1, state.2 ++ [(sample.1, none)])
    | some _ => (state.1 + 1, state.2 ++ [(sample.1, some state.1)])) (0, [])
  let reporter : UFn :=
    { name := reportFnName c.cname point
      params := params
      kinds := params.map (fun p => match p.2 with | .bool => .bool | _ => .int)
      res := none
      resBool := true
      held := []
      puts := []
      gives := []
      body := []
      ret := .bool answer
      checkReturn := some
        { check := c.cname
          point := point
          samples := slots
          floorStart := present.length
          floorCount := c.boden.length } }
  let head : UFnKopf :=
    { name := reporter.name
      names := params.map (·.1)
      types := params.map (·.2)
      kinds := reporter.kinds
      res := none
      resBool := true
      held := [] }
  let captures := present.zipIdx.map fun ((expr, _), i) =>
    (expr, SExpr.variable ("#checkSample#" ++ toString i))
  let sampleBindings := captures.map fun (expr, captured) => match captured with
    | .variable name => SAnw.bind false name none expr
    | _ => SAnw.other "invalid private sample binding"
  let floors := c.boden.map (checkSampleSubstitute captures 100000)
  let body := SAnw.block
    ([.bind false "#checkVerdict" (some (.atom "bool")) value] ++ sampleBindings ++
      [.bind false "#checkReport" (some (.atom "bool"))
        (.call reporter.name (captures.map (·.2) ++ floors ++ [.variable "#checkVerdict"]))])
    (some (.ret (some (.variable "#checkReport"))))
  pure (body, reporter, head)

mutual

/-- Instrument source blocks with their real lexical contexts. An individual
    statement is elaborated by the existing context transition, so shadowing
    and locals introduced inside each branch are resolved at that return. -/
def recordCheckCode (heads : List UFnKopf) (c : SCheck) :
    Nat → UCtx → Nat → SAnw → Except String (SAnw × List UFn × List UFnKopf × Nat)
  | 0, _, _, _ => .error "check recording expansion exhausted"
  | fuel + 1, ctx, point, statement => do
    let one := fun (inner : UCtx) (wrap : SAnw → SAnw) (branch : SAnw) => do
      let (branch, rs, hs, next) ← recordCheckCode heads c fuel inner point branch
      pure (wrap branch, rs, hs, next)
    let reasonCtx := fun (call : SExpr) (reason : String) =>
      match call with
      | .call name _ =>
        match (heads.find? (fun h => strEq h.name name)).bind (·.kanal) with
        | some (index, count) => uMitLokal ctx reason (.why index) (.why count) ctx.muts
        | none => ctx
      | _ => ctx
    match statement with
    | .ret (some value) =>
      let (body, reporter, head) ← recordCheckReturn ctx c point value
      pure (body, [reporter], [head], point + 1)
    | .block statements ending =>
      let (statements, ctx, reporters, extraHeads, point) ←
        recordCheckStatements heads c fuel ctx point statements
      match ending with
      | some (.ret (some value)) =>
        let (body, reporter, head) ← recordCheckReturn ctx c point value
        match body with
        | .block recordedPrelude ending =>
          pure (.block (statements ++ recordedPrelude) ending, reporters ++ [reporter],
            extraHeads ++ [head], point + 1)
        | _ => .error "check reporter expansion is not a block"
      | _ => pure (.block statements ending, reporters, extraHeads, point)
    | .cond condition yes branches no =>
      let (yes, rs, hs, point) ← recordCheckCode heads c fuel ctx point yes
      let mut reports := rs
      let mut extraHeads := hs
      let mut point := point
      let mut transformed : List SAnw := []
      for branch in branches do
        let (branch, rs, hs, next) ← recordCheckCode heads c fuel ctx point branch
        transformed := transformed ++ [branch]
        reports := reports ++ rs
        extraHeads := extraHeads ++ hs
        point := next
      let no ← match no with
        | none => pure none
        | some branch => do
          let (branch, rs, hs, next) ← recordCheckCode heads c fuel ctx point branch
          reports := reports ++ rs
          extraHeads := extraHeads ++ hs
          point := next
          pure (some branch)
      pure (.cond condition yes transformed no, reports, extraHeads, point)
    | .elsif condition branch =>
      let (branch, rs, hs, next) ← recordCheckCode heads c fuel ctx point branch
      pure (.elsif condition branch, rs, hs, next)
    | .callElse name args reason branch =>
      let inner := if reason.isEmpty then ctx else reasonCtx (.call name args) reason
      one inner (.callElse name args reason) branch
    | .bindElse name ty call reason branch =>
      one (reasonCtx call reason) (.bindElse name ty call reason) branch
    | .bindAxiomOptElse name ty call reason branch =>
      one (reasonCtx call reason) (.bindAxiomOptElse name ty call reason) branch
    | .each name start kind subject mode measure invariant branch =>
      let (_, inner, _) ← uLoopExport ctx name start kind subject mode measure invariant
      one inner (.each name start kind subject mode measure invariant) branch
    | .boundedLoop raw branch =>
      let header ← readBoundedHeader raw
      let inner ← uLoopBodyContext ctx header
      one inner (.boundedLoop raw) branch
    | .retry header branch =>
      one ctx (.retry header) branch
    | .loop header branch =>
      let (label, _) ← uForeverKopf ctx header
      one { ctx with loops := label :: ctx.loops } (.loop header) branch
    | .waive names branch => one ctx (.waive names) branch
    | .trim value ty branch => one ctx (.trim value ty) branch
    | .locks acquire target branch =>
      let inner := match target with
        | .variable name => { ctx with held := name :: ctx.held }
        | _ => ctx
      one inner (.locks acquire target) branch
    | .watch name branch => one ctx (.watch name) branch
    | .grow arena count branch => one ctx (.grow arena count) branch
    | .child branch => one ctx SAnw.child branch
    | .alloc mutable name ty arena count branch =>
      match branch with
      | none => pure (statement, [], [], point)
      | some branch => one ctx (fun branch => .alloc mutable name ty arena count (some branch)) branch
    | .cases value arms =>
      let mut reports : List UFn := []
      let mut extraHeads : List UFnKopf := []
      let mut point := point
      let mut transformed : List SAnw := []
      for arm in arms do
        let inner := match arm, (uSumPlatz ctx value).toOption with
          | .arm tag (some name) _, some (_, index) =>
            match (ctx.sums[index]?).bind (fun sum =>
                (sum.cases.find? (fun entry => strEq entry.1 tag)).bind (·.2)) with
            | some ty => uMitLokal ctx name
                (match ty with | .bool => .bool | _ => uArtVon ty) ty ctx.muts
            | none => ctx
          | _, _ => ctx
        let (arm, rs, hs, next) ← recordCheckCode heads c fuel inner point arm
        transformed := transformed ++ [arm]
        reports := reports ++ rs
        extraHeads := extraHeads ++ hs
        point := next
      pure (.cases value transformed, reports, extraHeads, point)
    | .arm tag binding branch => one ctx (.arm tag binding) branch
    | other => pure (other, [], [], point)

def recordCheckStatements (heads : List UFnKopf) (c : SCheck) :
    Nat → UCtx → Nat → List SAnw →
      Except String (List SAnw × UCtx × List UFn × List UFnKopf × Nat)
  | 0, _, _, _ => .error "check recording expansion exhausted"
  | _ + 1, ctx, point, [] => .ok ([], ctx, [], [], point)
  | fuel + 1, ctx, point, statement :: rest => do
    let (transformed, reporters, extraHeads, point) ←
      recordCheckCode heads c fuel ctx point statement
    let (_, nextCtx) ← uAnwReihe ctx.tabs heads 1000000 ctx [statement]
    let (rest, endCtx, more, moreHeads, point) ←
      recordCheckStatements heads c fuel nextCtx point rest
    let recordedPrelude := match statement, transformed with
      | .ret _, .block returnPrelude (some (.ret result)) => returnPrelude ++ [.ret result]
      | _, _ => [transformed]
    pure (recordedPrelude ++ rest, endCtx, reporters ++ more, extraHeads ++ moreHeads, point)

end

/-- A private reporter's result is exactly the executable floor verdict. -/
theorem report_conjunction (floors : List Bool) (verdict : Bool) :
    floors.foldl (fun result floor => result && floor) verdict = true ↔
      verdict = true ∧ ∀ floor ∈ floors, floor = true := by
  induction floors generalizing verdict with
  | nil => simp
  | cons floor rest ih => simp [ih, Bool.and_eq_true, and_assoc]

end Gabbro.Grammatik.Parser.Uebersetze
