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

def checkPlaceLabel : UMessOrt → String
  | .variable n => n
  | .feld b f => b ++ "." ++ f
  | .stelle b f i => b ++ "." ++ f ++ "[" ++ toString i ++ "]"

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
    | none => .error "check sample has no resolved numeric interval"
  | .error _ => do
    let _ ← uBool ctx expr
    pure .bool

/-- A source-indexed private call that captures actual arguments. Floors are
    separate Bool arguments, evaluated even for a false written verdict; the
    reporter returns their conjunction with that verdict. Ghost replay reads
    those same arguments, never recomputes expressions against a later world. -/
def recordCheckReturn (ctx : UCtx) (c : SCheck) (point : Nat) (value : SExpr) :
    Except String (SAnw × UFn × UFnKopf) := do
  let places ← c.misst.mapM uMessOrt
  let samples ← (c.misst.zip places).mapM fun (expr, place) => do
    if checkPlaceAbsent ctx expr then pure (checkPlaceLabel place, none)
    else pure (checkPlaceLabel place, some (expr, ← checkSampleType ctx expr))
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
    { name := reportFnName c.cname point, params, kinds := params.map (fun p =>
        match p.2 with | .bool => .bool | _ => .int),
      res := none, resBool := true, held := [], puts := [], gives := [],
      body := [], ret := .bool answer,
      checkReturn := some { check := c.cname, point, samples := slots,
        floorStart := present.length, floorCount := c.boden.length } }
  let head : UFnKopf :=
    { name := reporter.name, names := params.map (·.1), types := params.map (·.2),
      kinds := reporter.kinds, res := none, resBool := true, held := [] }
  let body := SAnw.block
    [.bind false "#checkReport" (some (.atom "bool"))
      (.call reporter.name (present.map (·.1) ++ c.boden ++ [value]))]
    (some (.ret (some (.variable "#checkReport"))))
  pure (body, reporter, head)

/-- Instrument source blocks with their real lexical contexts. An individual
    statement is elaborated by the existing context transition, so shadowing
    and locals introduced inside each branch are resolved at that return. -/
mutual

def recordCheckCode (heads : List UFnKopf) (c : SCheck) :
    Nat → UCtx → Nat → SAnw → Except String (SAnw × List UFn × List UFnKopf × Nat)
  | 0, _, _, _ => .error "check recording expansion exhausted"
  | fuel + 1, ctx, point, statement => do
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
        | .block prefix ending =>
          pure (.block (statements ++ prefix) ending, reporters ++ [reporter],
            extraHeads ++ [head], point + 1)
        | _ => .error "check reporter expansion is not a block"
      | _ => pure (.block statements ending, reporters, extraHeads, point)
    | .cond condition yes branches no =>
      let (yes, rs, hs, point) ← recordCheckCode heads c fuel ctx point yes
      let mut reports := rs
      let mut extraHeads := hs
      let mut point := point
      let mut transformed := []
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
    let prefix := match statement, transformed with
      | .ret _, .block prefix (some (.ret result)) => prefix ++ [.ret result]
      | _, _ => [transformed]
    pure (prefix ++ rest, endCtx, reporters ++ more, extraHeads ++ moreHeads, point)

end

/-- A private reporter's result is exactly the executable floor verdict. -/
theorem report_conjunction (floors : List Bool) (verdict : Bool) :
    floors.foldl (fun result floor => result && floor) verdict = true ↔
      verdict = true ∧ ∀ floor ∈ floors, floor = true := by
  induction floors generalizing verdict with
  | nil => simp
  | cons floor rest ih => simp [ih, Bool.and_eq_true, and_assoc]

end Gabbro.Grammatik.Parser.Uebersetze
