module
public import Grammatik.Parser.Elab.Uebersetze.Kontext.GuardRelation
public import Grammatik.Parser.Elab.Export.ExportMetadata
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil7
@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze.FieldNarrowing

/-- Only a pure field chain rooted in a lexical local can retain its value across calls.
    Slots, globals and indirect places remain on the ordinary refusal path. -/
def root : SExpr → Option String
  | .variable name => some name
  | .field base _ => root base
  | _ => none

mutual
/-- Replace the exact selected field read, including arithmetic and call arguments.
    Historical expressions and expressions with binders keep their original meaning. -/
def replace (place : SExpr) (name : String) (value : SExpr) : SExpr :=
  if beqSExpr place value then .variable name else
    match value with
    | .bin op a b => .bin op (replace place name a) (replace place name b)
    | .un op a => .un op (replace place name a)
    | .index a i => .index (replace place name a) (replace place name i)
    | .field a f => .field (replace place name a) f
    | .call g args => .call g (replaceList place name args)
    | .built g args => .built g (replaceList place name args)
    | .ext .label labels args => .ext .label labels (replaceList place name args)
    | value => value

def replaceList (place : SExpr) (name : String) : List SExpr → List SExpr
  | [] => []
  | value :: rest => replace place name value :: replaceList place name rest
end

/-- A write or rebinding of the containing record invalidates the snapshot. Its first
    assignment still evaluates the value before writing; compound assignments reuse the
    ordinary operator expansion. Targets are preserved, and later reads remain unchanged. -/
def replaceRun (place : SExpr) (owner name : String) : List SAnw → List SAnw × Bool
  | [] => ([], true)
  | s :: rest =>
    let writing : Option SAnw := match s with
      | .set target op value => do
        let targetOwner ← root target
        if !strEq targetOwner owner then none else do
          let value ← if strEq op "=" then some value
            else (uOpBasis op).map (fun op => SExpr.bin op target value)
          some (.set target "=" (replace place name value))
      | _ => none
    if writing.isSome then (writing.getD s :: rest, false)
    else if (uBindetS uLiestTiefe s).any (fun bound =>
        strEq bound owner || strEq bound name || strEq bound "*") then (s :: rest, false)
    else
      let (rest, whole) := replaceRun place owner name rest
      (uRewriteRuntimeReads (replace place name) uLiestTiefe s :: rest, whole)

mutual
/-- Expand a field narrow into an ordinary immutable binding followed by the existing
    local narrow. The successful continuation reads that snapshot until its root changes.
    Failure arms keep the original record and its original range. No model rule is added. -/
def expand : Nat → List String → Nat → SAnw → SAnw × Nat
  | 0, _, nr, body => (body, nr)
  | fuel + 1, locals, nr, body =>
    let visit := expand fuel
    let nested := fun extra nr body => visit (extra ++ locals) nr body
    let many := fun (nr : Nat) (bodies : List SAnw) => bodies.foldl (fun (acc : List SAnw × Nat) body =>
      let (body, nr) := nested [] acc.2 body
      (acc.1 ++ [body], nr)) ([], nr)
    match body with
    | .block ss ending =>
      let (ss, ending, nr) := expandRun fuel locals nr ss ending
      (.block ss ending, nr)
    | .cond c t alternatives fallback =>
      let (t, nr) := nested [] nr t
      let (alternatives, nr) := many nr alternatives
      let (fallback, nr) := match fallback with
        | none => (none, nr)
        | some b => let (b, nr) := nested [] nr b; (some b, nr)
      (.cond c t alternatives fallback, nr)
    | .elsif c b => let (b, nr) := nested [] nr b; (.elsif c b, nr)
    | .cases c arms => let (arms, nr) := many nr arms; (.cases c arms, nr)
    | .arm c binder b => let (b, nr) := nested binder.toList nr b; (.arm c binder b, nr)
    | .locks shared lock b => let (b, nr) := nested [] nr b; (.locks shared lock b, nr)
    | .trim place range b => let (b, nr) := nested [] nr b; (.trim place range b, nr)
    | .child b => let (b, nr) := nested [] nr b; (.child b, nr)
    | .waive names b => let (b, nr) := nested [] nr b; (.waive names b, nr)
    | .each a start domain subject mode raw inv b =>
      let (b, nr) := nested [a] nr b
      (.each a start domain subject mode raw inv b, nr)
    | .boundedLoop header b =>
      let (b, nr) := nested ((boundedLoopLocals header).map Prod.fst) nr b
      (.boundedLoop header b, nr)
    | .retry header b => let (b, nr) := nested [] nr b; (.retry header b, nr)
    | .loop header b => let (b, nr) := nested [] nr b; (.loop header b, nr)
    | .watch header b => let (b, nr) := nested [] nr b; (.watch header b, nr)
    | .bindElse x ty value reason b =>
      let (b, nr) := nested [reason] nr b
      (.bindElse x ty value reason b, nr)
    | .callElse callee args reason b =>
      let (b, nr) := nested [reason] nr b
      (.callElse callee args reason b, nr)
    | .callIndElse callee args reason b =>
      let (b, nr) := nested [reason] nr b
      (.callIndElse callee args reason b, nr)
    | .bindAxiomOptElse x ty value reason b =>
      let (b, nr) := nested [reason] nr b
      (.bindAxiomOptElse x ty value reason b, nr)
    | .alloc mu name ty arena count failure =>
      match failure with
      | none => (body, nr)
      | some b =>
        let (b, nr) := nested [] nr b
        (.alloc mu name ty arena count (some b), nr)
    | .grow arena count b =>
      let (b, nr) := nested [] nr b
      (.grow arena count b, nr)
    | body => (body, nr)
termination_by structural fuel => fuel

/-- Process lexical sequences together with their ending, so a final return reads the
    same narrowed field snapshot as an ordinary statement. Each step consumes fuel. -/
def expandRun : Nat → List String → Nat → List SAnw → Option SEnde →
    List SAnw × Option SEnde × Nat
  | 0, _, nr, ss, ending => (ss, ending, nr)
  | _ + 1, _, nr, [], ending => ([], ending, nr)
  | fuel + 1, locals, nr, s :: rest, ending =>
    let ordinary := fun (_ : Unit) =>
      let (s', nr) := expand fuel locals nr s
      let (tail, ending, nr) := expandRun fuel (ExportMetadata.binders s ++ locals) nr rest ending
      (s' :: tail, ending, nr)
    let field : Option (SExpr × String × Option SAnw) := match s with
      | .trim place@(.field ..) range failure => some (place, range, some failure)
      | .trimReq place@(.field ..) range => some (place, range, none)
      | _ => none
    match field with
    | some (place, range, failure) =>
      match root place with
      | some owner =>
        if locals.contains owner then
          let name := "#fieldNarrow:" ++ toString nr
          let (failure, nextNr) := match failure with
            | some b => let (b, nextNr) := expand fuel locals (nr + 1) b; (some b, nextNr)
            | none => (none, nr + 1)
          let next := match failure with
            | some failure => SAnw.trim (.variable name) range failure
            | none => SAnw.trimReq (.variable name) range
          let (rest, whole) := replaceRun place owner name rest
          let ending := if whole then uRewriteRuntimeReturn (replace place name) ending else ending
          let (tail, ending, nr) := expandRun fuel (name :: locals) nextNr rest ending
          (.bind false name none place :: next :: tail, ending, nr)
        else ordinary ()
      | none => ordinary ()
    | none => ordinary ()
termination_by structural fuel => fuel
end

end Gabbro.Grammatik.Parser.Uebersetze.FieldNarrowing
