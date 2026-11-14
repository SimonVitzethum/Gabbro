/- Number matching is source sugar for the existing integer equality and conditional forms. -/
module
public import Grammatik.Parser.Elab.Modules.MatchBodies
public import Grammatik.Parser.Elab.Modules.CallHoist
@[expose] public section

namespace Gabbro.Grammatik.Parser.MatchNumber

structure Kontext where
  constants : List (String × Int) := []
  cases : List String := []

/-- Only integer-typed, evaluated constants participate. Reuse the ordinary evaluator and
    type reader; a boolean/float/aggregate constant must never become a numeric pattern. -/
def kontext (items : List SItemTief) : Kontext :=
  let values := Uebersetze.uConstsRech (Uebersetze.uKonstFns items) items []
  let aliases := Uebersetze.uAliase values items
  let names := items.filterMap fun
    | .constT name ty _ =>
      match Uebersetze.uTypIn aliases [] [] [] [] ty with
      | .ok (.int _ _) => some name
      | _ => none
    | _ => none
  { constants := values.filter (fun entry => names.contains entry.1)
    cases := CallHoist.fallNamen items }

/-- Literal names are canonical decimal text. Source names cannot start with a digit. -/
def muster (k : Kontext) (name : String) : Option Int :=
  match armZahl? name with
  | some n => some (Int.ofNat n)
  | none => (k.constants.find? (fun entry => strEq entry.1 name)).map (·.2)

/-- Resolve all patterns before producing code, including duplicate constant values.
    Only the last arm may be a wildcard, and no numeric arm may bind a payload. -/
def arme (k : Kontext) : List SAnw → List Int →
    Except String (List (Int × SAnw) × SAnw)
  | [], _ => .error "number match: final wildcard arm is required"
  | .arm _ (some _) _ :: _, _ => .error "number match: pattern binders are not allowed"
  | [.arm "_" none body], _ => .ok ([], body)
  | .arm "_" none _ :: _, _ => .error "number match: wildcard must be the last arm"
  | .arm name none body :: rest, seen => do
    let some value := muster k name
      | throw "number match: integer or character literal or number constant expected"
    if seen.contains value then throw "number match: duplicate pattern value"
    let r ← arme k rest (value :: seen)
    pure ((value, body) :: r.1, r.2)
  | _, _ => .error "number match: arm expected"

/-- Negative named constants use the existing unary-negation expression. -/
def literal : Int → SExpr
  | .ofNat n => .lit n
  | .negSucc n => .un "-" (.lit (n + 1))

/-- One `if`, its ordered `else if` arms, and the mandatory final `else`. -/
def chain (value : SExpr) (branches : List (Int × SAnw)) (fallback : SAnw) : SAnw :=
  match branches with
  | [] => fallback
  | (c, body) :: rest =>
    .cond (.bin "==" value (literal c)) body
      (rest.map fun (c, body) => .elsif (.bin "==" value (literal c)) body) (some fallback)

/-- Named cases keep the tagged/option/reason path. A number constant that is also a tagged
    case is refused before either interpretation can win. An all-wildcard list cannot identify
    a numeric match and stays on the ordinary refusal path. The generated integer comparison
    makes the ordinary elaborator check that the scrutinee is a number, never a Bool or float. -/
def erweitereMatch (k : Kontext) (locals : List String) (nr : Nat)
    (e : SExpr) (arms : List SAnw) : Except String (List SAnw × Nat) := do
  if arms.any (fun
      | .arm name _ _ => (k.constants.any fun c => strEq c.1 name) && k.cases.contains name
      | _ => false) then
    throw "number match: pattern is both a number constant and a tagged case"
  let numeric := arms.any (fun
      | .arm name _ _ => (muster k name).isSome
      | _ => false) && arms.all (fun
      | .arm name _ _ => strEq name "_" || (muster k name).isSome
      | _ => false)
  if !numeric then return ([.cases e arms], nr)
  let (branches, fallback) ← arme k arms []
  let istLokal := match e with | .variable name => locals.contains name | _ => false
  if istLokal then return ([chain e branches fallback], nr)
  let fresh := "#m" ++ toString nr
  return ([.bind false fresh none e, chain (.variable fresh) branches fallback], nr + 1)

/-- Reuse the tagged wildcard walk, with lexical locals and sequence-valued replacements. -/
def erweitereS (k : Kontext) (locals : List String) (fuel nr : Nat) (s : SAnw) :
    Except String (List SAnw × Nat) :=
  MatchBodies.walk (erweitereMatch k) fuel locals nr s

def erweitereItem (k : Kontext) (nr : Nat) : SItemTief → Except String (SItemTief × Nat)
  | .fnT sig body => do
    if strEq sig.art "const" then return (.fnT sig body, nr)
    let (ss, nr) ← erweitereS k (sig.params.map (·.1)) 100000 nr body
    let rewritten := match ss with | [one] => one | many => .block many none
    return (.fnT sig rewritten, nr)
  | .gateT item => do
    let r ← erweitereItem k nr item
    return (.gateT r.1, r.2)
  | item => .ok (item, nr)

/-- Number matching adds no model constructor or acceptance rule: it exports only existing
    bindings and conditionals, checked and lowered by the ordinary verified pipeline. -/
def erweitere (items : List SItemTief) : Except String (List SItemTief) := do
  let k := kontext items
  let r ← items.foldlM (fun (acc : List SItemTief × Nat) item => do
    let r ← erweitereItem k acc.2 item
    pure (acc.1 ++ [r.1], r.2)) ([], 0)
  return r.1

/-- Unit output is accumulated once, preserving item order and the first refusal. -/
def erweitereFast (items : List SItemTief) : Except String (List SItemTief) := do
  let k := kontext items
  let r ← CallHoist.collectStepsM (ε := String) (σ := Nat) (α := SItemTief) (β := SItemTief)
    (fun (nr : Nat) item => do
    let r ← erweitereItem k nr item
    pure ([r.1], r.2)) items 0
  return r.1


@[csimp] theorem erweitere_eq_fast : @erweitere = @erweitereFast := by
  funext items
  simp only [erweitereFast, erweitere, CallHoist.collectStepsM_singleton]

end Gabbro.Grammatik.Parser.MatchNumber
