module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil7

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Equality of two stable tagged locals is ordinary exhaustive matching. Every constructor
    pair is visited; only equal constructors compare payloads. Payload equality stays with the
    ordinary elaborator, including its refusals for types without an equality form. Reserved
    payload names cannot capture source names and remain local to their respective match arms. -/
def uTaggedEqualityArms (schema : USum) (right : String) (yes no : SAnw) : List SAnw :=
  schema.cases.map fun left =>
    let inner := schema.cases.map fun other =>
      let body : SAnw := if strEq left.1 other.1 then
        match left.2 with
        | none => yes
        | some ty =>
          let a := SExpr.variable "#eq-left"
          let b := SExpr.variable "#eq-right"
          let condition : SExpr := match ty with
            | .bool => .bin "||" (.bin "&&" a b) (.bin "&&" (.un "!" a) (.un "!" b))
            | _ => .bin "==" a b
          SAnw.block [.cond condition yes [] (some no)] none
        else no
      SAnw.arm other.1 (other.2.map fun _ => "#eq-right") body
    SAnw.arm left.1 (left.2.map fun _ => "#eq-left")
      (.block [.cases (.variable right) inner] none)

/-- Select by declared tagged identity, never by scalar shape. Only stable locals/parameters
    are rewritten: reads of carriers and constructors retain their ordinary checked path. -/
def uTaggedEquality (ctx : UCtx) (condition : SExpr) (yes no : SAnw) :
    Except String (Option SAnw) := do
  let .bin op (.variable left) (.variable right) := condition | return none
  if op != "==" && op != "!=" then return none
  let .ok l := uParamNr ctx left | return none
  let .ok (.sum number) := uArtBei ctx.kinds l | return none
  let .ok r := uParamNr ctx right | return none
  let .ok (.sum other) := uArtBei ctx.kinds r | return none
  if number != other then throw "source export: equality of different tagged types"
  let some schema := ctx.sums[number]? | throw "tagged type unknown"
  let (yes, no) := if op == "==" then (yes, no) else (no, yes)
  return some (.cases (.variable left) (uTaggedEqualityArms schema right yes no))

end Gabbro.Grammatik.Parser.Uebersetze
