module

public import Grammatik.Parser.Item.ElementTief.Defs6

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- The nonempty comma-separated parameter list of a spec group. -/
def parseSpecNames : Nat → List Token → Except String (List String × List Token)
  | 0, _ => .error "spec.parameters: out of fuel"
  | f + 1, ts => do
      let (n, r) ← nimmName ts
      match r with
      | .zeichen "," :: rest =>
        let (ns, tail) ← parseSpecNames f rest
        return (n :: ns, tail)
      | _ => return ([n], r)

/-- Abstract functions have no body and require explicit effects and costs. -/
def parseSpecFunctions : Nat → List Token → Except String (List FnSig × List Token)
  | 0, _ => .error "spec.functions: out of fuel"
  | _ + 1, .zeichen "}" :: rest => .ok ([], rest)
  | f + 1, ts => do
      let (s, r) ← parseFnSig f "spec" ts
      let r ← fordereZeichen ";" r
      let (ss, r) ← parseSpecFunctions f r
      return (s :: ss, r)

/-- Implementation groups contain function declarations, never arbitrary items. -/
def parseImplFunctions : Nat → List Token → Except String (List SItemTief × List Token)
  | 0, _ => .error "spec.implementation: out of fuel"
  | _ + 1, .zeichen "}" :: rest => .ok ([], rest)
  | f + 1, ts => do
      let (mods, r) := sammleModifikatoren ts
      let (s, r) ← parseFnSig f (if mods.isEmpty then "impl" else letzteArt mods) r
      let (it, r) ← parseFnRest f s r
      let (its, r) ← parseImplFunctions f r
      return (it :: its, r)

/-- One effect argument per effect parameter; the `effects` word occurs only once. -/
def parseSpecEffects : Nat → List Token → Except String (List (List SEffekt) × List Token)
  | 0, _ => .error "spec.effects: out of fuel"
  | f + 1, ts => do
      let r ← fordereZeichen "{" ts
      let (es, r) ← if istZeichenZ "}" r then pure ([], r) else parseEffektListe f r
      let r ← fordereZeichen "}" r
      match r with
      | .zeichen "," :: rest =>
        let (args, r) ← parseSpecEffects f rest
        return (es :: args, r)
      | _ => return ([es], r)

/-- §5.1 `spec S[T; effects E] { fn ...; }`, distinct from `spec fn`. -/
def parseSpecGroup (f : Nat) (ts : List Token) : Except String (SItemTief × List Token) := do
  let r ← nimmWort "spec" ts
  let (n, r) ← nimmName r
  let r ← fordereZeichen "[" r
  let (types, r) ← parseSpecNames f r
  let (effects, r) ← match r with
    | .zeichen ";" :: rest => do
      let rest ← nimmWort "effects" rest
      parseSpecNames f rest
    | _ => pure ([], r)
  let r ← fordereZeichen "]" r
  let r ← fordereZeichen "{" r
  let (fs, r) ← parseSpecFunctions f r
  return (.specGroupT n types effects fs, r)

/-- §5.1 `impl S[types; effects {...}, {...}] { fn ... {...} }`. -/
def parseImplGroup (f : Nat) (ts : List Token) : Except String (SItemTief × List Token) := do
  let r ← nimmWort "impl" ts
  let (n, r) ← nimmName r
  let r ← fordereZeichen "[" r
  let (types, r) ← parseSpecTypes f r
  let (effects, r) ← match r with
    | .zeichen ";" :: rest => do
      let rest ← nimmWort "effects" rest
      parseSpecEffects f rest
    | _ => pure ([], r)
  let r ← fordereZeichen "]" r
  let r ← fordereZeichen "{" r
  let (fs, r) ← parseImplFunctions f r
  return (.implGroupT n types effects fs, r)

end Gabbro.Grammatik.Parser
