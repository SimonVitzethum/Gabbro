module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil10

@[expose] public section

namespace Gabbro.Grammatik.Parser.Spec
open Uebersetze

structure Group where
  name : String
  types : List String
  effects : List String
  functions : List FnSig
  deriving Repr

structure Instance where
  group : String
  types : List STyp
  effects : List (List SEffekt)
  functions : List SItemTief
  deriving Repr

def groups (items : List SItemTief) : List Group := items.filterMap fun
  | .specGroupT name types effects functions => some ⟨name, types, effects, functions⟩
  | _ => none

def instances (items : List SItemTief) : List Instance := items.filterMap fun
  | .implGroupT name types effects functions => some ⟨name, types, effects, functions⟩
  | _ => none

/-- Type aliases are transparent for instance selection and uniqueness. -/
def canonicalType (items : List SItemTief) : Nat → STyp → STyp
  | 0, t => t
  | f + 1, .atom n =>
    match items.find? (fun | .typeT _ m [] [] (some _) => strEq m n | _ => false) with
    | some (.typeT _ _ _ _ (some t)) => canonicalType items f t
    | _ => .atom n
  | f + 1, .ptr s r t => .ptr s r (canonicalType items f t)
  | f + 1, .array t n => .array (canonicalType items f t) n
  | f + 1, .range (.atom "u32") (.lit 0) (.lit 4294967295) false => .atom "u32"
  | f + 1, .range t lo hi b => .range (canonicalType items f t) lo hi b
  | f + 1, .wrap t => .wrap (canonicalType items f t)
  | f + 1, .embed t p s => .embed (canonicalType items f t) p s
  | _, t => t

/-- A spec type parameter denotes a whole type, recursively in structured types. -/
def substituteType (env : List (String × STyp)) : STyp → STyp
  | .atom n => ((env.find? fun p => strEq p.1 n).map Prod.snd).getD (.atom n)
  | .path [n] => ((env.find? fun p => strEq p.1 n).map Prod.snd).getD (.path [n])
  | .ptr s r t => .ptr s r (substituteType env t)
  | .range t lo hi b => .range (substituteType env t) lo hi b
  | .array t n => .array (substituteType env t) n
  | .wrap t => .wrap (substituteType env t)
  | .embed t p s => .embed (substituteType env t) p s
  | .entry ps none => .entry ps none
  | .entry ps (some t) => .entry ps (some (substituteType env t))
  | t => t

/-- Parentheses are absent from `SExpr`; flatten only conjunctions, like `verbund::konjunkte`.
    Ordinary `spec fn` predicates use the same expander as `refines` (`uSpecEin`). -/
def conjuncts : SExpr → List SExpr
  | .bin "&&" a b => conjuncts a ++ conjuncts b
  | p => [p]

def predicateSubset (small large : List SExpr) : Bool :=
  small.all fun p => large.any (beqSExpr p)

def predicates (specs : List (String × List String × SExpr)) (post : Bool)
    (rename : List (String × SExpr)) (s : FnSig) : List SExpr :=
  s.klauseln.flatMap fun k =>
    let p := match k with
      | .needs p => if post then none else some p
      | .gives p => if post then some p else none
      | _ => none
    p.toList.flatMap fun p => conjuncts (uSpecEin specs 1000 (sErsetze rename 1000 p))

mutual
def hasHeld : SExpr → Bool
  | .call "Held" _ => true
  | .field e _ | .arrow e _ | .un _ e | .old e => hasHeld e
  | .index a b | .bin _ a b => hasHeld a || hasHeld b
  | .call _ es | .built _ es | .ext _ _ es => heldList es
  | _ => false
def heldList : List SExpr → Bool
  | [] => false
  | e :: es => hasHeld e || heldList es
end

def functionEffects (s : FnSig) : List SEffekt := s.klauseln.flatMap fun
  | .effs es => es
  | _ => []

def uniqueNames : List String → Bool
  | [] => true
  | n :: ns => !(ns.any (strEq n)) && uniqueNames ns

/-- Evaluate cost expressions with the existing front-end constant evaluator. -/
def cost (items : List SItemTief) (s : FnSig) : Option Int :=
  let fns := uKonstFns items
  match s.klauseln.filterMap (fun | .cost e => some e | _ => none) with
  | [e] => uKonstWert 0 (2^64 - 1) fns (uConstsRech fns items []) 1000 e
  | _ => none

/-- Effects of a referenced instance use that instance's substituted abstract bounds.
    Fuel refuses cyclic instance-effect declarations; no unresolved effect reaches export. -/
def expandEffects (items : List SItemTief) (gs : List Group) (ins : List Instance)
    (types : List (String × STyp)) (env : List (String × List SEffekt)) :
    Nat → List SEffekt → Except String (List SEffekt)
  | 0, _ => .error "spec.effects.cycle"
  | f + 1, es => do
    let lists ← es.mapM fun e => match e with
      | .pure => pure []
      | .param n => match env.find? (fun p => strEq p.1 n) with
        | some (_, actual) => expandEffects items gs ins types [] f actual
        | none => .error ("spec.effects.parameter: " ++ n)
      | .instanceEffects n ts => do
        let ts := ts.map (substituteType types)
        let some g := gs.find? (fun g => strEq g.name n)
          | .error ("spec.effects.unknown: " ++ n)
        let [i] := ins.filter (fun i => strEq i.group n && beqSTypList (i.types.map (canonicalType items 128)) (ts.map (canonicalType items 128)))
          | .error ("spec.effects.instance: " ++ n)
        if g.types.length != ts.length || g.effects.length != i.effects.length then
          .error "spec.arguments"
        else
          expandEffects items gs ins (g.types.zip ts) (g.effects.zip i.effects) f
            (g.functions.flatMap functionEffects)
      | e => pure [e]
    return lists.flatten

/-- Parameter names in an implementation are alpha-renamed to the abstract head for comparison. -/
def renameEffect (env : List (String × SExpr)) : SEffekt → SEffekt
  | .reads p => .reads (sErsetze env 1000 p)
  | .writes p => .writes (sErsetze env 1000 p)
  | .locks b p => .locks b (sErsetze env 1000 p)
  | .takes p => .takes (sErsetze env 1000 p)
  | .posts p => .posts (sErsetze env 1000 p)
  | e => e

end Gabbro.Grammatik.Parser.Spec
