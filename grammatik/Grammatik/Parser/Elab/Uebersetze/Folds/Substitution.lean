module

public import Grammatik.Parser.Elab.Uebersetze.Folds.Expansion

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- The substitution of the parameters of a `spec fn` by the arguments of a use. A quantifier binder hides the
    parameter of its name in its body (the last operand). Structural in a fuel (an expression is far shallower). -/
def sErsetze (σ : List (String × SExpr)) : Nat → SExpr → SExpr
  | 0, e => e
  | n + 1, e =>
    match e with
    | .variable x => match σ.find? (fun p => strEq p.1 x) with
      | some p => p.2
      | none => e
    | .field a f => .field (sErsetze σ n a) f
    | .index a i => .index (sErsetze σ n a) (sErsetze σ n i)
    | .arrow a f => .arrow (sErsetze σ n a) f
    | .un o a => .un o (sErsetze σ n a)
    | .bin o a b => .bin o (sErsetze σ n a) (sErsetze σ n b)
    | .call f as => .call f (as.map (sErsetze σ n))
    | .built f as => .built f (as.map (sErsetze σ n))
    | .old a => .old (sErsetze σ n a)
    | .ext k ns xs =>
      if isFold k then
        match ns, xs with
        | binder :: _, subject :: filter :: value :: fallback =>
          let inner := σ.filter (fun pair => !strEq pair.1 binder)
          .ext k ns (sErsetze σ n subject :: sErsetze inner n filter ::
            sErsetze inner n value :: fallback.map (sErsetze σ n))
        | _, _ => .ext k ns (xs.map (sErsetze σ n))
      else if k == XKind.all || k == XKind.any || k == XKind.count then
        let σ' := σ.filter (fun p => !(ns.head?.any (strEq p.1 ·)))
        .ext k ns ((xs.dropLast.map (sErsetze σ n)) ++ (xs.getLast?.map (sErsetze σ' n)).toList)
      else .ext k ns (xs.map (sErsetze σ n))
    | e => e

/-- Every use `g(a…)` of a `spec fn` `g` replaced by its predicate over the arguments (SUGAR, `M130`), also inside
    the predicates it brings. Structural in a fuel. -/
def uSpecEin (specs : List (String × List String × SExpr)) : Nat → SExpr → SExpr
  | 0, e => e
  | n + 1, e =>
    match e with
    | .call f as =>
      let as' := as.map (uSpecEin specs n)
      match specs.find? (fun p => strEq p.1 f) with
      | some (_, ps, body) =>
        if ps.length == as'.length then uSpecEin specs n (sErsetze (ps.zip as') 1000 body) else .call f as'
      | none => .call f as'
    | .field a f => .field (uSpecEin specs n a) f
    | .index a i => .index (uSpecEin specs n a) (uSpecEin specs n i)
    | .arrow a f => .arrow (uSpecEin specs n a) f
    | .un o a => .un o (uSpecEin specs n a)
    | .bin o a b => .bin o (uSpecEin specs n a) (uSpecEin specs n b)
    | .built f as => .built f (as.map (uSpecEin specs n))
    | .old a => .old (uSpecEin specs n a)
    | .ext k ns xs => .ext k ns (xs.map (uSpecEin specs n))
    | e => e


end Gabbro.Grammatik.Parser.Uebersetze
