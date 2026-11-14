module

public import Grammatik.Parser.Elab.Uebersetze.Folds.Expansion
public import Grammatik.Parser.Namen.References

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

mutual
/-- All quantifier and fold binders, including binders inside nested operands.
    Collecting every binder deliberately over-approximates the scope of a parameter. -/
def specBinders : SExpr → List String
  | .field a _ | .arrow a _ | .un _ a | .old a => specBinders a
  | .index a b | .bin _ a b => specBinders a ++ specBinders b
  | .call _ args | .built _ args => specBinderList args
  | .ext kind names args =>
    (if isFold kind || kind == .all || kind == .any || kind == .count
      then names.take 1 else []) ++ specBinderList args
  | _ => []

def specBinderList : List SExpr → List String
  | [] => []
  | arg :: args => specBinders arg ++ specBinderList args
end

/-- Reuse the existing name collector. Including the argument's own binders also
    covers names it hides, including names in a quantifier's outer-scope domain. -/
def specArgumentCaptures (body arg : SExpr) : Bool :=
  let binders := specBinders body
  if binders.isEmpty then false
  else (Oeffentlich.namenA [] arg ++ specBinders arg).any fun name =>
    binders.any (strEq · name)

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
termination_by structural fuel => fuel

/-- Inline a `spec fn` only when substitution cannot capture argument names.
    A clashing call remains for the ordinary predicate reader to refuse.
    This shared gate also applies to `Spec.predicates`. Structural in a fuel. -/
def uSpecEin (specs : List (String × List String × SExpr)) : Nat → SExpr → SExpr
  | 0, e => e
  | n + 1, e =>
    match e with
    | .call f as =>
      let as' := as.map (uSpecEin specs n)
      match specs.find? (fun p => strEq p.1 f) with
      | some (_, ps, body) =>
        if ps.length == as'.length && !(as'.any (specArgumentCaptures body)) then
          uSpecEin specs n (sErsetze (ps.zip as') 1000 body)
        else .call f as'
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
termination_by structural fuel => fuel

end Gabbro.Grammatik.Parser.Uebersetze
