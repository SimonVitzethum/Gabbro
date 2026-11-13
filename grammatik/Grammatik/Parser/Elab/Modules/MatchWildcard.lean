/-
  A final wildcard in a tagged match is source sugar for the missing declared cases.
  Named arms identify exactly one tagged schema; all other shapes stay for the ordinary
  elaborator to refuse. Payloads receive fresh `#w` names, which source text cannot spell.
  No checker rule or machine G form changes: the result is an ordinary exhaustive match.
-/
module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil18
@[expose] public section

namespace Gabbro.Grammatik.Parser.MatchWildcard

/-- Expand only one final, binder-free wildcard following named cases of one unique schema.
    Existing arms retain their order; missing cases follow declaration order. -/
def erweitereArme (schemas : List (Uebersetze.USum STyp)) (nr : Nat)
    (arms : List SAnw) : List SAnw × Nat :=
  match arms.reverse with
  | .arm "_" none body :: previous =>
    if previous.isEmpty || !(previous.all fun
        | .arm name _ _ => !strEq name "_"
        | _ => false) then (arms, nr)
    else
      let candidates := schemas.filter fun schema => previous.all fun
        | .arm name _ _ => schema.cases.any (fun c => strEq c.1 name)
        | _ => false
      match candidates with
      | [schema] =>
        let missing := schema.cases.filter fun c => !(previous.any fun
          | .arm name _ _ => strEq c.1 name
          | _ => false)
        let generated := missing.foldl (fun (acc : List SAnw × Nat) c =>
          match c.2 with
          | none => (acc.1 ++ [.arm c.1 none body], acc.2)
          | some _ =>
            (acc.1 ++ [.arm c.1 (some ("#w" ++ toString acc.2)) body], acc.2 + 1)) ([], nr)
        (previous.reverse ++ generated.1, generated.2)
      | _ => (arms, nr)
  | _ => (arms, nr)

/-- Visit every nested statement body, threading fresh names through every copy.
    Fuel bounds recursion exactly as in the existing source rewrite. -/
def erweitereS (schemas : List (Uebersetze.USum STyp)) :
    Nat → Nat → SAnw → SAnw × Nat
  | 0, nr, s => (s, nr)
  | n + 1, nr, s =>
    let body := erweitereS schemas n
    let bodies : Nat → List SAnw → List SAnw × Nat := fun nr ss =>
      ss.foldl (fun (acc : List SAnw × Nat) t =>
        let r := body acc.2 t
        (acc.1 ++ [r.1], r.2)) ([], nr)
    match s with
    | .cond c t eis sonst =>
      let rt := body nr t
      let re := bodies rt.2 eis
      match sonst with
      | none => (.cond c rt.1 re.1 none, re.2)
      | some b => let rb := body re.2 b; (.cond c rt.1 re.1 (some rb.1), rb.2)
    | .elsif c b => let r := body nr b; (.elsif c r.1, r.2)
    | .cases scrutinee arms =>
      let expanded := erweitereArme schemas nr arms
      let r := bodies expanded.2 expanded.1
      (.cases scrutinee r.1, r.2)
    | .arm name binder b => let r := body nr b; (.arm name binder r.1, r.2)
    | .each a b c d m raw inv bdy =>
      let r := body nr bdy
      (.each a b c d m raw inv r.1, r.2)
    | .retry h b => let r := body nr b; (.retry h r.1, r.2)
    | .loop h b => let r := body nr b; (.loop h r.1, r.2)
    | .waive ns b => let r := body nr b; (.waive ns r.1, r.2)
    | .trim o t b => let r := body nr b; (.trim o t r.1, r.2)
    | .locks g o b => let r := body nr b; (.locks g o r.1, r.2)
    | .watch d b => let r := body nr b; (.watch d r.1, r.2)
    | .block ss ende => let r := bodies nr ss; (.block r.1 ende, r.2)
    | .bindElse x ty e g b => let r := body nr b; (.bindElse x ty e g r.1, r.2)
    | .callElse f args g b => let r := body nr b; (.callElse f args g r.1, r.2)
    | .callIndElse p args g b => let r := body nr b; (.callIndElse p args g r.1, r.2)
    | .bindAxiomOptElse x ty e g b =>
      let r := body nr b
      (.bindAxiomOptElse x ty e g r.1, r.2)
    | .alloc mu x ty arena count failure =>
      match failure with
      | none => (s, nr)
      | some b =>
        let r := body nr b
        (.alloc mu x ty arena count (some r.1), r.2)
    | .grow arena count b => let r := body nr b; (.grow arena count r.1, r.2)
    | .child b => let r := body nr b; (.child r.1, r.2)
    | _ => (s, nr)

/-- Ordinary function bodies, including gated functions; compile-time functions stay intact. -/
def erweitereItem (schemas : List (Uebersetze.USum STyp)) (nr : Nat) :
    SItemTief → SItemTief × Nat
  | .fnT sig b =>
    if strEq sig.art "const" then (.fnT sig b, nr)
    else let r := erweitereS schemas 100000 nr b; (.fnT sig r.1, r.2)
  | .gateT item => let r := erweitereItem schemas nr item; (.gateT r.1, r.2)
  | item => (item, nr)

/-- Replace final tagged-match wildcards in every ordinary function of the flat unit.
    Malformed schemas or ambiguous named cases never enable an expansion. -/
def erweitere (items : List SItemTief) : List SItemTief :=
  match Uebersetze.uSumSchemas (items.map fun
      | .taggedByT declaration _ => declaration
      | item => item) with
  | .error _ => items
  | .ok schemas =>
    (items.foldl (fun (acc : List SItemTief × Nat) item =>
      let r := erweitereItem schemas acc.2 item
      (acc.1 ++ [r.1], r.2)) ([], 0)).1

end Gabbro.Grammatik.Parser.MatchWildcard
