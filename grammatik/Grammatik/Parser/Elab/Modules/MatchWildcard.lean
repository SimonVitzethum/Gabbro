/-
  A final wildcard in a tagged match is source sugar for the missing declared cases.
  Named arms identify exactly one tagged schema; all other shapes stay for the ordinary
  elaborator to refuse. Payloads receive fresh `#w` names, which source text cannot spell.
  No checker rule or machine G form changes: the result is an ordinary exhaustive match.
-/
module
public import Grammatik.Parser.Elab.Modules.MatchBodies
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

/-- Visit the same nested bodies as number matching, threading fresh names through copies. -/
def erweitereS (schemas : List (Uebersetze.USum STyp))
    (fuel nr : Nat) (s : SAnw) : SAnw × Nat :=
  match MatchBodies.walk (fun _ nr e arms =>
      let r := erweitereArme schemas nr arms
      .ok ([.cases e r.1], r.2)) fuel [] nr s with
  | .ok ([one], next) => (one, next)
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

/-- The shared chunk accumulator avoids copying every preceding declaration. -/
def erweitereFast (items : List SItemTief) : List SItemTief :=
  match Uebersetze.uSumSchemas (items.map fun
      | .taggedByT declaration _ => declaration
      | item => item) with
  | .error _ => items
  | .ok schemas =>
    (CallHoist.collectSteps (σ := Nat) (α := SItemTief) (β := SItemTief) (fun (nr : Nat) item =>
      let r := erweitereItem schemas nr item
      ([r.1], r.2)) items 0).1


@[csimp] theorem erweitere_eq_fast : @erweitere = @erweitereFast := by
  funext items
  rfl

end Gabbro.Grammatik.Parser.MatchWildcard
