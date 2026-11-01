module
public import Stage0.Frontend.Environments
public import Grammatik.Parser.Elab.UebersetzeAllg
@[expose] public section


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Declaration classification only; every initializer remains attached to its original type. -/
private def arrayInput : SItemTief → Except String (Option (String × STyp × SKonstWert))
  | .constT name (.array element count) payload => .ok (some (name, .array element count, payload))
  | .constT name _ (.rows _) => .error ("constant " ++ name ++ ": row initializer requires an array type")
  | _ => .ok none

/-- An original array constant has both a canonical compile-time denotation and a typed canonical
    literal expression in the actual declaration universe, including every dimension and range. -/
def ArrayMeaning {original : List SItemTief} (u : UProg) (scope : Scopes original) (item : SItemTief) : Prop :=
  match arrayInput item with
  | .error _ => False
  | .ok none => True
  | .ok (some (_, ty, payload)) =>
    ∃ τ raw, ∃ term : Expr (declOf u) [] [] τ,
      uTyp scope.types [] ty = .ok τ ∧
      uKonstZeile scope.types scope.functions scope.values τ payload = some raw ∧
      lowLit (u := u) (Γ := []) (Λ := []) τ raw = .ok term

/-- Validate with the existing canonical evaluator and typed literal elaborator, never by silently
    filtering failed initializers. This also checks constants unused by runtime declarations. -/
def checkArrayItem {original : List SItemTief} (u : UProg) (scope : Scopes original)
    (item : SItemTief) : Except String (PLift (ArrayMeaning u scope item)) :=
  match hi : arrayInput item with
  | .error e => .error e
  | .ok none => .ok ⟨by simp only [ArrayMeaning, hi]⟩
  | .ok (some (name, ty, payload)) =>
    match ht : uTyp scope.types [] ty with
    | .error e => .error ("constant " ++ name ++ ": " ++ e)
    | .ok τ =>
      match hv : uKonstZeile scope.types scope.functions scope.values τ payload with
      | none => .error ("constant " ++ name ++ ": initializer has no canonical constant value")
      | some raw =>
        match he : lowLit (u := u) (Γ := []) (Λ := []) τ raw with
        | .error e => .error ("constant " ++ name ++ ": " ++ e)
        | .ok term => .ok ⟨by
            simp only [ArrayMeaning, hi]
            exact ⟨τ, raw, term, ht, hv, he⟩⟩

/-- Full source list validation; no array declaration is omitted because it is unused or invalid. -/
def checkArrays {original : List SItemTief} (u : UProg) (scope : Scopes original) :
    (items : List SItemTief) → Except String (PLift (∀ item ∈ items, ArrayMeaning u scope item))
  | [] => .ok ⟨by intro item h; simp at h⟩
  | item :: rest => do
    let head ← checkArrayItem u scope item
    let tail ← checkArrays u scope rest
    pure ⟨fun entry hm => by
      rcases List.mem_cons.mp hm with he | hr
      · subst entry; exact head.down
      · exact tail.down entry hr⟩

/-- A canonical collector entry whose literal has the exact canonical model type. -/
def ArrayCollected {original : List SItemTief} (u : UProg) (scope : Scopes original) (name : String) : Prop :=
  ∃ τ raw, ∃ term : Expr (declOf u) [] [] τ,
    (name, USide.typed τ raw) ∈ uKonstArrays scope.types scope.functions scope.values original ∧
    lowLit (u := u) (Γ := []) (Λ := []) τ raw = .ok term

/-- Every proved source array is retained by the actual canonical constant-array collector with
    its exact type and value, rather than merely producing a positive check result. -/
theorem arrayMeaning_collected {original : List SItemTief} (u : UProg) (scope : Scopes original)
    (name : String) (element : STyp) (count : SExpr) (payload : SKonstWert)
    (hm : SItemTief.constT name (.array element count) payload ∈ original)
    (h : ArrayMeaning u scope (.constT name (.array element count) payload)) :
    ArrayCollected u scope name := by
  obtain ⟨τ, raw, term, ht, hv, he⟩ := h
  refine ⟨τ, raw, term, ?_, he⟩
  apply List.mem_filterMap.mpr
  refine ⟨_, hm, ?_⟩
  simp only [ht, hv, Option.map_some]

end Gabbro.Stage0.Frontend
