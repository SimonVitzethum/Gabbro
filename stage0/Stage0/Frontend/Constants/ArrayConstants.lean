module
public import Stage0.Frontend.Environments
public import Stage0.Frontend.Constants.ConstantMeaning
public import Grammatik.Parser.Elab.UebersetzeAllg
public import Grammatik.Parser.Elab.Uebersetze.Records.Constants
@[expose] public section

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Classify every original constant; no declaration is lost at the scalar/aggregate boundary. -/
def arrayInput : SItemTief → Except String (Option (String × STyp × SKonstWert))
  | .constT name ty payload => .ok (some (name, ty, payload))
  | _ => .ok none

/-- The same canonical collector and leaf adapter used by the runtime source elaborator.
    Its partial collection is certified only after checking every original initializer below. -/
def constantValues {original : List SItemTief} (u : UProg) (scope : Scopes original) :
    List (String × USide) :=
  uKonstArrays scope.types scope.functions scope.values original
    (uRecordConstantTypes u.records) (uRecordConstant u.records scope.types scope.functions scope.values) true

/-- Every original constant has its canonical source denotation and a typed G literal.
    This covers scalars, explicit products and nested arrays of products, including unused data. -/
def ArrayMeaning {original : List SItemTief} (u : UProg) (scope : Scopes original) (item : SItemTief) : Prop :=
  match arrayInput item with
  | .error _ => False
  | .ok none => True
  | .ok (some (_, ty, payload)) =>
    ∃ τ raw, ∃ term : Expr (declOf u) [] [] τ,
      uTypIn scope.types [] (uRecordConstantTypes u.records) [] [] ty = .ok τ ∧
      uKonstZeile scope.types scope.functions scope.values τ payload
        (uRecordConstant u.records scope.types scope.functions scope.values) = some raw ∧
      lowLit (u := u) (Γ := []) (Λ := []) τ raw = .ok term ∧
      ConstantMeaning scope.types scope.functions scope.values item

/-- Validate original source syntax with the canonical evaluator and typed literal lowerer.
    A scalar-fold deferral is never admission: unknown types and bad unused values fail here. -/
def checkArrayItem {original : List SItemTief} (u : UProg) (scope : Scopes original)
    (item : SItemTief) : Except String (PLift (ArrayMeaning u scope item)) :=
  match hi : arrayInput item with
  | .error e => .error e
  | .ok none => .ok ⟨by simp only [ArrayMeaning, hi]⟩
  | .ok (some (name, ty, payload)) =>
    if hs : checkConstantMeaning scope.types scope.functions scope.values item = true then
      match ht : uTypIn scope.types [] (uRecordConstantTypes u.records) [] [] ty with
      | .error e => .error ("constant " ++ name ++ ": " ++ e)
      | .ok τ =>
        match hv : uKonstZeile scope.types scope.functions scope.values τ payload
            (uRecordConstant u.records scope.types scope.functions scope.values) with
        | none => .error ("constant " ++ name ++ ": initializer has no canonical constant value")
        | some raw =>
          match he : lowLit (u := u) (Γ := []) (Λ := []) τ raw with
          | .error e => .error ("constant " ++ name ++ ": " ++ e)
          | .ok term => .ok ⟨by
              simp only [ArrayMeaning, hi]
              exact ⟨τ, raw, term, ht, hv, he, checkConstantMeaning_sound _ _ _ _ hs⟩⟩
    else .error ("constant " ++ name ++ ": scalar binding does not match its original initializer")

/-- Strict whole-list validation; neither failure nor lack of a runtime use can filter an item. -/
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

/-- Actual collector retention, with an expression at exactly the original canonical type. -/
def ArrayCollected {original : List SItemTief} (u : UProg) (scope : Scopes original) (name : String) : Prop :=
  ∃ τ raw, ∃ term : Expr (declOf u) [] [] τ,
    (name, USide.typed τ raw) ∈ constantValues u scope ∧
    lowLit (u := u) (Γ := []) (Λ := []) τ raw = .ok term

/-- Canonical collection cannot silently drop any constant that passed the original-source check.
    The theorem applies equally to a direct product and a product under any array dimensions. -/
theorem constantMeaning_collected {original : List SItemTief} (u : UProg) (scope : Scopes original)
    (name : String) (ty : STyp) (payload : SKonstWert)
    (hm : SItemTief.constT name ty payload ∈ original)
    (h : ArrayMeaning u scope (.constT name ty payload)) : ArrayCollected u scope name := by
  obtain ⟨τ, raw, term, ht, hv, he, _⟩ := h
  refine ⟨τ, raw, term, ?_, he⟩
  apply List.mem_filterMap.mpr
  refine ⟨_, hm, ?_⟩
  cases ty <;> simp only [ht, hv, Option.map_some, Bool.true_eq_true, ↓reduceIte]

/-- The existing array retention interface also covers product-valued elements. -/
theorem arrayMeaning_collected {original : List SItemTief} (u : UProg) (scope : Scopes original)
    (name : String) (element : STyp) (count : SExpr) (payload : SKonstWert)
    (hm : SItemTief.constT name (.array element count) payload ∈ original)
    (h : ArrayMeaning u scope (.constT name (.array element count) payload)) :
    ArrayCollected u scope name :=
  constantMeaning_collected u scope name (.array element count) payload hm h

/-- Generic typing and retention of the actual leaf adapter, tied to the original initializer.
    In particular, a callback result alone never bypasses canonical G literal elaboration. -/
theorem constantMeaning_typed_retained {original : List SItemTief} (u : UProg) (scope : Scopes original)
    (name : String) (ty : STyp) (payload : SKonstWert)
    (hm : SItemTief.constT name ty payload ∈ original)
    (h : ArrayMeaning u scope (.constT name ty payload)) :
    ∃ τ raw, ∃ term : Expr (declOf u) [] [] τ,
      uTypIn scope.types [] (uRecordConstantTypes u.records) [] [] ty = .ok τ ∧
      uKonstZeile scope.types scope.functions scope.values τ payload
        (uRecordConstant u.records scope.types scope.functions scope.values) = some raw ∧
      (name, USide.typed τ raw) ∈ constantValues u scope ∧
      lowLit (u := u) (Γ := []) (Λ := []) τ raw = .ok term := by
  obtain ⟨τ, raw, term, ht, hv, he, _⟩ := h
  refine ⟨τ, raw, term, ht, hv, ?_, he⟩
  apply List.mem_filterMap.mpr
  refine ⟨_, hm, ?_⟩
  cases ty <;> simp only [ht, hv, Option.map_some, Bool.true_eq_true, ↓reduceIte]

/-- The mandatory final literal gate rechecks scalar binding semantics as well. Its successful
    certificate supplies the scalar classifier premise internally, including scope fallback. -/
theorem arrayMeaning_scalarStep {original : List SItemTief} (u : UProg) (scope : Scopes original)
    (item : SItemTief) (checked : ArrayMeaning u scope item) : ScalarStep scope item := by
  cases item <;> try trivial
  case constT name ty payload =>
    obtain ⟨_, _, _, _, _, _, meaning⟩ := checked
    exact constantMeaning_scalarStep scope _ meaning

end Gabbro.Stage0.Frontend
