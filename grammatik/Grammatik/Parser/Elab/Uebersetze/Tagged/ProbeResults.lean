module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil13
import all Init.Data.Repr

public section
namespace Gabbro.Grammatik.Parser.Uebersetze

-- These matches observe only the raw result, never a generalized subtype witness.
private theorem reader_ok {α : Type} {reader : Except String α}
    (result : { actual : α // reader = .ok actual }) :
    (match (generalizing := false) reader with | .ok _ => true | .error _ => false) = true := by
  exact congrArg (fun answer : Except String α =>
    match answer with | .ok _ => true | .error _ => false) result.property
private theorem reader_error {α : Type} {reader : Except String α}
    (result : { error : String // reader = .error error }) :
    (match (generalizing := false) reader with | .ok _ => false | .error _ => true) = true := by
  exact congrArg (fun answer : Except String α =>
    match answer with | .ok _ => false | .error _ => true) result.property
private theorem chain_ok {α β : Type} {first : Except String α} {next : α → Except String β}
    (parsed : { actual : α // first = .ok actual })
    (lowered : { actual : β // next parsed.val = .ok actual }) :
    (match (generalizing := false) first with
    | .error _ => false
    | .ok value =>
      match (generalizing := false) next value with
      | .ok _ => true
      | .error _ => false) = true := by
  exact (congrArg (fun answer : Except String α => match answer with
    | .error _ => false
    | .ok value => match next value with | .ok _ => true | .error _ => false) parsed.property).trans
      (congrArg (fun answer : Except String β =>
        match answer with | .ok _ => true | .error _ => false) lowered.property)
private theorem chain_first_error {α β : Type} {first : Except String α} {next : α → Except String β}
    (refused : { error : String // first = .error error }) :
    (match (generalizing := false) first with
    | .error _ => false
    | .ok value =>
      match (generalizing := false) next value with
      | .ok _ => true
      | .error _ => false) = false := by
  exact congrArg (fun answer : Except String α => match answer with
    | .error _ => false
    | .ok value => match next value with | .ok _ => true | .error _ => false) refused.property
-- Elaborate the supplied producer and its result before comparing Bool observations.
scoped macro "tagged_ok " reader:term : tactic => `(tactic| (
  let operation := $reader
  let certificate : { actual // operation = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
  exact reader_ok (reader := operation) certificate))
scoped macro "tagged_error " reader:term : tactic => `(tactic| (
  let operation := $reader
  let certificate : { error : String // operation = .error error } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
  exact reader_error (reader := operation) certificate))

-- No successful UProg is assumed: both expansion data and the actual subsequent
-- rejection are inferred separately from the same canonical elaborator.
scoped macro "tagged_rejected " name:ident " from " items:term : command => do
  let expanded := Lean.mkIdentFrom name (name.getId.appendAfter "_expanded")
  let error := Lean.mkIdentFrom name (name.getId.appendAfter "_error")
  let a ← `(command| private def $expanded : { actual : List SItemTief × List (STyp × String) //
      expandU $items = .ok actual } := by refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let b ← `(command| private def $error : { message : String //
      elabUExpanded ($expanded).val = .error message } := by refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let c ← `(command| private theorem $name : elabU $items = .error ($error).val :=
    (congrArg (fun result : Except String (List SItemTief × List (STyp × String)) =>
      result.bind elabUExpanded) ($expanded).property).trans ($error).property)
  return ⟨Lean.mkNullNode #[a, b, c]⟩

end Gabbro.Grammatik.Parser.Uebersetze
