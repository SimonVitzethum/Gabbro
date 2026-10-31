/- Reconstruct start arguments already accepted by the canonical frontend as canonical
   closed expressions. No source evaluator or alternative execution semantics is introduced. -/
import Grammatik.Parser.Elab.UebersetzeAllg

namespace Gabbro.Stage0.StartArgument
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Reification of exactly the existing `uStartArg` cases into the language's own typed syntax.
    In particular a pointer is a declared carrier capability, never an integer address. -/
def expression (u : UProg) (ty : Ty) (arg : SExpr)
    (accepted : uStartArg u.tabs ty arg = true) : Expr (declOf u) [] [] ty := by
  cases ty <;> cases arg <;> simp only [uStartArg] at accepted
  all_goals try contradiction
  case int.lit lo hi n =>
    have h := of_decide_eq_true accepted
    exact .widen h.1 h.2 (.lit n)
  case int.un lo hi op a =>
    cases a <;> try simp only at accepted
    all_goals try contradiction
    all_goals
      split at accepted <;> simp_all
      exact .widen accepted.1 accepted.2 (.lit _)
  case bool.tru => exact .tru
  case bool.fls => exact .fls
  case opt.call n name args => exact .none n
  case ptr.fnref n rw name =>
    by_cases hn : n < u.tabs.length
    · exact Expr.ptrOf (D := declOf u) (⟨n, hn⟩ : Fin u.tabs.length) n
        (by simp only [declOf, dite_eq_left hn]) rw
    · have hh : u.tabs[n]? = none := List.getElem?_eq_none (by omega)
      simp only [hh, Bool.false_eq_true] at accepted

/-- Reified numeric arguments retain the exact source numeral, not a default initial value. -/
theorem expression_literal (u : UProg) (lo hi : Int) (n : Nat)
    (accepted : uStartArg u.tabs (.int lo hi) (.lit n) = true)
    (before world : World (declOf u)) :
    (eval before (expression u (.int lo hi) (.lit n) accepted) world .nil).n = (n : Int) := by
  rfl

theorem expression_negative (u : UProg) (lo hi : Int) (n : Nat)
    (accepted : uStartArg u.tabs (.int lo hi) (.un "-" (.lit n)) = true)
    (before world : World (declOf u)) :
    (eval before (expression u (.int lo hi) (.un "-" (.lit n)) accepted) world .nil).n = -(n : Int) := by
  rfl

/-- A bounded negative start argument jointly witnesses acceptance and exact canonical value. -/
theorem expression_negative_zeuge (u : UProg) (world : World (declOf u)) :
    (eval world (expression u (.int (-9) 12) (.un "-" (.lit 7)) (by simp [uStartArg])) world .nil).n = -7 :=
  expression_negative u (-9) 12 7 (by simp [uStartArg]) world world

theorem expression_literal_zeuge (u : UProg) (world : World (declOf u)) :
    (eval world (expression u (.int 0 12) (.lit 7) (by simp [uStartArg])) world .nil).n = 7 :=
  expression_literal u 0 12 7 (by simp [uStartArg]) world world

/-- Argument environments are evaluated by the existing canonical `evalArgs`, including
    its order, and can be supplied directly to `Einheit.starts` and `RufStartG`. -/
def arguments (u : UProg) : (types : List Ty) → (args : List SExpr) →
    (checked : types.length = args.length ∧ (types.zip args).all (fun p => uStartArg u.tabs p.1 p.2) = true) →
    Args (declOf u) [] [] types
  | [], [], _ => .nil
  | ty :: types, arg :: args, checked =>
    .cons (expression u ty arg (by exact (Bool.and_eq_true_iff.mp checked.2).1))
      (arguments u types args ⟨by simpa using checked.1, by exact (Bool.and_eq_true_iff.mp checked.2).2⟩)
  | [], _ :: _, checked => by simp at checked
  | _ :: _, [], checked => by simp at checked

/-- A start retains its original arguments and name resolution, together with the existing
    canonical source acceptance check and an argument term at the actual function signature. -/
structure Resolved (u : UProg) (name : String) (sourceArgs : List SExpr) where
  function : (declOf u).Fn
  named : fnIdx u.fns name = .ok function
  canonical : uStartMit u.tabs u.fns name sourceArgs = .ok name
  checked : ((declOf u).params function).length = sourceArgs.length ∧
    (((declOf u).params function).zip sourceArgs).all (fun p => uStartArg u.tabs p.1 p.2) = true

/-- Resolve original source arguments before any names-only root list could discard them. -/
def resolve (u : UProg) (name : String) (sourceArgs : List SExpr) :
    Except String (Resolved u name sourceArgs) := do
  match hn : fnIdx u.fns name with
  | .error e => throw e
  | .ok f =>
    match hc : uStartMit u.tabs u.fns name sourceArgs with
    | .error e => throw e
    | .ok actual =>
      if hr : actual = name then
        if ha : ((declOf u).params f).length = sourceArgs.length ∧
            (((declOf u).params f).zip sourceArgs).all (fun p => uStartArg u.tabs p.1 p.2) = true then
          pure ⟨f, hn, hc.trans (congrArg Except.ok hr), ha⟩
        else throw "ir: source start arguments differ from the canonical function signature"
      else throw "ir: canonical start name differs from its source name"

/-- The existing canonical argument evaluator supplies the semantic start environment;
    writing this full environment to the frame is the shared ABI's separate obligation. -/
def Resolved.environment {u : UProg} {name : String} {sourceArgs : List SExpr}
    (start : Resolved u name sourceArgs) (world : World (declOf u)) :
    Env (declOf u) ((declOf u).params start.function) :=
  evalArgs world (arguments u _ sourceArgs start.checked) world .nil

/-- The reconstructed environment is a valid typed G/GX start, with the exact source
    acceptance and function-name provenance retained rather than a fabricated empty environment. -/
def Resolved.start {u : UProg} {name : String} {sourceArgs : List SExpr}
    (start : Resolved u name sourceArgs) (world : World (declOf u)) :
    Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f) :=
  ⟨start.function, start.environment world⟩

/-- Source origin for one typed start. Duplicate functions with different arguments remain
    distinct entries: a names-only deduplication would lose the specified environments. -/
structure SourceStart (u : UProg) (items : List SItemTief) where
  group : List (List String × List SExpr)
  declared : SItemTief.concT group ∈ items
  path : List String
  sourceArgs : List SExpr
  member : (path, sourceArgs) ∈ group
  name : String
  pathName : path.getLast? = some name
  resolved : Resolved u name sourceArgs

/-- Recover every explicit concurrent start from the original resolved source declarations.
    This is an argument adapter only; hardware entries and dynamically created starts have
    their own contracts and are not silently included as empty argument lists. -/
def fromItems (u : UProg) (items : List SItemTief) :
    Except String (List (SourceStart u items)) := do
  let groups : List (List (SourceStart u items)) ← items.attach.mapM fun item => do
    match hi : item.val with
    | .concT group =>
      group.attach.mapM fun entry => do
        let path := entry.val.1
        let sourceArgs := entry.val.2
        match hp : path.getLast? with
        | none => throw "ir: concurrent start has an empty source path"
        | some name =>
          let resolved ← resolve u name sourceArgs
          pure ⟨group, (by rw [← hi]; exact item.property), path, sourceArgs,
            entry.property, name, hp, resolved⟩
    | _ => pure []
  pure groups.flatten

end Gabbro.Stage0.StartArgument
