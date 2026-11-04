/- Reconstruct start arguments already accepted by the canonical frontend as canonical
   closed expressions. No source evaluator or alternative execution semantics is introduced. -/
module
public import Grammatik.Parser.Elab.UebersetzeAllg
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Stage0.StartArgument
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Reification of exactly the existing `uStartArg` cases into the language's own typed syntax.
    In particular a pointer is a declared carrier capability, never an integer address. -/
def expression (u : UProg) (ty : Ty) (arg : SExpr)
    (accepted : uStartArg u.spaces u.tabs ty arg = true) : Expr (declOf u) [] [] ty := by
  cases ty
  case ptr cap =>
    rcases cap with ⟨space, ⟨read, write, owner⟩, ⟨n⟩⟩
    cases owner with
    | some owner => cases arg <;> simp only [uStartArg, Bool.false_eq_true] at accepted
    | none =>
      cases arg <;> simp only [uStartArg] at accepted
      all_goals try contradiction
      rename_i name
      by_cases hn : n < u.tabs.length
      · simp only [List.getElem?_eq_getElem hn] at accepted
        have nominal : (u.tabs[n]).space = space ∧ space < u.spaces.length :=
          of_decide_eq_true (Bool.and_eq_true_iff.mp accepted).2
        exact Expr.ptrOf (D := declOf u) (⟨n, hn⟩ : Fin u.tabs.length) n
          (Deklaration.capTab_of (tabNr_some u n hn) nominal.1.symm nominal.2) (read, write)
      · have missing : u.tabs[n]? = none := List.getElem?_eq_none (by omega)
        simp only [missing, Bool.false_eq_true] at accepted
  all_goals cases arg <;> simp only [uStartArg] at accepted
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

/-- Reified numeric arguments retain the exact source numeral, not a default initial value. -/
theorem expression_literal (u : UProg) (lo hi : Int) (n : Nat)
    (accepted : uStartArg u.spaces u.tabs (.int lo hi) (.lit n) = true)
    (before world : World (declOf u)) :
    (eval before (expression u (.int lo hi) (.lit n) accepted) world .nil).n = (n : Int) := by
  rfl

theorem expression_negative (u : UProg) (lo hi : Int) (n : Nat)
    (accepted : uStartArg u.spaces u.tabs (.int lo hi) (.un "-" (.lit n)) = true)
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

/-- Canonical accepted start arguments are closed values: choosing a world cannot
    change the environment eventually encoded into a relocated root frame. -/
theorem expression_pure (u : UProg) (ty : Ty) (arg : SExpr)
    (accepted : uStartArg u.spaces u.tabs ty arg = true)
    (before world before' world' : World (declOf u)) :
    eval before (expression u ty arg accepted) world .nil =
      eval before' (expression u ty arg accepted) world' .nil := by
  cases ty
  case ptr cap =>
    change @Eq Unit _ _
    exact Subsingleton.elim _ _
  all_goals cases arg <;> simp only [uStartArg] at accepted
  all_goals try contradiction
  all_goals try rfl
  case int.un lo hi op a =>
    cases a <;> try simp only at accepted
    all_goals try contradiction
    all_goals split at accepted <;> simp_all <;> rfl

/-- Argument environments are evaluated by the existing canonical `evalArgs`, including
    its order, and can be supplied directly to `Einheit.starts` and `RufStartG`. -/
def arguments (u : UProg) : (types : List Ty) → (args : List SExpr) →
    (checked : types.length = args.length ∧ (types.zip args).all (fun p => uStartArg u.spaces u.tabs p.1 p.2) = true) →
    Args (declOf u) [] [] types
  | [], [], _ => .nil
  | ty :: types, arg :: args, checked =>
    .cons (expression u ty arg (by exact (Bool.and_eq_true_iff.mp checked.2).1))
      (arguments u types args ⟨by simpa using checked.1, by exact (Bool.and_eq_true_iff.mp checked.2).2⟩)
  | [], _ :: _, checked => by simp at checked
  | _ :: _, [], checked => by simp at checked

/-- Every complete start environment has the same canonical value in every world. -/
theorem arguments_pure (u : UProg) (types : List Ty) (args : List SExpr)
    (checked : types.length = args.length ∧
      (types.zip args).all (fun p => uStartArg u.spaces u.tabs p.1 p.2) = true)
    (before world before' world' : World (declOf u)) :
    evalArgs before (arguments u types args checked) world .nil =
      evalArgs before' (arguments u types args checked) world' .nil := by
  induction types generalizing args with
  | nil =>
    cases args with
    | nil => rfl
    | cons arg args => have impossible : 0 = args.length + 1 := checked.1; omega
  | cons ty types ih =>
    cases args with
    | nil => simp at checked
    | cons arg args =>
      simp only [arguments, evalArgs]
      congr 1
      · exact expression_pure u ty arg _ before world before' world'
      · exact ih args _


end Gabbro.Stage0.StartArgument
