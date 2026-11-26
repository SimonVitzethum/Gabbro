module

public import Core.Ast.Tree.Root

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

mutual

/-- The enclosing function's result is available in each statement and branch. -/
inductive Stmt (result : Option (Ty .value)) : Scope → Scope → Type where
  /-- `let name = value;`. The name enters scope after the initializer. -/
  | letValue (name : Identifier) (ordinary : name.val ≠ "mut".toList)
      (value : Expr scope type) : Stmt result scope (⟨name, type, false, false⟩ :: scope)
  /-- Assignment to a mutable range local, with SG-1 interval containment. -/
  | assignVar (ref : Local scope (.int lo hi)) (visible : ref.visible)
      (writable : ref.binding.mutable = true) (value : Expr scope (.int valueLo valueHi))
      (fits : Fits (.int valueLo valueHi) (.int lo hi)) : Stmt result scope scope
  /-- The returned expression fits the declared result type of this function. -/
  | ret (declared : result = some expected) (value : Expr scope type)
      (fits : Fits type expected) : Stmt result scope scope
  /-- Only the selected branch runs. Its new bindings are scoped to that branch. -/
  | ite (condition : Expr scope .bool) (yes no : BracedBlock result scope) : Stmt result scope scope
  /-- SYNTAX §6, fallthrough and the explicit void return. -/
  | retVoid (declared : result = none) : Stmt result scope scope
  /-- SYNTAX §7, a scalar mutable local with a written type. -/
  | letMutable (name : Identifier) (ordinary : ordinaryLocal name)
      (written : WrittenType) (valid : written.valid scope) (value : Expr scope type)
      (fits : Fits type written.type) : Stmt result scope (⟨name, written.type, true, false⟩ :: scope)
  /-- SYNTAX §6, direct call whose ordinary result is discarded. -/
  | directCall (call : DirectCall scope) : Stmt result scope scope
  /-- SYNTAX §7, direct call with a written result-binding type. -/
  | bindDirect (name : Identifier) (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
      (written : WrittenType) (valid : written.valid scope) (call : DirectCall scope) :
      Stmt result scope (⟨name, written.type, false, false⟩ :: scope)
  /-- SYNTAX §8, O18. The operation spelling bounds passes and the condition is retested. -/
  | whileBounded (condition : Expr scope .bool)
      (bound : Expr scope (.int lo hi)) (staticBound : bound.static) (nonnegative : 0 ≤ lo)
      (overflow : Identifier) (body : BracedBlock result scope) : Stmt result scope scope
  /-- SYNTAX §8, O18. Static endpoints and a body-local mutable index. -/
  | forRange (name : Identifier) (ordinary : ordinaryLocal name)
      (lo : Expr scope (.int low lowHi)) (hi : Expr scope (.int highLo high))
      (staticBounds : lo.static ∧ hi.static)
      (overflow : Option Identifier)
      (body : BracedBlock result (rangeBinding name low high :: scope)) : Stmt result scope scope
  /-- SYNTAX §7, bind a positional product once, in left-to-right pattern order. -/
  | tupleBind (pattern : TuplePattern) (annotation : Option WrittenType)
      (checked : pattern.valid scope annotation (first :: second :: types))
      (value : Expr scope (tupleType (first :: second :: types))) :
      Stmt result scope (pattern.bindings (first :: second :: types) ++ scope)
  /-- Field assignment updates exactly one position of a writable record local. -/
  | assignField (ref : Local scope (recordValueType name labels types)) (visible : ref.visible)
      (writable : ref.binding.mutable = true) (field : Identifier) (index : Fin types.length)
      (written : RecordFieldAt labels field index.val) (value : Expr scope source)
      (fits : Fits source (types.get index)) : Stmt result scope scope
  /-- The inferred mutable binding uses the initializer's exact type. -/
  | letMutableValue (name : Identifier) (ordinary : ordinaryLocal name)
      (value : Expr scope type) : Stmt result scope (⟨name, type, true, false⟩ :: scope)
  /-- Each arm consumes exactly the next declared tag and payload shape. -/
  | variantMatch (value : Expr scope (variantValueType name labels payloads))
      (arms : VariantArms result scope false labels payloads) : Stmt result scope scope
  | letOption (mutable : Bool) (name : Identifier) (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
      (carrier : Identifier) (resolved : scope.carrierCount carrier = some count)
      (value : OptionInitializer scope count) :
      Stmt result scope (⟨name, indexOptionType count, mutable, false⟩ :: scope)
  | retOption (declared : result = some (indexOptionType count))
      (value : OptionInitializer scope count) : Stmt result scope scope

  /-- Bind an inert address or a typed, non-copyable view. -/
  | letRegion (name : Identifier) (ordinary : name.val ≠ "mut".toList)
      (region : Local scope .ownedRegion) (visible : region.nameVisible)
      (receiverOrdinary : ordinaryLocal region.binding.name)
      (initializer : RegionInitializer) :
      Stmt result scope (⟨name, initializer.type, false, false⟩ :: scope)
  /-- Inventory keys `surface.SAnw.loop` and `syntax.forever`, SYNTAX §8: the unbounded service loop
      `forever [label] { body }`. The body repeats without end; every pass starts in the loop's own
      scope and drops the body's locals before the next pass. No `progress` assumption exists (PERFECT-MODEL
      §5): that the loop is endless is the language's meaning, never an environment promise. The per-pass
      cost, the loop frame and the invariant are written clauses of the loop, not part of this node. -/
  | forever (label : Option Identifier) (body : BracedBlock result scope) : Stmt result scope scope
  /-- The memory access statements (`Access`): the head word `mem` and one access form. -/
  | access (form : Access scope after) : Stmt result scope after

/-- Sequential scope composition inside a pair of braces. -/
inductive Block (result : Option (Ty .value)) : Scope → Scope → Type where
  | done : Block result scope scope
  | step : Stmt result before middle → Block result middle after → Block result before after

/-- Written braces delimit the lifetime and visibility of the body's new locals. -/
inductive BracedBlock (result : Option (Ty .value)) : Scope → Type where
  | braces (body : Block result before after) : BracedBlock result before

/-- Exhaustiveness is the index of an arm sequence. The optional final wildcard
    consumes every remaining declared case without binding a payload. -/
inductive VariantArms (result : Option (Ty .value)) : Scope → Bool →
    List Identifier → List (Option (Ty .value)) → Type where
  | done : VariantArms result scope allowWildcard [] []
  | nullary (label : Identifier) (caseName : label.val ≠ ['_']) (body : BracedBlock result scope)
      (rest : VariantArms result scope true labels payloads) :
      VariantArms result scope allowWildcard (label :: labels) (none :: payloads)
  | payload (label binder : Identifier) (ordinary : ordinaryLocal binder)
      (body : BracedBlock result (payloadBinding binder type :: scope))
      (rest : VariantArms result scope true labels payloads) :
      VariantArms result scope allowWildcard (label :: labels) (some type :: payloads)
  | wildcard (body : BracedBlock result scope) (nonempty : labels ≠ [])
      (shape : labels.length = payloads.length) : VariantArms result scope true labels payloads

end

mutual
def Stmt.returns : Stmt result before after → Bool
  | .ret .. | .retVoid .. | .retOption .. => true
  | .ite _ yes no => yes.returns && no.returns
  | .variantMatch _ arms => arms.returns
  -- No form leaves the loop yet, so control never falls through it.
  | .forever _ _ => true
  | _ => false

def Block.returns : Block result before after → Bool
  | .done => false
  | .step first rest => first.returns || rest.returns

def BracedBlock.returns : BracedBlock result before → Bool
  | .braces body => body.returns

def VariantArms.returns : VariantArms result scope allowed labels payloads → Bool
  | .done => true
  | .nullary _ _ body rest | .payload _ _ _ body rest => body.returns && rest.returns
  | .wildcard body _ _ => body.returns
end

end Gabbro.Core.Ast
