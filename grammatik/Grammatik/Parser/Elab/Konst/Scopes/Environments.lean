module
public import Grammatik.Parser.Elab.Konst.Scopes.Folds
public import Grammatik.Parser.Elab.Konst.Scopes.Correctness
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

-- One canonical source-scope implementation, shared with the Stage0 compiler.
namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- Complete ordered scalar scope: negatives and shadowed bindings are not filtered. -/
def typedConstants (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (items : List SItemTief) (values : List (String × Int)) : Option (List (String × Int)) :=
  items.foldlM (typedItem env fns) values

/-- Canonical scalar evaluation composes in source order with the entire intermediate scope;
    neither negative bindings nor shadowed names can be filtered at a declaration boundary. -/
theorem typedConstants_append (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (first rest : List SItemTief) (values : List (String × Int)) :
    typedConstants env fns (first ++ rest) values =
      (typedConstants env fns first values).bind (typedConstants env fns rest) := by
  exact List.foldlM_append

/-- The actual successful fold keeps its entire input scope as a prefix, never a filtered or
    reordered candidate. Deferred declarations still require the mandatory final literal gate. -/
theorem typedConstants_extends (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (items : List SItemTief) (values result : List (String × Int))
    (accepted : typedConstants env fns items values = some result) :
    ∃ suffix, result = values ++ suffix := by
  induction items generalizing values result with
  | nil =>
    exact ⟨[], by simpa only [List.append_nil] using (Option.some.inj accepted).symm⟩
  | cons item rest ih =>
    change (typedItem env fns values item).bind (typedConstants env fns rest) = some result at accepted
    cases step : typedItem env fns values item with
    | none => simp only [step, Option.bind_none, reduceCtorEq] at accepted
    | some next =>
      have tail : typedConstants env fns rest next = some result := by
        simpa only [step, Option.bind_some] using accepted
      obtain ⟨headSuffix, headEq⟩ := typedItem_extends env fns values next item step
      obtain ⟨tailSuffix, tailEq⟩ := ih next result tail
      exact ⟨headSuffix ++ tailSuffix, by rw [tailEq, headEq, List.append_assoc]⟩

/-- Canonical first-match lookup is stable under every successful scalar fold, even when
    later declarations repeat a spelling. Namespace uniqueness remains a separate mandatory gate. -/
theorem typedConstants_lookup (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (items : List SItemTief) (values result : List (String × Int)) (name : String)
    (binding : String × Int) (accepted : typedConstants env fns items values = some result)
    (found : values.find? (fun entry => strEq entry.1 name) = some binding) :
    result.find? (fun entry => strEq entry.1 name) = some binding := by
  obtain ⟨suffix, extended⟩ := typedConstants_extends env fns items values result accepted
  simp only [extended, List.find?_append, found, Option.some_or]


theorem typedItem_aliasItem (values : List (String × Int))
    (typeEnv aliasEnv : List (String × (Int × Int))) (fns : List UKonstFn) (item : SItemTief) :
    typedItem typeEnv fns values (aliasItem aliasEnv item) = typedItem typeEnv fns values item := by
  rcases aliasItem_sound aliasEnv item with h | ⟨flags, name, order, original, body, hs, ht, _⟩
  · rw [← h]
  · rw [ht, hs]
    rfl

/-- The source typed constant scope is derived from original declarations, not rewritten ones. -/
theorem typedConstants_aliases (initial values : List (String × Int))
    (typeEnv aliasEnv : List (String × (Int × Int))) (fns : List UKonstFn) (items : List SItemTief) :
    typedConstants typeEnv fns (aliases initial aliasEnv items) values =
      typedConstants typeEnv fns items values := by
  induction items generalizing aliasEnv values with
  | nil => rfl
  | cons item rest ih =>
    change (typedItem typeEnv fns values (aliasItem aliasEnv item)).bind
      (fun next => typedConstants typeEnv fns
        (aliases initial (aliasEnv ++ uAliase initial [aliasItem aliasEnv item]) rest) next) =
      (typedItem typeEnv fns values item).bind (fun next => typedConstants typeEnv fns rest next)
    rw [typedItem_aliasItem]
    congr 1
    funext next
    exact ih _ _

theorem constantFunction_aliasItem (typeEnv aliasEnv : List (String × (Int × Int)))
    (item : SItemTief) : constantFunction typeEnv (aliasItem aliasEnv item) = constantFunction typeEnv item := by
  rcases aliasItem_sound aliasEnv item with h | ⟨flags, name, order, original, body, hs, ht, _⟩
  · rw [← h]
  · rw [ht, hs]
    rfl

/-- Compile-time candidates come from the original source function declarations with unchanged
    bodies and checked canonical signatures; alias normalization cannot create a function. -/
theorem constantFunctions_aliases (initial : List (String × Int))
    (typeEnv aliasEnv : List (String × (Int × Int))) (items : List SItemTief) :
    constantFunctions typeEnv (aliases initial aliasEnv items) = constantFunctions typeEnv items := by
  induction items generalizing aliasEnv with
  | nil => rfl
  | cons item rest ih =>
    simp only [aliases, rewrite, constantFunctions, List.filterMap_cons]
    rw [constantFunction_aliasItem]
    have hr := ih (aliasEnv ++ uAliase initial [aliasItem aliasEnv item])
    cases hf : constantFunction typeEnv item with
    | none => simpa only [hf, constantFunctions, aliases] using hr
    | some fn => simpa only [hf, constantFunctions, aliases] using congrArg (List.cons fn) hr

/-- Canonical source scopes derived before runtime elaboration. Alias and scalar collection
    schedules retain certified declaration permutations, and functions keep their
    original bodies and signatures. Alias ranges use aliasStep; scalar values use typedConstants
    at every original declared range. -/
structure Scopes (original : List SItemTief) where
  values : List (String × Int)
  declared : List (String × (Int × Int))
  functions : List UKonstFn
  aliasConstants : List (String × Int)
  aliasOrigin : aliasConstants = uConstsRech (uKonstFns original) original [] ∨ aliasConstants = values
  functionsUseValues : Bool
  aliasOrder : List SItemTief
  aliasPermutation : aliasOrder.Perm original
  aliases : declared = aliasOrder.foldl (aliasStep aliasConstants) []
  functionOrigin : functions = constantFunctions
    (if functionsUseValues then declared ++ values.map (fun c => (c.1, (c.2, c.2))) else declared) original
  scalarOrder : List SItemTief
  scalarPermutation : scalarOrder.Perm original
  scalarValues : typedConstants declared functions scalarOrder [] = some values

/-- A binding found after any original scheduled prefix remains the first binding in the
    final certified scope. The suffix is evaluated by the same fold used by scalarValues. -/
theorem Scopes.prefix_lookup {original : List SItemTief} (scope : Scopes original)
    (leading suffix : List SItemTief) (values : List (String × Int)) (name : String) (binding : String × Int)
    (schedule : scope.scalarOrder = leading ++ suffix)
    (evaluated : typedConstants scope.declared scope.functions leading [] = some values)
    (found : values.find? (fun entry => strEq entry.1 name) = some binding) :
    scope.values.find? (fun entry => strEq entry.1 name) = some binding := by
  have final := scope.scalarValues
  rw [schedule, typedConstants_append, evaluated] at final
  exact typedConstants_lookup scope.declared scope.functions suffix values scope.values name binding final found

/-- The canonical environment used to elaborate compile-time function signatures. Existing
    scopes use declared aliases; dependent signatures additionally use certified scalar bounds. -/
def Scopes.functionTypes {items : List SItemTief} (scope : Scopes items) : List (String × (Int × Int)) :=
  if scope.functionsUseValues then scope.declared ++ scope.values.map (fun c => (c.1, (c.2, c.2)))
    else scope.declared

/-- Every function supplied to canonical scalar or nested-array evaluation retains its original
    body, pure/nonlogical clauses and exact canonical source signature. -/
theorem Scopes.functionMeaning {items : List SItemTief} (scope : Scopes items) :
    ∀ fn ∈ scope.functions, ∃ item ∈ items, FunctionMeaning scope.functionTypes item fn := by
  rw [scope.functionOrigin]
  exact constantFunctions_sound _ _

/-- The exact full name/type scope the canonical phase body consumes. -/
def Scopes.types {original : List SItemTief} (scope : Scopes original) : List (String × (Int × Int)) :=
  scope.declared ++ scope.values.map (fun c => (c.1, (c.2, c.2)))

/-- Final scalar values must leave all resolved alias ranges unchanged. -/
def ScopeStable {items : List SItemTief} (scope : Scopes items) : Prop :=
  uAliase scope.values (aliases scope.aliasConstants [] scope.aliasOrder) = scope.declared

/-- The canonical source-derived alias schedule and final-value stability are kept together. -/
structure DerivedScopes (items : List SItemTief) where
  scope : Scopes items
  stable : ScopeStable scope

/-- Construct scopes from the existing canonical evaluator at each original declared range.
    There is no executable source interpreter or alternative expression evaluation here. -/
def evaluatedScopes (items : List SItemTief) (values : List (String × Int))
    (h : typedConstants (prepare items).env (prepare items).fns items [] = some values) : Scopes items :=
  ⟨values, (prepare items).env, (prepare items).fns, (prepare items).initial,
    Or.inl rfl, false, items, .refl _,
    (by simpa only [prepare, List.nil_append] using (aliases_collected (prepare items).initial [] items)),
    constantFunctions_aliases (prepare items).initial (prepare items).env [] items, items, .refl _, h⟩

/-- The actual consumer needs the certified original scalar fold, not a second encoding through
    the legacy collector's builtin-only constant declarations. Preserve full alias stability. -/
def deriveScopes (items : List SItemTief) : Except String (DerivedScopes items) :=
  match h : typedConstants (prepare items).env (prepare items).fns items [] with
  | none => .error "compile-time scalar cannot be evaluated at its canonical declared range"
  | some values =>
    if hs : uAliase values (prepare items).expanded = (prepare items).env then
      .ok ⟨evaluatedScopes items values h, hs⟩
    else .error "compile-time alias range environment is not stable"

end Gabbro.Stage0.Frontend
