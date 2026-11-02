module
public import Stage0.Frontend.EnvironmentsPart1
public import Stage0.Frontend.Correctness
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


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- A dependent exclusive range is checked with the previous binding, without widening it. -/
theorem typedItem_sound_zeuge :
    ∃ lo hi value,
      uTyp [("LIMIT", (42, 42))] [] []
        (.range (.atom "u8") (.lit 0) (.bin "+" (.variable "LIMIT") (.lit 1)) true) =
          .ok (.int lo hi) ∧
      uKonstWert lo hi [] [("LIMIT", 42)] 64 (.variable "LIMIT") = some value ∧
      [("LIMIT", 42), ("ANSWER", 42)] = [("LIMIT", 42)] ++ [("ANSWER", value)] :=
  typedItem_sound [] [] [("LIMIT", 42)] [("LIMIT", 42), ("ANSWER", 42)] "ANSWER"
    (.range (.atom "u8") (.lit 0) (.bin "+" (.variable "LIMIT") (.lit 1)) true)
    (.variable "LIMIT") (by decide +kernel)

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

/-- Full ordered canonical environments must agree with the typed source declaration fold.
    Also require stability of alias ranges when newly folded constants become visible. -/
def EnvironmentCompatible (source target : List SItemTief) : Prop :=
  let p := prepare source
  let final := uConstsRech (uKonstFns target) target []
  typedConstants p.env p.fns p.expanded [] = some final ∧
    uAliase final p.expanded = p.env

instance (source target : List SItemTief) : Decidable (EnvironmentCompatible source target) := by
  unfold EnvironmentCompatible
  infer_instance

/-- Exact environments used by the downstream canonical elaborator, not merely output values. -/
def EnvironmentFacts (source target : List SItemTief) : Prop :=
  let p := prepare source
  let final := uConstsRech (uKonstFns target) target []
  typedConstants p.env p.fns p.expanded [] = some final ∧
    uAliase final target = p.env ∧
    uAliase p.initial p.expanded = source.foldl (aliasStep p.initial) []

/-- The checked equality supplies accepted-subset preservation; alias declaration collection is
    proved generically at arbitrary final constant environments. This is not total coverage. -/
theorem normalize_environments (items : List SItemTief)
    (h : EnvironmentCompatible items (normalizeAliases items)) :
    EnvironmentFacts items (normalizeAliases items) := by
  obtain ⟨hc, ha⟩ := h
  refine ⟨hc, ?_, ?_⟩
  · change uAliase _ (constants _ _ [] _) = _
    rw [constants_aliases]
    exact ha
  · simpa only [prepare, List.nil_append] using
      aliases_collected (prepare items).initial [] items

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

/-- Full source scope derivation: the local rewrites are eliminated from scalar/function origin
    facts, and the resulting environments are tied to the original declaration list. -/
def scopes (items target : List SItemTief)
    (h : EnvironmentFacts items target) : Scopes items := by
  let p := prepare items
  refine ⟨uConstsRech (uKonstFns target) target [], p.env, p.fns, p.initial,
    Or.inl rfl, false, items, .refl _, h.2.2, ?_, items, .refl _, ?_⟩
  · exact constantFunctions_aliases p.initial p.env [] items
  · have hc := h.1
    change typedConstants p.env p.fns p.expanded [] = _ at hc
    have ha : typedConstants p.env p.fns p.expanded [] = typedConstants p.env p.fns items [] :=
      typedConstants_aliases p.initial [] p.env [] p.fns items
    rw [ha] at hc
    exact hc

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

/-- Every old successful exact-collector comparison yields the same complete ordered scopes
    through the direct path. Thus removing that representation check changes no old endpoint. -/
theorem deriveScopes_of_compatible (items : List SItemTief)
    (h : EnvironmentCompatible items (normalizeAliases items)) :
    ∃ result, deriveScopes items = .ok result ∧
      result.scope = scopes items (normalizeAliases items) (normalize_environments items h) := by
  let old := scopes items (normalizeAliases items) (normalize_environments items h)
  have hv : typedConstants (prepare items).env (prepare items).fns items [] = some old.values :=
    old.scalarValues
  have hs : uAliase old.values (prepare items).expanded = (prepare items).env := h.2
  have he : deriveScopes items = .ok ⟨evaluatedScopes items old.values hv, hs⟩ := by
    unfold deriveScopes
    split
    · rename_i hx
      rw [hx] at hv
      contradiction
    · rename_i values hx
      have eqValues : values = old.values := Option.some.inj (hx.symm.trans hv)
      subst values
      simp only [hs, ↓reduceDIte]
  refine ⟨_, he, ?_⟩
  rfl

/-- A custom range with no exact builtin retains its negative intermediate and dependent value. -/
theorem deriveScopes_custom_negative_zeuge :
    let items := [SItemTief.typeT [] "Small" [] []
        (some (.range (.atom "i8") (bound (-10)) (.lit 100) false)),
      .constT "NEGATIVE" (.atom "Small") (.one (.bin "-" (.lit 0) (.lit 1))),
      .constT "ANSWER" (.atom "Small") (.one (.bin "+" (.variable "NEGATIVE") (.lit 43)))]
    ∃ result, deriveScopes items = .ok result ∧
      result.scope.values = [("NEGATIVE", -1), ("ANSWER", 42)] ∧
      result.scope.declared = [("Small", (-10, 100))] ∧
      ¬ EnvironmentCompatible items (normalizeAliases items) := by
  dsimp only
  refine ⟨(deriveScopes _).toOption.get (by decide +kernel), ?_, ?_, ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  all_goals decide +kernel

end Gabbro.Stage0.Frontend
