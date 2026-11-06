module
public import Grammatik.Parser.Elab.Konst.Scopes.Environments
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
      uTyp [("LIMIT", (42, 42))] [] [] []
        (.range (.atom "u8") (.lit 0) (.bin "+" (.variable "LIMIT") (.lit 1)) true) =
          .ok (.int lo hi) ∧
      uKonstWert lo hi [] [("LIMIT", 42)] 64 (.variable "LIMIT") = some value ∧
      [("LIMIT", 42), ("ANSWER", 42)] = [("LIMIT", 42)] ++ [("ANSWER", value)] :=
  typedItem_sound [] [] [("LIMIT", 42)] [("LIMIT", 42), ("ANSWER", 42)] "ANSWER"
    (.range (.atom "u8") (.lit 0) (.bin "+" (.variable "LIMIT") (.lit 1)) true)
    (.variable "LIMIT") (by decide +kernel) (by decide +kernel)

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

/-- The generic prefix/lookup chain on actual original declarations, with a negative binding
    read by a later checked expression. No fabricated candidate values enter the certificate. -/
theorem Scopes.prefix_lookup_zeuge :
    let leading : List SItemTief := [.constT "BASE" (.atom "i8") (.one (.un "-" (.lit 1)))]
    let suffix : List SItemTief := [.constT "ANSWER" (.atom "i8")
      (.one (.bin "+" (.variable "BASE") (.lit 43)))]
    ∃ scope : Scopes (leading ++ suffix),
      scope.values.find? (fun entry => strEq entry.1 "BASE") = some ("BASE", -1) := by
  dsimp only
  let scope := evaluatedScopes
    [.constT "BASE" (.atom "i8") (.one (.un "-" (.lit 1))),
     .constT "ANSWER" (.atom "i8") (.one (.bin "+" (.variable "BASE") (.lit 43)))]
    [("BASE", -1), ("ANSWER", 42)] (by decide +kernel)
  refine ⟨scope, Scopes.prefix_lookup scope
    [.constT "BASE" (.atom "i8") (.one (.un "-" (.lit 1)))]
    [.constT "ANSWER" (.atom "i8") (.one (.bin "+" (.variable "BASE") (.lit 43)))]
    [("BASE", -1)] "BASE" ("BASE", -1) rfl ?_ ?_⟩
  · decide +kernel
  · rfl

end Gabbro.Stage0.Frontend
