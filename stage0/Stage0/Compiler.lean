import Stage0.Frontend.Elaboration
import Stage0.Frontend.ArrayConstants
import Stage0.Senke.Ausdruck.Old.Source

namespace Gabbro.Stage0
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Parser.Cover.Differenz

/-- The actual source-to-G endpoint. Canonical elaboration consumes original runtime declarations
    and certified source scopes. The existing old(global) bridge and full checker remain mandatory. -/
structure Compiled (text : String) (options : Profil.Options := {}) where
  source : Frontend.Source text options
  unit : UProg
  main : (declOf unit).Fn
  program : Programm (declOf unit)
  elaborated : Frontend.elabWithScopes
    ((uMembers (pre108 source.items)).map OldSource.normalizeItem)
    source.scopes.values source.scopes.types source.scopes.functions
    (Frontend.tableWithEmpty source.scopes.values source.scopes.types) = .ok unit
  entry : fnIdx unit.fns "main" = .ok main
  lowered : ∃ raw fs, lowerAllg unit = .ok (raw, fs) ∧
    OldSource.restore (uMembers (pre108 source.items)) unit raw = .ok program
  accepted : OldSource.accepts unit program = .ok true
  arrayConstants : ∀ item ∈ uMembers (pre108 source.items), Frontend.ArrayMeaning unit source.scopes item

/-- Compilation only: the result is the same canonical G program passed to the IR emitter. -/
def compile (text : String) (options : Profil.Options := {}) : Except String (Compiled text options) := do
  let source ← Frontend.source text options
  let members := uMembers (pre108 source.items)
  match he : Frontend.elabWithScopes (members.map OldSource.normalizeItem)
      source.scopes.values source.scopes.types source.scopes.functions
      (Frontend.tableWithEmpty source.scopes.values source.scopes.types) with
  | .error e => throw e
  | .ok unit => do
    let arrays ← Frontend.checkArrays unit source.scopes members
    match hm : fnIdx unit.fns "main" with
    | .error e => throw e
    | .ok main =>
      match hl : lowerAllg unit with
      | .error e => throw e
      | .ok (raw, fs) =>
        match hr : OldSource.restore members unit raw with
        | .error e => throw e
        | .ok program =>
          match ha : OldSource.accepts unit program with
          | .error e => throw e
          | .ok false => throw "refused by the checker (AkzeptiertX)"
          | .ok true => pure ⟨source, unit, main, program, he, hm, ⟨raw, fs, hl, hr⟩, ha, arrays.down⟩

/-- Original-source scalar and function semantics, a unique acyclic alias namespace with a
    certified declaration permutation, and the identical
    UProg/declOf/lowerAllg endpoint of the actual compiler. Supplied scopes are not arbitrary premises:
    they are derived from the original declarations by Source.scopes and the canonical evaluators. -/
def CanonicalSourceProgram {text : String} {options : Profil.Options} (result : Compiled text options) : Prop :=
    let original := uMembers (pre108 result.source.items)
    let scope := result.source.scopes
    Profil.runnerCompatible options ∧
    result.source.prepared.selected = result.source.items ∧
    lex text = .ok result.source.tokens ∧
    parseTopTief result.source.tokens = .ok result.source.items ∧
    Oeffentlich.huelleZu result.source.items = true ∧
    (scope.aliasConstants = uConstsRech (uKonstFns original) original [] ∨ scope.aliasConstants = scope.values) ∧
    Frontend.AliasAcyclic original ∧
    (Frontend.aliasNames original).Nodup ∧
    scope.aliasOrder.Perm original ∧
    scope.declared = scope.aliasOrder.foldl (Frontend.aliasStep scope.aliasConstants) [] ∧
    (∀ item ∈ original, Frontend.AliasMeaning scope.types item) ∧
    scope.functions = Frontend.constantFunctions scope.functionTypes original ∧
    (∀ fn ∈ scope.functions, ∃ item ∈ original, Frontend.FunctionMeaning scope.functionTypes item fn) ∧
    (∀ names item table,
      Frontend.tableWithEmpty scope.values scope.types names item = .ok table →
      uTabelle scope.values scope.types names item = .ok table ∨
        Frontend.EmptyTableMeaning scope.values item table) ∧
    Frontend.ScopeStable scope ∧
    Frontend.typedConstants scope.declared scope.functions original [] = some scope.values ∧
    Frontend.compileTimeSafe original = true ∧
    Frontend.elabWithScopes (original.map OldSource.normalizeItem) scope.values scope.types scope.functions
      (Frontend.tableWithEmpty scope.values scope.types) = .ok result.unit ∧
    (∃ raw fs, lowerAllg result.unit = .ok (raw, fs) ∧
      OldSource.restore original result.unit raw = .ok result.program) ∧
    OldSource.accepts result.unit result.program = .ok true ∧
    (∀ item ∈ original, Frontend.ArrayMeaning result.unit scope item)

theorem compile_source_program (text : String) {options : Profil.Options} (result : Compiled text options) :
    CanonicalSourceProgram result := by
  exact ⟨result.source.prepared.compatible, result.source.prepared.unchanged, result.source.lexed, result.source.parsed, result.source.visibility, result.source.scopes.aliasOrigin, result.source.aliasDependencies.1, result.source.aliasDependencies.2, result.source.scopes.aliasPermutation, result.source.scopes.aliases, result.source.aliasMeanings, result.source.scopes.functionOrigin, result.source.scopes.functionMeaning, Frontend.tableWithEmpty_sound _ _, result.source.derived.stable,
    result.source.scopes.scalarValues, result.source.compileTime, result.elaborated, result.lowered,
    result.accepted, result.arrayConstants⟩

end Gabbro.Stage0
