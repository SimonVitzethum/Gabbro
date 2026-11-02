module
public import Stage0.Frontend.Elaboration
public import Stage0.Frontend.ArrayConstants
public import Stage0.Frontend.Initializers
public import Stage0.Senke.Ausdruck.Old.Source
@[expose] public section


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
  elaborated : (Frontend.elabWithScopes
    ((uMembers (pre108 source.items)).map OldSource.normalizeItem)
    source.scopes.values source.scopes.types source.scopes.functions
    (Frontend.tableWithEmpty source.scopes.values source.scopes.types)).map
      (fun u => {u with exportGate := ExportMetadata.check (uMembers (pre108 source.items))}) = .ok unit
  entry : fnIdx unit.fns "main" = .ok main
  lowered : ∃ raw fs, lowerAllg unit = .ok (raw, fs) ∧
    OldSource.restore (uMembers (pre108 source.items)) unit raw = .ok program
  accepted : OldSource.accepts unit program = .ok true
  arrayConstants : ∀ item ∈ uMembers (pre108 source.items), Frontend.ArrayMeaning unit source.scopes item
  initializerExports : Frontend.checkInitializers (uMembers (pre108 source.items)) unit = .ok ()
  constantExports : ExportMetadata.checkConstants (uMembers (pre108 source.items)) = .ok ()
  metadata : unit.exportGate = ExportMetadata.check (uMembers (pre108 source.items))

/-- Compilation only: the result is the same canonical G program passed to the IR emitter. -/
def compile (text : String) (options : Profil.Options := {}) : Except String (Compiled text options) := do
  let source ← Frontend.source text options
  let members := uMembers (pre108 source.items)
  match hc : ExportMetadata.checkConstants members with
  | .error error => throw error
  | .ok () => do
    match he : Frontend.elabWithScopes (members.map OldSource.normalizeItem)
        source.scopes.values source.scopes.types source.scopes.functions
        (Frontend.tableWithEmpty source.scopes.values source.scopes.types) with
    | .error e => throw e
    | .ok candidate => do
      let unit := {candidate with exportGate := ExportMetadata.check members}
      have elaborated : (Frontend.elabWithScopes (members.map OldSource.normalizeItem)
          source.scopes.values source.scopes.types source.scopes.functions
          (Frontend.tableWithEmpty source.scopes.values source.scopes.types)).map
            (fun u => {u with exportGate := ExportMetadata.check members}) = .ok unit := by
        rw [he]
        rfl
      match hi : Frontend.checkInitializers members unit with
      | .error error => throw error
      | .ok () => do
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
              | .ok true => pure ⟨source, unit, main, program, elaborated, hm, ⟨raw, fs, hl, hr⟩, ha, arrays.down, hi, hc, rfl⟩

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
    Frontend.ConstantAcyclic original ∧
    (Frontend.constantNames original).Nodup ∧
    scope.scalarOrder.Perm original ∧
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
    Frontend.typedConstants scope.declared scope.functions scope.scalarOrder [] = some scope.values ∧
    (∀ item ∈ original, Frontend.ConstantMeaning scope.types scope.functions scope.values item) ∧
    Frontend.checkInitializers original result.unit = .ok () ∧
    ExportMetadata.checkConstants original = .ok () ∧
    Frontend.compileTimeSafe original = true ∧
    (Frontend.elabWithScopes (original.map OldSource.normalizeItem) scope.values scope.types scope.functions
      (Frontend.tableWithEmpty scope.values scope.types)).map
        (fun u => {u with exportGate := ExportMetadata.check original}) = .ok result.unit ∧
    (∃ raw fs, lowerAllg result.unit = .ok (raw, fs) ∧
      OldSource.restore original result.unit raw = .ok result.program) ∧
    OldSource.accepts result.unit result.program = .ok true ∧
    (∀ item ∈ original, Frontend.ArrayMeaning result.unit scope item) ∧
    result.unit.exportGate = ExportMetadata.check original

theorem compile_source_program (text : String) {options : Profil.Options} (result : Compiled text options) :
    CanonicalSourceProgram result := by
  exact ⟨result.source.prepared.compatible, result.source.prepared.unchanged, result.source.lexed, result.source.parsed, result.source.visibility, result.source.scopes.aliasOrigin, result.source.aliasDependencies.1, result.source.aliasDependencies.2, result.source.constantDependencies.1, result.source.constantDependencies.2, result.source.scopes.scalarPermutation, result.source.scopes.aliasPermutation, result.source.scopes.aliases, result.source.aliasMeanings, result.source.scopes.functionOrigin, result.source.scopes.functionMeaning, Frontend.tableWithEmpty_sound _ _, result.source.derived.stable,
    result.source.scopes.scalarValues, result.source.constantMeanings, result.initializerExports, result.constantExports, result.source.compileTime, result.elaborated, result.lowered,
    result.accepted, result.arrayConstants, result.metadata⟩

/-- Every function the compiled unit generated for a transition declaration is in the lowered
    G program and carries its expansion certificate there (the program before the old(global)
    restoration, which replaces only `ensures`; a generated function has no `old` clause, so
    the restoration keeps its `ensures`). The call theorems of the certificate relate every
    successful call of it to the declaration's full pre/post relation and frame; no generated
    function is emitted without this certificate because `lowerAllg` refuses its name otherwise. -/
theorem compile_transitions_certified {text : String} {options : Profil.Options}
    (result : Compiled text options) :
    ∃ raw fs, lowerAllg result.unit = .ok (raw, fs) ∧
      OldSource.restore (uMembers (pre108 result.source.items)) result.unit raw = .ok result.program ∧
      ∀ c : Fin result.unit.fns.length, (fnAt result.unit c).name.startsWith "#transition#" = true →
        ∃ (state : UZustand) (tr : UTransition), transitionOfFn result.unit c = some (state, tr) ∧
          (Nonempty (TransitionExpansion raw c) ∨ Nonempty (TransitionShiftExpansion raw c)) := by
  obtain ⟨raw, fs, hl, hr⟩ := result.lowered
  exact ⟨raw, fs, hl, hr, fun c hname => lowerAllg_transition_certified result.unit raw fs hl c hname⟩

end Gabbro.Stage0
