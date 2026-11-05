module
public import Stage0.Frontend.Source

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstPhases
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The actual input phases, including the unchanged profile and source-hull guards. -/
structure SourceInput (text : String) where
  tokens : List Token
  items : List SItemTief
  lexed : lex text = .ok tokens
  parsed : parseTopTief tokens = .ok items
  prepared : Profil.Prepared {} items
  preparation : Profil.prepareItems {} items = .ok prepared
  visibility : Oeffentlich.huelleZu prepared.elaborierbar = true
  compileTime : Frontend.compileTimeSafe (uMembers (pre108 prepared.elaborierbar)) = true

def SourceInput.original {text : String} (input : SourceInput text) : List SItemTief :=
  uMembers (pre108 input.prepared.elaborierbar)

/-- Complete successes of the remaining source phases, before dependent scope projections. -/
structure SourceTail {text : String} (input : SourceInput text) where
  metadata : Konst.checkSourceMetadata input.original = .ok ()
  order : Frontend.AliasOrder input.original
  ordered : Frontend.orderAliases input.original = .ok order
  derived : Frontend.DerivedScopes input.original
  elaborated : Frontend.elaborateConstantScopes input.original = .ok derived
  aliases : input.original.all (Frontend.checkAliasMeaning derived.scope.types) = true
  constants : input.original.all
    (Frontend.checkConstantMeaning derived.scope.types derived.scope.functions derived.scope.values) = true

/-- Retain the canonical normalizer and its generic proof without reducing that proof at each fixture. -/
def sourceFrom {text : String} (input : SourceInput text) (tail : SourceTail input) :
    Frontend.Source text where
  tokens := input.tokens
  items := input.items
  members := (Frontend.normalize input.original).val
  lexed := input.lexed
  parsed := input.parsed
  prepared := input.prepared
  visibility := input.visibility
  compileTime := input.compileTime
  normalized := (Frontend.normalize input.original).property
  aliasDependencies := ⟨tail.order.acyclic, tail.order.unique⟩
  constantDependencies := Frontend.elaborateConstantScopes_dependencies
    input.original tail.derived tail.elaborated
  derived := tail.derived
  aliasMeanings := fun item member => Frontend.checkAliasMeaning_sound _ _
    (List.all_eq_true.mp tail.aliases item member)
  constantMeanings := fun item member => Frontend.checkConstantMeaning_sound _ _ _ _
    (List.all_eq_true.mp tail.constants item member)

/-- Replay every actual source branch against the complete phase packets. -/
theorem sourceFrom_eq {text : String} (input : SourceInput text) (tail : SourceTail input) :
    Frontend.source text = .ok (sourceFrom input tail) := by
  unfold Frontend.source
  split
  · rename_i error rejected
    cases rejected.symm.trans input.lexed
  · rename_i tokens selected
    have same : tokens = input.tokens := Except.ok.inj (selected.symm.trans input.lexed)
    subst tokens
    split
    · rename_i error rejected
      cases rejected.symm.trans input.parsed
    · rename_i items selected
      have same : items = input.items := Except.ok.inj (selected.symm.trans input.parsed)
      subst items
      split
      · rename_i error rejected
        cases rejected.symm.trans input.preparation
      · rename_i prepared selected
        have same : prepared = input.prepared :=
          Except.ok.inj (selected.symm.trans input.preparation)
        subst prepared
        split
        · split
          · dsimp only [bind, Except.bind]
            split
            · rename_i error rejected
              cases rejected.symm.trans tail.metadata
            · rename_i value selected
              cases value
              split
              · rename_i error rejected
                cases rejected.symm.trans tail.ordered
              · rename_i order selected
                have same : order = tail.order :=
                  Except.ok.inj (selected.symm.trans tail.ordered)
                subst order
                split
                · rename_i error rejected
                  cases rejected.symm.trans tail.elaborated
                · rename_i derived selected
                  have same : derived = tail.derived :=
                    Except.ok.inj (selected.symm.trans tail.elaborated)
                  subst derived
                  split
                  · split
                    · rfl
                    · rename_i rejected
                      exact False.elim (rejected tail.constants)
                  · rename_i rejected
                    exact False.elim (rejected tail.aliases)
          · rename_i rejected
            exact False.elim (rejected input.compileTime)
        · rename_i rejected
          exact False.elim (rejected input.visibility)

/-- A real metadata failure stops the same source pipeline before alias/scope construction. -/
theorem source_metadata_refused {text : String} (input : SourceInput text) (error : String)
    (refused : Konst.checkSourceMetadata input.original = .error error) :
    Frontend.source text = .error error := by
  unfold Frontend.source
  split
  · rename_i error rejected
    cases rejected.symm.trans input.lexed
  · rename_i tokens selected
    have same : tokens = input.tokens := Except.ok.inj (selected.symm.trans input.lexed)
    subst tokens
    split
    · rename_i error rejected
      cases rejected.symm.trans input.parsed
    · rename_i items selected
      have same : items = input.items := Except.ok.inj (selected.symm.trans input.parsed)
      subst items
      split
      · rename_i error rejected
        cases rejected.symm.trans input.preparation
      · rename_i prepared selected
        have same : prepared = input.prepared :=
          Except.ok.inj (selected.symm.trans input.preparation)
        subst prepared
        split
        · split
          · dsimp only [bind, Except.bind]
            split
            · rename_i actual selected
              have same : actual = error := Except.error.inj (selected.symm.trans refused)
              subst actual
              rfl
            · rename_i value selected
              cases selected.symm.trans refused
          · rename_i rejected
            exact False.elim (rejected input.compileTime)
        · rename_i rejected
          exact False.elim (rejected input.visibility)

end Gabbro.Stage0.Frontend.ConstPhases
