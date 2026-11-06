module
public import Stage0.Zeugen.Annahme.NamedSpace.Scanning
import all Stage0.Zeugen.Annahme.NamedSpace.Scanning
public import Stage0.SourceWitness.Owners
import all Stage0.SourceWitness.Owners
import all Grammatik.Parser.Lex.Lexer.Teil1
import Init.Data.String.Lemmas.Intercalate

@[expose] public section
namespace Gabbro.Stage0.NamedSpaceWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Frontend.ConstPhases
set_option maxRecDepth 2000
set_option maxHeartbeats 400000

namespace Phases

attribute [local cbv_opaque] Frontend.normalize uFloatLimit
attribute [local cbv_eval] String.intercalate_singleton

-- Fix the complete parser and profile results before introducing dependent
-- AliasOrder/DerivedScopes types. No AST or scope snapshot is provided.
def parsed : (pointer : Bool) →
    { items : List SItemTief // parseTopTief (wholeTokens pointer).val = .ok items }
  | false => by
    refine ⟨?plainResult, ?plainResultEq⟩
    case plainResultEq => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?pointerResult, ?pointerResultEq⟩
    case pointerResultEq => cbv <;> exact Eq.refl _

def prepared : (pointer : Bool) →
    { value : Profil.Prepared {} (parsed pointer).val //
      Profil.prepareItems {} (parsed pointer).val = .ok value }
  | false => by
    refine ⟨?plainResult, ?plainResultEq⟩
    case plainResultEq => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?pointerResult, ?pointerResultEq⟩
    case pointerResultEq => cbv <;> exact Eq.refl _

private theorem visibility (pointer : Bool) :
    Oeffentlich.huelleZu (prepared pointer).val.elaborierbar = true := by cases pointer <;> cbv
private theorem compileTime (pointer : Bool) :
    Frontend.compileTimeSafe (uMembers (pre108 (prepared pointer).val.elaborierbar)) = true := by
  cases pointer <;> cbv

def input (pointer : Bool) : SourceInput (sourceText pointer) where
  tokens := (wholeTokens pointer).val
  items := (parsed pointer).val
  lexed := by exact lexed pointer
  parsed := by exact (parsed pointer).property
  prepared := (prepared pointer).val
  preparation := by exact (prepared pointer).property
  visibility := by exact visibility pointer
  compileTime := by exact compileTime pointer

def original : (pointer : Bool) →
    { items : List SItemTief // (input pointer).original = items }
  | false => by
    refine ⟨?plainResult, ?plainResultEq⟩
    case plainResultEq => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?pointerResult, ?pointerResultEq⟩
    case pointerResultEq => cbv <;> exact Eq.refl _

private theorem metadata (pointer : Bool) :
    Konst.checkSourceMetadata (original pointer).val = .ok () := by cases pointer <;> cbv

def ordered : (pointer : Bool) →
    { order : Frontend.AliasOrder (original pointer).val //
      Frontend.orderAliases (original pointer).val = .ok order }
  | false => by
    refine ⟨?plainResult, ?plainResultEq⟩
    case plainResultEq => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?pointerResult, ?pointerResultEq⟩
    case pointerResultEq => cbv <;> exact Eq.refl _

def scopes : (pointer : Bool) →
    { derived : Frontend.DerivedScopes (original pointer).val //
      Frontend.elaborateConstantScopes (original pointer).val = .ok derived }
  | false => by
    refine ⟨?plainResult, ?plainResultEq⟩
    case plainResultEq => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?pointerResult, ?pointerResultEq⟩
    case pointerResultEq => cbv <;> exact Eq.refl _

private theorem aliases (pointer : Bool) :
    (original pointer).val.all (Frontend.checkAliasMeaning (scopes pointer).val.scope.types) = true := by
  cases pointer <;> cbv
private theorem constants (pointer : Bool) :
    (original pointer).val.all (Frontend.checkConstantMeaning (scopes pointer).val.scope.types
      (scopes pointer).val.scope.functions (scopes pointer).val.scope.values) = true := by
  cases pointer <;> cbv

def tail (pointer : Bool) : SourceTail (input pointer) :=
  SourceTail.ofOriginal (input pointer) (original pointer).val (original pointer).property
    (by exact metadata pointer) (ordered pointer).val (ordered pointer).property
    (scopes pointer).val (scopes pointer).property
    (by exact aliases pointer) (by exact constants pointer)

def source (pointer : Bool) : Frontend.Source (sourceText pointer) :=
  sourceFrom (input pointer) (tail pointer)

-- Opaque whole-field equations transport the same source packet without
-- repeatedly reopening the normalizer or the indexed SourceTail constructor.
theorem source_original (pointer : Bool) :
    uMembers (pre108 (source pointer).prepared.elaborierbar) = (original pointer).val :=
  (original pointer).property

theorem source_metadata (pointer : Bool) :
    Konst.checkSourceMetadata (uMembers (pre108 (source pointer).prepared.elaborierbar)) = .ok () := by
  rw [source_original]
  exact metadata pointer

end Phases
end Gabbro.Stage0.NamedSpaceWitness
