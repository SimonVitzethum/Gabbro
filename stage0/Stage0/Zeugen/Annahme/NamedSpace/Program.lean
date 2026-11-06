module
public import Stage0.Zeugen.Annahme.NamedSpace.Input
public import Stage0.Frontend.Witnesses.Constants.ProgramPackets
import Init.Data.String.Lemmas.Intercalate
import all Stage0.Zeugen.Annahme.NamedSpace.Input
import all Stage0.SourceWitness.Owners
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance

@[expose] public section
namespace Gabbro.Stage0.NamedSpaceWitness.Phases
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Frontend.ConstPhases
set_option maxRecDepth 2000
set_option maxHeartbeats 400000

attribute [local cbv_opaque] Frontend.normalize uFloatLimit lowStufe lowSeqL lowStructL
attribute [local cbv_eval]
  Gabbro.Grammatik.Parser.UebersetzeProben2.seq_select
  Gabbro.Grammatik.Parser.UebersetzeProben2.struct_select lowStufe_seq lowStufe_struct
  source_original String.intercalate_singleton

-- Infer complete results from the existing producers. Header is a thin record
-- of these values and closed equations; no dependent result is guessed there.
def expansion : (pointer : Bool) →
    { value : List SItemTief × List (STyp × String) //
      Modules.prepare (pre108 (source pointer).prepared.elaborierbar) = .ok value }
  | false => by
    refine ⟨?plainResult, ?plainResultEq⟩
    case plainResultEq => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?pointerResult, ?pointerResultEq⟩
    case pointerResultEq => cbv <;> exact Eq.refl _

private theorem constantGate (pointer : Bool) :
    Konst.checkSourceConstants (uMembers (pre108 (source pointer).prepared.elaborierbar)) = .ok () := by
  unfold Konst.checkSourceConstants
  split
  · exact source_metadata pointer
  · rfl

private theorem ordinary (pointer : Bool) :
    (uMembers (pre108 (source pointer).prepared.elaborierbar)).any Frontend.expansionHeader = false := by
  rw [source_original]
  cases pointer <;> cbv

def candidateUnit : (pointer : Bool) →
    { value : UProg //
      ((Frontend.elabWithScopes (pre108 (source pointer).prepared.elaborierbar)
        (source pointer).scopes.values (source pointer).scopes.types (source pointer).scopes.functions
        (Frontend.tableWithEmpty (source pointer).scopes.values (source pointer).scopes.types)).bind
        (Profil.selectUnit {})) = .ok value }
  | false => by
    refine ⟨?plainResult, ?plainResultEq⟩
    case plainResultEq => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?pointerResult, ?pointerResultEq⟩
    case pointerResultEq => cbv <;> exact Eq.refl _

def header (pointer : Bool) : Header (sourceText pointer) where
  source := source pointer
  sourceEq := by exact sourceFrom_eq (input pointer) (tail pointer)
  expanded := (expansion pointer).val.1
  requirements := (expansion pointer).val.2
  expansion := by exact (expansion pointer).property
  constants := by exact constantGate pointer
  ordinary := by exact ordinary pointer
  metadata := by exact source_metadata pointer
  candidate := (candidateUnit pointer).val
  elaborated := by exact (candidateUnit pointer).property

-- Only the compiler's already checked metadata field is normalized here.
-- Every other field is the same actual whole candidate returned above.
def unit (pointer : Bool) : UProg := { (candidateUnit pointer).val with exportGate := .ok () }

theorem header_unit (pointer : Bool) : (header pointer).unit = unit pointer := by
  unfold Header.unit header
  dsimp only
  rw [source_metadata]
  rfl

attribute [local cbv_eval] header_unit

private theorem main_ordinary : "main".startsWith "#transition#" = false := by
  decide +kernel

attribute [local cbv_eval] main_ordinary

private theorem function_count (pointer : Bool) : (header pointer).unit.fns.length = 1 := by
  rw [header_unit]
  cases pointer <;> cbv

def main (pointer : Bool) : Fin (header pointer).unit.fns.length :=
  ⟨0, by have count := function_count pointer; omega⟩

private theorem only_main (pointer : Bool) (f : Fin (header pointer).unit.fns.length) :
    f = main pointer := by
  apply Fin.ext
  have bound : f.val < 1 := by simpa only [function_count pointer] using f.isLt
  change f.val = 0
  omega

def code : (pointer : Bool) →
    { value : EnsTy (header pointer).unit (main pointer) ×
        RumpTy (header pointer).unit (main pointer) × ReqTy (header pointer).unit (main pointer) //
      lowerFnAt (header pointer).unit (main pointer) = .ok value }
  | false => by
    refine ⟨?plainResult, ?plainResultEq⟩
    case plainResultEq => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?pointerResult, ?pointerResultEq⟩
    case pointerResultEq => cbv <;> exact Eq.refl _

-- Transport the complete actual triple at an abstract unit before substituting
-- either fixture. In particular, Functions.values never re-runs lowerFnAt
-- through a toOption.get when the image builder asks for a body.
def selectedCode {u : UProg} {m : Fin u.fns.length}
    (only : ∀ f : Fin u.fns.length, f = m)
    (result : { value : EnsTy u m × RumpTy u m × ReqTy u m // lowerFnAt u m = .ok value })
    (f : Fin u.fns.length) :
    { value : EnsTy u f × RumpTy u f × ReqTy u f // lowerFnAt u f = .ok value } := by
  cases only f
  exact result

private theorem noInvariants (pointer : Bool) : (header pointer).unit.invs = [] := by
  rw [header_unit]; cases pointer <;> cbv
private theorem noMeasures (pointer : Bool) (f : Fin (header pointer).unit.fns.length) :
    (fnAt (header pointer).unit f).decreases = none := by
  have same := only_main pointer f
  subst f
  cases pointer <;> cbv
private theorem contracts (pointer : Bool) : contractGate (header pointer).unit = true := by
  cases pointer <;> cbv

def functions (pointer : Bool) : Functions (header pointer).unit where
  values := fun f => (selectedCode (by exact only_main pointer) (code pointer) f).val
  equations := fun f => by exact (selectedCode (only_main pointer) (code pointer) f).property
  noInvariants := by exact noInvariants pointer
  noMeasures := by exact noMeasures pointer
  contracts := by exact contracts pointer

-- The array certificate is indexed by the actual Header source list, not a
-- merely similar SourceInput list. This avoids a dependent array-field cast.
def arrays : (pointer : Bool) →
    { value : PLift (∀ item ∈ uMembers (pre108 (header pointer).source.prepared.elaborierbar),
        Frontend.ArrayMeaning (header pointer).unit (header pointer).source.scopes item) //
      Frontend.checkArrays (header pointer).unit (header pointer).source.scopes
        (uMembers (pre108 (header pointer).source.prepared.elaborierbar)) = .ok value }
  | false => by
    refine ⟨?plainResult, ?plainResultEq⟩
    case plainResultEq => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?pointerResult, ?pointerResultEq⟩
    case pointerResultEq => cbv <;> exact Eq.refl _

private theorem entry_free (pointer : Bool) (f : Fin (header pointer).unit.fns.length) :
    (OldSource.clauses (header pointer).expanded (fnAt (header pointer).unit f).name).any
      OldSource.hasEntry = false := by
  have same := only_main pointer f
  subst f
  cases pointer <;> cbv

private theorem entry (pointer : Bool) :
    fnIdx (header pointer).unit.fns (Profil.entryName {}) = .ok (main pointer) := by
  cases pointer <;> cbv
private theorem initializers (pointer : Bool) :
    Frontend.checkInitializers (uMembers (pre108 (header pointer).source.prepared.elaborierbar))
      (header pointer).unit = .ok () := by
  change Frontend.checkInitializers
    (uMembers (pre108 (source pointer).prepared.elaborierbar)) (header pointer).unit = .ok ()
  rw [source_original]
  cases pointer <;> cbv

private theorem restored (pointer : Bool) :
    OldSource.restore (pre108 (header pointer).source.prepared.elaborierbar)
      (header pointer).unit (functions pointer).program = .ok (functions pointer).program :=
  restore_entry_free _ (header pointer).expanded (header pointer).requirements
    (header pointer).unit (functions pointer).program (header pointer).expansion (entry_free pointer)

private theorem accepted (pointer : Bool) :
    OldSource.accepts (header pointer).unit (functions pointer).program = .ok true := by
  apply accepts_function_results (functions pointer)
  intro invariants pointers foreigns
  cases pointer <;> cbv

def body (pointer : Bool) : Body (header pointer) where
  functions := functions pointer
  main := main pointer
  entry := by exact entry pointer
  initializers := by exact initializers pointer
  arrays := (arrays pointer).val
  arrayEq := by exact (arrays pointer).property
  program := (functions pointer).program
  restored := by exact restored pointer
  accepted := by exact accepted pointer

def compilation (pointer : Bool) :
    { result : Compiled (sourceText pointer) // compile (sourceText pointer) = .ok result } :=
  compiledResult (header pointer) (body pointer)

-- Keep the complete compiler proof opaque. Only the certified field of its
-- actual constructor is projected; none of its success proof is replayed.
theorem compilation_source (pointer : Bool) :
    (compilation pointer).val.source = (source pointer) :=
  compiledResult_source (header pointer) (body pointer)
theorem compilation_unit (pointer : Bool) :
    (compilation pointer).val.unit = unit pointer :=
  (compiledResult_unit (header pointer) (body pointer)).trans (header_unit pointer)
theorem compilation_main (pointer : Bool) :
    (compilation pointer).val.main = main pointer :=
  compiledResult_main (header pointer) (body pointer)
-- Project the dependent unit/main pair together before normalizing either
-- concrete carrier. Rewriting unit alone underneath main would be ill typed.
theorem compilation_parameters (pointer : Bool) :
    (declOf (compilation pointer).val.unit).params (compilation pointer).val.main =
      (declOf (header pointer).unit).params (main pointer) := rfl
theorem compilation_program (pointer : Bool) :
    (compilation pointer).val.program = (functions pointer).program :=
  compiledResult_program (header pointer) (body pointer)

end Gabbro.Stage0.NamedSpaceWitness.Phases
