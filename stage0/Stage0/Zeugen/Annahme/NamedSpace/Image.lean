module
public import Stage0.Zeugen.Annahme.NamedSpace.Program
public import Stage0.SourceWitness.ImagePhases
import all Stage0.Zeugen.Annahme.NamedSpace.Program
import all Stage0.Senke.Images.Bild
import all Stage0.Senke.Images.SourceStarts
import all Stage0.Senke.Welt.MainEnv

@[expose] public section
namespace Gabbro.Stage0.NamedSpaceWitness.Phases
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Frontend.ConstPhases
set_option maxRecDepth 2000
set_option maxHeartbeats 400000

attribute [local cbv_opaque] Frontend.normalize uFloatLimit
attribute [local cbv_eval] compiledResult_source compiledResult_unit
  compiledResult_main compiledResult_program header_unit
  compilation_source compilation_unit compilation_main compilation_program

private theorem target (pointer : Bool) :
    validateTargetFor ({} : Profil.Options).arch ({} : Profil.Options).target
      (uMembers (pre108 (compilation pointer).val.source.items)) = .ok () := by
  rw [compilation_source]
  cases pointer <;> cbv
private theorem bindings (pointer : Bool) :
    toreVonFor ({} : Profil.Options).arch ({} : Profil.Options).target
      (uMembers (pre108 (compilation pointer).val.source.items)) = .ok [] := by
  rw [compilation_source]
  cases pointer <;> cbv
private theorem foreigns (pointer : Bool) : (compilation pointer).val.unit.axs = [] := by
  rw [compilation_unit]
  cases pointer <;> cbv

def tor (pointer : Bool) : (declOf (compilation pointer).val.unit).Ax → Option Senke.TorB :=
  fun _ => none

def plan : (pointer : Bool) →
    { value : StartArgument.Plan (compilation pointer).val.unit
        (uMembers (pre108 (compilation pointer).val.source.prepared.elaborierbar))
        (compilation pointer).val.main //
      StartArgument.plan (compilation pointer).val.unit
        (uMembers (pre108 (compilation pointer).val.source.prepared.elaborierbar))
        (compilation pointer).val.main = .ok value }
  | false => by
    refine ⟨?plainResult, ?plainResultEq⟩
    case plainResultEq => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?pointerResult, ?pointerResultEq⟩
    case pointerResultEq => cbv <;> exact Eq.refl _

theorem initial (pointer : Bool) : GabbroV.sp0OkB (compilation pointer).val.unit = true := by
  rw [compilation_unit]
  cases pointer <;> cbv

def arguments : (pointer : Bool) →
    { value : Env (declOf (compilation pointer).val.unit)
        ((declOf (compilation pointer).val.unit).params (compilation pointer).val.main) //
      Senke.mainEnv ((declOf (compilation pointer).val.unit).params (compilation pointer).val.main) =
        some value }
  | false => by
    refine ⟨?plainResult, ?plainResultEq⟩
    case plainResultEq => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?pointerResult, ?pointerResultEq⟩
    case pointerResultEq => cbv <;> exact Eq.refl _

-- Only the actual finite builder runs here: source parsing, collection,
-- lowering, restoration and admission have already supplied whole values.
def emission : (pointer : Bool) →
    { value : Senke.Bild (declOf (compilation pointer).val.unit) //
      Senke.bild irDurchlaeufe (compilation pointer).val.program
        (Senke.layU (compilation pointer).val.unit (tor pointer))
        (List.finRange (compilation pointer).val.unit.fns.length) Fin.val
        (fun g => ((compilation pointer).val.unit.fns[g.val]?.map (·.name)).getD "?")
        (compilation pointer).val.main (arguments pointer).val
        ((plan pointer).val.starts (Senke.initialWorld (compilation pointer).val.unit (initial pointer)))
        64 (Senke.bodenAusrichtung (compilation pointer).val.unit) = .ok value }
  | false => by
    refine ⟨?plainResult, ?plainResultEq⟩
    case plainResultEq => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?pointerResult, ?pointerResultEq⟩
    case pointerResultEq => cbv <;> exact Eq.refl _

-- A thin data constructor is independent of its closed success theorem.
-- It is exactly the constructor certified by the shared original-emitter API.
def image (pointer : Bool) : Emitted (sourceText pointer) 64 where
  compiled := (compilation pointer).val
  tor := tor pointer
  startPlan := (plan pointer).val
  initialValid := by exact initial pointer
  args := (arguments pointer).val
  pointers := by exact (arguments pointer).property
  image := (emission pointer).val
  emission := by exact (emission pointer).property

theorem image_produced (pointer : Bool) : emit (sourceText pointer) 64 = .ok (image pointer) :=
  ImagePhases.emit_from_phases (compilation pointer).val (compilation pointer).property
    (target pointer) [] (bindings pointer) (foreigns pointer) (tor pointer) rfl
    (plan pointer).val (plan pointer).property (initial pointer)
    (arguments pointer).val (arguments pointer).property
    (emission pointer).val (emission pointer).property

theorem image_unit (pointer : Bool) : (image pointer).compiled.unit = unit pointer :=
  compilation_unit pointer

end Gabbro.Stage0.NamedSpaceWitness.Phases
