module
public import Stage0.SourceWitness.Compiled
public import Stage0.SourceWitness.ImagePhases
import all Stage0.SourceWitness.Compiled
import all Stage0.SourceWitness.Input
import all Stage0.SourceWitness.Owners
import all Stage0.IRBild
import all Stage0.Bindung
import all Stage0.Senke.Images.Bild
import all Stage0.Senke.Images.SourceStarts
import all Stage0.Senke.Welt.MainEnv
import all Stage0.Senke.Welt.AnordnungLayouta

@[expose] public section
namespace Gabbro.Stage0.SourceWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
set_option maxRecDepth 2000
set_option maxHeartbeats 100000

private theorem source_target : validateTargetFor ({} : Profil.Options).arch
    ({} : Profil.Options).target (uMembers (pre108 sourceCompiled.val.source.items)) = .ok () := by cbv

private theorem source_gates : toreVonFor ({} : Profil.Options).arch
    ({} : Profil.Options).target (uMembers (pre108 sourceCompiled.val.source.items)) = .ok [] := by cbv

private def sourceTor : (declOf sourceCompiled.val.unit).Ax → Option Senke.TorB :=
  fun _ => none

private def sourcePlan : {plan : StartArgument.Plan sourceCompiled.val.unit
      (uMembers (pre108 sourceCompiled.val.source.prepared.elaborierbar)) sourceCompiled.val.main //
    StartArgument.plan sourceCompiled.val.unit
      (uMembers (pre108 sourceCompiled.val.source.prepared.elaborierbar)) sourceCompiled.val.main = .ok plan} := by
  refine ⟨?plan, ?made⟩
  case made => cbv <;> exact Eq.refl _

-- This field-index proof never enumerates the table's 2^32 cells.
private theorem source_initial : GabbroV.sp0OkB sourceCompiled.val.unit = true := by
  unfold GabbroV.sp0OkB GabbroV.sp0TabOkB
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro table _
    rw [compiled_fieldless table]
    rfl
  · rw [compiled_carriers.2.1]
    rfl

private def sourceArgs : {args : Env (declOf sourceCompiled.val.unit)
      ((declOf sourceCompiled.val.unit).params sourceCompiled.val.main) //
    Senke.mainEnv ((declOf sourceCompiled.val.unit).params sourceCompiled.val.main) = some args} := by
  refine ⟨?args, ?made⟩
  case made => cbv <;> exact Eq.refl _

private def sourceEmission : {image : Senke.Bild (declOf sourceCompiled.val.unit) //
    Senke.bild irDurchlaeufe sourceCompiled.val.program (Senke.layU sourceCompiled.val.unit sourceTor)
      (List.finRange sourceCompiled.val.unit.fns.length) Fin.val
      (fun g => (sourceCompiled.val.unit.fns[g.val]?.map (·.name)).getD "?")
      sourceCompiled.val.main sourceArgs.val
      (sourcePlan.val.starts (Senke.initialWorld sourceCompiled.val.unit source_initial))
      64 (Senke.bodenAusrichtung sourceCompiled.val.unit) = .ok image} := by
  refine ⟨?image, ?made⟩
  case made => cbv <;> exact Eq.refl _

-- All data are the same complete constructors returned by the production
-- phases. The equality below connects this packet to the one actual emit.
private def sourceImage : {image : Emitted text 64 // emit text 64 = .ok image} := by
  refine ⟨{
    compiled := sourceCompiled.val
    tor := sourceTor
    startPlan := sourcePlan.val
    initialValid := source_initial
    args := sourceArgs.val
    pointers := sourceArgs.property
    image := sourceEmission.val
    emission := sourceEmission.property }, ?_⟩
  have noForeign : sourceCompiled.val.unit.axs = [] := by cbv
  exact ImagePhases.emit_eq _ sourceCompiled.property source_target [] source_gates
    noForeign rfl sourcePlan.property

end Gabbro.Stage0.SourceWitness
