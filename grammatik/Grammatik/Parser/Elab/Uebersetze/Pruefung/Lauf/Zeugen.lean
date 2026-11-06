module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.ZeugenFacts
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Consumer
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Erhaltung
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.History
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Treue

import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.ZeugenFacts
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.ZeugenPhases
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.History
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Calls
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Units
import all Grammatik.Parser.Elab.UebersetzeAllg3.TransitionCert
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil1
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3Values
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil4
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Ende
import all Grammatik.Parser.Elab.UebersetzeAllg3.Kopf
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
import all Grammatik.Parser.Elab.UebersetzeAllg3.Transition
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
import all Grammatik.Parser.Elab.Generic.Signatures
import all Grammatik.Parser.Elab.Generic.StaticConformance
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
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- Pin the dictionary before substituting the source-backed declaration.
local instance retiringWitnessAxiomEquality (u : UProg) : DecidableEq (declOf u).Ax :=
  inferInstanceAs (DecidableEq (Fin u.axs.length))
local instance retiringWitnessFunctionEquality (u : UProg) : DecidableEq (declOf u).Fn :=
  inferInstanceAs (DecidableEq (Fin u.fns.length))

theorem retiringSource_selected :
    ((elabText checkTextBodenWahr).bind fun u =>
      uSelectCheckConsumers u [retiringSelection]).toOption.isSome = true := by
  exact congrArg (fun produced : Except String UProg => produced.toOption.isSome)
    RetiringWitness.selected.property

-- Public runtime data retain their original canonical getter definitions.
-- Only propositions cross the private implementation boundary below.
def retiringU : UProg :=
  ((elabText checkTextBodenWahr).bind fun u =>
    uSelectCheckConsumers u [retiringSelection]).toOption.get retiringSource_selected

private theorem retiring_unit : retiringU = RetiringWitness.unit :=
  Except.ok.inj ((except_ok_get (x := (elabText checkTextBodenWahr).bind fun u =>
    uSelectCheckConsumers u [retiringSelection]) retiringSource_selected).symm.trans
      RetiringWitness.selected.property)

private theorem retiring_facts : RetiringWitness.RetiringFacts retiringU :=
  Eq.mpr (congrArg (fun u : UProg => RetiringWitness.RetiringFacts u) retiring_unit)
    RetiringWitness.facts

theorem retiringU_lowered : (lowerAllg retiringU).toOption.isSome = true :=
  retiring_facts.common.lowered

def retiringP : Programm (declOf retiringU) :=
  ((lowerAllg retiringU).toOption.get retiringU_lowered).1

theorem retiringU_checks : (uCheckDecls retiringU).toOption.isSome = true :=
  retiring_facts.common.derived

def retiringChecks : List (CheckDecl (declOf retiringU)) :=
  (uCheckDecls retiringU).toOption.get retiringU_checks

private theorem retiring_check_nonempty : 0 < retiringChecks.length := by
  have count : retiringChecks.length = 1 := retiring_facts.checkCount
  omega

private theorem retiring_index_lt (index : Nat) (bound : index < 6) :
    index < retiringU.fns.length := by
  rw [retiring_facts.functionCount]
  exact bound

def retiringCheck : CheckDecl (declOf retiringU) :=
  retiringChecks.get ⟨0, by exact retiring_check_nonempty⟩

def retiringProbe : (declOf retiringU).Fn := ⟨1, by exact retiring_index_lt 1 (by decide)⟩
def retiringReporter : (declOf retiringU).Fn := ⟨2, by exact retiring_index_lt 2 (by decide)⟩
def retiringWrapper : (declOf retiringU).Fn := ⟨3, by exact retiring_index_lt 3 (by decide)⟩
def retiringConsumer : (declOf retiringU).Fn := ⟨4, by exact retiring_index_lt 4 (by decide)⟩
def retiringDriver : (declOf retiringU).Fn := ⟨5, by exact retiring_index_lt 5 (by decide)⟩

private theorem retiring_check_member : retiringCheck ∈ retiringChecks := List.get_mem _ _

private theorem retiring_descriptor : retiringCheck.name = "p" ∧
    retiringCheck.probe.val = 1 ∧ retiringCheck.gates.map Fin.val = [3] :=
  retiring_facts.descriptor retiringCheck retiring_check_member

private theorem retiring_check_probe : retiringCheck.probe = retiringProbe :=
  Fin.ext retiring_descriptor.2.1

private theorem retiring_check_name : retiringCheck.name = "p" := retiring_descriptor.1

private theorem retiring_probe_result : (declOf retiringU).erg retiringProbe = some .bool :=
  retiring_facts.boolResult retiringProbe (Or.inl rfl)

private theorem retiring_reporter_result : (declOf retiringU).erg retiringReporter = some .bool :=
  retiring_facts.boolResult retiringReporter (Or.inr rfl)

private theorem retiring_wrapper_declared : retiringWrapper ∈ retiringCheck.gates := by
  have member : retiringWrapper.val ∈ retiringCheck.gates.map Fin.val := by
    rw [retiring_descriptor.2.2]
    exact List.mem_singleton.mpr rfl
  obtain ⟨f, member, same⟩ := List.mem_map.mp member
  exact (Fin.ext same : f = retiringWrapper) ▸ member

/-- Source text, ordinary lowering and the full acceptance Bool, with the
    real declared check and selected physical consumer present. -/
theorem retiringU_accepted :
    AkzeptiertX retiringP (Cover.Differenz.sperrFamilie retiringU)
      (List.finRange retiringU.fns.length) [] [] [] [] retiringChecks = true :=
  retiring_facts.common.accepted

/-- The complete entry returns no physical Duty. -/
theorem retiringDriver_empty_end :
    (vertragVon (declOf retiringU) retiringDriver).ende = [] :=
  retiring_facts.driverEnd retiringDriver rfl

/-- The consumer's physical resource effect agrees with its ghost discharge. -/
theorem retiringConsumer_conservation :
    nach (declOf retiringU) retiringConsumer [Res.vonMarke (declOf retiringU) retiringCheck.duty] =
      [] := by
  have flow := retiring_facts.resources retiringCheck retiring_check_member
    retiringProbe retiringConsumer rfl rfl
  exact duty_consumer_conservation (declOf retiringU) retiringCheck
    ((declOf retiringU).signatur retiringConsumer) flow.2.2.1 flow.2.2.2

/-- The producer and selected consumer jointly leave no residual token. -/
theorem retiringCycle_conservation :
    nach (declOf retiringU) retiringConsumer
      (nach (declOf retiringU) retiringProbe
        [Res.vonMarke (declOf retiringU) retiringCheck.duty]) = [] := by
  have flow := retiring_facts.resources retiringCheck retiring_check_member
    retiringProbe retiringConsumer rfl rfl
  exact duty_cycle_conservation (declOf retiringU) retiringCheck
    ((declOf retiringU).signatur retiringProbe) ((declOf retiringU).signatur retiringConsumer)
    flow.1 flow.2.1 flow.2.2.1 flow.2.2.2

/-- An executable program with the consumer call omitted cannot return with
    its Duty outstanding. This is the real lowering gate, not a report-shape test. -/
def retiringUnconsumed : UProg :=
  { retiringU with fns := retiringU.fns.map fun f =>
    if strEq f.name "p#driver#g" then
      { f with body := [.bindCall "verdict" "p#probe" []] }
    else f }

theorem retiringUnconsumed_refused :
    (lowerAllg retiringUnconsumed).toOption.isNone = true := retiring_facts.unconsumed

/-- The second consumer call has no mark available; a copy of the ghost
    report cannot supply the missing physical resource. -/
def retiringDouble : UProg :=
  { retiringU with fns := retiringU.fns.map fun f =>
    if strEq f.name "p#driver#g" then
      { f with body := f.body ++ [.call "p#consume#g" []] }
    else f }

theorem retiringDouble_refused :
    (lowerAllg retiringDouble).toOption.isNone = true := retiring_facts.double

/-- Actual reporter parameters: measured x=3, floor=true, written verdict=true. -/
def retiringReporterEnv : Env (declOf retiringU) ((declOf retiringU).params retiringReporter) :=
  .cons ⟨3, by decide, by decide⟩ (.cons true (.cons true .nil))

/-- The generic decoder reads the measured value and floor directly from
    the actual saved parameter environment. -/
theorem retiringActual_samples :
    actualCheckReturn retiringU retiringReporter retiringReporterEnv true =
      some ("p", retiringReport) := by
  exact retiring_facts.capture retiringReporter rfl retiringReporterEnv retiring_reporter_result rfl

/-- Chronological call/return events of the generated ordinary cycle. The
    root remains at its empty-resource return; G logs callee pops only. -/
def retiringEvents (world : World (declOf retiringU)) :
    List (RufEreignisF (declOf retiringU)) :=
  [.eintritt retiringDriver .nil world,
    .eintritt retiringProbe .nil world,
    .eintritt retiringReporter retiringReporterEnv world,
    .rueck retiringReporter retiringReporterEnv true world world,
    .rueck retiringProbe .nil true world world,
    .eintritt retiringConsumer .nil world,
    .eintritt retiringWrapper .nil world,
    .eintritt ⟨0, by exact retiring_index_lt 0 (by decide)⟩ .nil world,
    .rueck ⟨0, by exact retiring_index_lt 0 (by decide)⟩ .nil () world world,
    .rueck retiringWrapper .nil () world world,
    .rueck retiringConsumer .nil () world world]

private theorem retiring_probe_verdict (before after : World (declOf retiringU)) :
    rueckUrteil retiringCheck (.rueck retiringProbe .nil true before after) = some true := by
  exact retiring_facts.verdict retiringCheck retiring_check_member retiringProbe rfl
    .nil retiring_probe_result before after

section retiringReplay
-- These equations are projections of the transported source certificate.
-- Replay cannot unfold the source, lowerAllg or the descriptor getter.
attribute [local cbv_opaque] retiringU retiringChecks retiringCheck actualCheckReturn rueckUrteil
attribute [local cbv_eval] retiring_check_probe retiring_check_name
  retiringActual_samples retiring_probe_verdict

private def retiringReplay (world : World (declOf retiringU)) :
    {state : CheckGhostState (declOf retiringU) //
      checkGhostHistory retiringU retiringCheck retiringConsumer retiringWrapper
        (retiringEvents world).reverse = state} := by
  refine ⟨?state, ?replayed⟩
  case replayed => cbv <;> exact Eq.refl _

/-- The ghost entry retains the actual sample/floor report, consumed once. -/
theorem retiringHistory_samples (world : World (declOf retiringU)) :
    (checkGhostHistory retiringU retiringCheck retiringConsumer retiringWrapper
      (retiringEvents world).reverse).history =
      [replayEintrag retiringCheck retiringReport retiringWrapper] := by
  rw [(retiringReplay world).property]
  simp only [replayEintrag, retiring_check_probe] <;> rfl

theorem retiringHistory_complete (world : World (declOf retiringU)) :
    checkGhostComplete (checkGhostHistory retiringU retiringCheck retiringConsumer
      retiringWrapper (retiringEvents world).reverse) = true := by
  rw [(retiringReplay world).property] <;> rfl

/-- The real recorded samples, once consumed, satisfy the unchanged goal leg
    by the generic conservation theorem, not a per-report shape argument. -/
theorem retiringHistory_treu (world : World (declOf retiringU)) :
    Zielsatz.CheckTreueG retiringP [retiringCheck]
      (checkGhostHistory retiringU retiringCheck retiringConsumer retiringWrapper
        (retiringEvents world).reverse).history :=
  checkGhostHistory_treu retiringU retiringP retiringCheck retiringConsumer retiringWrapper
    retiring_wrapper_declared (retiringEvents world).reverse (retiringHistory_complete world)

/-- A repeated consumption is also refused by ghost replay. -/
theorem retiringHistory_double_refused (world : World (declOf retiringU)) :
    checkGhostComplete (checkGhostHistory retiringU retiringCheck retiringConsumer retiringWrapper
      ((retiringEvents world ++ [.eintritt retiringConsumer .nil world,
        .rueck retiringConsumer .nil () world world]).reverse)) = false := by
  have appended :
      (retiringEvents world ++ [.eintritt retiringConsumer .nil world,
        .rueck retiringConsumer .nil () world world]).reverse =
      .rueck retiringConsumer .nil () world world ::
        .eintritt retiringConsumer .nil world :: (retiringEvents world).reverse := by
    rw [List.reverse_append]
    rfl
  rw [appended, checkGhostHistory_event, checkGhostHistory_event,
    (retiringReplay world).property] <;> cbv

end retiringReplay

/-- The sample cannot be replaced by a neighboring claimed value. -/
theorem retiringHistory_fabrication_refused :
    actualCheckReturn retiringU retiringReporter retiringReporterEnv true ≠
      some ("p", { retiringReport with proben := [⟨"x", 0, 4, true⟩] }) := by
  rw [retiringActual_samples]
  intro fabricated
  have samples := congrArg (fun result : Option (String × CheckReport) =>
    result.map (fun item => item.2.proben.map (·.wert))) fabricated
  change some [3] = some [4] at samples
  cases samples

end Gabbro.Grammatik.Parser.Uebersetze
