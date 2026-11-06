module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.ZeugenPhases
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Consumer
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Erhaltung
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.History
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Treue

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

-- Pin the finite axiom dictionary independently of the actual source packet.
local instance retiringWitnessAxiomEquality (u : UProg) : DecidableEq (declOf u).Ax :=
  inferInstanceAs (DecidableEq (Fin u.axs.length))

/-- Source text, ordinary lowering and the full acceptance Bool, with the
    real declared check and selected physical consumer present. -/
theorem retiringU_accepted :
    AkzeptiertX retiringP (Cover.Differenz.sperrFamilie retiringU)
      (List.finRange retiringU.fns.length) [] [] [] [] retiringChecks = true := by
  cbv

/-- The complete entry returns no physical Duty. -/
theorem retiringDriver_empty_end :
    (vertragVon (declOf retiringU) retiringDriver).ende = [] := rfl

/-- The consumer's physical resource effect agrees with its ghost discharge. -/
theorem retiringConsumer_conservation :
    nach (declOf retiringU) retiringConsumer [Res.vonMarke (declOf retiringU) retiringCheck.duty] =
      [] := by
  exact duty_consumer_conservation (declOf retiringU) retiringCheck
    ((declOf retiringU).signatur retiringConsumer) rfl rfl

/-- The producer and selected consumer jointly leave no residual token. -/
theorem retiringCycle_conservation :
    nach (declOf retiringU) retiringConsumer
      (nach (declOf retiringU) retiringProbe
        [Res.vonMarke (declOf retiringU) retiringCheck.duty]) = [] := by
  exact duty_cycle_conservation (declOf retiringU) retiringCheck
    ((declOf retiringU).signatur retiringProbe) ((declOf retiringU).signatur retiringConsumer)
    rfl rfl rfl rfl

-- A failed actual function cannot occur in a successful canonical program.
-- This uses the assembler's complete function-field theorem, not a second gate.
private theorem retiring_function_refused (u : UProg) (f : Fin u.fns.length)
    (error : String) (rejected : lowerFnAt u f = .error error) :
    (lowerAllg u).toOption.isNone = true := by
  cases made : lowerAllg u with
  | error error => rfl
  | ok result =>
    obtain ⟨fields, produced, _, _, _⟩ := lowerAllg_fields u result.1 result.2 made f
    rw [rejected] at produced
    cases produced

-- The same selected scalar/body equations apply to the two modified drivers.
-- Every actual mark, owner and return-permission check remains in the producer.
attribute [local cbv_opaque] lowCallArgOneL lowCallArgsAuxL withErg lowErg lowEnd
attribute [local cbv_eval] check_argument_bool check_argument_integer
  check_arguments_nil check_arguments_cons
  check_result_select check_return_empty check_return_bool check_end_empty check_end_bool
  floor_name_self floor_mark_self

/-- An executable program with the consumer call omitted cannot return with
    its Duty outstanding. This is the real lowering gate, not a report-shape test. -/
def retiringUnconsumed : UProg :=
  { retiringU with fns := retiringU.fns.map fun f =>
    if strEq f.name "p#driver#g" then
      { f with body := [.bindCall "verdict" "p#probe" []] }
    else f }

theorem retiringUnconsumed_refused :
    (lowerAllg retiringUnconsumed).toOption.isNone = true := by
  have failed : ∃ error : String,
      lowerFnAt retiringUnconsumed ⟨5, by change 5 < 6; decide⟩ = .error error := by
    refine ⟨?error, ?rejected⟩
    case rejected => cbv <;> exact Eq.refl _
  obtain ⟨error, rejected⟩ := failed
  exact retiring_function_refused retiringUnconsumed _ error rejected

/-- The second consumer call has no mark available; a copy of the ghost
    report cannot supply the missing physical resource. -/
def retiringDouble : UProg :=
  { retiringU with fns := retiringU.fns.map fun f =>
    if strEq f.name "p#driver#g" then
      { f with body := f.body ++ [.call "p#consume#g" []] }
    else f }

theorem retiringDouble_refused :
    (lowerAllg retiringDouble).toOption.isNone = true := by
  have failed : ∃ error : String,
      lowerFnAt retiringDouble ⟨5, by change 5 < 6; decide⟩ = .error error := by
    refine ⟨?error, ?rejected⟩
    case rejected => cbv <;> exact Eq.refl _
  obtain ⟨error, rejected⟩ := failed
  exact retiring_function_refused retiringDouble _ error rejected

/-- Actual reporter parameters: measured x=3, floor=true, written verdict=true. -/
def retiringReporterEnv : Env (declOf retiringU) ((declOf retiringU).params retiringReporter) :=
  .cons ⟨3, by decide, by decide⟩ (.cons true (.cons true .nil))

def retiringReport : CheckReport :=
  { proben := [⟨"x", 0, 3, true⟩], boeden := [true], urteil := true }

/-- The generic decoder reads the measured value and floor directly from
    the actual saved parameter environment. -/
theorem retiringActual_samples :
    actualCheckReturn retiringU retiringReporter retiringReporterEnv true =
      some ("p", retiringReport) := rfl

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
    .eintritt ⟨0, by decide⟩ .nil world,
    .rueck ⟨0, by decide⟩ .nil () world world,
    .rueck retiringWrapper .nil () world world,
    .rueck retiringConsumer .nil () world world]

section retiringReplay
attribute [local cbv_opaque] actualCheckReturn
attribute [local cbv_eval] retiringActual_samples

-- The saved-argument decoder above supplies the report. Infer the actual
-- state from the eleven real events before inspecting history/completeness.
private def retiringReplay (world : World (declOf retiringU)) :
    {state : CheckGhostState (declOf retiringU) //
      checkGhostHistory retiringU retiringCheck retiringConsumer retiringWrapper
        (retiringEvents world).reverse = state} := by
  refine ⟨?state, ?replayed⟩
  case replayed => cbv <;> exact Eq.refl _

end retiringReplay

/-- The ghost entry retains the actual sample/floor report, consumed once. -/
theorem retiringHistory_samples (world : World (declOf retiringU)) :
    (checkGhostHistory retiringU retiringCheck retiringConsumer retiringWrapper
      (retiringEvents world).reverse).history =
      [replayEintrag retiringCheck retiringReport retiringWrapper] := by
  rw [(retiringReplay world).property]
  rfl

theorem retiringHistory_complete (world : World (declOf retiringU)) :
    checkGhostComplete (checkGhostHistory retiringU retiringCheck retiringConsumer
      retiringWrapper (retiringEvents world).reverse) = true := by
  rw [(retiringReplay world).property]
  rfl

/-- The real recorded samples, once consumed, satisfy the unchanged goal leg
    by the generic conservation theorem, not a per-report shape argument. -/
theorem retiringHistory_treu (world : World (declOf retiringU)) :
    Zielsatz.CheckTreueG retiringP [retiringCheck]
      (checkGhostHistory retiringU retiringCheck retiringConsumer retiringWrapper
        (retiringEvents world).reverse).history :=
  checkGhostHistory_treu retiringU retiringP retiringCheck retiringConsumer retiringWrapper
    (by cbv) (retiringEvents world).reverse (retiringHistory_complete world)

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
    (retiringReplay world).property]
  cbv

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
