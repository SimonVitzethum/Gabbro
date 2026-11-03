module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Boden
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Consumer
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Erhaltung
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.History
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Treue

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The source is the complete check/floor/gate fixture. Driver policy is
    explicit configuration: execute `p`, and consume its report through `g`. -/
def retiringSelection : CheckConsumerSelection := ⟨"p", "g"⟩

theorem retiringSource_selected :
    ((elabText checkTextBodenWahr).bind fun u =>
      uSelectCheckConsumers u [retiringSelection]).toOption.isSome = true := by
  decide +kernel

def retiringU : UProg :=
  ((elabText checkTextBodenWahr).bind fun u =>
    uSelectCheckConsumers u [retiringSelection]).toOption.get retiringSource_selected

theorem retiringU_lowered : (lowerAllg retiringU).toOption.isSome = true := by
  decide +kernel

def retiringP : Programm (declOf retiringU) :=
  ((lowerAllg retiringU).toOption.get retiringU_lowered).1

theorem retiringU_checks : (uCheckDecls retiringU).toOption.isSome = true := by
  decide +kernel

def retiringChecks : List (CheckDecl (declOf retiringU)) :=
  (uCheckDecls retiringU).toOption.get retiringU_checks

def retiringCheck : CheckDecl (declOf retiringU) :=
  retiringChecks.get ⟨0, by decide +kernel⟩

def retiringProbe : (declOf retiringU).Fn := ⟨1, by decide +kernel⟩
def retiringReporter : (declOf retiringU).Fn := ⟨2, by decide +kernel⟩
def retiringWrapper : (declOf retiringU).Fn := ⟨3, by decide +kernel⟩
def retiringConsumer : (declOf retiringU).Fn := ⟨4, by decide +kernel⟩
def retiringDriver : (declOf retiringU).Fn := ⟨5, by decide +kernel⟩

/-- Source text, ordinary lowering and the full acceptance Bool, with the
    real declared check and selected physical consumer present. -/
theorem retiringU_accepted :
    AkzeptiertX retiringP (Cover.Differenz.sperrFamilie retiringU)
      (List.finRange retiringU.fns.length) [] [] [] [] retiringChecks = true := by
  decide +kernel

/-- The complete entry returns no physical Duty. -/
theorem retiringDriver_empty_end :
    (vertragVon (declOf retiringU) retiringDriver).ende = [] := rfl

/-- The consumer's physical resource effect agrees with its ghost discharge. -/
theorem retiringConsumer_conservation :
    nach (declOf retiringU) retiringConsumer [Res.vonMarke (declOf retiringU) retiringCheck.duty] =
      [] := by
  decide +kernel

/-- The producer and selected consumer jointly leave no residual token. -/
theorem retiringCycle_conservation :
    nach (declOf retiringU) retiringConsumer
      (nach (declOf retiringU) retiringProbe
        [Res.vonMarke (declOf retiringU) retiringCheck.duty]) = [] := by
  decide +kernel

/-- An executable program with the consumer call omitted cannot return with
    its Duty outstanding. This is the real lowering gate, not a report-shape test. -/
def retiringUnconsumed : UProg :=
  { retiringU with fns := retiringU.fns.map fun f =>
    if strEq f.name "p#driver#g" then
      { f with body := [.bindCall "verdict" "p#probe" []] }
    else f }

theorem retiringUnconsumed_refused :
    (lowerAllg retiringUnconsumed).toOption.isNone = true := by
  decide +kernel

/-- The second consumer call has no mark available; a copy of the ghost
    report cannot supply the missing physical resource. -/
def retiringDouble : UProg :=
  { retiringU with fns := retiringU.fns.map fun f =>
    if strEq f.name "p#driver#g" then
      { f with body := f.body ++ [.call "p#consume#g" []] }
    else f }

theorem retiringDouble_refused :
    (lowerAllg retiringDouble).toOption.isNone = true := by
  decide +kernel

/-- Actual reporter parameters: measured x=3, floor=true, written verdict=true. -/
def retiringReporterEnv : Env (declOf retiringU) ((declOf retiringU).params retiringReporter) :=
  .cons ⟨3, by decide +kernel, by decide +kernel⟩ (.cons true (.cons true .nil))

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
    .eintritt ⟨0, by decide +kernel⟩ .nil world,
    .rueck ⟨0, by decide +kernel⟩ .nil () world world,
    .rueck retiringWrapper .nil () world world,
    .rueck retiringConsumer .nil () world world]

/-- The ghost entry retains the actual sample/floor report, consumed once. -/
theorem retiringHistory_samples (world : World (declOf retiringU)) :
    (checkGhostHistory retiringU retiringCheck retiringConsumer retiringWrapper
      (retiringEvents world).reverse).history =
      [replayEintrag retiringCheck retiringReport retiringWrapper] := rfl

theorem retiringHistory_complete (world : World (declOf retiringU)) :
    checkGhostComplete (checkGhostHistory retiringU retiringCheck retiringConsumer
      retiringWrapper (retiringEvents world).reverse) = true := rfl

/-- The real recorded samples, once consumed, satisfy the unchanged goal leg
    by the generic conservation theorem, not a per-report shape argument. -/
theorem retiringHistory_treu (world : World (declOf retiringU)) :
    Zielsatz.CheckTreueG retiringP [retiringCheck]
      (checkGhostHistory retiringU retiringCheck retiringConsumer retiringWrapper
        (retiringEvents world).reverse).history :=
  checkGhostHistory_treu retiringU retiringP retiringCheck retiringConsumer retiringWrapper
    (by decide +kernel) (retiringEvents world).reverse (retiringHistory_complete world)

/-- A repeated consumption is also refused by ghost replay. -/
theorem retiringHistory_double_refused (world : World (declOf retiringU)) :
    checkGhostComplete (checkGhostHistory retiringU retiringCheck retiringConsumer retiringWrapper
      ((retiringEvents world ++ [.eintritt retiringConsumer .nil world,
        .rueck retiringConsumer .nil () world world]).reverse)) = false := rfl

/-- The sample cannot be replaced by a neighboring claimed value. -/
theorem retiringHistory_fabrication_refused :
    actualCheckReturn retiringU retiringReporter retiringReporterEnv true ≠
      some ("p", { retiringReport with proben := [⟨"x", 0, 4, true⟩] }) := by
  decide +kernel

end Gabbro.Grammatik.Parser.Uebersetze
