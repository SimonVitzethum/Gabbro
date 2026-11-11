/- C16 inventory item 16 (Stage-0 half): connected export correctness.

    Check-carrying units travel the same certified pipeline as all units:
    `emitted_check_correct` is the generic `Emitted.correct` certificate,
    unchanged. The vacuous `[]` leg is gone: `stage0_anspruch_erfuellt` pins
    that the end-to-end unit's derived `CheckDecl`s resolve to lowered
    function indices (their probes and gate wrappers, which `lowerAllg`
    covers as ordinary members of `u.fns`) and are admitted by `checkB`
    (`Zulassung.checkU_akzeptiert` accepts them in `AkzeptiertX`). -/
module
public import Stage0.IRBild
import Grammatik.Kern.Taktik.KernelRfl
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
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Ableitung
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Zulassung
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Boden
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Gegenprobe
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Fremdtor
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Treue
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert
@[expose] public section

namespace Gabbro.Stage0
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Parser.ExportPreservation Gabbro.Grammatik.Zielsatz

/-- What the Stage-0 gate needs for one elaborated check: resolution to
    lowered function indices -- its probe and gate wrappers, which `lowerAllg`
    covers as ordinary members of `u.fns` -- with the probe name retained.
    Met by `stage0_anspruch_erfuellt` at the `CheckDecl` level. -/
def CheckStage0Anspruch (u : UProg) (c : UCheck) : Prop :=
  ∃ p : Fin u.fns.length, ∃ gs : List (Fin u.fns.length),
    uCheckIdx u c = .ok (p, gs) ∧ (fnAt u p).name = c.probe

/-- The claim is met on the end-to-end unit: the derived `CheckDecl`s resolve
    to the probe and its gate wrapper, and `checkB` admits them. -/
theorem stage0_anspruch_erfuellt :
    (uCheckDecls checkU).map (fun cs => cs.map fun d =>
      ((fnAt checkU d.probe).name,
        d.gates.map fun g => (fnAt checkU g).name)) =
      .ok [("p#probe", ["p#tor#g"])] ∧
    checkB checkP [] [] (List.finRange checkU.fns.length) checkChecks = true :=
  ⟨by kernel_rfl, checkU_checkB⟩

/-- Both floor verdicts, the executable bound counterprobe, and both foreign
    gate forms use the same source/elaboration/lowering/admission path. No
    separate emitter or interpreter implements these forms. -/
theorem stage0_c16_formen_akzeptiert :
    AkzeptiertX checkPBodenWahr (Cover.Differenz.sperrFamilie uBodenWahr)
      (List.finRange uBodenWahr.fns.length) [] [] [] [] checkChecksBodenWahr = true ∧
    AkzeptiertX checkPBodenFalsch (Cover.Differenz.sperrFamilie uBodenFalsch)
      (List.finRange uBodenFalsch.fns.length) [] [] [] [] checkChecksBodenFalsch = true ∧
    AkzeptiertX checkPSonde (Cover.Differenz.sperrFamilie uSonde)
      (List.finRange uSonde.fns.length) [] [] [] [] checkChecksSonde = true ∧
    AkzeptiertX checkPFremd (Cover.Differenz.sperrFamilie uFremd)
      (List.finRange uFremd.fns.length) [] [] [] [] checkChecksFremd = true ∧
    AkzeptiertX checkPFremdFallible (Cover.Differenz.sperrFamilie uFremdFallible)
      (List.finRange uFremdFallible.fns.length) [] [] [] [] checkChecksFremdFallible = true :=
  ⟨bodenWahr_akzeptiert, bodenFalsch_akzeptiert, sonde_akzeptiert,
    fremd_akzeptiert, fremdFallible_akzeptiert⟩

/-- Measured counterprobe evidence additionally passes the executable binding
    and exact-image gate; structural admission alone claims no external run. -/
theorem stage0_c16_sondenachweis : checkChecksSonde.all (fun d =>
    sondenNachweisB checkChecksSonde d "ship" artefaktSonde
      .durchgefallen berichtSondeFalsch) = true := sonde_nachweisB

/-- Every emitted image -- including check-carrying units -- carries the
    inherited IR execution certificate for its exact source program. -/
theorem emitted_check_correct [Runner.IR.Kern] [Senke.CloneOK]
    {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) : output.Correct :=
  output.correct

/-- The exact emitted source program's ordinary IR simulation and its
    completed actual-sample history share one declaration and program. Ghost
    completion records retirement, not truth of the check's prose claim. -/
theorem emitted_check_history_correct [Runner.IR.Kern] [Senke.CloneOK]
    {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options)
    (machine : RufMaschineG (declOf output.compiled.unit)) (thread : Faden)
    (check : CheckDecl (declOf output.compiled.unit))
    (consumer gate : (declOf output.compiled.unit).Fn) (declared : gate ∈ check.gates)
    (complete : checkGhostComplete
      (checkGhostGX output.compiled.unit machine thread check consumer gate) = true) :
    output.Correct ∧ Zielsatz.CheckTreueG output.compiled.program [check]
      (checkGhostGX output.compiled.unit machine thread check consumer gate).history :=
  ⟨output.correct, checkGhostGX_treu output.compiled.unit output.compiled.program
    machine thread check consumer gate declared complete⟩

end Gabbro.Stage0
