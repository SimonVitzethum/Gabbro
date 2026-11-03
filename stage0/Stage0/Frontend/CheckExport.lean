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
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Ableitung
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Zulassung
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
  ⟨rfl, checkU_checkB⟩

/-- Every emitted image -- including check-carrying units -- carries the
    inherited IR execution certificate for its exact source program. -/
theorem emitted_check_correct [Runner.IR.Kern] [Senke.CloneOK]
    {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) : output.Correct :=
  output.correct

end Gabbro.Stage0
