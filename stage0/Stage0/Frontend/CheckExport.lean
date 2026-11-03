/- C16 inventory item 16 (Stage-0 half): connected export correctness.

    Check-carrying units travel the same certified pipeline as all units:
    `emitted_check_correct` is the generic `Emitted.correct` certificate,
    unchanged. `stage0_pruef_leer` pins what the pipeline currently checks:
    `OldSource.accepts` runs `AkzeptiertX` without checks, i.e. with
    `checks = []`, and `checkB ... [] = true`. `CheckStage0Anspruch` names
    what full closure still needs: every elaborated check resolves to
    lowered function indices (its probe and gate wrappers, which `lowerAllg`
    covers as ordinary members of `u.fns`), and the derived `CheckDecl`s are
    admitted by `checkB` -- blocked on the Marke-carrying declaration
    (`uCheckDecl_unbewohnt` in `Pruefung/Export`). -/
module
public import Stage0.IRBild
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert
@[expose] public section

namespace Gabbro.Stage0
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Parser.ExportPreservation Gabbro.Grammatik.Zielsatz

/-- What full closure needs at the Stage-0 gate: every elaborated check
    resolves to lowered function indices -- its probe and gate wrappers,
    which `lowerAllg` covers as ordinary members of `u.fns`. The matching
    `CheckDecl` admission by `checkB` is the lead's Marke-carrying
    declaration step. -/
def CheckStage0Anspruch (u : UProg) (c : UCheck) : Prop :=
  ∃ p : Fin u.fns.length, ∃ gs : List (Fin u.fns.length),
    uCheckIdx u c = .ok (p, gs) ∧ (fnAt u p).name = c.probe

/-- Today's Stage-0 acceptance of a check-carrying unit rests on the vacuous
    leg: `AkzeptiertX` runs with the default `checks = []`, and the empty
    admission holds. -/
theorem stage0_pruef_leer {D : Deklaration} [DecidableEq D.Fn] [DecidableEq D.Ax]
    (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    AkzeptiertX P S fs ls cs ws = AkzeptiertX P S fs ls cs ws [] [] ∧
      ∀ tabs globs, checkB P tabs globs fs [] = true :=
  ⟨rfl, fun _ _ => checkB_leer _ _ _ _⟩

/-- Every emitted image -- including check-carrying units -- carries the
    inherited IR execution certificate for its exact source program. -/
theorem emitted_check_correct [Runner.IR.Kern] [Senke.CloneOK]
    {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) : output.Correct :=
  output.correct

end Gabbro.Stage0
