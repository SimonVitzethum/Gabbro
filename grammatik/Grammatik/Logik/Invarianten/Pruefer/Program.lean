module

public import Grammatik.Logik.Invarianten.Pruefer.Writer

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer

open Frag Elim VC

variable {D : Deklaration}

/-- The program part of acceptance. The initial memory is checked separately
    because the existing program-checker interface has no initial-memory input. -/
structure CheckedProgram (program : Programm D) (S : SperrInv D) (functions : List D.Fn) where
  invariants : InvariantFormula program D.invs
  writers : ∀ f ∈ functions, InvariantDuties program S f

def checkProgram (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S) (budget : VCBudget := {}) (locks : List D.Lock := []) :
    Except Refusal (CheckedProgram program S functions) := do
  let _ ← collect locks
    (fun lock => (sources lock).isSome = true → Nonempty (LockFormula S lock))
    (fun lock => match source : sources lock with
      | none => .ok ⟨fun impossible => by simp [source] at impossible⟩
      | some _ => do
          let formula ← lockFormula S sources lock
          return ⟨fun _ => ⟨formula⟩⟩)
  let invariants ← invariantFormula program D.invs
  let writers ← collect functions (InvariantDuties program S)
    (fun f => checkWriter program S sources budget f (locks.any fun lock => (sources lock).isSome))
  return {
      invariants := invariants, writers := writers.down }

/-- A program is admitted only after translation and every writer decision
    succeed. Outside-fragment invariants are refused, never user logic and
    never an unknown result. Semantic lock predicates without optional source
    evidence remain user duty; they are not counted as checked invariants. -/
def programInvariantsB (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S) (budget : VCBudget := {}) (locks : List D.Lock := []) : Bool :=
  (checkProgram program S functions sources budget locks).toOption.isSome

/-- Exact certificate-producing acceptance, not semantic completeness for
    unsupported source syntax or for the conservative call-havoc abstraction. -/
def ProgramInvariantsChecked (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S) (budget : VCBudget := {}) (locks : List D.Lock := []) : Prop :=
  ∃ checked, checkProgram program S functions sources budget locks = .ok checked

theorem programInvariantsB_iff (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S) (budget : VCBudget) (locks : List D.Lock := []) :
    programInvariantsB program S functions sources budget locks = true ↔
      ProgramInvariantsChecked program S functions sources budget locks := by
  unfold programInvariantsB ProgramInvariantsChecked
  cases result : checkProgram program S functions sources budget locks with
  | error cause => simp
  | ok checked => simp

theorem programInvariantsB_sound (program : Programm D) (S : SperrInv D)
    (functions : List D.Fn) (sources : LockSources S) (budget : VCBudget)
    (complete : ∀ f, f ∈ functions) {locks : List D.Lock}
    (accepted : programInvariantsB program S functions sources budget locks = true) :
    ∀ f, InvariantDuties program S f := by
  obtain ⟨checked, result⟩ := (programInvariantsB_iff program S functions sources budget locks).mp accepted
  exact fun f => checked.writers f (complete f)

/-- Only the source predicates, contracts and the selected body matter for
    invariant duties. Unrelated bodies and handler-entry flags are irrelevant. -/
theorem invariantDuties_congr {left right : Programm D} {S S' : SperrInv D} (f : D.Fn)
    (invariants : left.invariante = right.invariante)
    (requires : left.requires = right.requires) (ensures : left.ensures = right.ensures)
    (body : left.rumpf f = right.rumpf f) (locks : S = S')
    (checked : InvariantDuties left S f) : InvariantDuties right S' f := by
  subst S'
  intro passes Q shared subset
  have facts := checked passes (axWahr D) shared subset
  unfold InvGutSA InvGutGrundA RespektiertRahmen RespektiertVertraege
    ReqAmEintritt EnsAmRueck InvAmRueck InvHaelt at facts ⊢
  rw [← invariants, ← requires, ← ensures, ← body]
  constructor <;> intro O frame local contract U havoc A atomic R respects noPre
  · exact facts.1 O frame local (axVertragOP_of_O _ (axVertragO_wahr O))
      U havoc A atomic R respects noPre
  · exact facts.2 O frame local (axVertragOP_of_O _ (axVertragO_wahr O))
      U havoc A atomic R respects noPre

end Gabbro.Grammatik.Invarianten.Pruefer
