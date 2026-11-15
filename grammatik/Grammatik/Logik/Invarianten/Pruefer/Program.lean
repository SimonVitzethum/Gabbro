module

public import Grammatik.Logik.Invarianten.Pruefer.Writer
public import Grammatik.Logik.Vertraege.Pruefer.Program

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
    Except Frag.Refusal (CheckedProgram program S functions) := do
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
  | error cause => simp [Except.toOption]
  | ok checked => simp [Except.toOption]

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
  constructor <;> intro O frame locality contract U havoc A atomic R respects noPre
  · exact facts.1 O frame locality (axVertragOP_of_O _ (axVertragO_wahr O))
      U havoc A atomic R respects noPre
  · exact facts.2 O frame locality (axVertragOP_of_O _ (axVertragO_wahr O))
      U havoc A atomic R respects noPre

/-- Check declaration syntax and generate the actual bodies' verification
    conditions. The strict contract WP also checks every lock release and
    scoped return; a failing release cannot hide in a permissive error post.
    Requires and ensures are checked by the same traversal, without assuming
    an invariant at entry that the existing semantic duties do not assume. -/
def checkInvariantVC (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S) (budget : VCBudget := {})
    (hints : Vertraege.Pruefer.LoopHints D := fun _ => none) (locks : List D.Lock := []) :
    Except Frag.Refusal (PLift (∀ f ∈ functions, Vertraege.Pruefer.ContractDuties program S f)) := do
  let _ ← checkProgram program S functions sources budget locks
  Vertraege.Pruefer.checkContracts program S functions sources budget hints

/-- Both algorithms remain checks: declaration/writer VCs and the strict
    contract/release VCs. The conjunction is shared by SC and atomic checkers. -/
def invariantVCB (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S := fun _ => none) (budget : VCBudget := {})
    (hints : Vertraege.Pruefer.LoopHints D := fun _ => none) (locks : List D.Lock := []) : Bool :=
  programInvariantsB program S functions sources budget locks &&
    Vertraege.Pruefer.KontrakteGeprueftB program S functions sources budget hints

/-- Factoring the concrete checker does not remove either pre-existing gate. -/
theorem invariantVCB_eq (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S) (budget : VCBudget)
    (hints : Vertraege.Pruefer.LoopHints D) (locks : List D.Lock) :
    invariantVCB program S functions sources budget hints locks =
      (programInvariantsB program S functions sources budget locks &&
        Vertraege.Pruefer.KontrakteGeprueftB program S functions sources budget hints) := rfl

/-- The shared Bool succeeds exactly when its two traversals construct the
    semantic certificate; no semantic proof is submitted to either traversal. -/
theorem invariantVCB_certificate (program : Programm D) (S : SperrInv D)
    (functions : List D.Fn) (sources : LockSources S) (budget : VCBudget)
    (hints : Vertraege.Pruefer.LoopHints D) (locks : List D.Lock) :
    invariantVCB program S functions sources budget hints locks = true ↔
      ∃ certificate, checkInvariantVC program S functions sources budget hints locks = .ok certificate := by
  cases generated : checkProgram program S functions sources budget locks <;>
    cases contracted : Vertraege.Pruefer.checkContracts program S functions sources budget hints <;>
    simp [invariantVCB, checkInvariantVC, programInvariantsB,
      Vertraege.Pruefer.KontrakteGeprueftB, generated, contracted, Except.toOption, Except.bind]

theorem invariantVCB_sound {program : Programm D} {S : SperrInv D}
    {functions : List D.Fn} {sources : LockSources S} {budget : VCBudget} {hints : Vertraege.Pruefer.LoopHints D} {locks : List D.Lock}
    (complete : ∀ f, f ∈ functions)
    (accepted : invariantVCB program S functions sources budget hints locks = true) :
    ∀ f, Vertraege.Pruefer.ContractDuties program S f :=
  Vertraege.Pruefer.KontrakteGeprueftB_sound complete (Bool.and_eq_true_iff.mp accepted).2

/-- The public invariant consequence is uniform in runtime budget, named
    oracle contracts and every shared-atomic rely admitted by the model. -/
theorem invariantVCB_invGutA {program : Programm D} {S : SperrInv D}
    {functions : List D.Fn} {sources : LockSources S} {budget : VCBudget} {hints : Vertraege.Pruefer.LoopHints D} {locks : List D.Lock}
    (complete : ∀ f, f ∈ functions)
    (accepted : invariantVCB program S functions sources budget hints locks = true)
    (passes : Nat) (Q : AxEns D) (shared : D.Tab ⊕ D.Glob → Prop)
    (subset : ∀ carrier, shared carrier → AtomarAusgenommen carrier) (f : D.Fn) :
    InvGutSA program passes Q S shared f ∧ InvGutGrundA program passes Q S shared f :=
  (invariantVCB_sound complete accepted f passes Q shared subset).2

end Gabbro.Grammatik.Invarianten.Pruefer
