module

public import Stage0.Senke.Ausdruck.Old.Pruefer
public import Stage0.ForeignSummary
public import Stage0.Senke.Welt.Lay
public import Runner.Basis.Res

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Invarianten Invarianten.Pruefer Invarianten.VC
  Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.Frag Invarianten.Modell
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

variable {D : Deklaration}

/-- Linux process-control requests are interpreted by the runner instead
    of going through the ordinary returning foreign-call continuation. -/
structure ImageGateTransportOK {D : Deklaration} (tor : D.Ax → Option Senke.TorB) : Prop where
  noClone : ∀ a gate, tor a = some gate → gate.nr ≠ Runner.NR_CLONE
  termination : ∀ a gate, tor a = some gate →
    (gate.nr = Runner.NR_EXIT ∨ gate.nr = Runner.NR_EXIT_GROUP) → D.aerg a = some .never

def imageGateTransportB (number : Nat) (result : Option Ty) : Bool :=
  decide (number ≠ Runner.NR_CLONE) &&
    decide ((number = Runner.NR_EXIT ∨ number = Runner.NR_EXIT_GROUP) → result = some .never)

/-- The executable decision keeps process control private to startup and
    allows Linux exit gates only under the model's non-returning type. -/
def checkImageGateTransports (u : UProg) (tor : (declOf u).Ax → Option Senke.TorB) :
    Except String (PLift (ImageGateTransportOK tor)) :=
  let gates := List.finRange u.axs.length
  let valid := fun a : (declOf u).Ax => (tor a).all fun gate =>
    imageGateTransportB gate.nr ((declOf u).aerg a)
  if checked : gates.all valid = true then .ok ⟨by
    have exactGate (a : (declOf u).Ax) (gate : Senke.TorB) (selected : tor a = some gate) :
        gate.nr ≠ Runner.NR_CLONE ∧
        ((gate.nr = Runner.NR_EXIT ∨ gate.nr = Runner.NR_EXIT_GROUP) → (declOf u).aerg a = some .never) := by
      have accepted := List.all_eq_true.mp checked a (List.mem_finRange a)
      simpa only [valid, selected, Option.all_some, imageGateTransportB, Bool.and_eq_true,
        decide_eq_true_eq] using accepted
    exact ⟨fun a gate selected => (exactGate a gate selected).1,
      fun a gate selected => (exactGate a gate selected).2⟩⟩
  else .error (match gates.find? (fun a => !valid a) with
    | some a => "ir: gate " ++ (uaxAt u a).name ++
        " binds clone or uses an exit number without returning never"
    | none => "ir: illegal Linux process-control gate")

/-- A declared non-returning process exit passes the real transport rule. -/
theorem neverExitGate_erfuellbar :
    imageGateTransportB Runner.NR_EXIT (some .never) = true ∧
    imageGateTransportB Runner.NR_EXIT_GROUP (some .never) = true := by
  decide

/-- The memory-dependent portion of the invariant decision. The lock
    predicate uses exactly the same collector as the full model check. -/
def CheckedInitialInvariants (E : Einheit D) (locks : List D.Lock) : Prop :=
  (∀ item ∈ D.invs, InvHaelt E.P item (E.sp0.welt [])) ∧
    (collect locks _ (checkLockInitial E.S E.lockFormulas E.sp0)).toOption.isSome = true

/-- Decide the invariants on the concrete initial memory after the program
    checker has already verified the writers. -/
def checkInitialInvariants (E : Einheit D) (locks : List D.Lock) :
    Except Frag.Refusal (PLift (CheckedInitialInvariants E locks)) := do
  let translated ← invariantFormula E.P D.invs
  if valid : translated.formula.eval (assignment (E.sp0.welt [])) = true then
    match locked : collect locks _ (checkLockInitial E.S E.lockFormulas E.sp0) with
    | .error cause => .error cause
    | .ok _ => return ⟨(translated.correct _).mp ((qf_eval _ _).mp valid), by rw [locked]; rfl⟩
  else .error (.unsupported "declared invariant is false in the initial memory")

/-- The accepted writer check and the checked initial memory together imply
    the exact invariant Bool of the goal theorem. -/
theorem CheckedInitialInvariants.goal_verdict {E : Einheit D} {functions : List D.Fn} {locks : List D.Lock}
    (initial : CheckedInitialInvariants E locks)
    (accepted : programInvariantsB E.P E.S functions E.lockFormulas {} locks = true) :
    invariantenGeprueftB E functions locks = true := by
  obtain ⟨program, read⟩ := (programInvariantsB_iff E.P E.S functions E.lockFormulas {} locks).mp accepted
  have valid := (qf_eval _ _).mpr ((program.invariants.correct _).mpr initial.1)
  unfold invariantenGeprueftB checkInvariants
  simp only [read, bind, Except.bind, dite_eq_left valid]
  have locked := initial.2
  cases result : collect locks _ (checkLockInitial E.S E.lockFormulas E.sp0) with
  | error cause => simp only [result, Except.toOption, Option.isSome_none, Bool.false_eq_true] at locked
  | ok checks => rfl

/-- The initial unit used for executable checks that need the program and
    concrete starts. Nonempty axiom families need separate reification. -/
abbrev initialUnit (u : UProg) (P : Programm (declOf u)) (memory : Speicher (declOf u))
    (starts : List (Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f)))
    (checks : List (CheckDecl (declOf u))) : Einheit (declOf u) :=
  OldSource.einheitVon u P (axWahr _) memory starts [] checks

/-- For axiom-free programs the emitter can decide the whole logic branch
    without any oracle contract supplied by the caller. -/
def checkAxiomFreeLogic (u : UProg) (P : Programm (declOf u)) (memory : Speicher (declOf u))
    (starts : List (Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f)))
    (checks : List (CheckDecl (declOf u))) :
    Except Frag.Refusal (PLift (u.axs.length = 0 →
      @nutzerPflichtGeprueftB _ (inferInstanceAs (DecidableEq (Fin u.fns.length)))
        (initialUnit u P memory starts checks) (List.finRange u.fns.length) (List.finRange u.locks.length) {} = true)) :=
  if noAxioms : u.axs.length = 0 then
    match read : @checkUnitLogic _ (inferInstanceAs (DecidableEq (Fin u.fns.length)))
        (initialUnit u P memory starts checks) (List.finRange u.fns.length) (List.finRange u.locks.length) {} with
    | .error cause => .error cause
    | .ok certificate => .ok ⟨fun _ => (nutzerPflichtGeprueftB_iff _ _ _ _).mpr ⟨certificate, read⟩⟩
  else .ok ⟨fun impossible => False.elim (noAxioms impossible)⟩

/-- Install the checked expressions without changing the source program,
    memory, or start configurations being judged. -/
def withForeignSummary (E : Einheit D) (summary : ForeignSummary E.P) : Einheit D :=
  { E with Q := summary.predicates, axiomSources := some summary.sources }

/-- Successful checking ties the exact foreign summary to the complete
    logic verdict of the model on the actual entry and root arguments. -/
structure CheckedForeignLogic (u : UProg) (E : Einheit (declOf u)) where
  summary : ForeignSummary E.P
  verdict : @nutzerPflichtGeprueftB _ (inferInstanceAs (DecidableEq (Fin u.fns.length)))
    (withForeignSummary E summary) (List.finRange u.fns.length) (List.finRange u.locks.length) {} = true

def checkImageForeignLogic (u : UProg) (E : Einheit (declOf u)) :
    Except String (CheckedForeignLogic u E) := do
  let summary ← checkForeignSummary u E.P
  letI : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length))
  let actual := withForeignSummary E summary
  match checked : checkUnitLogic actual (List.finRange u.fns.length) (List.finRange u.locks.length) {} with
  | .error refusal => .error ("foreign unit logic: " ++ refusal.message)
  | .ok certificate => .ok ⟨summary,
      (nutzerPflichtGeprueftB_iff _ _ _ _).mpr ⟨certificate, checked⟩⟩

end Gabbro.Stage0
