module

public import Grammatik.Logik.Invarianten.VC.Code
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T2.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC

open Frag Elim Elim.Korrekt Modell

variable {D : Deklaration} {V : Vertrag D}

/-- Every state-bearing exit owes the invariant, including reason returns.
    Stops have no post-state; absence of logic stops is a separate model duty. -/
def EndFlow {l : Bool} {Γ : Ctx} (terminal : QF (Observation D)) : EndAusgang V l Γ → Prop
  | .zurueck world _ | .why world _ | .leave _ world _ | .next _ world _ =>
      terminal.denote (assignment world)
  | .logik _ | .hardware _ => True

structure EndVC (program : Programm D) (checked : D.Fn → List D.Inv)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (code : Endblock D V l Γ Λ) (locals : Env D Γ) (terminal : QF (Observation D)) where
  formula : QF (Observation D)
  sound : ∀ (O : Orakel D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
    CallEvidence program checked calls → ∀ world, formula.denote (assignment world) →
      WP.wpE O passes calls code (EndFlow terminal) world locals

def endBlock (program : Programm D) (checked : D.Fn → List D.Inv)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (code : Endblock D V l Γ Λ) (locals : Env D Γ) (terminal : QF (Observation D)) :
    Except Frag.Refusal (EndVC program checked code locals terminal) :=
  match code with
  | .ret expression _ => .ok
      { formula := terminal
        sound := fun _ _ _ _ world valid => by
          change terminal.denote (assignment (world.lese Λ expression.orte))
          rw [assignment_lese]
          exact valid }
  | .retWhy _ _ => .ok
      { formula := terminal
        sound := fun _ _ _ _ _ valid => valid }
  | .leave _ => .ok
      { formula := terminal
        sound := fun _ _ _ _ _ valid => valid }
  | .next _ => .ok
      { formula := terminal
        sound := fun _ _ _ _ _ valid => valid }
  | .cons first rest => do
      let tail ← endBlock program checked rest locals terminal
      let head ← statement program checked first locals tail.formula terminal
      return {
          formula := head.formula
          sound := fun O passes calls evidence world valid => by
            have step := head.sound O passes calls evidence world valid
            unfold WP.wpS at step
            unfold WP.wpE
            simp only [execEnd]
            cases result : execStmt O passes calls first world locals with
            | ok next nextLocals =>
                rw [result] at step
                obtain ⟨same, ready⟩ := step
                subst nextLocals
                exact tail.sound O passes calls evidence next ready
            | zurueck next value => simpa only [result, Flow, EndFlow] using step
            | why next reason => simpa only [result, Flow, EndFlow] using step
            | leave h next nextLocals => simpa only [result, Flow, EndFlow] using step
            | next h next nextLocals => simpa only [result, Flow, EndFlow] using step
            | logik error => trivial
            | hardware error => trivial }
  | .ite condition yes no => do
      let guard ← translate condition locals
      let yesVC ← endBlock program checked yes locals terminal
      let noVC ← endBlock program checked no locals terminal
      return {
          formula := lower (.and (.imp guard.payload (quoteQF yesVC.formula))
            (.imp (.not guard.payload) (quoteQF noVC.formula)))
          sound := fun O passes calls evidence world valid => by
            let read := world.lese Λ condition.orte
            have branches := (lower_denote _ (assignment world)).mp valid
            have agree : assignment read = assignment world := assignment_lese _ _ _
            cases tested : eval read condition read locals with
            | true =>
                have present := (guard.correct read).mp tested
                rw [agree] at present
                have result := yesVC.sound O passes calls evidence read (by
                  rw [agree]
                  exact (quoteQF_denote _ _).mp (branches.1 present))
                simpa only [WP.wpE, execEnd, tested, wahr?, ↓reduceIte] using result
            | false =>
                have absent : ¬ guard.payload.denote (assignment world) := by
                  intro h
                  rw [← agree] at h
                  have := (guard.correct read).mpr h
                  simp only [tested, Bool.false_eq_true] at this
                have result := noVC.sound O passes calls evidence read (by
                  rw [agree]
                  exact (quoteQF_denote _ _).mp (branches.2 absent))
                simpa only [WP.wpE, execEnd, tested, wahr?, ↓reduceIte] using result }
  | .bind .. => .error (.unsupported "local bindings need a symbolic local environment")
  | .bindCall .. => .error (.unsupported "bound call results need a symbolic local environment")
  | _ => .error (.unsupported "writer end block: binding, loop, or scoped operation")

/-- Add the model type facts before universal closure. This prevents an
    impossible out-of-range integer assignment from rejecting a typed writer. -/
def writerMatrix (entry path : LProp (Observation D)) (pre : QF (Observation D)) :
    QF (Observation D) :=
  let body := lower (.imp (.and entry path) (quoteQF pre))
  lower (.imp (typeFacts (qfKeys body)) (quoteQF body))

/-- A writer VC is `entry AND path -> wp body invariant`, universally closed.
    The entry formula can include the translated invariant; the adapter below
    explicitly requires the model's function precondition to establish it. -/
def writerVC {program : Programm D} {checked : D.Fn → List D.Inv}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {code : Endblock D V l Γ Λ} {locals : Env D Γ} {terminal : QF (Observation D)}
    (compiled : EndVC program checked code locals terminal)
    (entry path : LProp (Observation D)) : LProp (Observation D) :=
  close (writerMatrix entry path compiled.formula)

theorem writerVC_closed {program : Programm D} {checked : D.Fn → List D.Inv}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {code : Endblock D V l Γ Λ} {locals : Env D Γ} {terminal : QF (Observation D)}
    (compiled : EndVC program checked code locals terminal)
    (entry path : LProp (Observation D)) :
    closedUnderB [] (writerVC compiled entry path) = true := close_closed _

/-- False VCs expose a checked assignment to the generated arithmetic
    condition. Call havoc is an abstraction: this theorem does not claim that
    every such assignment is an execution of a particular callee body. -/
def writerCounterexample {program : Programm D} {checked : D.Fn → List D.Inv}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {code : Endblock D V l Γ Λ} {locals : Env D Γ} {terminal : QF (Observation D)}
    (compiled : EndVC program checked code locals terminal)
    (entry path : LProp (Observation D)) : Option (Assignment (Observation D)) :=
  let matrix := writerMatrix entry path compiled.formula
  counterexample (qfKeys matrix) (quoteQF matrix)

theorem writerCounterexample_complete {program : Programm D} {checked : D.Fn → List D.Inv}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {code : Endblock D V l Γ Λ} {locals : Env D Γ} {terminal : QF (Observation D)}
    (compiled : EndVC program checked code locals terminal)
    (entry path : LProp (Observation D))
    (rejected : decideB (writerVC compiled entry path) = false) :
    ∃ values, writerCounterexample compiled entry path = some values :=
  counterexample_complete _ _ rejected

theorem writerCounterexample_sound {program : Programm D} {checked : D.Fn → List D.Inv}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {code : Endblock D V l Γ Λ} {locals : Env D Γ} {terminal : QF (Observation D)}
    (compiled : EndVC program checked code locals terminal)
    (entry path : LProp (Observation D)) (values : Assignment (Observation D))
    (found : writerCounterexample compiled entry path = some values) :
    entry.denote values ∧ path.denote values ∧ ¬ compiled.formula.denote values := by
  classical
  have invalid := counterexample_sound _ _ values found
  have matrixInvalid : ¬ (writerMatrix entry path compiled.formula).denote values :=
    fun h => invalid ((quoteQF_denote _ _).mpr h)
  let body := lower (.imp (.and entry path) (quoteQF compiled.formula))
  have bodyInvalid : ¬ body.denote values := by
    intro h
    apply matrixInvalid
    exact (lower_denote _ _).mpr (fun _ => (quoteQF_denote _ _).mpr h)
  have initial : entry.denote values ∧ path.denote values := by
    by_contra absent
    apply bodyInvalid
    exact (lower_denote _ _).mpr (fun h => False.elim (absent h))
  refine ⟨initial.1, initial.2, ?_⟩
  intro h
  apply bodyInvalid
  exact (lower_denote _ _).mpr (fun _ => (quoteQF_denote _ _).mpr h)

theorem writerVC_wp_sound {program : Programm D} {checked : D.Fn → List D.Inv}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {code : Endblock D V l Γ Λ} {locals : Env D Γ} {terminal : QF (Observation D)}
    (compiled : EndVC program checked code locals terminal)
    (entry path : LProp (Observation D))
    (accepted : decideB (writerVC compiled entry path) = true)
    (O : Orakel D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (evidence : CallEvidence program checked calls) (world : World D)
    (initial : entry.denote (assignment world)) (onPath : path.denote (assignment world)) :
    WP.wpE O passes calls code (EndFlow terminal) world locals := by
  have bounded := (lower_denote _ (assignment world)).mp
    (close_sound _ accepted (assignment world))
  have implication := (lower_denote _ (assignment world)).mp
    ((quoteQF_denote _ _).mp (bounded (typeFacts_sound _ world)))
  exact compiled.sound O passes calls evidence world
    ((quoteQF_denote _ _).mp (implication ⟨initial, onPath⟩))

/-- Exact connection to the model's own owed-invariant obligation. The current
    handler class has frames but does not promise checked callee invariants:
    `handlers` records that missing premise explicitly. With no callee facts it
    is discharged by `frameOnlyEvidence`, without using any ensures. The
    `entry` premise is necessary: `InvGutS` assumes requires, not Inv(pre). -/
theorem writerVC_sound (program : Programm D) (checked : D.Fn → List D.Inv)
    (f : D.Fn) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
    (post : InvariantFormula program (D.invs.filter (fun i => schuldet f i)))
    (compiled : ∀ locals : Env D (D.params f),
      EndVC program checked (program.rumpf f) locals post.formula)
    (entry path : LProp (Observation D))
    (accepted : ∀ locals, decideB (writerVC (compiled locals) entry path) = true)
    (initial : ∀ world locals, ReqAmEintritt program f world locals →
      entry.denote (assignment world) ∧ path.denote (assignment world))
    (handlers : ∀ calls, RespektiertRahmen program calls →
      OhneVorbedingung calls → CallEvidence program checked calls)
    (noLocks : (program.rumpf f).ohneLocks = true) : InvGutS program passes Q S f := by
  intro O _ _ _ U _ calls respects noPre world locals requires next value returned
  have run := writerVC_wp_sound (compiled locals) entry path (accepted locals)
    O passes calls (handlers calls respects noPre) world
    (initial world locals requires).1 (initial world locals requires).2
  unfold WP.wpE at run
  rw [Endblock.execH_ohne S O U passes calls _ noLocks world locals] at returned
  rw [returned] at run
  intro item member owed
  exact (post.correct next).mp run item (List.mem_filter.mpr ⟨member, owed⟩)

end Gabbro.Grammatik.Invarianten.VC
