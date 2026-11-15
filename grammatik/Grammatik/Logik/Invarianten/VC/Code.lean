module

public import Grammatik.Logik.Invarianten.VC.Calls
public import Grammatik.Logik.WP.Kern

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC

open Frag Elim Elim.Korrekt Modell

variable {D : Deklaration} {V : Vertrag D}

/-- Normal continuation and early exits have different obligations. In
    particular a return in the middle of a block must establish the FINAL
    invariant, not the precondition of unreachable remaining statements. -/
def Flow {l : Bool} {Γ : Ctx} (normal terminal : QF (Observation D))
    (locals : Env D Γ) : Ausgang V l Γ → Prop
  | .ok world next => next = locals ∧ normal.denote (assignment world)
  | .zurueck world _ | .why world _ | .leave _ world _ | .next _ world _ =>
      terminal.denote (assignment world)
  | .logik _ | .hardware _ => True

structure StatementVC (program : Programm D) (checked : D.Fn → List D.Inv)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Stmt D V l Γ Λ Λ') (locals : Env D Γ)
    (normal terminal : QF (Observation D)) where
  formula : QF (Observation D)
  sound : ∀ (O : Orakel D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
    CallEvidence program checked calls → ∀ world, formula.denote (assignment world) →
      WP.wpS O passes calls code (Flow normal terminal locals) world locals

structure BlockVC (program : Programm D) (checked : D.Fn → List D.Inv)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Block D V l Γ Λ Λ') (locals : Env D Γ)
    (normal terminal : QF (Observation D)) where
  formula : QF (Observation D)
  sound : ∀ (O : Orakel D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
    CallEvidence program checked calls → ∀ world, formula.denote (assignment world) →
      WP.wpB O passes calls code (Flow normal terminal locals) world locals

section Compiler

variable (program : Programm D) (checked : D.Fn → List D.Inv)

mutual

/-- Generate a sufficient weakest precondition for the actual typed statement.
    Unsupported source forms return an explicit refusal. Call havoc is the only
    intentional overapproximation in the supported straight-line subset. -/
def statement {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Stmt D V l Γ Λ Λ') (locals : Env D Γ)
    (normal terminal : QF (Observation D)) :
    Except Frag.Refusal (StatementVC program checked code locals normal terminal) :=
  match code with
  | .assignGlob name expression _ _ => do
      let pre ← scalarWP expression locals (.glob name) normal
      return {
          formula := pre.formula
          sound := fun O passes calls evidence world valid => by
            refine ⟨rfl, ?_⟩
            rw [assignment_schreibGlob]
            apply pre.sound
            rw [assignment_lese]
            exact valid }
  | .assignSlot table field index expression _ _ | .assignThru _ table _ field index expression _ _ => do
      let encodedIndex ← translate index locals
      let offset ← encodedIndex.constantIndex
      let pre ← scalarWP expression locals (.slot table field offset.val) normal
      return {
          formula := pre.formula
          sound := fun O passes calls evidence world valid => by
            refine ⟨rfl, ?_⟩
            rw [assignment_schreibSlot, offset.property]
            apply pre.sound
            rw [assignment_lese]
            exact valid }
  | .ite condition yes no => do
      let guard ← translate condition locals
      let yesVC ← block yes locals normal terminal
      let noVC ← block no locals normal terminal
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
                simp only [WP.wpS, WP.wpB, execStmt]
                split
                · exact result
                · rename_i other
                  exact (other tested).elim
            | false =>
                have absent : ¬ guard.payload.denote (assignment world) := by
                  intro h
                  rw [← agree] at h
                  have := (guard.correct read).mpr h
                  rw [tested] at this
                  exact Bool.noConfusion this
                have result := noVC.sound O passes calls evidence read (by
                  rw [agree]
                  exact (quoteQF_denote _ _).mp (branches.2 absent))
                simp only [WP.wpS, WP.wpB, execStmt]
                split
                · rename_i taken
                  exact Bool.noConfusion (taken.symm.trans tested)
                · exact result }
  | .call f args _ noReasons => do
      let facts ← invariantFormula program (checked f)
      return {
          formula := callWP f facts.formula normal
          sound := fun O passes calls evidence world valid => by
            let read := world.lese Λ args.orte
            let actual := evalArgs read args read locals
            have validRead : (callWP f facts.formula normal).denote (assignment read) := by
              rw [assignment_lese]
              exact valid
            unfold WP.wpS
            dsimp only [execStmt]
            cases reply : calls f read actual with
            | ok next value =>
                have frame := evidence.frame f read actual next value reply
                have known := (facts.correct next).mpr
                  (evidence.invariants f read actual next value reply)
                have result := callWP_sound f facts.formula normal read next validRead frame known
                exact ⟨rfl, result⟩
            | why next reason => exact (Fin.cast noReasons reason).elim0
            | logik error => trivial
            | hardware error => trivial }
  | .breaking _ body => do
      let pre ← block body locals normal terminal
      return {
          formula := pre.formula
          sound := fun O passes calls evidence world valid =>
            pre.sound O passes calls evidence world valid }
  | .ret expression _ => .ok
      { formula := terminal
        sound := fun O passes calls evidence world valid => by
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
  | .retry .. => .error (.unsupported "retry needs a checked loop invariant or budgeted unrolling")
  | .traverse .. => .error (.unsupported "traverse needs a checked loop invariant or budgeted unrolling")
  | .forever .. => .error (.unsupported "forever needs a checked loop invariant")
  | .locks .. => .error (.unsupported "lock scopes need acquire and release verification conditions")
  | .assignVar .. => .error (.unsupported "mutable locals need a symbolic local environment")
  | _ => .error (.unsupported "writer statement: requires a supported scalar, branch, or checked call")

/-- Sequence composition uses the existing WP calculus's actual continuation;
    no second execution semantics or interpreter is introduced. -/
def block {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Block D V l Γ Λ Λ') (locals : Env D Γ)
    (normal terminal : QF (Observation D)) :
    Except Frag.Refusal (BlockVC program checked code locals normal terminal) :=
  match code with
  | .nil => .ok
      { formula := normal
        sound := fun _ _ _ _ _ valid => ⟨rfl, valid⟩ }
  | .cons first rest => do
      let tail ← block rest locals normal terminal
      let head ← statement first locals tail.formula terminal
      return {
          formula := head.formula
          sound := fun O passes calls evidence world valid => by
            have step := head.sound O passes calls evidence world valid
            unfold WP.wpS at step
            unfold WP.wpB
            simp only [execBlock]
            cases result : execStmt O passes calls first world locals with
            | ok next nextLocals =>
                rw [result] at step
                obtain ⟨same, ready⟩ := step
                subst nextLocals
                exact tail.sound O passes calls evidence next ready
            | zurueck next value => simpa only [result, Flow] using step
            | why next reason => simpa only [result, Flow] using step
            | leave h next nextLocals => simpa only [result, Flow] using step
            | next h next nextLocals => simpa only [result, Flow] using step
            | logik error => trivial
            | hardware error => trivial }
  | .bind .. => .error (.unsupported "local bindings need a symbolic local environment")
  | .bindCall .. => .error (.unsupported "bound call results need a symbolic local environment")
  | _ => .error (.unsupported "writer block: local binding or non-scalar operation")

end

end Compiler

end Gabbro.Grammatik.Invarianten.VC
