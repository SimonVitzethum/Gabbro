module

public import Grammatik.Kern.Syntax.Extensions.Zucker.TransitionShift
public import Grammatik.Kern.Semantik.Semantik.TransitionCall

public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The source-stage equality of the constant edge holds exactly when the
    current cell is the edge's source: the legal entry of the primitive shift. -/
theorem constEdge_legal {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} (edge : ConstEdge D V Γ Λ)
    (state : World D) (env : Env D Γ)
    (holds : wahr? (eval state edge.write.sourceEq state env) = true) :
    (Wert.umTyp edge.numeric (state.slots edge.table (env.get edge.index).n edge.field)).n =
      edge.source := by
  simp only [ConstEdge.write, TransitionWrite.constEdge, TransitionWrite.sourceEq,
    eval_umTyp, eval, wahr?, Zahl.weiter] at holds
  simpa using holds

/-- The generated shift body writes exactly what the snapshot specification
    writes: the stored cell, with the same value, at the entry index. -/
theorem constEdge_written {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} (edge : ConstEdge D V Γ Λ)
    (entry state : World D) (env : Env D Γ) :
    edge.write.writtenWorld entry env state =
      state.schreibSlot edge.table Λ (env.get edge.index).n edge.field
        (Wert.umTyp edge.numeric.symm ⟨edge.target, edge.targetRange.1, edge.targetRange.2⟩) :=
  rfl

/-- Every successful call of a generated constant-edge function satisfies the
    declaration's full relation: the clause, the source-stage equality, the
    ordinary store of the target stage and the ordinary frame. The primitive
    shift agrees with that store because the requires made the entry legal. -/
theorem TransitionShiftExpansion.call_correct {P : Programm D} {f : D.Fn}
    (expansion : TransitionShiftExpansion P f) (O : Orakel D) (passes fuel : Nat)
    (entry : World D) (env : Env D (D.params f))
    (post : World D) (value : ErgVal D (D.erg f))
    (success : rufAt P O passes (fuel + 1) f entry env = .ok post value) :
    let checked := entry.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte
    let written := transitionWorld [expansion.shift.write] checked env checked
    ((∀ write ∈ [expansion.shift.write],
      wahr? (eval checked write.sourceEq checked env) = true) ∧
      wahr? (eval checked expansion.clause checked env) = true) ∧
    post.slots = written.slots ∧ post.globs = written.globs ∧
    Rahmen (D.schreibt f) (D.gschreibt f) entry post := by
  dsimp only
  obtain ⟨pre, bodyWorld, bodyValue, bodyRun, slots, globs⟩ :=
    transition_call_inversion P O passes fuel f entry env post value success
  let checked := entry.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte
  have preRelation := (transitionRequires_iff [expansion.shift.write] expansion.clause
    checked checked env).mp (by rw [← expansion.requires_exact]; exact pre)
  have legal := constEdge_legal expansion.shift checked env
    (preRelation.1 _ List.mem_cons_self)
  have shifted := transition_constant_shift (V := vertragVon D f) (l := false) O passes
    (rufAt P O passes fuel) expansion.shift.table expansion.shift.field expansion.shift.numeric
    expansion.shift.index expansion.shift.source expansion.shift.target
    expansion.shift.targetRange expansion.shift.erlaubt expansion.shift.right
    expansion.shift.guard checked env legal
  dsimp only at shifted
  obtain ⟨runShift, -, slotsEq, globsEq⟩ := shifted
  obtain ⟨world, hWorld, worldSlots, worldGlobs⟩ : ∃ world,
      execStmt O passes (rufAt P O passes fuel) expansion.shift.statement
          (entry.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) env =
        .ok world env ∧
      world.slots = (transitionWorld [expansion.shift.write] checked env checked).slots ∧
      world.globs = (transitionWorld [expansion.shift.write] checked env checked).globs :=
    ⟨_, runShift, by rw [slotsEq]; rfl, by rw [globsEq]; rfl⟩
  rw [expansion.body_exact] at bodyRun
  simp only [execEnd, hWorld] at bodyRun
  obtain ⟨returnValue, returnRun⟩ := transitionReturn_world (V := vertragVon D f)
    (Γ := D.params f) (Λ := Signatur.anfang D (D.signatur f)) expansion.result_none
    (by rw [expansion.resources])
    O passes (rufAt P O passes fuel) world env
  rw [returnRun] at bodyRun
  cases bodyRun
  have slotsFinal := slots.trans worldSlots
  have globsFinal := globs.trans worldGlobs
  refine ⟨preRelation, slotsFinal, globsFinal, ?_⟩
  have preFrame : Rahmen (D.schreibt f) (D.gschreibt f) entry checked := rahmen_gleich rfl rfl
  have rights : ∀ write ∈ [expansion.shift.write], write.Permitted (vertragVon D f) := by
    intro write member
    have same := List.mem_singleton.mp member
    subst same
    exact expansion.shift.right
  have postFrame : Rahmen (D.schreibt f) (D.gschreibt f)
      (transitionWorld [expansion.shift.write] checked env checked) post :=
    rahmen_gleich slotsFinal globsFinal
  exact (preFrame.trans (transitionWorld_frame [expansion.shift.write] rights checked checked env)).trans
    postFrame

end Gabbro.Grammatik
