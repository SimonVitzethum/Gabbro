module

public import Grammatik.Logik.Invarianten.VC.Compiler

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC.Extended

open Frag Elim Elim.Korrekt Modell

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D}
variable {program : Programm D} {checked : D.Fn → List D.Inv}

/-- The checker-facing entry point. Returned certificates can be fed directly
    to `writerVC`; refusals keep their offending source-form diagnostic.
    A supplied loop invariant is itself checked, never assumed. -/
def compileWriter (program : Programm D) (checked : D.Fn → List D.Inv)
    (facts : ∀ lock, Except Refusal (LockFormula S lock)) (budget : VCBudget)
    (loopInvariant : Option (QF (Observation D)))
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (code : Endblock D V l Γ Λ) (locals : Env D Γ) (terminal : QF (Observation D)) :
    Except Refusal (EndCondition program checked S code locals terminal) :=
  extendedEnd program checked facts budget.expansion loopInvariant budget.depth code locals terminal

/-- The existing writer matrix is independent of how its sufficient WP was
    generated. This instance covers locals, bounded loops and lock moves. -/
def writerVC {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {code : Endblock D V l Γ Λ} {locals : Env D Γ} {terminal : QF (Observation D)}
    (compiled : EndCondition program checked S code locals terminal)
    (entry path : LProp (Observation D)) : LProp (Observation D) :=
  close (writerMatrix entry path compiled.formula)

theorem writerVC_closed {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {code : Endblock D V l Γ Λ} {locals : Env D Γ} {terminal : QF (Observation D)}
    (compiled : EndCondition program checked S code locals terminal)
    (entry path : LProp (Observation D)) :
    closedUnderB [] (writerVC compiled entry path) = true := close_closed _

def writerCounterexample {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {code : Endblock D V l Γ Λ} {locals : Env D Γ} {terminal : QF (Observation D)}
    (compiled : EndCondition program checked S code locals terminal)
    (entry path : LProp (Observation D)) : Option (Assignment (Observation D)) :=
  let matrix := writerMatrix entry path compiled.formula
  counterexample (qfKeys matrix) (quoteQF matrix)

theorem writerCounterexample_complete {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {code : Endblock D V l Γ Λ} {locals : Env D Γ} {terminal : QF (Observation D)}
    (compiled : EndCondition program checked S code locals terminal)
    (entry path : LProp (Observation D))
    (rejected : decideB (writerVC compiled entry path) (writerVC_closed compiled entry path) = false) :
    ∃ values, writerCounterexample compiled entry path = some values :=
  counterexample_complete _ _ rejected

theorem writerVC_wp_sound {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {code : Endblock D V l Γ Λ} {locals : Env D Γ} {terminal : QF (Observation D)}
    (compiled : EndCondition program checked S code locals terminal)
    (entry path : LProp (Observation D))
    (accepted : decideB (writerVC compiled entry path) (writerVC_closed compiled entry path) = true)
    (runtime : Runtime program checked S) (world : World D)
    (initial : entry.denote (assignment world)) (onPath : path.denote (assignment world)) :
    runtime.wpE code (EndFlow terminal) world locals := by
  have bounded := (lower_denote _ (assignment world)).mp
    (close_sound _ accepted (assignment world))
  have implication := (lower_denote _ (assignment world)).mp
    ((quoteQF_denote _ _).mp (bounded (typeFacts_sound _ world)))
  exact compiled.sound runtime world
    ((quoteQF_denote _ _).mp (implication ⟨initial, onPath⟩))

/-- Generic owed-invariant soundness over the actual havoc/lock semantics.
    There is no `ohneLocks` premise and no use of unproved callee ensures.
    Q_rest is irrelevant: the generator accepts no foreign-call constructor. -/
theorem writerVC_sound (program : Programm D) (checked : D.Fn → List D.Inv)
    (f : D.Fn) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
    (post : InvariantFormula program (D.invs.filter (fun i => schuldet f i)))
    (compiled : ∀ locals : Env D (D.params f),
      EndCondition program checked S (program.rumpf f) locals post.formula)
    (entry path : LProp (Observation D))
    (accepted : ∀ locals, decideB (writerVC (compiled locals) entry path) (writerVC_closed (compiled locals) entry path) = true)
    (initial : ∀ world locals, ReqAmEintritt program f world locals →
      entry.denote (assignment world) ∧ path.denote (assignment world))
    (handlers : ∀ calls, RespektiertRahmen program calls →
      OhneVorbedingung calls → CallEvidence program checked calls) : InvGutS program passes Q S f := by
  intro O _ _ _ U havoc calls respects noPre world locals requires next value returned
  let runtime : Runtime program checked S :=
    { oracle := O
      passes := passes
      calls := calls
      evidence := handlers calls respects noPre
      environment := U
      havoc := havoc }
  have run := writerVC_wp_sound (compiled locals) entry path (accepted locals)
    runtime world (initial world locals requires).1 (initial world locals requires).2
  change EndFlow post.formula (execEndH S O U passes calls (program.rumpf f) world locals) at run
  rw [returned] at run
  intro item member owed
  exact (post.correct next).mp run item (List.mem_filter.mpr ⟨member, owed⟩)

end Gabbro.Grammatik.Invarianten.VC.Extended
