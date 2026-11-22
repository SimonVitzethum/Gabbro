module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.CheckedPoll

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)} {l : Bool} {Γ : Ctx}
  {types : TypeResolution} {f : AsyncFn}

@[expose] public def pollResultType (types : TypeResolution) (f : AsyncFn) : Ty :=
  .sum [some (types.ordinary f.resultType), some (stateType types f)]

@[expose] public def readyReply {types : TypeResolution} {f : AsyncFn}
    (value : Expr D Γ Λ (types.ordinary f.resultType)) : Expr D Γ Λ (pollResultType types f) :=
  .case _ ⟨0, Nat.zero_lt_succ 1⟩ (.val value)

@[expose] public def pendingReply {types : TypeResolution} {f : AsyncFn}
    (state : Var Γ (stateType types f)) : Expr D Γ Λ (pollResultType types f) :=
  .case _ ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩ (.val (.var state))

@[expose] public def resultExpr {declared : Option Ty} (result : declared = some (pollResultType types f))
    (value : Expr D Γ Λ (pollResultType types f)) : ErgExpr D Γ Λ declared :=
  result.symm ▸ ErgExpr.val value

@[expose] public def resultValue {declared : Option Ty} (result : declared = some (pollResultType types f))
    (value : Wert D (pollResultType types f)) : ErgVal D declared :=
  result.symm ▸ value

public theorem resultExpr_eval {declared : Option Ty} (result : declared = some (pollResultType types f))
    (value : Expr D Γ Λ (pollResultType types f)) (world : World D) (env : Env D Γ) :
    (resultExpr result value).orte = value.orte ∧
      evalErg world (resultExpr result value) world env = resultValue result (eval world value world env) := by
  subst declared
  exact ⟨rfl, rfl⟩

@[expose] public def Pollable : State (Value D) (Child D types) → Prop
  | .running .. | .waiting .. => True
  | .completed .. | .cancelled => False

@[expose] public def pollGuardArm (types : TypeResolution) (f : AsyncFn) :
    (phase : Phase) → Block D V l (phaseType types f phase :: Γ) Λ Λ
  | .completed | .cancelled => rejectBlock _ _ _ _ _
  | .running .. | .waiting .. => .nil

/-- Invalid activation of a completed or cancelled future is refused at
    the private poll entry. Running and Waiting dispatch are silent. -/
@[expose] public def pollGuard (types : TypeResolution) (f : AsyncFn)
    (state : Var Γ (stateType types f)) : Stmt D V l Γ Λ Λ :=
  phaseDispatch types f state (fun i => pollGuardArm types f ((phases f).get i))

private theorem pollGuardArm_exec (types : TypeResolution) (f : AsyncFn)
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (phase : Phase)
    (source : State (Value D) (Child D types)) (value : Wert D (phaseType types f phase))
    (payload : PhaseRep D types f phase source value) :
    (execBlock oracle passes calls (pollGuardArm (V := V) (Λ := Λ) (l := l) types f phase)
      world (.cons value env)).schrumpf =
      match source with
      | .running .. | .waiting .. => .ok world env
      | .completed .. | .cancelled => .logik .kapazitaet := by
  cases payload with
  | running | waiting => rfl
  | cancelled | completed =>
    rw [pollGuardArm, rejectBlock_exec]
    rfl

public theorem pollGuard_exec (types : TypeResolution) (f : AsyncFn)
    (inventory : Inventory D) (state : Var Γ (stateType types f))
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (source : State (Value D) (Child D types))
    (represented : Inv f types inventory source (env.get state)) :
    execStmt oracle passes calls (pollGuard (V := V) (Λ := Λ) (l := l) types f state) world env =
      match source with
      | .running .. | .waiting .. => .ok world env
      | .completed .. | .cancelled => .logik .kapazitaet := by
  obtain ⟨i, value, payload, _, ran⟩ := phaseDispatch_selects types f inventory state
    (fun i => pollGuardArm (V := V) (Λ := Λ) (l := l) types f ((phases f).get i)) oracle passes calls
    world env source represented
  exact ran.trans (pollGuardArm_exec types f oracle passes calls world env ((phases f).get i) source value payload)

@[expose] public def pollAnswerArm (state : Var Γ (stateType types f))
    (result : V.erg = some (pollResultType types f)) (exit : Λ.Perm V.ende) :
    (phase : Phase) → Block D V l (phaseType types f phase :: Γ) Λ Λ
  | .completed => .cons (.ret (resultExpr result (readyReply (.prodGet (.var .here) .head))) exit) .nil
  | .waiting .. => .cons (.ret (resultExpr result (pendingReply (.there state))) exit) .nil
  | .running .. | .cancelled => rejectBlock _ _ _ _ _

@[expose] public def pollAnswer (state : Var Γ (stateType types f))
    (result : V.erg = some (pollResultType types f)) (exit : Λ.Perm V.ende) : Stmt D V l Γ Λ Λ :=
  phaseDispatch types f state (fun i => pollAnswerArm state result exit ((phases f).get i))

private theorem pollAnswerArm_completed (state : Var Γ (stateType types f))
    (result : V.erg = some (pollResultType types f)) (exit : Λ.Perm V.ende)
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (phase : Phase) (value : Value D)
    (payload : Wert D (phaseType types f phase))
    (selected : PhaseRep D types f phase (.completed value ⟨[], []⟩) payload) :
    ∃ typed, valueAt D (types.ordinary f.resultType) value = some typed ∧
      (execBlock oracle passes calls (pollAnswerArm (l := l) state result exit phase)
        world (.cons payload env)).schrumpf = .zurueck world
          (resultValue result (⟨⟨0, Nat.zero_lt_succ 1⟩, typed⟩ : Wert D (pollResultType types f))) := by
  cases selected with
  | completed _ typed known =>
    let value : Expr D (phaseType types f .completed :: Γ) Λ (pollResultType types f) :=
      readyReply (.prodGet (.var .here) .head)
    let entered : Env D (phaseType types f .completed :: Γ) := .cons (typed, ()) env
    have observed := resultExpr_eval result value world entered
    have localReads : (resultExpr result value).orte = [] := observed.1
    refine ⟨typed, known, ?_⟩
    change Ausgang.zurueck (world.lese Λ (resultExpr result value).orte)
      (evalErg (world.lese Λ (resultExpr result value).orte) (resultExpr result value)
        (world.lese Λ (resultExpr result value).orte) entered) = _
    rw [localReads, show world.lese Λ [] = world from rfl, observed.2]
    rfl

public theorem pollAnswer_completed (inventory : Inventory D) (state : Var Γ (stateType types f))
    (result : V.erg = some (pollResultType types f)) (exit : Λ.Perm V.ende)
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (value : Value D)
    (represented : Inv f types inventory (.completed value ⟨[], []⟩) (env.get state)) :
    ∃ typed, valueAt D (types.ordinary f.resultType) value = some typed ∧
      execStmt oracle passes calls (pollAnswer (l := l) state result exit) world env = .zurueck world
        (resultValue result (⟨⟨0, Nat.zero_lt_succ 1⟩, typed⟩ : Wert D (pollResultType types f))) := by
  obtain ⟨i, payload, selected, _, ran⟩ := phaseDispatch_selects types f inventory state
    (fun i => pollAnswerArm (l := l) state result exit ((phases f).get i)) oracle passes calls world env _ represented
  obtain ⟨typed, known, returned⟩ := pollAnswerArm_completed (l := l) state result exit oracle passes calls
    world env ((phases f).get i) value payload selected
  exact ⟨typed, known, ran.trans returned⟩

/-- Generate an ordinary private G function. The single input is the
    future state, and its normal result is the canonical Ready/Pending sum. -/
@[expose] public def pollFunction {elaboration : Elaboration D V Λ types f}
    (table : (index : Fin (phases f).length) → PhasePlan elaboration ((phases f).get index))
    (result : V.erg = some (pollResultType types f)) (exit : Λ.Perm V.ende) :
    Endblock D V false [stateType types f] Λ :=
  .bind .fls
    (.cons (pollGuard types f (.there .here))
      (.cons (checkedRetryStmt table (.there .here) .here (rejectBlock _ _ _ _ _))
        (.cons (pollAnswer (.there .here) result exit)
          (.ret (resultExpr result (pendingReply (.there .here))) exit))))

end Gabbro.Grammatik.Async.Representation
