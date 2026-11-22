module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.AwaitLowering

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)} {l : Bool} {Γ : Ctx}

/-- Emit the ordinary match arms for the same ordered phases used by
    the canonical state record. Each block starts with its typed payload. -/
@[expose] public def phaseArms (types : TypeResolution) (f : AsyncFn) :
    (cases : List Phase) →
    ((index : Fin cases.length) → Block D V l (phaseType types f (cases.get index) :: Γ) Λ Λ) →
    Arms D V l Γ Λ Λ (cases.map fun phase => some (phaseType types f phase))
  | [], _ => .nil
  | _ :: rest, block =>
    .cons (block ⟨0, Nat.zero_lt_succ _⟩) (phaseArms types f rest (fun index => block index.succ))

/-- The ordinary match selects exactly the code at the encoded position,
    with the precise payload in the new binder. -/
public theorem phaseArms_exec (types : TypeResolution) (f : AsyncFn)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) :
    ∀ (cases : List Phase)
      (block : (index : Fin cases.length) → Block D V l (phaseType types f (cases.get index) :: Γ) Λ Λ)
      (index : Fin cases.length) (value : Wert D (phaseType types f (cases.get index))),
      execArms oracle passes calls (phaseArms types f cases block)
          (phaseValueAt D types f cases index value) world env =
        (execBlock oracle passes calls (block index) world (.cons value env)).schrumpf
  | [], _, index, _ => index.elim0
  | _ :: _, _, ⟨0, _⟩, _ => rfl
  | _ :: rest, block, ⟨offset + 1, valid⟩, value =>
    phaseArms_exec types f oracle passes calls world env rest (fun index => block index.succ)
      ⟨offset, Nat.lt_of_succ_lt_succ valid⟩ value

public theorem phaseArms_cost (types : TypeResolution) (f : AsyncFn)
    (exit : Nat) (calls : D.Fn → Nat) (passes limit : Nat) :
    ∀ (cases : List Phase)
      (blocks : (index : Fin cases.length) →
        Block D V l (phaseType types f (cases.get index) :: Γ) Λ Λ),
      (∀ index, kostenBlock exit calls passes (blocks index) ≤ limit) →
      kostenArms exit calls passes (phaseArms types f cases blocks) ≤ limit
  | [], _, _ => Nat.zero_le _
  | _ :: rest, blocks, bounded =>
    Nat.max_le_of_le_of_le (bounded ⟨0, Nat.zero_lt_succ _⟩)
      (phaseArms_cost types f exit calls passes limit rest (fun index => blocks index.succ)
        (fun index => bounded index.succ))

public theorem phaseArms_calls (types : TypeResolution) (f : AsyncFn)
    (direct : D.Fn → Bool) (indirect : Nat → Bool) (forever : Bool) :
    ∀ (cases : List Phase)
      (blocks : (index : Fin cases.length) →
        Block D V l (phaseType types f (cases.get index) :: Γ) Λ Λ),
      (∀ index, rufeB direct indirect forever (blocks index) = true) →
      rufeArms direct indirect forever (phaseArms types f cases blocks) = true
  | [], _, _ => rfl
  | _ :: rest, blocks, admitted =>
    Bool.and_eq_true_iff.mpr ⟨admitted ⟨0, Nat.zero_lt_succ _⟩,
      phaseArms_calls types f direct indirect forever rest (fun index => blocks index.succ)
        (fun index => admitted index.succ)⟩

public theorem PhaseListRep.locate {types : TypeResolution} {f : AsyncFn} {inventory : Inventory D}
    {cases : List Phase} {source : State (Value D) (Child D types)}
    {sum : Wert D (.sum (cases.map fun phase => some (phaseType types f phase)))}
    (represented : PhaseListRep D types f inventory cases source sum) :
    ∃ (index : Fin cases.length) (value : Wert D (phaseType types f (cases.get index))),
      sum = phaseValueAt D types f cases index value ∧
        PhaseRep D types f (cases.get index) source value ∧ MarksRep inventory (cases.get index) source := by
  induction represented with
  | first phase rest source value payload marks =>
    exact ⟨⟨0, Nat.zero_lt_succ _⟩, value, rfl, payload, marks⟩
  | later phase rest source sum _ _ ih =>
    obtain ⟨index, value, same, payload, marks⟩ := ih
    subst sum
    exact ⟨index.succ, value, rfl, payload, marks⟩

/-- Read only the phase field of the state record and dispatch through the
    canonical table. Neither the tag read nor entry into an arm emits an event. -/
@[expose] public def phaseDispatch (types : TypeResolution) (f : AsyncFn)
    (state : Var Γ (stateType types f))
    (block : (index : Fin (phases f).length) →
      Block D V l (phaseType types f ((phases f).get index) :: Γ) Λ Λ) : Stmt D V l Γ Λ Λ :=
  .onTag (.prodGet (.var state) .head) (phaseArms types f (phases f) block)

public theorem phaseDispatch_selects (types : TypeResolution) (f : AsyncFn) (inventory : Inventory D)
    (state : Var Γ (stateType types f))
    (block : (index : Fin (phases f).length) →
      Block D V l (phaseType types f ((phases f).get index) :: Γ) Λ Λ)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (source : State (Value D) (Child D types))
    (represented : Inv f types inventory source (env.get state)) :
    ∃ (index : Fin (phases f).length) (value : Wert D (phaseType types f ((phases f).get index))),
      PhaseRep D types f ((phases f).get index) source value ∧
      MarksRep inventory ((phases f).get index) source ∧
      execStmt oracle passes calls (phaseDispatch types f state block) world env =
        (execBlock oracle passes calls (block index) world (.cons value env)).schrumpf := by
  obtain ⟨index, value, encoded, payload, marks⟩ := PhaseListRep.locate represented
  refine ⟨index, value, payload, marks, ?_⟩
  have silent : world.lese Λ [] = world := rfl
  change execArms oracle passes calls (phaseArms types f (phases f) block) (env.get state).1
      (world.lese Λ []) env = _
  rw [silent, encoded]
  exact phaseArms_exec types f oracle passes calls world env (phases f) block index value

end Gabbro.Grammatik.Async.Representation
