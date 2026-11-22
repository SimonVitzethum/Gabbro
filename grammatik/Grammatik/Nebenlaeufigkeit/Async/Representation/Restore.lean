module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Slots

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {types : TypeResolution} {f : AsyncFn}
  {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- A lexical context belongs to the frame only if each name resolves to
    its declared type. The proof retains the lookup used for its G offset. -/
public inductive RestorePlan (types : TypeResolution) (f : AsyncFn) : List (String × Ty) → Type where
  | nil : RestorePlan types f []
  | cons (name : String) (sourceType : Parser.STyp) {rest : List (String × Ty)}
      (found : (f.params ++ f.fields).lookup name = some sourceType) (tail : RestorePlan types f rest) :
      RestorePlan types f ((name, types.ordinary sourceType) :: rest)

@[expose] public def restorePlanFor (types : TypeResolution) (f : AsyncFn) :
    (locals : List (String × Ty)) → Except String (RestorePlan types f locals)
  | [] => .ok .nil
  | (name, expected) :: rest => do
    match found : (f.params ++ f.fields).lookup name with
    | none => throw "async: missing saved local declaration"
    | some sourceType =>
      if same : types.ordinary sourceType = expected then
        let tail ← restorePlanFor types f rest
        pure (by subst expected; exact .cons name sourceType found tail)
      else throw "async: saved local type differs from expression scope"

@[expose] public def prependLocal {τ : Ty} (x : Var Γ τ) :
    (scope : Ctx) → Var (scope ++ Γ) τ
  | [] => x
  | _ :: rest => .there (prependLocal x rest)

@[expose] public def appendLocals : ∀ {scope : Ctx}, Env D scope → Env D Γ → Env D (scope ++ Γ)
  | _, .nil, outer => outer
  | _, .cons value rest, outer => .cons value (appendLocals rest outer)

public theorem get_prependLocal {τ : Ty} (x : Var Γ τ) (outer : Env D Γ) :
    ∀ {scope : Ctx} (locals : Env D scope), (appendLocals locals outer).get (prependLocal x scope) = outer.get x
  | _, .nil => rfl
  | _, .cons _ rest => get_prependLocal x outer rest

@[expose] public def removeLocals : (locals : Ctx) → Ausgang V l (locals ++ Γ) → Ausgang V l Γ
  | [], result => result
  | _ :: rest, result => removeLocals rest result.schrumpf

/-- Emit ordinary tagged projections in the lexical order of the scope.
    A dead field goes to the ordinary checked refusal arm. -/
@[expose] public def restoreFrameBlock : {locals : List (String × Ty)} → RestorePlan types f locals →
    Var Γ (frameType types f) → Block D V l (locals.map Prod.snd ++ Γ) Λ Λ → Block D V l Γ Λ Λ
  | [], .nil, _, body => body
  | _, .cons name sourceType (rest := rest) found tail, saved, body =>
    let selected := frameSlot types name sourceType (f.params ++ f.fields) found
    let savedLocal := prependLocal saved (rest.map Prod.snd)
    let read := Expr.prodGet (.var savedLocal) selected.val
    restoreFrameBlock tail saved (restoreSlot read body)

/-- The generated G binders restore all typed locals from their canonical
    slots, with no extra reads or changes to the body outcome. -/
public theorem restoreFrameBlock_rep {locals : List (String × Ty)} (plan : RestorePlan types f locals)
    (saved : Var Γ (frameType types f)) (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (outer : Env D Γ) (frame : Frame (Value D)) (phase : Phase)
    (represented : FrameRep D types f phase frame (outer.get saved)) :
    ∀ (body : Block D V l (locals.map Prod.snd ++ Γ) Λ Λ) (scope : Env D (locals.map Prod.snd)),
      (∀ entry ∈ locals, entry.1 ∈ liveAt f phase) → localsEnv D locals frame = some scope →
      execBlock oracle passes calls (restoreFrameBlock plan saved body) world outer =
        removeLocals (locals.map Prod.snd) (execBlock oracle passes calls body world (appendLocals scope outer)) := by
  induction plan with
  | nil => intro _ _ _ initialized; obtain rfl := Option.some.inj initialized; rfl
  | @cons name sourceType rest found tail ih =>
    intro body scope live initialized
    let selected := frameSlot types name sourceType (f.params ++ f.fields) found
    have needed := live (name, types.ordinary sourceType) List.mem_cons_self
    obtain ⟨value, ordinary, looked, typed, present⟩ := selected.property.read_live needed represented.slots
    cases restored : localsEnv D rest frame with
    | none =>
      simp only [localsEnv, looked, typed, restored, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at initialized
      cases initialized
    | some restScope =>
      simp only [localsEnv, looked, typed, restored, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def] at initialized
      obtain rfl := Option.some.inj initialized
      let savedLocal := prependLocal saved (rest.map Prod.snd)
      let read : Expr D (rest.map Prod.snd ++ Γ) Λ (.sum [none, some (types.ordinary sourceType)]) :=
        Expr.prodGet (.var savedLocal) selected.val
      have readLocal : read.orte = [] := rfl
      have ok : eval world read world (appendLocals restScope outer) =
          presentValue D (types.ordinary sourceType) ordinary := by
        change prodGetW selected.val ((appendLocals restScope outer).get savedLocal) = _
        rw [get_prependLocal saved outer restScope]
        exact present
      have noRead : world.lese Λ [] = world := rfl
      have step := restoreSlot_present oracle passes calls read body world (appendLocals restScope outer) ordinary
        (by simpa only [readLocal, noRead] using ok)
      simp only [readLocal, noRead] at step
      change execBlock oracle passes calls (restoreFrameBlock tail saved (restoreSlot read body)) world outer = _
      rw [ih _ restScope (fun item member => live item (List.mem_cons_of_mem _ member)) restored, step]
      rfl

end Gabbro.Grammatik.Async.Representation
