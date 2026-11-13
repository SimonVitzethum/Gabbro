module

public import Grammatik.Nebenlaeufigkeit.Async.Dispatch
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.Schritt.G1

namespace Gabbro.Grammatik.Async

variable {D : Deklaration}

/-- A payload binder lives only during an ordinary match arm. It is removed
    before the following segment, never retained in a future's storage. -/
@[expose] public def armContinuation {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (rest : Block D V l Γ Λ Λ')
    (tail : GRest D V l Γ Λ') : (c : Option Ty) → GRest D V l (ArmCtx Γ c) Λ
  | none => .dann rest tail
  | some _ => .schrumpf (.dann rest tail)

/-- The actual G successor, including the binder, continuation, thread trace
    and call log. The selected block is immutable code, not stored state. -/
@[expose] public def dispatchTarget (M : RufMaschineG D) (thread : Faden)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (rest : Block D (vertragVon D (M.faeden thread).kopf.f) l Γ Λ Λ')
    (tail : GRest D (vertragVon D (M.faeden thread).kopf.f) l Γ Λ')
    (environment : Env D Γ) (world : World D) (events : List (Ereignis D))
    (selected : Σ c : Option Ty,
      Block D (vertragVon D (M.faeden thread).kopf.f) l (ArmCtx Γ c) Λ Λ ×
        Nutzlast D.Fn D.passt c) : RufMaschineG D :=
  ⟨M.speicher,
    rufUpdateG M.faeden thread
      ⟨(M.faeden thread).stapel,
        ⟨(M.faeden thread).kopf.f, (M.faeden thread).kopf.rho,
          (M.faeden thread).kopf.s0,
          ⟨l, ArmCtx Γ selected.1, Λ, armEnv selected.2.2 environment,
            .dann selected.2.1 (armContinuation rest tail selected.1)⟩⟩,
        world.spur, (M.faeden thread).log⟩,
    M.lauf ++ rufEigenG thread events, M.start⟩

/-- Every generated dispatch is a step of the UNCHANGED machine G. This
    proves the control part of reification, not the implementations of the
    selected expression/child segments or their source correspondence. -/
public theorem dispatch_unfold (P : Programm D) (O : Orakel D) (passes : Nat)
    (M : RufMaschineG D) (thread : Faden)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (cases : List (Option Ty))
    (value : Expr D Γ Λ (.sum cases))
    (bodies : (i : Fin cases.length) →
      Block D (vertragVon D (M.faeden thread).kopf.f) l (ArmCtx Γ (cases.get i)) Λ Λ)
    (rest : Block D (vertragVon D (M.faeden thread).kopf.f) l Γ Λ Λ')
    (tail : GRest D (vertragVon D (M.faeden thread).kopf.f) l Γ Λ')
    (environment : Env D Γ)
    (head : (M.faeden thread).kopf.rest =
      ⟨l, Γ, Λ, environment, .dann (.cons (dispatch cases value bodies) rest) tail⟩)
    (world : World D) (read : world = (M.weltVon thread).lese Λ value.orte)
    (i : Fin cases.length) (payload : Nutzlast D.Fn D.passt (cases.get i))
    (evaluated : eval world value world environment =
      ⟨i, Fall.ofNutzlast D.Fn D.passt cases i payload⟩)
    (events : List (Ereignis D))
    (trace : world.spur = events ++ (M.faeden thread).spur)
    (held : HeldIn Λ (offen (M.faeden thread).spur)) :
    RufSchrittG1 P O passes M thread
      (dispatchTarget M thread l Γ Λ Λ' rest tail environment world events
        ⟨cases.get i, bodies i, payload⟩) := by
  have chosen : armWahlG (dispatchArms cases bodies)
      (eval world value world environment) = ⟨cases.get i, bodies i, payload⟩ := by
    rw [evaluated]
    exact dispatchArms_select cases bodies i payload
  have unfoldSelected
      (selected : Σ c : Option Ty,
        Block D (vertragVon D (M.faeden thread).kopf.f) l (ArmCtx Γ c) Λ Λ ×
          Nutzlast D.Fn D.passt c)
      (selection : armWahlG (dispatchArms cases bodies)
        (eval world value world environment) = selected) :
      RufSchrittG1 P O passes M thread
        (dispatchTarget M thread l Γ Λ Λ' rest tail environment world events selected) := by
    rcases selected with ⟨c, body, saved⟩
    cases c with
    | none =>
      exact RufSchrittG1.dannOnTagNone M thread l Γ Λ Λ Λ' cases value
        (dispatchArms cases bodies) rest tail environment head world read
        body saved selection events trace held
    | some type =>
      exact RufSchrittG1.dannOnTagSome M thread l Γ Λ Λ Λ' cases value
        (dispatchArms cases bodies) rest tail environment head world read
        type body saved selection events trace held
  exact unfoldSelected _ chosen

end Gabbro.Grammatik.Async
