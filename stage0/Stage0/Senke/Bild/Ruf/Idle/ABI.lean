module

public import Stage0.Senke.Bild.Ruf.Idle.CallOperands
public import Stage0.Senke.Tore.Code

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

/-- The idle extension shifts function type numbers while keeping physical layout. -/
def FrameLayout.withIdle (layout : FrameLayout) : FrameLayout :=
  { layout with params := layout.params.map tyR, result := layout.result.map tyR }

theorem FrameLayout.internalResult_withIdle (layout : FrameLayout) :
    layout.withIdle.internalResult = layout.internalResult := by
  simp only [FrameLayout.internalResult, FrameLayout.ensParams, FrameLayout.ensReserved,
    FrameLayout.parameterWords, FrameLayout.withIdle, tyR, contextWords_mapNumbers]

private theorem FrameLayout.result_withIdle (layout : FrameLayout) :
    layout.withIdle.result = layout.result.map tyR := rfl

private theorem FrameLayout.canonicalResult_withIdle (layout : FrameLayout) :
    layout.withIdle.canonicalResult = layout.canonicalResult := by
  simp only [FrameLayout.canonicalResult, FrameLayout.parameterWords, FrameLayout.withIdle,
    tyR, contextWords_mapNumbers]

private theorem FrameLayout.returnSpan_withIdle (layout : FrameLayout) :
    layout.withIdle.returnSpan = layout.returnSpan := by
  simp only [FrameLayout.returnSpan, FrameLayout.withIdle, tyR, returnWords_mapNumbers]

theorem retTop_withIdle (layout : FrameLayout) : retTop layout.withIdle = retTop layout := by
  simp only [retTop, FrameLayout.internalStatus, FrameLayout.internalResult_withIdle,
    FrameLayout.returnSpan_withIdle]

private theorem resultWords_tyR (result : Option Ty) : resultWords (result.map tyR) = resultWords result := by
  cases result <;> simp only [Option.map_none, Option.map_some, resultWords, tyR, valueWords_mapNumbers]

private theorem publishC_withIdle (layout : FrameLayout) : publishC layout.withIdle = publishC layout := by
  simp only [publishC, FrameLayout.canonicalStatus, FrameLayout.canonicalResult_withIdle,
    FrameLayout.internalResult_withIdle, FrameLayout.returnSpan_withIdle, FrameLayout.result_withIdle,
    resultWords_tyR]

theorem retC_withIdle (layout : FrameLayout) (source : Nat) (ensures : List II) :
    retC layout.withIdle source ensures = retC layout source ensures := by
  simp only [retC, FrameLayout.internalResult_withIdle, publishC_withIdle, FrameLayout.result_withIdle, resultWords_tyR]

theorem retWhyC_withIdle (layout : FrameLayout) (reason : Nat) :
    retWhyC layout.withIdle reason = retWhyC layout reason := by
  simp only [retWhyC, FrameLayout.canonicalStatus, FrameLayout.canonicalResult, FrameLayout.parameterWords,
    FrameLayout.returnSpan, FrameLayout.withIdle, tyR, contextWords_mapNumbers, returnWords_mapNumbers]

theorem gibTs_withIdle (L : Lay D) (scratch : Nat) (locks : List D.Lock) :
    gibTs L.withIdle scratch locks = gibTs L scratch locks := by
  induction locks with
  | nil => rfl
  | cons lock rest ih =>
    have release : gibT L.withIdle (L.withIdle.lk lock) scratch = gibT L (L.lk lock) scratch := rfl
    simp only [gibTs, release, ih]

theorem retScopedC_withIdle (L : Lay D) (layout : FrameLayout) (source : Nat)
    (ensures : List II) (locks : List D.Lock) :
    retScopedC L.withIdle layout.withIdle source ensures locks = retScopedC L layout source ensures locks := by
  simp only [retScopedC, FrameLayout.internalResult_withIdle, retTop_withIdle, gibTs_withIdle,
    publishC_withIdle, FrameLayout.result_withIdle, resultWords_tyR]

theorem retWhyScopedC_withIdle (L : Lay D) (layout : FrameLayout) (reason : Nat) (locks : List D.Lock) :
    retWhyScopedC L.withIdle layout.withIdle reason locks = retWhyScopedC L layout reason locks := by
  simp only [retWhyScopedC, retTop_withIdle, gibTs_withIdle, retWhyC_withIdle]

theorem callC_withIdle (A : D.Fn → Nat) (idleAddress : Nat) (f : D.Fn) (frame : Nat) (args : List II) :
    callC (D := D.mitRuhe) (fun g => g.elim idleAddress A) (some f) frame args =
      callC A f frame args := by
  simp only [callC, callTail_withIdle]

theorem receiveC_withIdle (signature : Signatur D.Tab D.Glob D.Lock D.Marke) (frame : Nat) :
    receiveC (D := D.mitRuhe) (sigR signature) frame = receiveC (D := D) signature frame := by
  simp only [receiveC, sigR, tyR, contextWords_mapNumbers, returnWords_mapNumbers]

theorem receiveTop_withIdle (signature : Signatur D.Tab D.Glob D.Lock D.Marke) (frame : Nat) :
    receiveTop (D := D.mitRuhe) (sigR signature) frame = receiveTop (D := D) signature frame := by
  simp only [receiveTop, sigR, tyR, contextWords_mapNumbers, returnWords_mapNumbers]

theorem elseC_withIdle (signature : Signatur D.Tab D.Glob D.Lock D.Marke) (frame : Nat)
    (call success failure : List II) :
    elseC (D := D.mitRuhe) (sigR signature) frame call success failure =
      elseC (D := D) signature frame call success failure := by
  unfold elseC
  rw [receiveC_withIdle (D := D)]
  simp only [sigR, tyR, contextWords_mapNumbers, returnWords_mapNumbers]

theorem elseTop_withIdle (f : D.Fn) (frame args success failure : Nat) :
    elseTop (D := D.mitRuhe) (some f) frame args success failure =
      elseTop f frame args success failure := by
  have parameters : contextWords (D.mitRuhe.params (some f)) = contextWords (D.params f) :=
    contextWords_mapNumbers (· + 1) id _
  have result : returnWords (D.mitRuhe.erg (some f)) (D.mitRuhe.gruende (some f)) =
      returnWords (D.erg f) (D.gruende f) := returnWords_mapNumbers (· + 1) id _ _
  simp only [elseTop, callTop_withIdle, parameters, result]

theorem elseTopInd_withIdle (index frame args success failure : Nat) :
    elseTopInd (D := D.mitRuhe) (index + 1) frame args success failure =
      elseTopInd (D := D) index frame args success failure := by
  simp only [elseTopInd, sigNrM, sigR, tyR, contextWords_mapNumbers, returnWords_mapNumbers]

theorem isPtr_tyR (type : Ty) : isPtr (tyR type) = isPtr type := by
  cases type <;> rfl

theorem wortTy_tyR (type : Ty) : wortTy (tyR type) = wortTy type := by
  cases type <;> rfl

theorem lowR_withIdle (L : Lay D) (reserved : Nat) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {types : List Ty} (args : Args D Γ Λ types) (dest : Nat),
      lowR L.withIdle (ruA args) dest reserved = lowR L args dest reserved
  | _, _, _, .nil, _ => rfl
  | _, _, _, @Args.cons _ _ _ type rest head tail, dest => by
    have next := lowR_withIdle L reserved tail (dest + 1)
    have first := lowE_withIdle L reserved true head dest
    simp only [ruA, lowR, isPtr_tyR, wortTy_tyR, first, next]
termination_by structural _ _ _ args _ => args

theorem areaC_withIdle (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) (result : Ty) (dest reserved : Nat) :
    areaC L.withIdle a (ruA args) (tyR result) dest reserved = areaC L a args result dest reserved := by
  have binding : L.withIdle.tor a = L.tor a := rfl
  have width : (D.mitRuhe.aparams a).length = (D.aparams a).length := List.length_map tyR
  have types : (D.mitRuhe.aparams a).all (fun ty => wortTy ty && !isPtr ty) =
      (D.aparams a).all (fun ty => wortTy ty && !isPtr ty) := by
    change ((D.aparams a).map tyR).all _ = _
    simp only [List.all_map, Function.comp_def, wortTy_tyR, isPtr_tyR]
  have resultWidth : valueWords (tyR result) = valueWords result := valueWords_mapNumbers (· + 1) id _
  simp only [areaC, binding, width, types, lowR_withIdle, resultWidth]

end Gabbro.Stage0.Senke
