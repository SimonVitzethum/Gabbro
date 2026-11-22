module

public import Stage0.Senke.Bild.Ruf.Idle.Expression
public import Stage0.Senke.Anweisung.Faelle.Hilfen

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

/-- Canonical argument evaluation remains right-to-left, and each
    argument keeps exactly its production frame address. -/
theorem lowA_withIdle (L : Lay D) (reserved : Nat) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {types : List Ty} (args : Args D Γ Λ types) (dest : Nat),
      lowA L.withIdle (ruA args) dest reserved = lowA L args dest reserved
  | _, _, _, .nil, _ => rfl
  | _, _, _, @Args.cons _ _ _ τ tail head rest, dest => by
    have arguments := lowA_withIdle L reserved rest dest
    have headCode := lowE_withIdle L reserved true head (dest + contextWords tail)
    simp only [ruA, lowA, tyR, contextWords_mapNumbers, arguments, headCode]
termination_by structural _ _ _ args _ => args

theorem lowErg_withIdle (L : Lay D) (reserved : Nat) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {result : Option Ty} (ret : ErgExpr D Γ Λ result) (dest : Nat),
      lowErg L.withIdle (ruErg ret) dest reserved = lowErg L ret dest reserved
  | _, _, _, .empty, _ => rfl
  | _, _, _, .val value, dest => by
    have mapped := lowE_withIdle L reserved true value dest
    simp only [ruErg, lowErg, Option.map_some, tyR, valueWords_mapNumbers, mapped]

theorem callTail_withIdle (A : D.Fn → Nat) (idleAddress : Nat) (f : D.Fn) (offset : Nat) (indirect : Bool) :
    callTail (D := D.mitRuhe) (fun g => g.elim idleAddress A) (some f) offset indirect =
      callTail A f offset indirect := by
  have width : contextWords (D.mitRuhe.params (some f)) = contextWords (D.params f) :=
    contextWords_mapNumbers (· + 1) id _
  simp only [callTail, width, Option.elim]

theorem callTop_withIdle (f : D.Fn) (offset top : Nat) :
    callTop (D := D.mitRuhe) (some f) offset top = callTop (D := D) f offset top := by
  have width : contextWords (D.mitRuhe.params (some f)) = contextWords (D.params f) :=
    contextWords_mapNumbers (· + 1) id _
  simp only [callTop, width]

theorem lowInd_withIdle (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    (ptr : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params) (reserved : Nat) :
    lowInd L.withIdle (n := n + 1) (ruE ptr) (ruA args) reserved = lowInd L ptr args reserved := by
  have pointerCode := lowE_withIdle L reserved true ptr (frei Γ reserved)
  have arguments := lowA_withIdle L reserved args (frei Γ reserved + FB)
  simp only [tyR, Ty.mapNumbers] at pointerCode arguments
  simp only [lowInd, sigNrM, sigR, frei_withIdle, indC, indTop, tyR, Ty.mapNumbers,
    contextWords_mapNumbers, pointerCode, arguments]

theorem lowIndElse_withIdle (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    (ptr : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params) (reserved : Nat) :
    lowIndElse L.withIdle (n := n + 1) (ruE ptr) (ruA args) reserved = lowIndElse L ptr args reserved := by
  have pointerCode := lowE_withIdle L reserved true ptr (frei Γ reserved)
  have arguments := lowA_withIdle L reserved args (frei Γ reserved + FB)
  simp only [tyR, Ty.mapNumbers] at pointerCode arguments
  simp only [lowIndElse, sigNrM, sigR, frei_withIdle, indC, indTop, tyR, Ty.mapNumbers,
    contextWords_mapNumbers, pointerCode, arguments]

end Gabbro.Stage0.Senke
