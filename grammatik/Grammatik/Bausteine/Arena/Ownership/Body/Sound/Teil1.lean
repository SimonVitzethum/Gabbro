module

public import Grammatik.Bausteine.Arena.Ownership.Body.Forms

@[expose] public section



/-! **Soundness of the general ownership body judgment.** For every
derivation, every world and environment in which the invariant holds, the
actual G outcome of the statement, block, end block or case arms keeps its
promise. The call handler `R` is arbitrary up to `Respects` for the
interface contracts; foreign bodies are framed by the existing hardware
assumption `GutO`. One induction over the derivation. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

theorem dropContext_isOwner {A : FreiForm D} (c : Context) {erg : Option Ty} (out : Flow.Output A erg) :
    dropContext c out = dropContextB c (Flow.Output.isOwner out) := by
  cases out <;> rfl

section Arms

variable {A : FreiForm D} {fr : Frame} {s0 : State} {V : Vertrag D} {out : Flow.Output A V.erg}

theorem Holds.arm {c : Context} {σ : World D} {Γ : Ctx} {ρ : Env D Γ} (h : Holds A fr s0 c σ ρ)
    (ca : Option (Int × Int)) (nutz : Nutzlast ca) : Holds A fr s0 (armBind c ca) σ (armEnv nutz ρ) := by
  match ca, nutz with
  | none, _ => exact h
  | some (_, _), v => exact h.bindNone (τ := .int _ _) v

theorem BPost.schrumpfArm {k c1 : Context} {l : Bool} {Γ : Ctx} (hk : k.references.length ≤ Γ.length)
    (ca : Option (Int × Int)) (o : Ausgang V l (ArmCtx Γ ca)) (h : BPost A fr s0 out k c1 o) :
    BPost A fr s0 out k (armDrop c1 ca) (o.schrumpfArm ca) := by
  match ca, o, h with
  | none, o, h => exact h
  | some (_, _), o, h => exact BPost.schrumpf hk o h

theorem armCtx_length (Γ : Ctx) : ∀ ca : Option (Int × Int), Γ.length ≤ (ArmCtx Γ ca).length
  | none => Nat.le_refl _
  | some (_, _) => Nat.le_succ _

theorem axiomAntwort_fst (O : Orakel D) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    (axiomAntwort O a σ ρ).1 = (O.wirkt a (σ.fragt (.inl a)) ρ).1 := by rfl

end Arms

section Sound

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}
  {O : Orakel D} {passes : Nat} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
  {fr : Frame} {s0 : State}

end Sound
end Gabbro.Grammatik.ArenaOwnership.Body
