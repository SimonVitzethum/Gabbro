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
    (ca : Option Ty) (nutz : Nutzlast D.Fn D.passt ca) : Holds A fr s0 (armBind c ca) σ (armEnv nutz ρ) := by
  match ca, nutz with
  | none, _ => exact h
  | some _, v => exact h.bindNone v

theorem BPost.schrumpfArm {k c1 : Context} {l : Bool} {Γ : Ctx} (hk : k.references.length ≤ Γ.length)
    (ca : Option Ty) (o : Ausgang V l (ArmCtx Γ ca)) (h : BPost A fr s0 out k c1 o) :
    BPost A fr s0 out k (armDrop c1 ca) (o.schrumpfArm ca) := by
  match ca, o, h with
  | none, o, h => exact h
  | some _, o, h => exact BPost.schrumpf hk o h

theorem armCtx_length (Γ : Ctx) : ∀ ca : Option Ty, Γ.length ≤ (ArmCtx Γ ca).length
  | none => Nat.le_refl _
  | some _ => Nat.le_succ _

theorem axiomAntwort_fst (O : Orakel D) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    (axiomAntwort O a σ ρ).1 = (O.wirkt a (σ.fragt (.inl a)) ρ).1 := by rfl

end Arms

section Sound

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}
  {O : Orakel D} {passes : Nat} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
  {fr : Frame} {s0 : State}

/-- Completed returns retain their certificate; only continuing outcomes map metadata. -/
theorem BPost.mapContinuing {k c' : Context} {l : Bool} {Γ : Ctx}
    (o : Ausgang V l Γ) (F : World D → World D) (hF : ∀ σ, MetaSame A σ (F σ))
    (h : BPost A fr s0 out k c' o) :
    BPost A fr s0 out k c' (match o with
      | .zurueck σ value => .zurueck σ value
      | .why σ reason => .why σ reason
      | outcome => outcome.mapWelt F) := by
  have mapped := BPost.mapMeta o F hF h
  cases o with
  | zurueck _ _ => exact h
  | why _ _ => exact h
  | _ => exact mapped

end Sound
end Gabbro.Grammatik.ArenaOwnership.Body
