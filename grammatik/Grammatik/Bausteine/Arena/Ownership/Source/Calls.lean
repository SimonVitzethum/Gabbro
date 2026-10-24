import Grammatik.Bausteine.Arena.Ownership.Source.Arguments
import Grammatik.Bausteine.Arena.Ownership.Boundary

namespace Gabbro.Grammatik.ArenaOwnership.Source

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- The caller context after a source consuming call is computed from the
actual argument expression. Every other source origin and cell is retained. -/
theorem checked_consuming_call (A : FreiForm D) (C : ∀ f, Contract D f)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : Respects A C R) (f : D.Fn)
    (x : Var (D.params f) (Ty.index (D.count A.tab))) (hC : C f = destructorContract A f x)
    (args : Args D Γ Λ (D.params f)) (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (c c' : Context) (g : Ghost) (caller callee : Frame) (s : State) (σ : World D) (ρ : Env D Γ)
    (i : Nat) (hc : consume c (argument args x) = some (c', i))
    (ht : caller.thread = callee.thread) (hgood : Realizes c g A caller s σ ρ)
    {σ' : World D} {ρ' : Env D Γ}
    (hrun : execStmt (l := l) O passes R (.call f args hp hr) σ ρ = .ok σ' ρ') :
    ∃ s' h, Realizes c' g A caller s' σ' ρ' ∧ g i = some h ∧
      (∀ frame, ¬ s'.access frame h) := by
  obtain ⟨hi, hright, hctx⟩ := consume_facts hc
  obtain ⟨ha, hf, hb, href, hrights⟩ := hgood
  obtain ⟨h, hg, hown⟩ := hrights.1 i .owned hright
  obtain ⟨h', hg', hvalue⟩ := origin_sound c g ρ href (argument args x) i hi
    (σ.lese Λ args.orte) (σ.lese Λ args.orte)
  rw [hg] at hg'
  cases hg'
  have hx : ((evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ).get x).n = h.slot := by
    rw [← eval_argument]
    exact Option.some.inj hvalue
  obtain ⟨s', ha', hf', hrho, hdead, hframe, _⟩ := consume_call_frame A C O passes R hR f x hC args hp hr
    caller callee s h σ ρ ha hf hown ht hx hrun
  subst ρ'
  refine ⟨s', h, ?_, hg, hdead⟩
  rw [hctx]
  exact ⟨ha', hf', Context.kill_bounded hb i, Context.kill_references href i,
    rights_after_consumption hrights hright hg hframe⟩

#print axioms checked_consuming_call

end Gabbro.Grammatik.ArenaOwnership.Source
