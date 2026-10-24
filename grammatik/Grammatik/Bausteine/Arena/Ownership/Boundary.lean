import Grammatik.Bausteine.Arena.Ownership.Bodies

/-! Argument-dependent ownership transfer at actual G calls. The runtime
argument is the existing index value; the owning grant is ghost state. -/

namespace Gabbro.Grammatik.ArenaOwnership

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- A consuming call to a checked destructor destroys precisely the handed
allocation. Every saved caller alias is unusable afterwards. -/
theorem consume_call_frame (A : FreiForm D) (C : ∀ f, Contract D f)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : Respects A C R) (f : D.Fn)
    (x : Var (D.params f) (Ty.index (D.count A.tab)))
    (hC : C f = destructorContract A f x)
    (args : Args D Γ Λ (D.params f)) (hp : RufPasst D V (D.signatur f) Λ)
    (hr : D.gruende f = 0) (caller callee : Frame) (s : State) (h : Handle)
    (σ : World D) (ρ : Env D Γ) (ha : s.agrees A σ) (hf : A.FreiOk σ)
    (ho : s.owns caller h) (ht : caller.thread = callee.thread)
    (hx : ((evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ).get x).n = h.slot)
    {σ' : World D} {ρ' : Env D Γ}
    (he : execStmt (l := l) O passes R (Stmt.call f args hp hr) σ ρ = .ok σ' ρ') :
    ∃ s' : State, s'.agrees A σ' ∧ A.FreiOk σ' ∧ ρ' = ρ ∧ (∀ frame, ¬ s'.access frame h) ∧
      (∀ j, j ≠ h.slot → s'.cells j = s.cells j) := by
  obtain ⟨si, hi, hm⟩ := State.move_exists ho ht
  have hmprops := State.move_valid ha.1 caller callee h hm
  have hsi := State.move_agrees (State.agrees_reads ha Λ args.orte) caller callee h hi hm
  have hpre : (C f).requires callee si
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) := by
    rw [hC]
    exact ⟨hi, hmprops.2.1, hmprops.2.2.2.1.trans hx.symm⟩
  have hpost := hR f callee si (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hsi (free_invariant_reads hf Λ args.orte) hpre
  change (match R f (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
    | .ok sw _ => Ausgang.ok (V := V) (l := l) sw ρ
    | .why _ r => keinGrund hr r
    | .logik e => Ausgang.logik e
    | .hardware e => Ausgang.hardware e) = .ok σ' ρ' at he
  cases hcall : R f (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok sw v =>
    rw [hcall] at he
    cases he
    have hpst := hpost.1 σ' v hcall
    rw [hC] at hpst
    obtain ⟨so, hso, hfree, released, hown, hslot, hrelease⟩ := hpst
    have hsame : released = hi := State.own_handles_equal hown hmprops.2.1
      (hslot.trans (hmprops.2.2.2.1.trans hx.symm).symm)
    subst released
    refine ⟨so, hso, hfree, rfl, State.release_excludes_slot hrelease hmprops.2.2.2.1.symm, ?_⟩
    intro j hj
    exact (State.release_other hrelease j (hmprops.2.2.2.1 ▸ hj)).trans (State.move_other hm j hj)
  | why sw r => exact (Fin.cast hr r).elim0
  | logik e => rw [hcall] at he; cases he
  | hardware e => rw [hcall] at he; cases he

theorem consume_call (A : FreiForm D) (C : ∀ f, Contract D f)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : Respects A C R) (f : D.Fn)
    (x : Var (D.params f) (Ty.index (D.count A.tab)))
    (hC : C f = destructorContract A f x)
    (args : Args D Γ Λ (D.params f)) (hp : RufPasst D V (D.signatur f) Λ)
    (hr : D.gruende f = 0) (caller callee : Frame) (s : State) (h : Handle)
    (σ : World D) (ρ : Env D Γ) (ha : s.agrees A σ) (hf : A.FreiOk σ)
    (ho : s.owns caller h) (ht : caller.thread = callee.thread)
    (hx : ((evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ).get x).n = h.slot)
    {σ' : World D} {ρ' : Env D Γ}
    (he : execStmt (l := l) O passes R (Stmt.call f args hp hr) σ ρ = .ok σ' ρ') :
    ∃ s' : State, s'.agrees A σ' ∧ A.FreiOk σ' ∧ ρ' = ρ ∧ (∀ frame, ¬ s'.access frame h) := by
  obtain ⟨s', ha', hf', hrho, hdead, _⟩ := consume_call_frame A C O passes R hR f x hC args hp hr
    caller callee s h σ ρ ha hf ho ht hx he
  exact ⟨s', ha', hf', hrho, hdead⟩

#print axioms consume_call_frame
#print axioms consume_call

end Gabbro.Grammatik.ArenaOwnership
