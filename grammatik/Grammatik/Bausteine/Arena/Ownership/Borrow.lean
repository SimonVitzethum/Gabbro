import Grammatik.Bausteine.Arena.Ownership.Return

/-! A call-scoped loan is different from a consuming argument: it restores
the lender's original grant and never gives the callee a release permission. -/

namespace Gabbro.Grammatik.ArenaOwnership

variable {D : Deklaration}

theorem borrow_result (A : FreiForm D) (C : ∀ f, Contract D f)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : Respects A C R) (f : D.Fn)
    (x : Var (D.params f) (Ty.index (D.count A.tab)))
    (he : D.erg f = some (Ty.index (D.count A.tab))) (hC : C f = identityContract A f x he .borrowed)
    (caller callee : Frame) (s loaned : State) (h : Handle)
    (σ : World D) (ρ : Env D (D.params f)) (ha : s.agrees A σ) (hf : A.FreiOk σ)
    (hlend : s.lend caller callee h = some loaned) (hx : h.slot = (ρ.get x).n)
    {σ' : World D} {v : ErgVal D (D.erg f)} (hrun : R f σ ρ = .ok σ' v) :
    s.agrees A σ' ∧ A.FreiOk σ' ∧ (ergWert he v).n = h.slot ∧
      loaned.endLoan callee h = some s ∧ loaned.release callee h = none := by
  have hl := State.lend_valid ha.1 caller callee h hlend
  have hal := State.lend_agrees ha caller callee h hlend
  have hpre : (C f).requires callee loaned ρ := by
    rw [hC]
    exact ⟨h, hl.2.1, hx⟩
  have hp := (hR f callee loaned σ ρ hal hf hpre).1 σ' v hrun
  rw [hC] at hp
  obtain ⟨ended, hae, hfe, hvalue, hsame⟩ := hp
  subst ended
  have hreturn := State.lend_endLoan caller callee h hlend
  refine ⟨State.endLoan_agrees hae callee h hreturn, hfe, hvalue.trans hx.symm, hreturn, ?_⟩
  simp only [State.release, hl.2.2.1, ↓reduceIte]

#print axioms borrow_result

end Gabbro.Grammatik.ArenaOwnership
