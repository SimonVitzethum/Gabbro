import Grammatik.Bausteine.Arena.Ownership.Factory

/-! Ownership of a result is instantiated from the actual returned value,
not from its numeric type or from a promise of an unexecuted allocation. -/

namespace Gabbro.Grammatik.ArenaOwnership

variable {D : Deklaration}

theorem factory_result (A : FreiForm D) (C : ∀ f, Contract D f)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : Respects A C R) (f : D.Fn)
    (he : D.erg f = some (Ty.index (D.count A.tab))) (hC : C f = factoryContract A f he)
    (caller callee : Frame) (ht : callee.thread = caller.thread)
    (s : State) (σ : World D) (ρ : Env D (D.params f))
    (ha : s.agrees A σ) (hf : A.FreiOk σ)
    {σ' : World D} {v : ErgVal D (D.erg f)} (hrun : R f σ ρ = .ok σ' v) :
    ∃ (s' : State) (h : Handle), s'.agrees A σ' ∧ A.FreiOk σ' ∧ s'.owns caller h ∧
      h.slot = (ergWert he v).n ∧
      (∀ old, s.owns caller old → s'.owns caller old) := by
  have hpre : (C f).requires callee s ρ := by rw [hC]; trivial
  have hp := (hR f callee s σ ρ ha hf hpre).1 σ' v hrun
  rw [hC] at hp
  obtain ⟨allocated, haa, hfa, result, hslot, halloc⟩ := hp
  have hown := (State.allocate_valid ha.1 callee result.slot halloc).2
  obtain ⟨returned, handle, hmove⟩ := State.move_exists hown ht
  have hm := State.move_valid haa.1 callee caller result hmove
  refine ⟨returned, handle, State.move_agrees haa callee caller result handle hmove, hfa, hm.2.1,
    hm.2.2.2.1.trans hslot, ?_⟩
  intro old hold
  obtain ⟨c, hc⟩ := State.own_cell hold
  have hne : old.slot ≠ result.slot := by
    intro hs
    rw [hs, State.allocate_empty halloc] at hc
    cases hc
  apply State.owns_from_same_cell (s := s)
  · exact (State.move_other hmove old.slot hne).trans (State.allocate_other halloc old.slot hne)
  · exact hold

theorem identity_result (A : FreiForm D) (C : ∀ f, Contract D f)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : Respects A C R) (f : D.Fn)
    (x : Var (D.params f) (Ty.index (D.count A.tab)))
    (he : D.erg f = some (Ty.index (D.count A.tab))) (hC : C f = identityContract A f x he .owned)
    (caller callee : Frame) (ht : caller.thread = callee.thread)
    (s : State) (original : Handle) (σ : World D) (ρ : Env D (D.params f))
    (ha : s.agrees A σ) (hf : A.FreiOk σ) (ho : s.owns caller original)
    (hx : original.slot = (ρ.get x).n)
    {σ' : World D} {v : ErgVal D (D.erg f)} (hrun : R f σ ρ = .ok σ' v) :
    ∃ (s' : State) (h : Handle), s'.agrees A σ' ∧ A.FreiOk σ' ∧ s'.owns caller h ∧
      h.slot = (ergWert he v).n ∧ h.allocation = original.allocation ∧
      (∀ frame, ¬ s'.access frame original) := by
  obtain ⟨entered, incoming, henter⟩ := State.move_exists ho ht
  have hen := State.move_valid ha.1 caller callee original henter
  have hae := State.move_agrees ha caller callee original incoming henter
  have hpre : (C f).requires callee entered ρ := by
    rw [hC]
    exact ⟨incoming, hen.2.1, hen.2.2.2.1.trans hx⟩
  have hp := (hR f callee entered σ ρ hae hf hpre).1 σ' v hrun
  rw [hC] at hp
  obtain ⟨ended, hah, hfh, hsame, hvalue⟩ := hp
  subst ended
  obtain ⟨returned, outgoing, hreturn⟩ := State.move_exists hen.2.1 ht.symm
  have hret := State.move_valid hah.1 callee caller incoming hreturn
  refine ⟨returned, outgoing, State.move_agrees hah callee caller incoming outgoing hreturn, hfh, hret.2.1,
    hret.2.2.2.1.trans (hen.2.2.2.1.trans (hx.trans hvalue.symm)),
    hret.2.2.2.2.trans hen.2.2.2.2, ?_⟩
  apply State.move_excludes_older hreturn hen.2.2.2.1.symm
  have hc := State.own_clock ha.1 ho
  rw [State.move_next henter]
  omega

#print axioms factory_result
#print axioms identity_result

end Gabbro.Grammatik.ArenaOwnership
