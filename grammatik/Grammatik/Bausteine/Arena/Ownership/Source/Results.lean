import Grammatik.Bausteine.Arena.Ownership.Source.Allocation
import Grammatik.Bausteine.Arena.Ownership.Source.Calls

namespace Gabbro.Grammatik.ArenaOwnership.Source

variable {D : Deklaration}

/-- A returned owning grant gets a new source origin. Older numeric aliases
remain associated with the consumed origin and cannot use the new grant. -/
theorem returned_context (A : FreiForm D) (c : Context) (g : Ghost) (frame : Frame)
    {Γ : Ctx} (s s' : State) (σ σ' : World D) (ρ : Env D Γ)
    (i : Nat) (h fresh : Handle) (k : Wert D (Ty.index (D.count A.tab)))
    (hc : Realizes c g A frame s σ ρ) (hi : c.rights i = some .owned) (hg : g i = some h)
    (ha' : s'.agrees A σ') (hf' : A.FreiOk σ')
    (heffect : s.returned s' frame h fresh) (hslot : fresh.slot = k.n) :
    Realizes (c.kill i).bindFresh (g.set c.next fresh) A frame s' σ' (.cons k ρ) := by
  obtain ⟨ha, hf, hb, href, hr⟩ := hc
  have hb' := Context.kill_bounded hb i
  have href' := Context.kill_references href i
  have hr' := rights_after_consumption hr hi hg heffect.2.2.2.1
  apply owning_context A (c.kill i) g frame s' σ' ρ k fresh hb' href' ha' hf' (hslot := hslot)
  apply extend_rights hr' heffect.1
  intro j mode old hj hgold
  have hne : j ≠ i := by intro he; simp [Context.kill, he] at hj
  have hjold : c.rights j = some mode := by simpa [Context.kill, hne] using hj
  have hdiff := hr.2 j i mode .owned hjold hi hne (Or.inr rfl) old h hgold hg
  exact heffect.2.1 ▸ hdiff

theorem checked_owning_result (A : FreiForm D) (C : ∀ f, Contract D f)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (hR : Respects A C R)
    (f : D.Fn) (x : Var (D.params f) (Ty.index (D.count A.tab)))
    (he : D.erg f = some (Ty.index (D.count A.tab))) (hC : C f = identityContract A f x he .owned)
    {Γ : Ctx} {Λ : List (Res D)} (args : Args D Γ Λ (D.params f))
    (c c' : Context) (g : Ghost) (caller callee : Frame) (s : State) (σ : World D) (ρ : Env D Γ)
    (i : Nat) (hc : consume c (argument args x) = some (c', i))
    (ht : caller.thread = callee.thread) (hgood : Realizes c g A caller s σ ρ)
    {σ' : World D} {v : ErgVal D (D.erg f)}
    (hrun : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = .ok σ' v) :
    ∃ s' h fresh, Realizes c'.bindFresh (g.set c.next fresh) A caller s' σ' (.cons (ergWert he v) ρ) ∧
      g i = some h ∧ (∀ frame, ¬ s'.access frame h) := by
  obtain ⟨hi, hright, hctx⟩ := consume_facts hc
  obtain ⟨h, hg, hown⟩ := hgood.2.2.2.2.1 i .owned hright
  obtain ⟨h', hg', hv⟩ := origin_sound c g ρ hgood.2.2.2.1 (argument args x) i hi
    (σ.lese Λ args.orte) (σ.lese Λ args.orte)
  rw [hg] at hg'
  cases hg'
  have hx : h.slot = ((evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ).get x).n := by
    rw [← eval_argument]
    exact (Option.some.inj hv).symm
  obtain ⟨s', fresh, ha', hf', heffect, hslot, hdead⟩ := identity_result A C R hR f x he hC caller callee ht s h
    _ _ (State.agrees_reads hgood.1 _ _) (free_invariant_reads hgood.2.1 _ _) hown hx hrun
  refine ⟨s', h, fresh, ?_, hg, hdead⟩
  rw [hctx]
  exact returned_context A c g caller s s' σ σ' ρ i h fresh (ergWert he v) hgood hright hg ha' hf' heffect hslot

#print axioms returned_context
#print axioms checked_owning_result

/-- A factory result is separated from every pre-existing source grant,
including a borrow. Its newly returned binder uses the common origin rule. -/
theorem checked_factory_result (A : FreiForm D) (C : ∀ f, Contract D f)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (hR : Respects A C R)
    (f : D.Fn) (he : D.erg f = some (Ty.index (D.count A.tab))) (hC : C f = factoryContract A f he)
    {Γ : Ctx} {Λ : List (Res D)} (args : Args D Γ Λ (D.params f))
    (c : Context) (g : Ghost) (caller callee : Frame) (s : State) (σ : World D) (ρ : Env D Γ)
    (ht : callee.thread = caller.thread) (hc : Realizes c g A caller s σ ρ)
    {σ' : World D} {v : ErgVal D (D.erg f)}
    (hrun : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = .ok σ' v) :
    ∃ s' fresh, Realizes c.bindFresh (g.set c.next fresh) A caller s' σ' (.cons (ergWert he v) ρ) := by
  obtain ⟨s', fresh, ha', hf', ho, hslot, _, hempty, hframe⟩ := factory_result A C R hR f he hC caller callee ht
    s _ _ (State.agrees_reads hc.1 _ _) (free_invariant_reads hc.2.1 _ _) hrun
  obtain ⟨ha, _, hb, href, hr⟩ := hc
  have hdisjoint : ∀ i mode old, c.rights i = some mode → g i = some old → old.slot ≠ fresh.slot := by
    intro i mode old hi hg
    have haccess := PassingMode.access_of_permits (Rights.handle hr hi hg)
    have hlive := State.access_live ha haccess
    obtain ⟨cell, hcell⟩ := (ha.2 old.slot).mp hlive
    intro heq
    rw [heq, hempty] at hcell
    cases hcell
  have hrights : Rights c g s' caller := by
    refine ⟨?_, hr.2⟩
    intro i mode hi
    obtain ⟨old, hg, hp⟩ := hr.1 i mode hi
    exact ⟨old, hg, PassingMode.permits_same_cell (hframe _ (hdisjoint i mode old hi hg)) hp⟩
  exact ⟨s', fresh, owning_context A c g caller s' σ' ρ (ergWert he v) fresh hb href ha' hf'
    (extend_rights hrights ho hdisjoint) hslot⟩

/-- Failure changes neither the source context nor any existing grant.
This covers arbitrary caller state, not only an empty-heap witness. -/
theorem checked_factory_reason (A : FreiForm D) (C : ∀ f, Contract D f)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (hR : Respects A C R)
    (f : D.Fn) (he : D.erg f = some (Ty.index (D.count A.tab))) (hC : C f = factoryContract A f he)
    {Γ : Ctx} {Λ : List (Res D)} (args : Args D Γ Λ (D.params f))
    (c : Context) (g : Ghost) (caller callee : Frame) (s : State) (σ : World D) (ρ : Env D Γ)
    (hc : Realizes c g A caller s σ ρ) {σ' : World D} {r : Fin (D.gruende f)}
    (hrun : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = .why σ' r) :
    Realizes c g A caller s σ' ρ := by
  have hpre : (C f).requires callee s (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) := by
    rw [hC]
    trivial
  have hout := (hR f callee s (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
    (State.agrees_reads hc.1 _ _) (free_invariant_reads hc.2.1 _ _) hpre).2 σ' r hrun
  rw [hC] at hout
  obtain ⟨s', ha', hf', hs⟩ := hout
  subst s'
  exact ⟨ha', hf', hc.2.2⟩

#print axioms checked_factory_result
#print axioms checked_factory_reason

end Gabbro.Grammatik.ArenaOwnership.Source
