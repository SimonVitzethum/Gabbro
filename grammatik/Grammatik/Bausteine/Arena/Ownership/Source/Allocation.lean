import Grammatik.Bausteine.Arena.Ownership.Source.Bindings

namespace Gabbro.Grammatik.ArenaOwnership.Source

variable {D : Deklaration}

def Ghost.set (g : Ghost) (i : Nat) (h : Handle) : Ghost := fun j => if j = i then some h else g j

@[simp] theorem Ghost.set_at (g : Ghost) (i : Nat) (h : Handle) : (g.set i h) i = some h := by simp [Ghost.set]
@[simp] theorem Ghost.set_other (g : Ghost) (i j : Nat) (h : Handle) (hne : j ≠ i) :
    (g.set i h) j = g j := by simp [Ghost.set, hne]

theorem Context.bindFresh_bounded {c : Context} (hb : c.bounded) : c.bindFresh.bounded := by
  constructor
  · intro i hi
    change c.next + 1 ≤ i at hi
    have hne : i ≠ c.next := by omega
    simp only [Context.bindFresh, ite_eq_right hne]
    exact hb.1 i (by omega)
  · intro ref hm i he
    rcases List.mem_append.mp hm with hm | hm
    · have hlt := hb.2 ref hm i he
      exact Nat.lt_succ_of_lt hlt
    · have href : ref = some c.next := by simpa using hm
      have hi : i = c.next := (Option.some.inj (href.symm.trans he)).symm
      subst i
      exact Nat.lt_succ_self _

theorem Rights.handle {c : Context} {g : Ghost} {s : State} {frame : Frame}
    (hr : Rights c g s frame) {i : Nat} {mode : PassingMode} {h : Handle}
    (hi : c.rights i = some mode) (hg : g i = some h) : mode.permits s frame h := by
  obtain ⟨k, hk, hp⟩ := hr.1 i mode hi
  rw [hg] at hk
  cases hk
  exact hp

theorem allocation_disjoint {A : FreiForm D} {c : Context} {g : Ghost} {s s' : State} {frame : Frame}
    {σ : World D} (ha : s.agrees A σ) (hr : Rights c g s frame)
    {slot : Int} {fresh : Handle} (hs : s.allocate frame slot = some (s', fresh))
    {i : Nat} {mode : PassingMode} {old : Handle} (hi : c.rights i = some mode) (hg : g i = some old) :
    old.slot ≠ slot := by
  have hp := PassingMode.access_of_permits (Rights.handle hr hi hg)
  have hl := State.access_live ha hp
  obtain ⟨cell, hc⟩ := (ha.2 old.slot).mp hl
  intro he
  rw [he, State.allocate_empty hs] at hc
  cases hc

/-- A new source origin receives a grant only when it is separated from
all active origins. This is shared by allocations and owning call results. -/
theorem extend_rights {c : Context} {g : Ghost} {s : State} {frame : Frame} {fresh : Handle}
    (hr : Rights c g s frame) (ho : s.owns frame fresh)
    (hdisjoint : ∀ i mode old, c.rights i = some mode → g i = some old → old.slot ≠ fresh.slot) :
    Rights c.bindFresh (g.set c.next fresh) s frame := by
  constructor
  · intro i mode hi
    by_cases hnew : i = c.next
    · subst i
      have hmode : mode = .owned := by simpa [Context.bindFresh] using hi.symm
      subst mode
      exact ⟨fresh, Ghost.set_at g c.next fresh, ho⟩
    · have hold : c.rights i = some mode := by simpa [Context.bindFresh, hnew] using hi
      obtain ⟨h, hg, hp⟩ := hr.1 i mode hold
      exact ⟨h, by simpa [Ghost.set, hnew] using hg, hp⟩
  · intro i j p q hi hj hne hown h k hgi hgj
    by_cases hinew : i = c.next
    · subst i
      have hjold : j ≠ c.next := Ne.symm hne
      have hhk : h = fresh := by simpa [Ghost.set] using hgi.symm
      subst h
      have hold : c.rights j = some q := by simpa [Context.bindFresh, hjold] using hj
      have hgk : g j = some k := by simpa [Ghost.set, hjold] using hgj
      exact Ne.symm (hdisjoint j q k hold hgk)
    · by_cases hjnew : j = c.next
      · subst j
        have hkk : k = fresh := by simpa [Ghost.set] using hgj.symm
        subst k
        have hold : c.rights i = some p := by simpa [Context.bindFresh, hinew] using hi
        have hgh : g i = some h := by simpa [Ghost.set, hinew] using hgi
        exact hdisjoint i p h hold hgh
      · apply hr.2 i j p q (by simpa [Context.bindFresh, hinew] using hi)
          (by simpa [Context.bindFresh, hjnew] using hj) hne hown h k
        · simpa [Ghost.set, hinew] using hgi
        · simpa [Ghost.set, hjnew] using hgj

theorem allocation_rights {A : FreiForm D} {c : Context} {g : Ghost} {s s' : State} {frame : Frame}
    {σ : World D} (ha : s.agrees A σ) (hr : Rights c g s frame)
    {slot : Int} {fresh : Handle} (hs : s.allocate frame slot = some (s', fresh)) (hslot : fresh.slot = slot) :
    Rights c.bindFresh (g.set c.next fresh) s' frame := by
  have hrights : Rights c g s' frame := by
    refine ⟨?_, hr.2⟩
    intro i mode hi
    obtain ⟨h, hg, hp⟩ := hr.1 i mode hi
    exact ⟨h, hg, PassingMode.permits_same_cell
      (State.allocate_other hs h.slot (allocation_disjoint ha hr hs hi hg)) hp⟩
  apply extend_rights hrights (State.allocate_valid ha.1 frame slot hs).2
  intro i mode old hi hg
  exact hslot ▸ allocation_disjoint ha hr hs hi hg

theorem References.setFresh {c : Context} {g : Ghost} {Γ : Ctx} {ρ : Env D Γ}
    (hb : c.bounded) (href : References c g ρ) (fresh : Handle) :
    References c (g.set c.next fresh) ρ := by
  refine ⟨href.1, ?_⟩
  intro τ x i hi
  obtain ⟨h, hg, hv⟩ := href.2 x i hi
  have hlt := hb.2 (some i) (Context.reference_member x i hi) i rfl
  exact ⟨h, by simpa [Ghost.set, Nat.ne_of_lt hlt] using hg, hv⟩

/-- Shared binder rule for freshly allocated and returned owning grants. -/
theorem owning_context (A : FreiForm D) (c : Context) (g : Ghost) (frame : Frame)
    {Γ : Ctx} (s' : State) (σ' : World D) (ρ : Env D Γ)
    (k : Wert D (Ty.index (D.count A.tab))) (fresh : Handle)
    (hb : c.bounded) (href : References c g ρ) (ha' : s'.agrees A σ') (hf' : A.FreiOk σ')
    (hr : Rights c.bindFresh (g.set c.next fresh) s' frame) (hslot : fresh.slot = k.n) :
    Realizes c.bindFresh (g.set c.next fresh) A frame s' σ' (.cons k ρ) := by
  refine ⟨ha', hf', Context.bindFresh_bounded hb, ?_, hr⟩
  have href' := References.setFresh hb href fresh
  change References (c.bind (some c.next)) (g.set c.next fresh) (.cons k ρ)
  apply References.bind href' k (some c.next)
  intro i hi
  cases hi
  exact ⟨fresh, Ghost.set_at g c.next fresh, by simpa [intVon] using congrArg some hslot.symm⟩

/-- Both actual G allocation paths use this same source-context update.
Old aliases retain their old origin; only the new binder receives the new
grant, even when the allocator reused the same numeric storage slot. -/
theorem allocation_context (A : FreiForm D) (c : Context) (g : Ghost) (frame : Frame)
    {Γ : Ctx} (s s' : State) (σ σ' : World D) (ρ : Env D Γ)
    (k : Wert D (Ty.index (D.count A.tab))) (fresh : Handle)
    (hc : Realizes c g A frame s σ ρ) (ha' : s'.agrees A σ') (hf' : A.FreiOk σ')
    (hs : s.allocate frame k.n = some (s', fresh)) (hslot : fresh.slot = k.n) :
    Realizes c.bindFresh (g.set c.next fresh) A frame s' σ' (.cons k ρ) := by
  obtain ⟨ha, _, hb, href, hr⟩ := hc
  exact owning_context A c g frame s' σ' ρ k fresh hb href ha' hf' (allocation_rights ha hr hs hslot) hslot


#print axioms allocation_context

end Gabbro.Grammatik.ArenaOwnership.Source
