import Grammatik.Bausteine.Arena.Ownership.Body.Plan

/-! The whole call, on the ledger. From the caller's invariant and a fitting
plan: the callee's interface precondition holds at the handoff ledger of a
fresh activation; and from nothing but the callee's interface postcondition
the caller's invariant holds again after the return, with every consumed
origin dead and an owning result bound under a new origin. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

/-! ## 1. The handed handles -/

def movedHandles (g : Ghost) (ms : List (Option PassingMode)) (os : List (Option Nat)) : List Handle :=
  (List.range ms.length).filterMap fun u => match ms[u]?, os[u]? with
    | some (some .owned), some (some i) => g i
    | _, _ => none

def lentHandles (g : Ghost) (ms : List (Option PassingMode)) (os : List (Option Nat)) : List Handle :=
  (List.range ms.length).filterMap fun u => match ms[u]?, os[u]? with
    | some (some .borrowed), some (some i) => g i
    | _, _ => none

variable {g : Ghost} {ms : List (Option PassingMode)} {os : List (Option Nat)}

theorem mem_handles {m : PassingMode} {h : Handle}
    (hm : h ∈ (List.range ms.length).filterMap fun u => match ms[u]?, os[u]? with
      | some (some m'), some (some i) => if m' = m then g i else none
      | _, _ => none) :
    ∃ (u i : Nat), ms[u]? = some (some m) ∧ os[u]? = some (some i) ∧ g i = some h := by
  obtain ⟨u, _, hu⟩ := List.mem_filterMap.mp hm
  revert hu
  cases hmu : ms[u]? with
  | none => intro h; cases h
  | some mo =>
    cases mo with
    | none => intro h; cases h
    | some m' =>
      cases hou : os[u]? with
      | none => intro h; cases h
      | some o =>
        cases o with
        | none => intro h; cases h
        | some i =>
          intro hu
          by_cases he : m' = m
          · subst he; simp only [ite_true] at hu; exact ⟨u, i, hmu, hou, hu⟩
          · simp [he] at hu

theorem mem_moved {h : Handle} (hm : h ∈ movedHandles g ms os) :
    ∃ (u i : Nat), ms[u]? = some (some PassingMode.owned) ∧ os[u]? = some (some i) ∧ g i = some h := by
  apply mem_handles (m := .owned)
  obtain ⟨u, hu, he⟩ := List.mem_filterMap.mp hm
  refine List.mem_filterMap.mpr ⟨u, hu, ?_⟩
  revert he
  cases ms[u]? with
  | none => intro h; cases h
  | some mo => cases mo with
    | none => intro h; cases h
    | some m => cases os[u]? with
      | none => cases m <;> intro h <;> cases h
      | some o => cases o with
        | none => cases m <;> intro h <;> cases h
        | some i => cases m <;> simp

theorem mem_lent {h : Handle} (hm : h ∈ lentHandles g ms os) :
    ∃ (u i : Nat), ms[u]? = some (some PassingMode.borrowed) ∧ os[u]? = some (some i) ∧ g i = some h := by
  apply mem_handles (m := .borrowed)
  obtain ⟨u, hu, he⟩ := List.mem_filterMap.mp hm
  refine List.mem_filterMap.mpr ⟨u, hu, ?_⟩
  revert he
  cases ms[u]? with
  | none => intro h; cases h
  | some mo => cases mo with
    | none => intro h; cases h
    | some m => cases os[u]? with
      | none => cases m <;> intro h <;> cases h
      | some o => cases o with
        | none => cases m <;> intro h <;> cases h
        | some i => cases m <;> simp

theorem moved_of {u i : Nat} {h : Handle} (hmu : ms[u]? = some (some .owned)) (hou : os[u]? = some (some i))
    (hg : g i = some h) : h ∈ movedHandles g ms os := by
  refine List.mem_filterMap.mpr ⟨u, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hmu).1, ?_⟩
  simp [hmu, hou, hg]

theorem lent_of {u i : Nat} {h : Handle} (hmu : ms[u]? = some (some .borrowed)) (hou : os[u]? = some (some i))
    (hg : g i = some h) : h ∈ lentHandles g ms os := by
  refine List.mem_filterMap.mpr ⟨u, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hmu).1, ?_⟩
  simp [hmu, hou, hg]

/-! ## 2. Handing over -/

/-- The callee's activation: fresh against every owner and loan in the ledger. -/
def calleeFrame (A : FreiForm D) (s : State) (fr : Frame) : Frame := s.freshFrame (D.count A.tab).toNat fr

/-- The callee's ghost: the moved grant for an owning parameter, the
caller's grant for a borrowed one. -/
def calleeGhost (g : Ghost) (ms : List (Option PassingMode)) (os : List (Option Nat)) (next : Nat) : Ghost :=
  fun u => match ms[u]?, os[u]? with
    | some (some .owned), some (some i) => (g i).map fun h => ⟨h.slot, h.allocation, next⟩
    | some (some .borrowed), some (some i) => g i
    | _, _ => none

variable {A : FreiForm D} {c : Context} {s : State} {fr : Frame} {σ : World D} {Γ : Ctx} {ρ : Env D Γ}

theorem rights_handle {c : Context} {g : Ghost} {s : State} {fr : Frame} (hr : Rights c g s fr) {i : Nat}
    (hi : (c.rights i).isSome) : ∃ m h, c.rights i = some m ∧ g i = some h ∧ m.permits s fr h := by
  cases hm : c.rights i with
  | none => rw [hm] at hi; cases hi
  | some m => obtain ⟨h, hg, hp⟩ := hr.1 i m hm; exact ⟨m, h, rfl, hg, hp⟩

theorem handoff_ok (hR : Realizes c g A fr s σ ρ) (hp : planFits c ms os = true) :
    HandoffOk s fr (calleeFrame A s fr) (movedHandles g ms os) (lentHandles g ms os) := by
  obtain ⟨ha, _, _, _, hr⟩ := hR
  refine ⟨ha.1, ?_, ?_, ?_, ?_⟩
  · intro h hm
    obtain ⟨u, i, hmu, hou, hg⟩ := mem_moved hm
    obtain ⟨i', hoi, _, hown⟩ := planFits_mode hp hmu
    rw [hou] at hoi; cases hoi
    exact Rights.handle hr (hown rfl) hg
  · intro h hm
    obtain ⟨u, i, hmu, hou, hg⟩ := mem_lent hm
    obtain ⟨i', hoi, hsome, _⟩ := planFits_mode hp hmu
    rw [hou] at hoi; cases hoi
    obtain ⟨m, k, hm', hgk, hpk⟩ := rights_handle hr hsome
    rw [hg] at hgk; cases hgk
    exact PassingMode.access_of_permits hpk
  · intro h hm k hk
    obtain ⟨u, i, hmu, hou, hg⟩ := mem_moved hm
    obtain ⟨v, j, hmv, hov, hgj⟩ := mem_lent hk
    obtain ⟨i', hoi, _, hown⟩ := planFits_mode hp hmu
    rw [hou] at hoi; cases hoi
    obtain ⟨j', hoj, hsome, _⟩ := planFits_mode hp hmv
    rw [hov] at hoj; cases hoj
    have hij : i ≠ j := by
      intro he; subst he
      have huv := planFits_owned_unique hp hmu hou hmv hov
      subst huv
      rw [hmu] at hmv; cases hmv
    obtain ⟨mj, kj, hmj, hgkj, _⟩ := rights_handle hr hsome
    rw [hgj] at hgkj; cases hgkj
    exact hr.2 i j .owned mj (hown rfl) hmj hij (Or.inl rfl) h k hg hgj
  · exact State.freshFrame_fresh ha fr

/-- **The callee's interface precondition holds at the handoff.** -/
theorem handoff_requires {Λ : List (Res D)} {params : Ctx} (modes : Modes params)
    (args : Args D Γ Λ params) (hms : modeList modes = ms) (hos : originList c args = os)
    (hR : Realizes c g A fr s σ ρ) (hp : planFits c ms os = true) (σa σb : World D) :
    References (Flow.parameterContext modes) (calleeGhost g ms os s.next) (evalArgs σa args σb ρ) ∧
      Rights (Flow.parameterContext modes) (calleeGhost g ms os s.next)
        (s.handoff (calleeFrame A s fr) (movedHandles g ms os) (lentHandles g ms os)) (calleeFrame A s fr) ∧
      Complete (Flow.parameterContext modes) (calleeGhost g ms os s.next)
        (s.handoff (calleeFrame A s fr) (movedHandles g ms os) (lentHandles g ms os)) (calleeFrame A s fr) := by
  have hok := handoff_ok (ms := ms) (os := os) hR hp
  obtain ⟨_, _, _, href, hr⟩ := hR
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · exact (Flow.parameterContext_length modes).1
  · intro τ x p hx
    rw [parameterContext_reference] at hx
    cases hmx : modeAt modes x with
    | none => rw [hmx] at hx; cases hx
    | some m =>
      rw [hmx] at hx
      cases hx
      have hmu : ms[x.unten]? = some (some m) := by rw [← hms, modeList_at, hmx]
      obtain ⟨i, hoi, hsome, _⟩ := planFits_mode hp hmu
      have horigin : origin c (argument args x) = some i := by
        have := originList_at c args x
        rw [hos, hoi] at this
        exact (Option.some.inj this).symm
      obtain ⟨h, hg, hv⟩ := origin_sound c g ρ href (argument args x) i horigin σa σb
      rw [eval_argument] at hv
      cases m with
      | owned => exact ⟨⟨h.slot, h.allocation, s.next⟩, by simp [calleeGhost, hmu, hoi, hg], hv⟩
      | borrowed => exact ⟨h, by simp [calleeGhost, hmu, hoi, hg], hv⟩
  · intro u m hu
    rw [parameterContext_rights, hms] at hu
    have hmu : ms[u]? = some (some m) := by
      cases hmu : ms[u]? with
      | none => simp [hmu] at hu
      | some mo => simp only [hmu, Option.getD_some] at hu; rw [hu]
    obtain ⟨i, hoi, hsome, hown⟩ := planFits_mode hp hmu
    obtain ⟨m', h, hm', hg, hperm⟩ := rights_handle hr hsome
    cases m with
    | owned =>
      refine ⟨⟨h.slot, h.allocation, s.next⟩, by simp [calleeGhost, hmu, hoi, hg], ?_⟩
      exact handoff_moved_owns hok (moved_of hmu hoi hg)
    | borrowed =>
      exact ⟨h, by simp [calleeGhost, hmu, hoi, hg], handoff_lent_access hok (lent_of hmu hoi hg)⟩
  · intro u v p q hu hv hne hown h k hgu hgv
    rw [parameterContext_rights, hms] at hu hv
    have hmu : ms[u]? = some (some p) := by
      cases hmu : ms[u]? with
      | none => simp [hmu] at hu
      | some mo => simp only [hmu, Option.getD_some] at hu; rw [hu]
    have hmv : ms[v]? = some (some q) := by
      cases hmv : ms[v]? with
      | none => simp [hmv] at hv
      | some mo => simp only [hmv, Option.getD_some] at hv; rw [hv]
    obtain ⟨i, hoi, hsi, hoi'⟩ := planFits_mode hp hmu
    obtain ⟨j, hoj, hsj, hoj'⟩ := planFits_mode hp hmv
    obtain ⟨mi, hi, hmi, hgi, _⟩ := rights_handle hr hsi
    obtain ⟨mj, hj, hmj, hgj, _⟩ := rights_handle hr hsj
    have hslot_u : h.slot = hi.slot := by
      cases p <;> simp [calleeGhost, hmu, hoi, hgi] at hgu <;> rw [← hgu]
    have hslot_v : k.slot = hj.slot := by
      cases q <;> simp [calleeGhost, hmv, hoj, hgj] at hgv <;> rw [← hgv]
    have hij : i ≠ j := by
      intro he; subst he
      rcases hown with hpo | hqo
      · subst hpo; exact hne (planFits_owned_unique hp hmu hoi hmv hoj)
      · subst hqo; exact hne (planFits_owned_unique hp hmv hoj hmu hoi).symm
    rw [hslot_u, hslot_v]
    rcases hown with hpo | hqo
    · subst hpo; exact hr.2 i j .owned mj (hoi' rfl) hmj hij (Or.inl rfl) hi hj hgi hgj
    · subst hqo; exact hr.2 i j mi .owned hmi (hoj' rfl) hij (Or.inr rfl) hi hj hgi hgj
  · intro slot cell hcell howner
    obtain ⟨hloans, h, hm, hslot, hc⟩ := handoff_callee_owned hok hcell howner
    obtain ⟨u, i, hmu, hou, hg⟩ := mem_moved hm
    refine ⟨hloans, u, ⟨h.slot, h.allocation, s.next⟩, ?_, ?_, hslot, ?_⟩
    · rw [parameterContext_rights, hms]; simp [hmu]
    · simp [calleeGhost, hmu, hou, hg]
    · subst hc; exact ⟨rfl, rfl⟩

/-! ## 3. Back at the caller -/

theorem afterCall_rights_of (hR : Realizes c g A fr s σ ρ) (hp : planFits c ms os = true)
    {s2 : State} {result : Option Handle}
    (hr : ReturnOk (s.handoff (calleeFrame A s fr) (movedHandles g ms os) (lentHandles g ms os)) s2
      (calleeFrame A s fr) result) :
    Rights (c.afterCall ms os) g (s2.restore fr (lentHandles g ms os) result) fr := by
  have hok := handoff_ok hR hp
  obtain ⟨_, _, _, _, hrt⟩ := hR
  refine ⟨?_, ?_⟩
  · intro j m hj
    obtain ⟨hcj, hcons⟩ := afterCall_rights_sub hj
    obtain ⟨h, hg, hperm⟩ := hrt.1 j m hcj
    have hunmoved : slotIn (movedHandles g ms os) h.slot = false := by
      cases hsm : slotIn (movedHandles g ms os) h.slot with
      | false => rfl
      | true =>
        obtain ⟨k, hk, hks⟩ := slotIn_iff.mp hsm
        obtain ⟨u, i, hmu, hou, hgk⟩ := mem_moved hk
        obtain ⟨i', hoi, _, hown⟩ := planFits_mode hp hmu
        rw [hou] at hoi; cases hoi
        have hij : i ≠ j := by
          intro he; subst he
          rw [consumes_iff.mpr ⟨u, hmu, hou⟩] at hcons; cases hcons
        exact absurd hks (hrt.2 i j .owned m (hown rfl) hcj hij (Or.inl rfl) k h hgk hg)
    obtain ⟨cell, hcell⟩ : ∃ cell, s.cells h.slot = some cell := by
      have ha := PassingMode.access_of_permits hperm
      unfold State.access at ha
      cases hc : s.cells h.slot with
      | none => rw [hc] at ha; cases ha
      | some cell => exact ⟨cell, rfl⟩
    have hsame := restore_unmoved hok hr hcell hunmoved
    exact ⟨h, hg, PassingMode.permits_same_cell (hsame.trans hcell.symm) hperm⟩
  · intro i j p q hi hj hne hown h k hgi hgj
    exact hrt.2 i j p q (afterCall_rights_sub hi).1 (afterCall_rights_sub hj).1 hne hown h k hgi hgj

/-- Every allocation the caller still owns after the call (other than an
owning result) is accounted for by an origin that was not consumed. -/
theorem afterCall_complete_rest (hR : Realizes c g A fr s σ ρ) (hc : Complete c g s fr)
    (hp : planFits c ms os = true) {s2 : State} {result : Option Handle}
    (hr : ReturnOk (s.handoff (calleeFrame A s fr) (movedHandles g ms os) (lentHandles g ms os)) s2
      (calleeFrame A s fr) result) :
    ∀ slot cell, (s2.restore fr (lentHandles g ms os) result).cells slot = some cell → cell.owner = fr →
      resultAt result slot = false →
      cell.loans = [] ∧ ∃ i h, (c.afterCall ms os).rights i = some .owned ∧ g i = some h ∧
        h.slot = slot ∧ cell.matches h := by
  have hok := handoff_ok hR hp
  intro slot cell h3 howner hres
  cases hs : s.cells slot with
  | none => rw [restore_new hr hs hres] at h3; cases h3
  | some old =>
    cases hm : slotIn (movedHandles g ms os) slot with
    | true => rw [restore_moved hok hr hm hres] at h3; cases h3
    | false =>
      rw [restore_unmoved hok hr hs hm] at h3
      cases h3
      obtain ⟨hloans, i, h, hi, hg, hslot, hmatch⟩ := hc slot cell hs howner
      refine ⟨hloans, i, h, ?_, hg, hslot, hmatch⟩
      rw [afterCall_rights]
      cases hcons : consumes ms os i with
      | false => exact hi
      | true =>
        obtain ⟨u, hmu, hou⟩ := consumes_iff.mp hcons
        have hmoved := moved_of hmu hou hg
        rw [← hslot, slotIn_of_mem hmoved] at hm
        cases hm

/-- **After a call with a plain result the caller's invariant holds again.** -/
theorem return_plain {s0 : State} (hR : Realizes c g A fr s σ ρ) (hc : Complete c g s fr)
    (hl : s0.local s fr) (hpr : s0.progress s) (hp : planFits c ms os = true)
    {s2 : State} {σ' : World D}
    (hr : ReturnOk (s.handoff (calleeFrame A s fr) (movedHandles g ms os) (lentHandles g ms os)) s2
      (calleeFrame A s fr) none)
    (ha : s2.agrees A σ') (hf : A.FreiOk σ') :
    Holds A fr s0 (c.afterCall ms os) σ' ρ := by
  have hok := handoff_ok hR hp
  refine ⟨g, s2.restore fr (lentHandles g ms os) none,
    ⟨restore_agrees hr ha, hf, afterCall_bounded hR.2.2.1, hR.2.2.2.1, afterCall_rights_of hR hp hr⟩,
    ?_, State.local_trans hl (restore_local hok hr), State.progress_trans hpr (restore_progress hok hr)⟩
  intro slot cell h3 howner
  exact afterCall_complete_rest hR hc hp hr slot cell h3 howner rfl

/-- **After a call with an owning result the caller's invariant holds with
the result bound under a new origin.** `k` is the returned index value. -/
theorem return_owner {s0 : State} (hR : Realizes c g A fr s σ ρ) (hc : Complete c g s fr)
    (hl : s0.local s fr) (hpr : s0.progress s) (hp : planFits c ms os = true)
    {s2 : State} {σ' : World D} {hres : Handle}
    (hr : ReturnOk (s.handoff (calleeFrame A s fr) (movedHandles g ms os) (lentHandles g ms os)) s2
      (calleeFrame A s fr) (some hres))
    (ha : s2.agrees A σ') (hf : A.FreiOk σ') (k : Wert D (Ty.index (D.count A.tab)))
    (hk : hres.slot = k.n) :
    Holds A fr s0 (c.afterCall ms os).bindFresh (σ') (.cons k ρ) := by
  have hok := handoff_ok hR hp
  have hres3 := restore_result (fr := fr) (lent := lentHandles g ms os) hr
  have hrights := afterCall_rights_of hR hp hr
  have hnext : s.next ≤ s2.next := Nat.le_trans (Nat.le_succ _) hr.progress.1
  have hdisjoint : ∀ i mode old, (c.afterCall ms os).rights i = some mode → g i = some old →
      old.slot ≠ (⟨hres.slot, hres.allocation, s2.next⟩ : Handle).slot := by
    intro i mode old hi hg he
    obtain ⟨h, hg', hperm⟩ := hrights.1 i mode hi
    rw [hg] at hg'; cases hg'
    obtain ⟨hci, _⟩ := afterCall_rights_sub hi
    obtain ⟨h0, hg0, hperm0⟩ := hR.2.2.2.2.1 i mode hci
    rw [hg] at hg0; cases hg0
    have ha0 := PassingMode.access_of_permits hperm0
    have ha3 := PassingMode.access_of_permits hperm
    unfold State.access at ha0 ha3
    rw [he, hres3.2] at ha3
    cases hc0 : s.cells old.slot with
    | none => rw [hc0] at ha0; cases ha0
    | some cell =>
      rw [hc0] at ha0
      have hv := hR.1.1 old.slot cell hc0
      have hg1 := ha0.1.2
      have hg2 := ha3.1.2
      simp only at hg2
      omega
  have ho : (s2.restore fr (lentHandles g ms os) (some hres)).owns fr ⟨hres.slot, hres.allocation, s2.next⟩ :=
    hres3.1
  refine ⟨g.set (c.afterCall ms os).next ⟨hres.slot, hres.allocation, s2.next⟩,
    s2.restore fr (lentHandles g ms os) (some hres),
    owning_context A (c.afterCall ms os) g fr _ σ' ρ k ⟨hres.slot, hres.allocation, s2.next⟩ (afterCall_bounded hR.2.2.1) hR.2.2.2.1
      (restore_agrees hr ha) hf (extend_rights hrights ho hdisjoint) hk,
    ?_, State.local_trans hl (restore_local hok hr), State.progress_trans hpr (restore_progress hok hr)⟩
  apply Complete.bindOwning (afterCall_bounded hR.2.2.1) ho
  intro slot cell h3 howner hne
  have hres' : resultAt (some hres) slot = false := by
    simp only [resultAt, Option.any_some, decide_eq_false_iff_not]
    exact fun he => hne he.symm
  exact afterCall_complete_rest hR hc hp hr slot cell h3 howner hres'

#print axioms handoff_requires
#print axioms return_plain
#print axioms return_owner

end Gabbro.Grammatik.ArenaOwnership.Body
