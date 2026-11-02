module
public import Grammatik.Bausteine.Arena.Struktur.ArenaLebt
public import Grammatik.Bausteine.Arena.Ownership.Statea
@[expose] public section


/-!
Ghost ownership of allocations in the existing arena world. A storage slot can be
reused. Its allocation incarnation and its current owning grant are distinct:
moving ownership issues a new grant, so returning an object never revives a saved
alias of a consumed argument. Loans keep the grant and form a scoped stack.
No payload memory or allocator implementation is duplicated here.
-/

namespace Gabbro.Grammatik.ArenaOwnership
theorem State.reset_valid (s : State) : s.reset.valid := by
  intro i c h
  cases h

theorem State.reset_no_access (s : State) (f : Frame) (h : Handle) :
    ¬ s.reset.access f h := by simp only [access, reset, not_false_eq_true]

/-- A live grant cannot survive a later grant for the same storage. -/
theorem State.future_no_access {s : State} (hv : s.valid) (f : Frame) (h : Handle)
    (hn : s.next ≤ h.grant) : ¬ s.access f h := by
  unfold State.access
  cases hc : s.cells h.slot with
  | none => simp only [not_false_eq_true]
  | some c =>
    intro ha
    have hh := hv h.slot c hc
    have hg := ha.1.2
    omega

theorem State.reuse_no_revival {s s' : State} {f : Frame} {i : Int} {h old : Handle}
    (he : s.allocate f i = some (s', h)) (hslot : old.slot = i) (hgrant : old.grant < s.next) :
    ∀ g, ¬ s'.access g old := by
  unfold State.allocate at he
  split at he
  · cases he
  · cases he
    intro g
    simp only [State.access, State.put, hslot, ite_true, Cell.matches]
    intro ha
    have heq := ha.1.2
    omega

theorem State.released_twice_no {s s' : State} {f : Frame} {h : Handle}
    (hv : s.valid) (he : s.release f h = some s') (g : Frame) : s'.release g h = none := by
  have hn := (State.release_valid hv f h he).2 g
  have hno : ¬ s'.owns g h := fun ho => hn (State.owner_access ho)
  simp only [release, hno, ↓reduceIte]

theorem State.moved_twice_no {s s' : State} {f g : Frame} {h h' : Handle}
    (hv : s.valid) (he : s.move f g h = some (s', h')) (k l : Frame) :
    s'.move k l h = none := by
  have hn := (State.move_valid hv f g h he).2.2.1 k
  have hno : ¬ s'.owns k h := fun ho => hn (State.owner_access ho)
  simp only [move, hno, false_and, ↓reduceIte]

theorem State.move_next {s s' : State} {f g : Frame} {h h' : Handle}
    (he : s.move f g h = some (s', h')) : s'.next = s.next + 1 := by
  unfold State.move at he
  split at he
  · cases he; rfl
  · cases he

theorem State.move_excludes_older {s s' : State} {f g : Frame} {h h' old : Handle}
    (he : s.move f g h = some (s', h')) (hs : old.slot = h.slot) (hg : old.grant < s.next) :
    ∀ k, ¬ s'.access k old := by
  unfold State.move at he
  split at he
  · cases he
    intro k
    simp only [State.access, State.put, hs, ite_true, Cell.matches]
    intro hh
    have heq := hh.1.2
    omega
  · cases he

theorem State.release_excludes_slot {s s' : State} {f : Frame} {h old : Handle}
    (he : s.release f h = some s') (hs : old.slot = h.slot) : ∀ k, ¬ s'.access k old := by
  unfold State.release at he
  split at he
  · cases he
    intro k
    simp only [access, put, hs, ↓reduceIte, not_false_eq_true]
  · cases he

theorem State.move_exists {s : State} {f g : Frame} {h : Handle}
    (ho : s.owns f h) (ht : f.thread = g.thread) : ∃ s' h', s.move f g h = some (s', h') := by
  simp only [move, ho, ht, and_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, exists_and_left, exists_eq',
  and_true]

theorem State.own_handles_equal {s : State} {f g : Frame} {h k : Handle}
    (hh : s.owns f h) (hk : s.owns g k) (hs : h.slot = k.slot) : h = k := by
  unfold State.owns at hh hk
  rw [hs] at hh
  cases hc : s.cells k.slot with
  | none => simp only [hc] at hk
  | some c =>
    rw [hc] at hh hk
    have ha := hh.1.1.symm.trans hk.1.1
    have hg := hh.1.2.symm.trans hk.1.2
    cases h; cases k
    simp only at hs ha hg
    cases hs; cases ha; cases hg; rfl

theorem State.own_cell {s : State} {f : Frame} {h : Handle} (ho : s.owns f h) :
    ∃ c, s.cells h.slot = some c := by
  unfold State.owns at ho
  cases hc : s.cells h.slot with
  | none => simp only [hc] at ho
  | some c => exact ⟨c, rfl⟩

theorem State.allocate_empty {s s' : State} {f : Frame} {i : Int} {h : Handle}
    (he : s.allocate f i = some (s', h)) : s.cells i = none := by
  unfold State.allocate at he
  split at he
  · cases he
  · assumption

theorem State.allocate_other {s s' : State} {f : Frame} {i : Int} {h : Handle}
    (he : s.allocate f i = some (s', h)) (j : Int) (hj : j ≠ i) : s'.cells j = s.cells j := by
  unfold State.allocate at he
  split at he
  · cases he
  · cases he; simp only [put, hj, ↓reduceIte]

theorem State.move_other {s s' : State} {f g : Frame} {h h' : Handle}
    (he : s.move f g h = some (s', h')) (j : Int) (hj : j ≠ h.slot) : s'.cells j = s.cells j := by
  unfold State.move at he
  split at he
  · cases he; simp only [put, hj, ↓reduceIte]
  · cases he

theorem State.release_other {s s' : State} {f : Frame} {h : Handle}
    (he : s.release f h = some s') (j : Int) (hj : j ≠ h.slot) : s'.cells j = s.cells j := by
  unfold State.release at he
  split at he
  · cases he; simp only [put, hj, ↓reduceIte]
  · cases he

theorem State.owns_from_same_cell {s s' : State} {f : Frame} {h : Handle}
    (he : s'.cells h.slot = s.cells h.slot) (ho : s.owns f h) : s'.owns f h := by
  simpa only [State.owns, he] using ho

theorem State.access_from_same_cell {s s' : State} {f : Frame} {h : Handle}
    (he : s'.cells h.slot = s.cells h.slot) (ho : s.access f h) : s'.access f h := by
  simpa only [State.access, he] using ho

theorem State.lend_valid {s : State} (hv : s.valid) (f g : Frame) (h : Handle)
    {s' : State} (he : s.lend f g h = some s') :
    s'.valid ∧ s'.access g h ∧ ¬ s'.owns g h ∧ ¬ s'.access f h := by
  unfold State.lend at he
  split at he
  · cases he
  · rename_i c hc
    split at he
    · rename_i hguard
      obtain ⟨hm, hf, ht, hgo, hgl⟩ := hguard
      have hh := hv h.slot c hc
      have hgf : g ≠ f := by
        intro eq
        by_cases hl : c.loans = []
        · exact hgo (by simpa [Cell.holder, hl] using (hf.trans eq.symm).symm)
        · have hmemb : c.holder ∈ c.loans := by
            cases heq : c.loans with
            | nil => exact False.elim (hl heq)
            | cons a rest => simp only [Cell.holder, heq, List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, List.mem_cons,
  true_or]
          exact hgl (by simpa [hf, eq] using hmemb)
      cases he
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i d hd
        by_cases hi : i = h.slot
        · subst i
          simp only [State.put_at, Option.some.injEq] at hd
          subst d
          exact ⟨hh.1, hh.2.1, List.nodup_cons.mpr ⟨hgl, hh.2.2.1⟩,
            by simp only [List.mem_cons, Ne.symm hgo, hh.2.2.2, or_self, not_false_eq_true]⟩
        · exact hv i d (by simpa [State.put, hi] using hd)
      · simpa [State.access, State.put, Cell.holder, Cell.matches] using hm
      · simp only [owns, put, ↓reduceIte, reduceCtorEq, and_false, not_false_eq_true]
      · simp only [access, put, ↓reduceIte, Cell.holder, List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
  hgf, and_false, not_false_eq_true]
    · cases he

theorem State.endLoan_valid {s : State} (hv : s.valid) (f : Frame) (h : Handle)
    {s' : State} (he : s.endLoan f h = some s') : s'.valid := by
  unfold State.endLoan at he
  split at he
  · cases he
  · rename_i c hc
    split at he
    · cases he
    · rename_i g rest hloans
      split at he
      · cases he
        intro i d hd
        by_cases hi : i = h.slot
        · subst i
          simp only [State.put_at, Option.some.injEq] at hd
          subst d
          have hh := hv h.slot c hc
          rw [hloans] at hh
          exact ⟨hh.1, hh.2.1, (List.nodup_cons.mp hh.2.2.1).2,
            fun hm => hh.2.2.2 (List.mem_cons_of_mem _ hm)⟩
        · exact hv i d (by simpa [State.put, hi] using hd)
      · cases he

theorem State.lend_endLoan {s : State} (f g : Frame) (h : Handle)
    {s' : State} (he : s.lend f g h = some s') : s'.endLoan g h = some s := by
  unfold State.lend at he
  split at he
  · cases he
  · rename_i c hc
    split at he
    · rename_i hguard
      cases he
      simp only [State.endLoan, State.put_at]
      rw [ite_eq_left ⟨hguard.1, trivial⟩]
      congr 1
      apply State.ext'
      · rfl
      · funext i
        by_cases hi : i = h.slot
        · subst i; simp only [put, ↓reduceIte, hc]
        · simp only [put, hi, ↓reduceIte]
    · cases he

theorem State.release_requires_owner {s s' : State} {f : Frame} {h : Handle}
    (he : s.release f h = some s') : s.owns f h := by
  unfold State.release at he
  split at he
  · assumption
  · cases he

theorem State.owned_live {D : Deklaration} {s : State} {A : FreiForm D} {σ : World D}
    (ha : s.agrees A σ) {f : Frame} {h : Handle} (ho : s.owns f h) : A.Lebt σ h.slot := by
  apply (ha.2 h.slot).mpr
  unfold State.owns at ho
  cases hc : s.cells h.slot with
  | none => simp only [hc] at ho
  | some c => exact ⟨c, rfl⟩

theorem State.access_live {D : Deklaration} {s : State} {A : FreiForm D} {σ : World D}
    (ha : s.agrees A σ) {f : Frame} {h : Handle} (ho : s.access f h) : A.Lebt σ h.slot := by
  apply (ha.2 h.slot).mpr
  unfold State.access at ho
  cases hc : s.cells h.slot with
  | none => simp only [hc] at ho
  | some c => exact ⟨c, rfl⟩

theorem State.reset_blocked_by_other {s : State} {f g : Frame} {h : Handle}
    (ho : s.owns g h) (hne : g ≠ f) : ¬ s.canReset f := by
  intro hr
  unfold State.owns at ho
  cases hc : s.cells h.slot with
  | none => simp only [hc] at ho
  | some c =>
    rw [hc] at ho
    exact hne (ho.2.1.symm.trans (hr h.slot c hc).1)

#print axioms State.move_valid
#print axioms State.lend_valid
#print axioms State.release_valid

end Gabbro.Grammatik.ArenaOwnership
