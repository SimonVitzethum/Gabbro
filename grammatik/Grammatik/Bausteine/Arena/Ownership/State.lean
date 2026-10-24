import Grammatik.Bausteine.Arena.Struktur.ArenaLebt

/-!
Ghost ownership of allocations in the existing arena world. A storage slot can be
reused. Its allocation incarnation and its current owning grant are distinct:
moving ownership issues a new grant, so returning an object never revives a saved
alias of a consumed argument. Loans keep the grant and form a scoped stack.
No payload memory or allocator implementation is duplicated here.
-/

namespace Gabbro.Grammatik.ArenaOwnership

structure Frame where
  thread : Nat
  activation : Nat
  deriving DecidableEq, Repr

structure Handle where
  slot : Int
  allocation : Nat
  grant : Nat
  deriving DecidableEq, Repr

structure Cell where
  allocation : Nat
  grant : Nat
  owner : Frame
  loans : List Frame
  deriving DecidableEq, Repr

def Cell.holder (c : Cell) : Frame := c.loans.headD c.owner

def Cell.matches (c : Cell) (h : Handle) : Prop :=
  c.allocation = h.allocation ∧ c.grant = h.grant

instance (c : Cell) (h : Handle) : Decidable (c.matches h) :=
  inferInstanceAs (Decidable (_ ∧ _))

structure State where
  next : Nat
  cells : Int → Option Cell

theorem State.ext' {s t : State} (hn : s.next = t.next) (hc : s.cells = t.cells) : s = t := by
  cases s; cases t; cases hn; cases hc; rfl

def State.empty : State := ⟨0, fun _ => none⟩

def State.put (s : State) (i : Int) (c : Option Cell) : State :=
  { s with cells := fun j => if j = i then c else s.cells j }

@[simp] theorem State.put_at (s : State) (i : Int) (c : Option Cell) :
    (s.put i c).cells i = c := by simp [State.put]

@[simp] theorem State.put_other (s : State) (i j : Int) (c : Option Cell) (h : j ≠ i) :
    (s.put i c).cells j = s.cells j := by simp [State.put, h]

def State.valid (s : State) : Prop :=
  ∀ i c, s.cells i = some c →
    c.allocation ≤ c.grant ∧ c.grant < s.next ∧ c.loans.Nodup ∧ c.owner ∉ c.loans

def State.access (s : State) (f : Frame) (h : Handle) : Prop :=
  match s.cells h.slot with
  | none => False
  | some c => c.matches h ∧ c.holder = f

def State.owns (s : State) (f : Frame) (h : Handle) : Prop :=
  match s.cells h.slot with
  | none => False
  | some c => c.matches h ∧ c.owner = f ∧ c.loans = []

instance (s : State) (f : Frame) (h : Handle) : Decidable (s.access f h) := by
  unfold State.access
  split <;> infer_instance

instance (s : State) (f : Frame) (h : Handle) : Decidable (s.owns f h) := by
  unfold State.owns
  split <;> infer_instance

def State.allocate (s : State) (f : Frame) (i : Int) : Option (State × Handle) :=
  match s.cells i with
  | some _ => none
  | none => some
      ({ (s.put i (some ⟨s.next, s.next, f, []⟩)) with next := s.next + 1 },
       ⟨i, s.next, s.next⟩)

def State.release (s : State) (f : Frame) (h : Handle) : Option State :=
  if s.owns f h then some (s.put h.slot none) else none

def State.move (s : State) (f g : Frame) (h : Handle) : Option (State × Handle) :=
  if s.owns f h ∧ f.thread = g.thread then
    some ({ (s.put h.slot (some ⟨h.allocation, s.next, g, []⟩)) with next := s.next + 1 },
      ⟨h.slot, h.allocation, s.next⟩)
  else none

def State.lend (s : State) (f g : Frame) (h : Handle) : Option State :=
  match s.cells h.slot with
  | none => none
  | some c =>
    if c.matches h ∧ c.holder = f ∧ f.thread = g.thread ∧ g ≠ c.owner ∧ g ∉ c.loans then
      some (s.put h.slot (some { c with loans := g :: c.loans }))
    else none

def State.endLoan (s : State) (f : Frame) (h : Handle) : Option State :=
  match s.cells h.slot with
  | none => none
  | some c =>
    match c.loans with
    | [] => none
    | g :: rest =>
      if c.matches h ∧ g = f then
        some (s.put h.slot (some { c with loans := rest }))
      else none

/-- Reset may retire the current frame's allocations, but no other frame's
rights and no outstanding loan. The next grant is never reset. -/
def State.canReset (s : State) (f : Frame) : Prop :=
  ∀ i c, s.cells i = some c → c.owner = f ∧ c.loans = []

def State.reset (s : State) : State := ⟨s.next, fun _ => none⟩

/-- The ghost ledger describes exactly the live slots of the actual G world. -/
def State.agrees {D : Deklaration} (s : State) (A : FreiForm D) (σ : World D) : Prop :=
  s.valid ∧ ∀ i, A.Lebt σ i ↔ ∃ c, s.cells i = some c

theorem State.empty_valid : State.empty.valid := by
  intro i c h
  cases h

theorem State.owner_access {s : State} {f : Frame} {h : Handle} (ho : s.owns f h) :
    s.access f h := by
  unfold State.owns at ho
  unfold State.access
  cases hc : s.cells h.slot with
  | none => simp [hc] at ho
  | some c =>
    rw [hc] at ho
    exact ⟨ho.1, by simp [Cell.holder, ho.2.2, ho.2.1]⟩

theorem State.owner_unique {s : State} {f g : Frame} {h : Handle}
    (hf : s.owns f h) (hg : s.owns g h) : f = g := by
  unfold State.owns at hf hg
  cases hc : s.cells h.slot with
  | none => simp [hc] at hf
  | some c =>
    rw [hc] at hf hg
    exact hf.2.1.symm.trans hg.2.1

theorem State.access_unique {s : State} {f g : Frame} {h : Handle}
    (hf : s.access f h) (hg : s.access g h) : f = g := by
  unfold State.access at hf hg
  cases hc : s.cells h.slot with
  | none => simp [hc] at hf
  | some c =>
    rw [hc] at hf hg
    exact hf.2.symm.trans hg.2

theorem State.own_clock {s : State} {f : Frame} {h : Handle}
    (hv : s.valid) (ho : s.owns f h) : h.allocation ≤ h.grant ∧ h.grant < s.next := by
  unfold State.owns at ho
  cases hc : s.cells h.slot with
  | none => simp [hc] at ho
  | some c =>
    rw [hc] at ho
    have hh := hv h.slot c hc
    rcases ho.1 with ⟨ha, hg⟩
    exact ⟨ha ▸ hg ▸ hh.1, hg ▸ hh.2.1⟩

theorem State.allocate_valid {s : State} (hv : s.valid) (f : Frame) (i : Int)
    {s' : State} {h : Handle} (he : s.allocate f i = some (s', h)) :
    s'.valid ∧ s'.owns f h := by
  unfold State.allocate at he
  split at he
  · cases he
  · cases he
    constructor
    · intro j c hc
      by_cases hj : j = i
      · subst j
        simp only [State.put, ite_true, Option.some.injEq] at hc
        subst c
        exact ⟨Nat.le_refl _, Nat.lt_succ_self _, List.nodup_nil, by simp⟩
      · simp only [State.put, ite_eq_right hj] at hc
        have hh := hv j c hc
        exact ⟨hh.1, Nat.lt_succ_of_lt hh.2.1, hh.2.2⟩
    · simp [State.owns, State.put, Cell.matches]

theorem State.release_valid {s : State} (hv : s.valid) (f : Frame) (h : Handle)
    {s' : State} (he : s.release f h = some s') :
    s'.valid ∧ (∀ g, ¬ s'.access g h) := by
  unfold State.release at he
  split at he
  · cases he
    constructor
    · intro i c hc
      by_cases hi : i = h.slot
      · subst i; simp at hc
      · exact hv i c (by simpa [State.put, hi] using hc)
    · intro g
      simp [State.access, State.put]
  · cases he

theorem State.move_valid {s : State} (hv : s.valid) (f g : Frame) (h : Handle)
    {s' : State} {h' : Handle} (he : s.move f g h = some (s', h')) :
    s'.valid ∧ s'.owns g h' ∧ (∀ k, ¬ s'.access k h) ∧
      h'.slot = h.slot ∧ h'.allocation = h.allocation := by
  unfold State.move at he
  split at he
  · rename_i ho
    have hclock := State.own_clock hv ho.1
    cases he
    refine ⟨?_, ?_, ?_, rfl, rfl⟩
    · intro i c hc
      by_cases hi : i = h.slot
      · subst i
        simp only [State.put, ite_true, Option.some.injEq] at hc
        subst c
        exact ⟨Nat.le_trans hclock.1 (Nat.le_of_lt hclock.2), Nat.lt_succ_self _,
          List.nodup_nil, by simp⟩
      · simp only [State.put, ite_eq_right hi] at hc
        have hh := hv i c hc
        exact ⟨hh.1, Nat.lt_succ_of_lt hh.2.1, hh.2.2⟩
    · simp [State.owns, State.put, Cell.matches]
    · intro k
      simp only [State.access, State.put, ite_true, Cell.matches]
      intro ha
      omega
  · cases he

theorem State.reset_valid (s : State) : s.reset.valid := by
  intro i c h
  cases h

theorem State.reset_no_access (s : State) (f : Frame) (h : Handle) :
    ¬ s.reset.access f h := by simp [State.reset, State.access]

/-- A live grant cannot survive a later grant for the same storage. -/
theorem State.future_no_access {s : State} (hv : s.valid) (f : Frame) (h : Handle)
    (hn : s.next ≤ h.grant) : ¬ s.access f h := by
  unfold State.access
  cases hc : s.cells h.slot with
  | none => simp
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
  simp [State.release, hno]

theorem State.moved_twice_no {s s' : State} {f g : Frame} {h h' : Handle}
    (hv : s.valid) (he : s.move f g h = some (s', h')) (k l : Frame) :
    s'.move k l h = none := by
  have hn := (State.move_valid hv f g h he).2.2.1 k
  have hno : ¬ s'.owns k h := fun ho => hn (State.owner_access ho)
  simp [State.move, hno]

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
    simp [State.access, State.put, hs]
  · cases he

theorem State.move_exists {s : State} {f g : Frame} {h : Handle}
    (ho : s.owns f h) (ht : f.thread = g.thread) : ∃ s' h', s.move f g h = some (s', h') := by
  simp [State.move, ho, ht]

theorem State.own_handles_equal {s : State} {f g : Frame} {h k : Handle}
    (hh : s.owns f h) (hk : s.owns g k) (hs : h.slot = k.slot) : h = k := by
  unfold State.owns at hh hk
  rw [hs] at hh
  cases hc : s.cells k.slot with
  | none => simp [hc] at hk
  | some c =>
    rw [hc] at hh hk
    have ha := hh.1.1.symm.trans hk.1.1
    have hg := hh.1.2.symm.trans hk.1.2
    cases h; cases k
    simp only at hs ha hg
    cases hs; cases ha; cases hg; rfl

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
            | cons a rest => simp [Cell.holder, heq]
          exact hgl (by simpa [hf, eq] using hmemb)
      cases he
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i d hd
        by_cases hi : i = h.slot
        · subst i
          simp only [State.put_at, Option.some.injEq] at hd
          subst d
          exact ⟨hh.1, hh.2.1, List.nodup_cons.mpr ⟨hgl, hh.2.2.1⟩,
            by simp [Ne.symm hgo, hh.2.2.2]⟩
        · exact hv i d (by simpa [State.put, hi] using hd)
      · simpa [State.access, State.put, Cell.holder, Cell.matches] using hm
      · simp [State.owns, State.put]
      · simp [State.access, State.put, Cell.holder, hgf]
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
        · subst i; simp [State.put, hc]
        · simp [State.put, hi]
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
  | none => simp [hc] at ho
  | some c => exact ⟨c, rfl⟩

theorem State.access_live {D : Deklaration} {s : State} {A : FreiForm D} {σ : World D}
    (ha : s.agrees A σ) {f : Frame} {h : Handle} (ho : s.access f h) : A.Lebt σ h.slot := by
  apply (ha.2 h.slot).mpr
  unfold State.access at ho
  cases hc : s.cells h.slot with
  | none => simp [hc] at ho
  | some c => exact ⟨c, rfl⟩

theorem State.reset_blocked_by_other {s : State} {f g : Frame} {h : Handle}
    (ho : s.owns g h) (hne : g ≠ f) : ¬ s.canReset f := by
  intro hr
  unfold State.owns at ho
  cases hc : s.cells h.slot with
  | none => simp [hc] at ho
  | some c =>
    rw [hc] at ho
    exact hne (ho.2.1.symm.trans (hr h.slot c hc).1)

#print axioms State.move_valid
#print axioms State.lend_valid
#print axioms State.release_valid

end Gabbro.Grammatik.ArenaOwnership
