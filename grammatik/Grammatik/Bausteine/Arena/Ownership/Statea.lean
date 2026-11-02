module
public import Grammatik.Bausteine.Arena.Struktur.ArenaLebt
@[expose] public section


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
    (s.put i c).cells i = c := by simp only [put, ↓reduceIte]

@[simp] theorem State.put_other (s : State) (i j : Int) (c : Option Cell) (h : j ≠ i) :
    (s.put i c).cells j = s.cells j := by simp only [put, h, ↓reduceIte]

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
  | none => simp only [hc] at ho
  | some c =>
    rw [hc] at ho
    exact ⟨ho.1, by simp only [Cell.holder, ho.2.2, ho.2.1, List.headD_eq_head?_getD, List.head?_nil, Option.getD_none]⟩

theorem State.owner_unique {s : State} {f g : Frame} {h : Handle}
    (hf : s.owns f h) (hg : s.owns g h) : f = g := by
  unfold State.owns at hf hg
  cases hc : s.cells h.slot with
  | none => simp only [hc] at hf
  | some c =>
    rw [hc] at hf hg
    exact hf.2.1.symm.trans hg.2.1

theorem State.access_unique {s : State} {f g : Frame} {h : Handle}
    (hf : s.access f h) (hg : s.access g h) : f = g := by
  unfold State.access at hf hg
  cases hc : s.cells h.slot with
  | none => simp only [hc] at hf
  | some c =>
    rw [hc] at hf hg
    exact hf.2.symm.trans hg.2

theorem State.own_clock {s : State} {f : Frame} {h : Handle}
    (hv : s.valid) (ho : s.owns f h) : h.allocation ≤ h.grant ∧ h.grant < s.next := by
  unfold State.owns at ho
  cases hc : s.cells h.slot with
  | none => simp only [hc] at ho
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
        exact ⟨Nat.le_refl _, Nat.lt_succ_self _, List.nodup_nil, by simp only [List.not_mem_nil, not_false_eq_true]⟩
      · simp only [State.put, ite_eq_right hj] at hc
        have hh := hv j c hc
        exact ⟨hh.1, Nat.lt_succ_of_lt hh.2.1, hh.2.2⟩
    · simp only [owns, put, ↓reduceIte, Cell.matches, and_self]

theorem State.release_valid {s : State} (hv : s.valid) (f : Frame) (h : Handle)
    {s' : State} (he : s.release f h = some s') :
    s'.valid ∧ (∀ g, ¬ s'.access g h) := by
  unfold State.release at he
  split at he
  · cases he
    constructor
    · intro i c hc
      by_cases hi : i = h.slot
      · subst i; simp only [put_at, reduceCtorEq] at hc
      · exact hv i c (by simpa [State.put, hi] using hc)
    · intro g
      simp only [access, put, ↓reduceIte, not_false_eq_true]
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
          List.nodup_nil, by simp only [List.not_mem_nil, not_false_eq_true]⟩
      · simp only [State.put, ite_eq_right hi] at hc
        have hh := hv i c hc
        exact ⟨hh.1, Nat.lt_succ_of_lt hh.2.1, hh.2.2⟩
    · simp only [owns, put, ↓reduceIte, Cell.matches, and_self]
    · intro k
      simp only [State.access, State.put, ite_true, Cell.matches]
      intro ha
      omega
  · cases he


end Gabbro.Grammatik.ArenaOwnership
