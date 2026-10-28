import Grammatik.Bausteine.Arena.Ownership.Body.Holds

/-! **The ledger seen from one activation of the running machine.** One
ledger serves every thread. A cell belongs to the thread of its owner; its
loans are activations of the same thread, deeper than the owner, the
deepest first (`Disciplined`). An activation sees only the cells owned at
or above it in its own thread, with the loans to deeper activations hidden
(`viewAt`): what a suspended caller has lent to its callees is, seen from
the caller, still its own. A step of the running (deepest) activation of a
thread that keeps every cell it does not own (`State.local`) changes no
view but its own, and nothing another thread sees. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

/-- `g` is an activation of `fr`'s thread below `fr` on the stack. -/
def _root_.Gabbro.Grammatik.ArenaOwnership.Frame.Deeper (fr g : Frame) : Prop := g.thread = fr.thread ∧ fr.activation < g.activation

instance (fr g : Frame) : Decidable (fr.Deeper g) := inferInstanceAs (Decidable (_ ∧ _))

/-- The loans of a cell: of the owner's thread, deeper than the owner, the deepest first. -/
def _root_.Gabbro.Grammatik.ArenaOwnership.Cell.Ordered (c : Cell) : Prop :=
  (∀ g ∈ c.loans, c.owner.Deeper g) ∧ c.loans.Pairwise (fun a b => b.activation < a.activation)

/-- **The discipline of the ledger** against the running depth of every thread: every
    activation a cell names exists. -/
def _root_.Gabbro.Grammatik.ArenaOwnership.State.Disciplined (s : State) (depth : Nat → Nat) : Prop :=
  ∀ i c, s.cells i = some c → c.Ordered ∧ c.owner.activation ≤ depth c.owner.thread ∧
    ∀ g ∈ c.loans, g.activation ≤ depth g.thread

/-- `fr` sees the cell: owned in its thread, at or above it. -/
def _root_.Gabbro.Grammatik.ArenaOwnership.Frame.Sees (fr : Frame) (c : Cell) : Prop :=
  c.owner.thread = fr.thread ∧ c.owner.activation ≤ fr.activation

instance (fr : Frame) (c : Cell) : Decidable (fr.Sees c) := inferInstanceAs (Decidable (_ ∧ _))

/-- The cell as `fr` sees it: loans to deeper activations hidden. -/
def _root_.Gabbro.Grammatik.ArenaOwnership.Cell.at (c : Cell) (fr : Frame) : Cell :=
  { c with loans := c.loans.filter (fun g => !decide (fr.Deeper g)) }

/-- **The ledger seen from `fr`.** -/
def _root_.Gabbro.Grammatik.ArenaOwnership.State.viewAt (s : State) (fr : Frame) : State :=
  ⟨0, fun i => match s.cells i with
    | some c => if fr.Sees c then some (c.at fr) else none
    | none => none⟩

namespace View

variable {s s' : State} {depth : Nat → Nat}

theorem viewAt_cells (s : State) (fr : Frame) (i : Int) :
    (s.viewAt fr).cells i = (s.cells i).bind (fun c => if fr.Sees c then some (c.at fr) else none) := by
  simp only [State.viewAt]
  cases s.cells i <;> rfl

/-- Two ledgers with the same cells everywhere `fr` looks have the same view. -/
theorem viewAt_eq {fr : Frame}
    (h : ∀ i, (s.cells i).bind (fun c => if fr.Sees c then some (c.at fr) else none) =
      (s'.cells i).bind (fun c => if fr.Sees c then some (c.at fr) else none)) :
    s.viewAt fr = s'.viewAt fr := by
  exact State.ext' rfl (funext fun i => by rw [viewAt_cells, viewAt_cells, h i])

/-- The running activation of a thread: deeper than every activation the ledger names. -/
def Running (depth : Nat → Nat) (fr : Frame) : Prop := fr.activation = depth fr.thread

theorem no_deeper (hd : s.Disciplined depth) {fr : Frame} (hr : Running depth fr) {i : Int} {c : Cell}
    (hc : s.cells i = some c) : ∀ g ∈ c.loans, ¬ fr.Deeper g := by
  intro g hg ⟨ht, hlt⟩
  have := (hd i c hc).2.2 g hg
  rw [ht, ← hr] at this
  omega

theorem at_running (hd : s.Disciplined depth) {fr : Frame} (hr : Running depth fr) {i : Int} {c : Cell}
    (hc : s.cells i = some c) : c.at fr = c := by
  have hn := no_deeper hd hr hc
  cases c with
  | mk a g o loans =>
    simp only [Cell.at, Cell.mk.injEq, true_and]
    apply List.filter_eq_self.mpr
    intro x hx
    simpa using hn x hx

/-- **What the running activation is allowed, it is allowed in its view, and back.** -/
theorem permits_running (hd : s.Disciplined depth) {fr : Frame} (hr : Running depth fr)
    (m : PassingMode) (h : Handle) : m.permits (s.viewAt fr) fr h ↔ m.permits s fr h := by
  have key : ∀ c, s.cells h.slot = some c →
      ((m.permits (s.viewAt fr) fr h) ↔ (m.permits s fr h)) := by
    intro c hc
    have hat := at_running hd hr hc
    cases m with
    | owned =>
      simp only [PassingMode.permits, State.owns, viewAt_cells, hc, Option.bind_some]
      by_cases hs : fr.Sees c
      · simp only [hs, ↓reduceIte, hat]
      · simp only [hs, ite_false]
        constructor
        · intro h; exact h.elim
        · rintro ⟨_, ho, _⟩
          exact hs ⟨by rw [ho], by rw [ho]; exact Nat.le_refl _⟩
    | borrowed =>
      simp only [PassingMode.permits, State.access, viewAt_cells, hc, Option.bind_some]
      by_cases hs : fr.Sees c
      · simp only [hs, ↓reduceIte, hat]
      · simp only [hs, ite_false]
        constructor
        · intro h; exact h.elim
        · rintro ⟨_, hh⟩
          apply hs
          cases hl : c.loans with
          | nil =>
            simp only [Cell.holder, hl, List.headD_nil] at hh
            exact ⟨by rw [hh], by rw [hh]; exact Nat.le_refl _⟩
          | cons g rest =>
            simp only [Cell.holder, hl, List.headD_cons] at hh
            have hdp := (hd h.slot c hc).1.1 g (by rw [hl]; exact List.mem_cons_self)
            subst hh
            exact ⟨hdp.1.symm, Nat.le_of_lt hdp.2⟩
  cases hc : s.cells h.slot with
  | some c => exact key c hc
  | none =>
    cases m <;> simp only [PassingMode.permits, State.owns, viewAt_cells, hc, Option.bind_none, State.access]

theorem rights_running (hd : s.Disciplined depth) {fr : Frame} (hr : Running depth fr) {c : Context}
    {g : Ghost} : Rights c g (s.viewAt fr) fr ↔ Rights c g s fr := by
  unfold Rights
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun o m hm => by
      obtain ⟨h, hg, hp⟩ := h1 o m hm
      exact ⟨h, hg, (permits_running hd hr m h).mp hp⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun o m hm => by
      obtain ⟨h, hg, hp⟩ := h1 o m hm
      exact ⟨h, hg, (permits_running hd hr m h).mpr hp⟩, h2⟩

theorem complete_running (hd : s.Disciplined depth) {fr : Frame} (hr : Running depth fr) {c : Context}
    {g : Ghost} : Complete c g (s.viewAt fr) fr ↔ Complete c g s fr := by
  unfold Complete
  constructor
  · intro h slot cell hc ho
    have hs : fr.Sees cell := ⟨by rw [ho], by rw [ho]; exact Nat.le_refl _⟩
    have := h slot (cell.at fr) (by rw [viewAt_cells, hc]; simp only [Option.bind_some, hs, ↓reduceIte]) (by simpa [Cell.at] using ho)
    rwa [at_running hd hr hc] at this
  · intro h slot cell hc ho
    rw [viewAt_cells] at hc
    cases hcs : s.cells slot with
    | none => rw [hcs] at hc; cases hc
    | some c0 =>
      rw [hcs] at hc
      simp only [Option.bind_some] at hc
      split at hc
      · cases hc
        rw [at_running hd hr hcs] at ho ⊢
        exact h slot c0 hcs ho
      · cases hc

/-! ## A step of the running activation -/

/-- A step that keeps every cell the running activation `fr` does not own, in both directions. -/
theorem local_cells {fr : Frame} (hl : s.local s' fr) (i : Int) (c : Cell) (ho : c.owner ≠ fr) :
    s.cells i = some c ↔ s'.cells i = some c :=
  ⟨fun h => hl.1 i c h ho, fun h => hl.2 i c h ho⟩

/-- **A step of the running activation `fr` changes no other activation's view.** -/
theorem local_view (hd : s.Disciplined depth) {fr : Frame} (hr : Running depth fr) (hl : s.local s' fr)
    {fr2 : Frame} (hne : fr2.thread ≠ fr.thread ∨ fr2.activation < fr.activation) :
    s.viewAt fr2 = s'.viewAt fr2 := by
  have hhid : ∀ c : Cell, c.owner = fr → ¬ fr2.Sees c := by
    intro c ho ⟨ht, ha⟩
    rw [ho] at ht ha
    rcases hne with h | h
    · exact h ht.symm
    · omega
  apply viewAt_eq
  intro i
  cases h1 : s.cells i with
  | none =>
    cases h2 : s'.cells i with
    | none => rfl
    | some c' =>
      by_cases ho : c'.owner = fr
      · simp only [Option.bind_none, Option.bind_some, hhid c' ho, ↓reduceIte]
      · rw [← local_cells hl i c' ho, h1] at h2; cases h2
  | some c =>
    by_cases ho : c.owner = fr
    · cases h2 : s'.cells i with
      | none => simp only [Option.bind_some, hhid c ho, ↓reduceIte, Option.bind_none]
      | some c' =>
        by_cases ho' : c'.owner = fr
        · simp only [Option.bind_some, hhid c ho, ↓reduceIte, hhid c' ho']
        · rw [← local_cells hl i c' ho', h1] at h2
          cases h2; exact absurd ho ho'
    · rw [(local_cells hl i c ho).mp h1]

/-- **The discipline survives a step of the running activation** whose own cells carry no loans. -/
theorem local_disciplined (hd : s.Disciplined depth) {fr : Frame} (hr : Running depth fr)
    (hl : s.local s' fr) (hown : ∀ i c, s'.cells i = some c → c.owner = fr → c.loans = []) :
    s'.Disciplined depth := by
  intro i c hc
  by_cases ho : c.owner = fr
  · have hn := hown i c hc ho
    refine ⟨⟨by simp only [hn, List.not_mem_nil, false_implies, implies_true], by simp only [hn, List.Pairwise.nil]⟩, by rw [ho, hr]; exact Nat.le_refl _, by simp only [hn, List.not_mem_nil, false_implies, implies_true]⟩
  · exact hd i c ((local_cells hl i c ho).mpr hc)

end View

end Gabbro.Grammatik.ArenaOwnership.Machine
