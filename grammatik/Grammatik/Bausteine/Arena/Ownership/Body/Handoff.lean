import Grammatik.Bausteine.Arena.Ownership.Body.Holds

/-! The ledger side of a call. At the call the caller hands its owning
arguments to the fresh callee activation (each moved allocation gets a new
grant owned by the callee) and lends its borrowed arguments (the callee goes
on top of the loan stack). At the return every loan comes back, an owning
result moves to the caller with a new grant, and every other allocation is
exactly as before. Nothing here trusts the callee: the return lemmas assume
only the callee's checked interface postcondition. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

def slotIn (hs : List Handle) (j : Int) : Bool := hs.any (fun h => decide (h.slot = j))

theorem slotIn_iff {hs : List Handle} {j : Int} : slotIn hs j = true ↔ ∃ h ∈ hs, h.slot = j := by
  simp only [slotIn, List.any_eq_true, decide_eq_true_eq]

theorem slotIn_of_mem {hs : List Handle} {h : Handle} (hm : h ∈ hs) : slotIn hs h.slot = true :=
  slotIn_iff.mpr ⟨h, hm, rfl⟩

def resultAt (result : Option Handle) (j : Int) : Bool := result.any (fun h => decide (h.slot = j))

/-- One cell at the callee's entry. -/
def handoffCell (next : Nat) (cf : Frame) (moved lent : List Handle) (j : Int) (cell : Cell) : Cell :=
  bif slotIn moved j then ⟨cell.allocation, next, cf, []⟩
  else bif slotIn lent j then { cell with loans := cf :: cell.loans } else cell

/-- **The ledger at the callee's entry.** -/
def _root_.Gabbro.Grammatik.ArenaOwnership.State.handoff (s : State) (cf : Frame)
    (moved lent : List Handle) : State :=
  ⟨s.next + 1, fun j => (s.cells j).map (handoffCell s.next cf moved lent j)⟩

/-- One cell back at the caller. -/
def restoreCell (next : Nat) (fr : Frame) (lent : List Handle) (result : Option Handle) (j : Int)
    (cell : Cell) : Cell :=
  bif resultAt result j then ⟨cell.allocation, next, fr, []⟩
  else bif slotIn lent j then { cell with loans := cell.loans.tail } else cell

/-- **The ledger back at the caller.** -/
def _root_.Gabbro.Grammatik.ArenaOwnership.State.restore (s : State) (fr : Frame) (lent : List Handle)
    (result : Option Handle) : State :=
  ⟨s.next + 1, fun j => (s.cells j).map (restoreCell s.next fr lent result j)⟩

/-- What the caller's source check establishes about the handed arguments. -/
structure HandoffOk (s : State) (fr cf : Frame) (moved lent : List Handle) : Prop where
  valid : s.valid
  owned : ∀ h ∈ moved, s.owns fr h
  lentAccess : ∀ h ∈ lent, s.access fr h
  disjoint : ∀ h ∈ moved, ∀ k ∈ lent, h.slot ≠ k.slot
  fresh : ∀ j cell, s.cells j = some cell → cell.owner ≠ cf ∧ cf ∉ cell.loans

section Handoff

variable {s : State} {fr cf : Frame} {moved lent : List Handle}

theorem handoff_cells (j : Int) :
    (s.handoff cf moved lent).cells j = (s.cells j).map (handoffCell s.next cf moved lent j) := rfl

theorem handoff_none (j : Int) : (s.handoff cf moved lent).cells j = none ↔ s.cells j = none := by
  rw [handoff_cells]; simp only [Option.map_eq_none_iff]

theorem handoff_other {j : Int} (hm : slotIn moved j = false) (hl : slotIn lent j = false) :
    (s.handoff cf moved lent).cells j = s.cells j := by
  rw [handoff_cells]
  cases s.cells j <;> simp only [Option.map_none, Option.map_some, handoffCell, hm, hl, cond_eq_ite, Bool.false_eq_true, ↓reduceIte]

theorem moved_cell (hok : HandoffOk s fr cf moved lent) {h : Handle} (hm : h ∈ moved) :
    s.cells h.slot = some ⟨h.allocation, h.grant, fr, []⟩ := by
  have ho := hok.owned h hm
  unfold State.owns at ho
  cases hc : s.cells h.slot with
  | none => simp only [hc] at ho
  | some cell =>
    rw [hc] at ho
    obtain ⟨⟨ha, hg⟩, hf, hl⟩ := ho
    cases cell
    simp_all

theorem handoff_moved (hok : HandoffOk s fr cf moved lent) {h : Handle} (hm : h ∈ moved) :
    (s.handoff cf moved lent).cells h.slot = some ⟨h.allocation, s.next, cf, []⟩ := by
  rw [handoff_cells, moved_cell hok hm]
  simp only [Option.map_some, handoffCell, slotIn_of_mem hm, cond_eq_ite, ↓reduceIte]

theorem handoff_moved_owns (hok : HandoffOk s fr cf moved lent) {h : Handle} (hm : h ∈ moved) :
    (s.handoff cf moved lent).owns cf ⟨h.slot, h.allocation, s.next⟩ := by
  simp only [State.owns, handoff_moved hok hm, Cell.matches, and_self]

theorem lent_cell (hok : HandoffOk s fr cf moved lent) {k : Handle} (hk : k ∈ lent) :
    ∃ cell, s.cells k.slot = some cell ∧ cell.matches k ∧ cell.holder = fr := by
  have ha := hok.lentAccess k hk
  unfold State.access at ha
  cases hc : s.cells k.slot with
  | none => simp only [hc] at ha
  | some cell => rw [hc] at ha; exact ⟨cell, rfl, ha⟩

theorem not_moved_of_lent (hok : HandoffOk s fr cf moved lent) {k : Handle} (hk : k ∈ lent) :
    slotIn moved k.slot = false := by
  cases hm : slotIn moved k.slot with
  | false => rfl
  | true =>
    obtain ⟨h, hh, he⟩ := slotIn_iff.mp hm
    exact absurd he (hok.disjoint h hh k hk)

theorem handoff_lent (hok : HandoffOk s fr cf moved lent) {k : Handle} (hk : k ∈ lent) :
    ∃ cell, s.cells k.slot = some cell ∧ cell.matches k ∧ cell.holder = fr ∧
      (s.handoff cf moved lent).cells k.slot = some { cell with loans := cf :: cell.loans } := by
  obtain ⟨cell, hc, hm, hh⟩ := lent_cell hok hk
  refine ⟨cell, hc, hm, hh, ?_⟩
  rw [handoff_cells, hc]
  simp only [Option.map_some, handoffCell, not_moved_of_lent hok hk, slotIn_of_mem hk, cond_eq_ite, ↓reduceIte,
  Bool.false_eq_true]

theorem handoff_lent_access (hok : HandoffOk s fr cf moved lent) {k : Handle} (hk : k ∈ lent) :
    (s.handoff cf moved lent).access cf k := by
  obtain ⟨cell, _, hm, _, h1⟩ := handoff_lent hok hk
  simp only [State.access, h1, Cell.holder, List.headD_cons]
  exact ⟨hm, by simp only⟩

theorem handoff_valid (hok : HandoffOk s fr cf moved lent) : (s.handoff cf moved lent).valid := by
  intro j c hc
  rw [handoff_cells, Option.map_eq_some_iff] at hc
  obtain ⟨cell, hs, rfl⟩ := hc
  have hh := hok.valid j cell hs
  have hfr := hok.fresh j cell hs
  cases hm : slotIn moved j
  · cases hl : slotIn lent j
    · simp only [handoffCell, hm, hl, Bool.cond_false]
      exact ⟨hh.1, Nat.lt_succ_of_lt hh.2.1, hh.2.2⟩
    · simp only [handoffCell, hm, hl, Bool.cond_false, Bool.cond_true]
      refine ⟨hh.1, Nat.lt_succ_of_lt hh.2.1, List.nodup_cons.mpr ⟨hfr.2, hh.2.2.1⟩, ?_⟩
      simp only [List.mem_cons, not_or]
      exact ⟨hfr.1, hh.2.2.2⟩
  · simp only [handoffCell, hm, Bool.cond_true]
    exact ⟨by omega, Nat.lt_succ_self _, List.nodup_nil, by simp only [List.not_mem_nil, not_false_eq_true]⟩

theorem handoff_agrees {A : FreiForm D} {σ : World D} (hok : HandoffOk s fr cf moved lent)
    (ha : s.agrees A σ) : (s.handoff cf moved lent).agrees A σ := by
  refine ⟨handoff_valid hok, fun i => (ha.2 i).trans ?_⟩
  rw [handoff_cells]
  cases s.cells i <;> simp only [reduceCtorEq, exists_false, Option.map_none, Option.some.injEq, exists_eq', Option.map_some]

theorem handoff_progress : s.progress (s.handoff cf moved lent) := by
  refine ⟨Nat.le_succ _, ?_⟩
  intro j c hc hlt
  rw [handoff_cells, Option.map_eq_some_iff] at hc
  obtain ⟨cell, hs, rfl⟩ := hc
  cases hm : slotIn moved j
  · cases hl : slotIn lent j
    · simp only [handoffCell, hm, hl, Bool.cond_false]; exact ⟨cell, hs, rfl, rfl⟩
    · simp only [handoffCell, hm, hl, Bool.cond_false, Bool.cond_true]; exact ⟨cell, hs, rfl, rfl⟩
  · simp only [handoffCell, hm, Bool.cond_true] at hlt; exact absurd hlt (Nat.lt_irrefl _)

/-- Every allocation the callee owns at entry is a handed one. -/
theorem handoff_callee_owned (hok : HandoffOk s fr cf moved lent) {j : Int} {c : Cell}
    (hc : (s.handoff cf moved lent).cells j = some c) (ho : c.owner = cf) :
    c.loans = [] ∧ ∃ h ∈ moved, h.slot = j ∧ c = ⟨h.allocation, s.next, cf, []⟩ := by
  rw [handoff_cells, Option.map_eq_some_iff] at hc
  obtain ⟨cell, hs, rfl⟩ := hc
  have hfr := hok.fresh j cell hs
  cases hm : slotIn moved j
  · cases hl : slotIn lent j
    · simp only [handoffCell, hm, hl, Bool.cond_false] at ho; exact absurd ho hfr.1
    · simp only [handoffCell, hm, hl, Bool.cond_false, Bool.cond_true] at ho; exact absurd ho hfr.1
  · obtain ⟨h, hh, he⟩ := slotIn_iff.mp hm
    subst he
    rw [moved_cell hok hh] at hs
    cases hs
    simp only [handoffCell, hm, Bool.cond_true]
    refine ⟨?_, h, hh, rfl, ?_⟩ <;> simp only

end Handoff

section Restore

variable {s s1 s2 : State} {fr cf : Frame} {moved lent : List Handle} {result : Option Handle}

/-- What the callee's checked interface postcondition gives about its
effect: local and progressing, and either no owned allocation is left
(plain output) or exactly the result. -/
structure ReturnOk (s1 s2 : State) (cf : Frame) (result : Option Handle) : Prop where
  valid : s2.valid
  isLocal : s1.local s2 cf
  progress : s1.progress s2
  owned : ∀ j c, s2.cells j = some c → c.owner = cf → ∃ h, result = some h ∧ j = h.slot ∧ c.loans = [] ∧
    c.matches h
  result : ∀ h, result = some h → s2.owns cf h

theorem resultAt_iff {result : Option Handle} {j : Int} :
    resultAt result j = true ↔ ∃ h, result = some h ∧ h.slot = j := by
  cases result <;> simp only [resultAt, Option.any_none, Bool.false_eq_true, reduceCtorEq, false_and, exists_false, Option.any_some, decide_eq_true_eq, Option.some.injEq, exists_eq_left']

theorem restore_cells (j : Int) :
    (s2.restore fr lent result).cells j = (s2.cells j).map (restoreCell s2.next fr lent result j) := rfl

/-- Away from the handed slots the caller gets back exactly what it had. -/
theorem restore_unmoved (hok : HandoffOk s fr cf moved lent)
    (hr : ReturnOk (s.handoff cf moved lent) s2 cf result) {j : Int} {cell : Cell}
    (hs : s.cells j = some cell) (hm : slotIn moved j = false) :
    (s2.restore fr lent result).cells j = some cell := by
  have hfr := hok.fresh j cell hs
  have h1 : (s.handoff cf moved lent).cells j = some (handoffCell s.next cf moved lent j cell) := by
    rw [handoff_cells, hs]; rfl
  have howner : (handoffCell s.next cf moved lent j cell).owner ≠ cf := by
    cases hl : slotIn lent j <;> simp only [handoffCell, hm, hl, cond_eq_ite, Bool.false_eq_true, ↓reduceIte, ne_eq, hfr.1, not_false_eq_true]
  have h2 := hr.isLocal.1 j _ h1 howner
  have hres : resultAt result j = false := by
    cases hra : resultAt result j with
    | false => rfl
    | true =>
      obtain ⟨h, hh, he⟩ := resultAt_iff.mp hra
      have ho := hr.result h hh
      simp only [State.owns, he, h2] at ho
      exact absurd ho.2.1 howner
  rw [restore_cells, h2]
  cases hl : slotIn lent j <;> simp only [handoffCell, hm, hl, cond_eq_ite, Bool.false_eq_true, ↓reduceIte, Option.map_some, restoreCell, hres, List.tail_cons]

/-- A handed allocation the callee did not return is gone. -/
theorem restore_moved (hok : HandoffOk s fr cf moved lent)
    (hr : ReturnOk (s.handoff cf moved lent) s2 cf result) {j : Int}
    (hm : slotIn moved j = true) (hres : resultAt result j = false) :
    (s2.restore fr lent result).cells j = none := by
  rw [restore_cells]
  cases h2 : s2.cells j with
  | none => rfl
  | some c =>
    by_cases ho : c.owner = cf
    · obtain ⟨h, hh, he, _⟩ := hr.owned j c h2 ho
      subst he
      simp only [resultAt, hh, Option.any_some, decide_true, Bool.true_eq_false] at hres
    · obtain ⟨h, hh, he⟩ := slotIn_iff.mp hm
      subst he
      have hback := hr.isLocal.2 h.slot c h2 ho
      rw [handoff_moved hok hh] at hback
      cases hback
      exact absurd rfl ho

/-- A slot that was empty stays empty unless it is the returned result. -/
theorem restore_new (hr : ReturnOk (s.handoff cf moved lent) s2 cf result) {j : Int}
    (hs : s.cells j = none) (hres : resultAt result j = false) :
    (s2.restore fr lent result).cells j = none := by
  rw [restore_cells]
  cases h2 : s2.cells j with
  | none => rfl
  | some c =>
    by_cases ho : c.owner = cf
    · obtain ⟨h, hh, he, _⟩ := hr.owned j c h2 ho
      subst he
      simp only [resultAt, hh, Option.any_some, decide_true, Bool.true_eq_false] at hres
    · have hback := hr.isLocal.2 j c h2 ho
      rw [(handoff_none j).mpr hs] at hback
      cases hback

/-- The returned allocation belongs to the caller under a new grant. -/
theorem restore_result {h : Handle} (hr : ReturnOk s1 s2 cf (some h)) :
    (s2.restore fr lent (some h)).owns fr ⟨h.slot, h.allocation, s2.next⟩ ∧
      (s2.restore fr lent (some h)).cells h.slot = some ⟨h.allocation, s2.next, fr, []⟩ := by
  have ho := hr.result h rfl
  unfold State.owns at ho
  cases h2 : s2.cells h.slot with
  | none => simp only [h2] at ho
  | some c =>
    rw [h2] at ho
    have hc : (s2.restore fr lent (some h)).cells h.slot = some ⟨h.allocation, s2.next, fr, []⟩ := by
      rw [restore_cells, h2]
      simp only [Option.map_some, restoreCell, resultAt, Option.any_some, decide_true, ho.1.1, cond_eq_ite,
  ↓reduceIte]
    exact ⟨by simp only [State.owns, hc, Cell.matches, and_self], hc⟩

theorem restore_valid (hr : ReturnOk s1 s2 cf result) : (s2.restore fr lent result).valid := by
  intro j c hc
  rw [restore_cells, Option.map_eq_some_iff] at hc
  obtain ⟨cell, hs, rfl⟩ := hc
  have hh := hr.valid j cell hs
  cases hra : resultAt result j
  · cases hl : slotIn lent j
    · simp only [restoreCell, hra, hl, Bool.cond_false]
      exact ⟨hh.1, Nat.lt_succ_of_lt hh.2.1, hh.2.2⟩
    · simp only [restoreCell, hra, hl, Bool.cond_false, Bool.cond_true]
      exact ⟨hh.1, Nat.lt_succ_of_lt hh.2.1, hh.2.2.1.sublist (List.tail_sublist _),
        fun hm => hh.2.2.2 (List.mem_of_mem_tail hm)⟩
  · simp only [restoreCell, hra, Bool.cond_true]
    exact ⟨by omega, Nat.lt_succ_self _, List.nodup_nil, by simp only [List.not_mem_nil, not_false_eq_true]⟩

theorem restore_agrees {A : FreiForm D} {σ : World D} (hr : ReturnOk s1 s2 cf result)
    (ha : s2.agrees A σ) : (s2.restore fr lent result).agrees A σ := by
  refine ⟨restore_valid hr, fun i => (ha.2 i).trans ?_⟩
  rw [restore_cells]
  cases s2.cells i <;> simp only [reduceCtorEq, exists_false, Option.map_none, Option.some.injEq, exists_eq', Option.map_some]

/-- The caller's view of the whole call: every allocation of another
activation is untouched, nothing new belongs to another activation, and no
older grant is manufactured. -/
theorem restore_local (hok : HandoffOk s fr cf moved lent)
    (hr : ReturnOk (s.handoff cf moved lent) s2 cf result) :
    s.local (s2.restore fr lent result) fr := by
  constructor
  · intro j cell hs howner
    have hm : slotIn moved j = false := by
      cases hm : slotIn moved j with
      | false => rfl
      | true =>
        obtain ⟨h, hh, he⟩ := slotIn_iff.mp hm
        subst he
        rw [moved_cell hok hh] at hs
        cases hs
        exact absurd rfl howner
    exact restore_unmoved hok hr hs hm
  · intro j c hc howner
    cases hra : resultAt result j with
    | true =>
      obtain ⟨h, hh, he⟩ := resultAt_iff.mp hra
      subst hh he
      rw [(restore_result hr).2] at hc
      cases hc
      exact absurd rfl howner
    | false =>
      cases hs : s.cells j with
      | none => rw [restore_new hr hs hra] at hc; cases hc
      | some cell =>
        cases hm : slotIn moved j with
        | false => rw [restore_unmoved hok hr hs hm] at hc; exact hc
        | true => rw [restore_moved hok hr hm hra] at hc; cases hc

theorem restore_progress (hok : HandoffOk s fr cf moved lent)
    (hr : ReturnOk (s.handoff cf moved lent) s2 cf result) :
    s.progress (s2.restore fr lent result) := by
  have hn : s.next ≤ s2.next := Nat.le_trans (Nat.le_succ _) hr.progress.1
  refine ⟨Nat.le_trans hn (Nat.le_succ _), ?_⟩
  intro j c hc hlt
  cases hra : resultAt result j with
  | true =>
    obtain ⟨h, hh, he⟩ := resultAt_iff.mp hra
    subst hh he
    rw [(restore_result hr).2] at hc
    cases hc
    simp only at hlt
    omega
  | false =>
    cases hs : s.cells j with
    | none => rw [restore_new hr hs hra] at hc; cases hc
    | some cell =>
      cases hm : slotIn moved j with
      | false =>
        rw [restore_unmoved hok hr hs hm] at hc
        cases hc
        exact ⟨c, rfl, rfl, rfl⟩
      | true => rw [restore_moved hok hr hm hra] at hc; cases hc

end Restore

#print axioms handoff_agrees
#print axioms restore_local
#print axioms restore_progress

end Gabbro.Grammatik.ArenaOwnership.Body
