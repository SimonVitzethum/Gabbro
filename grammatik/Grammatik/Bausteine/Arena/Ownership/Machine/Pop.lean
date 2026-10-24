import Grammatik.Bausteine.Arena.Ownership.Machine.Head
import Grammatik.Bausteine.Arena.Ownership.Body.Forms
import Grammatik.Bausteine.Arena.Ownership.Body.Check.Ops

/-! **The ledger when the running activation returns.** The returning
activation `cf` hands what it owns (at most its owning result) to its caller
`fr` under a new grant, and leaves every loan it holds. Seen from the
caller, nothing else changes: what it had lent to `cf` is again its own,
and no other activation's view moves. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

/-- One cell when `cf` returns to `fr`. -/
def popCell (next : Nat) (cf fr : Frame) (cell : Cell) : Cell :=
  if cell.owner = cf then ⟨cell.allocation, next, fr, []⟩
  else { cell with loans := cell.loans.filter (fun g => decide (g ≠ cf)) }

/-- **The ledger after `cf` returns to `fr`.** -/
def _root_.Gabbro.Grammatik.ArenaOwnership.State.pop (s : State) (cf fr : Frame) : State :=
  ⟨s.next + 1, fun j => (s.cells j).map (popCell s.next cf fr)⟩

namespace Pop

variable {s : State} {cf fr : Frame}

theorem cells (j : Int) : (s.pop cf fr).cells j = (s.cells j).map (popCell s.next cf fr) := rfl

theorem none_iff (j : Int) : (s.pop cf fr).cells j = none ↔ s.cells j = none := by
  rw [cells]; cases s.cells j <;> simp

theorem valid (hv : s.valid) : (s.pop cf fr).valid := by
  intro i c hc
  rw [cells] at hc
  cases hs : s.cells i with
  | none => rw [hs] at hc; cases hc
  | some old =>
    rw [hs] at hc
    simp only [Option.map_some, Option.some.injEq] at hc
    subst hc
    obtain ⟨h1, h2, h3, h4⟩ := hv i old hs
    unfold popCell
    split
    · exact ⟨by show old.allocation ≤ s.next; omega, by show s.next < s.next + 1; omega, List.nodup_nil, by simp⟩
    · refine ⟨h1, by show old.grant < s.next + 1; omega, h3.filter _, fun hm => h4 (List.mem_filter.mp hm).1⟩

theorem progress : s.progress (s.pop cf fr) := by
  refine ⟨Nat.le_succ _, ?_⟩
  intro slot cell hc hlt
  rw [cells] at hc
  cases hs : s.cells slot with
  | none => rw [hs] at hc; cases hc
  | some old =>
    rw [hs] at hc
    simp only [Option.map_some, Option.some.injEq] at hc
    subst hc
    unfold popCell at hlt ⊢
    split at hlt
    · simp at hlt
    · rename_i hne
      simp only [hne, if_false]
      exact ⟨old, rfl, rfl, rfl⟩

theorem agrees {D : Deklaration} {A : FreiForm D} {σ : World D} (ha : s.agrees A σ) :
    (s.pop cf fr).agrees A σ := by
  refine ⟨valid ha.1, fun i => (ha.2 i).trans ?_⟩
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨popCell s.next cf fr c, by rw [cells, hc]; rfl⟩
  · rintro ⟨c, hc⟩
    cases hs : s.cells i with
    | none => rw [cells, hs] at hc; cases hc
    | some old => exact ⟨old, rfl⟩

/-- The thread `t` returns from activation `a + 1` to `a`. -/
def lower (depth : Nat → Nat) (t a : Nat) : Nat → Nat := fun u => if u = t then a else depth u

theorem frame_eq {f g : Frame} (ht : f.thread = g.thread) (ha : f.activation = g.activation) : f = g := by
  cases f; cases g; simp_all

variable {depth : Nat → Nat} {t a : Nat}

/-- **The discipline survives the return.** -/
theorem disciplined (hd : s.Disciplined depth) (hdepth : depth t = a + 1) :
    (s.pop ⟨t, a + 1⟩ ⟨t, a⟩).Disciplined (lower depth t a) := by
  have below : ∀ g : Frame, g.activation ≤ depth g.thread → g ≠ ⟨t, a + 1⟩ →
      g.activation ≤ lower depth t a g.thread := by
    intro g hg hne
    unfold lower
    split
    · rename_i hgt
      rw [hgt, hdepth] at hg
      have : g.activation ≠ a + 1 := fun he => hne (frame_eq hgt he)
      omega
    · exact hg
  intro i c hc
  rw [cells] at hc
  cases hs : s.cells i with
  | none => rw [hs] at hc; cases hc
  | some old =>
    rw [hs] at hc
    simp only [Option.map_some, Option.some.injEq] at hc
    subst hc
    obtain ⟨⟨hdeep, hsort⟩, hown, hloans⟩ := hd i old hs
    unfold popCell
    split
    · refine ⟨⟨by simp, by simp⟩, ?_, by simp⟩
      simp [lower]
    · rename_i hne
      refine ⟨⟨fun g hg => hdeep g ((List.mem_filter.mp hg).1), hsort.filter _⟩, below _ hown hne, ?_⟩
      intro g hg
      have hgne : g ≠ ⟨t, a + 1⟩ := by simpa using (List.mem_filter.mp hg).2
      exact below g (hloans g ((List.mem_filter.mp hg).1)) hgne

/-- **No other activation's view moves.** -/
theorem view_other (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {fr2 : Frame}
    (hne : fr2.thread ≠ t ∨ fr2.activation < a) :
    (s.pop ⟨t, a + 1⟩ ⟨t, a⟩).viewAt fr2 = s.viewAt fr2 := by
  apply View.viewAt_eq
  intro i
  rw [cells]
  cases hs : s.cells i with
  | none => rfl
  | some c =>
    simp only [Option.map_some, Option.bind_some]
    unfold popCell
    split
    · rename_i hcf
      have h1 : ¬ fr2.Sees ⟨c.allocation, s.next, ⟨t, a⟩, []⟩ := by
        rintro ⟨ht, hlt⟩
        simp at ht hlt
        rcases hne with h | h
        · exact h ht.symm
        · omega
      have h2 : ¬ fr2.Sees c := by
        rintro ⟨ht, hlt⟩
        rw [hcf] at ht hlt
        simp at ht hlt
        rcases hne with h | h
        · exact h ht.symm
        · omega
      simp [h1, h2]
    · rename_i hcf
      by_cases hsee : fr2.Sees c
      · have hsee' : fr2.Sees { c with loans := c.loans.filter (fun g => decide (g ≠ ⟨t, a + 1⟩)) } := hsee
        simp only [hsee, hsee', if_true, Option.some.injEq]
        simp only [Cell.at, Cell.mk.injEq, true_and]
        rw [List.filter_filter]
        apply List.filter_congr
        intro g hg
        have hdg := (hd i c hs).1.1 g hg
        by_cases hgcf : g = ⟨t, a + 1⟩
        · subst hgcf
          have hthr : (⟨t, a + 1⟩ : Frame).thread = fr2.thread := hdg.1.trans hsee.1
          have : fr2.Deeper ⟨t, a + 1⟩ := by
            refine ⟨hthr, ?_⟩
            rcases hne with h | h
            · exact absurd hthr.symm h
            · show fr2.activation < a + 1; omega
          simp [this]
        · simp [hgcf]
      · have hsee' : ¬ fr2.Sees { c with loans := c.loans.filter (fun g => decide (g ≠ ⟨t, a + 1⟩)) } := hsee
        rw [if_neg hsee, if_neg hsee']

end Pop

/-! ## The caller, running again -/

namespace Pop

variable {s : State} {depth : Nat → Nat} {t a : Nat}

/-- A cell the caller sees: after the return it is the cell as the caller saw it. -/
theorem pop_at (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {i : Int} {c : Cell}
    (hc : s.cells i = some c) (hsee : (⟨t, a⟩ : Frame).Sees c) :
    popCell s.next ⟨t, a + 1⟩ ⟨t, a⟩ c = c.at ⟨t, a⟩ := by
  have hne : c.owner ≠ ⟨t, a + 1⟩ := by
    intro he; have := hsee.2; rw [he] at this; exact absurd this (by simp)
  unfold popCell
  rw [if_neg hne]
  simp only [Cell.at, Cell.mk.injEq, true_and]
  apply List.filter_congr
  intro g hg
  obtain ⟨hgt, hlt⟩ := (hd i c hc).1.1 g hg
  have hle := (hd i c hc).2.2 g hg
  have ht : g.thread = t := hgt.trans hsee.1
  rw [ht, hdepth] at hle
  by_cases hgcf : g = ⟨t, a + 1⟩
  · subst hgcf
    have : (⟨t, a⟩ : Frame).Deeper ⟨t, a + 1⟩ := ⟨rfl, by simp⟩
    simp [this]
  · have hga : g.activation ≠ a + 1 := fun he => hgcf (frame_eq ht he)
    have : ¬ (⟨t, a⟩ : Frame).Deeper g := by
      rintro ⟨_, h⟩; simp at h; omega
    simp [hgcf, this]

theorem cell_seen (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {i : Int} {c' : Cell}
    (hv : (s.viewAt ⟨t, a⟩).cells i = some c') : (s.pop ⟨t, a + 1⟩ ⟨t, a⟩).cells i = some c' := by
  rw [View.viewAt_cells] at hv
  cases hs : s.cells i with
  | none => rw [hs] at hv; cases hv
  | some c =>
    rw [hs] at hv
    simp only [Option.bind_some] at hv
    split at hv
    · rename_i hsee
      cases hv
      rw [cells, hs]
      simp only [Option.map_some, pop_at hd hdepth hs hsee]
    · cases hv

theorem rights (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {c : Context} {g : Ghost}
    (hr : Rights c g (s.viewAt ⟨t, a⟩) ⟨t, a⟩) : Rights c g (s.pop ⟨t, a + 1⟩ ⟨t, a⟩) ⟨t, a⟩ := by
  refine ⟨fun o m hm => ?_, hr.2⟩
  obtain ⟨h, hg, hp⟩ := hr.1 o m hm
  refine ⟨h, hg, ?_⟩
  have ha := PassingMode.access_of_permits hp
  unfold State.access at ha
  cases hv : (s.viewAt ⟨t, a⟩).cells h.slot with
  | none => rw [hv] at ha; exact ha.elim
  | some c' => exact PassingMode.permits_same_cell ((cell_seen hd hdepth hv).trans hv.symm) hp

/-- The caller's cells after the return: the handed-back allocation, or as the caller saw them. -/
theorem owned_cells (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {j : Int} {cell : Cell}
    (hc : (s.pop ⟨t, a + 1⟩ ⟨t, a⟩).cells j = some cell) (ho : cell.owner = ⟨t, a⟩) :
    (∃ old, s.cells j = some old ∧ old.owner = ⟨t, a + 1⟩ ∧ cell = ⟨old.allocation, s.next, ⟨t, a⟩, []⟩) ∨
      (s.viewAt ⟨t, a⟩).cells j = some cell := by
  rw [cells] at hc
  cases hs : s.cells j with
  | none => rw [hs] at hc; cases hc
  | some old =>
    rw [hs] at hc
    simp only [Option.map_some, Option.some.injEq] at hc
    by_cases hcf : old.owner = ⟨t, a + 1⟩
    · left
      refine ⟨old, rfl, hcf, ?_⟩
      rw [← hc]; unfold popCell; rw [if_pos hcf]
    · right
      have hsee : (⟨t, a⟩ : Frame).Sees old := by
        have : cell.owner = old.owner := by rw [← hc]; unfold popCell; rw [if_neg hcf]
        show old.owner.thread = t ∧ old.owner.activation ≤ a
        rw [← this, ho]; exact ⟨rfl, Nat.le_refl _⟩
      rw [View.viewAt_cells, hs]
      simp only [Option.bind_some, if_pos hsee]
      rw [← hc, pop_at hd hdepth hs hsee]

/-- **A caller whose callee returned nothing it owned.** -/
theorem frame_plain {D : Deklaration} (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {c : Context}
    {g : Ghost} {Γ : Ctx} {ρ : Env D Γ} (hf : FrameOk c g (s.viewAt ⟨t, a⟩) ⟨t, a⟩ ρ)
    (hclosed : s.closed ⟨t, a + 1⟩) : FrameOk c g (s.pop ⟨t, a + 1⟩ ⟨t, a⟩) ⟨t, a⟩ ρ := by
  refine ⟨hf.1, hf.2.1, rights hd hdepth hf.2.2.1, ?_⟩
  intro j cell hc ho
  rcases owned_cells hd hdepth hc ho with ⟨old, hs, hcf, _⟩ | hv
  · exact absurd hcf (hclosed j old hs)
  · exact hf.2.2.2 j cell hv ho

/-- The allocation an owning callee hands back. -/
def handBack (s : State) (h : Handle) : Handle := ⟨h.slot, h.allocation, s.next⟩

theorem owns_handBack (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {h : Handle}
    (ho : s.owns ⟨t, a + 1⟩ h) : (s.pop ⟨t, a + 1⟩ ⟨t, a⟩).owns ⟨t, a⟩ (handBack s h) := by
  obtain ⟨old, hs⟩ := State.own_cell ho
  have hm := State.owned_cell ho hs
  simp only [State.owns, handBack, cells, hs, Option.map_some]
  unfold popCell
  rw [if_pos hm.2.1]
  exact ⟨⟨hm.1.1, rfl⟩, rfl, rfl⟩

theorem disjoint_handBack (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {c : Context} {g : Ghost}
    (hr : Rights c g (s.viewAt ⟨t, a⟩) ⟨t, a⟩) {h : Handle} (ho : s.owns ⟨t, a + 1⟩ h) :
    ∀ i mode old, c.rights i = some mode → g i = some old → old.slot ≠ (handBack s h).slot := by
  intro i mode old hi hg he
  obtain ⟨h', hg', hp⟩ := hr.1 i mode hi
  rw [hg] at hg'; cases hg'
  have ha := PassingMode.access_of_permits hp
  unfold State.access at ha
  obtain ⟨cell, hs⟩ := State.own_cell ho
  have hm := State.owned_cell ho hs
  simp only [handBack] at he
  rw [he, View.viewAt_cells, hs] at ha
  by_cases hsee : (⟨t, a⟩ : Frame).Sees cell
  · have := hsee.2; rw [hm.2.1] at this; exact absurd this (by simp)
  · simp [hsee] at ha

theorem complete_handBack (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {c : Context} {g : Ghost}
    (hb : c.bounded) (hc : Complete c g (s.viewAt ⟨t, a⟩) ⟨t, a⟩) {h : Handle} (ho : s.owns ⟨t, a + 1⟩ h)
    (hsingle : s.single ⟨t, a + 1⟩ h) :
    Complete c.bindFresh (g.set c.next (handBack s h)) (s.pop ⟨t, a + 1⟩ ⟨t, a⟩) ⟨t, a⟩ := by
  apply Complete.bindOwning hb (owns_handBack hd hdepth ho)
  intro slot cell h3 howner hne
  rcases owned_cells hd hdepth h3 howner with ⟨old, hs, hcf, _⟩ | hv
  · exact absurd (hsingle slot old hs hcf).1 hne
  · exact hc slot cell hv howner

/-- **A caller whose callee handed back an allocation**, bound under a new origin. -/
theorem frame_owner {D : Deklaration} (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {c : Context}
    {g : Ghost} {Γ : Ctx} {τ : Ty} {ρ : Env D Γ} (hf : FrameOk c g (s.viewAt ⟨t, a⟩) ⟨t, a⟩ ρ) {h : Handle}
    (ho : s.owns ⟨t, a + 1⟩ h) (hsingle : s.single ⟨t, a + 1⟩ h) (v : Wert D τ) (hv : intVon τ v = some h.slot) :
    FrameOk c.bindFresh (g.set c.next (handBack s h)) (s.pop ⟨t, a + 1⟩ ⟨t, a⟩) ⟨t, a⟩ (.cons v ρ) := by
  refine ⟨Context.bindFresh_bounded hf.1, ?_,
    extend_rights (rights hd hdepth hf.2.2.1) (owns_handBack hd hdepth ho) (disjoint_handBack hd hdepth hf.2.2.1 ho),
    complete_handBack hd hdepth hf.1 hf.2.2.2 ho hsingle⟩
  have href' := References.setFresh hf.1 hf.2.1 (handBack s h)
  change References (c.bind (some c.next)) (g.set c.next (handBack s h)) (.cons v ρ)
  apply References.bind href' v (some c.next)
  intro i hi
  cases hi
  exact ⟨handBack s h, Ghost.set_at g c.next _, hv⟩

/-- … with the result discarded. -/
theorem frame_ownerDrop {D : Deklaration} (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {c : Context}
    {g : Ghost} {Γ : Ctx} {ρ : Env D Γ} (hf : FrameOk c g (s.viewAt ⟨t, a⟩) ⟨t, a⟩ ρ) {h : Handle}
    (ho : s.owns ⟨t, a + 1⟩ h) (hsingle : s.single ⟨t, a + 1⟩ h) :
    FrameOk c.bindFresh.drop (g.set c.next (handBack s h)) (s.pop ⟨t, a + 1⟩ ⟨t, a⟩) ⟨t, a⟩ ρ := by
  refine ⟨Body.Context.drop_bounded (Context.bindFresh_bounded hf.1), ?_,
    extend_rights (rights hd hdepth hf.2.2.1) (owns_handBack hd hdepth ho) (disjoint_handBack hd hdepth hf.2.2.1 ho),
    complete_handBack hd hdepth hf.1 hf.2.2.2 ho hsingle⟩
  have href' := References.setFresh hf.1 hf.2.1 (handBack s h)
  have hrefs : c.bindFresh.drop.references = c.references := by
    simp [Context.bindFresh, Context.drop]
  exact ⟨by rw [hrefs]; exact href'.1, fun x i hi => href'.2 x i (by
    simp only [Context.reference, hrefs] at hi ⊢; exact hi)⟩

end Pop

end Gabbro.Grammatik.ArenaOwnership.Machine
