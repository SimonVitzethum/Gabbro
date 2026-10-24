import Grammatik.Bausteine.Arena.Ownership.Machine.Pop
import Grammatik.Bausteine.Arena.Ownership.Body.Call

/-! **The ledger at a call.** The running activation `fr` of thread `t` at
depth `a` calls; the callee runs at depth `a + 1`, an activation the
disciplined ledger does not name. Owning arguments move to the callee
under new grants, borrowed ones are lent to it. Seen from the caller,
only what it handed over is gone; no other activation's view moves. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

namespace Push

variable {s : State} {depth : Nat → Nat} {t a : Nat} {moved lent : List Handle}

/-- **The next depth is fresh.** -/
theorem fresh (hd : s.Disciplined depth) (hdepth : depth t = a) :
    ∀ j cell, s.cells j = some cell → cell.owner ≠ ⟨t, a + 1⟩ ∧ (⟨t, a + 1⟩ : Frame) ∉ cell.loans := by
  intro j cell hc
  obtain ⟨_, hown, hloans⟩ := hd j cell hc
  refine ⟨fun he => ?_, fun hm => ?_⟩
  · rw [he, hdepth] at hown; exact absurd hown (by simp)
  · have := hloans _ hm; simp only at this; rw [hdepth] at this; omega

theorem holder_thread {c : Cell} (ho : c.Ordered) {fr : Frame} (hh : c.holder = fr) :
    c.owner.thread = fr.thread ∧ c.owner.activation ≤ fr.activation := by
  cases hl : c.loans with
  | nil => simp [Cell.holder, hl] at hh; rw [hh]; exact ⟨rfl, Nat.le_refl _⟩
  | cons g rest =>
    simp [Cell.holder, hl] at hh
    have := ho.1 g (by rw [hl]; exact List.mem_cons_self)
    subst hh
    exact ⟨this.1.symm, Nat.le_of_lt this.2⟩

/-- **The discipline survives the call.** -/
theorem disciplined (hd : s.Disciplined depth) (hdepth : depth t = a)
    (hok : HandoffOk s ⟨t, a⟩ ⟨t, a + 1⟩ moved lent) :
    (s.handoff ⟨t, a + 1⟩ moved lent).Disciplined (Pop.lower depth t (a + 1)) := by
  have mono : ∀ u, depth u ≤ Pop.lower depth t (a + 1) u := by
    intro u; unfold Pop.lower; split
    · rename_i h; rw [h, hdepth]; omega
    · exact Nat.le_refl _
  intro j c hc
  rw [handoff_cells, Option.map_eq_some_iff] at hc
  obtain ⟨cell, hs, rfl⟩ := hc
  obtain ⟨⟨hdeep, hsort⟩, hown, hloans⟩ := hd j cell hs
  cases hm : slotIn moved j
  · cases hl : slotIn lent j
    · simp only [handoffCell, hm, hl, Bool.cond_false]
      exact ⟨⟨hdeep, hsort⟩, Nat.le_trans hown (mono _), fun g hg => Nat.le_trans (hloans g hg) (mono _)⟩
    · simp only [handoffCell, hm, hl, Bool.cond_false, Bool.cond_true]
      obtain ⟨k, hk, hks⟩ := slotIn_iff.mp hl
      obtain ⟨cell', hc', _, hh⟩ := lent_cell hok hk
      rw [hks, hs] at hc'
      cases hc'
      obtain ⟨hth, hact⟩ := holder_thread ⟨hdeep, hsort⟩ hh
      have hot : cell.owner.activation ≤ a := by
        have := hown; rw [hth, hdepth] at this; exact this
      have hloansa : ∀ g ∈ cell.loans, g.activation ≤ a := by
        intro g hg
        have := hloans g hg
        rw [(hdeep g hg).1, hth, hdepth] at this
        exact this
      refine ⟨⟨?_, ?_⟩, Nat.le_trans hown (mono _), ?_⟩
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨hth.symm, by simp; omega⟩
        · exact hdeep g hg
      · refine List.Pairwise.cons (fun b hb => ?_) hsort
        have := hloansa b hb; simp; omega
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · simp [Pop.lower]
        · exact Nat.le_trans (hloans g hg) (mono _)
  · simp only [handoffCell, hm, Bool.cond_true]
    exact ⟨⟨by simp, by simp⟩, by simp [Pop.lower], by simp⟩

/-- **No view below or beside the caller moves.** -/
theorem view_other (hd : s.Disciplined depth) (hdepth : depth t = a)
    (hok : HandoffOk s ⟨t, a⟩ ⟨t, a + 1⟩ moved lent) {fr2 : Frame}
    (hne : fr2.thread ≠ t ∨ fr2.activation < a) :
    (s.handoff ⟨t, a + 1⟩ moved lent).viewAt fr2 = s.viewAt fr2 := by
  apply View.viewAt_eq
  intro j
  rw [handoff_cells]
  cases hs : s.cells j with
  | none => rfl
  | some cell =>
    simp only [Option.map_some, Option.bind_some]
    cases hm : slotIn moved j
    · cases hl : slotIn lent j
      · simp only [handoffCell, hm, hl, Bool.cond_false]
      · simp only [handoffCell, hm, hl, Bool.cond_false, Bool.cond_true]
        by_cases hsee : fr2.Sees cell
        · have hsee' : fr2.Sees { cell with loans := ⟨t, a + 1⟩ :: cell.loans } := hsee
          rw [if_pos hsee, if_pos hsee']
          obtain ⟨k, hk, hks⟩ := slotIn_iff.mp hl
          obtain ⟨cell', hc', _, hh⟩ := lent_cell hok hk
          rw [hks, hs] at hc'
          cases hc'
          have hth := (holder_thread (hd j cell hs).1 hh).1
          have hdeep : fr2.Deeper ⟨t, a + 1⟩ := by
            refine ⟨hth.symm.trans hsee.1, ?_⟩
            rcases hne with h | h
            · exact absurd (hth.symm.trans hsee.1).symm h
            · simp; omega
          simp [Cell.at, hdeep]
        · have hsee' : ¬ fr2.Sees { cell with loans := ⟨t, a + 1⟩ :: cell.loans } := hsee
          rw [if_neg hsee, if_neg hsee']
    · simp only [handoffCell, hm, Bool.cond_true]
      obtain ⟨h, hh, hhs⟩ := slotIn_iff.mp hm
      have hmc := moved_cell hok hh
      rw [hhs, hs] at hmc
      cases hmc
      have h1 : ¬ fr2.Sees ⟨h.allocation, s.next, ⟨t, a + 1⟩, []⟩ := by
        rintro ⟨ht, hlt⟩
        simp at ht hlt
        rcases hne with hn | hn
        · exact hn ht.symm
        · omega
      have h2 : ¬ fr2.Sees ⟨h.allocation, h.grant, ⟨t, a⟩, []⟩ := by
        rintro ⟨ht, hlt⟩
        simp at ht hlt
        rcases hne with hn | hn
        · exact hn ht.symm
        · omega
      rw [if_neg h1, if_neg h2]

/-- **The caller's view after the call**: what it handed over is gone, nothing else moves. -/
theorem view_caller (hok : HandoffOk s ⟨t, a⟩ ⟨t, a + 1⟩ moved lent) (j : Int) :
    ((s.handoff ⟨t, a + 1⟩ moved lent).viewAt ⟨t, a⟩).cells j =
      if slotIn moved j then none else (s.viewAt ⟨t, a⟩).cells j := by
  rw [View.viewAt_cells, View.viewAt_cells, handoff_cells]
  cases hs : s.cells j with
  | none => split <;> rfl
  | some cell =>
    simp only [Option.map_some, Option.bind_some]
    cases hm : slotIn moved j
    · cases hl : slotIn lent j
      · simp only [handoffCell, hm, hl, Bool.cond_false, Bool.false_eq_true, if_false]
      · simp only [handoffCell, hm, hl, Bool.cond_false, Bool.cond_true, Bool.false_eq_true, if_false]
        have hsee : ((⟨t, a⟩ : Frame).Sees { cell with loans := ⟨t, a + 1⟩ :: cell.loans }) ↔
            (⟨t, a⟩ : Frame).Sees cell := Iff.rfl
        have hdeep : (⟨t, a⟩ : Frame).Deeper ⟨t, a + 1⟩ := ⟨rfl, by simp⟩
        by_cases h : (⟨t, a⟩ : Frame).Sees cell
        · rw [if_pos (hsee.mpr h), if_pos h]
          simp [Cell.at, hdeep]
        · rw [if_neg (fun h' => h (hsee.mp h')), if_neg h]
    · simp only [handoffCell, hm, Bool.cond_true, if_true]
      have : ¬ (⟨t, a⟩ : Frame).Sees ⟨cell.allocation, s.next, ⟨t, a + 1⟩, []⟩ := by
        rintro ⟨_, hlt⟩; exact absurd hlt (by simp)
      rw [if_neg this]

/-! ## The two activations after the call -/

section Frames

variable {D : Deklaration} {A : FreiForm D} {c : Context} {g : Ghost} {σ : World D} {Γ : Ctx} {ρ : Env D Γ}
  {ms : List (Option PassingMode)} {os : List (Option Nat)}

/-- What the caller kept is not handed over. -/
theorem unmoved (hR : Realizes c g A ⟨t, a⟩ s σ ρ) (hp : planFits c ms os = true) {j : Nat} {m : PassingMode}
    {h : Handle} (hcj : c.rights j = some m) (hcons : consumes ms os j = false) (hg : g j = some h) :
    slotIn (movedHandles g ms os) h.slot = false := by
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
    exact absurd hks (hR.2.2.2.2.2 i j .owned m (hown rfl) hcj hij (Or.inl rfl) k h hgk hg)

/-- **The caller, suspended at the call**, over the ledger it sees. -/
theorem caller_frame (hd : s.Disciplined depth) (hdepth : depth t = a) (hR : Realizes c g A ⟨t, a⟩ s σ ρ)
    (hc : Complete c g s ⟨t, a⟩) (hp : planFits c ms os = true) :
    FrameOk (c.afterCall ms os) g
      ((s.handoff ⟨t, a + 1⟩ (movedHandles g ms os) (lentHandles g ms os)).viewAt ⟨t, a⟩) ⟨t, a⟩ ρ := by
  have hok := handoff_ok_at hR hp ⟨t, a + 1⟩ (fresh hd hdepth)
  have hrun : View.Running depth ⟨t, a⟩ := hdepth.symm
  refine ⟨afterCall_bounded hR.2.2.1, hR.2.2.2.1, ⟨fun j m hj => ?_, fun i j p q hi hj hne hown h k hgi hgj =>
    hR.2.2.2.2.2 i j p q (afterCall_rights_sub hi).1 (afterCall_rights_sub hj).1 hne hown h k hgi hgj⟩, ?_⟩
  · obtain ⟨hcj, hcons⟩ := afterCall_rights_sub hj
    obtain ⟨h, hg, hperm⟩ := hR.2.2.2.2.1 j m hcj
    refine ⟨h, hg, PassingMode.permits_same_cell ?_ ((View.permits_running hd hrun m h).mpr hperm)⟩
    rw [view_caller hok, unmoved hR hp hcj hcons hg]
    rfl
  · intro slot cell h3 howner
    rw [view_caller hok] at h3
    cases hm : slotIn (movedHandles g ms os) slot with
    | true => rw [hm] at h3; cases h3
    | false =>
      rw [hm] at h3
      simp only [Bool.false_eq_true, if_false] at h3
      obtain ⟨hloans, i, h, hi, hg, hslot, hmatch⟩ := (View.complete_running hd hrun).mpr hc slot cell h3 howner
      refine ⟨hloans, i, h, ?_, hg, hslot, hmatch⟩
      rw [afterCall_rights]
      cases hcons : consumes ms os i with
      | false => exact hi
      | true =>
        obtain ⟨u, hmu, hou⟩ := consumes_iff.mp hcons
        have hmoved := moved_of hmu hou hg
        rw [← hslot, slotIn_of_mem hmoved] at hm
        cases hm

/-- **The callee, running at its entry.** -/
theorem callee_frame {Λ : List (Res D)} {params : Ctx} (modes : Modes params) (args : Args D Γ Λ params)
    (hms : modeList modes = ms) (hos : originList c args = os) (hd : s.Disciplined depth) (hdepth : depth t = a)
    (hR : Realizes c g A ⟨t, a⟩ s σ ρ) (hp : planFits c ms os = true) (σa σb : World D) :
    FrameOk (Flow.parameterContext modes) (calleeGhost g ms os s.next)
      (s.handoff ⟨t, a + 1⟩ (movedHandles g ms os) (lentHandles g ms os)) ⟨t, a + 1⟩ (evalArgs σa args σb ρ) :=
  ⟨Flow.parameterContext_bounded modes, handoff_requires_at modes args hms hos hR hp σa σb _ (fresh hd hdepth)⟩

end Frames

end Push

end Gabbro.Grammatik.ArenaOwnership.Machine
