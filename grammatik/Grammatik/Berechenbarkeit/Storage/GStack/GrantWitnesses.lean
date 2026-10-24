import Grammatik.Berechenbarkeit.Storage.GStack.Grants
import Grammatik.Berechenbarkeit.Storage.GStack.Witnesses

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.GrantWitnesses

open ArenaOwnership InvDynZeuge Witnesses

def owner : Frame := ⟨0, 0⟩
def other : Frame := ⟨0, 1⟩

theorem empty_agrees : State.empty.agrees FA initialWorld := by
  refine ⟨State.empty_valid, fun i => ?_⟩
  constructor
  · intro hi
    have hcount : FA.stand initialWorld = 0 := rfl
    have := hi.1
    have := hi.2.1
    omega
  · rintro ⟨cell, hc⟩
    cases hc

/-- Existing cells deliberately belong to another frame, including a live
cell outside the represented chain. All survive recycling the free slot. -/
def reusedRights : State :=
  ⟨3, fun i => if i = 0 then some ⟨0, 0, other, []⟩
    else if i = 2 then some ⟨1, 1, other, []⟩
    else if i = 3 then some ⟨2, 2, other, []⟩ else none⟩

theorem reused_valid : reusedRights.valid := by
  intro i c hc
  change (if i = 0 then some ⟨0, 0, other, []⟩
    else if i = 2 then some ⟨1, 1, other, []⟩
    else if i = 3 then some ⟨2, 2, other, []⟩ else none) = some c at hc
  split at hc
  · cases hc; exact ⟨by decide, by decide, by decide, by decide⟩
  · split at hc
    · cases hc; exact ⟨by decide, by decide, by decide, by decide⟩
    · split at hc
      · cases hc; exact ⟨by decide, by decide, by decide, by decide⟩
      · cases hc

theorem reused_agrees : reusedRights.agrees FA w0 := by
  refine ⟨reused_valid, fun i => ?_⟩
  rw [lebt_w0]
  by_cases hi : i = 0
  · simp [reusedRights, hi]
  · by_cases hj : i = 2
    · simp [reusedRights, hj]
    · by_cases hk : i = 3
      · simp [reusedRights, hk]
      · simp [reusedRights, hi, hj, hk]
        omega

theorem reused_other_owns : reusedRights.owns other ⟨3, 2, 2⟩ := by decide

/-- A joint observation of real code, payloads, free-list safety and grants. -/
def Cycle (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f)
    (allocator : Allocator FA FV false [Payload, Payload] []) (σ : World FD)
    (values : List (Wert FD Payload)) (slot : Int) (s : State) : Prop :=
    ∃ (σ1 σ2 : World FD) (s1 s2 : State) (h : Handle),
      execBlock O passes R
        (Block.pushAllocated allocator LL LG rfl fdarf rfl (fgdarf _) .nil)
        σ initialEnv = .ok σ1 initialEnv ∧
      s.allocate owner slot = some (s1, h) ∧ h.slot = slot ∧
      s1.agrees FA σ1 ∧ s1.owns owner h ∧
      execBlock O passes R
        (Block.popAndRelease LL LG rfl (fgdarf _) rfl fdarf rfl (fgdarf _) failure
          (.cons (.assignVar (.there (.there .here)) (.var .here)) .nil))
        σ1 initialEnv = .ok σ2 (.cons seven (.cons seven .nil)) ∧
      s1.release owner h = some s2 ∧ s2.agrees FA σ2 ∧
      Represents LL LG σ2 values ∧ FA.FreiOk σ2 ∧
      (∀ old : Handle, old.slot = slot → ∀ f, ¬ s2.access f old) ∧
      (∀ i, i ≠ slot → s2.cells i = s.cells i)

/-- Instantiate actual push and pop together, including preservation of
unrelated rights held by another frame. -/
theorem cycle (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f)
    (allocator : Allocator FA FV false [Payload, Payload] []) (σ : World FD)
    (values : List (Wert FD Payload)) (slot : Int) (s : State)
    (ha : s.agrees FA σ) (hr : Represents LL LG σ values)
    (hc : Allocated O passes R FA allocator σ initialEnv seven slot) :
    Cycle O passes R allocator σ values slot s := by
  obtain ⟨σ1, k1, s1, h, hp, hk1, hh, hs1, ha1, ho1, hhead, hr1, hf1⟩ :=
    push_owned O passes R allocator LL LG rfl fdarf rfl (fgdarf _)
      σ initialEnv seven values slot s owner ha hr hc
  obtain ⟨σ2, k2, s2, he, hk2, hs2, ha2, hr2, hf2, halias, hother⟩ :=
    pop_owned O passes R LL LG rfl (fgdarf _) rfl fdarf rfl (fgdarf _) failure
      (.cons (.assignVar (.there (.there .here)) (.var .here)) .nil)
      σ1 initialEnv seven values s1 owner h ha1 ho1 (hh.trans hhead.symm) hr1 hf1
  refine ⟨σ1, σ2, s1, s2, h, hp .nil, hs1, hh, ha1, ho1, he.trans (by rfl), hs2, ha2,
    hr2, hf2, ?_, ?_⟩
  · intro old hold f
    exact halias old (hold.trans hh.symm) f
  · intro i hi
    exact (hother i (fun heq => hi (heq.trans hh))).trans (State.allocate_other hs1 i hi)

theorem fresh_owned_cycle_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    Cycle O passes R fresh initialWorld [] 0 State.empty :=
  cycle O passes R fresh initialWorld [] 0 State.empty empty_agrees empty_contents
    (fresh_allocated O passes R FA (.there .here) rfl fdarf rfl (fgdarf _) failure
      initialWorld initialEnv initial_free (by decide))

theorem reused_owned_cycle_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    Cycle O passes R recycle w0 [zero, zero] 1 reusedRights :=
  cycle O passes R recycle w0 [zero, zero] 1 reusedRights reused_agrees reused_contents
    (reused_allocated O passes R FA (.there .here) rfl fdarf rfl (fgdarf _) failure
      w0 initialEnv freiOk_w0 (by decide))

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.GrantWitnesses
