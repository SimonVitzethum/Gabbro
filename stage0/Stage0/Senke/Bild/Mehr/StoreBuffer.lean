module

public import Runner.Mach.TSO
public import Stage0.Senke.Bild.Mehr.Lokal

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.Beweis Runner.Mach

/-- Applying the same pending stores preserves agreement on every address
    already shared by the two memory views. -/
theorem buffers_agree {region : W → Prop} {before after : Mem}
    (stores : List (W × W)) (agree : GleichAuf region before after) :
    GleichAuf region
      (stores.foldl (fun m store => Mem.write m store.1 8 store.2.toNat) before)
      (stores.foldl (fun m store => Mem.write m store.1 8 store.2.toNat) after) := by
  induction stores generalizing before after with
  | nil => exact agree
  | cons store rest ih =>
    simp only [List.foldl_cons]
    apply ih
    intro address member
    have same := agree address member
    refine ⟨?_, same.2.1, same.2.2⟩
    simp only [Mem.write]
    split
    · rfl
    · exact same.1

/-- Flushing a private store preserves the writer's entire view and every
    other thread's view on its footprint. -/
theorem tso_flush_preserves_views {layout : Lay} {before after : (TSO layout).St}
    (flush : (TSO layout).tau before after) (footprint : Nat → W → Prop)
    (disjoint : ∀ i store, store ∈ before.1.buf i →
      ∀ j, j ≠ i → ∀ address, footprint j address → ¬ fenster store.1 address) :
    ∀ j, GleichAuf (footprint j) (after.1.view j) (before.1.view j) := by
  obtain ⟨i, address, value, tail, head, drained⟩ := flush
  intro j
  rw [drained]
  by_cases same : j = i
  · subst j
    simp only [TSt.view, TSt.setBuf, if_pos rfl, head, List.foldl_cons]
    exact fun y _ => GleichAt.refl _ y
  · simp only [TSt.view, TSt.setBuf, if_neg same]
    apply buffers_agree
    intro y member
    have pending : (address, value) ∈ before.1.buf i := by
      rw [head]
      exact List.mem_cons_self
    have outside := disjoint i (address, value) pending j same y member
    exact (write_nurIn before.1.m address value.toNat).gleichAt outside

/-- An enqueued store changes the issuer's view just like an immediate
    store and leaves every other view intact until a flush. -/
theorem tso_store_updates_view {layout : Lay} {before after : (TSO layout).St}
    {i : Nat} {address value : W} {answer : Ans}
    (step : (TSO layout).ans before i (.wr address value) answer after) :
    (answer = none ∧ after = before) ∨
      (answer = some (0, 0) ∧
        after.1.view i = Mem.write (before.1.view i) address 8 value.toNat ∧
        ∀ j, j ≠ i → after.1.view j = before.1.view j) := by
  rcases step with ⟨_, refused, same⟩ | ⟨_, accepted, enqueued⟩
  · exact Or.inl ⟨refused, same⟩
  · refine Or.inr ⟨accepted, ?_, ?_⟩
    · rw [enqueued]
      simp only [TSt.view, TSt.setBuf, if_pos rfl, ↓reduceIte, List.foldl_append, List.foldl_cons, List.foldl_nil]
    · intro j different
      rw [enqueued]
      simp only [TSt.view, TSt.setBuf, if_neg different]

/-- At a private read, interpreting the request on the local memory view
    supplies precisely the data used by a read-blind continuation. -/
theorem tso_private_read {layout : Lay} {before after : (TSO layout).St}
    {i width : Nat} {address : W} {answer : Ans} {localView : Mem}
    {resume : Ans → Res IR.T}
    (step : (TSO layout).ans before i (.rd width address) answer after)
    (agree : GleichAuf (fenster address) (before.1.view i) localView)
    (blind : ∀ value extra, resume (some (value, extra)) = resume (some (value, 0))) :
    after = before ∧ resume answer = resume ((rdN localView width address).map (·, 0)) := by
  obtain ⟨same, extra, rfl⟩ := step
  refine ⟨same, ?_⟩
  have read : rdN (before.1.view i) width address = rdN localView width address := by
    unfold rdN
    split
    · rw [gleich_rd8 agree]
    · rw [gleich_rd32 agree]
    · exact gleich_rd64 agree
    · rfl
  rw [read]
  cases rdN localView width address with
  | none => rfl
  | some value => exact blind value extra

/-- A compare-and-swap needs a drained issuing thread. Its answer and next
    visible memory are then exactly the ones computed by the IR memory. -/
theorem tso_cas_updates_view {layout : Lay} {before after : (TSO layout).St}
    {i : Nat} {address expected replacement : W} {answer : Ans}
    (step : (TSO layout).ans before i (.cas address expected replacement) answer after) :
    before.1.buf i = [] ∧
      IR.memAns (before.1.view i) (.cas address expected replacement) =
        some (answer, after.1.view i) := by
  obtain ⟨empty, outcome⟩ := step
  have original : before.1.view i = before.1.m := by
    simp only [TSt.view, empty, List.foldl_nil]
  refine ⟨empty, ?_⟩
  rcases outcome with ⟨refused, rfl, rfl⟩ | ⟨old, changed, accepted, rfl, state⟩
  · rw [original, memAns_cas, refused]
  · rw [original, memAns_cas, accepted, state]
    simp only [TSt.view, empty, List.foldl_nil]

end Gabbro.Stage0.Senke.BildMehr
