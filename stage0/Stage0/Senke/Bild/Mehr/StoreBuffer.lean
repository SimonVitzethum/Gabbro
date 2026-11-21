module

public import Runner.Mach.TSO
public import Stage0.Senke.Bild.Mehr.Lokal

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.Beweis Runner.Mach

private theorem write_agrees {before after : Mem} {address base : W} (value : Nat)
    (same : GleichAt before after address) :
    GleichAt (Mem.write before base 8 value) (Mem.write after base 8 value) address := by
  refine ⟨?_, same.2.1, same.2.2⟩
  simp only [Mem.write]
  split
  · rfl
  · exact same.1

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
    exact write_agrees store.2.toNat (agree address member)

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

private theorem rdN_agrees {before after : Mem} {address : W} (width : Nat)
    (agree : GleichAuf (fenster address) before after) :
    rdN before width address = rdN after width address := by
  unfold rdN
  split
  · rw [gleich_rd8 agree]
  · rw [gleich_rd32 agree]
  · exact gleich_rd64 agree
  · rfl

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
  rw [rdN_agrees width agree]
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

/-- Pending stores that miss an address leave the byte and its permissions
    equal to committed memory. -/
theorem view_agrees_at {state : TSt} {i : Nat} {address : W}
    (outside : ∀ store ∈ state.buf i, ¬ fenster store.1 address) :
    GleichAt (state.view i) state.m address := by
  have far : ∀ store ∈ state.buf i, ∀ offset, offset < 8 →
      address ≠ store.1 + BitVec.ofNat 64 offset := by
    intro store present offset width same
    apply outside store present
    rw [same]
    exact fenster_add store.1 width
  obtain ⟨byte, readable⟩ := foldl_far (state.buf i) state.m far
  exact ⟨byte, readable, congrFun (foldl_wr (state.buf i) state.m) address⟩

/-- Select the memory supplying one address in the common view. -/
noncomputable def viewAt (state : TSt) (footprint : Nat → W → Prop) (address : W) : Mem := by
  classical
  exact if visible : ∃ i, footprint i address then state.view (Classical.choose visible) else state.m

/-- A common view keeps committed bytes outside every footprint. On a
    footprint it uses one thread's visible byte and permissions. -/
noncomputable def mergedView (state : TSt) (footprint : Nat → W → Prop) : Mem where
  b y := (viewAt state footprint y).b y
  rd y := (viewAt state footprint y).rd y
  wr y := (viewAt state footprint y).wr y

/-- With disjoint pending stores, the common view agrees with each thread
    on its private footprint, even when read-only parts overlap. -/
theorem tso_views_merge (state : TSt) (footprint : Nat → W → Prop)
    (disjoint : ∀ i store, store ∈ state.buf i →
      ∀ j, j ≠ i → ∀ address, footprint j address → ¬ fenster store.1 address) :
    ∀ i, GleichAuf (footprint i) (mergedView state footprint) (state.view i) := by
  intro i address present
  change GleichAt (viewAt state footprint address) (state.view i) address
  let visible : ∃ thread, footprint thread address := ⟨i, present⟩
  rw [show viewAt state footprint address = state.view (Classical.choose visible) from dif_pos visible]
  let other := Classical.choose visible
  have represented : footprint other address := Classical.choose_spec visible
  by_cases same : other = i
  · change GleichAt (state.view other) (state.view i) address
    rw [same]
    exact GleichAt.refl _ _
  · exact (view_agrees_at (fun store member =>
      disjoint other store member i (Ne.symm same) address present)).trans
      ((view_agrees_at (fun store member =>
        disjoint i store member other same address represented)).symm)

/-- The projected memory retains the runner's dispatch table. Each visible
    view and committed memory already agree on those read-only bytes. -/
theorem mergedView_table {layout : Lay} (state : (TSO layout).St)
    (footprint : Nat → W → Prop) : TabInv layout (mergedView state.1 footprint) := by
  intro row rowBound offset offsetBound
  let address := taddr layout (BitVec.ofNat 64 row) + BitVec.ofNat 64 offset
  change (viewAt state.1 footprint address).b address = _ ∧
    (viewAt state.1 footprint address).rd address = true ∧
    (viewAt state.1 footprint address).wr address = false
  by_cases visible : ∃ i, footprint i address
  · rw [show viewAt state.1 footprint address = state.1.view (Classical.choose visible) from dif_pos visible]
    exact view_table state.2 (Classical.choose visible) rowBound offset offsetBound
  · rw [show viewAt state.1 footprint address = state.1.m from dif_neg visible]
    exact state.2.1 row rowBound offset offsetBound

private theorem mem_eq_of_agreement {before after : Mem}
    (same : ∀ address, GleichAt before after address) : before = after := by
  have bytes := funext (fun address => (same address).1)
  have readable := funext (fun address => (same address).2.1)
  have writable := funext (fun address => (same address).2.2)
  cases before
  cases after
  cases bytes
  cases readable
  cases writable
  rfl

/-- A private buffer flush projects to no memory step. Ownership keeps
    the flushed bytes inside the writer's footprint. -/
theorem mergedView_flush {layout : Lay} {before after : (TSO layout).St}
    (flush : (TSO layout).tau before after) (footprint : Nat → W → Prop)
    (inside : ∀ i store, store ∈ before.1.buf i →
      ∀ address, fenster store.1 address → footprint i address)
    (disjoint : ∀ i store, store ∈ before.1.buf i →
      ∀ j, j ≠ i → ∀ address, footprint j address → ¬ fenster store.1 address) :
    mergedView after.1 footprint = mergedView before.1 footprint := by
  apply mem_eq_of_agreement
  intro address
  change GleichAt (viewAt after.1 footprint address) (viewAt before.1 footprint address) address
  by_cases visible : ∃ i, footprint i address
  · simp only [viewAt, dif_pos visible]
    exact tso_flush_preserves_views flush footprint disjoint _ address (Classical.choose_spec visible)
  · simp only [viewAt, dif_neg visible]
    obtain ⟨i, base, value, tail, head, drained⟩ := flush
    have pending : (base, value) ∈ before.1.buf i := by
      rw [head]
      exact List.mem_cons_self
    rw [drained]
    exact (write_nurIn before.1.m base value.toNat).gleichAt
      (fun touched => visible ⟨i, inside i (base, value) pending address touched⟩)

/-- The common view is a well-formed state of the runner's SC model. -/
noncomputable def projectSCState {layout : Lay} (footprint : Nat → W → Prop)
    (state : (TSO layout).St) : (SC layout).St :=
  ⟨mergedView state.1 footprint, mergedView_table state footprint⟩

/-- A private TSO flush has no visible step in the SC projection. -/
theorem projectSCState_flush {layout : Lay} {before after : (TSO layout).St}
    (flush : (TSO layout).tau before after) (footprint : Nat → W → Prop)
    (inside : ∀ i store, store ∈ before.1.buf i →
      ∀ address, fenster store.1 address → footprint i address)
    (disjoint : ∀ i store, store ∈ before.1.buf i →
      ∀ j, j ≠ i → ∀ address, footprint j address → ¬ fenster store.1 address) :
    projectSCState footprint after = projectSCState footprint before :=
  Subtype.ext (mergedView_flush flush footprint inside disjoint)

/-- Every permitted private TSO read is also a read of the SC projection
    with the same answer. -/
theorem projectSCState_read {layout : Lay} {before after : (TSO layout).St}
    {i width : Nat} {address : W} {answer : Ans}
    (read : (TSO layout).ans before i (.rd width address) answer after)
    (footprint : Nat → W → Prop)
    (inside : ∀ y, fenster address y → footprint i y)
    (disjoint : ∀ thread store, store ∈ before.1.buf thread →
      ∀ other, other ≠ thread → ∀ y, footprint other y → ¬ fenster store.1 y) :
    (SC layout).ans (projectSCState footprint before) i (.rd width address) answer
      (projectSCState footprint after) := by
  obtain ⟨same, extra, result⟩ := read
  have agree : GleichAuf (fenster address) (before.1.view i) (mergedView before.1 footprint) :=
    fun y member => (tso_views_merge before.1 footprint disjoint i y (inside y member)).symm
  refine ⟨congrArg (projectSCState footprint) same, extra, ?_⟩
  exact result.trans (congrArg (fun bytes : Option W => bytes.map (·, extra)) (rdN_agrees width agree))

private theorem mergedView_wr (state : TSt) (footprint : Nat → W → Prop) :
    (mergedView state footprint).wr = state.m.wr := by
  funext address
  change (viewAt state footprint address).wr address = state.m.wr address
  by_cases visible : ∃ i, footprint i address
  · simp only [viewAt, dif_pos visible, TSt.view, foldl_wr]
  · simp only [viewAt, dif_neg visible]

private theorem merging_a_store {before after : TSt} (footprint : Nat → W → Prop)
    (i : Nat) (address value : W)
    (owns : ∀ y, fenster address y → footprint i y ∧ ∀ j, footprint j y → j = i)
    (committed : ∀ y, ¬ fenster address y → GleichAt after.m before.m y)
    (issued : after.view i = Mem.write (before.view i) address 8 value.toNat)
    (others : ∀ j, j ≠ i → GleichAuf (footprint j) (after.view j) (before.view j)) :
    mergedView after footprint = Mem.write (mergedView before footprint) address 8 value.toNat := by
  apply mem_eq_of_agreement
  intro y
  by_cases visible : ∃ j, footprint j y
  · let j := Classical.choose visible
    have atThread (state : TSt) : GleichAt (mergedView state footprint) (state.view j) y := by
      change GleichAt (viewAt state footprint y) (state.view j) y
      rw [show viewAt state footprint y = state.view j from dif_pos visible]
      exact GleichAt.refl _ _
    by_cases issuer : j = i
    · have current := atThread after
      have prior := (atThread before).symm
      rw [issuer, issued] at current
      rw [issuer] at prior
      exact current.trans (write_agrees value.toNat prior)
    · have outside : ¬ fenster address y := fun touched =>
        issuer ((owns y touched).2 j (Classical.choose_spec visible))
      have current := atThread after
      have localAgreement := others j issuer y (Classical.choose_spec visible)
      exact (current.trans (localAgreement.trans (atThread before).symm)).trans
        ((write_nurIn (mergedView before footprint) address value.toNat).gleichAt outside).symm
  · have outside : ¬ fenster address y := fun touched => visible ⟨i, (owns y touched).1⟩
    have same : GleichAt (mergedView after footprint) (mergedView before footprint) y := by
      change GleichAt (viewAt after footprint y) (viewAt before footprint y) y
      simpa only [viewAt, dif_neg visible] using committed y outside
    exact same.trans ((write_nurIn (mergedView before footprint) address value.toNat).gleichAt outside).symm

/-- A store through an exclusive footprint is a single SC store, including
    its normal refusal when the bytes are unwritable. -/
theorem projectSCState_store {layout : Lay} {before after : (TSO layout).St}
    {i : Nat} {address value : W} {answer : Ans}
    (step : (TSO layout).ans before i (.wr address value) answer after)
    (footprint : Nat → W → Prop)
    (owns : ∀ y, fenster address y → footprint i y ∧ ∀ j, footprint j y → j = i) :
    (SC layout).ans (projectSCState footprint before) i (.wr address value) answer
      (projectSCState footprint after) := by
  have permissions := mergedView_wr before.1 footprint
  have views := tso_store_updates_view step
  rcases step with ⟨denied, refused, same⟩ | ⟨allowed, accepted, enqueued⟩
  · refine Or.inl ⟨?_, refused, congrArg (projectSCState footprint) same⟩
    change (mergedView before.1 footprint).wr64 address value = none
    simp only [wr64_eq, permissions, denied, Bool.false_eq_true, ↓reduceIte]
  · rcases views with ⟨refused, _⟩ | ⟨_, issued, others⟩
    · rw [accepted] at refused
      cases refused
    · have committed : after.1.m = before.1.m := by rw [enqueued] <;> rfl
      have written := merging_a_store footprint i address value owns
        (fun y _ => by rw [committed]; exact GleichAt.refl _ y) issued
        (fun j different y _ => by rw [others j different]; exact GleichAt.refl _ y)
      refine Or.inr ⟨_, ?_, accepted, written⟩
      change (mergedView before.1 footprint).wr64 address value =
        some (Mem.write (mergedView before.1 footprint) address 8 value.toNat)
      simp only [wr64_eq, permissions, allowed, ↓reduceIte]

/-- A compare-and-swap on an exclusive footprint uses the same old word,
    permission checks and comparison as the SC projection. -/
theorem projectSCState_cas {layout : Lay} {before after : (TSO layout).St}
    {i : Nat} {address expected value : W} {answer : Ans}
    (step : (TSO layout).ans before i (.cas address expected value) answer after)
    (footprint : Nat → W → Prop)
    (owns : ∀ y, fenster address y → footprint i y ∧ ∀ j, footprint j y → j = i)
    (disjoint : ∀ thread store, store ∈ before.1.buf thread →
      ∀ other, other ≠ thread → ∀ y, footprint other y → ¬ fenster store.1 y) :
    (SC layout).ans (projectSCState footprint before) i (.cas address expected value) answer
      (projectSCState footprint after) := by
  obtain ⟨empty, outcome⟩ := step
  have beforeView : before.1.view i = before.1.m := by
    simp only [TSt.view, empty, List.foldl_nil]
  have agree : GleichAuf (fenster address) (mergedView before.1 footprint) before.1.m := by
    rw [← beforeView]
    exact fun y touched => tso_views_merge before.1 footprint disjoint i y (owns y touched).1
  let old := BitVec.ofNat 64 (Mem.le before.1.m address 8)
  let permitted := Mem.all before.1.m.rd address 8 && Mem.all before.1.m.wr address 8
  have source : before.1.m.cas address expected value =
      if permitted = true then some (old, if old = expected then Mem.write before.1.m address 8 value.toNat
        else before.1.m) else none := cas_eq _ _ _ _
  have projected : (mergedView before.1 footprint).cas address expected value =
      if permitted = true then some (old, if old = expected then
        Mem.write (mergedView before.1 footprint) address 8 value.toNat else mergedView before.1 footprint)
      else none := by
    rw [cas_eq, gleich_rdall agree, gleich_wr agree, gleich_le agree]
  rcases outcome with ⟨refused, noneAnswer, same⟩ | ⟨observed, changed, accepted, returned, state⟩
  · refine Or.inl ⟨?_, noneAnswer, congrArg (projectSCState footprint) same⟩
    change (mergedView before.1 footprint).cas address expected value = none
    by_cases allowed : permitted = true
    · rw [source, if_pos allowed] at refused
      cases refused
    · rw [projected, if_neg allowed]
  · have allowed : permitted = true := by
      by_cases decided : permitted = true
      · exact decided
      · rw [source, if_neg decided] at accepted
        cases accepted
    rw [source, if_pos allowed] at accepted
    have values := Option.some.inj accepted
    have observedEq : old = observed := congrArg Prod.fst values
    have writtenEq : (if old = expected then Mem.write before.1.m address 8 value.toNat
        else before.1.m) = changed := congrArg Prod.snd values
    refine Or.inr ⟨old, if old = expected then
      Mem.write (mergedView before.1 footprint) address 8 value.toNat else mergedView before.1 footprint,
      ?_, ?_, ?_⟩
    · change (mergedView before.1 footprint).cas address expected value = _
      rw [projected, if_pos allowed]
    · rw [returned, observedEq]
    · by_cases matchesExpected : old = expected
      · rw [if_pos matchesExpected] at writtenEq
        have committedWrite : after.1 = {before.1 with m := Mem.write before.1.m address 8 value.toNat} := by
          rw [state, ← writtenEq]
        have committedOutside (y : W) (outside : ¬ fenster address y) :
            GleichAt after.1.m before.1.m y := by
          rw [committedWrite]
          exact (write_nurIn before.1.m address value.toNat).gleichAt outside
        have issuer : after.1.view i = Mem.write (before.1.view i) address 8 value.toNat := by
          rw [committedWrite, beforeView]
          simp only [TSt.view, empty, List.foldl_nil]
        have others (j : Nat) (different : j ≠ i) :
            GleichAuf (footprint j) (after.1.view j) (before.1.view j) := by
          rw [committedWrite]
          unfold TSt.view
          apply buffers_agree
          intro y member
          exact (write_nurIn before.1.m address value.toNat).gleichAt
            (fun touched => different ((owns y touched).2 j member))
        change mergedView after.1 footprint = _
        rw [if_pos matchesExpected]
        exact merging_a_store footprint i address value owns committedOutside issuer others
      · rw [if_neg matchesExpected] at writtenEq
        have same : after.1 = before.1 := by rw [state, ← writtenEq]
        change mergedView after.1 footprint = _
        rw [same, if_neg matchesExpected]

end Gabbro.Stage0.Senke.BildMehr
