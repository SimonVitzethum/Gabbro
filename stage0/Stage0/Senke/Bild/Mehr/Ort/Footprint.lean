module

public import Stage0.Senke.Bild.Mehr.PrivatePath

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Runner.Beweis Runner.Mach

/-- A byte without any pending store reads its committed value under
    every assignment of view ownership. -/
theorem mergedView_unbuffered (state : TSt) (footprint : Nat → W → Prop) (byte : W)
    (unwritten : ∀ thread store, store ∈ state.buf thread → ¬ fenster store.1 byte) :
    GleichAt (mergedView state footprint) state.m byte := by
  change GleichAt (viewAt state footprint byte) state.m byte
  by_cases assigned : ∃ thread, footprint thread byte
  · rw [show viewAt state footprint byte = state.view (Classical.choose assigned) from dif_pos assigned]
    exact view_agrees_at (unwritten (Classical.choose assigned))
  · rw [show viewAt state footprint byte = state.m from dif_neg assigned]
    exact .refl _ _

/-- Reassigning view ownership is silent as soon as both descriptions
    retain the exclusive owner of each still-pending store. This applies
    when a lock grants a carrier and when a drained carrier is released. -/
theorem projectSCState_reassign {layout : Runner.Beweis.Lay} {state : (TSO layout).St}
    {before after : Nat → W → Prop}
    (old : PrivateBuffers before state.1) (new : PrivateBuffers after state.1) :
    projectSCState after state = projectSCState before state := by
  apply Subtype.ext
  apply mem_eq_of_agreement
  intro byte
  by_cases written : ∃ thread store, store ∈ state.1.buf thread ∧ fenster store.1 byte
  · obtain ⟨thread, store, pending, hit⟩ := written
    have current := mergedView_accessible_at state.1 after thread byte
      (fun i s found a touched => (new i s found a touched).1) (new thread store pending byte hit).2
    have previous := mergedView_accessible_at state.1 before thread byte
      (fun i s found a touched => (old i s found a touched).1) (old thread store pending byte hit).2
    exact current.trans previous.symm
  · have unbuffered (thread : Nat) (store : W × W) (pending : store ∈ state.1.buf thread) :
        ¬ fenster store.1 byte := fun hit => written ⟨thread, store, pending, hit⟩
    exact (mergedView_unbuffered state.1 after byte unbuffered).trans
      (mergedView_unbuffered state.1 before byte unbuffered).symm

/-- When a host operation preserves the issuing view and all buffers,
    the merged image is unchanged. A difference in committed bytes
    hidden by the issuer's buffer cannot affect any projected byte. -/
theorem projectSCState_issuerView {layout : Runner.Beweis.Lay} {before after : (TSO layout).St}
    {footprint : Nat → W → Prop} (issuer : Nat)
    (owned : PrivateBuffers footprint before.1)
    (buffers : after.1.buf = before.1.buf) (view : after.1.view issuer = before.1.view issuer) :
    projectSCState footprint after = projectSCState footprint before := by
  have ownedAfter : PrivateBuffers footprint after.1 := by
    intro thread store pending byte hit
    rw [buffers] at pending
    exact owned thread store pending byte hit
  apply Subtype.ext
  apply mem_eq_of_agreement
  intro byte
  by_cases buffered : ∃ store ∈ before.1.buf issuer, fenster store.1 byte
  · obtain ⟨store, pending, hit⟩ := buffered
    have stillPending : store ∈ after.1.buf issuer := by rw [buffers]; exact pending
    have old := mergedView_accessible_at before.1 footprint issuer byte
      (fun i s found a touched => (owned i s found a touched).1) (owned issuer store pending byte hit).2
    have new := mergedView_accessible_at after.1 footprint issuer byte
      (fun i s found a touched => (ownedAfter i s found a touched).1) (ownedAfter issuer store stillPending byte hit).2
    rw [view] at new
    exact new.trans old.symm
  · have outsideOld (store : W × W) (pending : store ∈ before.1.buf issuer) : ¬ fenster store.1 byte :=
      fun hit => buffered ⟨store, pending, hit⟩
    have outsideNew (store : W × W) (pending : store ∈ after.1.buf issuer) : ¬ fenster store.1 byte :=
      outsideOld store (by simpa only [buffers] using pending)
    have prior := view_agrees_at (state := before.1) outsideOld
    have current := view_agrees_at (state := after.1) outsideNew
    rw [view] at current
    have committed := current.symm.trans prior
    change GleichAt (viewAt after.1 footprint byte) (viewAt before.1 footprint byte) byte
    by_cases assigned : ∃ i, footprint i byte
    · rw [show viewAt after.1 footprint byte = after.1.view (Classical.choose assigned) from dif_pos assigned,
        show viewAt before.1 footprint byte = before.1.view (Classical.choose assigned) from dif_pos assigned]
      simp only [TSt.view, buffers]
      exact buffers_agree (before.1.buf (Classical.choose assigned))
        (region := (· = byte)) (fun _ exactByte => exactByte.symm ▸ committed) byte rfl
    · simpa only [viewAt, dif_neg assigned] using committed

/-- The selected thread can buffer stores to a freshly protected region
    in addition to the bytes it already owns. -/
def claimRegion (footprint : Nat → W → Prop) (owner : Nat) (region : W → Prop) :
    Nat → W → Prop :=
  fun thread byte => footprint thread byte ∨ thread = owner ∧ region byte

def releaseRegion (footprint : Nat → W → Prop) (owner : Nat) (region : W → Prop) :
    Nat → W → Prop :=
  fun thread byte => footprint thread byte ∧ (thread ≠ owner ∨ ¬ region byte)

theorem PrivateBuffers.claimRegion {footprint : Nat → W → Prop} {state : TSt}
    (buffers : PrivateBuffers footprint state) (owner : Nat) (region : W → Prop)
    (free : ∀ byte, region byte → ∀ thread, ¬ footprint thread byte) :
    PrivateBuffers (claimRegion footprint owner region) state := by
  intro issuer store pending byte hit
  obtain ⟨owned, exclusive⟩ := buffers issuer store pending byte hit
  refine ⟨.inl owned, ?_⟩
  intro other assigned
  rcases assigned with known | ⟨_, claimed⟩
  · exact exclusive other known
  · exact (free byte claimed issuer owned).elim

theorem PrivateBuffers.releaseRegion {footprint : Nat → W → Prop} {state : TSt}
    (buffers : PrivateBuffers footprint state) (owner : Nat) (region : W → Prop)
    (drained : ∀ store ∈ state.buf owner, ∀ byte, region byte → ¬ fenster store.1 byte) :
    PrivateBuffers (releaseRegion footprint owner region) state := by
  intro issuer store pending byte hit
  obtain ⟨owned, exclusive⟩ := buffers issuer store pending byte hit
  refine ⟨⟨owned, ?_⟩, fun other assigned => exclusive other assigned.1⟩
  by_cases same : issuer = owner
  · subst issuer
    exact .inr (fun present => drained store pending byte present hit)
  · exact .inl same

end Gabbro.Stage0.Senke.BildMehr
