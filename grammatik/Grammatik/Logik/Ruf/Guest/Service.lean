module

public import Grammatik.Logik.Ruf.Guest.Boundary
public import Grammatik.Logik.Ruf.FremdRuf.T10

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

/-! Isolation is a software proof obligation over actual C08 records. None of
    the propositions below belongs to HardwareAnnahmen. In particular, naming
    a region, ABI or falsifier does not prove the isolation-service contract. -/

/-- Per-invocation extent interpretation, supplied by the verified service
    binding. `storage` includes every byte the guest owns, including its stack;
    it is not inferred from a label or from the code capability's identity. -/
structure GuestServicePflicht (E : Einheit D) (O : Orakel D)
    (H : List (BoundaryRecord D)) (g : GuestBoundary D)
    (storage : BoundaryRecord D → List (Konzession D)) : Prop where
  admitted : g.admittedB = true
  foreign : ForeignPflicht E O H
  isolated : ∀ n : Fin H.length, g.service = some (H.get n).ax →
    GuestBoundary.StorageDisjoint
      (GrantInventory (E.grants0 ++ H.take n.val)) (storage (H.get n))
  failure : ∀ n : Fin H.length, g.service = some (H.get n).ax →
    (H.get n).erfolg = false →
    (H.get n).konzession = none ∧ (H.get n).freigabe = none

/-- Protected live grants and guest storage are disjoint at every invocation,
    including a failing invocation. Initial grants participate in the same
    inventory; checking just the grants issued during this call is insufficient. -/
theorem guest_storage_disjoint {E : Einheit D} {O : Orakel D}
    {H : List (BoundaryRecord D)} {g : GuestBoundary D}
    {storage : BoundaryRecord D → List (Konzession D)}
    (h : GuestServicePflicht E O H g storage) (n : Fin H.length)
    (hs : g.service = some (H.get n).ax)
    (p : Konzession D) (hp : p ∈ GrantInventory (E.grants0 ++ H.take n.val))
    (s : Konzession D) (hguest : s ∈ storage (H.get n)) :
    ¬ p.ueberschneidet s := h.isolated n hs p hp s hguest

/-- A failed invocation cannot manufacture a grant or release an existing one. -/
theorem guest_failure_preserves_grants {E : Einheit D} {O : Orakel D}
    {H : List (BoundaryRecord D)} {g : GuestBoundary D}
    {storage : BoundaryRecord D → List (Konzession D)}
    (h : GuestServicePflicht E O H g storage) (n : Fin H.length)
    (hs : g.service = some (H.get n).ax) (hf : (H.get n).erfolg = false)
    (inventory : List (Konzession D)) :
    grantSchritt inventory (H.get n) = inventory := by
  obtain ⟨hc, hr⟩ := h.failure n hs hf
  simp [grantSchritt, hf, hc, hr]

/-- Software contract transport is exactly C08's transport on the actual
    recorded call. The guest adds no new postcondition and assumes no OS
    behaviour. `hpre` is the caller's user-logic duty; `hlink` binds the record
    to the actual implementation, independently of the guest's contents. -/
theorem guest_service_contract {E : Einheit D} {O : Orakel D}
    {H : List (BoundaryRecord D)} {g : GuestBoundary D}
    {storage : BoundaryRecord D → List (Konzession D)}
    (h : GuestServicePflicht E O H g storage) {HA : List (AxEintrag D)}
    (hpre : CallSitePflichtFremd E.P.axVertrag HA)
    (hlink : ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a))
      (x : World D × Int), (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA →
      D.axHerkunft a = some AxOrigin.software → O.wirkt a (σ.fragt (.inl a)) ρ = x)
    {a : D.Ax} {σ : World D} {ρ : Env D (D.aparams a)} {x : World D × Int}
    (hmem : (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA)
    (hsw : D.axHerkunft a = some AxOrigin.software)
    {v : ErgVal D (D.aerg a)} (hv : einpassenErg O.zeiger (D.aerg a) x.2 = some v) :
    AxNach E.P.axVertrag a σ ρ x.1 v :=
  vertragANeu_sw_of_foreign h.foreign hpre hlink hmem hsw hv

/-- The same obligation transports to a prefix containing the same actual
    records. This is a structural restriction of the checked invocation set,
    rather than an OS or hardware assumption. -/
theorem guest_isolation_at_prefix {E : Einheit D} {O : Orakel D}
    {H : List (BoundaryRecord D)} {g : GuestBoundary D}
    {storage : BoundaryRecord D → List (Konzession D)}
    (h : GuestServicePflicht E O H g storage) (n : Fin H.length)
    (hs : g.service = some (H.get n).ax) :
    GuestBoundary.storageDisjointB
      (GrantInventory (E.grants0 ++ H.take n.val)) (storage (H.get n)) = true :=
  (GuestBoundary.storageDisjointB_iff _ _).mpr (h.isolated n hs)

/-- Failure also preserves the folded live inventory, with initial grants
    and every preceding call retained. It cannot erase somebody else's grant
    by pretending that the guest has a separate, initially empty inventory. -/
theorem guest_failure_inventory {E : Einheit D} {O : Orakel D}
    {H : List (BoundaryRecord D)} {g : GuestBoundary D}
    {storage : BoundaryRecord D → List (Konzession D)}
    (h : GuestServicePflicht E O H g storage) (n : Fin H.length)
    (hs : g.service = some (H.get n).ax) (hf : (H.get n).erfolg = false) :
    GrantInventory ((E.grants0 ++ H.take n.val) ++ [H.get n]) =
      GrantInventory (E.grants0 ++ H.take n.val) := by
  rw [grantInventory_anhang]
  exact guest_failure_preserves_grants h n hs hf _

end Gabbro.Grammatik
