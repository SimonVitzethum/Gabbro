module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Guest.Contracts
public import Grammatik.Logik.Ruf.Guest.Service
@[expose] public section
namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Uebersetze UebersetzeAllg

/-- Re-resolve the exact source names against the actual declaration used by
    the program and checker, then apply the canonical typed boundary check.
    No descriptor is reconstructed from a name-only or empty adapter. -/
def sourceGuest (u : UProg) (source : UGuest) : Except String (GuestBoundary (declOf u)) := do
  let caller ← fnIdx u.fns source.name
  let service ← match uaxIdx u.axs source.service with
    | .ok service => pure service
    | .error _ => throw "entrust: missing isolation service binding"
  let table ← tabIdx u.tabs source.code
  let code ← match GuestBoundary.pointerInputs ((declOf u).aparams service) with
    | code :: _ => pure code
    | [] => throw "entrust: code needs an immutable region capability"
  if code.target != .table table.val then
    throw "entrust: transferred regions differ from the service arguments"
  let guest : GuestBoundary (declOf u) :=
    { caller, code, service := some service, transfers := [],
      available := resOf u caller, behavior := .returns,
      abi := if (ProfilBindung.wertVon .arch source.arch).isSome then some .userspace else none }
  guest.check
  pure guest

/-- Fail rather than shortening a source descriptor list. -/
def sourceGuestList (u : UProg) : List UGuest → Except String (List (GuestBoundary (declOf u)))
  | [] => pure []
  | source :: rest => do
    let guest ← sourceGuest u source
    let tail ← sourceGuestList u rest
    pure (guest :: tail)

def sourceGuests (u : UProg) : Except String (List (GuestBoundary (declOf u))) :=
  sourceGuestList u u.guests

/-- The actual checker receives exactly one descriptor per admitted source
    declaration, in source order; a failed resolution cannot disappear. -/
theorem sourceGuestList_length (u : UProg) (sources : List UGuest)
    (guests : List (GuestBoundary (declOf u)))
    (h : sourceGuestList u sources = .ok guests) : guests.length = sources.length := by
  induction sources generalizing guests with
  | nil => cases h; rfl
  | cons source rest ih =>
    cases hs : sourceGuest u source with
    | error error => simp [sourceGuestList, hs] at h
    | ok guest =>
      cases ht : sourceGuestList u rest with
      | error error => simp [sourceGuestList, hs, ht] at h
      | ok tail =>
        simp only [sourceGuestList, hs, ht, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at h
        subst guests
        simp only [List.length_cons, ih tail ht]

theorem sourceGuests_complete (u : UProg) (guests : List (GuestBoundary (declOf u)))
    (h : sourceGuests u = .ok guests) : guests.length = u.guests.length :=
  sourceGuestList_length u u.guests guests h

/-- User logic supplies software isolation on actual C08 calls, under the
    very program whose foreign contracts were exported. This duty is never
    inserted into HardwareAnnahmen or discharged by a source assume item. -/
def SourceGuestPflicht (u : UProg) (E : Zielsatz.Einheit (declOf u))
    (O : Orakel (declOf u)) (history : List (BoundaryRecord (declOf u)))
    (storage : BoundaryRecord (declOf u) → List (Konzession (declOf u))) : Prop :=
  ∃ guests, sourceGuests u = .ok guests ∧
    ∀ guest ∈ guests, GuestServicePflicht E O history guest storage

end Gabbro.Grammatik.Parser.UebersetzeAllg2
