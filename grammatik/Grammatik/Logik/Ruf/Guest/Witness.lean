module

public import Grammatik.Logik.Ruf.Guest.Boundary
public import Grammatik.Zielsatz.Kern.Akzeptiert.Guest

@[expose] public section

namespace Gabbro.Grammatik.GuestWitness

def code : DataCapTy := .table 0 (true, false)
def data : DataCapTy := ⟨0, ⟨true, true, some 0⟩, .table 1⟩

/-- Two nominal regions, one owner and two software services: one takes only
    immutable code, the other additionally takes the owned data region. -/
def D : Deklaration where
  Tab := Bool
  decTab := inferInstance
  count := fun _ => 8
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 255
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some false | 1 => some true | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Unit
  decMarke := inferInstance
  stufen := fun _ => 2
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun | false => [] | true => [()]
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := [], erg := none, gruende := 0, haelt := [],
      schreibt := fun _ => false, gschreibt := fun e => nomatch e,
      konsumiert := [], produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ _ h => List.not_mem_nil h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Bool
  aparams := fun | false => [.ptr code] | true => [.ptr code, .ptr data]
  aerg := fun _ => none
  agruende := fun _ => 1
  aschreibt := fun _ _ => false
  agschreibt := fun _ e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ h => by cases h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e
  ownerNr := fun | 0 => some () | _ => none
  axHerkunft := fun _ => some .software

def guest : GuestBoundary D :=
  { caller := (), code, service := some false, transfers := [], available := [],
    behavior := .returns, abi := some .userspace }

def transfer : GuestTransfer D := ⟨data, (), 0⟩

def ownedGuest : GuestBoundary D :=
  { guest with service := some true, transfers := [transfer],
    available := [.marke () 0] }

theorem guest_admitted : guest.check = .ok () := by decide
theorem owned_admitted : ownedGuest.check = .ok () := by decide

/-- Joint non-degenerate instance of the owner theorem: the transferred
    region has one real owner mark in the actual call-site resource context. -/
theorem transfer_owned_zeuge :
    GuestBoundary.transferB ownedGuest.available transfer = true ∧
      Res.marke transfer.owner transfer.stage ∈ ownedGuest.available :=
  ⟨by decide, GuestBoundary.transfer_owned (by decide)⟩

theorem no_service :
    ({ guest with service := none }).check =
      .error "entrust: missing isolation service binding" := by decide

theorem no_owner :
    ({ ownedGuest with available := [] }).check =
      .error "entrust: caller does not own a transferred region" := by decide

theorem forged_owner :
    ({ ownedGuest with transfers :=
      [{ transfer with capability := { data with rights := ⟨true, true, some 7⟩ } }] }).check =
      .error "entrust: caller does not own a transferred region" := by decide

theorem no_abi :
    ({ guest with abi := none }).check = .error "entrust: unknown userspace ABI" := by decide

theorem registers_refused :
    ({ guest with registers := ["rdi"] }).check =
      .error "entrust: register-state or privileged transfer is excluded" := by decide

theorem privileged_refused :
    ({ guest with privileged := true }).check =
      .error "entrust: register-state or privileged transfer is excluded" := by decide

theorem mutable_code_refused :
    ({ guest with code := .table 0 (true, true) }).check =
      .error "entrust: code needs an immutable region capability" := by decide

theorem wrong_transfer_arguments :
    ({ ownedGuest with service := some false }).check =
      .error "entrust: transferred regions differ from the service arguments" := by decide

theorem false_noreturn_refused :
    ({ guest with behavior := .noreturn }).check =
      .error "entrust: noreturn service needs a never result" := by decide

def protectedGrant : Konzession D := { tab := false, basis := 0, laenge := 8 }
def guestStorage : Konzession D := { tab := true, basis := 0, laenge := 8 }

theorem disjoint_storage :
    GuestBoundary.storageDisjointB [protectedGrant] [guestStorage] = true := by decide

theorem overlap_refused :
    GuestBoundary.storageDisjointB [protectedGrant] [protectedGrant] = false := by decide

theorem storage_disjoint_zeuge :
    GuestBoundary.StorageDisjoint [protectedGrant] [guestStorage] :=
  (GuestBoundary.storageDisjointB_iff _ _).mp disjoint_storage

def program : Programm D where
  invariante := fun e => nomatch e
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => .ret .empty (List.Perm.refl _)

def locks : SperrInv D := ⟨fun e => nomatch e, fun e => nomatch e⟩

/-- The admission is actually conjoined with the existing whole-program
    checker. This is a model fixture, not a source-to-IR witness. -/
theorem checked_guest :
    Akzeptiert program locks [()] [] [.inl false, .inl true] [] [] [] [] [guest] = true := by
  decide +kernel

theorem checked_missing_service :
    Akzeptiert program locks [()] [] [.inl false, .inl true] [] [] [] []
      [{ guest with service := none }] = false := by
  decide +kernel

/-- The service's typed input contract exists on the ordinary program field;
    admission itself establishes no software implementation or OS guarantee. -/
theorem ordinary_contract :
    program.axVertrag false = callVertragWahr D (D.asignatur false) := rfl

theorem no_hardware_isolation : D.axBeleg false = none ∧
    D.axHerkunft false = some AxOrigin.software := ⟨rfl, rfl⟩

end Gabbro.Grammatik.GuestWitness
