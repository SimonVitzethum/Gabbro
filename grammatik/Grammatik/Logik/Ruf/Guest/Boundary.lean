module

public import Grammatik.Logik.Ruf.FremdRuf.T4

@[expose] public section

namespace Gabbro.Grammatik

/-! C14's bounded guest boundary. Code is an immutable input capability to a
    software service; it is never a G instruction or a machine address. The
    record is admission data, not an isolation assumption or an execution path. -/

inductive GuestReturn where
  | returns
  | noreturn
  deriving DecidableEq, Repr

/-- The closed ordinary call ABI. Register-state and privileged entry have no
    constructor. Architecture selection remains the image binding's duty. -/
inductive GuestAbi where
  | userspace
  deriving DecidableEq, Repr

structure GuestTransfer (D : Deklaration) where
  capability : DataCapTy
  owner : D.Marke
  stage : Nat

/-- A boundary binds one particular caller, code input and foreign service.
    `transfers` is the complete list of non-code pointer inputs, in order;
    `available` is the caller's actual resource context at this call site.
    Extents and isolation at a particular invocation are software proof duties. -/
structure GuestBoundary (D : Deklaration) where
  caller : D.Fn
  code : DataCapTy
  service : Option D.Ax
  transfers : List (GuestTransfer D)
  available : List (Res D)
  behavior : GuestReturn
  abi : Option GuestAbi
  registers : List String := []
  privileged : Bool := false

namespace GuestBoundary

variable {D : Deklaration}

def pointerInputs : List Ty → List DataCapTy
  | [] => []
  | .ptr cap :: rest => cap :: pointerInputs rest
  | _ :: rest => pointerInputs rest

/-- The adapter admits explicit top-level region inputs only. A reference,
    callback or aggregate could hide additional capabilities; its complete
    transfer interpretation must exist before it can cross this boundary. -/
def inputsB (inputs : List Ty) : Bool := inputs.all fun
  | .int .. | .bool | .opt _ | .why _ | .fl .. | .str _ | .ptr _ => true
  | _ => false

/-- A live nominal table capability, with its declared space preserved. -/
def regionB (cap : DataCapTy) : Bool :=
  match cap.target with
  | .table n => match D.tabNr n with
    | none => false
    | some t => decide (D.tableSpace t = cap.space)

/-- Ownership is a linear resource, independently of read/write permissions. -/
def transferB (available : List (Res D)) (t : GuestTransfer D) : Bool :=
  regionB (D := D) t.capability &&
    (match t.capability.rights.owner with
    | none => false
    | some n => decide (D.ownerNr n = some t.owner)) &&
    decide (Res.marke t.owner t.stage ∈ available) && decide (t.stage < D.stufen t.owner) &&
    (match t.capability.target with
    | .table n => match D.tabNr n with
      | none => false
      | some table => decide (t.owner ∈ D.eigner table))

/-- Named refusals are shared by source admission and the Bool checker. No
    missing origin, owner, ABI or service is repaired by a default. -/
def check (g : GuestBoundary D) : Except String Unit := do
  let a ← match g.service with
    | none => throw "entrust: missing isolation service binding"
    | some a => pure a
  if g.abi != some .userspace then throw "entrust: unknown userspace ABI"
  if !g.registers.isEmpty || g.privileged then
    throw "entrust: register-state or privileged transfer is excluded"
  if D.axHerkunft a != some .software || (D.axBeleg a).isSome then
    throw "entrust: isolation service must be a software binding"
  if D.agruende a = 0 then throw "entrust: isolation service needs a failure channel"
  if !regionB (D := D) g.code || !g.code.rights.read || g.code.rights.write ||
      g.code.rights.owner.isSome then
    throw "entrust: code needs an immutable region capability"
  if !inputsB (D.aparams a) then
    throw "entrust: nested capability or callback needs an explicit service boundary"
  if !g.transfers.all (transferB g.available) then
    throw "entrust: caller does not own a transferred region"
  if !decide ((g.transfers.map (fun t => t.owner)).Nodup) then
    throw "entrust: a region owner is transferred more than once"
  if pointerInputs (D.aparams a) != g.code :: g.transfers.map (·.capability) then
    throw "entrust: transferred regions differ from the service arguments"
  match g.behavior with
  | .returns =>
    if D.aerg a = some .never then throw "entrust: returning service has a never result"
  | .noreturn =>
    if D.aerg a != some .never then throw "entrust: noreturn service needs a never result"

def admittedB (g : GuestBoundary D) : Bool := g.check.isOk

def admissionB (guests : List (GuestBoundary D)) : Bool := guests.all admittedB

theorem admissionB_nil : admissionB (D := D) [] = true := rfl

theorem admissionB_each {guests : List (GuestBoundary D)}
    (h : admissionB guests = true) (g : GuestBoundary D) (hg : g ∈ guests) :
    admittedB g = true := List.all_eq_true.mp h g hg

/-- Admission can never silently choose an invocation service. -/
theorem missing_service (g : GuestBoundary D) (h : g.service = none) :
    g.check = .error "entrust: missing isolation service binding" := by
  simp [check, h]

/-- A transfer accepted by the checker carries the actual owner resource. -/
theorem transfer_owned {available : List (Res D)} {t : GuestTransfer D}
    (h : transferB available t = true) : Res.marke t.owner t.stage ∈ available := by
  simp only [transferB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

/-- Guest storage must stay outside every protected live grant. The service
    proves this at each call, using the C08 live inventory, on success and
    failure. A source assumption cannot supply this proposition. -/
def StorageDisjoint (protected guestOwned : List (Konzession D)) : Prop :=
  ∀ p ∈ protected, ∀ g ∈ guestOwned, ¬ p.ueberschneidet g

def storageDisjointB (protected guestOwned : List (Konzession D)) : Bool :=
  protected.all fun p => guestOwned.all fun g =>
    !(decide (p.tab = g.tab) && decide (p.basis < g.basis + (g.laenge : Int)) &&
      decide (g.basis < p.basis + (p.laenge : Int)))

theorem storageDisjointB_iff (protected guestOwned : List (Konzession D)) :
    storageDisjointB protected guestOwned = true ↔ StorageDisjoint protected guestOwned := by
  simp [storageDisjointB, StorageDisjoint, Konzession.ueberschneidet,
    List.all_eq_true, Bool.and_eq_true]

/-- The ordinary-call certificate names the existing typed G node. No guest
    interpreter, instruction semantics or additional step rule is introduced. -/
structure Invocation (g : GuestBoundary D) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ Λ' : List (Res D)) where
  admitted : g.admittedB = true
  service : D.Ax
  resolved : g.service = some service
  context : g.available = Λ
  result : Option Ty
  args : Args D Γ Λ (D.aparams service)
  result_eq : D.aerg service = result
  callFits : RufPasst D V (D.asignatur service) Λ
  writes : ∀ t, D.aschreibt service t = true → darf D t Λ
  globalWrites : ∀ x, D.agschreibt service x = true → gdarf D x Λ
  fallible : 0 < D.agruende service
  failure : Endblock D V l (reasonTy (D.agruende service) :: Γ)
    (nachSig D (D.asignatur service) Λ)
  continuation : Block D V l (ErgCtx Γ result)
    (nachSig D (D.asignatur service) Λ) Λ'
  caller_eq : V = vertragVon D g.caller

def Invocation.lower {g : GuestBoundary D} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (i : Invocation g V l Γ Λ Λ') :
    Block D V l Γ Λ Λ' :=
  .bindAxiomOptElse i.result i.service i.args i.result_eq i.callFits
    i.writes i.globalWrites i.fallible i.failure i.continuation

theorem Invocation.lower_eq {g : GuestBoundary D} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (i : Invocation g V l Γ Λ Λ') :
    i.lower = .bindAxiomOptElse i.result i.service i.args i.result_eq
      i.callFits i.writes i.globalWrites i.fallible i.failure i.continuation := rfl

end GuestBoundary
end Gabbro.Grammatik
