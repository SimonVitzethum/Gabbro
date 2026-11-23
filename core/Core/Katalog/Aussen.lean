module
public import Core.Katalog.Geraet

@[expose] public section

namespace Gabbro.Core.Katalog

inductive Endpunkt where
  | uart
  | virtio
  | bios
  | uefi
  | psci
  | sbi
  | hosted
  | cProcess
  deriving DecidableEq, Repr

def Plattform.geraet (p : Plattform) : Endpunkt → Option GeraeteDaten
  | .uart => some p.uart
  | .virtio => some p.virtio
  | .bios | .uefi | .psci | .sbi | .hosted | .cProcess => none

def GeraeteDaten.register (d : GeraeteDaten) (offset : Nat) : Option Register :=
  d.registers.find? (fun r => r.offset == offset)

def Register.grenze (r : Register) : Nat := 2 ^ (8 * r.bytes)

inductive Recht where
  | read
  | write
  | resolve
  | invoke
  deriving DecidableEq, Repr

structure Objekt where
  endpoint : Endpunkt
  id : Nat
  deriving DecidableEq, Repr

structure Herkunft where
  object : Objekt
  generation : Nat
  deriving DecidableEq, Repr

/-- An outside object reference issued by that endpoint. The language tracks ownership of its handle. -/
structure Handle where
  channel : Nat
  origin : Herkunft
  rights : List Recht
  deriving DecidableEq, Repr

structure Zugriff where
  handle : Handle
  right : Recht
  deriving DecidableEq, Repr

structure ObjektSicht where
  generation : Nat
  alive : Bool
  ready : Bool
  body : List UInt8
  registers : Nat → Nat

/-- One outside snapshot at the commit cut. Dead objects retain a tombstone generation. -/
structure AussenSicht where
  objects : Objekt → ObjektSicht
  channels : Endpunkt → Nat → Option Handle
  names : Objekt → List UInt8 → Option Handle

def AussenSicht.herkunft (s : AussenSicht) (o : Objekt) : Herkunft :=
  ⟨o, (s.objects o).generation⟩

def AussenSicht.gueltig (s : AussenSicht) (endpoint : Endpunkt) (access : Zugriff) : Bool :=
  let h := access.handle
  let o := h.origin.object
  o.endpoint == endpoint && s.channels endpoint h.channel == some h &&
    (s.objects o).alive && h.origin == s.herkunft o && access.right ∈ h.rights

inductive Dienst where
  | readSectors
  | memoryMap
  | enableA20
  | exitBootServices
  | cpuOn
  | hartStart
  deriving DecidableEq, Repr

/-- Current rights are determined by the operation. Every additional object is checked at the same cut. -/
inductive AussenOperation where
  | read
  | write (bytes : List UInt8)
  | resolve (name : List UInt8)
  | firmware (service : Dienst) (bytes : List UInt8)
  | exchange (message : List UInt8)
  | registerRead (offset : Nat)
  | registerWrite (offset value : Nat)
  | waitRegister (offset expected : Nat)
  deriving DecidableEq, Repr

def AussenOperation.required : AussenOperation → Recht
  | .read => .read
  | .write _ => .write
  | .resolve _ => .resolve
  | .firmware _ _ => .invoke
  | .exchange _ => .invoke
  | .registerRead _ => .read
  | .registerWrite _ _ => .write
  | .waitRegister _ _ => .read

structure Frage where
  endpoint : Endpunkt
  handle : Handle
  other : List Zugriff
  operation : AussenOperation
  deriving DecidableEq, Repr

def Frage.zugriffe (q : Frage) : List Zugriff :=
  ⟨q.handle, q.operation.required⟩ :: q.other

/-- Firmware ABI names belong to the outside row. An exchange with C crosses a process boundary
    and the wire payload contains only copied bytes. -/
inductive DienstAbi where
  | biosInterrupt
  | efiX64
  | efiAapcs
  | psciSmc
  | sbiEcall
  deriving DecidableEq, Repr

def Plattform.firmwareAbi (p : Plattform) (e : Endpunkt) : Option DienstAbi :=
  match e with
  | .bios => if p = .x86_64 then some .biosInterrupt else none
  | .uefi =>
    match p with
    | .x86_64 => some .efiX64
    | .aarch64 => some .efiAapcs
    | .riscv64 => none
  | .psci => if p = .aarch64 then some .psciSmc else none
  | .sbi => if p = .riscv64 then some .sbiEcall else none
  | .uart | .virtio | .hosted | .cProcess => none

def dienstAngeboten (endpoint : Endpunkt) (service : Dienst) : Bool :=
  match endpoint with
  | .bios => service ∈ [Dienst.readSectors, .memoryMap, .enableA20]
  | .uefi => service ∈ [Dienst.memoryMap, .exitBootServices]
  | .psci => service == .cpuOn
  | .sbi => service == .hartStart
  | .uart | .virtio | .hosted | .cProcess => false

inductive AussenFehler where
  | unsupported
  | staleOrDenied
  | unavailable
  | unknownName
  deriving DecidableEq, Repr

inductive AussenWert where
  | data (bytes : List UInt8)
  | written (bytes : List UInt8)
  | handle (h : Handle)
  | register (value : Nat)
  | registerWritten (offset value : Nat)
  | firmware (service : Dienst) (request response : List UInt8)
  | exchanged (request response : List UInt8)
  deriving DecidableEq, Repr

structure Antwort where
  origin : Herkunft
  checkedObjects : List Herkunft
  result : Except AussenFehler AussenWert
  deriving Repr

inductive Entscheidung where
  | warten
  | antwort (a : Antwort)
  deriving Repr

def registerZugriff (d : GeraeteDaten) (q : AussenOperation) : Bool :=
  match q with
  | .registerRead offset => (d.register offset).any Register.read
  | .registerWrite offset value => (d.register offset).any (fun r => r.write && value < r.grenze)
  | .waitRegister offset value => (d.register offset).any (fun r => r.read && value < r.grenze)
  | .read | .write _ | .resolve _ | .firmware _ _ | .exchange _ => false

def Plattform.operationAngeboten (p : Plattform) (q : Frage) : Bool :=
  match q.endpoint with
  | .uart => registerZugriff p.uart q.operation
  | .virtio => registerZugriff p.virtio q.operation
  | .hosted =>
    match q.operation with
    | .read | .write _ | .resolve _ => true
    | .firmware _ _ | .exchange _ | .registerRead _ | .registerWrite _ _ | .waitRegister _ _ => false
  | .cProcess =>
    match q.operation with
    | .exchange _ => q.other.isEmpty
    | .read | .write _ | .resolve _ | .firmware _ _ | .registerRead _ | .registerWrite _ _
    | .waitRegister _ _ => false
  | .bios | .uefi | .psci | .sbi =>
    match q.operation with
    | .firmware service _ => (p.firmwareAbi q.endpoint).isSome && dienstAngeboten q.endpoint service
    | .read | .write _ | .resolve _ | .exchange _ | .registerRead _ | .registerWrite _ _
    | .waitRegister _ _ => false

def Plattform.registerWert (p : Plattform) (q : Frage) (view : ObjektSicht) (offset : Nat) : Nat :=
  match (p.geraet q.endpoint).bind (fun d => d.register offset) with
  | none => 0
  | some r => view.registers offset % r.grenze

def AussenSicht.erfolg (p : Plattform) (s : AussenSicht) (q : Frage) : Except AussenFehler AussenWert :=
  let o := q.handle.origin.object
  let view := s.objects o
  match q.operation with
  | .read => .ok (.data view.body)
  | .write bytes => .ok (.written bytes)
  | .resolve name =>
    match s.names o name with
    | none => .error .unknownName
    | some h =>
      if h.origin.object.endpoint == q.endpoint && (s.objects h.origin.object).alive &&
          h.origin == s.herkunft h.origin.object && s.channels q.endpoint h.channel == some h then
        .ok (.handle h)
      else .error .unknownName
  | .firmware service bytes => .ok (.firmware service bytes view.body)
  | .exchange bytes => .ok (.exchanged bytes view.body)
  | .registerRead offset | .waitRegister offset _ => .ok (.register (p.registerWert q view offset))
  | .registerWrite offset v => .ok (.registerWritten offset v)

/-- A row waits only for a valid register wait whose condition is false at the current cut. -/
def AussenSicht.wartet (p : Plattform) (s : AussenSicht) (q : Frage) : Bool :=
  match q.operation with
  | .waitRegister offset expected =>
    let view := s.objects q.handle.origin.object
    !(view.ready && p.registerWert q view offset == expected)
  | .read | .write _ | .resolve _ | .firmware _ _ | .exchange _ | .registerRead _ | .registerWrite _ _ =>
    false

/-- The result and complete revalidation footprint are read from one commit snapshot. An old handle
    fails explicitly. Register wait is the only operation in these rows with a permitted non-answer. -/
def atomar (p : Plattform) (s : AussenSicht) (q : Frage) : Entscheidung :=
  let o := q.handle.origin.object
  let origin := s.herkunft o
  if !p.operationAngeboten q then .antwort ⟨origin, [], .error .unsupported⟩
  else if !(q.zugriffe.all (s.gueltig q.endpoint)) then
    .antwort ⟨origin, [], .error .staleOrDenied⟩
  else if s.wartet p q then .warten
  else
    let checked := q.zugriffe.map (fun a => s.herkunft a.handle.origin.object)
    let result := if (s.objects o).ready then s.erfolg p q else .error .unavailable
    .antwort ⟨origin, checked, result⟩

theorem atomar_warten_iff (p : Plattform) (s : AussenSicht) (q : Frage) :
    atomar p s q = .warten ↔
      p.operationAngeboten q = true ∧ q.zugriffe.all (s.gueltig q.endpoint) = true ∧ s.wartet p q = true := by
  cases offered : p.operationAngeboten q <;>
    cases valid : q.zugriffe.all (s.gueltig q.endpoint) <;>
    cases wait : s.wartet p q <;>
    simp only [atomar, offered, valid, wait, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_true, ite_false, true_and, false_and]
  all_goals exact ⟨(fun h => by cases h), False.elim⟩

theorem atomar_ungueltig {p s q} (offered : p.operationAngeboten q = true)
    (denied : q.zugriffe.all (s.gueltig q.endpoint) = false) :
    atomar p s q = .antwort ⟨s.herkunft q.handle.origin.object, [], .error .staleOrDenied⟩ := by
  simp only [atomar, offered, denied, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]

theorem atomar_aktuell {p s q a v} (answered : atomar p s q = .antwort a)
    (success : a.result = .ok v) :
    a.origin = s.herkunft q.handle.origin.object ∧
      a.checkedObjects = q.zugriffe.map (fun r => s.herkunft r.handle.origin.object) ∧
      ∀ access ∈ q.zugriffe, s.gueltig q.endpoint access = true := by
  unfold atomar at answered
  split at answered
  · cases answered
    cases success
  · split at answered
    · cases answered
      cases success
    · rename_i valid
      split at answered
      · cases answered
      · cases answered
        have allValid : q.zugriffe.all (s.gueltig q.endpoint) = true := by
          cases h : q.zugriffe.all (s.gueltig q.endpoint) with
          | false => exact (valid (by rw [h]; rfl)).elim
          | true => rfl
        exact ⟨rfl, rfl, List.all_eq_true.mp allValid⟩

end Gabbro.Core.Katalog
