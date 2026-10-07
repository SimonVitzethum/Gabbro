/-
  File:      Arm/Mem/Barriers.lean
  Subject:   Barrier-ordered-before (bob, Arm ARM B2.3) over candidate executions.
  Sail:
    - sail-arm/arm-v9.4-a/src/interface.sail:166-184 (DxB, Barrier union)
    - sail-arm/arm-v9.4-a/src/impdefs.sail:880-894 (DataMemoryBarrier et al.)
    - sail-arm/arm-v9.4-a/src/v8_base.sail:1911-1919 (MBReqDomain, MBReqTypes)
    - sail-arm/arm-v9.4-a/src/instrs64.sail:10271-10277 (DMB),
      10342-10345 (DSB), 22746-22748 (ISB)
    - sail/lib/concurrency_interface/read_write_v1.sail
      (AS_rel_or_acq = LDAR/STLR, AS_acq_rcpc = LDAPR)
-/
import Arm.Mem.Event

namespace Arm

def Ev.isRead : Ev → Bool
  | { kind := .read _, .. } => true
  | _ => false

def Ev.isWrite : Ev → Bool
  | { kind := .write _, .. } => true
  | _ => false

def Ev.isAcquire : Ev → Bool
  | { kind := .read { ord := .acquire, .. }, .. } => true
  | _ => false

def Ev.isAcquirePC : Ev → Bool
  | { kind := .read { ord := .acquirePC, .. }, .. } => true
  | _ => false

def Ev.isRelease : Ev → Bool
  | { kind := .write { ord := .release, .. }, .. } => true
  | _ => false

/-- v1 scope: only inner-shareable and full-system barriers order observers. -/
def Domain.v1Orders : Domain → Bool
  | .ish => true
  | .sy => true
  | _ => false

def Ev.isDmbFull : Ev → Bool
  | { kind := .barrier (.dmb d .all), .. } => d.v1Orders
  | _ => false

def poMem (x : Exec) (a b : Nat) : Bool :=
  x.po.any fun p => p.1 == a && p.2 == b

def rdOf (x : Exec) (i : Nat) : Bool :=
  match x.ev? i with | some e => e.isRead | none => false

def wrOf (x : Exec) (i : Nat) : Bool :=
  match x.ev? i with | some e => e.isWrite | none => false

def memOf (x : Exec) (i : Nat) : Bool := rdOf x i || wrOf x i

def Ev.isDmbLd : Ev → Bool
  | { kind := .barrier (.dmb d .ld), .. } => d.v1Orders
  | _ => false

def Ev.isDmbSt : Ev → Bool
  | { kind := .barrier (.dmb d .st), .. } => d.v1Orders
  | _ => false

/-- DMB clause of bob (Arm ARM B2.3.5): a ;po; barrier ;po; c with the
    classes the barrier type orders: full [R|W]..[R|W], LD [R]..[R|W],
    ST [W]..[W]. -/
def dmbHolds (x : Exec) (a c : Nat) : Bool :=
  x.evs.any fun b =>
    poMem x a b.id && poMem x b.id c &&
    ((b.isDmbFull && memOf x a && memOf x c) ||
     (b.isDmbLd && rdOf x a && memOf x c) ||
     (b.isDmbSt && wrOf x a && wrOf x c))

/-- DSB predicates (Sail: impdefs.sail:884-886). -/
def Ev.isDsbFull : Ev → Bool
  | { kind := .barrier (.dsb d .all), .. } => d.v1Orders
  | _ => false

def Ev.isDsbLd : Ev → Bool
  | { kind := .barrier (.dsb d .ld), .. } => d.v1Orders
  | _ => false

def Ev.isDsbSt : Ev → Bool
  | { kind := .barrier (.dsb d .st), .. } => d.v1Orders
  | _ => false

/-- DSB data-ordering clause: at the data-memory level a DSB orders the same
    classes as the DMB of the same type (Arm ARM B2.3: DSB completes only
    after all prior data accesses complete). The completion half beyond data
    accesses (no later instruction completes until the DSB does) has no event
    in this model and stays CUTS. Sail: impdefs.sail:884-886. -/
def dsbHolds (x : Exec) (a c : Nat) : Bool :=
  x.evs.any fun b =>
    poMem x a b.id && poMem x b.id c &&
    ((b.isDsbFull && memOf x a && memOf x c) ||
     (b.isDsbLd && rdOf x a && memOf x c) ||
     (b.isDsbSt && wrOf x a && wrOf x c))

/-- Acquire clause (Arm ARM B2.3): LDAR orders po-later reads and writes;
    LDAPR (RCpc) orders po-later reads only. -/
def acqHolds (x : Exec) (a c : Nat) : Bool :=
  match x.ev? a with
  | some e =>
    poMem x a c &&
    ((e.isAcquire && memOf x c) || (e.isAcquirePC && rdOf x c))
  | none => false

/-- Release clause (Arm ARM B2.3): STLR is ordered after po-earlier reads
    and writes. -/
def relHolds (x : Exec) (a c : Nat) : Bool :=
  match x.ev? c with
  | some e => poMem x a c && e.isRelease && memOf x a
  | none => false

/-- Release-acquire (Arm ARM B2.3): STLR ;po; LDAR, and STLR ;po; LDAPR
    (release sequence head of the RCpc extension), are ordered. -/
def relAcqHolds (x : Exec) (a c : Nat) : Bool :=
  match x.ev? a, x.ev? c with
  | some e₁, some e₂ =>
    poMem x a c && e₁.isRelease && (e₂.isAcquire || e₂.isAcquirePC)
  | _, _ => false

/-- Barrier-ordered-before: the function agent 07 plugs into
    `OrderingParts.bob`. -/
def bobHolds (x : Exec) (a c : Nat) : Bool :=
  dmbHolds x a c || dsbHolds x a c || acqHolds x a c || relHolds x a c ||
    relAcqHolds x a c

def bob (x : Exec) : Rel :=
  (x.evs.flatMap fun a => x.evs.map fun c => (a.id, c.id)).filter
    fun p => bobHolds x p.1 p.2

/-
CUTS: `bob` covers DMB and acquire/release; DSB, ISB and all theorems open.
-/
