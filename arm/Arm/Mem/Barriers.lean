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

/-
CUTS: predicates only; `bob`, DMB LD/ST clauses, DSB, ISB and all theorems open.
-/
