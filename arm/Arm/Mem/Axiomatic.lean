/-
  File:      Arm/Mem/Axiomatic.lean
  Subject:   Armv8-A/Armv9-A axiomatic memory model: coherence, atomicity and
             external-visibility (`ob`) axioms over candidate executions.
  Model:     Arm ARM section B2.3 and Arm's herd model `aarch64.cat`. The Arm
             ARM text is not on this machine; clause citations are from the
             agent's knowledge of the published model, not a measured copy.
-/
import Arm.Mem.Event

namespace Arm

/-- Plug-in ordering parts owned by other agents (B2.3, `aarch64.cat` clause
    `obs | dob | aob | bob`): agent 09 supplies `aob` (atomics, exclusives),
    agent 10 supplies `bob` (barriers, acquire/release). -/
structure OrderingParts where
  aob : Rel
  bob : Rel
  deriving Repr

/-- The empty plug-in: no atomic or barrier ordering (for the witnesses). -/
def noParts : OrderingParts := { aob := [], bob := [] }

/-- A read event. -/
def isReadEv : Ev → Bool
  | { kind := .read _, .. } => true
  | _ => false

/-- A write event. -/
def isWriteEv : Ev → Bool
  | { kind := .write _, .. } => true
  | _ => false

/-- Endpoints of `p` run on the same core (false if either is missing). -/
def sameCorePair (x : Exec) (p : Nat × Nat) : Bool :=
  match x.ev? p.1, x.ev? p.2 with
  | some a, some b => a.core == b.core
  | _, _ => false

/-- Endpoints of `p` touch the same address (false for barriers/missing). -/
def sameLocPair (x : Exec) (p : Nat × Nat) : Bool :=
  match x.ev? p.1, x.ev? p.2 with
  | some { kind := .read a, .. }, some { kind := .read b, .. } => a.addr == b.addr
  | some { kind := .read a, .. }, some { kind := .write b, .. } => a.addr == b.addr
  | some { kind := .write a, .. }, some { kind := .read b, .. } => a.addr == b.addr
  | some { kind := .write a, .. }, some { kind := .write b, .. } => a.addr == b.addr
  | _, _ => false

end Arm

/-
CUTS: skeleton only; derived relations and axioms land in the next steps.
No theorem yet, so no `#print axioms`.
-/
