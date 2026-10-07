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

/-- Union of two finite relations. -/
def Rel.union (r s : Rel) : Rel := (r ++ s).dedup

/-- Intersection of two finite relations. -/
def Rel.inter (r s : Rel) : Rel :=
  r.filter fun p => s.any fun q => q.1 == p.1 && q.2 == p.2

/-- `p.2` satisfies `f` (the `;[S]` set-restriction of `aarch64.cat`;
    `false` if the event is missing). -/
def targetIs (f : Ev → Bool) (x : Exec) (p : Nat × Nat) : Bool :=
  match x.ev? p.2 with
  | some e => f e
  | none => false

/-- From-reads: `rf^-1;co` (`aarch64.cat`, B2.3 coherence: a read is ordered
    before every write coherence-after the write it read from). -/
def fr (x : Exec) : Rel := x.rf.inv.comp x.co

/-- Internal reads-from: same-core `rf` (`aarch64.cat` `rfi = rf & int`). -/
def rfi (x : Exec) : Rel := x.rf.filter (sameCorePair x)

/-- External reads-from: cross-core `rf` (`aarch64.cat` `rfe = rf & ext`,
    B2.3 observed-before source). -/
def rfe (x : Exec) : Rel := x.rf.filter fun p => !(sameCorePair x p)

/-- External coherence order: cross-core `co` (`aarch64.cat` `coe = co & ext`,
    B2.3 observed-before source). -/
def coe (x : Exec) : Rel := x.co.filter fun p => !(sameCorePair x p)

/-- Per-location program order: `po` restricted to same-address pairs
    (`aarch64.cat` `po-loc`, B2.3 per-location coherence). -/
def po_loc (x : Exec) : Rel := x.po.filter (sameLocPair x)

end Arm

/-
CUTS: helpers plus the derived coherence relations; `dob`, `obs`, `ob`
and the three axioms land in the next steps.
No theorem yet, so no `#print axioms`.
-/
