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

/-- External from-reads: cross-core `fr` (`aarch64.cat` `fre = fr & ext`,
    B2.3 observed-before source). -/
def fre (x : Exec) : Rel := (fr x).filter fun p => !(sameCorePair x p)

/-- Dependency-ordered-before (`aarch64.cat` `dob`, B2.3 dependency rules):
    address and data dependencies; control dependency to a write; control or
    address dependency followed by `po` to a write; address dependency followed
    by `po` to a write (a subset of the previous clause, kept for readability);
    address or data dependency feeding a write observed by an internal read. -/
def dob (x : Exec) : Rel :=
  let ctrlW : Rel := x.ctrl.filter (targetIs isWriteEv x)
  let ctrlAddrPoW : Rel :=
    ((x.ctrl.union x.addr).comp x.po).filter (targetIs isWriteEv x)
  let addrPoW : Rel := (x.addr.comp x.po).filter (targetIs isWriteEv x)
  let depRfi : Rel := (x.addr.union x.data).comp (rfi x)
  ((x.addr.union x.data).union ctrlW).union (ctrlAddrPoW.union (addrPoW.union depRfi))

/-- Observed-before: the cross-core communication orders (`aarch64.cat`
    `obs = rfe | fre | coe`, B2.3 external visibility). -/
def obs (x : Exec) : Rel := ((rfe x).union (fre x)).union (coe x)

/-- Ordered-before: `obs | dob | aob | bob` (`aarch64.cat`, B2.3). `aob` and
    `bob` are plugged in by agents 09 and 10. -/
def ob (parts : OrderingParts) (x : Exec) : Rel :=
  (((obs x).union (dob x)).union parts.aob).union parts.bob

/-- Coherence axiom: per-location order is acyclic (`aarch64.cat`
    `acyclic po-loc | ca | rf | fr as internal`, B2.3 coherence). -/
def internal (x : Exec) : Bool :=
  Rel.acyclic (Rel.union (Rel.union (Rel.union (po_loc x) x.co) x.rf) (fr x)) x.size

/-- External axiom: ordered-before is acyclic (`aarch64.cat`
    `acyclic ob as external`, B2.3 external visibility). -/
def external (parts : OrderingParts) (x : Exec) : Bool :=
  Rel.acyclic (ob parts x) x.size

/-- Atomicity axiom: no exclusive/atomic pair is split by an intervening
    external write (`aarch64.cat` `empty rmw & (fre;coe) as atomic`). -/
def atomic (x : Exec) : Bool :=
  (Rel.inter x.rmw ((fre x).comp (coe x))).isEmpty

/-- A candidate execution is consistent if it satisfies all three axioms.
    The conjunction is well-formedness-independent: `Exec` well-formedness
    (unique ids, `rf`/`co` shape) is owned by agent 06. -/
def consistent (parts : OrderingParts) (x : Exec) : Bool :=
  internal x && external parts x && atomic x

/-- A plain 8-byte access at address `a`. -/
def acc (a : Addr) : Access := { addr := a, size := 8, ord := .plain, excl := false }

/-- Message passing with initial writes: allowed without barriers, so all
    three axioms hold under the empty plug-in. -/
def xCoherent : Exec :=
  { evs := [⟨0, 0, .write (acc 0#64), 1⟩, ⟨1, 0, .write (acc 8#64), 1⟩,
            ⟨2, 1, .read (acc 8#64), 1⟩, ⟨3, 1, .read (acc 0#64), 0⟩,
            ⟨4, 0, .write (acc 0#64), 0⟩, ⟨5, 0, .write (acc 8#64), 0⟩]
    po := [(0, 1), (2, 3)], addr := [], data := [], ctrl := []
    rf := [(4, 3), (1, 2)], co := [(4, 0), (5, 1)], rmw := [] }

/-- Coherence violation: two same-location writes with a cyclic `co`. -/
def xCoherenceBad : Exec :=
  { evs := [⟨0, 0, .write (acc 0#64), 1⟩, ⟨1, 0, .write (acc 0#64), 2⟩]
    po := [], addr := [], data := [], ctrl := []
    rf := [], co := [(0, 1), (1, 0)], rmw := [] }

/-- Load buffering with address dependencies: the classic `external` (B2.3
    `ob`) violation, coherent and atomic in isolation. -/
def xLbAddr : Exec :=
  { evs := [⟨0, 0, .read (acc 0#64), 1⟩, ⟨1, 0, .write (acc 8#64), 1⟩,
            ⟨2, 1, .read (acc 8#64), 1⟩, ⟨3, 1, .write (acc 0#64), 1⟩]
    po := [(0, 1), (2, 3)], addr := [(0, 1), (2, 3)], data := [], ctrl := []
    rf := [(1, 2), (3, 0)], co := [], rmw := [] }

/-- Split exclusive pair: an external write lands between the `rmw` read and
    write (`fre;coe` meets `rmw`), coherent and externally ordered. -/
def xRmwSplit : Exec :=
  { evs := [⟨0, 0, .read (acc 0#64), 7⟩, ⟨1, 0, .write (acc 0#64), 8⟩,
            ⟨2, 1, .write (acc 0#64), 9⟩, ⟨3, 0, .write (acc 0#64), 7⟩]
    po := [], addr := [], data := [], ctrl := []
    rf := [(3, 0)], co := [(3, 2), (2, 1)], rmw := [(0, 1)] }

/-- The message-passing witness satisfies all three axioms. -/
theorem wit_coherent_ok : consistent noParts xCoherent = true := by decide

/-- The cyclic-`co` witness fails coherence, and nothing else. -/
theorem wit_coherence_bad_internal : internal xCoherenceBad = false := by decide

theorem wit_coherence_bad_external : external noParts xCoherenceBad = true := by decide

theorem wit_coherence_bad_atomic : atomic xCoherenceBad = true := by decide

theorem wit_coherence_bad : consistent noParts xCoherenceBad = false := by decide

/-- The load-buffering witness fails the external axiom, and nothing else. -/
theorem wit_lb_internal : internal xLbAddr = true := by decide

theorem wit_lb_external : external noParts xLbAddr = false := by decide

theorem wit_lb_atomic : atomic xLbAddr = true := by decide

theorem wit_lb : consistent noParts xLbAddr = false := by decide

/-- The split-pair witness fails atomicity, and nothing else. -/
theorem wit_rmw_internal : internal xRmwSplit = true := by decide

theorem wit_rmw_external : external noParts xRmwSplit = true := by decide

theorem wit_rmw_atomic : atomic xRmwSplit = false := by decide

theorem wit_rmw : consistent noParts xRmwSplit = false := by decide

end Arm

/-
CUTS: model complete, witnesses pending. `dob` clause list follows the
published `aarch64.cat` from knowledge (see report), not a measured copy.
No theorem yet, so no `#print axioms`.
-/
