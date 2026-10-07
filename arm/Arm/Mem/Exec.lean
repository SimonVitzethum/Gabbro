/-
  File:      Arm/Mem/Exec.lean
  Subject:   Candidate executions from per-core traces, and their
             well-formedness check `Exec.wf`.
  Sail:      one trace replays one core's `__ReadMem`/`__WriteMem` effects of
             sail-arm/arm-v9.4-a/src/mem.sail lines 44-57; this file only
             combines traces of distinct cores into the object the memory
             model (agent 07) is a predicate on. Consistency itself is NOT
             defined here.
-/
import Arm.Mem.Trace

namespace Arm

/-- The candidate execution of several cores' runs for a chosen reads-from
    `rf` and coherence order `co` (`rmw` defaults to empty). Callers thread
    fresh event ids across traces; `Exec.wf` refuses overlaps. -/
def Exec.ofTraces (trs : List Trace) (rf co : Rel) (rmw : Rel := []) : Exec :=
  { evs  := trs.flatMap (·.evs)
    po   := trs.flatMap (·.po)
    addr := trs.flatMap (·.addr)
    data := trs.flatMap (·.data)
    ctrl := trs.flatMap (·.ctrl)
    rf, co, rmw }

/-- Event side conditions used by `wf`. -/
def Ev.isRead : Ev → Bool
  | { kind := .read _, .. } => true
  | _ => false

def Ev.isWrite : Ev → Bool
  | { kind := .write _, .. } => true
  | _ => false

def Ev.addr? : Ev → Option Addr
  | { kind := .read a, .. } => some a.addr
  | { kind := .write a, .. } => some a.addr
  | { kind := .barrier _, .. } => none

def Ev.size? : Ev → Option Nat
  | { kind := .read a, .. } => some a.size
  | { kind := .write a, .. } => some a.size
  | { kind := .barrier _, .. } => none

/-- Every read has exactly one write it reads from, with the same address,
    size and value. -/
def Exec.rfOk (x : Exec) : Bool :=
  x.rf.all (fun p =>
    match x.ev? p.1, x.ev? p.2 with
    | some w, some r => w.isWrite && r.isRead
    | _, _ => false)
  && x.evs.all fun e =>
    if e.isRead then
      match x.rf.filter (·.2 == e.id) with
      | [(w, _)] =>
        match x.ev? w with
        | some we =>
          we.isWrite && (we.addr? == e.addr?)
            && (we.size? == e.size?) && (we.val == e.val)
        | none => false
      | _ => false
    else true

/-- `co` is a strict total order per location: only same-address writes,
    irreflexive, transitive, and total over same-address writes. -/
def Exec.coOk (x : Exec) : Bool :=
  let ws := x.evs.filter (·.isWrite)
  x.co.all (fun p =>
    match x.ev? p.1, x.ev? p.2 with
    | some a, some b =>
      a.isWrite && b.isWrite && (a.addr? == b.addr?) && (p.1 != p.2)
    | _, _ => false)
  && !(x.co.any fun p => p.1 == p.2)
  && (x.co.comp x.co).all x.co.contains
  && ws.all fun a => ws.all fun b =>
    a.id == b.id || (a.addr? != b.addr?)
      || x.co.contains (a.id, b.id) || x.co.contains (b.id, a.id)

/-- `po` is per core and transitive (irreflexive with it: a strict order). -/
def Exec.poOk (x : Exec) : Bool :=
  x.po.all (fun p =>
    match x.ev? p.1, x.ev? p.2 with
    | some a, some b => (a.core == b.core) && (p.1 != p.2)
    | _, _ => false)
  && !(x.po.any fun p => p.1 == p.2)
  && (x.po.comp x.po).all x.po.contains

/-- Dependencies relate a read to a po-later event. -/
def Exec.depOk (x : Exec) : Bool :=
  (x.addr ++ x.data ++ x.ctrl).all fun p =>
    match x.ev? p.1 with
    | some a => a.isRead && x.po.contains p
    | none => false

/-- `rmw` pairs a read with a po-later write of the same core and address
    (one exclusive or atomic pair). -/
def Exec.rmwOk (x : Exec) : Bool :=
  x.rmw.all fun p =>
    match x.ev? p.1, x.ev? p.2 with
    | some r, some w =>
      r.isRead && w.isWrite && (r.core == w.core)
        && (r.addr? == w.addr?) && x.po.contains p
    | _, _ => false

/-- Well-formedness of a candidate execution (decidable): unique ids, and
    every clause above. -/
def Exec.wf (x : Exec) : Bool :=
  let ids := x.evs.map (·.id)
  (ids.length == ids.eraseDups.length)
    && x.rfOk && x.coOk && x.poOk && x.depOk && x.rmwOk

/-- Fixture address cell used by the planted examples. -/
def accX : Access := { addr := 0, size := 8, ord := .plain, excl := false }

/-- Good example: one core writes 1 and reads 1 back. -/
def exGood : Exec :=
  { evs := [{ id := 0, core := 0, kind := .write accX, val := 1 },
            { id := 1, core := 0, kind := .read accX, val := 1 }]
    po := [(0, 1)], addr := [], data := [], ctrl := []
    rf := [(0, 1)], co := [], rmw := [] }

theorem exGood_wf : Exec.wf exGood = true := by decide

/-- Bad: the read answers 2 but its write holds 1 (rf value mismatch). -/
def exBadRf : Exec :=
  { evs := [{ id := 0, core := 0, kind := .write accX, val := 1 },
            { id := 1, core := 0, kind := .read accX, val := 2 }]
    po := [(0, 1)], addr := [], data := [], ctrl := []
    rf := [(0, 1)], co := [], rmw := [] }

theorem exBadRf_wf : Exec.wf exBadRf = false := by decide

/-- Bad: two same-address writes with no `co` edge (totality fails). -/
def exBadCo : Exec :=
  { evs := [{ id := 0, core := 0, kind := .write accX, val := 1 },
            { id := 1, core := 0, kind := .write accX, val := 2 }]
    po := [(0, 1)], addr := [], data := [], ctrl := []
    rf := [], co := [], rmw := [] }

theorem exBadCo_wf : Exec.wf exBadCo = false := by decide

/-- Bad: a `po` edge across two cores. -/
def exBadPo : Exec :=
  { evs := [{ id := 0, core := 0, kind := .write accX, val := 1 },
            { id := 1, core := 1, kind := .write accX, val := 1 }]
    po := [(0, 1)], addr := [], data := [], ctrl := []
    rf := [], co := [(0, 1)], rmw := [] }

theorem exBadPo_wf : Exec.wf exBadPo = false := by decide

/-- Bad: a data edge starting at a write instead of a read. -/
def exBadDep : Exec :=
  { evs := [{ id := 0, core := 0, kind := .write accX, val := 1 },
            { id := 1, core := 0, kind := .read accX, val := 1 }]
    po := [(0, 1)], addr := [], data := [(0, 1)], ctrl := []
    rf := [(0, 1)], co := [], rmw := [] }

theorem exBadDep_wf : Exec.wf exBadDep = false := by decide

/-- Bad: an `rmw` pair across two cores. -/
def exBadRmw : Exec :=
  { evs := [{ id := 0, core := 0, kind := .read accX, val := 1 },
            { id := 1, core := 1, kind := .write accX, val := 1 },
            { id := 2, core := 1, kind := .write accX, val := 0 }]
    po := [(1, 2)], addr := [], data := [], ctrl := []
    rf := [(2, 0)], co := [(2, 1)], rmw := [(0, 1)] }

theorem exBadRmw_wf : Exec.wf exBadRmw = false := by decide

#print axioms exGood_wf
#print axioms exBadRf_wf
#print axioms exBadCo_wf
#print axioms exBadPo_wf
#print axioms exBadDep_wf
#print axioms exBadRmw_wf

end Arm

/-
CUTS: `Exec.ofTraces` and `Exec.wf` with all clauses are written. Good and
bad examples (planted refusals) and the two-core message-passing witness
assembled from `Eff` trees are NOT yet written.
-/
