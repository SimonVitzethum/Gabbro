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
    LDAPR (RCpc) orders po-later reads only. Stated with `any` so every
    proof goes through `List.any_eq_false` uniformly. -/
def acqHolds (x : Exec) (a c : Nat) : Bool :=
  poMem x a c &&
    x.evs.any fun e =>
      e.id == a && ((e.isAcquire && memOf x c) || (e.isAcquirePC && rdOf x c))

/-- Release clause (Arm ARM B2.3): STLR is ordered after po-earlier reads
    and writes. -/
def relHolds (x : Exec) (a c : Nat) : Bool :=
  poMem x a c && memOf x a &&
    x.evs.any fun e => e.id == c && e.isRelease

/-- Release-acquire (Arm ARM B2.3): STLR ;po; LDAR, and STLR ;po; LDAPR
    (release sequence head of the RCpc extension), are ordered. -/
def relAcqHolds (x : Exec) (a c : Nat) : Bool :=
  poMem x a c &&
    (x.evs.any fun e => e.id == a && e.isRelease) &&
    (x.evs.any fun e => e.id == c && (e.isAcquire || e.isAcquirePC))

/-- ISB (Sail: impdefs.sail:888-890, instrs64.sail:22746-22748): flushes the
    pipeline so later instructions are fetched afresh. At the data-memory
    level v1 models the control-dependency leg: a read `a` with a ctrl edge
    to an ISB `b` is ordered before every po-later data access `c`. The
    fetch half (later fetches see the ISB) has no fetch event in this model
    and stays CUTS. -/
def Ev.isIsb : Ev → Bool
  | { kind := .barrier .isb, .. } => true
  | _ => false

def ctrlMem (x : Exec) (a b : Nat) : Bool :=
  x.ctrl.any fun p => p.1 == a && p.2 == b

def isbHolds (x : Exec) (a c : Nat) : Bool :=
  x.evs.any fun b =>
    ctrlMem x a b.id && poMem x b.id c && b.isIsb && rdOf x a &&
      memOf x c

/-- Barrier-ordered-before: the function agent 07 plugs into
    `OrderingParts.bob`. -/
def bobHolds (x : Exec) (a c : Nat) : Bool :=
  dmbHolds x a c || dsbHolds x a c || acqHolds x a c || relHolds x a c ||
    relAcqHolds x a c || isbHolds x a c

def bob (x : Exec) : Rel :=
  (x.evs.flatMap fun a => x.evs.map fun c => (a.id, c.id)).filter
    fun p => bobHolds x p.1 p.2

/-- Message passing with NO barrier: core 0 writes x then y, core 1 reads
    y then x. Nothing here is ordered by `bob`. -/
def mpNone : Exec :=
  { evs := [{ id := 0, core := 0, kind := .write ⟨0, 4, .plain, false⟩, val := 1 },
            { id := 1, core := 0, kind := .write ⟨8, 4, .plain, false⟩, val := 1 },
            { id := 2, core := 1, kind := .read ⟨8, 4, .plain, false⟩, val := 1 },
            { id := 3, core := 1, kind := .read ⟨0, 4, .plain, false⟩, val := 0 }],
    po := [(0, 1), (2, 3)], addr := [], data := [], ctrl := [],
    rf := [(1, 2)], co := [], rmw := [] }

/-- Message passing with a `DMB ST` (inner-shareable) between the writes. -/
def mpDmbSt : Exec :=
  { evs := [{ id := 0, core := 0, kind := .write ⟨0, 4, .plain, false⟩, val := 1 },
            { id := 1, core := 0, kind := .barrier (.dmb .ish .st), val := 0 },
            { id := 2, core := 0, kind := .write ⟨8, 4, .plain, false⟩, val := 1 },
            { id := 3, core := 1, kind := .read ⟨8, 4, .plain, false⟩, val := 1 },
            { id := 4, core := 1, kind := .read ⟨0, 4, .plain, false⟩, val := 0 }],
    po := [(0, 1), (1, 2), (0, 2), (3, 4)], addr := [], data := [],
    ctrl := [], rf := [(2, 3)], co := [], rmw := [] }

/-- Message passing with a `DMB LD` (inner-shareable) between the reads. -/
def mpDmbLd : Exec :=
  { evs := [{ id := 0, core := 0, kind := .write ⟨0, 4, .plain, false⟩, val := 1 },
            { id := 1, core := 0, kind := .write ⟨8, 4, .plain, false⟩, val := 1 },
            { id := 2, core := 1, kind := .read ⟨8, 4, .plain, false⟩, val := 1 },
            { id := 3, core := 1, kind := .barrier (.dmb .ish .ld), val := 0 },
            { id := 4, core := 1, kind := .read ⟨0, 4, .plain, false⟩, val := 0 }],
    po := [(0, 1), (2, 3), (3, 4), (2, 4)], addr := [], data := [],
    ctrl := [], rf := [(1, 2)], co := [], rmw := [] }

/-- Message passing with STLR/LDAR instead of barriers. -/
def mpRelAcq : Exec :=
  { evs := [{ id := 0, core := 0, kind := .write ⟨0, 4, .plain, false⟩, val := 1 },
            { id := 1, core := 0, kind := .write ⟨8, 4, .release, false⟩, val := 1 },
            { id := 2, core := 1, kind := .read ⟨8, 4, .acquire, false⟩, val := 1 },
            { id := 3, core := 1, kind := .read ⟨0, 4, .plain, false⟩, val := 0 }],
    po := [(0, 1), (2, 3)], addr := [], data := [], ctrl := [],
    rf := [(1, 2)], co := [], rmw := [] }

/-- Witness: the barrier-free shape is NOT ordered by `bob`. -/
theorem mp_none_bob_empty : bob mpNone = [] := by decide

/-- Witness: with `DMB ST` the two writes ARE ordered. -/
theorem mp_dmb_st_orders : (0, 2) ∈ bob mpDmbSt := by decide

/-- Witness: with `DMB LD` the two reads ARE ordered. -/
theorem mp_dmb_ld_orders : (2, 4) ∈ bob mpDmbLd := by decide

/-- Witness: the release write IS ordered after the earlier write. -/
theorem mp_rel_orders : (0, 1) ∈ bob mpRelAcq := by decide

/-- Witness: the later read IS ordered after the acquire. -/
theorem mp_acq_orders : (2, 3) ∈ bob mpRelAcq := by decide

/-- A plain execution (no barrier, acquire or release event anywhere) has no
    DMB edge: every `any` witness would need one. -/
theorem dmbHolds_false_of_plain (x : Exec) (a c : Nat)
    (h : x.evs.all (fun e => decide ((e.isDmbFull || e.isDmbLd || e.isDmbSt) = false)) = true) :
    dmbHolds x a c = false := by
  unfold dmbHolds
  rw [List.any_eq_false]
  intro b hb hcon
  have hpred := (List.all_eq_true.mp h) b hb
  have hbig : (b.isDmbFull || b.isDmbLd || b.isDmbSt) = false :=
    of_decide_eq_true hpred
  simp only [Bool.or_eq_false_iff] at hbig
  obtain ⟨⟨hf, hl⟩, hs⟩ := hbig
  have hcond : (poMem x a b.id && poMem x b.id c &&
      ((b.isDmbFull && memOf x a && memOf x c) ||
       (b.isDmbLd && rdOf x a && memOf x c) ||
       (b.isDmbSt && wrOf x a && wrOf x c))) = false := by
    simp [hf, hl, hs]
  rw [hcond] at hcon
  simp at hcon

/-- Same for DSB. -/
theorem dsbHolds_false_of_plain (x : Exec) (a c : Nat)
    (h : x.evs.all (fun e => decide ((e.isDsbFull || e.isDsbLd || e.isDsbSt) = false)) = true) :
    dsbHolds x a c = false := by
  unfold dsbHolds
  rw [List.any_eq_false]
  intro b hb hcon
  have hpred := (List.all_eq_true.mp h) b hb
  have hbig : (b.isDsbFull || b.isDsbLd || b.isDsbSt) = false :=
    of_decide_eq_true hpred
  simp only [Bool.or_eq_false_iff] at hbig
  obtain ⟨⟨hf, hl⟩, hs⟩ := hbig
  have hcond : (poMem x a b.id && poMem x b.id c &&
      ((b.isDsbFull && memOf x a && memOf x c) ||
       (b.isDsbLd && rdOf x a && memOf x c) ||
       (b.isDsbSt && wrOf x a && wrOf x c))) = false := by
    simp [hf, hl, hs]
  rw [hcond] at hcon
  simp at hcon

/-- Same for the acquire leg. -/
theorem acqHolds_false_of_plain (x : Exec) (a c : Nat)
    (h : x.evs.all (fun e => decide ((e.isAcquire || e.isAcquirePC) = false)) = true) :
    acqHolds x a c = false := by
  unfold acqHolds
  cases hP : poMem x a c with
  | false => rfl
  | true =>
    show (x.evs.any fun e => e.id == a &&
      ((e.isAcquire && memOf x c) || (e.isAcquirePC && rdOf x c))) = false
    rw [List.any_eq_false]
    intro e he hcon
    have hpred := (List.all_eq_true.mp h) e he
    have hbig : (e.isAcquire || e.isAcquirePC) = false :=
      of_decide_eq_true hpred
    simp only [Bool.or_eq_false_iff] at hbig
    obtain ⟨ha, hq⟩ := hbig
    rw [ha, hq] at hcon
    simp at hcon

/-- Same for the release leg. -/
theorem relHolds_false_of_plain (x : Exec) (a c : Nat)
    (h : x.evs.all (fun e => decide (e.isRelease = false)) = true) :
    relHolds x a c = false := by
  unfold relHolds
  cases hP : (poMem x a c && memOf x a) with
  | false => rfl
  | true =>
    show (x.evs.any fun e => e.id == c && e.isRelease) = false
    rw [List.any_eq_false]
    intro e he hcon
    have hpred := (List.all_eq_true.mp h) e he
    have hrel : e.isRelease = false := of_decide_eq_true hpred
    rw [hrel] at hcon
    simp at hcon

/-- Same for the release-acquire leg. -/
theorem relAcqHolds_false_of_plain (x : Exec) (a c : Nat)
    (h : x.evs.all (fun e => decide ((e.isRelease || e.isAcquire || e.isAcquirePC) = false)) = true) :
    relAcqHolds x a c = false := by
  unfold relAcqHolds
  cases hP : poMem x a c with
  | false => rfl
  | true =>
    have h1 : (x.evs.any fun e => e.id == a && e.isRelease) = false := by
      rw [List.any_eq_false]
      intro e he hcon
      have hpred := (List.all_eq_true.mp h) e he
      have hbig : (e.isRelease || e.isAcquire || e.isAcquirePC) = false :=
        of_decide_eq_true hpred
      simp only [Bool.or_eq_false_iff] at hbig
      obtain ⟨⟨hr, _⟩, _⟩ := hbig
      rw [hr] at hcon
      simp at hcon
    simp [h1]

/-- Same for the ISB leg. -/
theorem isbHolds_false_of_plain (x : Exec) (a c : Nat)
    (h : x.evs.all (fun e => decide (e.isIsb = false)) = true) :
    isbHolds x a c = false := by
  unfold isbHolds
  rw [List.any_eq_false]
  intro b hb hcon
  have hpred := (List.all_eq_true.mp h) b hb
  have hisb : b.isIsb = false := of_decide_eq_true hpred
  have hcond : (ctrlMem x a b.id && poMem x b.id c && b.isIsb && rdOf x a &&
      memOf x c) = false := by
    simp [hisb]
  rw [hcond] at hcon
  simp at hcon

/-
CUTS: `bob` covers DMB and acquire/release; DSB, ISB and all theorems open.
-/
