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
import Arm.Mem.Exec

namespace Arm

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

/-- LDAPR (acquirePC, RCpc) orders a po-later read, but not a po-later write. -/
def mpAcqPC : Exec :=
  { evs := [{ id := 0, core := 0, kind := .read ⟨8, 4, .acquirePC, false⟩, val := 1 },
            { id := 1, core := 0, kind := .read ⟨0, 4, .plain, false⟩, val := 0 },
            { id := 2, core := 0, kind := .write ⟨8, 4, .plain, false⟩, val := 1 }],
    po := [(0, 1), (0, 2)], addr := [], data := [], ctrl := [],
    rf := [], co := [], rmw := [] }

/-- Same-core STLR followed by LDAR: the `[L];po;[A]` leg fires. -/
def mpRelAcqSA : Exec :=
  { evs := [{ id := 0, core := 0, kind := .write ⟨8, 4, .release, false⟩, val := 1 },
            { id := 1, core := 0, kind := .read ⟨8, 4, .acquire, false⟩, val := 1 }],
    po := [(0, 1)], addr := [], data := [], ctrl := [],
    rf := [], co := [], rmw := [] }

/-- A read with a control dependency to an ISB orders po-later accesses. -/
def mpIsb : Exec :=
  { evs := [{ id := 0, core := 0, kind := .read ⟨0, 4, .plain, false⟩, val := 0 },
            { id := 1, core := 0, kind := .barrier .isb, val := 0 },
            { id := 2, core := 0, kind := .write ⟨8, 4, .plain, false⟩, val := 1 }],
    po := [(0, 1), (1, 2), (0, 2)], addr := [], data := [],
    ctrl := [(0, 1)], rf := [], co := [], rmw := [] }

/-- Message passing with a `DSB ST` between the writes. -/
def mpDsbSt : Exec :=
  { evs := [{ id := 0, core := 0, kind := .write ⟨0, 4, .plain, false⟩, val := 1 },
            { id := 1, core := 0, kind := .barrier (.dsb .ish .st), val := 0 },
            { id := 2, core := 0, kind := .write ⟨8, 4, .plain, false⟩, val := 1 },
            { id := 3, core := 1, kind := .read ⟨8, 4, .plain, false⟩, val := 1 },
            { id := 4, core := 1, kind := .read ⟨0, 4, .plain, false⟩, val := 0 }],
    po := [(0, 1), (1, 2), (0, 2), (3, 4)], addr := [], data := [],
    ctrl := [], rf := [(2, 3)], co := [], rmw := [] }

/-- Witness: LDAPR orders the po-later read. -/
theorem mp_acqpc_orders_read : (0, 1) ∈ bob mpAcqPC := by decide

/-- Witness: LDAPR does NOT order the po-later write (RCpc weakness). -/
theorem mp_acqpc_write_unordered : bob mpAcqPC = [(0, 1)] := by decide

/-- Witness: same-core STLR `;po;` LDAR is ordered. -/
theorem mp_relacq_sa_orders : (0, 1) ∈ bob mpRelAcqSA := by decide

/-- Witness: it is ordered by exactly the release-acquire leg. -/
theorem mp_relacq_sa_leg : relAcqHolds mpRelAcqSA 0 1 = true := by decide

/-- Witness: ISB with a control dependency orders the later access. -/
theorem mp_isb_orders : (0, 2) ∈ bob mpIsb := by decide

/-- Witness: with `DSB ST` the two writes ARE ordered. -/
theorem mp_dsb_st_orders : (0, 2) ∈ bob mpDsbSt := by decide

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

/-- One concrete plain event, shared by the splitter witness. -/
def plainEv : Ev := ⟨0, 0, .write ⟨0, 4, .plain, false⟩, 1⟩

/-- Witnesses: each clause lemma fires (as `false`) on the non-degenerate
    barrier-free MP fixture — none of them is vacuous. -/
theorem dmbHolds_false_of_plain_zeuge : dmbHolds mpNone 0 3 = false := by decide

theorem dsbHolds_false_of_plain_zeuge : dsbHolds mpNone 0 3 = false := by decide

theorem acqHolds_false_of_plain_zeuge : acqHolds mpNone 0 3 = false := by decide

theorem relHolds_false_of_plain_zeuge : relHolds mpNone 0 3 = false := by decide

theorem relAcqHolds_false_of_plain_zeuge : relAcqHolds mpNone 0 3 = false := by decide

theorem isbHolds_false_of_plain_zeuge : isbHolds mpNone 0 3 = false := by decide

/-- Split one whole-execution plainness fact into the six per-clause facts. -/
theorem big_plain_split (e : Ev)
    (h : decide ((e.isDmbFull || e.isDmbLd || e.isDmbSt || e.isDsbFull || e.isDsbLd || e.isDsbSt || e.isAcquire || e.isAcquirePC || e.isRelease || e.isIsb) = false) = true) :
    (e.isDmbFull || e.isDmbLd || e.isDmbSt) = false ∧
    (e.isDsbFull || e.isDsbLd || e.isDsbSt) = false ∧
    (e.isAcquire || e.isAcquirePC) = false ∧
    e.isRelease = false ∧
    (e.isRelease || e.isAcquire || e.isAcquirePC) = false ∧
    e.isIsb = false := by
  have hbig : (e.isDmbFull || e.isDmbLd || e.isDmbSt || e.isDsbFull || e.isDsbLd || e.isDsbSt || e.isAcquire || e.isAcquirePC || e.isRelease || e.isIsb) = false :=
    of_decide_eq_true h
  simp only [Bool.or_eq_false_iff] at hbig
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hf, hl⟩, hs⟩, hdf⟩, hdl⟩, hds⟩, haq⟩, hqp⟩, hrl⟩, his⟩ := hbig
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Bool.or_eq_false_iff]
    exact ⟨⟨hf, hl⟩, hs⟩
  · simp only [Bool.or_eq_false_iff]
    exact ⟨⟨hdf, hdl⟩, hds⟩
  · simp only [Bool.or_eq_false_iff]
    exact ⟨haq, hqp⟩
  · exact hrl
  · simp only [Bool.or_eq_false_iff]
    exact ⟨⟨hrl, haq⟩, hqp⟩
  · exact his

/-- Witness: the splitter fires on a concrete plain event. -/
theorem big_plain_split_zeuge :
    (plainEv.isDmbFull || plainEv.isDmbLd || plainEv.isDmbSt) = false ∧
    (plainEv.isDsbFull || plainEv.isDsbLd || plainEv.isDsbSt) = false ∧
    (plainEv.isAcquire || plainEv.isAcquirePC) = false ∧
    plainEv.isRelease = false ∧
    (plainEv.isRelease || plainEv.isAcquire || plainEv.isAcquirePC) = false ∧
    plainEv.isIsb = false :=
  big_plain_split _ (by decide)

/-- A plain access is never ordered by `bob`: with no DMB, DSB, ISB,
    acquire or release event anywhere in the execution, every clause of
    `bobHolds` is false, so `bob` is empty. -/
theorem plain_never_bob (x : Exec)
    (h : x.evs.all (fun e => decide ((e.isDmbFull || e.isDmbLd || e.isDmbSt || e.isDsbFull || e.isDsbLd || e.isDsbSt || e.isAcquire || e.isAcquirePC || e.isRelease || e.isIsb) = false)) = true) :
    bob x = [] := by
  have hdmb : x.evs.all (fun e => decide ((e.isDmbFull || e.isDmbLd || e.isDmbSt) = false)) = true := by
    rw [List.all_eq_true] at h ⊢
    intro e he
    have hp := h e he
    have hs : (e.isDmbFull || e.isDmbLd || e.isDmbSt) = false :=
      (big_plain_split e hp).1
    rw [hs]
    rfl
  have hdsb : x.evs.all (fun e => decide ((e.isDsbFull || e.isDsbLd || e.isDsbSt) = false)) = true := by
    rw [List.all_eq_true] at h ⊢
    intro e he
    have hp := h e he
    have hs : (e.isDsbFull || e.isDsbLd || e.isDsbSt) = false :=
      (big_plain_split e hp).2.1
    rw [hs]
    rfl
  have hacq : x.evs.all (fun e => decide ((e.isAcquire || e.isAcquirePC) = false)) = true := by
    rw [List.all_eq_true] at h ⊢
    intro e he
    have hp := h e he
    have hs : (e.isAcquire || e.isAcquirePC) = false :=
      (big_plain_split e hp).2.2.1
    rw [hs]
    rfl
  have hrel : x.evs.all (fun e => decide (e.isRelease = false)) = true := by
    rw [List.all_eq_true] at h ⊢
    intro e he
    have hp := h e he
    have hs : e.isRelease = false := (big_plain_split e hp).2.2.2.1
    rw [hs]
    rfl
  have hrelacq : x.evs.all (fun e => decide ((e.isRelease || e.isAcquire || e.isAcquirePC) = false)) = true := by
    rw [List.all_eq_true] at h ⊢
    intro e he
    have hp := h e he
    have hs : (e.isRelease || e.isAcquire || e.isAcquirePC) = false :=
      (big_plain_split e hp).2.2.2.2.1
    rw [hs]
    rfl
  have hisb : x.evs.all (fun e => decide (e.isIsb = false)) = true := by
    rw [List.all_eq_true] at h ⊢
    intro e he
    have hp := h e he
    have hs : e.isIsb = false := (big_plain_split e hp).2.2.2.2.2
    rw [hs]
    rfl
  have h1 : ∀ (a c : Nat), dmbHolds x a c = false :=
    fun a c => dmbHolds_false_of_plain x a c hdmb
  have h2 : ∀ (a c : Nat), dsbHolds x a c = false :=
    fun a c => dsbHolds_false_of_plain x a c hdsb
  have h3 : ∀ (a c : Nat), acqHolds x a c = false :=
    fun a c => acqHolds_false_of_plain x a c hacq
  have h4 : ∀ (a c : Nat), relHolds x a c = false :=
    fun a c => relHolds_false_of_plain x a c hrel
  have h5 : ∀ (a c : Nat), relAcqHolds x a c = false :=
    fun a c => relAcqHolds_false_of_plain x a c hrelacq
  have h6 : ∀ (a c : Nat), isbHolds x a c = false :=
    fun a c => isbHolds_false_of_plain x a c hisb
  unfold bob
  rw [List.filter_eq_nil_iff]
  intro p _
  have hfalse : bobHolds x p.1 p.2 = false := by
    unfold bobHolds
    rw [h1 p.1 p.2, h2 p.1 p.2, h3 p.1 p.2, h4 p.1 p.2, h5 p.1 p.2,
      h6 p.1 p.2]
    rfl
  rw [hfalse]
  exact by decide

/-- Witness: the plainness premise is load-bearing — the fenced shape IS
    ordered, so `plain_never_bob` is not vacuous. -/
theorem plain_never_bob_zeuge : bob mpDmbSt ≠ [] := by decide

#print axioms plain_never_bob
#print axioms dmbHolds_false_of_plain
#print axioms dsbHolds_false_of_plain
#print axioms acqHolds_false_of_plain
#print axioms relHolds_false_of_plain
#print axioms relAcqHolds_false_of_plain
#print axioms isbHolds_false_of_plain
#print axioms big_plain_split

/-
CUTS:
- Proved: the six `bob` clauses (DMB full/ld/st, DSB data classes, LDAR,
  LDAPR/RCpc, STLR, STLR`;po;`LDAR/LDAPR, ISB-with-ctrl), `bob` itself, the
  MP witness facts, and `plain_never_bob` with its splitter and witnesses.
- Shareability v1: only `ish`/`sy` barriers order observers (`Domain.v1Orders`);
  `nsh`/`osh` barriers order nothing. No per-observer domainFiltering yet.
- DSB completion beyond data accesses has no event in this model (no
  instruction-completion event): only the data classes are ordered here.
- ISB fetch half has no event in this model (no fetch event): only the
  read`;ctrl;`ISB`;po;`mem leg is ordered here.
- `Exec` well-formedness (unique ids, po transitive/irreflexive, ctrl shape)
  is agent 06's `Exec.lean`, not stated here; `bob` reads `po`/`ctrl` as given.
- `bob` is one leg for agent 07's `OrderingParts.bob`; coherence, reads-from,
  from-reads, dependencies `addr`/`data`, `rmw` and the outer Arm order are
  not in this file.
- `Barrier` (`Arm/Basic.lean`, frozen) has no SB/SSBB/PSSBB form, so those
  barriers cannot be named here; proposed as vocabulary follow-up.
- The `excl` (exclusive-pair) flag carries no extra `bob` edge: exclusives
  order through their `ord` (plain/acquire/release) and barriers, as Arm lists.
-/
