/-
  File:      Arm/Mem/Dep.lean
  Subject:   Dependency detection by perturbation: re-run an `Eff` tree with
             one read value changed and compare the later events.
  Sail:      the replayed effects are `__ReadMem`/`__WriteMem` of
             sail-arm/arm-v9.4-a/src/mem.sail lines 44-57, as in
             `Arm/Mem/Trace.lean`; the limitation proved here is that the
             `Eff` interface (`Arm/Isa/Monad.lean`) hides data flow inside Lean
             continuations, so syntactic (register-flow) dependencies in the
             sense of the Arm ASL are invisible to any function of events.
-/
import Arm.Mem.Exec

namespace Arm

/-- Instrumented run: events plus the event id of each read, in read order. -/
structure DepOut where
  evs : List Ev
  rids : List Nat
  deriving Repr

/-- Like `runEff`, but records every read's event id in `rids`. -/
def runDep : Nat → Eff Unit → CoreId → Nat → Nat → (Nat → Nat) → Option (DepOut × Nat × Nat)
  | 0, _, _, _, _, _ => none
  | f + 1, e, core, next, nr, sup =>
    match e with
    | .ret _ => some ({ evs := [], rids := [] }, next, nr)
    | .rdX _ k => runDep f (k 0) core next nr sup
    | .wrX _ _ k => runDep f k core next nr sup
    | .rdV _ k => runDep f (k 0) core next nr sup
    | .wrV _ _ k => runDep f k core next nr sup
    | .rdPC k => runDep f (k 0) core next nr sup
    | .wrPC _ k => runDep f k core next nr sup
    | .rdNZCV k => runDep f (k 0) core next nr sup
    | .wrNZCV _ k => runDep f k core next nr sup
    | .rdSys _ k => runDep f (k 0) core next nr sup
    | .wrSys _ _ k => runDep f k core next nr sup
    | .rdMem a k =>
      let v := sup nr
      match runDep f (k v) core (next + 1) (nr + 1) sup with
      | none => none
      | some (o, nx, nrr) =>
        some ({ evs := { id := next, core, kind := .read a, val := v } :: o.evs,
                rids := next :: o.rids }, nx, nrr)
    | .wrMem a v k =>
      match runDep f k core (next + 1) nr sup with
      | none => none
      | some (o, nx, nrr) =>
        some ({ evs := { id := next, core, kind := .write a, val := v } :: o.evs,
                rids := o.rids }, nx, nrr)
    | .bar b k =>
      match runDep f k core (next + 1) nr sup with
      | none => none
      | some (o, nx, nrr) =>
        some ({ evs := { id := next, core, kind := .barrier b, val := 0 } :: o.evs,
                rids := o.rids }, nx, nrr)
    | .raise _ => some ({ evs := [], rids := [] }, next, nr)

/-- Events of one run, forgetting ids and read counts. -/
def evsOf (p : Eff Unit) (core next fuel : Nat) (s : Nat → Nat) : Option (List Ev) :=
  match runDep fuel p core next 0 s with
  | none => none
  | some (o, _, _) => some o.evs

/-- Two read supplies agree except possibly at read `i`. -/
def AgreeExcept (s₁ s₂ : Nat → Nat) (i : Nat) : Prop :=
  ∀ j, j ≠ i → s₁ j = s₂ j

/-- The supply `sup` with read `i` re-answered by `v'`. -/
def pert (sup : Nat → Nat) (i v' : Nat) : Nat → Nat :=
  fun j => if j = i then v' else sup j

theorem pert_agree (sup : Nat → Nat) (i v' : Nat) :
    AgreeExcept (pert sup i v') sup i :=
  fun _j hj => if_neg hj

/-- Compare one pair of same-position events from the base and the perturbed
    run: changed address is an addr edge, changed written value a data edge,
    changed kind (or, in `cmpLater`, changed length) a ctrl edge. A later
    read whose value differs is ignored: read values are supply artifacts,
    never influenced through the tree. -/
def cmpEv (r : Nat) (e e' : Ev) : Rel × Rel × Rel :=
  if e.kind = e'.kind then
    if e.addr? = e'.addr? then
      if e.isWrite = true ∧ e'.isWrite = true then
        if e.val = e'.val then ([], [], [])
        else ([], [(r, e.id)], [])
      else ([], [], [])
    else ([(r, e.id)], [], [])
  else ([], [], [(r, e.id)])

/-- Compare two full runs position by position. -/
def cmpLater (r : Nat) : List Ev → List Ev → Rel × Rel × Rel
  | [], [] => ([], [], [])
  | [], e' :: _ => ([], [], [(r, e'.id)])
  | e :: _, [] => ([], [], [(r, e.id)])
  | e :: es, e' :: es' =>
    ((cmpEv r e e').1 ++ (cmpLater r es es').1,
     (cmpEv r e e').2.1 ++ (cmpLater r es es').2.1,
     (cmpEv r e e').2.2 ++ (cmpLater r es es').2.2)

/-- Dependency detection by perturbation: run `p` under `sup`, re-run it with
    read `i` re-answered by `v'`, and compare the two event lists. Returns the
    perturbed read's event id with the addr, data and ctrl edges out of it. -/
def detect (p : Eff Unit) (core next : Nat) (sup : Nat → Nat) (fuel : Nat)
    (i v' : Nat) : Option (Nat × Rel × Rel × Rel) :=
  match runDep fuel p core next 0 sup with
  | none => none
  | some (o, _, _) =>
    match o.rids[i]? with
    | none => none
    | some r =>
      match runDep fuel p core next 0 (pert sup i v') with
      | none => none
      | some (o', _, _) =>
        let (a, d, c) := cmpLater r o.evs o'.evs
        some (r, a, d, c)

/-- Written value of an event, if it is a write. -/
def evWriteVal : Option Ev → Option Nat
  | some e => if e.isWrite = true then some e.val else none
  | none => none

/-- Behavioural influence of read `i` on the address of event `e`: two runs
    whose supplies agree except at `i` show different addresses at `e`. -/
def AddrInfl (p : Eff Unit) (core next fuel i e : Nat) : Prop :=
  ∃ s₁ s₂ evs₁ evs₂ x₁ x₂, AgreeExcept s₁ s₂ i
    ∧ evsOf p core next fuel s₁ = some evs₁
    ∧ evsOf p core next fuel s₂ = some evs₂
    ∧ x₁ ∈ evs₁ ∧ x₂ ∈ evs₂ ∧ x₁.id = e ∧ x₂.id = e
    ∧ x₁.addr? ≠ x₂.addr?

/-- Behavioural influence of read `i` on the value written by event `e`. -/
def DataInfl (p : Eff Unit) (core next fuel i e : Nat) : Prop :=
  ∃ s₁ s₂ evs₁ evs₂ x₁ x₂, AgreeExcept s₁ s₂ i
    ∧ evsOf p core next fuel s₁ = some evs₁
    ∧ evsOf p core next fuel s₂ = some evs₂
    ∧ x₁ ∈ evs₁ ∧ x₂ ∈ evs₂ ∧ x₁.id = e ∧ x₂.id = e
    ∧ evWriteVal (some x₁) ≠ evWriteVal (some x₂)

/-- The kind sequences of two runs differ here: different lengths, or a
    position where the kinds differ. Mirrors `cmpLater`'s ctrl logic, so no
    injectivity reasoning is needed below. -/
def kindsNe : List Ev → List Ev → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => True
  | e :: es, e' :: es' => e.kind ≠ e'.kind ∨ kindsNe es es'

/-- Behavioural influence of read `i` on the later event structure: two runs
    whose supplies agree except at `i` run different kind sequences. -/
def CtrlInfl (p : Eff Unit) (core next fuel i : Nat) : Prop :=
  ∃ s₁ s₂ evs₁ evs₂, AgreeExcept s₁ s₂ i
    ∧ evsOf p core next fuel s₁ = some evs₁
    ∧ evsOf p core next fuel s₂ = some evs₂
    ∧ kindsNe evs₁ evs₂

theorem cmpEv_addr (r : Nat) (e e' : Ev) (t : Nat)
    (h : (r, t) ∈ (cmpEv r e e').1) :
    t = e.id ∧ e.addr? ≠ e'.addr? := by
  unfold cmpEv at h
  cases hk : decide (e.kind = e'.kind) with
  | true =>
    have hkk : e.kind = e'.kind := of_decide_eq_true hk
    rw [if_pos hkk] at h
    cases ha : decide (e.addr? = e'.addr?) with
    | true =>
      have haa : e.addr? = e'.addr? := of_decide_eq_true ha
      rw [if_pos haa] at h
      cases hw : decide (e.isWrite = true ∧ e'.isWrite = true) with
      | true =>
        have hww : e.isWrite = true ∧ e'.isWrite = true :=
          of_decide_eq_true hw
        rw [if_pos hww] at h
        cases hv : decide (e.val = e'.val) with
        | true =>
          have hvv : e.val = e'.val := of_decide_eq_true hv
          rw [if_pos hvv] at h
          simp at h
        | false =>
          have hvv : ¬ (e.val = e'.val) := of_decide_eq_false hv
          rw [if_neg hvv] at h
          simp at h
      | false =>
        have hww : ¬ (e.isWrite = true ∧ e'.isWrite = true) :=
          of_decide_eq_false hw
        rw [if_neg hww] at h
        simp at h
    | false =>
      have haa : ¬ (e.addr? = e'.addr?) := of_decide_eq_false ha
      rw [if_neg haa] at h
      simp only [List.mem_singleton] at h
      have hte : t = e.id := congrArg Prod.snd h
      exact ⟨hte, haa⟩
  | false =>
    have hkk : ¬ (e.kind = e'.kind) := of_decide_eq_false hk
    rw [if_neg hkk] at h
    simp at h

theorem cmpEv_data (r : Nat) (e e' : Ev) (t : Nat)
    (h : (r, t) ∈ (cmpEv r e e').2.1) :
    t = e.id ∧ evWriteVal (some e) ≠ evWriteVal (some e') := by
  unfold cmpEv at h
  cases hk : decide (e.kind = e'.kind) with
  | true =>
    have hkk : e.kind = e'.kind := of_decide_eq_true hk
    rw [if_pos hkk] at h
    cases ha : decide (e.addr? = e'.addr?) with
    | true =>
      have haa : e.addr? = e'.addr? := of_decide_eq_true ha
      rw [if_pos haa] at h
      cases hw : decide (e.isWrite = true ∧ e'.isWrite = true) with
      | true =>
        have hww : e.isWrite = true ∧ e'.isWrite = true :=
          of_decide_eq_true hw
        rw [if_pos hww] at h
        cases hv : decide (e.val = e'.val) with
        | true =>
          have hvv : e.val = e'.val := of_decide_eq_true hv
          rw [if_pos hvv] at h
          simp at h
        | false =>
          have hvv : ¬ (e.val = e'.val) := of_decide_eq_false hv
          rw [if_neg hvv] at h
          simp only [List.mem_singleton] at h
          have hte : t = e.id := congrArg Prod.snd h
          have w1 : evWriteVal (some e) = some e.val := by
            simp only [evWriteVal]
            rw [if_pos hww.1]
          have w2 : evWriteVal (some e') = some e'.val := by
            simp only [evWriteVal]
            rw [if_pos hww.2]
          rw [w1, w2]
          exact ⟨hte, by simpa using hvv⟩
      | false =>
        have hww : ¬ (e.isWrite = true ∧ e'.isWrite = true) :=
          of_decide_eq_false hw
        rw [if_neg hww] at h
        simp at h
    | false =>
      have haa : ¬ (e.addr? = e'.addr?) := of_decide_eq_false ha
      rw [if_neg haa] at h
      simp at h
  | false =>
    have hkk : ¬ (e.kind = e'.kind) := of_decide_eq_false hk
    rw [if_neg hkk] at h
    simp at h

theorem cmpEv_ctrl (r : Nat) (e e' : Ev) (t : Nat)
    (h : (r, t) ∈ (cmpEv r e e').2.2) : e.kind ≠ e'.kind := by
  unfold cmpEv at h
  cases hk : decide (e.kind = e'.kind) with
  | true =>
    have hkk : e.kind = e'.kind := of_decide_eq_true hk
    rw [if_pos hkk] at h
    cases ha : decide (e.addr? = e'.addr?) with
    | true =>
      have haa : e.addr? = e'.addr? := of_decide_eq_true ha
      rw [if_pos haa] at h
      cases hw : decide (e.isWrite = true ∧ e'.isWrite = true) with
      | true =>
        have hww : e.isWrite = true ∧ e'.isWrite = true :=
          of_decide_eq_true hw
        rw [if_pos hww] at h
        cases hv : decide (e.val = e'.val) with
        | true =>
          have hvv : e.val = e'.val := of_decide_eq_true hv
          rw [if_pos hvv] at h
          simp at h
        | false =>
          have hvv : ¬ (e.val = e'.val) := of_decide_eq_false hv
          rw [if_neg hvv] at h
          simp at h
      | false =>
        have hww : ¬ (e.isWrite = true ∧ e'.isWrite = true) :=
          of_decide_eq_false hw
        rw [if_neg hww] at h
        simp at h
    | false =>
      have haa : ¬ (e.addr? = e'.addr?) := of_decide_eq_false ha
      rw [if_neg haa] at h
      simp at h
  | false =>
    exact of_decide_eq_false hk

end Arm

/-
CUTS: skeleton only. `evsOf`, `AgreeExcept`/`pert`, `cmpEv`/`cmpLater`,
`detect`, the influence relations, the soundness proofs, the xor-invisibility
theorem and the per-kind witnesses are NOT yet written.
-/
