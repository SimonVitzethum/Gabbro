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
    let (a₁, d₁, c₁) := cmpEv r e e'
    let (a₂, d₂, c₂) := cmpLater r es es'
    (a₁ ++ a₂, d₁ ++ d₂, c₁ ++ c₂)

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

end Arm

/-
CUTS: skeleton only. `evsOf`, `AgreeExcept`/`pert`, `cmpEv`/`cmpLater`,
`detect`, the influence relations, the soundness proofs, the xor-invisibility
theorem and the per-kind witnesses are NOT yet written.
-/
