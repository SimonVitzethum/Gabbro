/-
  File:      Arm/Lit/Enumerate.lean
  Subject:   Candidate executions of a litmus program: elaboration to `Exec` events
             plus enumeration of every `rf` choice and every total `co` per location.
  Note:      Test-bench code, not a Sail translation (no Sail line to cite). Until
             agent 07's `Arm/Mem/Axiomatic.lean` lands, consistency is an abstract
             parameter `cons : Exec -> Bool`. Sizes are fixed to 8 bytes per access
             and exclusives are absent (`excl := false`); recorded in CUTS.
-/
import Arm.Basic
import Arm.Mem.Event
import Arm.Lit.Prog

namespace Arm.Lit

/-- Address of litmus location `l`. All litmus accesses are 8 bytes. -/
def locAddr (l : Nat) : Addr := BitVec.ofNat 64 l

def mkAccess (l : Nat) (ord : AccOrd) : Access :=
  { addr := locAddr l, size := 8, ord := ord, excl := false }

/-- Association-list lookup. -/
def lookup : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (k', v) :: rest, k => if k == k' then some v else lookup rest k

/-- All ordered pairs `(i, j)` with `i` before `j` in the list (transitive po/co). -/
def prefixPairs : List Nat → Rel
  | [] => []
  | i :: rest => (rest.map fun j => (i, j)) ++ prefixPairs rest

theorem prefixPairs_nil : prefixPairs [] = [] := rfl

/-- Every list with `x` inserted at one more position. -/
def inserts (x : α) : List α → List (List α)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: ((inserts x ys).map fun zs => y :: zs)

/-- All permutations, by insertion. Terminates on the list structure. -/
def perms : List α → List (List α)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap fun ys => inserts x ys

/-- Cartesian product: one choice per list. Terminates on the outer list. -/
def choices : List (List α) → List (List α)
  | [] => [[]]
  | xs :: xss => (choices xss).flatMap fun rest => xs.map fun x => x :: rest

theorem perms_nil : perms ([] : List Nat) = [[]] := rfl

theorem choices_nil : choices ([] : List (List Nat)) = [[]] := rfl

-- Non-degenerate witnesses: the combinators do not collapse on two elements.
example : perms [1, 2] = [[1, 2], [2, 1]] := rfl

example : choices [[1, 2], [3]] = [[1, 3], [2, 3]] := rfl

#print axioms prefixPairs_nil
#print axioms perms_nil
#print axioms choices_nil

/-- Mutable-while-walking state of one core's elaboration. -/
structure Walk where
  next : Nat
  evs : List Ev
  ids : List Nat
  locOf : List (Nat × Nat)
  valOf : List (Nat × Nat)
  loadDst : List (Nat × Nat)
  stReg : List (Nat × Nat)
  evOf : List (Option Nat)
  loads : List (Nat × Nat)
  pend : List (DepKind × Nat)
  copies : List (Nat × Nat)
  addr : Rel
  data : Rel
  ctrl : Rel
  deriving DecidableEq, Repr

def walkInit (start : Nat) : Walk :=
  { next := start, evs := [], ids := [], locOf := [], valOf := [], loadDst := [],
    stReg := [], evOf := [], loads := [], pend := [], copies := [],
    addr := [], data := [], ctrl := [] }

def mkEv (id core : Nat) (kind : EvKind) (val : Nat) : Ev :=
  { id := id, core := core, kind := kind, val := val }

/-- Add one dependency edge of flavour `k`. -/
def addDep (k : DepKind) (e : Nat × Nat) (w : Walk) : Walk :=
  match k with
  | .addr => { w with addr := e :: w.addr }
  | .data => { w with data := e :: w.data }
  | .ctrl => { w with ctrl := e :: w.ctrl }

/-- Apply every pending `dep` marker to memory event `tgt`, then clear them.
    A marker whose source register has no producing load contributes no edge. -/
def applyPend (s : Walk) (tgt : Nat) : Walk :=
  s.pend.foldl (fun w p => match lookup w.loads p.2 with
    | some src => addDep p.1 (src, tgt) w
    | none => w) { s with pend := [] }

/-- One elaboration step on `core`. Barriers keep pending markers; a `dep`
    marker queues itself and records the register copy for the replay. -/
def step (core : Nat) (s : Walk) : LitInstr → Walk
  | .ld dst loc ord =>
    let nid := s.next
    let e := mkEv nid core (.read (mkAccess loc ord)) 0
    let s1 := { s with next := nid + 1, evs := s.evs ++ [e], ids := s.ids ++ [nid] }
    let s2 := { s1 with locOf := s1.locOf ++ [(nid, loc)] }
    let s3 := { s2 with loadDst := s2.loadDst ++ [(nid, dst)] }
    let s4 := { s3 with evOf := s3.evOf ++ [some nid], loads := (dst, nid) :: s3.loads }
    applyPend s4 nid
  | .st loc v ord =>
    let nid := s.next
    let e := mkEv nid core (.write (mkAccess loc ord)) v
    let s1 := { s with next := nid + 1, evs := s.evs ++ [e], ids := s.ids ++ [nid] }
    let s2 := { s1 with locOf := s1.locOf ++ [(nid, loc)] }
    let s3 := { s2 with valOf := s2.valOf ++ [(nid, v)], evOf := s2.evOf ++ [some nid] }
    applyPend s3 nid
  | .stReg loc src ord =>
    let nid := s.next
    let e := mkEv nid core (.write (mkAccess loc ord)) 0
    let s1 := { s with next := nid + 1, evs := s.evs ++ [e], ids := s.ids ++ [nid] }
    let s2 := { s1 with locOf := s1.locOf ++ [(nid, loc)] }
    let s3 := { s2 with stReg := s2.stReg ++ [(nid, src)] }
    let s4 := { s3 with evOf := s3.evOf ++ [some nid] }
    let s5 := match lookup s.loads src with
      | some w => { s4 with data := (w, nid) :: s4.data }
      | none => s4
    applyPend s5 nid
  | .fence b =>
    let nid := s.next
    let e := mkEv nid core (.barrier b) 0
    let s1 := { s with next := nid + 1, evs := s.evs ++ [e], ids := s.ids ++ [nid] }
    { s1 with evOf := s1.evOf ++ [some nid] }
  | .dep k src dst =>
    let s1 := { s with pend := s.pend ++ [(k, src)] }
    let s2 := { s1 with copies := s1.copies ++ [(src, dst)] }
    { s2 with evOf := s2.evOf ++ [none] }

end Arm.Lit

/-
CUTS: only the terminating combinators so far. Elaboration of `LitProg` to events,
`rf`/`co` enumeration, outcome checking and the verdict function are NOT yet written.
-/
