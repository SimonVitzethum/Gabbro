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

/-- Locations read or written by one instruction. -/
def instrLocs : LitInstr → List Nat
  | .ld _ loc _ => [loc]
  | .st loc _ _ => [loc]
  | .stReg loc _ _ => [loc]
  | _ => []

/-- Every location of the program (code plus initial memory), deduplicated. -/
def allLocs (p : LitProg) : List Nat :=
  ((p.cores.flatMap fun is => is.flatMap instrLocs) ++ (p.init.map fun q => q.1)).eraseDups

/-- Initial value of `l` (0 when the program does not initialise it). -/
def initVal (p : LitProg) (l : Nat) : Nat := (lookup p.init l).getD 0

/-- One row per location: the initial write event, its location and its value. -/
def initRows (id n : Nat) : List Nat → LitProg → List (Ev × Nat × Nat)
  | [], _ => []
  | l :: ls, p => ({ id := id, core := n, kind := .write (mkAccess l .plain), val := initVal p l }, l, initVal p l) :: initRows (id + 1) n ls p

/-- Whole-program elaboration: all events plus the maps candidates need. -/
structure Elab where
  next : Nat
  evs : List Ev
  po : Rel
  addr : Rel
  data : Rel
  ctrl : Rel
  locOf : List (Nat × Nat)
  valOf : List (Nat × Nat)
  loadDst : List (Nat × Nat)
  stReg : List (Nat × Nat)
  copies : List (List (Nat × Nat))
  evOf : List (List (Option Nat))
  coreOf : List (Nat × Nat)
  reads : List Nat
  writes : List Nat
  nCores : Nat
  deriving DecidableEq, Repr

def elabEmpty : Elab :=
  { next := 0, evs := [], po := [], addr := [], data := [], ctrl := [], locOf := [], valOf := [], loadDst := [], stReg := [], copies := [], evOf := [], coreOf := [], reads := [], writes := [], nCores := 0 }

def isReadEv : Ev → Bool
  | { kind := .read _, .. } => true
  | _ => false

def isWriteEv : Ev → Bool
  | { kind := .write _, .. } => true
  | _ => false

/-- Read event ids elaborated by one core walk, in program order. -/
def readIds (w : Walk) : List Nat := ((w.evs.filter isReadEv).map fun v => v.id)

/-- Initialise the elaboration with one write event per location. -/
def rowEv : Ev × Nat × Nat → Ev
  | (e, _, _) => e

def rowLoc : Ev × Nat × Nat → Nat × Nat
  | (e, l, _) => (e.id, l)

def rowVal : Ev × Nat × Nat → Nat × Nat
  | (e, _, v) => (e.id, v)

def rowCore (n : Nat) : Ev × Nat × Nat → Nat × Nat
  | (e, _, _) => (e.id, n)

def elabInit (rows : List (Ev × Nat × Nat)) (n : Nat) : Elab :=
  let f0 := { elabEmpty with evs := rows.map rowEv }
  let f1 := { f0 with next := rows.length }
  let f2 := { f1 with locOf := rows.map rowLoc }
  let f3 := { f2 with valOf := rows.map rowVal }
  let f4 := { f3 with coreOf := rows.map (rowCore n) }
  let f5 := { f4 with writes := rows.map fun r => (rowEv r).id }
  { f5 with nCores := n }

/-- Elaborate one core's instructions and merge them into the whole program. -/
def addCore (e : Elab) (core : Nat) (is : List LitInstr) : Elab :=
  let w := is.foldl (step core) (walkInit e.next)
  let a0 := { e with next := w.next }
  let a1 := { a0 with evs := a0.evs ++ w.evs }
  let a2 := { a1 with po := a1.po ++ prefixPairs w.ids }
  let a3 := { a2 with addr := a2.addr ++ w.addr }
  let a4 := { a3 with data := a3.data ++ w.data }
  let a5 := { a4 with ctrl := a4.ctrl ++ w.ctrl }
  let a6 := { a5 with locOf := a5.locOf ++ w.locOf }
  let a7 := { a6 with valOf := a6.valOf ++ w.valOf }
  let a8 := { a7 with loadDst := a7.loadDst ++ w.loadDst }
  let a9 := { a8 with stReg := a8.stReg ++ w.stReg }
  let b0 := { a9 with copies := a9.copies ++ [w.copies] }
  let b1 := { b0 with evOf := b0.evOf ++ [w.evOf] }
  let b2 := { b1 with coreOf := b1.coreOf ++ (w.ids.map fun i => (i, core)) }
  let b3 := { b2 with reads := b2.reads ++ readIds w }
  { b3 with writes := b3.writes ++ ((w.evs.filter isWriteEv).map fun v => v.id) }

def elabGo : Nat → Elab → List (List LitInstr) → Elab
  | _, e, [] => e
  | c, e, is :: rest => elabGo (c + 1) (addCore e c is) rest

/-- Elaborate a whole litmus program: init writes first, then every core. -/
def elabProg (p : LitProg) : Elab :=
  elabGo 0 (elabInit (initRows 0 p.cores.length (allLocs p) p) p.cores.length) p.cores

/-- All write event ids at location `l`. -/
def writesAtLoc (e : Elab) (l : Nat) : List Nat :=
  e.writes.filter fun wid => lookup e.locOf wid == some l

end Arm.Lit

/-
CUTS: only the terminating combinators so far. Elaboration of `LitProg` to events,
`rf`/`co` enumeration, outcome checking and the verdict function are NOT yet written.
-/
