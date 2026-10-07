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

/-- Set register `k` to `v` in a register file. -/
def upd (m : List (Nat × Nat)) (k v : Nat) : List (Nat × Nat) :=
  (k, v) :: (m.filter fun q => match q with | (a, _) => a != k)

theorem upd_lookup (m : List (Nat × Nat)) (k v : Nat) :
    lookup (upd m k v) k = some v := by simp [upd, lookup]

-- Witness: `upd_lookup` is non-degenerate (overwrite and unrelated keys).
example : lookup (upd [(1, 2)] 0 9) 0 = some 9 := rfl

example : lookup (upd [(1, 2)] 1 9) 0 = none := rfl

/-- The `n`-th element of a list. -/
def nth : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth xs n

/-- Replay one core: loads read candidate values, `stReg` and `dep` flow on.
    Returns the final register file plus the `stReg` write values. -/
def replayCore : List LitInstr → List (Option Nat) → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat) → (List (Nat × Nat) × List (Nat × Nat))
  | [], _, regs, wr, _, _ => (regs, wr)
  | _, [], regs, wr, _, _ => (regs, wr)
  | i :: is, e :: es, regs, wr, rv, copies =>
    match i with
    | .ld dst _ _ => match e with
      | some eid => replayCore is es (upd regs dst ((lookup rv eid).getD 0)) wr rv copies
      | none => replayCore is es regs wr rv copies
    | .stReg _ src _ =>
      let v := (lookup regs src).getD 0
      match e with
      | some eid => replayCore is es regs (wr ++ [(eid, v)]) rv copies
      | none => replayCore is es regs wr rv copies
    | .dep _ _ _ => match copies with
      | (src, dst) :: rest => replayCore is es (upd regs dst ((lookup regs src).getD 0)) wr rv rest
      | [] => replayCore is es regs wr rv []
    | _ => replayCore is es regs wr rv copies

def fstOf : List (Nat × Nat) × List (Nat × Nat) → List (Nat × Nat)
  | (x, _) => x

def sndOf : List (Nat × Nat) × List (Nat × Nat) → List (Nat × Nat)
  | (_, y) => y

/-- Per-core elaboration data zipped together for the replay. -/
def coreTriples (p : LitProg) (e : Elab) :
    List ((List LitInstr × List (Option Nat)) × List (Nat × Nat)) :=
  (p.cores.zip e.evOf).zip e.copies

def corePair (t : (List LitInstr × List (Option Nat)) × List (Nat × Nat))
    (rv : List (Nat × Nat)) : List (Nat × Nat) × List (Nat × Nat) :=
  match t with
  | ((is, ev), cp) => replayCore is ev [] [] rv cp

/-- Candidate writes for read `r`: every write at the read's location. -/
def rfCands (e : Elab) (r : Nat) : List Nat :=
  match lookup e.locOf r with
  | some l => writesAtLoc e l
  | none => []

/-- All `rf` assignments as `(write, read)` pairs, one write per read. -/
def rfCombos (e : Elab) : List (List (Nat × Nat)) :=
  (choices (e.reads.map fun r => rfCands e r)).map fun ws => ws.zip e.reads

/-- An initial write of the elaboration (core `nCores` marks init events). -/
def isInitWrite (e : Elab) (wid : Nat) : Bool :=
  lookup e.coreOf wid == some e.nCores

/-- Total `co` orders at one location: the initial write first, then any order. -/
def coOrdersLoc (e : Elab) (l : Nat) : List (List Nat) :=
  let ws := writesAtLoc e l
  match ws.filter (isInitWrite e) with
  | [iw] => (perms (ws.filter fun w => !(isInitWrite e w))).map fun p => iw :: p
  | _ => perms ws

/-- All `co` relations: one total order per location, concatenated. -/
def coCombos (e : Elab) (locs : List Nat) : List Rel :=
  (choices (locs.map fun l => coOrdersLoc e l)).map fun orders => orders.flatMap prefixPairs

/-- Apply read values and `stReg` write values of one candidate to the events. -/
def applyVals (evs : List Ev) (vals : List (Nat × Nat)) : List Ev :=
  evs.map fun v => match lookup vals v.id with
    | some x => { v with val := x }
    | none => v

/-- `stReg` write values of one candidate (register replay over `rv`). -/
def replayStores (p : LitProg) (e : Elab) (rv : List (Nat × Nat)) : List (Nat × Nat) :=
  (coreTriples p e).flatMap fun t => sndOf (corePair t rv)

/-- One resolution round: the register replay over the current read values
    gives `stReg` write values; reads then take their own write's value. -/
def resolveRound (p : LitProg) (e : Elab) (rf : List (Nat × Nat))
    (cur : List (Nat × Nat)) : List (Nat × Nat) :=
  let sv := replayStores p e cur
  let all := e.valOf ++ sv
  rf.map fun q => match q with | (w, r) => (r, (lookup all w).getD 0)

/-- Iterate resolution rounds (fuel-bounded, hence terminating; one round per
    event suffices for loop-free litmus cores; the last round wins on a
    value cycle, which no litmus test in the suite has). -/
def resolveVals : Nat → LitProg → Elab → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, _, _, cur => cur
  | n + 1, p, e, rf, cur => resolveVals n p e rf (resolveRound p e rf cur)

/-- Read values of one candidate, with `stReg`-sourced reads resolved. -/
def readValsOf (p : LitProg) (e : Elab) (rf : List (Nat × Nat)) : List (Nat × Nat) :=
  resolveVals (e.evs.length + 1) p e rf []

/-- Build one candidate `Exec`: values filled in, `rmw` empty (no exclusives). -/
def mkExec (p : LitProg) (e : Elab) (rf : List (Nat × Nat)) (co : Rel) : Exec :=
  let rv := readValsOf p e rf
  let vals := rv ++ replayStores p e rv
  { evs := applyVals e.evs vals, po := e.po, addr := e.addr, data := e.data, ctrl := e.ctrl, rf := rf, co := co, rmw := [] }

/-- All candidate executions: every `rf` times every total `co` per location. -/
def candidates (p : LitProg) : List Exec :=
  let e := elabProg p
  (rfCombos e).flatMap fun rf => (coCombos e (allLocs p)).map fun co => mkExec p e rf co

/-- Final register files of one candidate execution. -/
def execRegs (p : LitProg) (e : Elab) (x : Exec) : List (List (Nat × Nat)) :=
  let rv := x.evs.map fun v => (v.id, v.val)
  (coreTriples p e).map fun t => fstOf (corePair t rv)

/-- Value of event `i` in `evs`. -/
def evVal (evs : List Ev) (i : Nat) : Option Nat :=
  (evs.find? fun v => v.id == i).map fun v => v.val

/-- The `co`-last write at each location determines final memory. -/
def coLast (co : Rel) (ws : List Nat) : Option Nat :=
  ws.find? fun w => !(ws.any fun v => co.contains (w, v))

def memVals (e : Elab) (co : Rel) (evs : List Ev) (locs : List Nat) : List (Nat × Nat) :=
  locs.map fun l => match coLast co (writesAtLoc e l) with
    | some w => (l, (evVal evs w).getD 0)
    | none => (l, 0)

/-- A final outcome: register and memory values. -/
structure Outcome where
  regs : List (Nat × Nat × Nat)
  mem : List (Nat × Nat)
  deriving DecidableEq, Repr

def atomHoldReg (got : List (List (Nat × Nat))) : Nat × Nat × Nat → Bool
  | (c, r, v) => match nth got c with
    | some rf => lookup rf r == some v
    | none => false

def atomHoldMem (got : List (Nat × Nat)) : Nat × Nat → Bool
  | (l, v) => lookup got l == some v

/-- The outcome holds on the candidate execution. -/
def outcomeHolds (p : LitProg) (e : Elab) (x : Exec) (o : Outcome) : Bool :=
  ((o.regs.all fun t => atomHoldReg (execRegs p e x) t) && (o.mem.all fun q => atomHoldMem (memVals e x.co x.evs (allLocs p)) q))

/-- The litmus verdict: `allowed` iff some `cons`-consistent candidate reaches it. -/
inductive Verdict where
  | allowed | forbidden
  deriving DecidableEq, Repr

def checkOutcome (cons : Exec → Bool) (p : LitProg) (o : Outcome) : Verdict :=
  let e := elabProg p
  if (candidates p).any fun x => cons x && outcomeHolds p e x o then .allowed else .forbidden

-- The empty program has exactly one (empty) candidate.
example : (candidates { cores := [], init := [], final := [] }).length = 1 := rfl

-- A single store: no reads, one candidate, writes are init then the store.
def singleStore : LitProg :=
  { cores := [[.st 0 1 .plain]], init := [], final := [] }

example : (elabProg singleStore).reads = [] := rfl

example : (elabProg singleStore).writes = [0, 1] := rfl

example : (candidates singleStore).length = 1 := rfl

#print axioms upd_lookup

end Arm.Lit

/-
CUTS: only the terminating combinators so far. Elaboration of `LitProg` to events,
`rf`/`co` enumeration, outcome checking and the verdict function are NOT yet written.
-/
