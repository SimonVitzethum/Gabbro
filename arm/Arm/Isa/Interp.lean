/-
  File:      Arm/Isa/Interp.lean
  Subject:   Concrete test interpreter for the `Eff` effect tree: a `Machine`
             record (GPRs, SP, PC, NZCV, SIMD regs, sysregs, byte memory) and
             `run`. Association lists keep every test vector decidable.
  Sail:      sail-arm/arm-v9.4-a/src/interface.sail (register/memory accessors),
             sail-arm/arm-v9.4-a/src/mem.sail:85 (`_Mem_read` byte transport).
-/
import Arm.Isa.Monad
import Arm.Isa.IntCore
import Arm.Isa.Integer
import Arm.Isa.IntBit
import Arm.Isa.IntMul
import Arm.Isa.IntCond

namespace Arm

/-- Concrete test machine. `x` holds X0-X30 (index 31 reads as zero, writes
    are discarded: XZR); `mem` maps byte addresses to bytes, absent reads 0. -/
-- Sail: interface.sail (register file), mem.sail:85 (byte-addressed memory).
structure Machine where
  x : List (BitVec 64)
  sp : BitVec 64
  pc : BitVec 64
  nzcv : BitVec 4
  v : List (BitVec 128)
  sys : List (String × BitVec 64)
  mem : List (Nat × Nat)

/-- Replace element `n` (no-op past the end). -/
def setNth {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | y :: xs, k + 1, v => y :: setNth xs k v

/-- Read X `n` (31 is XZR); short register files read as zero. -/
-- Sail: interface.sail (`X_read`: 31 is the zero register).
def getX (m : Machine) (n : Nat) : BitVec 64 :=
  if n == 31 then BitVec.ofNat 64 0
  else match m.x[n]? with | some b => b | none => BitVec.ofNat 64 0

/-- Write X `d` (31 is XZR: discarded). -/
-- Sail: interface.sail (`X_set`: 31 writes nowhere).
def setX (m : Machine) (n : Nat) (v : BitVec 64) : Machine :=
  if n == 31 then m else { m with x := setNth m.x n v }

/-- Read V `n`; short files read as zero. -/
-- Sail: interface.sail (`V_read`).
def getV (m : Machine) (n : Nat) : BitVec 128 :=
  match m.v[n]? with | some b => b | none => BitVec.ofNat 128 0

/-- Write V `n`. -/
-- Sail: interface.sail (`V_set`).
def setV (m : Machine) (n : Nat) (v : BitVec 128) : Machine :=
  { m with v := setNth m.v n v }

/-- Read a named system register; `"SP"` is the stack pointer, others default
    to zero. -/
-- Sail: interface.sail (system accessors; `SP_read` for the stack pointer).
def getSys (m : Machine) (s : String) : BitVec 64 :=
  if s == "SP" then m.sp
  else match m.sys.find? (fun p => p.1 == s) with
    | some (_, v) => v
    | none => BitVec.ofNat 64 0

/-- Write a named system register; `"SP"` is the stack pointer. -/
-- Sail: interface.sail (`SP_set` for the stack pointer).
def setSys (m : Machine) (s : String) (v : BitVec 64) : Machine :=
  if s == "SP" then { m with sp := v }
  else { m with sys := (s, v) :: m.sys.filter (fun p => p.1 != s) }

/-- Read one byte (absent addresses read as zero). -/
-- Sail: mem.sail:85 (`_Mem_read` byte transport).
def ldByte (m : Machine) (a : Nat) : Nat :=
  match m.mem.find? (fun p => p.1 == a % Int.pow2 64) with
  | some (_, b) => b % 256
  | none => 0

/-- Write one byte (addresses wrap at 2^64). -/
-- Sail: mem.sail (`_Mem_set` byte transport).
def stByte (m : Machine) (a v : Nat) : Machine :=
  { m with mem := (a % Int.pow2 64, v % 256) ::
    m.mem.filter (fun p => p.1 != a % Int.pow2 64) }

/-- Little-endian load of `acc.size` bytes (1, 2, 4, 8, 16). -/
-- Sail: mem.sail:85; byte composition is little-endian (SCTLR.EE = 0).
def loadLE (m : Machine) (acc : Access) : Nat := go acc.size
where go : Nat → Nat
  | 0 => 0
  | (k+1) => ldByte m ((acc.addr.toNat + k) % Int.pow2 64) * 256 ^ k + go k

/-- Little-endian store of `acc.size` bytes (1, 2, 4, 8, 16). -/
-- Sail: mem.sail (`_Mem_set`); byte composition is little-endian.
def storeLE (m : Machine) (acc : Access) (v : Nat) : Machine := go acc.size m
where go : Nat → Machine → Machine
  | 0, s => s
  | (k+1), s =>
    go k (stByte s ((acc.addr.toNat + k) % Int.pow2 64) ((v / 256 ^ k) % 256))

/-- Run an `Eff` tree with `fuel` steps. Barriers are ignored (sequential
    model); `raise` returns the exception. Running out of fuel is a harness
    error (code 999), NOT Sail behaviour: vectors below use ample fuel. -/
-- Sail: interface.sail (the accessors `run` answers), mem.sail:85 (memory).
def runF : Nat → Eff α → Machine → Except Exc (α × Machine)
  | 0, _, _ => .error (.other 999)
  | _ + 1, .ret a, m => .ok (a, m)
  | f + 1, .rdX n k, m => runF f (k (getX m n)) m
  | f + 1, .wrX n v k, m => runF f k (setX m n v)
  | f + 1, .rdV n k, m => runF f (k (getV m n)) m
  | f + 1, .wrV n v k, m => runF f k (setV m n v)
  | f + 1, .rdPC k, m => runF f (k m.pc) m
  | f + 1, .wrPC v k, m => runF f k { m with pc := v }
  | f + 1, .rdNZCV k, m => runF f (k m.nzcv) m
  | f + 1, .wrNZCV v k, m => runF f k { m with nzcv := v }
  | f + 1, .rdSys s k, m => runF f (k (getSys m s)) m
  | f + 1, .wrSys s v k, m => runF f k (setSys m s v)
  | f + 1, .rdMem a k, m => runF f (k (loadLE m a)) m
  | f + 1, .wrMem a v k, m => runF f k (storeLE m a v)
  | f + 1, .bar _ k, m => runF f k m
  | _ + 1, .raise e, _ => .error e

/-- Run with fixed ample fuel (every ported instruction needs at most 8 steps). -/
def run (e : Eff α) (m : Machine) : Except Exc (α × Machine) := runF 128 e m

/-- One decoded integer instruction, as a vector runs it. Constructor fields
    mirror the `exec*` signatures of the family files. -/
inductive Op where
  | addSubImm (d n w imm : Nat) (sub setflags : Bool)
  | addSubShift (d n m w : Nat) (st : Int.ShiftTy) (amt : Nat) (sub setflags : Bool)
  | addSubExt (d n m w : Nat) (e : Int.ExtTy) (sh : Nat) (sub setflags : Bool)
  | adcSbc (d n m w : Nat) (sub setflags : Bool)
  | logImm (d n w mask : Nat) (inv : Bool) (op : Int.LogicOp) (sf : Bool)
  | logShift (d n m w : Nat) (inv : Bool) (op : Int.LogicOp) (sf : Bool)
      (st : Int.ShiftTy) (amt : Nat)
  | shiftVar (d n m w : Nat) (st : Int.ShiftTy)
  | movWide (d w imm : Nat) (mk : Int.MovKind) (pos : Nat)
  | adr (d imm : Nat) (page : Bool)
  | bitfield (d n w r s wm tm : Nat) (ext inz : Bool)
  | extr (d n m w lsb : Nat)
  | clzCls (d n w : Nat) (isCls : Bool)
  | rbit (d n w : Nat)
  | rev (d n w cont : Nat)
  | cntPop (d n w : Nat)
  | ctz (d n w : Nat)
  | abs (d n w : Nat)
  | mulAddSub (a d m n w : Nat) (sub : Bool)
  | wideMul (a d m n : Nat) (sub u : Bool)
  | div (d m n w : Nat) (u : Bool)
  | mulHi (d m n w : Nat) (u : Bool)
  | condSel (d m n w cond : Nat) (ei ev : Bool)
  | condCmpR (n m w cond dflt : Nat) (sub : Bool)
  | condCmpI (n w imm cond dflt : Nat) (sub : Bool)

/-- Dispatch a decoded op to its execute semantics. -/
def execOp : Op → Eff Unit
  | .addSubImm d n w imm sub sf => Int.execAddSubImm d n w imm sub sf
  | .addSubShift d n m w st amt sub sf => Int.execAddSubShift d n m w st amt sub sf
  | .addSubExt d n m w e sh sub sf => Int.execAddSubExt d n m w e sh sub sf
  | .adcSbc d n m w sub sf => Int.execAdcSbc d n m w sub sf
  | .logImm d n w mask inv op sf => Int.execLogicalImm d n w mask inv op sf
  | .logShift d n m w inv op sf st amt => Int.execLogicalShift d n m w inv op sf st amt
  | .shiftVar d n m w st => Int.execShiftVar d n m w st
  | .movWide d w imm mk pos => Int.execMovWide d w imm mk pos
  | .adr d imm page => Int.execAdr d imm page
  | .bitfield d n w r s wm tm ext inz => Int.execBitfield d n w r s wm tm ext inz
  | .extr d n m w lsb => Int.execExtract d n m w lsb
  | .clzCls d n w isCls => Int.execClzCls d n w isCls
  | .rbit d n w => Int.execRbit d n w
  | .rev d n w cont => Int.execRev d n w cont
  | .cntPop d n w => Int.execCntPop d n w
  | .ctz d n w => Int.execCtz d n w
  | .abs d n w => Int.execAbs d n w
  | .mulAddSub a d m n w sub => Int.execMulAddSub a d m n w sub
  | .wideMul a d m n sub u => Int.execWideMul a d m n sub u
  | .div d m n w u => Int.execDiv d m n w u
  | .mulHi d m n w u => Int.execMulHi d m n w u
  | .condSel d m n w cond ei ev => Int.execCondSelect d m n w cond ei ev
  | .condCmpR n m w cond dflt sub => Int.execCondCmpReg n m w cond dflt sub
  | .condCmpI n w imm cond dflt sub => Int.execCondCmpImm n w imm cond dflt sub

end Arm

/-
CUTS: skeleton only. V registers, sysregs, memory and `run` are open.
-/
