import Runner.IR.Step
import Runner.Prog.Elf
import Runner.Prog.Proben
import Runner.Test.Diff

/-! # `runner DIR`: writes the runner binary and the probe images with their expected results

Off the trust path: it prints the bytes the proofs are about (`Runner.Prog.image`) and, for each probe, what the
IR semantics (`Runner.IR.step`) answers under a kernel that implements `write` and `exit_group` only. The guardian
compares that with the runner on the processor. -/

open Runner Runner.Prog

def toBytes (l : List B) : ByteArray := ⟨(l.map fun b => b.toNat.toUInt8).toArray⟩

/-- A flat memory for the image only (readable and writable), as bytes: the toy machine's store. -/
structure Flat where
  base : Nat
  d : ByteArray

def Flat.ok (f : Flat) (a : W) (n : Nat) : Bool := f.base ≤ a.toNat && a.toNat + n ≤ f.base + f.d.size

def Flat.get (f : Flat) (a : W) (n : Nat) : Nat :=
  (List.range n).foldr (fun j acc => acc * 256 + (f.d.get! (a.toNat - f.base + j)).toNat) 0

def Flat.put (f : Flat) (a : W) (v : W) : Flat :=
  { f with d := (List.range 8).foldl (fun d j => d.set! (a.toNat - f.base + j) (v.toNat / 256 ^ j % 256).toUInt8) f.d }

def flatAns (f : Flat) : Op → Option (Ans × Flat)
  | .rd n a => some (if f.ok a n then some (BitVec.ofNat 64 (f.get a n), 0) else none, f)
  | .wr a v => some (if f.ok a 8 then (some (0, 0), f.put a v) else (none, f))
  | .cas a e n => some (if f.ok a 8 then
      let o := BitVec.ofNat 64 (f.get a 8)
      (some (o, 0), if o = e then f.put a n else f) else (none, f))
  | .sys _ => none

/-- The IR machine with a toy kernel (`write`, `exit`, `exit_group`, `clone`; every other call answers
    `-ENOSYS`), the threads taking turns one request each. Answers the output and the end: `some code` for
    `exit_group`, `some 256` for a fault, `none` out of fuel. -/
partial def irRun (fuel : Nat) (m : Flat) (ths : Array (Option (Res IR.T))) (out : Array B) :
    Array B × Option Nat := Id.run do
  let mut m := m
  let mut ths := ths
  let mut out := out
  let mut f := fuel
  while f > 0 do
    f := f - 1
    if ths.all (·.isNone) then return (out, some 0)
    for i in [0:ths.size] do
      match ths[i]! with
      | none => pure ()
      | some r =>
        let r := match r with | .next t => IR.step t | r => r
        match r with
        | .next t => ths := ths.set! i (some (IR.step t))
        | .fault | .unk => return (out, some 256)
        | .ask (.sys q) k =>
          if q.nr.toNat = NR_EXIT_GROUP then return (out, some (q.a1.toNat % 256))
          else if q.nr.toNat = NR_EXIT then ths := ths.set! i none
          else if q = cloneReq then
            ths := ths.set! i (some (k (some (BitVec.ofNat 64 (1000 + ths.size), 0))))
            ths := ths.push (some (k (some (0, 0))))
          else
            let ret := if q.nr.toNat = 1 then q.a3 else BitVec.ofInt 64 (-38)
            if q.nr.toNat = 1 then
              out := out ++ ((List.range q.a3.toNat).map fun j => BitVec.ofNat 8 (m.get (q.a2 + BitVec.ofNat 64 j) 1)).toArray
            ths := ths.set! i (some (k (some (ret, 0))))
        | .ask o k =>
          match flatAns m o with
          | some (a, m') => m := m'; ths := ths.set! i (some (k a))
          | none => return (out, some 256)
  return (out, none)

def expected (img : List B) : Array B × Option Nat :=
  let m : Flat := ⟨IMG, ⟨(img.map fun b => b.toNat.toUInt8).toArray⟩⟩
  let fp := BitVec.ofNat 64 (m.get (BitVec.ofNat 64 IMG) 8)
  irRun 100000000 m #[some (IR.step { pc := BitVec.ofNat 64 (IMG + 16), fp := fp })] #[]

def difftest (dir : String) (n : Nat) : IO UInt32 := do
  let (prog, expect, masks) := Runner.Test.gen n
  IO.FS.writeBinFile (dir ++ "/xtest") (toBytes prog)
  IO.FS.writeBinFile (dir ++ "/xtest.expect") (toBytes expect)
  IO.FS.writeFile (dir ++ "/xtest.mask") (String.intercalate "\n" (masks.map fun (m, k) => s!"{m} {k}") ++ "\n")
  let mut fl := ""
  for f in Runner.Test.faults do
    IO.FS.writeBinFile (dir ++ s!"/fault-{f.name}") (toBytes f.prog)
    fl := fl ++ s!"{f.name} {f.signal} {f.model}\n"
  IO.FS.writeFile (dir ++ "/faults.txt") fl
  IO.println s!"difftest: {masks.length} cases, {Runner.Test.faults.length} fault programs"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["difftest", dir, n] => return (← difftest dir n.toNat!)
  | _ => pure ()
  let dir := args.headD "."
  IO.FS.writeBinFile (dir ++ "/runner") (toBytes image)
  for (name, img) in [("hello", hello), ("probe", probe), ("threads", threads)] do
    IO.FS.writeBinFile (dir ++ s!"/{name}.img") (toBytes img)
    let (out, code) := expected img
    IO.FS.writeBinFile (dir ++ s!"/{name}.out") (toBytes out.toList)
    IO.FS.writeFile (dir ++ s!"/{name}.code") s!"{code.getD 999}\n"
  IO.println s!"runner: {image.length} bytes, code {codeLen}, table at {tblOff}, {prog.length} instructions"
  return 0
