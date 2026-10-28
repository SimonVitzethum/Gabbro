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

/-- The memory right after the loader: the image at `IMG`, readable and writable, nothing else. -/
def imgMem (img : Array B) : Mem :=
  { b := fun a => if IMG ≤ a.toNat ∧ a.toNat < IMG + img.size then img[a.toNat - IMG]! else 0
    rd := fun a => IMG ≤ a.toNat ∧ a.toNat < IMG + img.size
    wr := fun a => IMG ≤ a.toNat ∧ a.toNat < IMG + img.size }

def bytesAt (m : Mem) (a : W) (n : Nat) : List B :=
  (List.range n).map fun i => m.b (a + BitVec.ofNat 64 i)

/-- Runs the IR: the output and the end (`some code` for `exit_group`, `some 256` for a fault, `none` out of fuel). -/
def irRun : Nat → IR.S → Array B → Array B × Option Nat
  | 0, _, out => (out, none)
  | f + 1, s, out =>
    match IR.step s with
    | .next s' => irRun f s' out
    | .fault | .unk => (out, some 256)
    | .sys q k =>
      if q.nr = 231 then (out, some (q.a1.toNat % 256))
      else
        let (r, out') :=
          if q.nr = 1 then (q.a3, out ++ (bytesAt s.mem q.a2 q.a3.toNat).toArray)
          else (BitVec.ofInt 64 (-38), out)
        match k ⟨r, s.mem, 0⟩ with
        | some s' => irRun f s' out'
        | none => (out', some 256)

def expected (img : List B) : Array B × Option Nat :=
  let m := imgMem img.toArray
  let fp := (m.rd64 (BitVec.ofNat 64 IMG)).getD 0
  irRun 1000000 { pc := BitVec.ofNat 64 (IMG + 16), fp := fp, mem := m } #[]

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
  for (name, img) in [("hello", hello), ("probe", probe)] do
    IO.FS.writeBinFile (dir ++ s!"/{name}.img") (toBytes img)
    let (out, code) := expected img
    IO.FS.writeBinFile (dir ++ s!"/{name}.out") (toBytes out.toList)
    IO.FS.writeFile (dir ++ s!"/{name}.code") s!"{code.getD 999}\n"
  IO.println s!"runner: {image.length} bytes, code {codeLen}, table at {tblOff}, {prog.length} instructions"
  return 0
