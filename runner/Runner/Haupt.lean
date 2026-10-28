import Runner.Prog.Elf
import Runner.Prog.Proben
import Runner.Prog.Liste
import Runner.Test.Diff

/-! # `runner DIR`: writes the runner binary, its listing and the probe images

Off the trust path: it prints the bytes the proofs are about (`Runner.Prog.image`), the listing `runner.s`, and the
probe images. No Lean program runs the IR: the probes' outputs are fixed files (`runner/proben/NAME.aus`,
`NAME.code`) that only the runner on the processor is compared with. `runner difftest DIR N` writes the
differential tests of the x86-64 model (`Runner/Test/`). -/

open Runner Runner.Prog

def toBytes (l : List B) : ByteArray := ⟨(l.map fun b => b.toNat.toUInt8).toArray⟩

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
  IO.FS.writeFile (dir ++ "/runner.s") listing
  for (name, img) in [("hello", hello), ("probe", probe), ("threads", threads)] do
    IO.FS.writeBinFile (dir ++ s!"/{name}.img") (toBytes img)
  IO.println s!"runner: {image.length} bytes, code {codeLen}, table at {tblOff}, {prog.length} instructions"
  return 0
