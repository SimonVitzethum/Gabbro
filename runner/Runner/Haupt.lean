module
public import Runner.Prog.Elf
public import Runner.Prog.Proben
public import Runner.Prog.Liste
public import Runner.Test.Diff
public import Runner.Test.Floating
-- `lean --run` needs the generators' IR and that of their transitive dependencies.
-- Keep the ordinary imports and definitions for the native Lake executable as well.
meta import Runner.Prog.Proben
meta import Runner.Prog.Liste
meta import Runner.Test.Diff
meta import Runner.Test.Floating
@[expose] public section


/-! # `runner DIR`: writes the runner binary, its listing and the probe images

Off the trust path: it prints the bytes the proofs are about (`Runner.Prog.image`), the listing `runner.s`, and the
probe images. No Lean program runs the IR: the probes' outputs are fixed files (`runner/proben/NAME.aus`,
`NAME.code`) that only the runner on the processor is compared with. `runner difftest DIR N` writes the
differential tests of the x86-64 model (`Runner/Test/`). `runner floating DIR`
writes the whole-IR floating boundary images and their `floating.tsv` manifest. -/

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

def floatingTests (dir : String) : IO UInt32 := do
  let mut manifest := Runner.Test.Floating.manifestHeader
  let mut count := 0
  for test in Runner.Test.Floating.fixtures do
    IO.FS.writeBinFile (dir ++ "/" ++ test.fileName count) (toBytes test.image)
    manifest := manifest ++ test.manifestRow count
    count := count + 1
  IO.FS.writeFile (dir ++ "/floating.tsv") manifest
  IO.println s!"floating: {count} IR images, opcodes 28..59, manifest floating.tsv"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["difftest", dir, n] => return (← difftest dir n.toNat!)
  | ["floating", dir] => return (← floatingTests dir)
  | _ => pure ()
  let dir := args.headD "."
  IO.FS.writeBinFile (dir ++ "/runner") (toBytes image)
  IO.FS.writeFile (dir ++ "/runner.s") listing
  for (name, img) in [("hello", hello), ("probe", probe), ("threads", threads), ("threads64", threadsN 64 10000), ("io", io), ("lit-sb", litSB), ("lit-sbcas", litSBcas), ("lit-mp", litMP), ("lit-lb", litLB)] do
    IO.FS.writeBinFile (dir ++ s!"/{name}.img") (toBytes img)
  IO.println s!"runner: {image.length} bytes, code {codeLen}, table at {tblOff}, {prog.length} instructions"
  return 0
