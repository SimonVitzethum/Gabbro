/- Compile checked Gabbro source to an S0IR image. Execution belongs to the assembly runner. -/
module
public import Stage0.IRBild
public import Stage0.Diagnose
-- Load transitive compiler IR for `lean --run`; retain the runtime import and native main.
meta import Stage0.IRBild
@[expose] public section


namespace Gabbro.Stage0

/-- The text of a program given as several source files: the files in order, one after the other.
    A unit is a list of items, so the items of the files form one unit. -/
def quelltext (files : List String) : IO String := do
  let mut text := ""
  for file in files do
    text := text ++ (← IO.FS.readFile file) ++ "\n"
  return text

def haupt (args : List String) : IO UInt32 := do
  match args with
  | "--ir" :: rest =>
    let paths := rest.takeWhile fun arg => !arg.startsWith "--"
    let tail := rest.drop paths.length
    match paths.getLast?, paths.dropLast with
    | some output, source :: more =>
      match Profil.parseOptions tail {} with
      | .error error => IO.eprintln ("stage0: " ++ error); return 2
      | .ok options =>
        let text ← quelltext (source :: more)
        match irBild text irStapel options with
        | .error error =>
          IO.eprintln ("stage0: " ++ error)
          for note in Diagnose.notes text options do
            IO.eprintln ("stage0: note: " ++ note)
          return 1
        | .ok bytes =>
          IO.FS.writeBinFile output ⟨(bytes.map fun b => b.toNat.toUInt8).toArray⟩
          return 0
    | _, _ =>
      IO.eprintln "usage: stage0 --ir SOURCE.gab [SOURCE.gab ...] IMAGE [--arch x86_64] [--target NAME] [--testbuild]"
      return 2
  | _ =>
    IO.eprintln "usage: stage0 --ir SOURCE.gab [SOURCE.gab ...] IMAGE [--arch x86_64] [--target NAME] [--testbuild]"
    return 2

end Gabbro.Stage0

def main (args : List String) : IO UInt32 := Gabbro.Stage0.haupt args
