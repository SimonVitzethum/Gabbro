/- Compile checked Gabbro source to an S0IR image. Execution belongs to the assembly runner. -/
import Stage0.IRBild

namespace Gabbro.Stage0

def haupt (args : List String) : IO UInt32 := do
  match args with
  | "--ir" :: source :: output :: tail =>
    match Profil.parseOptions tail {} with
    | .error error => IO.eprintln ("stage0: " ++ error); return 2
    | .ok options =>
      match irBild (← IO.FS.readFile source) irStapel options with
      | .error error => IO.eprintln ("stage0: " ++ error); return 1
      | .ok bytes =>
        IO.FS.writeBinFile output ⟨(bytes.map fun b => b.toNat.toUInt8).toArray⟩
        return 0
  | _ =>
    IO.eprintln "usage: stage0 --ir PROGRAM.gab IMAGE [--arch x86_64] [--target NAME]"
    return 2

end Gabbro.Stage0

def main (args : List String) : IO UInt32 := Gabbro.Stage0.haupt args
