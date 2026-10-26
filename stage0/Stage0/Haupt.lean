/-
  File:      stage0/Stage0/Haupt.lean
  Subject:   The executable `stage0` (`stage0/lakefile.toml`).

    stage0 [--schritte N] [--passes N] PROGRAM.gab < INPUT > OUTPUT

  checks PROGRAM with the goal theorem's checker Bool and runs its `main` on the thread machine (`boot`, `Lauf/Boot.lean`): the input
  bytes go to `io.ein`/`ein_len`, the output is `io.aus` up to `aus_len`. A refusal or a stop goes to stderr with
  exit code 1.
-/
import Stage0.Lauf.Boot

namespace Gabbro.Stage0

/-- Read the options in front of the program path. -/
def optionen : Budget → List String → Except String (Budget × String)
  | B, "--schritte" :: n :: rest => match n.toNat? with
    | some k => optionen { B with schritte := k } rest
    | none => .error "--schritte takes a number"
  | B, "--passes" :: n :: rest => match n.toNat? with
    | some k => optionen { B with passes := k } rest
    | none => .error "--passes takes a number"
  | B, [p] => .ok (B, p)
  | _, _ => .error "usage: stage0 [--schritte N] [--passes N] PROGRAM.gab < INPUT > OUTPUT"

def haupt (args : List String) : IO UInt32 := do
  match optionen {} args with
  | .error e => IO.eprintln e; pure 2
  | .ok (B, pfad) =>
    let src ← IO.FS.readFile pfad
    let ein ← (← IO.getStdin).readBinToEnd
    match boot B src ein.toList with
    | .error e => IO.eprintln ("stage0: " ++ e); pure 1
    | .ok aus =>
      let out ← IO.getStdout
      out.write ⟨aus.toArray⟩
      out.flush
      pure 0

end Gabbro.Stage0

def main (args : List String) : IO UInt32 := Gabbro.Stage0.haupt args
