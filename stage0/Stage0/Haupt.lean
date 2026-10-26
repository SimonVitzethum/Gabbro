/-
  File:      stage0/Stage0/Haupt.lean
  Subject:   The executable `stage0` (`stage0/lakefile.toml`).

    stage0 [--schritte N] [--passes N] PROGRAM.gab < INPUT > OUTPUT

  checks PROGRAM with the goal theorem's checker Bool and runs its `main` on the thread machine with real system calls
  (`bootIO`, `Tor/LaufIO.lean`: the run, then its replay under the observed answers). A program
  that binds system-call gates does its own input and output; one that binds none gets the input bytes in
  `io.ein`/`ein_len`, and its output is `io.aus` up to `aus_len`. A refusal or a stop goes to stderr with
  exit code 1.
-/
import Stage0.Tor.LaufIO

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
    match ← bootIO B src (do pure (← (← IO.getStdin).readBinToEnd).toList) with
    | .error e => IO.eprintln ("stage0: " ++ e); pure 1
    | .ok aus =>
      let out ← IO.getStdout
      out.write ⟨aus.toArray⟩
      out.flush
      -- threads still blocked in the kernel do not hold up the end of the run
      IO.Process.exit 0

end Gabbro.Stage0

def main (args : List String) : IO UInt32 := Gabbro.Stage0.haupt args
