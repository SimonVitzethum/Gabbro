import Grammatik.Berechenbarkeit.Storage.BrainfuckHeap
import Grammatik.Berechenbarkeit.Brainfuck.Witnesses

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.HeapWitnesses

open ArenaOwnership (Frame)
open TM2Heap

def owner : Frame := ⟨0, 0⟩

inductive Observation where
  | halted (output : List Brainfuck.Byte)
  | exhausted
  | outOfMemory
  | invalid
  | invalidOutput
  deriving DecidableEq, Repr

def observe {n : Nat}
    (result : TM2Heap.RunResult (fun _ : Brainfuck.Stack => Brainfuck.Byte) (Fin (n + 1)) Brainfuck.Byte) :
    Observation :=
  match result with
  | .halted C =>
    match BrainfuckHeap.observedOutput C owner with
    | some output => .halted output
    | none => .invalidOutput
  | .exhausted _ => .exhausted
  | .outOfMemory _ => .outOfMemory
  | .invalid _ => .invalid

def currentOutput {n : Nat}
    (result : TM2Heap.RunResult (fun _ : Brainfuck.Stack => Brainfuck.Byte) (Fin (n + 1)) Brainfuck.Byte) :
    Option (List Brainfuck.Byte) :=
  match result with
  | .halted C | .exhausted C => BrainfuckHeap.observedOutput C owner
  | .outOfMemory S => (S.observe owner .output).map List.reverse
  | .invalid _ => none

set_option maxRecDepth 8192 in
theorem transfer_zeuge :
    observe (BrainfuckHeap.run Brainfuck.Witnesses.transfer true owner 19 [3]) = .halted [3] := by decide

set_option maxRecDepth 8192 in
theorem insufficient_fuel_zeuge :
    observe (BrainfuckHeap.run Brainfuck.Witnesses.transfer true owner 18 [3]) = .exhausted := by decide

set_option maxRecDepth 8192 in
theorem nested_zeuge :
    observe (BrainfuckHeap.run Brainfuck.Witnesses.nested true owner 40 []) = .halted [4] := by decide

theorem wrap_zeuge :
    observe (BrainfuckHeap.run Brainfuck.Witnesses.wrap true owner 2 []) = .halted [255] := by decide

def emptyProgram : Brainfuck.Program 0 := ⟨#v[], by decide⟩

theorem empty_entry_zeuge :
    observe (BrainfuckHeap.run emptyProgram true owner 0 [7]) = .halted [] := by decide

theorem input_oom_zeuge :
    observe (BrainfuckHeap.run Brainfuck.Witnesses.transfer false owner 19 [3]) = .outOfMemory := by decide

theorem output_oom_zeuge :
    observe (BrainfuckHeap.run Brainfuck.Witnesses.wrap false owner 2 []) = .outOfMemory := by decide

set_option maxRecDepth 8192 in
theorem output_prefix_zeuge :
    observe (BrainfuckHeap.run Brainfuck.Witnesses.diverging true owner 10 []) = .exhausted ∧
    currentOutput (BrainfuckHeap.run Brainfuck.Witnesses.diverging true owner 10 []) = some [0] := by decide

/-- No target budget and no provider answer can turn the divergent guest into
a normal halt. This is a generic proof application, not just a finite probe. -/
theorem divergence_zeuge (available : Bool) (fuel : Nat)
    (C : Configuration (fun _ : Brainfuck.Stack => Brainfuck.Byte) (Fin 5) Brainfuck.Byte) :
    BrainfuckHeap.run Brainfuck.Witnesses.diverging available owner fuel [] ≠ .halted C :=
  BrainfuckHeap.divergence_preserved _ _ Brainfuck.Witnesses.divergence_zeuge available owner fuel C

def peekProgram : Turing.TM2.Stmt (fun _ : Unit => Bool) Unit Bool :=
  .push () id (.load not (.peek () (fun _ value => value.getD false)
    (.pop () (fun _ value => !(value.getD false)) .halt)))

def inspectBool (result : Outcome (fun _ : Unit => Bool) Unit Bool) :
    Option (Bool × Option (List Bool) × Nat × Nat) :=
  match result with
  | .success C => some (C.state, C.storage.observe owner (),
      (C.storage.regions ()).memory.extent, (C.storage.regions ()).memory.free.length)
  | _ => none

/-- Peek preserves the cell; the following pop still sees it and releases it. -/
theorem peek_pop_zeuge :
    inspectBool (evaluate true owner peekProgram true .empty) = some (false, some [], 1, 1) := by decide

end Gabbro.Grammatik.Berechenbarkeit.Storage.HeapWitnesses
