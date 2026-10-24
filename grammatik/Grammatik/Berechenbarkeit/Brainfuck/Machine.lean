/-
  File:      Grammatik/Berechenbarkeit/Brainfuck/Machine.lean
  Subject:   Byte Brainfuck with an unbounded tape and an explicit bracket validator.

  A finite program has all eight commands and bounded jump destinations. The validator
  additionally checks properly nested matching brackets. Tape storage is two finite lists
  around the head, extended with zero on demand, with no fixed capacity. Output is stored
  in reverse order; `output` presents the externally visible order. EOF supplies zero.
-/
import Mathlib.Computability.TuringMachine.StackTuringMachine

namespace Gabbro.Grammatik.Berechenbarkeit.Brainfuck

abbrev Byte := Fin 256

def increment (b : Byte) : Byte := ⟨(b.val + 1) % 256, Nat.mod_lt _ (by decide)⟩
def decrement (b : Byte) : Byte := ⟨(b.val + 255) % 256, Nat.mod_lt _ (by decide)⟩

/-- Closing brackets jump to the first command of the body on a nonzero head. -/
inductive Instruction (n : Nat) where
  | right | left | increment | decrement | input | output
  | open (exit : Fin (n + 1))
  | close (body : Fin (n + 1))
  deriving DecidableEq, Repr

/-- Check both nesting and the exact opening/closing jump destinations. -/
def checkBrackets {n : Nat} : List (Instruction n) → Nat → List (Nat × Nat) → Bool
  | [], _, stack => stack.isEmpty
  | .open exit :: rest, pc, stack => checkBrackets rest (pc + 1) ((pc, exit.val) :: stack)
  | .close body :: rest, pc, (opening, exit) :: stack =>
      body.val == opening + 1 && exit == pc + 1 && checkBrackets rest (pc + 1) stack
  | .close _ :: _, _, [] => false
  | _ :: rest, pc, stack => checkBrackets rest (pc + 1) stack

/-- Finite syntax, not a host-language evaluator. `valid` excludes malformed brackets. -/
structure Program (n : Nat) where
  code : Vector (Instruction n) n
  valid : checkBrackets code.toList 0 [] = true

/-- No tape extent bound: either list can grow during execution. -/
structure State (n : Nat) where
  pc : Fin (n + 1)
  head : Byte
  left : List Byte
  right : List Byte
  remainingInput : List Byte
  reversedOutput : List Byte
  deriving DecidableEq, Repr

def State.output {n : Nat} (s : State n) : List Byte := s.reversedOutput.reverse

def initial {n : Nat} (input : List Byte) : State n :=
  ⟨0, 0, [], [], input, []⟩

def successor {n : Nat} (pc : Fin (n + 1)) (running : pc.val < n) : Fin (n + 1) :=
  ⟨pc.val + 1, by omega⟩

/-- The source operation on the unbounded tape, with explicit control-flow destinations. -/
def execute {n : Nat} (op : Instruction n) (next : Fin (n + 1)) (s : State n) : State n :=
    match op with
    | .right => { s with pc := next, left := s.head :: s.left, head := s.right.headD 0, right := s.right.tail }
    | .left => { s with pc := next, right := s.head :: s.right, head := s.left.headD 0, left := s.left.tail }
    | .increment => { s with pc := next, head := increment s.head }
    | .decrement => { s with pc := next, head := decrement s.head }
    | .input => { s with pc := next, head := s.remainingInput.headD 0, remainingInput := s.remainingInput.tail }
    | .output => { s with pc := next, reversedOutput := s.head :: s.reversedOutput }
    | .open exit => { s with pc := if s.head = 0 then exit else next }
    | .close body => { s with pc := if s.head = 0 then next else body }

/-- One executable small step. Only reaching the end of the program is normal halt. -/
def step {n : Nat} (p : Program n) (s : State n) : Option (State n) :=
  if running : s.pc.val < n then
    some (execute (p.code.get ⟨s.pc.val, running⟩) (successor s.pc running) s)
  else none

/-- A finite run with exactly `k` genuine source steps. -/
inductive Steps {n : Nat} (p : Program n) : Nat → State n → State n → Prop where
  | zero (s) : Steps p 0 s s
  | more {k s t u} : step p s = some t → Steps p k t u → Steps p (k + 1) s u

def HaltsWith {n : Nat} (p : Program n) (input output : List Byte) : Prop :=
  ∃ k s, Steps p k (initial input) s ∧ step p s = none ∧ s.output = output

/-- Normal halt is determined exactly by the program counter, not by a resource stop. -/
theorem halt_iff {n : Nat} (p : Program n) (s : State n) :
    step p s = none ↔ s.pc.val = n := by
  unfold step
  split <;> simp_all <;> omega

theorem increment_wrap : increment 255 = 0 := by decide
theorem decrement_wrap : decrement 0 = 255 := by decide

end Gabbro.Grammatik.Berechenbarkeit.Brainfuck
