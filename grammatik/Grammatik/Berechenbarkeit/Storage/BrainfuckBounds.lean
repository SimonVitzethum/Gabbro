import Grammatik.Berechenbarkeit.Storage.BrainfuckHeap
import Grammatik.Berechenbarkeit.Storage.TM2Cost

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.BrainfuckHeap

open ArenaOwnership (Frame)
open TM2Heap

theorem jump_operation_bound {n : Nat} (pc : Fin (n + 1)) : operationBound (Brainfuck.jump pc) = 1 := by
  unfold Brainfuck.jump
  split <;> rfl

/-- At most one allocation and one pop, plus final control transfer. -/
theorem instruction_operation_bound {n : Nat} (op : Brainfuck.Instruction n) (next : Fin (n + 1)) :
    operationBound (Brainfuck.compileInstruction op next) ≤ 4 := by
  cases op <;> simp only [Brainfuck.compileInstruction, Fin.isValue, operationBound, jump_operation_bound, Nat.reduceAdd, Std.le_refl, Nat.reduceLeDiff, max_self]

theorem program_operation_bound {n : Nat} (p : Brainfuck.Program n) (label : Fin (n + 1)) :
    operationBound (Brainfuck.compile p label) ≤ 4 := by
  unfold Brainfuck.compile
  split
  · exact instruction_operation_bound _ _
  · change 1 ≤ 4; omega

/-- No termination prediction is needed to bound a proposed finite run. -/
theorem conditional_operation_bound {n : Nat} (p : Brainfuck.Program n) (available : Bool)
    (frame : Frame) (fuel : Nat)
    (C : Configuration (fun _ : Brainfuck.Stack => Brainfuck.Byte) (Fin (n + 1)) Brainfuck.Byte) :
    ∃ operations, Driven (Brainfuck.compile p) available frame (transitionBudget n fuel) C operations
        (drive (Brainfuck.compile p) available frame (transitionBudget n fuel) C) ∧
      operations ≤ transitionBudget n fuel * 4 :=
  drive_operation_bound _ _ _ _ _ 4 (program_operation_bound p)

/-- A real source halting trace gives both an executable target termination
certificate and its operation bound. Input loading and output observation are
separate finite procedures; this bound covers the interpreter run between them. -/
theorem halting_trace_with_bound {n k : Nat} (p : Brainfuck.Program n) (frame : Frame)
    (input : List Brainfuck.Byte) (target : Brainfuck.State n)
    (ht : Brainfuck.Steps p k (Brainfuck.initial input) target) (hh : Brainfuck.step p target = none) :
    ∃ start C operations,
      loadInput (Brainfuck.finiteMachine p) true frame input = .success start ∧
      run p true frame k input = .halted C ∧
      Driven (Brainfuck.compile p) true frame (transitionBudget n k) start operations (.halted C) ∧
      operations ≤ transitionBudget n k * 4 ∧ observedOutput C frame = some target.output := by
  obtain ⟨start, hs, hr⟩ := loadInput_correct (Brainfuck.finiteMachine p) frame input
  have hcert := Brainfuck.runFor_complete ht hh k (Nat.le_refl _)
  obtain ⟨C, he, _, hout⟩ := run_complete p frame k input hcert
  obtain ⟨operations, htrace, hbound⟩ := conditional_operation_bound p true frame k start
  have hd : drive (Brainfuck.compile p) true frame (transitionBudget n k) start = .halted C := by
    simpa [run, hs] using he
  rw [hd] at htrace
  exact ⟨start, C, operations, hs, he, htrace, hbound, hout⟩

end Gabbro.Grammatik.Berechenbarkeit.Storage.BrainfuckHeap
