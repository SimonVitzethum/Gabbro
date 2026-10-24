/-
  File:      Grammatik/Berechenbarkeit/Brainfuck/Witnesses.lean
  Subject:   Nondegenerate byte-Brainfuck and TM2 compiler witnesses.

  These are reference semantics/compiler witnesses, not Gabbro-backend certificates.
  They exercise real tape writes, both pointer directions, nested loops, input/EOF,
  output, wraparound, an insufficient bound, and output followed by divergence.
-/
import Grammatik.Berechenbarkeit.Brainfuck.Fuel

namespace Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses

/-- `,[>+<-]>.`: move the input byte to the next tape cell, then print it. -/
def transfer : Program 9 :=
  ⟨#v[.input, .open 7, .right, .increment, .left, .decrement, .close 2, .right, .output], by decide⟩

def transferFinal : State 9 := ⟨9, 3, [0], [], [], [3]⟩

theorem transfer_zeuge :
    runFor (step transfer) 19 (initial [3]) = .halted transferFinal := by decide

theorem transfer_halts_zeuge : HaltsWith transfer [3] [3] :=
  (haltsWith_iff_fuel _ _ _).mpr ⟨19, transferFinal, transfer_zeuge, rfl⟩

theorem transfer_tm2_zeuge : TMHaltsWith transfer [3] [3] :=
  (compiler_correct _ _ _).mp transfer_halts_zeuge

theorem insufficient_fuel_zeuge : ∃ s,
    runFor (step transfer) 18 (initial [3]) = .exhausted s ∧ s.output = [] := by
  exact ⟨⟨8, 3, [0], [], [], []⟩, by decide, rfl⟩

/-- EOF supplies zero, so the loop is skipped and the next zero cell is printed. -/
theorem eof_zeuge : HaltsWith transfer [] [0] := by
  apply (haltsWith_iff_fuel _ _ _).mpr
  exact ⟨4, ⟨9, 0, [0], [], [], [0]⟩, by decide, rfl⟩

/-- `++[>++[>+<-]<-]>>.`: genuinely nested, data-dependent loops. -/
def nested : Program 18 :=
  ⟨#v[.increment, .increment, .open 15, .right, .increment, .increment, .open 12,
      .right, .increment, .left, .decrement, .close 7, .left, .decrement, .close 3,
      .right, .right, .output], by decide⟩

theorem nested_zeuge : HaltsWith nested [] [4] := by
  apply (haltsWith_iff_fuel _ _ _).mpr
  exact ⟨40, ⟨18, 4, [0, 0], [], [], [4]⟩, by decide, rfl⟩

def wrap : Program 2 := ⟨#v[.decrement, .output], by decide⟩

theorem wrap_zeuge : HaltsWith wrap [] [255] := by
  apply (haltsWith_iff_fuel _ _ _).mpr
  exact ⟨2, ⟨2, 255, [], [], [], [255]⟩, by decide, rfl⟩

/-- `.+[]`: an output is already visible before an infinite loop. -/
def diverging : Program 4 :=
  ⟨#v[.output, .increment, .open 4, .close 3], by decide⟩

def spin : State 4 := ⟨3, 1, [], [], [], [0]⟩

theorem output_before_divergence_zeuge :
    runFor (step diverging) 3 (initial []) = .exhausted spin ∧ spin.output = [0] := by decide

theorem spin_step_zeuge : step diverging spin = some spin := rfl

/-- A genuine self-loop has no finite halting evaluation. -/
theorem self_loop_not_terminating {S : Type} (advance : S → Option S) (s : S)
    (loop : advance s = some s) : ¬ (StateTransition.eval advance s).Dom := by
  intro terminates
  have member : (StateTransition.eval advance s).get terminates ∈ StateTransition.eval advance s :=
    ⟨terminates, rfl⟩
  have impossible : advance s = some s → False :=
    StateTransition.evalInduction (C := fun a => advance a = some a → False) member
      (fun a _ ih ha => ih a ha ha)
  exact impossible loop

theorem divergence_zeuge : ¬ (StateTransition.eval (step diverging) (initial [])).Dom := by
  have hrun : StateTransition.Reaches (step diverging) (initial []) spin :=
    .head rfl (.head rfl (.head rfl .refl))
  rw [StateTransition.reaches_eval hrun]
  exact self_loop_not_terminating _ _ spin_step_zeuge

/-- Reflection rules out even a spurious normal TM2 halt, while preserving the earlier output. -/
theorem tm2_divergence_zeuge :
    ¬ (StateTransition.eval (Turing.TM2.step (compile diverging)) (encode (initial []))).Dom :=
  fun h => divergence_zeuge ((termination_iff _ _).mp h)

/-- Reversed or unmatched bracket destinations do not get a well-formed-program proof. -/
theorem invalid_brackets_zeuge :
    checkBrackets ([.open 3, .increment, .close 2] : List (Instruction 3)) 0 [] = false ∧
    checkBrackets ([.close 0] : List (Instruction 1)) 0 [] = false := by decide

/-- `+[>+]`: this one fixed finite program grows the tape without bound. -/
def growing : Program 5 :=
  ⟨#v[.increment, .open 5, .right, .increment, .close 2], by decide⟩

def growingState (n : Nat) : State 5 := ⟨2, 1, List.replicate n 1, [], [], []⟩

theorem growing_next (n : Nat) :
    StateTransition.Reaches (step growing) (growingState n) (growingState (n + 1)) :=
  .head rfl (.head rfl (.head rfl .refl))

theorem growing_reached (n : Nat) :
    StateTransition.Reaches (step growing) (initial []) (growingState n) := by
  induction n with
  | zero => exact .head rfl (.head rfl .refl)
  | succ n ih => exact ih.trans (growing_next n)

/-- The unbounded-tape premise is met by reachable source states, not an arbitrary
    infinite initial tape or a machine family with an increasing fixed capacity. -/
theorem unbounded_tape_zeuge (n : Nat) :
    ∃ s, StateTransition.Reaches (step growing) (initial []) s ∧ s.left.length = n :=
  ⟨growingState n, growing_reached n, List.length_replicate⟩

theorem unbounded_tm2_zeuge (n : Nat) :
    ∃ t, Turing.TM2.Reaches (compile growing) (encode (initial [])) t ∧ (t.stk .left).length = n :=
  ⟨encode (growingState n), reachable_preservation growing (growing_reached n), List.length_replicate⟩

end Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses
