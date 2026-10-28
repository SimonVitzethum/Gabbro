import Grammatik.Berechenbarkeit.Storage.TM2Observe

/-! Brainfuck.Byte-Brainfuck on executable linked region storage. The existing BF→TM2
compiler is reused, including its finite source labels and byte-valued control.
The target is the new heap component; the final G admission/compiler bridge is
still required before this becomes a Gabbro universality theorem. -/

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.BrainfuckHeap

open ArenaOwnership (Frame)
open Brainfuck
open TM2Heap

def transitionBudget (size fuel : Nat) : Nat := fuel + if size = 0 then 1 else 0

/-- The empty source starts already halted. Mathlib's bundled machine starts at
its main label, so that one case has exactly one silent entry/halt transition. -/
theorem initial_budget {n : Nat} (p : Program n) (input : List Brainfuck.Byte) (fuel : Nat) :
    Brainfuck.runFor (Turing.TM2.step (compile p)) (transitionBudget n fuel)
      (Turing.initList (finiteMachine p) input) =
        (Brainfuck.runFor (Brainfuck.step p) fuel (initial input)).map encode := by
  cases n with
  | zero =>
    have hentry : Turing.TM2.step (compile p) (Turing.initList (finiteMachine p) input) =
        some (encode (initial input)) := by
      change some ⟨none, 0, (Turing.initList (finiteMachine p) input).stk⟩ = some (encode (initial input))
      congr 2
      funext k; cases k <;> rfl
    have ht : ∀ fuel, Brainfuck.runFor (Turing.TM2.step (compile p)) fuel (encode (initial input)) =
        .halted (encode (initial input)) := by intro fuel; cases fuel <;> rfl
    have hs : ∀ fuel, Brainfuck.runFor (Brainfuck.step p) fuel (initial input) =
        .halted (initial input) := by intro fuel; cases fuel <;> rfl
    simp only [transitionBudget, ite_true, Brainfuck.runFor, hentry, ht, hs, Brainfuck.RunResult.map]
  | succ n =>
    simpa [transitionBudget, finite_initial_nonempty] using runFor_translation p fuel (initial input)

def run {n : Nat} (p : Program n) (available : Bool) (frame : Frame) (fuel : Nat) (input : List Brainfuck.Byte) :
    TM2Heap.RunResult (fun _ : Stack => Brainfuck.Byte) (Fin (n + 1)) Brainfuck.Byte :=
  match loadInput (finiteMachine p) available frame input with
  | .success C => drive (compile p) available frame (transitionBudget n fuel) C
  | .outOfMemory S => .outOfMemory S
  | .invalid S => .invalid S

def observedOutput {n : Nat}
    (C : Configuration (fun _ : Stack => Brainfuck.Byte) (Fin (n + 1)) Brainfuck.Byte) (frame : Frame) : Option (List Brainfuck.Byte) :=
  (C.storage.observe frame .output).map List.reverse

/-- Every supplied finite halting certificate transfers to the allocated linked
representation, with exact output and a precise empty-program entry adjustment. -/
theorem run_complete {n : Nat} (p : Program n) (frame : Frame) (fuel : Nat) (input : List Brainfuck.Byte)
    {target : State n} (he : Brainfuck.runFor (Brainfuck.step p) fuel (initial input) = .halted target) :
    ∃ C, run p true frame fuel input = .halted C ∧
      C.Represents frame (encode target) ∧ observedOutput C frame = some target.output := by
  obtain ⟨start, hstart, hr⟩ := loadInput_correct (finiteMachine p) frame input
  have hsource := initial_budget p input fuel
  rw [he] at hsource
  obtain ⟨C, hrun, hrep⟩ := drive_complete (compile p) frame (transitionBudget n fuel) hr hsource
  refine ⟨C, by simp only [run, hstart, hrun], hrep, ?_⟩
  have hout := Store.observe_correct hrep.2.2 Stack.output
  simp only [observedOutput, hout, encode, storageOf, Option.map_some, State.output]

/-- Conversely, normal target completion contains a genuine finite source
halting certificate. Exhaustion and OOM cannot be used as such a certificate. -/
theorem run_sound {n : Nat} (p : Program n) (frame : Frame) (fuel : Nat) (input : List Brainfuck.Byte)
    {C : Configuration (fun _ : Stack => Brainfuck.Byte) (Fin (n + 1)) Brainfuck.Byte}
    (he : run p true frame fuel input = .halted C) :
    ∃ target, Brainfuck.runFor (Brainfuck.step p) fuel (initial input) = .halted target ∧
      C.Represents frame (encode target) ∧ observedOutput C frame = some target.output := by
  obtain ⟨start, hstart, hr⟩ := loadInput_correct (finiteMachine p) frame input
  have hrun : drive (compile p) true frame (transitionBudget n fuel) start = .halted C := by
    simpa [run, hstart] using he
  obtain ⟨c, hs, hrep⟩ := drive_sound (compile p) frame (transitionBudget n fuel) hr hrun
  rw [initial_budget p input fuel] at hs
  cases ht : Brainfuck.runFor (Brainfuck.step p) fuel (initial input) with
  | exhausted target => simp only [RunResult.map, ht, reduceCtorEq] at hs
  | halted target =>
    simp only [ht, Brainfuck.RunResult.map, Brainfuck.RunResult.halted.injEq] at hs
    subst c
    refine ⟨target, rfl, hrep, ?_⟩
    have hout := Store.observe_correct hrep.2.2 Stack.output
    simp only [observedOutput, hout, encode, storageOf, Option.map_some, State.output]

theorem normal_halting_iff {n : Nat} (p : Program n) (frame : Frame) (fuel : Nat) (input output : List Brainfuck.Byte) :
    (∃ C, run p true frame fuel input = .halted C ∧ observedOutput C frame = some output) ↔
      ∃ target, Brainfuck.runFor (Brainfuck.step p) fuel (initial input) = .halted target ∧ target.output = output := by
  constructor
  · rintro ⟨C, he, hout⟩
    obtain ⟨target, ht, _, hvalue⟩ := run_sound p frame fuel input he
    exact ⟨target, ht, Option.some.inj (hvalue.symm.trans hout)⟩
  · rintro ⟨target, ht, rfl⟩
    obtain ⟨C, he, _, hout⟩ := run_complete p frame fuel input ht
    exact ⟨C, he, hout⟩

/-- Normal completion is equivalent to a finite source termination certificate;
this theorem supplies no procedure that terminates on every divergent program. -/
theorem compiler_correct {n : Nat} (p : Program n) (frame : Frame) (input output : List Brainfuck.Byte) :
    (∃ fuel C, run p true frame fuel input = .halted C ∧ observedOutput C frame = some output) ↔
      HaltsWith p input output := by
  rw [haltsWith_iff_fuel]
  constructor
  · rintro ⟨fuel, C, he, ho⟩
    obtain ⟨target, ht, hv⟩ := (normal_halting_iff p frame fuel input output).mp ⟨C, he, ho⟩
    exact ⟨fuel, target, ht, hv⟩
  · rintro ⟨fuel, target, ht, ho⟩
    obtain ⟨C, he, hv⟩ := (normal_halting_iff p frame fuel input output).mpr ⟨target, ht, ho⟩
    exact ⟨fuel, C, he, hv⟩

/-- Provider answers may remove successful runs, but cannot manufacture a normal
guest halt. This is soundness even when allocation is allowed to fail. -/
theorem run_sound_any {n : Nat} (p : Program n) (available : Bool) (frame : Frame) (fuel : Nat)
    (input : List Brainfuck.Byte) {C : Configuration (fun _ : Stack => Brainfuck.Byte) (Fin (n + 1)) Brainfuck.Byte}
    (he : run p available frame fuel input = .halted C) :
    ∃ target, Brainfuck.runFor (Brainfuck.step p) fuel (initial input) = .halted target ∧
      C.Represents frame (encode target) ∧ observedOutput C frame = some target.output := by
  have hload := loadInput_safe (finiteMachine p) available frame input
  cases hl : loadInput (finiteMachine p) available frame input with
  | outOfMemory S => simp only [run, hl, reduceCtorEq] at he
  | invalid S => simp only [Outcome.Compatible, hl] at hload
  | success start =>
    have hr : start.Represents frame (Turing.initList (finiteMachine p) input) := by
      simpa [hl, Outcome.Compatible] using hload
    have hrun : drive (compile p) available frame (transitionBudget n fuel) start = .halted C := by
      simpa [run, hl] using he
    obtain ⟨c, hs, hrep⟩ := drive_sound_any (compile p) available frame (transitionBudget n fuel) hr hrun
    rw [initial_budget p input fuel] at hs
    cases ht : Brainfuck.runFor (Brainfuck.step p) fuel (initial input) with
    | exhausted target => simp only [RunResult.map, ht, reduceCtorEq] at hs
    | halted target =>
      simp only [ht, Brainfuck.RunResult.map, Brainfuck.RunResult.halted.injEq] at hs
      subst c
      refine ⟨target, rfl, hrep, ?_⟩
      have hout := Store.observe_correct hrep.2.2 Stack.output
      simp only [observedOutput, hout, encode, storageOf, Option.map_some, State.output]

theorem divergence_preserved {n : Nat} (p : Program n) (input : List Brainfuck.Byte)
    (hd : ¬ (StateTransition.eval (Brainfuck.step p) (initial input)).Dom)
    (available : Bool) (frame : Frame) (fuel : Nat)
    (C : Configuration (fun _ : Stack => Brainfuck.Byte) (Fin (n + 1)) Brainfuck.Byte) :
    run p available frame fuel input ≠ .halted C := by
  intro he
  obtain ⟨target, ht, _, _⟩ := run_sound_any p available frame fuel input he
  have hh := (haltsWith_iff_fuel p input target.output).mpr ⟨fuel, target, ht, rfl⟩
  obtain ⟨t, hm, _⟩ := (haltsWith_iff_eval p input target.output).mp hh
  exact hd hm.1

end Gabbro.Grammatik.Berechenbarkeit.Storage.BrainfuckHeap
