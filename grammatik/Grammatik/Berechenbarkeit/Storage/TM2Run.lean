import Grammatik.Berechenbarkeit.Storage.TM2Initialize
import Grammatik.Berechenbarkeit.Brainfuck.Fuel

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.TM2Heap

open ArenaOwnership (Frame)

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

inductive RunResult (Γ : K → Type) (Λ σ : Type) where
  | halted (configuration : Configuration Γ Λ σ)
  | exhausted (configuration : Configuration Γ Λ σ)
  | outOfMemory (storage : Store Γ)
  | invalid (storage : Store Γ)

/-- Fuel counts finite-control transitions. Halt, an insufficient bound and a
provider refusal are different constructors, including at zero fuel. -/
def drive (program : Λ → Turing.TM2.Stmt Γ Λ σ) (available : Bool) (frame : Frame) :
    Nat → Configuration Γ Λ σ → RunResult Γ Λ σ
  | fuel, C =>
    match C.label with
    | none => .halted C
    | some label =>
      match fuel with
      | 0 => .exhausted C
      | fuel + 1 =>
        match evaluate available frame (program label) C.state C.storage with
        | .success C' => drive program available frame fuel C'
        | .outOfMemory S => .outOfMemory S
        | .invalid S => .invalid S

def RunResult.Matches (result : RunResult Γ Λ σ) (frame : Frame)
    (source : Brainfuck.RunResult (Turing.TM2.Cfg Γ Λ σ)) : Prop :=
  match result, source with
  | .halted C, .halted c | .exhausted C, .exhausted c => C.Represents frame c
  | _, _ => False

/-- Exact finite-budget correspondence. Allocation is available in this theorem;
no fuel exhaustion or OOM is identified with a successful source halt. -/
theorem drive_correct (program : Λ → Turing.TM2.Stmt Γ Λ σ) (frame : Frame) (fuel : Nat)
    {C : Configuration Γ Λ σ} {c : Turing.TM2.Cfg Γ Λ σ} (hr : C.Represents frame c) :
    (drive program true frame fuel C).Matches frame (Brainfuck.runFor (Turing.TM2.step program) fuel c) := by
  induction fuel generalizing C c with
  | zero =>
    rcases C with ⟨label, state, S⟩
    rcases c with ⟨sourceLabel, sourceState, values⟩
    obtain ⟨rfl, rfl, hr⟩ := hr
    cases label <;> exact ⟨rfl, rfl, hr⟩
  | succ fuel ih =>
    rcases C with ⟨label, state, S⟩
    rcases c with ⟨sourceLabel, sourceState, values⟩
    obtain ⟨rfl, rfl, hr⟩ := hr
    cases label with
    | none => exact ⟨rfl, rfl, hr⟩
    | some label =>
      obtain ⟨S', he, hr'⟩ := evaluate_correct (program label) frame state S values hr
      have hi := ih (C := ⟨(Turing.TM2.stepAux (program label) state values).l,
        (Turing.TM2.stepAux (program label) state values).var, S'⟩)
        (c := Turing.TM2.stepAux (program label) state values) ⟨rfl, rfl, hr'⟩
      rw [drive]
      dsimp only
      rw [he]
      exact hi

theorem drive_complete (program : Λ → Turing.TM2.Stmt Γ Λ σ) (frame : Frame) (fuel : Nat)
    {C : Configuration Γ Λ σ} {c c' : Turing.TM2.Cfg Γ Λ σ} (hr : C.Represents frame c)
    (he : Brainfuck.runFor (Turing.TM2.step program) fuel c = .halted c') :
    ∃ C', drive program true frame fuel C = .halted C' ∧ C'.Represents frame c' := by
  have hh := drive_correct program frame fuel hr
  rw [he] at hh
  cases hd : drive program true frame fuel C with
  | halted C' => exact ⟨C', rfl, by simpa [hd, RunResult.Matches] using hh⟩
  | exhausted C' => simp [hd, RunResult.Matches] at hh
  | outOfMemory S => simp [hd, RunResult.Matches] at hh
  | invalid S => simp [hd, RunResult.Matches] at hh

theorem drive_sound (program : Λ → Turing.TM2.Stmt Γ Λ σ) (frame : Frame) (fuel : Nat)
    {C C' : Configuration Γ Λ σ} {c : Turing.TM2.Cfg Γ Λ σ} (hr : C.Represents frame c)
    (he : drive program true frame fuel C = .halted C') :
    ∃ c', Brainfuck.runFor (Turing.TM2.step program) fuel c = .halted c' ∧ C'.Represents frame c' := by
  have hh := drive_correct program frame fuel hr
  rw [he] at hh
  cases hs : Brainfuck.runFor (Turing.TM2.step program) fuel c with
  | halted c' => exact ⟨c', rfl, by simpa [hs, RunResult.Matches] using hh⟩
  | exhausted c' => simp [hs, RunResult.Matches] at hh

/-- Failure retains a safe prefix; it is the only additional allowed outcome.
Every normal result still matches exactly the same finite TM2 budget. -/
def RunResult.PartialMatches (result : RunResult Γ Λ σ) (frame : Frame)
    (source : Brainfuck.RunResult (Turing.TM2.Cfg Γ Λ σ)) : Prop :=
  match result with
  | .outOfMemory S => ∃ values, S.Represents frame values
  | .invalid _ => False
  | _ => result.Matches frame source

theorem drive_partial_correct (program : Λ → Turing.TM2.Stmt Γ Λ σ) (available : Bool)
    (frame : Frame) (fuel : Nat) {C : Configuration Γ Λ σ} {c : Turing.TM2.Cfg Γ Λ σ}
    (hr : C.Represents frame c) :
    (drive program available frame fuel C).PartialMatches frame
      (Brainfuck.runFor (Turing.TM2.step program) fuel c) := by
  induction fuel generalizing C c with
  | zero =>
    rcases C with ⟨label, state, S⟩
    rcases c with ⟨sourceLabel, sourceState, values⟩
    obtain ⟨rfl, rfl, hr⟩ := hr
    cases label <;> exact ⟨rfl, rfl, hr⟩
  | succ fuel ih =>
    rcases C with ⟨label, state, S⟩
    rcases c with ⟨sourceLabel, sourceState, values⟩
    obtain ⟨rfl, rfl, hr⟩ := hr
    cases label with
    | none => exact ⟨rfl, rfl, hr⟩
    | some label =>
      have hs := evaluate_safe (program label) available frame state S values hr
      cases he : evaluate available frame (program label) state S with
      | success C' =>
        have hc : C'.Represents frame (Turing.TM2.stepAux (program label) state values) := by
          simpa [he, Outcome.Compatible] using hs
        rw [drive]
        dsimp only
        rw [he]
        exact ih hc
      | outOfMemory S' =>
        rw [drive]
        dsimp only
        rw [he]
        simpa [RunResult.PartialMatches, he, Outcome.Compatible] using hs
      | invalid S' => simp [he, Outcome.Compatible] at hs

theorem drive_sound_any (program : Λ → Turing.TM2.Stmt Γ Λ σ) (available : Bool) (frame : Frame)
    (fuel : Nat) {C C' : Configuration Γ Λ σ} {c : Turing.TM2.Cfg Γ Λ σ}
    (hr : C.Represents frame c) (he : drive program available frame fuel C = .halted C') :
    ∃ c', Brainfuck.runFor (Turing.TM2.step program) fuel c = .halted c' ∧ C'.Represents frame c' := by
  have hh := drive_partial_correct program available frame fuel hr
  rw [he] at hh
  cases hs : Brainfuck.runFor (Turing.TM2.step program) fuel c with
  | halted c' => exact ⟨c', rfl, by simpa [hs, RunResult.PartialMatches, RunResult.Matches] using hh⟩
  | exhausted c' => simp [hs, RunResult.PartialMatches, RunResult.Matches] at hh

end Gabbro.Grammatik.Berechenbarkeit.Storage.TM2Heap
