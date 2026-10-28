/-
  File:      Grammatik/Berechenbarkeit/Brainfuck/Fuel.lean
  Subject:   Executable finite termination certificates, with exhaustion kept distinct.

  Fuel counts source/TM2 small steps here, not Gabbro loop passes. A checked finite run
  proves normal termination; exhaustion says only that this bound was insufficient.
  The exact same bound works for the proved one-step BF-to-TM2 translation. Its later
  transfer to Gabbro needs the actual target's administrative/scheduler overhead proof.
-/
import Grammatik.Berechenbarkeit.Brainfuck.ToTM2

namespace Gabbro.Grammatik.Berechenbarkeit.Brainfuck

inductive RunResult (S : Type) where
  | halted (state : S)
  | exhausted (state : S)
  deriving DecidableEq, Repr

def RunResult.map {S T : Type} (f : S → T) : RunResult S → RunResult T
  | .halted s => .halted (f s)
  | .exhausted s => .exhausted (f s)

/-- A total checker for a proposed finite step bound. Even at zero fuel, a state
    already at normal halt is recognized; no actual transition is allowed for free. -/
def runFor {S : Type} (advance : S → Option S) : Nat → S → RunResult S
  | 0, s => match advance s with
      | none => .halted s
      | some _ => .exhausted s
  | fuel + 1, s => match advance s with
      | none => .halted s
      | some t => runFor advance fuel t

/-- A normal answer from the bounded checker contains a real finite halting trace. -/
theorem runFor_sound {n : Nat} (p : Program n) (fuel : Nat) (s t : State n)
    (h : runFor (step p) fuel s = .halted t) :
    ∃ k, k ≤ fuel ∧ Steps p k s t ∧ step p t = none := by
  induction fuel generalizing s with
  | zero =>
      cases hs : step p s with
      | none => simp only [runFor, hs, RunResult.halted.injEq] at h
                subst t
                exact ⟨0, Nat.le_refl _, .zero s, hs⟩
      | some u => simp only [runFor, hs, reduceCtorEq] at h
  | succ fuel ih =>
      cases hs : step p s with
      | none => simp only [runFor, hs, RunResult.halted.injEq] at h
                subst t
                exact ⟨0, Nat.zero_le _, .zero s, hs⟩
      | some u =>
          simp only [runFor, hs] at h
          obtain ⟨k, hk, ht, hn⟩ := ih u h
          exact ⟨k + 1, by omega, .more hs ht, hn⟩

/-- A supplied finite halting trace is recognized at every sufficient bound. -/
theorem runFor_complete {n : Nat} {p : Program n} {k : Nat} {s t : State n}
    (trace : Steps p k s t) (halt : step p t = none) :
    ∀ fuel, k ≤ fuel → runFor (step p) fuel s = .halted t := by
  induction trace with
  | zero s => intro fuel _; cases fuel <;> simp only [runFor, halt]
  | more hs _ ih =>
      intro fuel bound
      cases fuel with
      | zero => omega
      | succ fuel => simpa only [runFor, hs] using ih halt fuel (by omega)

theorem runFor_iff {n : Nat} (p : Program n) (fuel : Nat) (s t : State n) :
    runFor (step p) fuel s = .halted t ↔
      ∃ k, k ≤ fuel ∧ Steps p k s t ∧ step p t = none :=
  ⟨runFor_sound p fuel s t, fun ⟨_, hk, ht, hn⟩ => runFor_complete ht hn fuel hk⟩

/-- Termination is exactly the existence of a checkable finite certificate. This
    semidecision does not promise a finite answer when the program diverges. -/
theorem haltsWith_iff_fuel {n : Nat} (p : Program n) (input output : List Byte) :
    HaltsWith p input output ↔
      ∃ fuel s, runFor (step p) fuel (initial input) = .halted s ∧ s.output = output := by
  constructor
  · rintro ⟨k, s, ht, hn, ho⟩
    exact ⟨k, s, runFor_complete ht hn k (Nat.le_refl _), ho⟩
  · rintro ⟨fuel, s, hs, ho⟩
    obtain ⟨k, _, ht, hn⟩ := runFor_sound p fuel _ _ hs
    exact ⟨k, s, ht, hn, ho⟩

/-- Increasing a sufficient bound preserves the complete result. -/
theorem runFor_mono {n : Nat} (p : Program n) {fuel larger : Nat} (bound : fuel ≤ larger)
    {s t : State n} (h : runFor (step p) fuel s = .halted t) :
    runFor (step p) larger s = .halted t := by
  obtain ⟨k, hk, ht, hn⟩ := runFor_sound p fuel s t h
  exact runFor_complete ht hn larger (Nat.le_trans hk bound)

/-- Source and TM2 bounded execution agree on both normal halt and exhaustion,
    including the full intermediate tape/input/output state. -/
theorem runFor_translation {n : Nat} (p : Program n) (fuel : Nat) (s : State n) :
    runFor (Turing.TM2.step (compile p)) fuel (encode s) =
      (runFor (step p) fuel s).map encode := by
  induction fuel generalizing s with
  | zero => cases hs : step p s <;> simp only [runFor, step_correct, hs, Option.map_none, RunResult.map, Option.map_some]
  | succ fuel ih =>
      cases hs : step p s with
      | none => simp only [runFor, step_correct, hs, Option.map_none, RunResult.map]
      | some t => simpa only [runFor, step_correct, hs, Option.map_some] using ih t

end Gabbro.Grammatik.Berechenbarkeit.Brainfuck
