import Grammatik.Berechenbarkeit.Storage.TM2Run

/-! Conditional operation bounds for the linked-store interpreter. Units count
abstract heap primitives and control operations, not CPU cycles, allocator
latency, provider latency or the physical cost of representing a reference.
Hardware/WCET and G cost bridges are separate obligations. -/

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.TM2Heap

open ArenaOwnership (Frame)

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

def operationBound : Turing.TM2.Stmt Γ Λ σ → Nat
  | .push _ _ rest | .peek _ _ rest | .load _ rest => 1 + operationBound rest
  | .pop _ _ rest => 2 + operationBound rest
  | .branch _ yes no => 1 + max (operationBound yes) (operationBound no)
  | .goto _ | .halt => 1

/-- A faithful trace of the existing interpreter, including failed operations. -/
inductive Counted (available : Bool) (frame : Frame) :
    Turing.TM2.Stmt Γ Λ σ → σ → Store Γ → Nat → Outcome Γ Λ σ → Prop where
  | pushFail {k value rest state S} : S.push available frame k (value state) = none →
      Counted available frame (.push k value rest) state S 1 (.outOfMemory S)
  | push {k value rest state S S' n result} : S.push available frame k (value state) = some S' →
      Counted available frame rest state S' n result →
      Counted available frame (.push k value rest) state S (1 + n) result
  | peekFail {k update rest state S} : S.peek frame k = none →
      Counted available frame (.peek k update rest) state S 1 (.invalid S)
  | peek {k update rest state S value n result} : S.peek frame k = some value →
      Counted available frame rest (update state value) S n result →
      Counted available frame (.peek k update rest) state S (1 + n) result
  | popFail {k update rest state S} : S.pop frame k = none →
      Counted available frame (.pop k update rest) state S 2 (.invalid S)
  | pop {k update rest state S S' value n result} : S.pop frame k = some (S', value) →
      Counted available frame rest (update state value) S' n result →
      Counted available frame (.pop k update rest) state S (2 + n) result
  | load {update rest state S n result} : Counted available frame rest (update state) S n result →
      Counted available frame (.load update rest) state S (1 + n) result
  | yes {guard yes no state S n result} : guard state = true →
      Counted available frame yes state S n result →
      Counted available frame (.branch guard yes no) state S (1 + n) result
  | no {guard yes no state S n result} : guard state = false →
      Counted available frame no state S n result →
      Counted available frame (.branch guard yes no) state S (1 + n) result
  | goto {destination state S} : Counted available frame (.goto destination) state S 1
      (.success ⟨some (destination state), state, S⟩)
  | halt {state S} : Counted available frame .halt state S 1 (.success ⟨none, state, S⟩)

theorem Counted.sound {code : Turing.TM2.Stmt Γ Λ σ} {available frame state S n result}
    (ht : Counted available frame code state S n result) : evaluate available frame code state S = result := by
  induction ht with
  | pushFail he => simp [evaluate, he]
  | push he _ ih => simpa [evaluate, he] using ih
  | peekFail he => simp [evaluate, he]
  | peek he _ ih => simpa [evaluate, he] using ih
  | popFail he => simp [evaluate, he]
  | pop he _ ih => simpa [evaluate, he] using ih
  | load _ ih => exact ih
  | yes he _ ih => simpa [evaluate, he] using ih
  | no he _ ih => simpa [evaluate, he] using ih
  | goto => rfl
  | halt => rfl

theorem Counted.exists (code : Turing.TM2.Stmt Γ Λ σ) (available : Bool) (frame : Frame)
    (state : σ) (S : Store Γ) :
    ∃ n, Counted available frame code state S n (evaluate available frame code state S) := by
  induction code generalizing state S with
  | push k value rest ih =>
    cases he : S.push available frame k (value state) with
    | none => exact ⟨1, by simpa [evaluate, he] using Counted.pushFail (rest := rest) he⟩
    | some S' =>
      obtain ⟨n, ht⟩ := ih state S'
      exact ⟨1 + n, by simpa [evaluate, he] using Counted.push he ht⟩
  | peek k update rest ih =>
    cases he : S.peek frame k with
    | none => exact ⟨1, by simpa [evaluate, he] using Counted.peekFail (update := update) (rest := rest) he⟩
    | some value =>
      obtain ⟨n, ht⟩ := ih (update state value) S
      exact ⟨1 + n, by simpa [evaluate, he] using Counted.peek he ht⟩
  | pop k update rest ih =>
    cases he : S.pop frame k with
    | none => exact ⟨2, by simpa [evaluate, he] using Counted.popFail (update := update) (rest := rest) he⟩
    | some pair =>
      obtain ⟨n, ht⟩ := ih (update state pair.2) pair.1
      exact ⟨2 + n, by simpa [evaluate, he] using Counted.pop he ht⟩
  | load update rest ih =>
    obtain ⟨n, ht⟩ := ih (update state) S
    exact ⟨1 + n, .load ht⟩
  | branch guard yes no ihYes ihNo =>
    cases he : guard state with
    | false =>
      obtain ⟨n, ht⟩ := ihNo state S
      exact ⟨1 + n, by simpa [evaluate, he] using Counted.no (yes := yes) he ht⟩
    | true =>
      obtain ⟨n, ht⟩ := ihYes state S
      exact ⟨1 + n, by simpa [evaluate, he] using Counted.yes (no := no) he ht⟩
  | goto destination => exact ⟨1, .goto⟩
  | halt => exact ⟨1, .halt⟩

theorem Counted.bound {code : Turing.TM2.Stmt Γ Λ σ} {available frame state S n result}
    (ht : Counted available frame code state S n result) : 0 < n ∧ n ≤ operationBound code := by
  induction ht <;> simp only [operationBound] <;> omega

/-- Every control pass finishes within a bound computed solely from its finite
statement tree, regardless of heap size, branch results or provider refusal. -/
theorem finite_pass_bound (code : Turing.TM2.Stmt Γ Λ σ) (available : Bool) (frame : Frame)
    (state : σ) (S : Store Γ) :
    ∃ n, Counted available frame code state S n (evaluate available frame code state S) ∧
      0 < n ∧ n ≤ operationBound code := by
  obtain ⟨n, ht⟩ := Counted.exists code available frame state S
  exact ⟨n, ht, ht.bound⟩

inductive Driven (program : Λ → Turing.TM2.Stmt Γ Λ σ) (available : Bool) (frame : Frame) :
    Nat → Configuration Γ Λ σ → Nat → RunResult Γ Λ σ → Prop where
  | halted {fuel C} : C.label = none → Driven program available frame fuel C 0 (.halted C)
  | exhausted {C label} : C.label = some label → Driven program available frame 0 C 0 (.exhausted C)
  | next {fuel C C' label consumed rest result} : C.label = some label →
      Counted available frame (program label) C.state C.storage consumed (.success C') →
      Driven program available frame fuel C' rest result →
      Driven program available frame (fuel + 1) C (consumed + rest) result
  | oom {fuel C label consumed S} : C.label = some label →
      Counted available frame (program label) C.state C.storage consumed (.outOfMemory S) →
      Driven program available frame (fuel + 1) C consumed (.outOfMemory S)
  | invalid {fuel C label consumed S} : C.label = some label →
      Counted available frame (program label) C.state C.storage consumed (.invalid S) →
      Driven program available frame (fuel + 1) C consumed (.invalid S)

theorem Driven.sound {program : Λ → Turing.TM2.Stmt Γ Λ σ} {available frame fuel C n result}
    (ht : Driven program available frame fuel C n result) : drive program available frame fuel C = result := by
  induction ht with
  | halted he => rw [drive, he]
  | exhausted he => rw [drive, he]
  | next he hc _ ih => rw [drive, he]; dsimp only; rw [hc.sound]; exact ih
  | oom he hc => rw [drive, he]; dsimp only; rw [hc.sound]
  | invalid he hc => rw [drive, he]; dsimp only; rw [hc.sound]

theorem Driven.exists (program : Λ → Turing.TM2.Stmt Γ Λ σ) (available : Bool) (frame : Frame)
    (fuel : Nat) (C : Configuration Γ Λ σ) :
    ∃ n, Driven program available frame fuel C n (drive program available frame fuel C) := by
  induction fuel generalizing C with
  | zero =>
    cases he : C.label with
    | none => exact ⟨0, by rw [drive, he]; exact Driven.halted he⟩
    | some label => exact ⟨0, by rw [drive, he]; exact Driven.exhausted he⟩
  | succ fuel ih =>
    cases hl : C.label with
    | none => exact ⟨0, by rw [drive, hl]; exact Driven.halted hl⟩
    | some label =>
      obtain ⟨n, hc⟩ := Counted.exists (program label) available frame C.state C.storage
      cases he : evaluate available frame (program label) C.state C.storage with
      | success C' =>
        obtain ⟨rest, ht⟩ := ih C'
        refine ⟨n + rest, ?_⟩
        rw [drive, hl]
        dsimp only
        rw [he]
        exact .next hl (by simpa only [he] using hc) ht
      | outOfMemory S =>
        refine ⟨n, ?_⟩
        rw [drive, hl]
        dsimp only
        rw [he]
        exact .oom hl (by simpa only [he] using hc)
      | invalid S =>
        refine ⟨n, ?_⟩
        rw [drive, hl]
        dsimp only
        rw [he]
        exact .invalid hl (by simpa only [he] using hc)

theorem Driven.bound {program : Λ → Turing.TM2.Stmt Γ Λ σ} {available frame fuel C n result}
    (ht : Driven program available frame fuel C n result) (bound : Nat)
    (hb : ∀ label, operationBound (program label) ≤ bound) : n ≤ fuel * bound := by
  induction ht with
  | halted => omega
  | exhausted => simp
  | @next fuel C C' label consumed rest result _ hc _ ih =>
    have hh := Nat.le_trans hc.bound.2 (hb label)
    rw [Nat.add_mul]
    omega
  | @oom fuel C label consumed S _ hc =>
    have hh := Nat.le_trans hc.bound.2 (hb label)
    rw [Nat.add_mul]
    omega
  | @invalid fuel C label consumed S _ hc =>
    have hh := Nat.le_trans hc.bound.2 (hb label)
    rw [Nat.add_mul]
    omega

/-- A conditional whole-run bound, covering normal halt, OOM and exhaustion.
It bounds only the operations performed during the supplied transition budget. -/
theorem drive_operation_bound (program : Λ → Turing.TM2.Stmt Γ Λ σ) (available : Bool) (frame : Frame)
    (fuel : Nat) (C : Configuration Γ Λ σ) (bound : Nat)
    (hb : ∀ label, operationBound (program label) ≤ bound) :
    ∃ n, Driven program available frame fuel C n (drive program available frame fuel C) ∧ n ≤ fuel * bound := by
  obtain ⟨n, ht⟩ := Driven.exists program available frame fuel C
  exact ⟨n, ht, ht.bound bound hb⟩

end Gabbro.Grammatik.Berechenbarkeit.Storage.TM2Heap
