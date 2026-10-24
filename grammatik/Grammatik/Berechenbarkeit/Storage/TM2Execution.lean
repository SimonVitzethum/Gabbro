import Grammatik.Berechenbarkeit.Storage.TM2Heap

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.TM2Heap

open ArenaOwnership (Frame)

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

structure Configuration (Γ : K → Type) (Λ σ : Type) where
  label : Option Λ
  state : σ
  storage : Store Γ

inductive Outcome (Γ : K → Type) (Λ σ : Type) where
  | success (configuration : Configuration Γ Λ σ)
  | outOfMemory (storage : Store Γ)
  | invalid (storage : Store Γ)

/-- One finite TM2 statement tree. Every stack access is a linked-cell operation;
allocation refusal is distinct from normal halt and invalid rights. -/
def evaluate (available : Bool) (frame : Frame) :
    Turing.TM2.Stmt Γ Λ σ → σ → Store Γ → Outcome Γ Λ σ
  | .push k value rest, state, S =>
    match S.push available frame k (value state) with
    | none => .outOfMemory S
    | some S' => evaluate available frame rest state S'
  | .peek k update rest, state, S =>
    match S.peek frame k with
    | none => .invalid S
    | some value => evaluate available frame rest (update state value) S
  | .pop k update rest, state, S =>
    match S.pop frame k with
    | none => .invalid S
    | some (S', value) => evaluate available frame rest (update state value) S'
  | .load update rest, state, S => evaluate available frame rest (update state) S
  | .branch guard yes no, state, S =>
    if guard state then evaluate available frame yes state S else evaluate available frame no state S
  | .goto destination, state, S => .success ⟨some (destination state), state, S⟩
  | .halt, state, S => .success ⟨none, state, S⟩

/-- With successful provider answers, every TM2 operation has an executable,
memory-safe realisation in the new storage component. No stack oracle is used. -/
theorem evaluate_correct (code : Turing.TM2.Stmt Γ Λ σ) (frame : Frame)
    (state : σ) (S : Store Γ) (values : ∀ k, List (Γ k)) (hr : S.Represents frame values) :
    ∃ S', evaluate true frame code state S = .success
        ⟨(Turing.TM2.stepAux code state values).l, (Turing.TM2.stepAux code state values).var, S'⟩ ∧
      S'.Represents frame (Turing.TM2.stepAux code state values).stk := by
  induction code generalizing state S values with
  | push k value rest ih =>
    obtain ⟨S', he, hr'⟩ := Store.push_correct hr k (value state)
    obtain ⟨S'', hrun, hrep⟩ := ih state S' _ hr'
    exact ⟨S'', by simpa [evaluate, he] using hrun, hrep⟩
  | peek k update rest ih =>
    have he := Store.peek_correct hr k
    obtain ⟨S', hrun, hrep⟩ := ih (update state (values k).head?) S values hr
    exact ⟨S', by simpa [evaluate, he] using hrun, hrep⟩
  | pop k update rest ih =>
    obtain ⟨S', he, hr'⟩ := Store.pop_correct hr k
    obtain ⟨S'', hrun, hrep⟩ := ih (update state (values k).head?) S' _ hr'
    exact ⟨S'', by simpa [evaluate, he] using hrun, hrep⟩
  | load update rest ih => exact ih (update state) S values hr
  | branch guard yes no ihYes ihNo =>
    cases he : guard state with
    | false => simpa [evaluate, he] using ihNo state S values hr
    | true => simpa [evaluate, he] using ihYes state S values hr
  | goto destination => exact ⟨S, rfl, hr⟩
  | halt => exact ⟨S, rfl, hr⟩

def Configuration.Represents (C : Configuration Γ Λ σ) (frame : Frame) (c : Turing.TM2.Cfg Γ Λ σ) : Prop :=
  C.label = c.l ∧ C.state = c.var ∧ C.storage.Represents frame c.stk

/-- OOM may expose only a safe intermediate storage state. It is not a normal
completion of the simulated instruction. Invalid references are excluded. -/
def Outcome.Compatible (result : Outcome Γ Λ σ) (frame : Frame) (c : Turing.TM2.Cfg Γ Λ σ) : Prop :=
  match result with
  | .success C => C.Represents frame c
  | .outOfMemory S => ∃ values, S.Represents frame values
  | .invalid _ => False

theorem evaluate_safe (code : Turing.TM2.Stmt Γ Λ σ) (available : Bool) (frame : Frame)
    (state : σ) (S : Store Γ) (values : ∀ k, List (Γ k)) (hr : S.Represents frame values) :
    (evaluate available frame code state S).Compatible frame (Turing.TM2.stepAux code state values) := by
  induction code generalizing state S values with
  | push k value rest ih =>
    cases he : S.push available frame k (value state) with
    | none => exact (by simpa [evaluate, he, Outcome.Compatible] using Exists.intro values hr)
    | some S' =>
      have hr' := Store.push_spec hr k (value state) he
      simpa [evaluate, he] using ih state S' _ hr'
  | peek k update rest ih =>
    have he := Store.peek_correct hr k
    simpa [evaluate, he] using ih (update state (values k).head?) S values hr
  | pop k update rest ih =>
    obtain ⟨S', he, hr'⟩ := Store.pop_correct hr k
    simpa [evaluate, he] using ih (update state (values k).head?) S' _ hr'
  | load update rest ih => exact ih (update state) S values hr
  | branch guard yes no ihYes ihNo =>
    cases he : guard state with
    | false => simpa [evaluate, he] using ihNo state S values hr
    | true => simpa [evaluate, he] using ihYes state S values hr
  | goto destination => exact ⟨rfl, rfl, hr⟩
  | halt => exact ⟨rfl, rfl, hr⟩

def step (program : Λ → Turing.TM2.Stmt Γ Λ σ) (available : Bool) (frame : Frame)
    (C : Configuration Γ Λ σ) : Option (Outcome Γ Λ σ) :=
  C.label.map (fun label => evaluate available frame (program label) C.state C.storage)

theorem step_correct (program : Λ → Turing.TM2.Stmt Γ Λ σ) (frame : Frame)
    {C : Configuration Γ Λ σ} {c c' : Turing.TM2.Cfg Γ Λ σ}
    (hr : C.Represents frame c) (he : Turing.TM2.step program c = some c') :
    ∃ C', step program true frame C = some (.success C') ∧ C'.Represents frame c' := by
  rcases C with ⟨label, state, S⟩
  rcases c with ⟨sourceLabel, sourceState, values⟩
  obtain ⟨rfl, rfl, hr⟩ := hr
  cases label with
  | none => cases he
  | some label =>
    cases he
    obtain ⟨S', hrun, hrep⟩ := evaluate_correct (program label) frame state S values hr
    exact ⟨⟨(Turing.TM2.stepAux (program label) state values).l,
      (Turing.TM2.stepAux (program label) state values).var, S'⟩,
      by simpa [step] using congrArg some hrun, rfl, rfl, hrep⟩

end Gabbro.Grammatik.Berechenbarkeit.Storage.TM2Heap
