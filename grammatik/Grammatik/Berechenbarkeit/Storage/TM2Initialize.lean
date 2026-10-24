import Grammatik.Berechenbarkeit.Storage.TM2Execution

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.TM2Heap

open ArenaOwnership (Frame)

variable {K : Type} {Γ : K → Type} [DecidableEq K]

inductive LoadResult (Γ : K → Type) where
  | loaded (storage : Store Γ)
  | outOfMemory (storage : Store Γ)

/-- Load from a finite external input by allocating real linked cells, tail first.
Failure is explicit; it does not supply an abstract pre-populated stack. -/
def Store.load (available : Bool) (frame : Frame) (k : K) : List (Γ k) → Store Γ → LoadResult Γ
  | [], S => .loaded S
  | value :: rest, S =>
    match Store.load available frame k rest S with
    | .outOfMemory S' => .outOfMemory S'
    | .loaded S' =>
      match S'.push available frame k value with
      | none => .outOfMemory S'
      | some S'' => .loaded S''

theorem Store.load_correct (frame : Frame) (k : K) (input : List (Γ k))
    (S : Store Γ) (values : ∀ k, List (Γ k)) (hr : S.Represents frame values) :
    ∃ S', S.load true frame k input = .loaded S' ∧
      S'.Represents frame (Function.update values k (input ++ values k)) := by
  induction input generalizing S values with
  | nil =>
    exact ⟨S, rfl, by simpa using hr⟩
  | cons value rest ih =>
    obtain ⟨S', he, hr'⟩ := ih S values hr
    obtain ⟨S'', hp, hr''⟩ := Store.push_correct hr' k value
    exact ⟨S'', by simp [Store.load, he, hp], by simpa using hr''⟩

def LoadResult.Compatible (result : LoadResult Γ) (frame : Frame) (values : ∀ k, List (Γ k)) : Prop :=
  match result with
  | .loaded S => S.Represents frame values
  | .outOfMemory S => ∃ valuesSoFar, S.Represents frame valuesSoFar

theorem Store.load_safe (available : Bool) (frame : Frame) (k : K) (input : List (Γ k))
    (S : Store Γ) (values : ∀ k, List (Γ k)) (hr : S.Represents frame values) :
    (S.load available frame k input).Compatible frame (Function.update values k (input ++ values k)) := by
  induction input generalizing S values with
  | nil => simpa [Store.load, LoadResult.Compatible] using hr
  | cons value rest ih =>
    have hi := ih S values hr
    cases hl : S.load available frame k rest with
    | outOfMemory S' => simpa [Store.load, hl, LoadResult.Compatible] using hi
    | loaded S' =>
      have hr' : S'.Represents frame (Function.update values k (rest ++ values k)) := by
        simpa [hl, LoadResult.Compatible] using hi
      cases hp : S'.push available frame k value with
      | none =>
        simpa [Store.load, hl, hp, LoadResult.Compatible] using Exists.intro _ hr'
      | some S'' =>
        have hr'' := Store.push_spec hr' k value hp
        simpa [Store.load, hl, hp, LoadResult.Compatible] using hr''

def loadInput (machine : Turing.FinTM2) (available : Bool) (frame : Frame)
    (input : List (machine.Γ machine.k₀)) : Outcome machine.Γ machine.Λ machine.σ :=
  match (Store.empty : Store machine.Γ).load available frame machine.k₀ input with
  | .loaded S => .success ⟨some machine.main, machine.initialState, S⟩
  | .outOfMemory S => .outOfMemory S

theorem loadInput_correct (machine : Turing.FinTM2) (frame : Frame)
    (input : List (machine.Γ machine.k₀)) :
    ∃ C, loadInput machine true frame input = .success C ∧
      C.Represents frame (Turing.initList machine input) := by
  obtain ⟨S, he, hr⟩ := Store.load_correct frame machine.k₀ input
    (Store.empty : Store machine.Γ) (fun _ => []) (Store.empty_represents frame)
  refine ⟨⟨some machine.main, machine.initialState, S⟩, by simp [loadInput, he], rfl, rfl, ?_⟩
  have hvalues : Function.update (fun k => ([] : List (machine.Γ k))) machine.k₀ input =
      (Turing.initList machine input).stk := by
    funext k
    by_cases hk : k = machine.k₀
    · subst k; simp [Turing.initList]
    · simp [Turing.initList, hk]
  simpa only [List.append_nil, hvalues] using hr

theorem loadInput_safe (machine : Turing.FinTM2) (available : Bool) (frame : Frame)
    (input : List (machine.Γ machine.k₀)) :
    (loadInput machine available frame input).Compatible frame (Turing.initList machine input) := by
  have hh := Store.load_safe available frame machine.k₀ input (Store.empty : Store machine.Γ)
    (fun _ => []) (Store.empty_represents frame)
  cases hl : (Store.empty : Store machine.Γ).load available frame machine.k₀ input with
  | outOfMemory S => simpa [loadInput, hl, Outcome.Compatible, LoadResult.Compatible] using hh
  | loaded S =>
    have hr : S.Represents frame (Function.update (fun k => ([] : List (machine.Γ k))) machine.k₀ input) := by
      simpa [hl, LoadResult.Compatible] using hh
    have hvalues : Function.update (fun k => ([] : List (machine.Γ k))) machine.k₀ input =
        (Turing.initList machine input).stk := by
      funext k
      by_cases hk : k = machine.k₀
      · subst k; simp [Turing.initList]
      · simp [Turing.initList, hk]
    rw [hvalues] at hr
    simp only [loadInput, hl, Outcome.Compatible]
    exact ⟨rfl, rfl, hr⟩

end Gabbro.Grammatik.Berechenbarkeit.Storage.TM2Heap
