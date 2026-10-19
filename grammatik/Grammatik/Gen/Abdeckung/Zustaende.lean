/-
  File:      Grammatik/Gen/Abdeckung/Zustaende.lean
  Subject:   The register members that are STATES, not program terms: the dynamic arena (`DynArena`: ceiling, commit
             floor, committed prefix) and the free-list state (`FreiZustand`: high-water mark, freed slots). They are
             enumerated completely up to a bound (every structure of the register with its proofs, built by deciding the
             proof arguments), so the register members they carry are covered by an enumeration of their own and the
             coverage report names them as such.
-/
import Grammatik.Bausteine.Arena.ArenaDyn

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.ArenaDyn

/-- All sublists. -/
def teilmengen {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: as => teilmengen as ++ (teilmengen as).map (a :: ·)

/-- Every dynamic arena with ceiling at most `m`. -/
def dynZustaende (m : Nat) : List DynArena :=
  (List.range (m + 1)).flatMap fun M => (List.range (M + 1)).flatMap fun c => (List.range (c + 1)).filterMap fun hi =>
    if h : hi ≤ c ∧ c ≤ M ∧ 0 < M then some ⟨M, hi, c, h.1, h.2.1, h.2.2⟩ else none

/-- Every free-list state with high-water mark at most `m` and a free list of distinct slots below it. -/
def freiZustaende (m : Nat) : List FreiZustand :=
  (List.range (m + 1)).flatMap fun b => (teilmengen (List.range b)).filterMap fun fr =>
    if h : ∀ i ∈ fr, i < b then some ⟨b, fr, h⟩ else none

/-- The dynamic arenas of ceiling at most 3: 19 of them. -/
theorem dynZustaende_zahl : (dynZustaende 3).length = 19 := by decide

/-- The free-list states with a high-water mark of at most 3: every subset of the slots below it. -/
theorem freiZustaende_zahl : (freiZustaende 3).length = 15 := by decide

end Gabbro.Grammatik.Gen
