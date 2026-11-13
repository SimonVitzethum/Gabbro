module
public import Lean
@[expose] public section

namespace Gabbro.Body

/-- Finite iteration with explicit continuation or terminal outcome. The callback is the
    existing Body block semantics; no source syntax or external environment is interpreted. -/
def traverseRun {S O : Type} (body : S → Sum S O) (finish : S → O)
    (bindIndex : S → Int → S) : List Int → S → O
  | [], s => finish s
  | i :: is, s =>
      match body (bindIndex s i) with
      | .inl s' => traverseRun body finish bindIndex is s'
      | .inr out => out

/-- Test before every pass, including after the last permitted pass. Exhaustion executes
    the explicit handler in the current state. The bound counts passes, never tests. -/
def retryRun {S O : Type} (test : S → Option Bool) (body : S → Sum S O)
    (finish exceeded : S → O) (stuck : O) : Nat → S → O
  | 0, s =>
      match test s with
      | some true => finish s
      | some false => exceeded s
      | none => stuck
  | n + 1, s =>
      match test s with
      | some true => finish s
      | some false =>
          match body s with
          | .inl s' => retryRun test body finish exceeded stuck n s'
          | .inr out => out
      | none => stuck

end Gabbro.Body
