/- Assembly, relocation and size evidence for consuming emission.
   The instruction paths are composed in Consuming.Execution. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Code
public section

namespace Gabbro.Stage0.Senke.Consuming
open Gabbro.Grammatik Runner.IR

/-- Successful assembly bounds every local jump displacement in magnitude:
    both its origin and destination are instruction positions in the image. -/
theorem assemble_size {fragment : List Piece} {code : List II}
    (h : assemble fragment = some code) : 16 * code.length < 2 ^ 31 := by
  unfold assemble at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨instructions, encoded, h⟩ := h
  split at h
  · next size =>
    simp only [Option.some.injEq] at h
    subst code
    exact size
  · cases h

/-- Resolving body targets depends only on the probe's length. Recompilation
    with actual targets cannot silently shift any following label. -/
theorem targets_same_length (s counter saved fuel failure : Nat) (count bound : Int)
    (invariant member edge measure probe actual : List II)
    (same : actual.length = probe.length) :
    targets (pieces s counter saved fuel failure count bound
      invariant member edge measure actual) =
    targets (pieces s counter saved fuel failure count bound
      invariant member edge measure probe) := by
  simp [targets, pieces, position, Piece.width, same]

/-- The emitted body really is a candidate produced with its own resolved
    targets. This is the evidence required by the structural body hypothesis;
    a probe compiled with zero targets is never substituted for it. -/
theorem emit_actual {s counter saved fuel failure : Nat} {count bound : Int}
    {invariant member edge measure : List II × Nat}
    {body : Int × Int → Option (List II × Nat)} {code : List II} {top : Nat}
    (h : emit s counter saved fuel failure count bound
      invariant member edge measure body = some (code, top)) :
    ∃ (actual : List II × Nat) (exits : Int × Int),
      body exits = some actual ∧
      targets (pieces s counter saved fuel failure count bound
        invariant.1 member.1 edge.1 measure.1 actual.1) = some exits ∧
      assemble (pieces s counter saved fuel failure count bound
        invariant.1 member.1 edge.1 measure.1 actual.1) = some code ∧
      invariant.2 ≤ top ∧ member.2 ≤ top ∧ edge.2 ≤ top ∧
      measure.2 ≤ top ∧ actual.2 ≤ top ∧ counter + 1 ≤ top ∧ saved + 1 ≤ top ∧
      s + 12 ≤ top := by
  unfold emit at h
  split at h
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨probe, probeCode, exits, exitCode, actual, actualCode, h⟩ := h
    split at h
    · next same =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨instructions, assembled, output⟩ := h
      simp only [Prod.mk.injEq] at output
      obtain ⟨rfl, rfl⟩ := output
      refine ⟨actual, exits, actualCode, ?_, assembled, ?_⟩
      · rw [targets_same_length s counter saved fuel failure count bound
          invariant.1 member.1 edge.1 measure.1 probe.1 actual.1 same]
        exact exitCode
      · omega
    · cases h
  · cases h

/-- The public emission result inherits the assembler's actual image gate. -/
theorem emit_size {s counter saved fuel failure : Nat} {count bound : Int}
    {invariant member edge measure : List II × Nat}
    {body : Int × Int → Option (List II × Nat)} {code : List II} {top : Nat}
    (h : emit s counter saved fuel failure count bound
      invariant member edge measure body = some (code, top)) :
    16 * code.length < 2 ^ 31 := by
  obtain ⟨actual, exits, bodyCode, exitCode, assembled, bounds⟩ := emit_actual h
  exact assemble_size assembled

/-- Every successful candidate carries the bounded fuel and operand domain
    checks needed by the concrete signed comparisons. -/
theorem emit_bounds {s counter saved fuel failure : Nat} {count bound : Int}
    {invariant member edge measure : List II × Nat}
    {body : Int × Int → Option (List II × Nat)} {code : List II} {top : Nat}
    (h : emit s counter saved fuel failure count bound
      invariant member edge measure body = some (code, top)) :
    fuel < 2 ^ 31 ∧ failure < 2 ^ 31 ∧
      inW count count = true ∧ inW 0 bound = true := by
  unfold emit at h
  split at h
  · assumption
  · cases h

/-- Oversized fuel is refused before even requesting a body candidate. -/
theorem emit_refuses_fuel (s counter saved fuel failure : Nat) (count bound : Int)
    (invariant member edge measure : List II × Nat)
    (body : Int × Int → Option (List II × Nat)) (large : 2 ^ 31 ≤ fuel) :
    emit s counter saved fuel failure count bound
      invariant member edge measure body = none := by
  unfold emit
  split
  · omega
  · rfl

end Gabbro.Stage0.Senke.Consuming
