/- Construction of separated sums with the common constant and payload emitters. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Sum.Model
public import Stage0.Senke.Ausdruck.Aggregat.Hilfen
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- The header is materialized before the payload so constant scratch cannot
    overwrite payload limbs. Every unused payload word is explicitly zeroed. -/
def sumSpanL (cs : List (Option Ty)) (i : Fin cs.length) (d : Nat)
    (payload : Option (List II × Nat)) : Option (List II × Nat) := do
  let child ← payload
  let header := constWords (integerEncoding (integerWords 0 (cs.length - 1)) i.val) d
  let zeros := constWords (List.replicate (sumPayloadWords cs - payloadWords (cs.get i)) 0)
    (d + integerWords 0 (cs.length - 1) + payloadWords (cs.get i))
  pure (header.1 ++ child.1 ++ zeros.1,
    max (max header.2 child.2) (max zeros.2 (d + valueWords (.sum cs))))

theorem sumSpanL_top {cs : List (Option Ty)} {i : Fin cs.length} {d top : Nat}
    {payload : Option (List II × Nat)} {c : List II}
    (made : sumSpanL cs i d payload = some (c, top)) : d < top := by
  simp only [sumSpanL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq, Prod.mk.injEq] at made
  obtain ⟨child, _, _, rfl⟩ := made
  have positive := valueWords_pos (.sum cs)
  omega

/-- Zero padding does not need a scratch limb beyond its own span. -/
theorem constZeros_top (n d : Nat) : (constWords (List.replicate n 0) d).2 = d + n := by
  induction n generalizing d with
  | zero => simp [constWords]
  | succ n ih =>
    simp only [List.replicate_succ, constWords, ih]
    simp [wordConst, lit32, Nat.max_eq_right (by omega : d + 1 ≤ d + 1 + n)] <;> omega

/-- A bare payload and a typed payload use exactly the same construction kernel. -/
theorem sumSpanL_span {cs : List (Option Ty)} {i : Fin cs.length} {d top : Nat}
    {payload : Option (List II × Nat)} {c : List II}
    (made : sumSpanL cs i d payload = some (c, top)) : d + valueWords (.sum cs) ≤ top := by
  simp only [sumSpanL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq, Prod.mk.injEq] at made
  obtain ⟨child, _, _, rfl⟩ := made
  omega

/-- Test a separated tag above the complete input span, preserving all payload words. -/
def sumSpanTestC (s scratch k : Nat) : List II :=
  [ci 2 scratch s 0, ci 1 (scratch + 1) k 0, ci 14 scratch scratch (scratch + 1)]

/-- Selected payloads move forward into the binder's ordinary context span. -/
def sumSpanPayloadC (s : Nat) (c : Option Ty) : List II :=
  copyWords (payloadWords c) s (s + 1)

end Gabbro.Stage0.Senke
