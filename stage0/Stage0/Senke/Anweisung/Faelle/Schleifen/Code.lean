/- Bounded retry uses finite control flow: no hidden counter can collide with a body or callee frame.
   Each check precedes its attempt; the final check precedes the overflow block. Code size is linear in
   the bound. Leave skips all remaining attempts; next and fallthrough reach the following check. -/
import Stage0.Senke.Ausdruck

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Move a contiguous live range upward, including overlapping ranges. -/
def relocateC (base shift : Nat) : Nat → List II
  | 0 => []
  | n + 1 => [ci 2 (base + shift + n) (base + n) 0] ++ relocateC base shift n

@[simp] theorem relocateC_length (base shift n : Nat) :
    (relocateC base shift n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [relocateC, ih]

/-- A true condition skips the remaining code; false enters it. -/
def retryTest (s : Nat) (cc rest : List II) : List II :=
  cc ++ [ci 19 s 32 0] ++ [ci 18 (16 * (rest.length + 1)) 0 0] ++ rest

/-- Unroll a static bound, lowering each body against its own leave/next targets.
    Overflow retains the enclosing loop's targets. The usual image-size gate bounds all jumps. -/
def retryC (s : Nat) (cc overflow : List II × Nat)
    (body : Int × Int → Option (List II × Nat)) : Nat → Option (List II × Nat)
  | 0 => some (retryTest s cc.1 overflow.1, max cc.2 overflow.2)
  | n + 1 => do
    let rest ← retryC s cc overflow body n
    let cb ← body (16 * rest.1.length, 0)
    pure (retryTest s cc.1 (cb.1 ++ rest.1), max cc.2 (max cb.2 rest.2))

end Gabbro.Stage0.Senke
