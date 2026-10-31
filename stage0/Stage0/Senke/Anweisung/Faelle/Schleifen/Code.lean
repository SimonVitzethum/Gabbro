/- Shared retry, reserved-counter and constant-size forever code.
   Bounded retry uses finite control flow: no hidden counter can collide with a body or callee frame.
   Each check precedes its attempt; the final check precedes the overflow block. Code size is linear in
   the bound. Leave skips all remaining attempts; next and fallthrough reach the following check. -/
import Stage0.Senke.Ausdruck
import Stage0.Senke.Stopp

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

/-- Constant-size control, independent of the runtime budget. The zero branch
enters the caller-supplied budget stop; a positive budget is decremented using
an immutable slot containing one. -/
def foreverCounter (counter one : Nat) (stop : Int) : List II :=
  [ci 19 counter stop 0, ci 4 counter counter one]

def foreverCounterInit (counter : Nat) (budget : Int) : List II :=
  [ci 1 counter budget 0]

/-- Body exits relative to the end of the body. Leave skips both stops and the
    backedge; next jumps directly to the counter header. -/
def foreverTargets (invariant body : Nat) : Int × Int :=
  (128, -(16 * (invariant + body + 3 : Nat) : Int))

/-- The header starts after the two initialization instructions. False invariants
    stop with 104; exhausted fuel stops with 111 before evaluating the invariant. -/
def foreverCode (counter one scratch budget : Nat) (cc cb : List II) : List II :=
  foreverCounterInit counter budget ++ [ci 1 one 1 0] ++
    foreverCounter counter one (16 * (cc.length + cb.length + 8)) ++
    cc ++ [ci 19 scratch (16 * (cb.length + 2)) 0] ++ cb ++
    [ci 18 64 0 0] ++ stopC 104 scratch ++
    [ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0] ++
    stopC 111 scratch

/-- Signed instruction immediates bound the semantic budget more tightly than
    the runtime counter word. Check before invoking the body candidate producer.
    The first candidate measures length only; the second uses actual targets.
    Refuse if its length changes, rather than trusting a relocation assumption. -/
def foreverC (counter one scratch budget : Nat) (inv : List II × Nat)
    (body : Int × Int → Option (List II × Nat)) : Option (List II × Nat) := do
  if budget < 2 ^ 31 then
    let probe ← body (0, 0)
    let actual ← body (foreverTargets inv.1.length probe.1.length)
    if actual.1.length = probe.1.length then
      pure (foreverCode counter one scratch budget inv.1 actual.1,
        max inv.2 (max actual.2 (max (counter + 1) (max (one + 1) (scratch + 8)))))
    else none
  else none

end Gabbro.Stage0.Senke
