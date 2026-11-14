/- Constant-size retry and forever control with source-derived reserved counters. -/
module
public import Stage0.Senke.Ausdruck
public import Stage0.Senke.Stopp
@[expose] public section


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
  cc ++ ([ci 19 s 32 0] ++ ([ci 18 (16 * (rest.length + 1)) 0 0] ++ rest))

/-- Constant-size control, independent of the runtime budget. The zero branch
enters the caller-supplied budget stop; a positive budget is decremented using
an immutable slot containing one. -/
def foreverCounter (counter one : Nat) (stop : Int) : List II :=
  [ci 19 counter stop 0, ci 4 counter counter one]

def foreverCounterInit (counter : Nat) (budget : Int) : List II :=
  [ci 1 counter budget 0]

/-- Targets relative to the end of the single retry body. Fallthrough executes
    the backedge; next jumps to the condition, and leave skips the overrun. -/
def retryTargets (condition body overflow : Nat) : Int × Int :=
  (16 * (overflow + 1), -(16 * (condition + body + 4 : Nat) : Int))

/-- One condition, one body and one overrun block. The condition precedes the
    fuel test even at zero, exactly as in `retryLauf`. -/
def retryHeader (counter one scratch : Nat) (cc cb cu : List II) : List II :=
  retryTest scratch cc
    (foreverCounter counter one (16 * (cb.length + 3)) ++ (cb ++
      ([ci 18 (-(16 * (cc.length + cb.length + 4 : Nat) : Int)) 0 0] ++ cu)))

def retryCode (counter one scratch budget : Nat) (cc cb cu : List II) : List II :=
  foreverCounterInit counter budget ++ [ci 1 one 1 0] ++
    retryHeader counter one scratch cc cb cu

/-- Measure a body once, lower it at its real targets, then check that length
    is stable. Neither compilation nor the emitted image recurses on fuel. -/
def retryC (counter one scratch budget : Nat) (condition overflow : List II × Nat)
    (body : Int × Int → Option (List II × Nat)) : Option (List II × Nat) := do
  if budget < 2 ^ 31 then
    let probe ← body (0, 0)
    let actual ← body (retryTargets condition.1.length probe.1.length overflow.1.length)
    if actual.1.length = probe.1.length ∧
        16 * (condition.1.length + actual.1.length + overflow.1.length + 7) < 2 ^ 31 then
      pure (retryCode counter one scratch budget condition.1 actual.1 overflow.1,
        max condition.2 (max actual.2 (max overflow.2
          (max (counter + 1) (max (one + 1) (scratch + 1))))))
    else none
  else none

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
