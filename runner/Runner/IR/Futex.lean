import Runner.IR.Seq

/-! Named OS behavior for the runner's existing futex requests. This is a
binding premise, never a hardware assumption or a Lean kernel postulate.
`Kern.ans` may include memory changes by other threads while WAIT is pending;
clients must supply their own frame/interference invariant for those changes.
No scheduling, eventual return, eventual acquisition or fairness is assumed. -/
namespace Runner.IR

/-- Linux private futex requests used by the actual Stage-0 lock emitter.
    WAIT compares only the low 32 bits, even though the owner occupies 64 bits. -/
def futexReq (a op v : W) : Req := ⟨202, a, op, v, 0, 0, 0⟩

/-- The explicit classification of a WAIT completion. A spurious completion
    includes interruptions and mismatch/error returns, which the lock retries.
    A word changed back before return is classified as spurious here; there
    is no syscall history in the sequential runner relation. -/
class FutexOK (spurious : W → W → Mem → Mem → Prop) [Kern] : Prop where
  wait_return : ∀ a v m r x m',
    Kern.ans (futexReq a 128 v) m (some (r, x)) m' →
    (∃ observed, m'.rd32 a = some observed ∧ observed ≠ v.setWidth 32) ∨ spurious a v m m'
  /-- A successful WAKE reports at most the requested number woken; negative
      error returns are allowed. The count says nothing about who runs next. -/
  wake_return : ∀ a n m r x m',
    Kern.ans (futexReq a 129 n) m (some (r, x)) m' → 0 ≤ r.toInt → r.toNat ≤ n.toNat

/-- The class is inhabited without adding assumptions about progress or writes.
    This test kernel admits spurious WAIT and zero-waiter WAKE, preserving memory. -/
abbrev futexKernel : Kern where
  ans q m ans m' := m' = m ∧ ∃ a v, (q = futexReq a 128 v ∨ q = futexReq a 129 v) ∧ ans = some (0, 0)

theorem futexOK_zeuge : @FutexOK (fun _ _ _ _ => True) futexKernel := by
  letI : Kern := futexKernel
  refine ⟨?_, ?_⟩
  · intro a v m r x m' _; exact Or.inr trivial
  · intro a n m r x m' h _
    obtain ⟨_, _, _, _, he⟩ := h
    cases he
    exact Nat.zero_le _

end Runner.IR
