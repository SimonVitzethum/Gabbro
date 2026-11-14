/- The freestanding contention edge executes two instructions and preserves all
   memory, including the ticket in slot two. No kernel premise is needed. -/
module
public import Stage0.Senke.Sperre.Warten.Retry
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration}

/-- Failed serving comparison: branch to the binding, then retry the serving
    read. Both steps keep the complete state, not only the abstract lock. -/
theorem nimmT_spin_retry {L : Lay D} {m0 m : Mem} {pc fp : W}
    {s a p : Nat} {code : List II} {f : Nat → W} {n u w : W}
    (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f n u w)
    (hc : At code p (nimmT L a s)) (binding : L.lockWait = .spin)
    (compared : f 6 = bool (f 5 == f 2)) (waiting : f 2 ≠ f 5) :
    Star ⟨pc + BitVec.ofNat 64 (16 * (p + 10)), fp⟩ m
      ⟨pc + BitVec.ofNat 64 (16 * (p + 7)), fp⟩ m := by
  have branch := ls_brz_zero E h (hc.get (j := 10) rfl) (e := 6) (k := 2)
    rfl rfl (by omega) (by omega)
    (by rw [compared]; exact bool_ne (Ne.symm waiting))
  have entry : code[p + 12]? = some (ci 18 (-80) 0 0) := by
    have cell := hc.get (j := 12) (by simp [nimmT, binding, waitEntry])
    exact cell
  have retry := ls_jmp_back E h.ag (i := p + 7) (k := 5)
    (by simpa only [Nat.add_assoc] using entry) rfl (by decide)
  exact branch.trans retry

end Gabbro.Stage0.Senke
