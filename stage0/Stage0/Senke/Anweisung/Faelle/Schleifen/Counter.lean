/- A protected runtime counter uses an explicitly reserved frame slot, never slot 3
(the entry snapshot). The body and callees must stay below this reservation before
this fragment can replace the current refusal of forever. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Code

namespace Gabbro.Stage0.Senke
open Runner Runner.IR

/-- Constant-size control, independent of the runtime budget. The zero branch
enters the caller-supplied budget stop; a positive budget is decremented using
an immutable slot containing one. -/
def foreverCounter (counter one : Nat) (stop : Int) : List II :=
  [ci 19 counter stop 0, ci 4 counter counter one]

def foreverCounterInit (counter : Nat) (budget : Int) : List II :=
  [ci 1 counter budget 0]

section
variable [Kern]

theorem counter_init {t : T} {m m' : Mem} {d k c : BitVec 32}
    (hi : InsAt m t.pc 1 d k c)
    (hw : m.wr64 (slot t.fp (sx d)) (sx k) = some m') :
    Run (step t) m (nxt t) m' := by
  apply run_step hi (by decide)
  exact f2_run hi (f1_run hi (run_wr64 hw))

theorem counter_zero {t : T} {m : Mem} {d jump c : BitVec 32}
    (hi : InsAt m t.pc 19 d jump c)
    (hz : m.rd64 (slot t.fp (sx d)) = some 0) :
    Run (step t) m {t with pc := t.pc + sx jump} m :=
  run_step hi (by decide) (run_brz_zero hi hz)

theorem counter_positive {t : T} {m : Mem} {d jump c : BitVec 32} {v : W}
    (hi : InsAt m t.pc 19 d jump c)
    (hv : m.rd64 (slot t.fp (sx d)) = some v) (hne : v ≠ 0) :
    Run (step t) m (nxt t) m :=
  run_step hi (by decide) (run_brz_ne hi hv hne)

theorem counter_decrement {t : T} {m m' : Mem} {d one : BitVec 32} {v : W}
    (hi : InsAt m t.pc 4 d d one)
    (hv : m.rd64 (slot t.fp (sx d)) = some v)
    (h1 : m.rd64 (slot t.fp (sx one)) = some 1)
    (hw : m.wr64 (slot t.fp (sx d)) (v - 1) = some m') :
    Run (step t) m (nxt t) m' := by
  apply run_step hi (by decide)
  exact run_bin hi hv h1 rfl hw
end

/-- Reserving [counter,counter+1) preserves every other byte and permissions. -/
theorem counter_protected {m : Mem} {fp : W} {counter : Nat}
    (room : fp.toNat + 8 * (counter + 1) ≤ 2 ^ 64) (v : Nat) :
    Agree fp counter (counter + 1) m
      (Mem.write m (slot fp (BitVec.ofNat 64 counter)) 8 v) :=
  agree_write room (by omega) (by omega) v

theorem counter_decrement_zeuge : (3 : W) - 1 = 2 ∧ (3 : W) ≠ 0 ∧
    (foreverCounter 12 13 64).length = 2 := by decide

/-- A nonempty reservation above the ABI and ordinary variable slots. -/
theorem counter_protected_zeuge (m : Mem) :
    Agree 0 12 13 m (Mem.write m (slot 0 (BitVec.ofNat 64 12)) 8 2) ∧
    (3 : W) - 1 = 2 ∧ (foreverCounter 12 13 64).length = 2 := by
  exact ⟨counter_protected (by decide) 2, by decide, by decide⟩

end Gabbro.Stage0.Senke
