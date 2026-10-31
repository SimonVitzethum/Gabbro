/- Counter and immutable decrement word occupy the reserved frame prefix.
   Lexical locals and callee frames start above that prefix. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Code
import Stage0.Senke.Rueckkehr

namespace Gabbro.Stage0.Senke
open Runner Runner.IR

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

/-- The existing statement/call frame contract protects a reserved counter below
its writable suffix, including world writes. This is an interface lemma: lowering
must still establish the reservation bound for the body and every callee. -/
theorem counter_preserved [Kern] {D : Gabbro.Grammatik.Deklaration} {L : Lay D}
    {fp : W} {Ks K d counter : Nat} {m m' : Mem}
    (layout : WIn L fp Ks K) (frame : AgreeW L fp d K m m')
    (reserved : counter < d) (bound : d ≤ K) :
    m'.rd64 (slot fp (BitVec.ofNat 64 counter)) =
      m.rd64 (slot fp (BitVec.ofNat 64 counter)) :=
  agreeW_rdW layout frame reserved bound

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

/-- The actual expression layout writes at the first free slot, so this slot
    cannot simultaneously hold a loop counter without changing allocation. -/
theorem counter_expression_collision [Kern] {D : Gabbro.Grammatik.Deklaration}
    (L : Lay D) {Γ : Gabbro.Grammatik.Ctx}
    {Λ : List (Gabbro.Grammatik.Res D)} :
    lowE L (show Gabbro.Grammatik.Expr D Γ Λ .bool from .tru) (frei Γ) =
      some ([ci 1 (frei Γ) 1 0], frei Γ + 1) := rfl

/-- Updating an allocated prefix cell preserves every lexical variable (including
parameters), the ABI header, and every other reservation cell. The memory update
is the actual runner write; separation follows from canonical variable placement. -/
theorem reserved_write_preserves [Kern] {D : Gabbro.Grammatik.Deklaration} {L : Lay D}
    {Γ : Gabbro.Grammatik.Ctx} {ρ : Gabbro.Grammatik.Env D Γ}
    {m : Mem} {fp : W} {reserved K j : Nat} (value : Nat)
    (room : fp.toNat + 8 * K ≤ 2 ^ 64) (bound : frei Γ reserved ≤ K)
    (allocated : j < reserved) (env : EnvAt L m fp ρ reserved) :
    EnvAt L (Mem.write m (slot fp (BitVec.ofNat 64 (FB + j))) 8 value) fp ρ reserved ∧
    ∀ i, i < FB + reserved → i ≠ FB + j →
      (Mem.write m (slot fp (BitVec.ofNat 64 (FB + j))) 8 value).rd64
        (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i)) := by
  have hj : FB + j < K := by unfold frei at bound; omega
  constructor
  · intro τ x
    obtain ⟨w, read, enc⟩ := env τ x
    have low := vslot_reserved x reserved
    have high := vslot_lt (reserved := reserved) x
    refine ⟨w, ?_, enc⟩
    rw [Mem.rd64_write_far (slot_far room hj (by omega) (by omega))]
    exact read
  · intro i hi ne
    exact Mem.rd64_write_far (slot_far room hj (by unfold frei at bound; omega) (Ne.symm ne))

/-- Reservation is function-wide: changing its size changes every parameter and
local slot by exactly that amount. A loop-local shift cannot reuse the old EnvAt. -/
theorem reservation_variable_offset {Γ : Gabbro.Grammatik.Ctx}
    {τ : Gabbro.Grammatik.Ty} (x : Gabbro.Grammatik.Var Γ τ) (reserved extra : Nat) :
    vslot x (reserved + extra) = vslot x reserved + extra ∧
      frei Γ (reserved + extra) = frei Γ reserved + extra := by
  simp only [vslot, frei]
  omega

/-- Two words per active loop give disjoint counter/one pairs at every depth.
The byte offsets are derived from the runner slot definition without wraparound. -/
theorem nested_reservation_offsets {fp : W} {K depth outer : Nat}
    (room : fp.toNat + 8 * K ≤ 2 ^ 64) (bound : FB + 2 * depth ≤ K)
    (inside : outer < depth) :
    (slot fp (BitVec.ofNat 64 (FB + 2 * outer))).toNat =
      fp.toNat + 8 * FB + 16 * outer ∧
    (slot fp (BitVec.ofNat 64 (FB + 2 * outer + 1))).toNat =
      fp.toNat + 8 * FB + 16 * outer + 8 ∧
    ∀ inner, outer < inner → inner < depth →
      FB + 2 * outer + 1 < FB + 2 * inner := by
  constructor
  · rw [slot_toNat room (by omega)]; omega
  constructor
  · rw [slot_toNat room (by omega)]; omega
  · intro inner before within
    omega

/-- A parameter in a nonempty context moves past both nested counter pairs.
Its old ABI slot is occupied by the outer counter, demonstrating why an entry
relocation is required before a function-wide reservation can be enabled. -/
theorem reservation_parameter_offset_zeuge :
    vslot (Gabbro.Grammatik.Var.here : Gabbro.Grammatik.Var [.bool] .bool) 4 = 8 ∧
    vslot (Gabbro.Grammatik.Var.here : Gabbro.Grammatik.Var [.bool] .bool) 0 = FB ∧
    (slot (4096 : W) (BitVec.ofNat 64 (FB + 2))).toNat = 4144 ∧
    (slot (4096 : W) (BitVec.ofNat 64 (FB + 3))).toNat = 4152 := by decide

end Gabbro.Stage0.Senke
