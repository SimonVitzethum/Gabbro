/- Value-level composition for C13; all execution is supplied by existing limb kernels. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Saturation
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Shift
public import Stage0.Senke.Ausdruck.Aggregat.Werte.IntegerResize
@[expose] public section

namespace Gabbro.Stage0.Senke.BitBuiltin
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false

/-- The ordinary structural induction hypothesis, shared by the bounded bit folds. -/
def Produces [Kern] {D : Deklaration} (L : Lay D) (fp : Runner.W) (K : Nat)
    {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) (reserved : Nat)
    (f : Emitter) (τ : Ty) (v : Wert D τ) : Prop :=
  ∀ d c top, f d = some (c, top) → top ≤ K → ∀ m pc,
    Pre L m pc fp K d c ρ W reserved → ValueOk L m pc fp K d c τ v

variable [Kern] {D : Deklaration} {L : Lay D} {fp : Runner.W} {K reserved : Nat}
  {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
local notation "Runs" => Produces L fp K ρ W reserved

/-- Proof-only packaging of a nonnegative natural value in its declared interval. -/
def natural (hi : Int) (n : Nat) (bound : (n : Int) ≤ hi) : Zahl 0 hi :=
  ⟨n, by omega, bound⟩

/-- Internal shifts reserve one extra bit, including W=1 and amount W. -/
theorem field_bound (w : Nat) : (2 : Int) ^ (w + 1) - 1 < 2 ^ (w + 2) := by
  have monotone : (2 : Int) ^ (w + 1) ≤ 2 ^ (w + 2) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) (show w + 1 ≤ w + 2 by omega)
  omega

theorem cast_ok {lo hi lo' hi' : Int} (x : Zahl lo hi) (r : Zahl lo' hi')
    (same : r.n = x.n) {f : Emitter} (ih : Runs f (.int lo hi) x) :
    Runs (cast lo hi lo' hi' f) (.int lo' hi') r := by
  intro d c top emitted fits m pc pre
  simp only [cast, Option.map_eq_some_iff] at emitted
  obtain ⟨⟨cc, tt⟩, lowered, equal⟩ := emitted
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact resizeIntegerL_ok x r same
    (fun cc tt hc ht hp => ih d cc tt hc ht m pc hp) lowered (by omega) pre

theorem constant_ok {hi : Int} (x : Zahl 0 hi) : Runs (constant hi x.n) (.int 0 hi) x := by
  intro d c top emitted fits m pc pre
  exact intConstL_ok x emitted fits pre

theorem add_ok {ha hb hr : Int} (x : Zahl 0 ha) (y : Zahl 0 hb) (r : Zahl 0 hr)
    (same : r.n = x.n + y.n) {fa fb : Emitter}
    (ia : Runs fa (.int 0 ha) x) (ib : Runs fb (.int 0 hb) y) :
    Runs (add ha hb hr fa fb) (.int 0 hr) r := by
  apply cast_ok (Zahl.add x y) r same
  intro d c top emitted fits m pc pre
  exact wideAdd_ok x y (ia d) (ib _) emitted fits pre

theorem sub_ok {ha hb hr : Int} (x : Zahl 0 ha) (y : Zahl 0 hb) (r : Zahl 0 hr)
    (same : r.n = x.n - y.n) {fa fb : Emitter}
    (ia : Runs fa (.int 0 ha) x) (ib : Runs fb (.int 0 hb) y) :
    Runs (sub ha hb hr fa fb) (.int 0 hr) r := by
  apply cast_ok (Zahl.sub x y) r same
  intro d c top emitted fits m pc pre
  exact wideSub_ok x y (ia d) (ib _) emitted fits pre

theorem shl_ok {hi : Int} (width s : Nat) (bound : hi < (2 : Int) ^ width)
    (amount : s < width) (x : Zahl 0 hi) (y : Zahl 0 (s : Int))
    (r : Zahl 0 (hi * 2 ^ s)) (same : r.n = ((x.n.toNat * 2 ^ y.n.toNat : Nat) : Int))
    {fa fb : Emitter} (ia : Runs fa (.int 0 hi) x) (ib : Runs fb (.int 0 (s : Int)) y) :
    Runs (shl hi s fa fb) (.int 0 (hi * 2 ^ s)) r := by
  have value : r = Zahl.shl width bound (by omega) (by decide) (by decide) x y := by
    apply Zahl.ext_n
    rw [same]
    change ((x.n.toNat * 2 ^ y.n.toNat : Nat) : Int) = x.n * 2 ^ y.n.toNat
    rw [Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int, Int.toNat_of_nonneg x.lo_le]
  subst r
  intro d c top emitted fits m pc pre
  simpa only [Int.toNat_natCast] using
    wideShl_ok width bound (by omega) (by decide) (by decide) x y (ia d) (ib _) emitted fits pre

theorem shr_ok {hi : Int} (width s : Nat) (bound : hi < (2 : Int) ^ width)
    (amount : s < width) (x : Zahl 0 hi) (y : Zahl 0 (s : Int))
    (r : Zahl 0 hi) (same : r.n = ((x.n.toNat / 2 ^ y.n.toNat : Nat) : Int))
    {fa fb : Emitter} (ia : Runs fa (.int 0 hi) x) (ib : Runs fb (.int 0 (s : Int)) y) :
    Runs (shr hi s fa fb) (.int 0 hi) r := by
  have value : r = Zahl.shr width bound (by omega) (by decide) (by decide) x y := by
    apply Zahl.ext_n
    rw [same]
    change ((x.n.toNat / 2 ^ y.n.toNat : Nat) : Int) = x.n / 2 ^ y.n.toNat
    rw [Int.natCast_ediv, Int.natCast_pow, Int.cast_ofNat_Int, Int.toNat_of_nonneg x.lo_le]
  subst r
  intro d c top emitted fits m pc pre
  exact wideShr_ok width bound (by omega) (by decide) (by decide) x y (ia d) (ib _) emitted fits pre

theorem mask_ok {hi : Int} (bits : Nat) (x : Zahl 0 hi)
    (r : Zahl 0 ((2 : Int) ^ bits - 1))
    (same : r.n = ((x.n.toNat % 2 ^ bits : Nat) : Int)) {fa : Emitter}
    (ia : Runs fa (.int 0 hi) x) :
    Runs (mask hi bits fa) (.int 0 ((2 : Int) ^ bits - 1)) r := by
  let upper := (2 : Int) ^ bits - 1
  have pos : (0 : Int) < 2 ^ bits := by positivity
  let z : Zahl 0 upper := ⟨upper, by dsimp [upper]; omega, by omega⟩
  have zn : z.n.toNat = 2 ^ bits - 1 := by
    have cast : ((2 ^ bits - 1 : Nat) : Int) = upper := by
      rw [Int.ofNat_sub (by have : (0 : Nat) < 2 ^ bits := Nat.pow_pos (by decide); omega)]
      simp only [Int.natCast_pow, Int.cast_ofNat_Int, upper]
    rw [show z.n = upper from rfl, ← cast, Int.toNat_natCast]
  have value : r = Zahl.band (by decide) (by decide) z x := by
    apply Zahl.ext_n
    change r.n = ((z.n.toNat &&& x.n.toNat : Nat) : Int)
    rw [zn, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, same]
  subst r
  intro d c top emitted fits m pc pre
  exact wideBand_ok (by decide) (by decide) z x
    (constant_ok z d) (ia _) emitted fits pre

theorem eq_ok {ha hb : Int} (x : Zahl 0 ha) (y : Zahl 0 hb) {fa fb : Emitter}
    (ia : Runs fa (.int 0 ha) x) (ib : Runs fb (.int 0 hb) y) :
    Runs (eq ha hb fa fb) .bool (decide (x.n = y.n)) := by
  intro d c top emitted fits m pc pre
  exact wideEq_ok x y (ia d) (ib _) emitted fits pre

theorem lt_ok {ha hb : Int} (x : Zahl 0 ha) (y : Zahl 0 hb) {fa fb : Emitter}
    (ia : Runs fa (.int 0 ha) x) (ib : Runs fb (.int 0 hb) y) :
    Runs (lt ha hb fa fb) .bool (decide (x.n < y.n)) := by
  intro d c top emitted fits m pc pre
  exact wideLt_ok x y (ia d) (ib _) emitted fits pre

theorem choose_ok {τ : Ty} (b : Bool) (x y : Wert D τ) {fc fa fb : Emitter}
    (ic : Runs fc .bool b) (ia : Runs fa τ x) (ib : Runs fb τ y) :
    Runs (choose fc fa fb) τ (if b then x else y) := by
  intro d c top emitted fits m pc pre
  simp only [choose, Option.map_eq_some_iff] at emitted
  obtain ⟨⟨cc, tt⟩, lowered, equal⟩ := emitted
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  simp only [wennL, bind, Option.bind_eq_some_iff] at lowered
  obtain ⟨⟨cc, tc⟩, hc, ⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, lowered⟩ := lowered
  split at lowered
  · next budget =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj lowered)
    refine wenn_ok (bc := b) pre budget (by omega) ?_ ?_ ?_
    · intro hp
      exact (ic d cc tc hc (by omega) m pc hp).word trivial
    · intro yes m pc hp
      simpa only [yes, if_true] using ia d ca ta ha (by omega) m pc hp
    · intro no m pc hp
      simpa only [no, Bool.false_eq_true, if_false] using ib d cb tb hb (by omega) m pc hp
  · cases lowered

end Gabbro.Stage0.Senke.BitBuiltin
