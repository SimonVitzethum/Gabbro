/- C13 bit builtin preservation at the public typed dispatch. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.BitBuiltin.Folds
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.BitBuiltin.Bytes
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.BitBuiltin.Rotate
@[expose] public section

namespace Gabbro.Stage0.Senke.BitBuiltin
open Gabbro.Grammatik Runner.IR
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D} {fp : Runner.W} {K reserved : Nat}
  {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
local notation "Runs" => Produces L fp K ρ W reserved

/-- Equal range spellings transport the complete producer certificate without inserting
    an emitted integer resize. The canonical Zahl value is identified by its number. -/
private theorem transport_result {hi hi' : Int} {f : Emitter}
    (domain : hi = hi') (v : Zahl 0 hi) (r : Zahl 0 hi') (same : r.n = v.n)
    (code : Runs f (.int 0 hi) v) : Runs f (.int 0 hi') r := by
  subst hi'
  have value : v = r := Zahl.ext_n same.symm
  cases value
  exact code

theorem unary_ok {τ1 τ : Ty} (op : IntBuiltin [τ1] τ) (x : Wert D τ1)
    {fa : Emitter} (ia : Runs fa τ1 x) :
    Runs (unary op fa) τ (evalIntBuiltin1 op x) := by
  cases op with
  | clz w =>
    let u := (2 : Int) ^ (w + 1) - 1
    let full : Zahl 0 u := ⟨x.n, by have := x.lo_le; omega, x.le_hi⟩
    let count : Zahl 0 (w : Int) := ⟨(w : Int), by omega, by omega⟩
    have bound : u < (2 : Int) ^ (w + 2) := field_bound w
    have fits : full.n.toNat < 2 ^ (w + 1) := (zahlNat_bounds w x).2
    apply sub_ok count (logarithmValue w full fits) (Zahl.clz w x) ?_ (constant_ok count)
      (logarithm_ok (w + 2) bound (by omega) w full fits (cast_ok x full rfl ia))
    change ((w - x.n.toNat.log2 : Nat) : Int) = (w : Int) - (x.n.toNat.log2 : Int)
    exact Int.ofNat_sub (log_bound w full.n.toNat fits)
  | log2Floor w =>
    let u := (2 : Int) ^ (w + 1) - 1
    let full : Zahl 0 u := ⟨x.n, by have := x.lo_le; omega, x.le_hi⟩
    have bound : u < (2 : Int) ^ (w + 2) := field_bound w
    have fits : full.n.toNat < 2 ^ (w + 1) := (zahlNat_bounds w x).2
    exact logarithm_ok (w + 2) bound (by omega) w full fits (cast_ok x full rfl ia)
  | ctz w =>
    let u := (2 : Int) ^ (w + 1) - 1
    let full : Zahl 0 u := ⟨x.n, by have := x.lo_le; omega, x.le_hi⟩
    have bound : u < (2 : Int) ^ (w + 2) := field_bound w
    exact cast_ok (trailingValue (w + 1) full) (Zahl.ctz w x) rfl
      (trailing_ok (w + 2) bound (by omega) (w + 1) full (cast_ok x full rfl ia))
  | popcount w =>
    have bound := field_bound w
    erw [show evalIntBuiltin1 (D := D) (.popcount w) x = Zahl.popcount w x from rfl]
    change Runs (population ((2 : Int) ^ (w + 1) - 1) (w + 1) fa)
      (.int 0 ((w : Int) + 1)) (Zahl.popcount w x)
    exact transport_result
      (by simp only [Int.natCast_add, Int.natCast_one] : ((w + 1 : Nat) : Int) = (w : Int) + 1)
      (populationValue (w + 1) x) (Zahl.popcount w x) rfl
      (population_ok (w + 2) bound (by omega) (w + 1) x ia)
  | bswap16 =>
    erw [show evalIntBuiltin1 (D := D) .bswap16 x = Zahl.bswap16 x from rfl]
    change Runs (reverseBytes ((2 : Int) ^ 16 - 1) 2 fa)
      (.int 0 ((2 : Int) ^ 16 - 1)) (Zahl.bswap16 x)
    exact transport_result (by decide : (256 : Int) ^ 2 - 1 = (2 : Int) ^ 16 - 1)
      (reverseValue 2 x) (Zahl.bswap16 x)
      (by change (bswap16n x.n.toNat : Int) = (reverseNat 2 x.n.toNat : Int); rw [reverseNat_bswap16])
      (reverseBytes_ok 17 (by decide) (by decide) 2 x ia)
  | bswap32 =>
    erw [show evalIntBuiltin1 (D := D) .bswap32 x = Zahl.bswap32 x from rfl]
    change Runs (reverseBytes ((2 : Int) ^ 32 - 1) 4 fa)
      (.int 0 ((2 : Int) ^ 32 - 1)) (Zahl.bswap32 x)
    exact transport_result (by decide : (256 : Int) ^ 4 - 1 = (2 : Int) ^ 32 - 1)
      (reverseValue 4 x) (Zahl.bswap32 x)
      (by change (bswap32n x.n.toNat : Int) = (reverseNat 4 x.n.toNat : Int); rw [reverseNat_bswap32])
      (reverseBytes_ok 33 (by decide) (by decide) 4 x ia)
  | bswap64 =>
    erw [show evalIntBuiltin1 (D := D) .bswap64 x = Zahl.bswap64 x from rfl]
    change Runs (reverseBytes ((2 : Int) ^ 64 - 1) 8 fa)
      (.int 0 ((2 : Int) ^ 64 - 1)) (Zahl.bswap64 x)
    exact transport_result (by decide : (256 : Int) ^ 8 - 1 = (2 : Int) ^ 64 - 1)
      (reverseValue 8 x) (Zahl.bswap64 x)
      (by change (bswap64n x.n.toNat : Int) = (reverseNat 8 x.n.toNat : Int); rw [reverseNat_bswap64])
      (reverseBytes_ok 65 (by decide) (by decide) 8 x ia)

end Gabbro.Stage0.Senke.BitBuiltin
