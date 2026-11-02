/- C13 witnesses (`_zeuge`) of the value semantics of the closed integer builtins and of the count fold
   (`Kern/Semantik/Semantik/Eingebaut.lean`), on concrete numbers at two storage widths: `W = 8` and `W = 70`
   (a partial top limb and a multiword carry in a 64-bit-limb carrier). Every statement is checked by evaluation
   (`rfl`), so a wrong definition of an operation is a failed proof here, not a wrong claim. -/

module

public import Grammatik.Kern.Semantik.Semantik.Eingebaut
public import Grammatik.Kern.Semantik.Semantik.T1

@[expose] public section

namespace Gabbro.Grammatik

namespace EingebautZeuge

/-- A number of the unsigned range of width `w + 1`, named without a proof term. -/
def zw (w : Nat) (n : Int) (h0 : 0 ≤ n := by decide) (h1 : n ≤ (2 : Int) ^ (w + 1) - 1 := by decide) :
    Zahl 0 ((2 : Int) ^ (w + 1) - 1) := ⟨n, h0, h1⟩

/-- An amount `0 .. w`. -/
def za (w : Nat) (n : Int) (h0 : 0 ≤ n := by decide) (h1 : n ≤ (w : Int) := by decide) : Zahl 0 (w : Int) :=
  ⟨n, h0, h1⟩

/-- A number of the range `lo .. hi`. -/
def zr (lo hi n : Int) (h0 : lo ≤ n := by decide) (h1 : n ≤ hi := by decide) : Zahl lo hi := ⟨n, h0, h1⟩

variable {D : Deklaration}

/-! ## Wrapping arithmetic, at `W = 8` and `W = 70` -/

/-- Wrap-overflow: `255 +% 1 = 0`. -/
theorem addW8_wrap_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.addW 7) (zw 7 255) (zw 7 1)).n = 0 := by rfl

/-- No wrap: `200 +% 55 = 255`. -/
theorem addW8_exakt_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.addW 7) (zw 7 200) (zw 7 55)).n = 255 := by rfl

/-- A carry through every limb: `(2^70 - 1) +% 1 = 0`. -/
theorem addW70_uebertrag_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.addW 69) (zw 69 (2 ^ 70 - 1)) (zw 69 1)).n = 0 := by rfl

/-- Wrap-underflow: `0 -% 1 = 2^8 - 1`. -/
theorem subW8_unterlauf_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.subW 7) (zw 7 0) (zw 7 1)).n = 255 := by rfl

/-- Wrap-underflow at a partial limb: `0 -% 1 = 2^70 - 1`. -/
theorem subW70_unterlauf_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.subW 69) (zw 69 0) (zw 69 1)).n = 2 ^ 70 - 1 := by rfl

/-- `16 *% 16 = 0` at `W = 8`. -/
theorem mulW8_wrap_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.mulW 7) (zw 7 16) (zw 7 16)).n = 0 := by rfl

/-- `2^69 *% 2 = 0` at `W = 70`. -/
theorem mulW70_wrap_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.mulW 69) (zw 69 (2 ^ 69)) (zw 69 2)).n = 0 := by rfl

/-- Shift amount `0`: the value stays. -/
theorem shlW8_null_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.shlW 7) (zw 7 5) (za 7 0)).n = 5 := by rfl

/-- Shift amount `W - 1`: `3 <<% 7 = 128` (the top bit survives, the next is shifted out). -/
theorem shlW8_oben_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.shlW 7) (zw 7 3) (za 7 7)).n = 128 := by rfl

/-- Shift amount `W - 1` at `W = 70`. -/
theorem shlW70_oben_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.shlW 69) (zw 69 3) (za 69 69)).n = 2 ^ 69 := by rfl

/-! ## Saturating addition, unsigned and signed ranges -/

/-- High saturation on `0 .. 255`. -/
theorem addS_hoch_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.addS 0 255) (zr 0 255 200) (zr 0 255 100)).n = 255 := by rfl

/-- No saturation inside the range. -/
theorem addS_innen_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.addS 0 255) (zr 0 255 20) (zr 0 255 100)).n = 120 := by rfl

/-- High saturation on the signed range `-128 .. 127`. -/
theorem addS_vz_hoch_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.addS (-128) 127) (zr (-128) 127 100) (zr (-128) 127 100)).n = 127 := by rfl

/-- Low saturation on the signed range `-128 .. 127`. -/
theorem addS_vz_tief_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.addS (-128) 127) (zr (-128) 127 (-100)) (zr (-128) 127 (-100))).n = -128 := by
  rfl

/-- A sum exactly at the upper bound of a range that starts above zero stays. -/
theorem addS_oberkante_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.addS 10 20) (zr 10 20 10) (zr 10 20 10)).n = 20 := by rfl

/-! ## Bit counts and scans -/

/-- `clz` at `1` and at the top bit, `W = 8`. -/
theorem clz8_zeuge :
    (evalIntBuiltin1 (D := D) (IntBuiltin.clz 7) (zr 1 255 1)).n = 7 ∧
    (evalIntBuiltin1 (D := D) (IntBuiltin.clz 7) (zr 1 255 128)).n = 0 := ⟨rfl, rfl⟩

/-- `ctz` at `1` and at the top bit, `W = 8`. -/
theorem ctz8_zeuge :
    (evalIntBuiltin1 (D := D) (IntBuiltin.ctz 7) (zr 1 255 1)).n = 0 ∧
    (evalIntBuiltin1 (D := D) (IntBuiltin.ctz 7) (zr 1 255 128)).n = 7 := ⟨rfl, rfl⟩

/-- `log2_floor` at `1` and at the top value, `W = 8`. -/
theorem log2Floor8_zeuge :
    (evalIntBuiltin1 (D := D) (IntBuiltin.log2Floor 7) (zr 1 255 1)).n = 0 ∧
    (evalIntBuiltin1 (D := D) (IntBuiltin.log2Floor 7) (zr 1 255 255)).n = 7 := ⟨rfl, rfl⟩

/-- `popcount` at `0` and at all bits, `W = 8` (the result reaches `W`). -/
theorem popcount8_zeuge :
    (evalIntBuiltin1 (D := D) (IntBuiltin.popcount 7) (zw 7 0)).n = 0 ∧
    (evalIntBuiltin1 (D := D) (IntBuiltin.popcount 7) (zw 7 255)).n = 8 := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `popcount` at all bits across a partial limb, `W = 70`. -/
theorem popcount70_zeuge :
    (Zahl.popcount 69 (zw 69 (2 ^ 70 - 1))).n = 70 := by decide +kernel

set_option maxRecDepth 100000 in
/-- `clz` and `ctz` at `W = 70`. -/
theorem clzctz70_zeuge :
    (Zahl.clz 69 (zr 1 (2 ^ 70 - 1) 1)).n = 69 ∧
    (Zahl.ctz 69 (zr 1 (2 ^ 70 - 1) (2 ^ 69))).n = 69 := by decide +kernel

/-! ## Rotates and byte swaps -/

/-- `rotl` carries the top bit around: `129 rotl 1 = 3`. -/
theorem rotl8_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.rotl 7) (zw 7 129) (za 7 1)).n = 3 := by rfl

/-- `rotr` carries the low bit around: `129 rotr 1 = 192`. -/
theorem rotr8_zeuge :
    (evalIntBuiltin2 (D := D) (IntBuiltin.rotr 7) (zw 7 129) (za 7 1)).n = 192 := by rfl

/-- The rotates are inverse on a sample, `W = 8`. -/
theorem rot8_invers_zeuge :
    (Zahl.rotr 7 (Zahl.rotl 7 (zw 7 173) (za 7 3)) (za 7 3)).n = 173 := by decide

/-- The rotates are inverse on a sample across a partial limb, `W = 70`. -/
theorem rot70_invers_zeuge :
    (Zahl.rotr 69 (Zahl.rotl 69 (zw 69 (2 ^ 69 + 12345)) (za 69 66)) (za 69 66)).n =
      2 ^ 69 + 12345 := by decide

/-- `bswap32` reverses the bytes and is an involution on a sample. -/
theorem bswap32_zeuge :
    (evalIntBuiltin1 (D := D) IntBuiltin.bswap32 (zr 0 (2 ^ 32 - 1) 0x11223344)).n = 0x44332211 ∧
    (Zahl.bswap32 (Zahl.bswap32 (zr 0 (2 ^ 32 - 1) 0x11223344))).n = 0x11223344 := ⟨rfl, by decide⟩

/-- `bswap16` and `bswap64` on samples. -/
theorem bswap16_64_zeuge :
    (evalIntBuiltin1 (D := D) IntBuiltin.bswap16 (zr 0 (2 ^ 16 - 1) 0x1234)).n = 0x3412 ∧
    (evalIntBuiltin1 (D := D) IntBuiltin.bswap64 (zr 0 (2 ^ 64 - 1) 0x0102030405060708)).n =
      0x0807060504030201 := ⟨rfl, rfl⟩

/-! ## The count fold -/

/-- Empty domain: `0`. -/
theorem zaehle_leer_zeuge : (zaehleWahr 0 (fun _ => true)).n = 0 := by decide

/-- Every index counts, no index counts. -/
theorem zaehle_alle_keine_zeuge :
    (zaehleWahr 4 (fun _ => true)).n = 4 ∧ (zaehleWahr 4 (fun _ => false)).n = 0 := by decide

/-- Mixed truth values: the even indices of `0 ..< 5` are three. -/
theorem zaehle_gemischt_zeuge : (zaehleWahr 5 (fun k => decide (k.n % 2 = 0))).n = 3 := by decide

/-- A nested binder: the `a` below three with at least two `b ≤ a`, are `a = 1, 2`. -/
theorem zaehle_verschachtelt_zeuge :
    (zaehleWahr 3 (fun a => decide (2 ≤ (zaehleWahr 3 (fun b => decide (b.n ≤ a.n))).n))).n = 2 := by decide

/-- The count as an expression: the indices of `0 ..< 4` below `2`, evaluated by `eval`, whatever the world. -/
theorem count_ausdruck_zeuge (σ₀ σ : World D) :
    (eval σ₀ (Expr.count (D := D) (Γ := []) (Λ := []) 4 (Expr.lt (Expr.var .here) (Expr.lit 2))) σ Env.nil).n = 2 := by
  rfl

/-- The count is at most its bound, for every predicate: the bound `count ≤ n` is in the type. -/
theorem zaehle_beschraenkt_zeuge :
    ∀ k : Nat, (zaehleWahr 3 (fun j => decide (j.n ≤ (k : Int)))).n ≤ ((3 : Nat) : Int) :=
  fun k => (zaehleWahr 3 (fun j => decide (j.n ≤ (k : Int)))).le_hi

end EingebautZeuge

end Gabbro.Grammatik
