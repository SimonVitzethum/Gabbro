/- C13 bit witnesses at W=8 and W=70, with the actual expression and image paths. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.BuiltinProbes
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.BuiltinOldProbes
@[expose] public section

namespace Gabbro.Stage0.Senke.BitBuiltinProbe
open Gabbro.Grammatik Runner.IR
open AggregateProbe (D layout world)
open BuiltinProbe (unsigned amount)
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def nonzero (w : Nat) (n : Int) (lower : 1 ≤ n)
    (upper : n ≤ (2 : Int) ^ (w + 1) - 1) : Expr D [] [] (.int 1 ((2 : Int) ^ (w + 1) - 1)) :=
  .widen lower upper (.lit n)

/-- Both endpoints exercise every scan; popcount includes zero and a partial
    top limb filled entirely with ones. -/
def endpoints (w : Nat) (one : 1 ≤ (2 : Int) ^ (w + 1) - 1)
    (top : (2 : Int) ^ w ≤ (2 : Int) ^ (w + 1) - 1)
    (positive : 1 ≤ (2 : Int) ^ w) : Expr D [] [] .bool :=
  [ .eq (.intBuiltin1 (.clz w) (nonzero w 1 (by omega) one)) (.lit w),
    .eq (.intBuiltin1 (.ctz w) (nonzero w 1 (by omega) one)) (.lit 0),
    .eq (.intBuiltin1 (.log2Floor w) (nonzero w 1 (by omega) one)) (.lit 0),
    .eq (.intBuiltin1 (.clz w) (nonzero w (2 ^ w) positive top)) (.lit 0),
    .eq (.intBuiltin1 (.ctz w) (nonzero w (2 ^ w) positive top)) (.lit w),
    .eq (.intBuiltin1 (.log2Floor w) (nonzero w (2 ^ w) positive top)) (.lit w),
    .eq (.intBuiltin1 (.popcount w) (unsigned w 0 (by omega) (by omega))) (.lit 0),
    .eq (.intBuiltin1 (.popcount w) (unsigned w (2 ^ (w + 1) - 1) (by omega) (by omega)))
      (.lit (w + 1 : Nat)) ].foldr Expr.and .tru

def checks : Expr D [] [] .bool :=
  [ endpoints 7 (by decide) (by decide) (by decide),
    endpoints 69 (by decide) (by decide) (by decide),
    .eq (.intBuiltin2 (.rotr 7) (.intBuiltin2 (.rotl 7)
        (unsigned 7 165 (by decide) (by decide)) (amount 7 7 (by decide)))
      (amount 7 7 (by decide))) (.lit 165),
    .eq (.intBuiltin2 (.rotr 69) (.intBuiltin2 (.rotl 69)
        (unsigned 69 (2 ^ 64 + 165) (by decide) (by decide)) (amount 69 69 (by decide)))
      (amount 69 69 (by decide))) (.lit (2 ^ 64 + 165)),
    .eq (.intBuiltin2 (.rotl 7) (unsigned 7 165 (by decide) (by decide))
      (amount 7 0 (by decide))) (.lit 165),
    .eq (.intBuiltin2 (.rotr 69) (unsigned 69 (2 ^ 69) (by decide) (by decide))
      (amount 69 0 (by decide))) (.lit (2 ^ 69)),
    .eq (.intBuiltin2 (.rotl 69) (unsigned 69 (2 ^ 69) (by decide) (by decide))
      (amount 69 1 (by decide))) (.lit 1),
    .eq (.intBuiltin2 (.rotr 69) (unsigned 69 1 (by decide) (by decide))
      (amount 69 1 (by decide))) (.lit (2 ^ 69)),
    -- Named swaps have fixed widths; an 8-bit payload and a 70-bit container
    -- exercise their inclusion in surrounding values without inventing bswap8/70.
    .eq (.intBuiltin1 .bswap16 (.intBuiltin1 .bswap16
      (unsigned 15 165 (by decide) (by decide)))) (.lit 165),
    .eq (.intBuiltin1 .bswap32 (.intBuiltin1 .bswap32
      (unsigned 31 305419896 (by decide) (by decide)))) (.lit 305419896),
    .eq (.widen (lo' := 0) (hi' := 2 ^ 70 - 1) (by decide) (by decide)
      (.intBuiltin1 .bswap64 (.intBuiltin1 .bswap64
        (unsigned 63 72623859790382856 (by decide) (by decide))))) (.lit 72623859790382856)
  ].foldr Expr.and .tru

theorem bit_semantics_zeuge : eval world checks world .nil = true := by decide +kernel

def compiled : List II × Nat := (lowE layout checks 4).getD ([], 0)

theorem bit_lowering_zeuge :
    lowE layout checks 4 = some compiled ∧ compiled.1 ≠ [] ∧ compiled.2 ≤ 256 := by decide +kernel

def memory : Runner.Mem where
  b a := ((compiled.1.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

theorem bytes : BytesAt memory 0 (compiled.1.flatMap encII) := by
  intro i hi
  refine ⟨rfl, rfl, ?_⟩
  have size : (compiled.1.flatMap encII).length < 2 ^ 64 := by decide +kernel
  simp only [memory, Nat.zero_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), List.getElem?_eq_getElem hi, Option.getD_some]

theorem pre [Kern] : PreS layout memory 0 1073741824 256 4 compiled.1 (Env.nil : Env D []) := by
  refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
    codeAt_bytes compiled.1 0 (by decide +kernel) bytes, ?_, ?_, trivial, wstab_true _ _⟩
  · unfold CodeFar; decide +kernel
  · intro _ x; nomatch x

/-- Real bytes and a disjoint frame instantiate the generic theorem at every
    bit family, both full and partial limbs, rather than only reducing Zahl. -/
theorem lowE_ok_zeuge [Kern] :
    lowE layout checks 4 = some compiled ∧
    PreS layout memory 0 1073741824 256 4 compiled.1 (Env.nil : Env D []) ∧
    ValueOk layout memory 0 1073741824 256 4 compiled.1 .bool true := by
  refine ⟨bit_lowering_zeuge.1, pre, ?_⟩
  have hw : ∀ m, WeltAt m layout world := by
    intro m
    refine ⟨(fun t => Fin.elim0 t), (fun g => Fin.elim0 g), ?_⟩
    intro x hl hh
    change 65536 ≤ x at hl
    change x < 65536 at hh
    omega
  simpa only [bit_semantics_zeuge] using lowE_ok (same := by intro _; rfl) world world (W := fun _ => True)
    (fun m _ => hw m) AggregateProbe.hLay checks 4 compiled.1 compiled.2
    bit_lowering_zeuge.1 bit_lowering_zeuge.2.2 memory 0 .nil pre

def program : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have zero : f = 0 := by change f < 1 at hf; omega
    subst f
    exact .ret (.val (.wenn checks (.widen (by decide) (by decide) (.lit 42))
      (.widen (by decide) (by decide) (.lit 0)))) (.refl [])

def image : Except String (List Runner.B) := do
  let b ← bild 1 program (layU AggregateProbe.u (fun _ => none)) [⟨0, by decide⟩] Fin.val
    (fun _ => "main") ⟨0, by decide⟩ .nil [] 1024
  pure b.bytes

theorem connected_image_zeuge : image.isOk = true := by decide +kernel

/-- The snapshot-aware dispatch retains the actual entry operand. -/
theorem snapshot_bit_zeuge :
    let expression : Expr BuiltinOldProbe.D [] [] (.int 0 8) :=
      .intBuiltin1 (.popcount 7) (.oldG BuiltinOldProbe.global BuiltinOldProbe.access)
    (eval BuiltinOldProbe.entry expression BuiltinOldProbe.exitWorld .nil).n = 3 ∧
    (eval BuiltinOldProbe.exitWorld expression BuiltinOldProbe.exitWorld .nil).n = 2 ∧
    (lowEns BuiltinOldProbe.layout BuiltinOldProbe.frameLayout expression 8).isSome = true := by
  decide +kernel

end Gabbro.Stage0.Senke.BitBuiltinProbe
