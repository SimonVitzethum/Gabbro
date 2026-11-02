/- C13 joint witnesses: exact-width arithmetic, aggregate transport and count binders. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Proben
public import Stage0.Senke.Ausdruck.Quant.Proben
public import Stage0.Senke.Ausdruck.Old.Sound
@[expose] public section

namespace Gabbro.Stage0.Senke.BuiltinProbe
open Gabbro.Grammatik Runner.IR
open AggregateProbe (D layout world)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def unsigned {Γ : Ctx} {Λ : List (Res D)} (w : Nat) (n : Int)
    (lower : 0 ≤ n) (upper : n ≤ (2 : Int) ^ (w + 1) - 1) :
    Expr D Γ Λ (.int 0 ((2 : Int) ^ (w + 1) - 1)) :=
  .widen lower upper (.lit n)

def signed {Γ : Ctx} {Λ : List (Res D)} (n : Int) (lower : -8 ≤ n) (upper : n ≤ 7) :
    Expr D Γ Λ (.int (-8) 7) := .widen lower upper (.lit n)

def amount {Γ : Ctx} {Λ : List (Res D)} (w n : Nat) (bound : n ≤ w) :
    Expr D Γ Λ (.int 0 (w : Int)) := .widen (by omega) (by omega) (.lit n)

def mixed : Expr D [] [] (.int 0 4) := .count 4 (.lt (.var .here) (.lit 2))

/-- The inner count reads both binders; exactly three outer indices match once. -/
def nested : Expr D [] [] (.int 0 3) :=
  .count 3 (.eq (.count 3 (.eq (.var .here) (.var (.there .here)))) (.lit 1))

def checks : Expr D [] [] .bool :=
  [ .eq (.intBuiltin2 (.addW 7) (unsigned 7 255 (by decide) (by decide))
      (unsigned 7 1 (by decide) (by decide))) (.lit 0),
    .eq (.intBuiltin2 (.subW 7) (unsigned 7 0 (by decide) (by decide))
      (unsigned 7 1 (by decide) (by decide))) (.lit 255),
    .eq (.intBuiltin2 (.mulW 7) (unsigned 7 255 (by decide) (by decide))
      (unsigned 7 255 (by decide) (by decide))) (.lit 1),
    .eq (.intBuiltin2 (.shlW 7) (unsigned 7 255 (by decide) (by decide))
      (amount 7 7 (by decide))) (.lit 128),
    .eq (.intBuiltin2 (.shlW 7) (unsigned 7 129 (by decide) (by decide))
      (amount 7 0 (by decide))) (.lit 129),
    .eq (.intBuiltin2 (.addW 69) (unsigned 69 (2 ^ 70 - 1) (by decide) (by decide))
      (unsigned 69 1 (by decide) (by decide))) (.lit 0),
    .eq (.intBuiltin2 (.addW 69) (unsigned 69 (2 ^ 64 - 1) (by decide) (by decide))
      (unsigned 69 1 (by decide) (by decide))) (.lit (2 ^ 64)),
    .eq (.intBuiltin2 (.subW 69) (unsigned 69 0 (by decide) (by decide))
      (unsigned 69 1 (by decide) (by decide))) (.lit (2 ^ 70 - 1)),
    .eq (.intBuiltin2 (.mulW 69) (unsigned 69 (2 ^ 70 - 1) (by decide) (by decide))
      (unsigned 69 (2 ^ 70 - 1) (by decide) (by decide))) (.lit 1),
    .eq (.intBuiltin2 (.shlW 69) (unsigned 69 3 (by decide) (by decide))
      (amount 69 69 (by decide))) (.lit (2 ^ 69)),
    .eq (.intBuiltin2 (.addS 0 255) (unsigned 7 200 (by decide) (by decide))
      (unsigned 7 100 (by decide) (by decide))) (.lit 255),
    .eq (.intBuiltin2 (.addS (-8) 7) (signed (-7) (by decide) (by decide))
      (signed (-3) (by decide) (by decide))) (.lit (-8)),
    .eq (.intBuiltin2 (.addS (-8) 7) (signed 6 (by decide) (by decide))
      (signed 4 (by decide) (by decide))) (.lit 7),
    .eq (.intBuiltin2 (.addS (-8) 7) (signed (-2) (by decide) (by decide))
      (signed 3 (by decide) (by decide))) (.lit 1),
    .eq (.intBuiltin2 (.addS 0 (2 ^ 70 - 1))
      (unsigned 69 (2 ^ 70 - 1) (by decide) (by decide))
      (unsigned 69 1 (by decide) (by decide))) (.lit (2 ^ 70 - 1)),
    .eq (.intBuiltin2 (.addS (-(2 ^ 69)) (2 ^ 69 - 1))
      (.widen (by decide) (by decide) (.lit (-(2 ^ 69))))
      (.widen (by decide) (by decide) (.lit (-1)))) (.lit (-(2 ^ 69))),
    .eq (.intBuiltin2 (.addS (-(2 ^ 69)) (2 ^ 69 - 1))
      (.widen (by decide) (by decide) (.lit (2 ^ 69 - 1)))
      (.widen (by decide) (by decide) (.lit 1))) (.lit (2 ^ 69 - 1)),
    .eq (.arrGet (.arrCons (.intBuiltin2 (.addW 69)
      (unsigned 69 (2 ^ 64 - 1) (by decide) (by decide))
      (unsigned 69 1 (by decide) (by decide)))
      (.arrCons (unsigned 69 7 (by decide) (by decide)) .arrNil))
      (.widen (by decide) (by decide) (.lit 0))) (.lit (2 ^ 64)),
    .eq mixed (.lit 2), .eq nested (.lit 3),
    .eq (.count 0 .tru) (.lit 0)
  ].foldr Expr.and .tru

theorem semantics_zeuge : eval world checks world .nil = true := by decide +kernel

def compiled : List II × Nat := (lowE layout checks 4).getD ([], 0)

theorem lowering_zeuge : lowE layout checks 4 = some compiled ∧ compiled.1 ≠ [] ∧ compiled.2 ≤ 256 := by
  decide +kernel

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

theorem pre [Kern] : PreS layout memory 0 1048576 256 4 compiled.1 (Env.nil : Env D []) := by
  refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
    codeAt_bytes compiled.1 0 (by decide +kernel) bytes, ?_, ?_, trivial, wstab_true _ _⟩
  · unfold CodeFar; decide +kernel
  · intro _ x; nomatch x

/-- The actual compiler path invokes the arithmetic/count composition proofs on
    nonempty code and a frame disjoint from all code bytes. -/
theorem intBuiltin2L_ok_zeuge [Kern] :
    lowE layout checks 4 = some compiled ∧
    PreS layout memory 0 1048576 256 4 compiled.1 (Env.nil : Env D []) ∧
    ValueOk layout memory 0 1048576 256 4 compiled.1 .bool true := by
  refine ⟨lowering_zeuge.1, pre, ?_⟩
  have hw : ∀ m, WeltAt m layout world := by
    intro m
    refine ⟨(fun t => Fin.elim0 t), (fun g => Fin.elim0 g), ?_⟩
    intro x hl hh
    change 65536 ≤ x at hl
    change x < 65536 at hh
    omega
  simpa only [semantics_zeuge] using lowE_ok world world (W := fun _ => True)
    (fun m _ => hw m) AggregateProbe.hLay checks 4 compiled.1 compiled.2
    lowering_zeuge.1 lowering_zeuge.2.2 memory 0 .nil pre

/-- The same nonempty fixture passes function/return and image assembly, rather
    than remaining a detached expression emitter. -/
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

theorem mask_modulus_zeuge :
    (((2 ^ 70 + 5 : Int).toNat &&& (2 ^ 70 - 1) : Nat) : Int) = 5 := by
  rw [mask_modulus 69 _ (by decide)]
  decide

theorem countL_bounds_zeuge :
    ∃ c top, lowE layout (reserved := 3) nested 9 = some (c, top) ∧
      9 < top ∧ c.length < 2 ^ 31 := by
  let ct := (lowE layout (reserved := 3) nested 9).getD ([], 0)
  have emitted : lowE layout (reserved := 3) nested 9 = some ct := by decide +kernel
  have bounds := countL_bounds emitted
  exact ⟨ct.1, ct.2, emitted, bounds.1, bounds.2.2⟩

theorem countVal_idxAb_bound_zeuge :
    countVal (idxAb 4 1 3) (fun k => decide (k.n < 3)) = 2 ∧
    countVal (idxAb 4 1 3) (fun k => decide (k.n < 3)) ≤ 3 ∧
    1 + countVal (idxAb 4 1 3) (fun k => decide (k.n < 3)) ≤ 4 := by
  exact ⟨by decide +kernel, countVal_idxAb_bound 4 1 3 _ (by decide)⟩

/-- Code expansion and index immediates fail closed; empty count needs no body. -/
theorem count_refused_zeuge :
    countL 4 8 0 none = some ([ci 1 8 0 0], 9) ∧
    countL 4 8 1 none = none ∧
    countL 4 8 (2 ^ 31) (some ([], 12)) = none ∧
    countL 4 8 (2 ^ 29) (some ([], 12)) = none := by decide +kernel

def occupied : Expr QuantProbe.D [] [] (.int 0 4) :=
  .count 4 (.istSome (.slot QuantProbe.tab QuantProbe.field (.var .here) QuantProbe.access))

theorem table_count_zeuge :
    (eval QuantProbe.initial occupied QuantProbe.linked .nil).n = 3 ∧
    (lowE (layU QuantProbe.u (fun _ => none) 65536) occupied 8).isSome = true := by
  decide +kernel

/-- Named cuts: no CPU scan zero convention, rotate or byte swap is assumed. -/
theorem builtin_refused_zeuge :
    lowE layout (Γ := []) (Λ := []) (.intBuiltin1 (.clz 7) (.widen (by decide) (by decide) (.lit 1))) 4 = none ∧
    lowE layout (Γ := []) (Λ := []) (.intBuiltin1 (.ctz 7) (.widen (by decide) (by decide) (.lit 128))) 4 = none ∧
    lowE layout (Γ := []) (Λ := []) (.intBuiltin1 (.log2Floor 7) (.widen (by decide) (by decide) (.lit 3))) 4 = none ∧
    lowE layout (Γ := []) (Λ := []) (.intBuiltin1 (.popcount 7) (unsigned 7 255 (by decide) (by decide))) 4 = none ∧
    lowE layout (Γ := []) (Λ := []) (.intBuiltin1 .bswap16 (unsigned 15 4660 (by decide) (by decide))) 4 = none ∧
    lowE layout (Γ := []) (Λ := []) (.intBuiltin1 .bswap32 (unsigned 31 305419896 (by decide) (by decide))) 4 = none ∧
    lowE layout (Γ := []) (Λ := []) (.intBuiltin1 .bswap64 (unsigned 63 72623859790382856 (by decide) (by decide))) 4 = none ∧
    lowE layout (Γ := []) (Λ := []) (.intBuiltin2 (.rotl 7) (unsigned 7 129 (by decide) (by decide)) (amount 7 1 (by decide))) 4 = none ∧
    lowE layout (Γ := []) (Λ := []) (.intBuiltin2 (.rotr 7) (unsigned 7 129 (by decide) (by decide)) (amount 7 1 (by decide))) 4 = none := by
  decide +kernel

end Gabbro.Stage0.Senke.BuiltinProbe
