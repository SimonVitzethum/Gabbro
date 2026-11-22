module

public import Stage0.Senke.Bild.Ruf.Idle.Operands
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe.Teil2

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

private theorem storedExpr_ru {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) :
    storedExpr (ruE e) = storedExpr e := by
  cases e <;> rfl

private theorem lowPayload_kind {Γ : Ctx} {Λ : List (Res D)} {c c' : Option Ty}
    (h : c = c') (e : NutzlastExpr D Γ Λ c) (L : Lay D) (dst reserve : Nat) (currentOld : Bool) :
    lowPayload L (h ▸ e) dst reserve currentOld = lowPayload L e dst reserve currentOld := by
  cases h
  rfl

private theorem lowN_kind {Γ : Ctx} {Λ : List (Res D)} {c c' : Option Ty}
    (h : c = c') (e : NutzlastExpr D Γ Λ c) (L : Lay D) (tag dst reserve : Nat) (currentOld : Bool) :
    lowN L tag (h ▸ e) dst reserve currentOld = lowN L tag e dst reserve currentOld := by
  cases h
  rfl

private theorem lowProdArgs_types {Γ : Ctx} {Λ : List (Res D)} {fs fs' : List Ty}
    (h : fs = fs') (args : Args D Γ Λ fs) (L : Lay D) (dst reserve : Nat) (currentOld : Bool) :
    lowProdArgs L (h ▸ args) dst reserve currentOld = lowProdArgs L args dst reserve currentOld := by
  cases h
  rfl

theorem unary_withIdle {a r : Ty} (op : IntBuiltin [a] r) (code : BitBuiltin.Emitter) :
    BitBuiltin.unary (ibR op) code = BitBuiltin.unary op code := by
  cases op <;> rfl

theorem binary_withIdle {a b r : Ty} (op : IntBuiltin [a, b] r) (dest : Nat)
    (left right : BitBuiltin.Emitter) :
    intBuiltin2L (ibR op) dest left right = intBuiltin2L op dest left right := by
  cases op <;> rfl

mutual

/-- The typed expression traversal emits the same instructions and scratch
    ceiling in the productive source and in the logical GX declaration. -/
theorem lowE_withIdle (L : Lay D) (reserve : Nat) (currentOld : Bool) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (dst : Nat),
      lowE L.withIdle (ruE e) dst reserve currentOld = lowE L e dst reserve currentOld
  | _, _, _, .tru, _ | _, _, _, .fls, _ | _, _, _, .ptrOf .., _
  | _, _, _, .arrNil, _ | _, _, _, .fnref .., _ => rfl
  | _, _, _, .lit _, _ | _, _, _, .none _, _ | _, _, _, .why .., _
  | _, _, _, .strLit .., _ => by
    simp only [lowE, ruE, lowEWith, encodeWords]
  | _, _, _, .var x, _ => by
    simp only [lowE, ruE, lowEWith, specLookup, vslot_varR, tyR, valueWords_mapNumbers]
  | _, _, _, .glob .., _ | _, _, _, .oldG .., _ => by
    simp only [lowE, ruE, lowEWith, globalValueC_withIdle]
  | _, _, _, .widen _ _ e, _ | _, _, _, .neg e, _ | _, _, _, .not e, _
  | _, _, _, .strLen e, _ | _, _, _, .strWeit _ e, _ | _, _, _, .some e, _
  | _, _, _, .istSome e, _ => by
    have mapped := lowE_withIdle L reserve currentOld e
    simp only [lowE, tyR, Ty.mapNumbers] at mapped
    simp only [lowE, ruE, lowEWith, tyR, Ty.mapNumbers, mapped, funext mapped]
  | _, _, _, .intBuiltin1 op e, dest => by
    have mapped := congrArg (fun code => BitBuiltin.unary op code dest)
      (funext (lowE_withIdle L reserve currentOld e))
    simp only [lowE, ruE, lowEWith, unary_withIdle]
    with_unfolding_all exact mapped
  | _, _, _, .add a b, _ | _, _, _, .sub a b, _ | _, _, _, .mul a b, _
  | _, _, _, .lt a b, _ | _, _, _, .le a b, _ | _, _, _, .eq a b, _
  | _, _, _, .fllt a b, _ | _, _, _, .flle a b, _ | _, _, _, .and a b, _
  | _, _, _, .or a b, _ | _, _, _, .div _ _ a b, _ | _, _, _, .rem _ _ a b, _
  | _, _, _, .sdiv _ a b, _ | _, _, _, .srem _ a b, _ | _, _, _, .band _ _ a b, _
  | _, _, _, .bor _ _ _ _ _ a b, _ | _, _, _, .bxor _ _ _ _ _ a b, _
  | _, _, _, .shl _ _ _ _ _ a b, _ | _, _, _, .shr _ _ _ _ _ a b, _
  | _, _, _, .strCat a b, _ | _, _, _, .strGet a b, _ | _, _, _, .strEq a b, _
  | _, _, _, .strLt a b, _ | _, _, _, .refEq a b, _ | _, _, _, .eng a _ _ b, _
  | _, _, _, .arrCons a b, _ => by
    have left := lowE_withIdle L reserve currentOld a
    have right := lowE_withIdle L reserve currentOld b
    simp only [lowE, tyR, Ty.mapNumbers] at left right
    simp only [lowE, ruE, lowEWith, inUE, inWE, nichtMin, lt64, Ty.mapNumbers,
      valueWords, valueWords_mapNumbers, left, right, funext left, funext right] <;>
      with_unfolding_all rfl
  | _, _, _, .intBuiltin2 op a b, dest => by
    have left := lowE_withIdle L reserve currentOld a
    have right := lowE_withIdle L reserve currentOld b
    let before := fun d => lowE L.withIdle (ruE b) d reserve currentOld
    let after := fun d => lowE L a d reserve currentOld
    have mapped := (congrArg (fun code => intBuiltin2L op dest code before) (funext left)).trans
      (congrArg (intBuiltin2L op dest after) (funext right))
    simp only [lowE, ruE, lowEWith, binary_withIdle]
    with_unfolding_all exact mapped
  | _, _, _, .slot _ _ index _, _ | _, _, _, .thru _ _ _ _ index _, _
  | _, _, _, .thruOwn _ _ _ _ index _ _ _ _ _ _, _ | _, _, _, .slotRef index _ _ _ _ _, _
  | _, _, _, .oldS _ _ index _, _ => by
    have mapped := lowE_withIdle L reserve currentOld index
    simp only [lowE, tyR, Ty.mapNumbers] at mapped
    simp only [lowE, ruE, lowEWith, Deklaration.mitRuhe, tyR,
      valueWords_mapNumbers, Ty.mapNumbers, slotValueC_withIdle, mapped]
  | _, _, _, .getBytes _ _ _ _ index _ _ _, _ => by
    have mapped := lowE_withIdle L reserve currentOld index
    simp only [lowE, tyR, Ty.mapNumbers] at mapped
    simp only [lowE, ruE, lowEWith, readBytesWideL_withIdle, tyR, Ty.mapNumbers, funext mapped]
  | Γ, _, _, .forallSlots t body _, dest => by
    simp only [lowE, ruE, lowEWith, specLookup, frei_withIdle, Deklaration.mitRuhe]
    with_unfolding_all exact (congrArg (quantL true (frei Γ reserve) dest (D.count t))
      (lowE_withIdle L reserve currentOld body (dest + 3)))
  | Γ, _, _, .existsSlots t body _, dest => by
    simp only [lowE, ruE, lowEWith, specLookup, frei_withIdle, Deklaration.mitRuhe]
    with_unfolding_all exact (congrArg (quantL false (frei Γ reserve) dest (D.count t))
      (lowE_withIdle L reserve currentOld body (dest + 3)))
  | Γ, _, _, .count n body, dest => by
    simp only [lowE, ruE, lowEWith, specLookup, frei_withIdle]
    with_unfolding_all exact (congrArg (countL (frei Γ reserve) dest n)
      (lowE_withIdle L reserve currentOld body (dest + 3)))
  | _, _, _, .reaches _ _ _ a b _, _ => by
    have left := lowE_withIdle L reserve currentOld a
    have right := lowE_withIdle L reserve currentOld b
    simp only [lowE, tyR, Ty.mapNumbers] at left right
    simp only [lowE, ruE, lowEWith, reachesL_withIdle, tyR, Ty.mapNumbers, left, right]
  | _, _, _, .wenn cond a b, _ => by
    have test := lowE_withIdle L reserve currentOld cond
    have left := lowE_withIdle L reserve currentOld a
    have right := lowE_withIdle L reserve currentOld b
    simp only [lowE, tyR, Ty.mapNumbers] at test left right
    simp only [lowE, ruE, lowEWith, tyR, Ty.mapNumbers, test, left, right]
  | _, _, _, .arrGet a i, _ => by
    have address := lowStorage_withIdle L reserve currentOld a
    have array := lowE_withIdle L reserve currentOld a
    have index := lowE_withIdle L reserve currentOld i
    simp only [lowE, lowStorage, tyR, Ty.mapNumbers] at address array index
    have stored := storedExpr_ru a
    simp only [lowE, ruE, lowEWith, stored, arrReadL, arrGetL,
      tyR, Ty.mapNumbers, valueWords_mapNumbers, valueWords, address, array, index]
    split
    · next present =>
      have same : storedExpr a = true := by exact stored.symm.trans present
      rw [ite_eq_left same]
    · next absent =>
      have same : ¬ storedExpr a = true := fun yes => absent (stored.trans yes)
      rw [ite_eq_right same]
  | _, _, _, .arrSet a i v, _ => by
    have array := lowE_withIdle L reserve currentOld a
    have index := lowE_withIdle L reserve currentOld i
    have value := lowE_withIdle L reserve currentOld v
    simp only [lowE, tyR, Ty.mapNumbers] at array index value
    simp only [lowE, ruE, lowEWith, arrSetL, tyR, Ty.mapNumbers, valueWords_mapNumbers, valueWords, array, index, value]
  | _, _, _, .prodGet v field, _ => by
    have value := lowE_withIdle L reserve currentOld v
    simp only [lowE, tyR, Ty.mapNumbers] at value
    simp only [lowE, ruE, lowEWith, prodGetL, productOffset_withIdle,
      tyR, Ty.mapNumbers, valueWords_mapNumbers, productWords_mapFields, valueWords, value]
  | _, _, _, .prodSet v field next, _ => by
    have source := lowE_withIdle L reserve currentOld v
    have value := lowE_withIdle L reserve currentOld next
    simp only [lowE, tyR, Ty.mapNumbers] at source value
    simp only [lowE, ruE, lowEWith, prodSetL, productOffset_withIdle,
      tyR, Ty.mapNumbers, valueWords_mapNumbers, productWords_mapFields, valueWords, source, value]
  | _, _, _, .prod _ args, dst => by
    have mapped := (lowProdArgs_types (Ty.map_eq_mapFields (· + 1) id _) (ruA args) L.withIdle dst reserve currentOld).trans
      (lowProdArgs_withIdle L reserve currentOld args dst)
    simp only [lowProdArgs] at mapped
    simp only [lowE, ruE, lowEWith, mapped]
  | _, _, _, .case cases tag payload, dst => by
    let cast := (Ty.mapCases_get (· + 1) id cases tag).symm
    have compact := (lowN_kind cast (ruN payload) L.withIdle tag.val dst reserve currentOld).trans
      (lowN_withIdle L reserve currentOld payload tag.val dst)
    have full := (lowPayload_kind cast (ruN payload) L.withIdle
      (dst + integerWords 0 (cases.length - 1)) reserve currentOld).trans
      (lowPayload_withIdle L reserve currentOld payload (dst + integerWords 0 (cases.length - 1)))
    simp only [lowN, lowPayload, cast] at compact full
    simp only [lowE, ruE, lowEWith, Ty.mapCases_length, sumFits_mapNumbers, sumSpanL_withIdle, compact, full]
termination_by structural _ _ _ e _ => e

private theorem lowStorage_withIdle (L : Lay D) (reserve : Nat) (currentOld : Bool) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (dst : Nat),
      lowStorage L.withIdle (ruE e) dst reserve currentOld = lowStorage L e dst reserve currentOld
  | _, _, _, .var x, _ => by simp only [lowStorage, ruE, lowStorageWith, specLookup, vslot_varR]
  | _, _, _, .glob .., _ => rfl
  | _, _, _, .slot _ _ i _, _ | _, _, _, .thru _ _ _ _ i _, _
  | _, _, _, .thruOwn _ _ _ _ i _ _ _ _ _ _, _ | _, _, _, .slotRef i _ _ _ _ _, _ => by
    have mapped := lowE_withIdle L reserve currentOld i
    simp only [lowE, tyR, Ty.mapNumbers] at mapped
    simp only [lowStorage, ruE, lowStorageWith, cellAddressC_withIdle, tyR, Ty.mapNumbers, mapped]
  | _, _, _, .lit .., _ | _, _, _, .tru .., _ | _, _, _, .fls .., _
  | _, _, _, .ptrOf .., _ | _, _, _, .fnref .., _ | _, _, _, .refEq .., _
  | _, _, _, .oldG .., _ | _, _, _, .oldS .., _ | _, _, _, .widen .., _
  | _, _, _, .add .., _ | _, _, _, .sub .., _ | _, _, _, .neg .., _
  | _, _, _, .mul .., _ | _, _, _, .div .., _ | _, _, _, .rem .., _
  | _, _, _, .sdiv .., _ | _, _, _, .srem .., _ | _, _, _, .getBytes .., _
  | _, _, _, .band .., _ | _, _, _, .bor .., _ | _, _, _, .bxor .., _
  | _, _, _, .shl .., _ | _, _, _, .shr .., _ | _, _, _, .lt .., _
  | _, _, _, .le .., _ | _, _, _, .eq .., _ | _, _, _, .fllt .., _
  | _, _, _, .flle .., _ | _, _, _, .and .., _ | _, _, _, .or .., _
  | _, _, _, .not .., _ | _, _, _, .none .., _ | _, _, _, .some .., _
  | _, _, _, .istSome .., _ | _, _, _, .case .., _ | _, _, _, .why .., _
  | _, _, _, .forallSlots .., _ | _, _, _, .existsSlots .., _ | _, _, _, .reaches .., _
  | _, _, _, .arrNil .., _ | _, _, _, .arrCons .., _ | _, _, _, .arrGet .., _
  | _, _, _, .arrSet .., _ | _, _, _, .strLit .., _ | _, _, _, .strLen .., _
  | _, _, _, .strCat .., _ | _, _, _, .strGet .., _ | _, _, _, .strEq .., _
  | _, _, _, .strLt .., _ | _, _, _, .strWeit .., _ | _, _, _, .wenn .., _
  | _, _, _, .eng .., _ | _, _, _, .intBuiltin1 .., _ | _, _, _, .intBuiltin2 .., _
  | _, _, _, .count .., _ | _, _, _, .prod .., _ | _, _, _, .prodGet .., _
  | _, _, _, .prodSet .., _ => rfl
termination_by structural _ _ _ e _ => e

private theorem lowPayload_withIdle (L : Lay D) (reserve : Nat) (currentOld : Bool) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option Ty} (p : NutzlastExpr D Γ Λ c) (dst : Nat),
      lowPayload L.withIdle (ruN p) dst reserve currentOld = lowPayload L p dst reserve currentOld
  | _, _, _, .empty, _ => rfl
  | _, _, _, .val value, dst => lowE_withIdle L reserve currentOld value dst
termination_by structural _ _ _ p _ => p

private theorem lowN_withIdle (L : Lay D) (reserve : Nat) (currentOld : Bool) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option Ty} (p : NutzlastExpr D Γ Λ c) (tag dst : Nat),
      lowN L.withIdle tag (ruN p) dst reserve currentOld = lowN L tag p dst reserve currentOld
  | _, _, _, .empty, _, _ => rfl
  | _, _, _, .val (τ := τ) value, tag, dst => by
    have mapped := lowE_withIdle L reserve currentOld value dst
    simp only [lowE, tyR, Ty.mapNumbers] at mapped
    cases τ <;> simp only [lowN, ruN, lowNWith, Option.map_some, tyR, Ty.mapNumbers, mapped]
    case int lo _ =>
      let pack (code : Option (List II × Nat)) := do
        let child ← code
        pure (packSum dst lo tag child)
      with_unfolding_all exact (congrArg pack mapped)
termination_by structural _ _ _ p _ _ => p

private theorem lowProdArgs_withIdle (L : Lay D) (reserve : Nat) (currentOld : Bool) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {ts : List Ty} (args : Args D Γ Λ ts) (dst : Nat),
      lowProdArgs L.withIdle (ruA args) dst reserve currentOld = lowProdArgs L args dst reserve currentOld
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons (τ := τ) head tail, dst => by
    have value := lowE_withIdle L reserve currentOld head dst
    have rest := lowProdArgs_withIdle L reserve currentOld tail (dst + valueWords τ)
    simp only [lowE, lowProdArgs] at value rest
    simp only [lowProdArgs, ruA, lowProdArgsWith, tyR, valueWords_mapNumbers, value, rest]
termination_by structural _ _ _ args _ => args
end

end Gabbro.Stage0.Senke
