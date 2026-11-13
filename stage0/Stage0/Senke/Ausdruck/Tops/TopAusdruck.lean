module
public import Stage0.Senke.Ausdruck.Tops.TopBasis
@[expose] public section

variable {currentOld : Bool}


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem lowE_top_prodSet {name : Nat} {fs : List Ty} {σ : Ty}
    (i : FieldAt fs σ) (d : Nat) (v e : Option (List II × Nat))
    (c : List II) (top : Nat)
    (h : prodSetL (name := name) i d v e = some (c, top)) : d < top := by
  simp only [prodSetL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨cv, tv⟩, hv, ⟨ce, te⟩, he, _, rfl⟩ := h
  have positive := valueWords_pos σ
  have bound := Nat.le_max_right (max tv te)
    (d + valueWords (.prod name fs) + valueWords σ)
  omega

theorem lowE_top_prodGet {reserved : Nat} {Λ : List (Res D)} {Γ : Ctx}
    {name : Nat} {fs : List Ty} {σ : Ty} (i : FieldAt fs σ)
    (v : Expr D Γ Λ (.prod name fs)) (d : Nat) (c : List II) (top : Nat)
    (h : prodGetL (name := name) i d (lowE (currentOld := currentOld) L (reserved := reserved) v d) = some (c, top)) :
    d < top := by
  simp only [prodGetL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨cv, tv⟩, hv, _, rfl⟩ := h
  have positive := valueWords_pos σ
  have bound := Nat.le_max_right (max tv (d + valueWords (.prod name fs))) (d + valueWords σ)
  omega

theorem lowE_top {reserved : Nat} {Λ : List (Res D)} : {Γ : Ctx} → {τ : Ty} → (e : Expr D Γ Λ τ) → (d : Nat) → (c : List II) →
    (top : Nat) → lowE (currentOld := currentOld) L (reserved := reserved) e d = some (c, top) → d < top
  | _, _, .arrNil, d, c, top, h => by
    simp only [lowE_eqs, Option.some.injEq, Prod.mk.injEq] at h; omega
  | _, _, .arrCons a rest, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact lowE_top a d c top h
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, _, _, rfl⟩ := h
      have := lowE_top a d ca ta ha
      omega
  | _, _, .arrGet a _, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact arrReadL_top h
    · split at h
      · exact lowE_top a d c top h
      · simp only [arrGetL] at h
        split at h
        · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, _, _, rfl⟩ := h
          have := lowE_top a d ca ta ha
          omega
        · cases h
  | _, _, .arrSet a i v, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact lowE_top v d c top h
    · simp only [arrSetL] at h
      split at h
      · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨ca, ta⟩, ha, ⟨cv, tv⟩, hv, ⟨ci, ti⟩, hi, _, rfl⟩ := h
        have := lowE_top a d ca ta ha
        omega
      · cases h
  | _, _, @Expr.strLit _ n _ _ bs hb, d, c, top, h => by
    simp only [lowE_eqs, Option.some.injEq] at h
    have ceiling := congrArg Prod.snd h
    dsimp only at ceiling
    have span := constWords_span (encodeWords L (.str n) ⟨bs, hb⟩) d
    have width := encodeWords_length L (.str n) ⟨bs, hb⟩
    have positive := valueWords_pos (.str n)
    omega
  | _, _, .strLen s, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact wordL_top h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨cs, ts⟩, hs, out⟩ := h
      cases out
      have := lowE_top s d cs ts hs
      omega
  | _, _, .strEq s t, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact wordL_top h
    · split at h
      · simp only [strEqMixedL] at h
        split at h
        · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨cs, ts⟩, hs, ⟨ct, tt⟩, ht, _, rfl⟩ := h
          omega
        · split at h
          · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨cs, ts⟩, hs, ⟨ct, tt⟩, ht, _, rfl⟩ := h
            omega
          · cases h
      · simp only [strEqLongL] at h
        split at h
        · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨cs, ts⟩, hs, ⟨ct, tt⟩, ht, _, rfl⟩ := h
          omega
        · cases h
  | _, _, .strLt _ _, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact wordL_top h
    · simp only [strLtSpanL] at h
      split at h
      · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨cs, ts⟩, _, ⟨ct, tt⟩, _, _, rfl⟩ := h
        omega
      · cases h
  | _, _, .strGet _ _, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact strGetL_top h
    · split at h
      · simp only [strGetWideL] at h
        split at h
        · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, _, _, _, rfl, rfl⟩ := h
          omega
        · cases h
      · cases h
  | _, _, .strCat s t, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · split at h
      · exact lowE_top t d c top h
      · exact lowE_top s d c top h
    · simp only [strCatSpanL] at h
      split at h
      · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨cs, ts⟩, _, ⟨ct, tt⟩, _, _, rfl⟩ := h
        omega
      · cases h
  | _, _, .strWeit _ s, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · exact lowE_top s d c top h
    · split at h
      · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨⟨cs, ts⟩, hs, rfl, rfl⟩ := h
        omega
      · split at h
        · simp only [strExpandL] at h
          split at h
          · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨cs, ts⟩, hs, rfl, rfl⟩ := h
            have := lowE_top s d cs ts hs
            omega
          · cases h
        · simp only [strTakeL] at h
          split at h
          · simp only [bind, Option.bind_eq_some_iff] at h
            obtain ⟨⟨cs, ts⟩, hs, h⟩ := h
            have := lowE_top s d cs ts hs
            split at h
            · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h; omega
            · split at h <;> (simp only [pure, Option.some.injEq, Prod.mk.injEq] at h; omega)
          · cases h
  | _, _, .widen _ _ e, d, c, top, h =>
    resizeIntegerL_top h (fun cc tt hc => lowE_top e d cc tt hc)
  | _, _, .some e, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact lowE_top e d c top h
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨ce, te⟩, he, _, rfl⟩ := h
      have := lowE_top e (d + 1) ce te he
      omega
  | _, _, .refEq a b, d, c, top, h => wordL_top h
  | _, _, .and a b, d, c, top, h | _, _, .or a b, d, c, top, h =>
    bin_top (fun c t h => lowE_top a d c t h) h
  | _, _, .lt a b, d, c, top, h | _, _, .eq a b, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact scalarCompareL_top (fun c t h => lowE_top a d c t h) h
    · exact wideBinaryL_top h
  | _, _, .div _ _ a b, d, c, top, h
  | _, _, .add a b, d, c, top, h | _, _, .sub a b, d, c, top, h | _, _, .mul a b, d, c, top, h
  | _, _, .rem _ _ a b, d, c, top, h | _, _, .sdiv _ a b, d, c, top, h | _, _, .srem _ a b, d, c, top, h
  | _, _, .band _ _ a b, d, c, top, h
  | _, _, .shr _ _ _ _ _ a b, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact bin_top (fun c t h => lowE_top a d c t h) h
    · exact wideBinaryL_top h
  | _, _, .bor _ _ _ _ _ a b, d, c, top, h | _, _, .bxor _ _ _ _ _ a b, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact resizeIntegerL_top h (fun cc tt hc => bin_top (fun c t h => lowE_top a d c t h) hc)
    · exact wideBinaryL_top h
  | _, _, .shl _ _ _ _ _ a b, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact bin_top (fun c t h => lowE_top a d c t h) h
    · exact wideBinaryL_top h
  | _, _, .fllt a b, d, c, top, h | _, _, .flle a b, d, c, top, h => by
    simp only [lowE_eqs] at h
    exact floatExprL_top h
  | _, _, .neg a, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ca, ta⟩, _, he⟩ := h
      simp only [bin2, Prod.mk.injEq] at he
      omega
    · exact wideUnaryL_top h
  | _, _, .not a, d, c, top, h => by
    simp only [lowE_eqs, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, _, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    omega
  | _, _, .istSome e, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ce, te⟩, _, he⟩ := h
      simp only [bin2, Prod.mk.injEq] at he
      omega
    · exact lowE_top e d c top h
  | _, _, .le a b, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨cc, tc⟩, _, h⟩ := h
      simp only [bin2, Prod.mk.injEq] at h
      omega
    · exact wideBinaryL_top h
  | _, _, .lit n, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · exact constValue_top (L := L) (τ := .int n n) ⟨n, by omega, by omega⟩ h
  | _, _, .why n r, d, c, top, h => constValue_top (L := L) (τ := .why n) r h
  | _, _, .none n, d, c, top, h => constValue_top (L := L) (τ := .opt n) none h
  | _, _, .fnref .., d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · cases h
  | _, τ, .var _, d, c, top, h => by
    simp only [lowE_eqs, Option.some.injEq, Prod.mk.injEq] at h
    have := valueWords_pos τ
    omega
  | _, _, .tru, d, c, top, h | _, _, .fls, d, c, top, h
  | _, _, .ptrOf .., d, c, top, h => by
    simp only [lowE_eqs, Option.some.injEq, Prod.mk.injEq] at h; omega
  | _, _, .glob g _, d, c, top, h => by
    simp only [lowE_eqs, globalValueC] at h
    split at h
    · have positive := valueWords_pos (D.gtyp g)
      simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · cases h
  | _, _, .slotRef i _ _ _ _ _, d, c, top, h
  | _, _, .slot _ _ i _, d, c, top, h | _, _, .thru _ _ _ _ i _, d, c, top, h | _, _, .thruOwn _ _ _ _ i _ _ _ _ _ _, d, c, top, h => by
    simp only [lowE_eqs, bind, Option.bind_eq_some_iff] at h
    obtain ⟨ci', _, hs⟩ := h
    simp only [slotValueC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨_, _, rfl, rfl⟩ := hs
    omega
  | _, _, .case cs i nutz, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact lowN_top nutz _ _ _ h
    · exact sumSpanL_top h
  | _, _, .wenn cond a b, d, c, top, h => by
    simp only [lowE_eqs, wennL, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨cc, tc⟩, hc, ⟨ca, ta⟩, _, ⟨cb, tb⟩, _, h⟩ := h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      have := lowE_top cond d cc tc hc
      omega
    · cases h
  | _, _, .eng e lo' hi' b, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · simp only [engL, bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨ce, te⟩, he, ⟨cb, tb⟩, _, ⟨ct, tt⟩, _, h⟩ := h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := lowE_top e d ce te he
        omega
      · cases h
    · exact wideEngL_top h
  | _, _, .getBytes t f _ n i _ _ _, d, c, top, h => by
    simp only [lowE_eqs] at h
    exact readBytesWideL_top h
  | _, _, .forallSlots .., d, c, top, h | _, _, .existsSlots .., d, c, top, h => by
    simp only [lowE_eqs, quantL] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨cb, _, h⟩ := h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · cases h
  | _, _, .reaches .., d, c, top, h => by
    simp only [lowE_eqs, reachesL, bind, Option.bind_eq_some_iff] at h
    obtain ⟨ca, _, cb, _, h⟩ := h
    split at h
    · exact reachL_top _ _ _ h
    · cases h
  | _, _, .count .., d, c, top, h => (countL_bounds h).1
  | _, _, .prod _ args, d, c, top, h => lowE_top_prod d _ c top h
  | _, _, .prodGet v i, d, c, top, h => lowE_top_prodGet i v d c top h
  | _, _, .prodSet v i e, d, c, top, h => lowE_top_prodSet i d _ _ c top h
  | _, _, .intBuiltin2 op a b, d, c, top, h => intBuiltin2L_top op h
  | _, _, .intBuiltin1 op a, d, c, top, h => BitBuiltin.unary_top op h
  | _, _, .oldG g _, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · simp only [globalValueC] at h
      split at h
      · have positive := valueWords_pos (D.gtyp g)
        simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · cases h
    · cases h
  | _, _, .oldS t f i _, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨index, _, made⟩ := h
      simp only [slotValueC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at made
      obtain ⟨_, _, rfl, rfl⟩ := made
      omega
    · cases h



end Gabbro.Stage0.Senke
