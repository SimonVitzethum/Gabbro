module

public import Bruecke.Kodierung
public import Bruecke.Pflichten
public import Bruecke.Ausdruck.Teil1
public import Bruecke.Ausdruck.Glob

@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

/-! ## 3. Sides: the typed value lowering, in the bridge's fragment -/

/-- **A side with a Body form lowers to a number** (`lowWertE` answers `ls.wert`), and the Body
    term evaluates to the number the G term does. -/
theorem lowWertE_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {er : Option Ty}
    {sd : USide} {wv : LowWert u Γ Λ} {eB : Gabbro.Body.Expr}
    (h : lowWertE u Γ Λ fn er sd = .ok wv) (hb : numericSideExprG u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WGRel u σ w) (hL : LRel fn (if er.isSome then 1 else 0) ρ β) :
    ∃ ls : LowSide u Γ Λ, wv = ls.wert ∧
      Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf (.int ls.range.1 ls.range.2) (eval σ₀ ls.term σ ρ)) := by
  have recurse (sd' : USide) (hlt : sizeOf sd' < sizeOf sd)
      {wv' : LowWert u Γ Λ} {eB' : Gabbro.Body.Expr}
      (h' : lowWertE u Γ Λ fn er sd' = .ok wv')
      (hb' : numericSideExprG u fn sd' = some eB') :=
    lowWertE_sim h' hb' hA hT σ₀ σ ρ w β hW hL
  cases sd with
  | lit n =>
    simp only [lowWertE, Except.ok.injEq] at h
    subst h
    simp only [numericSideExprG, Option.some.injEq] at hb
    subst hb
    exact ⟨_, rfl, rfl⟩
  | param p =>
    have hN : numericParam fn p = true := by
      simp only [numericSideExprG] at hb
      split at hb
      · assumption
      · cases hb
    cases hpw : lowParamWert u Γ Λ fn (if er.isSome then 1 else 0) p with
    | none =>
      simp only [lowWertE, hpw] at h
      cases hp : lowParamSide u Γ Λ fn (if er.isSome then 1 else 0) p with
      | error e => simp [hp, Except.map] at h
      | ok ls =>
        simp only [hp, Except.map, Except.ok.injEq] at h
        subst h
        simp only [numericSideExprG, hN, ↓reduceIte, Option.some.injEq] at hb
        subst hb
        refine ⟨ls, rfl, ?_⟩
        simp only [Gabbro.Body.eval]
        rw [lowParamSide_sim hp σ₀ σ ρ β hL]
    | some answer =>
      simp only [lowWertE, hpw] at h
      subst answer
      unfold lowParamWert at hpw
      cases hj : paramPos fn.params p with
      | error err => simp [hj] at hpw
      | ok j =>
        have hn := hN
        unfold numericParam at hn
        rw [paramPos_find _ _ _ hj] at hn
        cases ht : fn.params[j]? with
        | none => simp [ht] at hn
        | some q =>
          rcases q with ⟨name, ty⟩
          cases ty <;> try { simp [ht] at hn }
          case int lo hi =>
            cases hk : fn.kinds[j]? with
            | none => simp [hj, ht, hk] at hpw
            | some k =>
              cases k <;> simp only [hj, ht, hk] at hpw
              all_goals first
                | (cases hpw; done)
                | (cases hv : lowVar Γ ((if er.isSome then 1 else 0) + j) (.int lo hi) with
                  | error err => simp [hv] at hpw
                  | ok v =>
                    simp only [hv, Option.some.injEq, Except.ok.injEq] at hpw
                    cases hpw
                    simp only [numericSideExprG, hN, ↓reduceIte, Option.some.injEq] at hb
                    subst eB
                    refine ⟨{ range := (lo, hi)
                              term := Expr.var v }, rfl, ?_⟩
                    simp only [Gabbro.Body.eval]
                    rw [hL p j hj, nthVal_lowVar Γ _ _ v ρ hv]
                    rfl)
  | slot b f ix =>
    simp only [lowWertE, lowDurchWert_none hT] at h
    cases hd : lowDurch u Γ Λ fn (if er.isSome then 1 else 0) b f ix with
    | error e => simp [hd, Except.map] at h
    | ok ls =>
      simp only [hd, Except.map, Except.ok.injEq] at h
      subst h
      obtain ⟨c, hc, hv⟩ := lowDurch_sim hd hA hT σ₀ σ ρ w β hW.1 hL
      simp only [numericSideExprG, slotPlace, hc, Option.map_some, Option.some.injEq] at hb
      subst hb
      exact ⟨ls, rfl, hv⟩
  | tab b f ix =>
    simp only [lowWertE, lowTabWert_none hT] at h
    cases hd : lowTabRead u Γ Λ fn (if er.isSome then 1 else 0) b f ix with
    | error e => simp [hd, Except.map] at h
    | ok ls =>
      simp only [hd, Except.map, Except.ok.injEq] at h
      subst h
      simp only [numericSideExprG, slotPlace, Option.some.injEq] at hb
      subst hb
      exact ⟨ls, rfl, lowTabRead_sim hd σ₀ σ ρ w β hW.1 hL⟩
  | glob g =>
    simp only [numericSideExprG] at hb
    split at hb
    · cases hb
    · rename_i i hi
      cases ht : (globAt u i).ty with
      | int lo hi' =>
        simp only [ht, Option.some.injEq] at hb
        subst eB
        have hn : lowGlobWert u Γ Λ g = none := by
          simp only [lowGlobWert, hi, ht]
        simp only [lowWertE, hn] at h
        cases hg : lowGlobSide u Γ Λ g with
        | error err => simp only [hg, Except.map, reduceCtorEq] at h
        | ok ls =>
          simp only [hg, Except.map, Except.ok.injEq] at h
          subst wv
          exact ⟨ls, rfl, lowGlobRead_sim hg σ₀ σ ρ w β hW.2⟩
      | bool => simp only [ht, reduceCtorEq] at hb
      | wert ty => simp only [ht, reduceCtorEq] at hb
  | add x y =>

    cases hsx : numericSideExprG u fn x with
    | none => simp [numericSideExprG, hsx, binE] at hb
    | some ex =>
      cases hsy : numericSideExprG u fn y with
      | none => simp [numericSideExprG, hsx, hsy, binE] at hb
      | some ey =>
        simp only [numericSideExprG, hsx, hsy, binE, Option.some.injEq] at hb
        subst hb
        cases hx : lowWertE u Γ Λ fn er x with
        | error e => simp [lowWertE, zahlVon, lowZwei, hx, Except.map] at h
        | ok wa =>
          obtain ⟨lx, rfl, h1⟩ := recurse x (by simp_wf; omega) hx hsx
          simp only [LowSide.wert] at hx
          cases hy : lowWertE u Γ Λ fn er y with
          | error e => simp [lowWertE, zahlVon, lowZwei, LowWert.zahl, hx, hy, Except.map] at h
          | ok wb =>
            obtain ⟨ly, rfl, h2⟩ := recurse y (by simp_wf; omega) hy hsy
            simp only [LowSide.wert] at hy
            simp only [lowWertE, hx, hy, Except.ok.injEq] at h
            subst h
            refine ⟨_, rfl, ?_⟩
            show Gabbro.Body.eval ⟨w, β⟩ (.bin .add ex ey) = _
            rw [show Gabbro.Body.eval ⟨w, β⟩ (.bin .add ex ey) =
              (match Gabbro.Body.eval ⟨w, β⟩ ex, Gabbro.Body.eval ⟨w, β⟩ ey with
                | some x, some y => Gabbro.Body.binop .add x y
                | _, _ => none) from rfl]
            rw [h1, h2]
            rfl
  | sub x y =>
    cases hsx : numericSideExprG u fn x with
    | none => simp [numericSideExprG, hsx, binE] at hb
    | some ex =>
      cases hsy : numericSideExprG u fn y with
      | none => simp [numericSideExprG, hsx, hsy, binE] at hb
      | some ey =>
        simp only [numericSideExprG, hsx, hsy, binE, Option.some.injEq] at hb
        subst hb
        cases hx : lowWertE u Γ Λ fn er x with
        | error e => simp [lowWertE, zahlVon, lowZwei, hx, Except.map] at h
        | ok wa =>
          obtain ⟨lx, rfl, h1⟩ := recurse x (by simp_wf; omega) hx hsx
          simp only [LowSide.wert] at hx
          cases hy : lowWertE u Γ Λ fn er y with
          | error e => simp [lowWertE, zahlVon, lowZwei, LowWert.zahl, hx, hy, Except.map] at h
          | ok wb =>
            obtain ⟨ly, rfl, h2⟩ := recurse y (by simp_wf; omega) hy hsy
            simp only [LowSide.wert] at hy
            simp only [lowWertE, zahlVon, hx, hy, LowWert.zahl, Except.ok.injEq] at h
            subst h
            refine ⟨_, rfl, ?_⟩
            show Gabbro.Body.eval ⟨w, β⟩ (.bin .sub ex ey) = _
            rw [show Gabbro.Body.eval ⟨w, β⟩ (.bin .sub ex ey) =
              (match Gabbro.Body.eval ⟨w, β⟩ ex, Gabbro.Body.eval ⟨w, β⟩ ey with
                | some x, some y => Gabbro.Body.binop .sub x y
                | _, _ => none) from rfl]
            rw [h1, h2]
            rfl
  | mul x y =>
    cases hsx : numericSideExprG u fn x with
    | none => simp [numericSideExprG, hsx, binE] at hb
    | some ex =>
      cases hsy : numericSideExprG u fn y with
      | none => simp [numericSideExprG, hsx, hsy, binE] at hb
      | some ey =>
        simp only [numericSideExprG, hsx, hsy, binE, Option.some.injEq] at hb
        subst hb
        cases hx : lowWertE u Γ Λ fn er x with
        | error e => simp [lowWertE, zahlVon, lowZwei, hx, Except.map] at h
        | ok wa =>
          obtain ⟨lx, rfl, h1⟩ := recurse x (by simp_wf; omega) hx hsx
          simp only [LowSide.wert] at hx
          cases hy : lowWertE u Γ Λ fn er y with
          | error e => simp [lowWertE, zahlVon, lowZwei, LowWert.zahl, hx, hy, Except.map] at h
          | ok wb =>
            obtain ⟨ly, rfl, h2⟩ := recurse y (by simp_wf; omega) hy hsy
            simp only [LowSide.wert] at hy
            simp only [lowWertE, zahlVon, hx, hy, LowWert.zahl, Except.ok.injEq] at h
            subst h
            refine ⟨_, rfl, ?_⟩
            show Gabbro.Body.eval ⟨w, β⟩ (.bin .mul ex ey) = _
            rw [show Gabbro.Body.eval ⟨w, β⟩ (.bin .mul ex ey) =
              (match Gabbro.Body.eval ⟨w, β⟩ ex, Gabbro.Body.eval ⟨w, β⟩ ey with
                | some x, some y => Gabbro.Body.binop .mul x y
                | _, _ => none) from rfl]
            rw [h1, h2]
            rfl
  | conv lo hi x =>
    have hb' : numericSideExprG u fn x = some eB := hb
    cases hx : lowWertE u Γ Λ fn er x with
    | error e => simp [lowWertE, zahlVon, hx, Except.map] at h
    | ok wa =>
      obtain ⟨lx, rfl, h1⟩ := recurse x (by simp_wf; omega) hx hb'
      simp only [LowSide.wert] at hx
      simp only [lowWertE, zahlVon, hx, LowWert.zahl] at h
      unfold LowSide.conv at h
      split at h
      · split at h
        · simp only [Except.map, Except.ok.injEq] at h
          subst h
          refine ⟨_, rfl, ?_⟩
          rw [h1]
          rfl
        · simp [Except.map] at h
      · simp [Except.map] at h
  | band x y =>
    cases hsx : numericSideExprG u fn x with
    | none => simp [numericSideExprG, hsx, binE] at hb
    | some ex =>
      cases hsy : numericSideExprG u fn y with
      | none => simp [numericSideExprG, hsx, hsy, binE] at hb
      | some ey =>
        simp only [numericSideExprG, hsx, hsy, binE, Option.some.injEq] at hb
        subst hb
        cases hx : lowWertE u Γ Λ fn er x with
        | error e => simp [lowWertE, zahlVon, lowZwei, hx, Except.map] at h
        | ok wa =>
          obtain ⟨lx, rfl, h1⟩ := recurse x (by simp_wf; omega) hx hsx
          simp only [LowSide.wert] at hx
          cases hy : lowWertE u Γ Λ fn er y with
          | error e => simp [lowWertE, zahlVon, lowZwei, LowWert.zahl, hx, hy, Except.map] at h
          | ok wb =>
            obtain ⟨ly, rfl, h2⟩ := recurse y (by simp_wf; omega) hy hsy
            simp only [LowSide.wert] at hy
            simp only [lowWertE, zahlVon, lowZwei, hx, hy, LowWert.zahl] at h
            unfold LowSide.and at h
            split at h
            · rename_i h0
              split at h
              · rename_i h0'
                simp only [Except.map, Except.ok.injEq] at h
                subst h
                refine ⟨_, rfl, ?_⟩
                have ha : 0 ≤ (eval σ₀ lx.term σ ρ : Zahl lx.range.1 lx.range.2).n :=
                  Int.le_trans h0 (eval σ₀ lx.term σ ρ : Zahl lx.range.1 lx.range.2).lo_le
                have hb0 : 0 ≤ (eval σ₀ ly.term σ ρ : Zahl ly.range.1 ly.range.2).n :=
                  Int.le_trans h0' (eval σ₀ ly.term σ ρ : Zahl ly.range.1 ly.range.2).lo_le
                show Gabbro.Body.eval ⟨w, β⟩ (.bin .band ex ey) = _
                rw [show Gabbro.Body.eval ⟨w, β⟩ (.bin .band ex ey) =
                  (match Gabbro.Body.eval ⟨w, β⟩ ex, Gabbro.Body.eval ⟨w, β⟩ ey with
                    | some x, some y => Gabbro.Body.binop .band x y
                    | _, _ => none) from rfl]
                rw [h1, h2]
                simp only [valOf_int, Gabbro.Body.binop, Gabbro.Body.bits, if_pos (And.intro ha hb0)]
                rfl
              · simp [Except.map] at h
            · simp [Except.map] at h
  | bor x y =>
    cases hsx : numericSideExprG u fn x with
    | none => simp [numericSideExprG, hsx, binE] at hb
    | some ex =>
      cases hsy : numericSideExprG u fn y with
      | none => simp [numericSideExprG, hsx, hsy, binE] at hb
      | some ey =>
        simp only [numericSideExprG, hsx, hsy, binE, Option.some.injEq] at hb
        subst hb
        cases hx : lowWertE u Γ Λ fn er x with
        | error e => simp [lowWertE, zahlVon, lowZwei, hx, Except.map] at h
        | ok wa =>
          obtain ⟨lx, rfl, h1⟩ := recurse x (by simp_wf; omega) hx hsx
          simp only [LowSide.wert] at hx
          cases hy : lowWertE u Γ Λ fn er y with
          | error e => simp [lowWertE, zahlVon, lowZwei, LowWert.zahl, hx, hy, Except.map] at h
          | ok wb =>
            obtain ⟨ly, rfl, h2⟩ := recurse y (by simp_wf; omega) hy hsy
            simp only [LowSide.wert] at hy
            simp only [lowWertE, zahlVon, lowZwei, hx, hy, LowWert.zahl] at h
            unfold LowSide.or at h
            split at h
            · rename_i h0
              split at h
              · rename_i h0'
                split at h
                · rename_i hw1
                  split at h
                  · rename_i hw2
                    simp only [Except.map, Except.ok.injEq] at h
                    subst h
                    refine ⟨_, rfl, ?_⟩
                    have ha : 0 ≤ (eval σ₀ lx.term σ ρ : Zahl lx.range.1 lx.range.2).n :=
                      Int.le_trans h0 (eval σ₀ lx.term σ ρ : Zahl lx.range.1 lx.range.2).lo_le
                    have hb0 : 0 ≤ (eval σ₀ ly.term σ ρ : Zahl ly.range.1 ly.range.2).n :=
                      Int.le_trans h0' (eval σ₀ ly.term σ ρ : Zahl ly.range.1 ly.range.2).lo_le
                    show Gabbro.Body.eval ⟨w, β⟩ (.bin .bor ex ey) = _
                    rw [show Gabbro.Body.eval ⟨w, β⟩ (.bin .bor ex ey) =
                      (match Gabbro.Body.eval ⟨w, β⟩ ex, Gabbro.Body.eval ⟨w, β⟩ ey with
                        | some x, some y => Gabbro.Body.binop .bor x y
                        | _, _ => none) from rfl]
                    rw [h1, h2]
                    simp only [valOf_int, Gabbro.Body.binop, Gabbro.Body.bits, if_pos (And.intro ha hb0)]
                    rfl
                  · simp [Except.map] at h
                · simp [Except.map] at h
              · simp [Except.map] at h
            · simp [Except.map] at h
  | bxor x y =>
    cases hsx : numericSideExprG u fn x with
    | none => simp [numericSideExprG, hsx, binE] at hb
    | some ex =>
      cases hsy : numericSideExprG u fn y with
      | none => simp [numericSideExprG, hsx, hsy, binE] at hb
      | some ey =>
        simp only [numericSideExprG, hsx, hsy, binE, Option.some.injEq] at hb
        subst hb
        cases hx : lowWertE u Γ Λ fn er x with
        | error e => simp [lowWertE, zahlVon, lowZwei, hx, Except.map] at h
        | ok wa =>
          obtain ⟨lx, rfl, h1⟩ := recurse x (by simp_wf; omega) hx hsx
          simp only [LowSide.wert] at hx
          cases hy : lowWertE u Γ Λ fn er y with
          | error e => simp [lowWertE, zahlVon, lowZwei, LowWert.zahl, hx, hy, Except.map] at h
          | ok wb =>
            obtain ⟨ly, rfl, h2⟩ := recurse y (by simp_wf; omega) hy hsy
            simp only [LowSide.wert] at hy
            simp only [lowWertE, zahlVon, lowZwei, hx, hy, LowWert.zahl] at h
            unfold LowSide.xoder at h
            split at h
            · rename_i h0
              split at h
              · rename_i h0'
                split at h
                · rename_i hw1
                  split at h
                  · rename_i hw2
                    simp only [Except.map, Except.ok.injEq] at h
                    subst h
                    refine ⟨_, rfl, ?_⟩
                    have ha : 0 ≤ (eval σ₀ lx.term σ ρ : Zahl lx.range.1 lx.range.2).n :=
                      Int.le_trans h0 (eval σ₀ lx.term σ ρ : Zahl lx.range.1 lx.range.2).lo_le
                    have hb0 : 0 ≤ (eval σ₀ ly.term σ ρ : Zahl ly.range.1 ly.range.2).n :=
                      Int.le_trans h0' (eval σ₀ ly.term σ ρ : Zahl ly.range.1 ly.range.2).lo_le
                    show Gabbro.Body.eval ⟨w, β⟩ (.bin .bxor ex ey) = _
                    rw [show Gabbro.Body.eval ⟨w, β⟩ (.bin .bxor ex ey) =
                      (match Gabbro.Body.eval ⟨w, β⟩ ex, Gabbro.Body.eval ⟨w, β⟩ ey with
                        | some x, some y => Gabbro.Body.binop .bxor x y
                        | _, _ => none) from rfl]
                    rw [h1, h2]
                    simp only [valOf_int, Gabbro.Body.binop, Gabbro.Body.bits, if_pos (And.intro ha hb0)]
                    rfl
                  · simp [Except.map] at h
                · simp [Except.map] at h
              · simp [Except.map] at h
            · simp [Except.map] at h
  | _ => simp [numericSideExprG] at hb
termination_by sizeOf sd
decreasing_by assumption

end Gabbro.Bruecke
