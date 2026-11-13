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
    (h : lowWertE u Γ Λ fn er sd = .ok wv) (hb : sideExprG u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WGRel u σ w) (hL : LRel fn (if er.isSome then 1 else 0) ρ β) :
    ∃ ls : LowSide u Γ Λ, wv = ls.wert ∧
      Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf (.int ls.range.1 ls.range.2) (eval σ₀ ls.term σ ρ)) := by
  have recurse (sd' : USide) (hlt : sizeOf sd' < sizeOf sd)
      {wv' : LowWert u Γ Λ} {eB' : Gabbro.Body.Expr}
      (h' : lowWertE u Γ Λ fn er sd' = .ok wv')
      (hb' : sideExprG u fn sd' = some eB') :=
    lowWertE_sim h' hb' hA hT σ₀ σ ρ w β hW hL
  cases sd with
  | lit n =>
    simp only [lowWertE, Except.ok.injEq] at h
    subst h
    simp only [sideExprG, Option.some.injEq] at hb
    subst hb
    exact ⟨_, rfl, rfl⟩
  | param p =>
    have hN : numericParam fn p = true := by
      simp only [sideExprG] at hb
      split at hb
      · assumption
      · cases hb
    simp only [lowWertE, lowParamWert_none hA hN] at h
    cases hp : lowParamSide u Γ Λ fn (if er.isSome then 1 else 0) p with
    | error e => simp [hp, Except.map] at h
    | ok ls =>
      simp only [hp, Except.map, Except.ok.injEq] at h
      subst h
      simp only [sideExprG, hN, ↓reduceIte, Option.some.injEq] at hb
      subst hb
      refine ⟨ls, rfl, ?_⟩
      simp only [Gabbro.Body.eval]
      rw [lowParamSide_sim hp σ₀ σ ρ β hL]
  | slot b f ix =>
    simp only [lowWertE, lowDurchWert_none hT] at h
    cases hd : lowDurch u Γ Λ fn (if er.isSome then 1 else 0) b f ix with
    | error e => simp [hd, Except.map] at h
    | ok ls =>
      simp only [hd, Except.map, Except.ok.injEq] at h
      subst h
      obtain ⟨c, hc, hv⟩ := lowDurch_sim hd hA hT σ₀ σ ρ w β hW.1 hL
      simp only [sideExprG, slotPlace, hc, Option.map_some, Option.some.injEq] at hb
      subst hb
      exact ⟨ls, rfl, hv⟩
  | tab b f ix =>
    simp only [lowWertE, lowTabWert_none hT] at h
    cases hd : lowTabRead u Γ Λ fn (if er.isSome then 1 else 0) b f ix with
    | error e => simp [hd, Except.map] at h
    | ok ls =>
      simp only [hd, Except.map, Except.ok.injEq] at h
      subst h
      simp only [sideExprG, slotPlace, Option.some.injEq] at hb
      subst hb
      exact ⟨ls, rfl, lowTabRead_sim hd σ₀ σ ρ w β hW.1 hL⟩
  | glob g =>
    simp only [sideExprG] at hb
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

    cases hsx : sideExprG u fn x with
    | none => simp [sideExprG, hsx, binE] at hb
    | some ex =>
      cases hsy : sideExprG u fn y with
      | none => simp [sideExprG, hsx, hsy, binE] at hb
      | some ey =>
        simp only [sideExprG, hsx, hsy, binE, Option.some.injEq] at hb
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
    cases hsx : sideExprG u fn x with
    | none => simp [sideExprG, hsx, binE] at hb
    | some ex =>
      cases hsy : sideExprG u fn y with
      | none => simp [sideExprG, hsx, hsy, binE] at hb
      | some ey =>
        simp only [sideExprG, hsx, hsy, binE, Option.some.injEq] at hb
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
    cases hsx : sideExprG u fn x with
    | none => simp [sideExprG, hsx, binE] at hb
    | some ex =>
      cases hsy : sideExprG u fn y with
      | none => simp [sideExprG, hsx, hsy, binE] at hb
      | some ey =>
        simp only [sideExprG, hsx, hsy, binE, Option.some.injEq] at hb
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
    have hb' : sideExprG u fn x = some eB := hb
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
    cases hsx : sideExprG u fn x with
    | none => simp [sideExprG, hsx, binE] at hb
    | some ex =>
      cases hsy : sideExprG u fn y with
      | none => simp [sideExprG, hsx, hsy, binE] at hb
      | some ey =>
        simp only [sideExprG, hsx, hsy, binE, Option.some.injEq] at hb
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
    cases hsx : sideExprG u fn x with
    | none => simp [sideExprG, hsx, binE] at hb
    | some ex =>
      cases hsy : sideExprG u fn y with
      | none => simp [sideExprG, hsx, hsy, binE] at hb
      | some ey =>
        simp only [sideExprG, hsx, hsy, binE, Option.some.injEq] at hb
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
    cases hsx : sideExprG u fn x with
    | none => simp [sideExprG, hsx, binE] at hb
    | some ex =>
      cases hsy : sideExprG u fn y with
      | none => simp [sideExprG, hsx, hsy, binE] at hb
      | some ey =>
        simp only [sideExprG, hsx, hsy, binE, Option.some.injEq] at hb
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
  | _ => simp [sideExprG] at hb
termination_by sizeOf sd
decreasing_by assumption

theorem lowSideVal_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {sd : USide} {ls : LowSide u Γ Λ} {eB : Gabbro.Body.Expr}
    (h : lowSideVal u Γ Λ fn sd = .ok ls) (hb : sideExprG u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WGRel u σ w) (hL : LRel fn 0 ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf (.int ls.range.1 ls.range.2) (eval σ₀ ls.term σ ρ)) := by
  unfold lowSideVal at h
  split at h
  · cases h
  · cases hw : lowWertE u Γ Λ fn none sd with
    | error e => simp [lowSideEns, zahlVon, hw] at h
    | ok wv =>
      obtain ⟨ls', rfl, he⟩ := lowWertE_sim (er := none) hw hb hA hT σ₀ σ ρ w β hW hL
      simp only [lowSideEns, zahlVon, hw, LowSide.wert, LowWert.zahl, Except.ok.injEq] at h
      subst h
      exact he

/-- A value fitted into a target range (`lowWertAt`) keeps its number. -/
theorem lowWertAt_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {lo hi : Int}
    {sd : USide} {e : Expr (declOf u) Γ Λ (.int lo hi)} {eB : Gabbro.Body.Expr}
    (h : lowWertAt u Γ Λ fn lo hi sd = .ok e) (hb : sideExprG u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WGRel u σ w) (hL : LRel fn 0 ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf (.int lo hi) (eval σ₀ e σ ρ)) := by
  unfold lowWertAt at h
  split at h
  · cases h
  · rename_i ls hls
    split at h
    · split at h
      · cases h
        rw [lowSideVal_sim hls hb hA hT σ₀ σ ρ w β hW hL]
        rfl
      · cases h
    · cases h

end Gabbro.Bruecke
