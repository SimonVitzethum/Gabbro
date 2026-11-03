module

public import Bruecke.Kodierung
public import Bruecke.Pflichten
public import Bruecke.Ausdruck.Teil1

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
    (h : lowWertE u Γ Λ fn er sd = .ok wv) (hb : sideExpr u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WRel u σ w) (hL : LRel fn (if er.isSome then 1 else 0) ρ β) :
    ∃ ls : LowSide u Γ Λ, wv = ls.wert ∧
      Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf (.int ls.range.1 ls.range.2) (eval σ₀ ls.term σ ρ)) := by
  induction sd generalizing wv eB with
  | lit n =>
    simp only [lowWertE, Except.ok.injEq] at h
    subst h
    simp only [sideExpr, Option.some.injEq] at hb
    subst hb
    exact ⟨_, rfl, rfl⟩
  | param p =>
    simp only [lowWertE, lowParamWert_none hA] at h
    cases hp : lowParamSide u Γ Λ fn (if er.isSome then 1 else 0) p with
    | error e => simp [hp, Except.map] at h
    | ok ls =>
      simp only [hp, Except.map, Except.ok.injEq] at h
      subst h
      simp only [sideExpr, Option.some.injEq] at hb
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
      obtain ⟨c, hc, hv⟩ := lowDurch_sim hd hA hT σ₀ σ ρ w β hW hL
      simp only [sideExpr, slotPlace, hc, Option.map_some, Option.some.injEq] at hb
      subst hb
      exact ⟨ls, rfl, hv⟩
  | tab b f ix =>
    simp only [lowWertE, lowTabWert_none hT] at h
    cases hd : lowTabRead u Γ Λ fn (if er.isSome then 1 else 0) b f ix with
    | error e => simp [hd, Except.map] at h
    | ok ls =>
      simp only [hd, Except.map, Except.ok.injEq] at h
      subst h
      simp only [sideExpr, slotPlace, Option.some.injEq] at hb
      subst hb
      exact ⟨ls, rfl, lowTabRead_sim hd σ₀ σ ρ w β hW hL⟩
  | add x y ihx ihy =>
    cases hsx : sideExpr u fn x with
    | none => simp [sideExpr, hsx, binE] at hb
    | some ex =>
      cases hsy : sideExpr u fn y with
      | none => simp [sideExpr, hsx, hsy, binE] at hb
      | some ey =>
        simp only [sideExpr, hsx, hsy, binE, Option.some.injEq] at hb
        subst hb
        cases hx : lowWertE u Γ Λ fn er x with
        | error e => simp [lowWertE, zahlVon, lowZwei, hx, Except.map] at h
        | ok wa =>
          obtain ⟨lx, rfl, h1⟩ := ihx hx hsx
          simp only [LowSide.wert] at hx
          cases hy : lowWertE u Γ Λ fn er y with
          | error e => simp [lowWertE, zahlVon, lowZwei, LowWert.zahl, hx, hy, Except.map] at h
          | ok wb =>
            obtain ⟨ly, rfl, h2⟩ := ihy hy hsy
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
  | sub x y ihx ihy =>
    cases hsx : sideExpr u fn x with
    | none => simp [sideExpr, hsx, binE] at hb
    | some ex =>
      cases hsy : sideExpr u fn y with
      | none => simp [sideExpr, hsx, hsy, binE] at hb
      | some ey =>
        simp only [sideExpr, hsx, hsy, binE, Option.some.injEq] at hb
        subst hb
        cases hx : lowWertE u Γ Λ fn er x with
        | error e => simp [lowWertE, zahlVon, lowZwei, hx, Except.map] at h
        | ok wa =>
          obtain ⟨lx, rfl, h1⟩ := ihx hx hsx
          simp only [LowSide.wert] at hx
          cases hy : lowWertE u Γ Λ fn er y with
          | error e => simp [lowWertE, zahlVon, lowZwei, LowWert.zahl, hx, hy, Except.map] at h
          | ok wb =>
            obtain ⟨ly, rfl, h2⟩ := ihy hy hsy
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
  | mul x y ihx ihy =>
    cases hsx : sideExpr u fn x with
    | none => simp [sideExpr, hsx, binE] at hb
    | some ex =>
      cases hsy : sideExpr u fn y with
      | none => simp [sideExpr, hsx, hsy, binE] at hb
      | some ey =>
        simp only [sideExpr, hsx, hsy, binE, Option.some.injEq] at hb
        subst hb
        cases hx : lowWertE u Γ Λ fn er x with
        | error e => simp [lowWertE, zahlVon, lowZwei, hx, Except.map] at h
        | ok wa =>
          obtain ⟨lx, rfl, h1⟩ := ihx hx hsx
          simp only [LowSide.wert] at hx
          cases hy : lowWertE u Γ Λ fn er y with
          | error e => simp [lowWertE, zahlVon, lowZwei, LowWert.zahl, hx, hy, Except.map] at h
          | ok wb =>
            obtain ⟨ly, rfl, h2⟩ := ihy hy hsy
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
  | conv lo hi x ihx =>
    have hb' : sideExpr u fn x = some eB := hb
    cases hx : lowWertE u Γ Λ fn er x with
    | error e => simp [lowWertE, zahlVon, hx, Except.map] at h
    | ok wa =>
      obtain ⟨lx, rfl, h1⟩ := ihx hx hb'
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
  | band x y ihx ihy =>
    cases hsx : sideExpr u fn x with
    | none => simp [sideExpr, hsx, binE] at hb
    | some ex =>
      cases hsy : sideExpr u fn y with
      | none => simp [sideExpr, hsx, hsy, binE] at hb
      | some ey =>
        simp only [sideExpr, hsx, hsy, binE, Option.some.injEq] at hb
        subst hb
        cases hx : lowWertE u Γ Λ fn er x with
        | error e => simp [lowWertE, zahlVon, lowZwei, hx, Except.map] at h
        | ok wa =>
          obtain ⟨lx, rfl, h1⟩ := ihx hx hsx
          simp only [LowSide.wert] at hx
          cases hy : lowWertE u Γ Λ fn er y with
          | error e => simp [lowWertE, zahlVon, lowZwei, LowWert.zahl, hx, hy, Except.map] at h
          | ok wb =>
            obtain ⟨ly, rfl, h2⟩ := ihy hy hsy
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
  | bor x y ihx ihy =>
    cases hsx : sideExpr u fn x with
    | none => simp [sideExpr, hsx, binE] at hb
    | some ex =>
      cases hsy : sideExpr u fn y with
      | none => simp [sideExpr, hsx, hsy, binE] at hb
      | some ey =>
        simp only [sideExpr, hsx, hsy, binE, Option.some.injEq] at hb
        subst hb
        cases hx : lowWertE u Γ Λ fn er x with
        | error e => simp [lowWertE, zahlVon, lowZwei, hx, Except.map] at h
        | ok wa =>
          obtain ⟨lx, rfl, h1⟩ := ihx hx hsx
          simp only [LowSide.wert] at hx
          cases hy : lowWertE u Γ Λ fn er y with
          | error e => simp [lowWertE, zahlVon, lowZwei, LowWert.zahl, hx, hy, Except.map] at h
          | ok wb =>
            obtain ⟨ly, rfl, h2⟩ := ihy hy hsy
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
  | bxor x y ihx ihy =>
    cases hsx : sideExpr u fn x with
    | none => simp [sideExpr, hsx, binE] at hb
    | some ex =>
      cases hsy : sideExpr u fn y with
      | none => simp [sideExpr, hsx, hsy, binE] at hb
      | some ey =>
        simp only [sideExpr, hsx, hsy, binE, Option.some.injEq] at hb
        subst hb
        cases hx : lowWertE u Γ Λ fn er x with
        | error e => simp [lowWertE, zahlVon, lowZwei, hx, Except.map] at h
        | ok wa =>
          obtain ⟨lx, rfl, h1⟩ := ihx hx hsx
          simp only [LowSide.wert] at hx
          cases hy : lowWertE u Γ Λ fn er y with
          | error e => simp [lowWertE, zahlVon, lowZwei, LowWert.zahl, hx, hy, Except.map] at h
          | ok wb =>
            obtain ⟨ly, rfl, h2⟩ := ihy hy hsy
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
  | _ => simp [sideExpr] at hb

theorem lowSideVal_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {sd : USide} {ls : LowSide u Γ Λ} {eB : Gabbro.Body.Expr}
    (h : lowSideVal u Γ Λ fn sd = .ok ls) (hb : sideExpr u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WRel u σ w) (hL : LRel fn 0 ρ β) :
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
    (h : lowWertAt u Γ Λ fn lo hi sd = .ok e) (hb : sideExpr u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WRel u σ w) (hL : LRel fn 0 ρ β) :
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

/-! ## 4. `ensures` -/

/-- The accumulator only grows: `old` reads are appended, and `result` once met stays met. -/
def Vor (a b : Acc) : Prop := (∃ l, b.olds = a.olds ++ l) ∧ (a.result = true → b.result = true)

theorem Vor.refl (a : Acc) : Vor a a := ⟨⟨[], by simp⟩, id⟩

theorem Vor.trans {a b c : Acc} (h1 : Vor a b) (h2 : Vor b c) : Vor a c := by
  obtain ⟨⟨l1, h1⟩, r1⟩ := h1
  obtain ⟨⟨l2, h2⟩, r2⟩ := h2
  exact ⟨⟨l1 ++ l2, by rw [h2, h1, List.append_assoc]⟩, fun h => r2 (r1 h)⟩

/-- An `ensures` side other than `old(..)` and `result` is the side's Body form, and adds nothing to
    the accumulator. -/
theorem ensSide_sonst {fn : UFn} {a a' : Acc} {sd : USide} {x : Gabbro.Body.Expr}
    (h : ensSide u fn a sd = some (x, a')) (h1 : ∀ b f ix, sd ≠ .old b f ix) (h2 : sd ≠ .erg) :
    sideExpr u fn sd = some x ∧ a' = a := by
  unfold ensSide at h
  split at h
  all_goals first
    | exact absurd rfl (h1 _ _ _)
    | exact absurd rfl h2
    | (cases h; done)
    | (cases hs : sideExpr u fn sd with
       | none => rw [hs] at h; cases h
       | some e =>
         rw [hs] at h
         simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         exact ⟨rfl, rfl⟩)

theorem ensSide_vor {fn : UFn} {a a' : Acc} {sd : USide} {x : Gabbro.Body.Expr}
    (h : ensSide u fn a sd = some (x, a')) : Vor a a' := by
  by_cases hold : ∃ b f ix, sd = .old b f ix
  · obtain ⟨b, f, ix, rfl⟩ := hold
    simp only [ensSide] at h
    cases hp : slotPlace u fn (.old b f ix) with
    | none => rw [hp] at h; cases h
    | some pl =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨⟨[pl], rfl⟩, id⟩
  · by_cases herg : sd = .erg
    · subst herg
      simp only [ensSide, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨⟨[], by simp⟩, fun _ => rfl⟩
    · obtain ⟨_, rfl⟩ := ensSide_sonst h (fun b f ix e => hold ⟨b, f, ix, e⟩) herg
      exact Vor.refl _

/-- The represented comparison sides cannot select the separate bounded-count lowering. -/
theorem ensSide_ohneCount {fn : UFn} {a a' : Acc} {sd : USide} {x : Gabbro.Body.Expr}
    (h : ensSide u fn a sd = some (x, a')) : usideHatZaehle sd = false := by
  cases sd <;> simp_all [ensSide, sideExpr, usideHatZaehle]

theorem ensExpr_vor {fn : UFn} : ∀ (e : UEns) {a a' : Acc} {x : Gabbro.Body.Expr},
    ensExpr u fn a e = some (x, a') → Vor a a'
  | .tru, a, a', x, h => by
      simp only [ensExpr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact Vor.refl _
  | .fls, a, a', x, h => by
      simp only [ensExpr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact Vor.refl _
  | .cmp op l r, a, a', x, h => by
      simp only [ensExpr] at h
      split at h
      · rename_i o le a1 _ hl
        split at h
        · rename_i re a2 hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact (ensSide_vor hl).trans (ensSide_vor hr)
        · cases h
      · cases h
  | .and x y, a, a', z, h => by
      simp only [ensExpr] at h
      split at h
      · rename_i xe a1 hx
        split at h
        · rename_i ye a2 hy
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact (ensExpr_vor x hx).trans (ensExpr_vor y hy)
        · cases h
      · cases h
  | .or x y, a, a', z, h => by
      simp only [ensExpr] at h
      split at h
      · rename_i xe a1 hx
        split at h
        · rename_i ye a2 hy
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact (ensExpr_vor x hx).trans (ensExpr_vor y hy)
        · cases h
      · cases h
  | .not x, a, a', z, h => by
      simp only [ensExpr] at h
      split at h
      · rename_i xe a1 hx
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact ensExpr_vor x hx
      · cases h
  -- All other predicates are outside the Body fragment (`ensExpr` returns `none`).
  | _, _, _, _, h => by simp [ensExpr] at h

/-- **The binding an `ensures` clause is evaluated under** (`clauseAux` builds it): the
    parameters as in the entry state, `result` as the answer (the G context's first entry when
    there is a result), and the `i`th `old` name as the value the `i`th entry read has in the
    entry state `s₀`. -/
structure EnsBind {D : Deklaration} {Γ : Ctx} (fn : UFn) (er : Option Ty)
    (ρ : Env D Γ) (s₀ : Gabbro.Body.State) (A : Acc) (β : Gabbro.Body.Binding) : Prop where
  par : LRel fn (if er.isSome then 1 else 0) ρ β
  res : A.result = true → β "result" = nthVal ρ 0
  old : ∀ i (hi : i < A.olds.length), Gabbro.Body.eval s₀ (A.olds[i]) = some (β (oldName i))

end Gabbro.Bruecke
