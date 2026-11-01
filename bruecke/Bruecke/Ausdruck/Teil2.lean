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

theorem lowSideVal_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {sd : USide} {ls : LowSide u Γ Λ} {eB : Gabbro.Body.Expr}
    (h : lowSideVal u Γ Λ fn sd = .ok ls) (hb : sideExpr u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WRel u σ w) (hL : LRel fn 0 ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf (.int ls.weit.1 ls.weit.2) (eval σ₀ ls.term σ ρ)) := by
  induction sd generalizing ls eB with
  | lit n =>
    simp only [lowSideVal] at h; cases h
    simp only [sideExpr] at hb; cases hb
    rfl
  | param p =>
    simp only [lowSideVal] at h
    simp only [sideExpr] at hb; cases hb
    simp only [Gabbro.Body.eval]
    rw [lowParamSide_sim h σ₀ σ ρ β hL]
  | slot b f ix =>
    simp only [lowSideVal] at h
    obtain ⟨c, hc, hv⟩ := lowDurch_sim h hA hT σ₀ σ ρ w β hW hL
    simp only [sideExpr, slotPlace, hc, Option.map_some] at hb
    cases hb
    exact hv
  | tab b f ix =>
    simp only [lowSideVal] at h
    simp only [sideExpr, slotPlace] at hb
    cases hb
    exact lowTabRead_sim h σ₀ σ ρ w β hW hL
  | alt b f ix => simp only [lowSideVal] at h; cases h
  | erg => simp only [lowSideVal] at h; cases h
  | add x y ihx ihy =>
    simp only [lowSideVal] at h
    cases hx : lowSideVal u Γ Λ fn x with
    | error e => simp [hx] at h
    | ok lx =>
      cases hy : lowSideVal u Γ Λ fn y with
      | error e => simp [hx, hy] at h
      | ok ly =>
        simp only [hx, hy, Except.ok.injEq] at h
        subst h
        cases hsx : sideExpr u fn x with
        | none => simp [sideExpr, hsx, binE] at hb
        | some ex =>
          cases hsy : sideExpr u fn y with
          | none => simp [sideExpr, hsx, hsy, binE] at hb
          | some ey =>
            simp only [sideExpr, hsx, hsy, binE, Option.some.injEq] at hb
            subst hb
            have h1 := ihx hx hsx
            have h2 := ihy hy hsy
            show Gabbro.Body.eval ⟨w, β⟩ (.bin .add ex ey) = _
            rw [show Gabbro.Body.eval ⟨w, β⟩ (.bin .add ex ey) =
              (match Gabbro.Body.eval ⟨w, β⟩ ex, Gabbro.Body.eval ⟨w, β⟩ ey with
                | some x, some y => Gabbro.Body.binop .add x y
                | _, _ => none) from rfl]
            rw [h1, h2]
            rfl
  | sub x y ihx ihy =>
    simp only [lowSideVal] at h
    cases hx : lowSideVal u Γ Λ fn x with
    | error e => simp [hx] at h
    | ok lx =>
      cases hy : lowSideVal u Γ Λ fn y with
      | error e => simp [hx, hy] at h
      | ok ly =>
        simp only [hx, hy, Except.ok.injEq] at h
        subst h
        cases hsx : sideExpr u fn x with
        | none => simp [sideExpr, hsx, binE] at hb
        | some ex =>
          cases hsy : sideExpr u fn y with
          | none => simp [sideExpr, hsx, hsy, binE] at hb
          | some ey =>
            simp only [sideExpr, hsx, hsy, binE, Option.some.injEq] at hb
            subst hb
            have h1 := ihx hx hsx
            have h2 := ihy hy hsy
            show Gabbro.Body.eval ⟨w, β⟩ (.bin .sub ex ey) = _
            rw [show Gabbro.Body.eval ⟨w, β⟩ (.bin .sub ex ey) =
              (match Gabbro.Body.eval ⟨w, β⟩ ex, Gabbro.Body.eval ⟨w, β⟩ ey with
                | some x, some y => Gabbro.Body.binop .sub x y
                | _, _ => none) from rfl]
            rw [h1, h2]
            rfl
  | mul x y ihx ihy =>
    simp only [lowSideVal] at h
    cases hx : lowSideVal u Γ Λ fn x with
    | error e => simp [hx] at h
    | ok lx =>
      cases hy : lowSideVal u Γ Λ fn y with
      | error e => simp [hx, hy] at h
      | ok ly =>
        simp only [hx, hy, Except.ok.injEq] at h
        subst h
        cases hsx : sideExpr u fn x with
        | none => simp [sideExpr, hsx, binE] at hb
        | some ex =>
          cases hsy : sideExpr u fn y with
          | none => simp [sideExpr, hsx, hsy, binE] at hb
          | some ey =>
            simp only [sideExpr, hsx, hsy, binE, Option.some.injEq] at hb
            subst hb
            have h1 := ihx hx hsx
            have h2 := ihy hy hsy
            show Gabbro.Body.eval ⟨w, β⟩ (.bin .mul ex ey) = _
            rw [show Gabbro.Body.eval ⟨w, β⟩ (.bin .mul ex ey) =
              (match Gabbro.Body.eval ⟨w, β⟩ ex, Gabbro.Body.eval ⟨w, β⟩ ey with
                | some x, some y => Gabbro.Body.binop .mul x y
                | _, _ => none) from rfl]
            rw [h1, h2]
            rfl
  | conv lo hi x ihx =>
    simp only [lowSideVal] at h
    cases hx : lowSideVal u Γ Λ fn x with
    | error e => simp [hx] at h
    | ok lx =>
      simp only [hx] at h
      unfold LowSide.conv at h
      split at h
      · rename_i h1
        split at h
        · rename_i h2
          cases h
          have hb' : sideExpr u fn x = some eB := hb
          rw [ihx hx hb']
          rfl
        · cases h
      · cases h
  | band x y ihx ihy =>
    simp only [lowSideVal, lowZwei] at h
    cases hx : lowSideVal u Γ Λ fn x with
    | error e => simp [hx] at h
    | ok lx =>
      cases hy : lowSideVal u Γ Λ fn y with
      | error e => simp [hx, hy] at h
      | ok ly =>
        simp only [hx, hy] at h
        unfold LowSide.and at h
        split at h
        · rename_i h0
          split at h
          · rename_i h0'
            cases h
            cases hsx : sideExpr u fn x with
            | none => simp [sideExpr, hsx, binE] at hb
            | some ex =>
              cases hsy : sideExpr u fn y with
              | none => simp [sideExpr, hsx, hsy, binE] at hb
              | some ey =>
                simp only [sideExpr, hsx, hsy, binE, Option.some.injEq] at hb
                subst hb
                have h1 := ihx hx hsx
                have h2 := ihy hy hsy
                have ha : 0 ≤ (eval σ₀ lx.term σ ρ : Zahl lx.weit.1 lx.weit.2).n :=
                  Int.le_trans h0 (eval σ₀ lx.term σ ρ : Zahl lx.weit.1 lx.weit.2).lo_le
                have hb0 : 0 ≤ (eval σ₀ ly.term σ ρ : Zahl ly.weit.1 ly.weit.2).n :=
                  Int.le_trans h0' (eval σ₀ ly.term σ ρ : Zahl ly.weit.1 ly.weit.2).lo_le
                show Gabbro.Body.eval ⟨w, β⟩ (.bin .band ex ey) = _
                rw [show Gabbro.Body.eval ⟨w, β⟩ (.bin .band ex ey) =
                  (match Gabbro.Body.eval ⟨w, β⟩ ex, Gabbro.Body.eval ⟨w, β⟩ ey with
                    | some x, some y => Gabbro.Body.binop .band x y
                    | _, _ => none) from rfl]
                rw [h1, h2]
                simp only [valOf_int, Gabbro.Body.binop, Gabbro.Body.bits, if_pos (And.intro ha hb0)]
                rfl
          · cases h
        · cases h
  | bor x y ihx ihy =>
    simp only [lowSideVal, lowZwei] at h
    cases hx : lowSideVal u Γ Λ fn x with
    | error e => simp [hx] at h
    | ok lx =>
      cases hy : lowSideVal u Γ Λ fn y with
      | error e => simp [hx, hy] at h
      | ok ly =>
        simp only [hx, hy] at h
        unfold LowSide.or at h
        split at h
        · rename_i h0
          split at h
          · rename_i h0'
            split at h
            · rename_i hw1
              split at h
              · rename_i hw2
                cases h
                cases hsx : sideExpr u fn x with
                | none => simp [sideExpr, hsx, binE] at hb
                | some ex =>
                  cases hsy : sideExpr u fn y with
                  | none => simp [sideExpr, hsx, hsy, binE] at hb
                  | some ey =>
                    simp only [sideExpr, hsx, hsy, binE, Option.some.injEq] at hb
                    subst hb
                    have h1 := ihx hx hsx
                    have h2 := ihy hy hsy
                    have ha : 0 ≤ (eval σ₀ lx.term σ ρ : Zahl lx.weit.1 lx.weit.2).n :=
                      Int.le_trans h0 (eval σ₀ lx.term σ ρ : Zahl lx.weit.1 lx.weit.2).lo_le
                    have hb0 : 0 ≤ (eval σ₀ ly.term σ ρ : Zahl ly.weit.1 ly.weit.2).n :=
                      Int.le_trans h0' (eval σ₀ ly.term σ ρ : Zahl ly.weit.1 ly.weit.2).lo_le
                    show Gabbro.Body.eval ⟨w, β⟩ (.bin .bor ex ey) = _
                    rw [show Gabbro.Body.eval ⟨w, β⟩ (.bin .bor ex ey) =
                      (match Gabbro.Body.eval ⟨w, β⟩ ex, Gabbro.Body.eval ⟨w, β⟩ ey with
                        | some x, some y => Gabbro.Body.binop .bor x y
                        | _, _ => none) from rfl]
                    rw [h1, h2]
                    simp only [valOf_int, Gabbro.Body.binop, Gabbro.Body.bits, if_pos (And.intro ha hb0)]
                    rfl
              · cases h
            · cases h
          · cases h
        · cases h
  | bxor x y ihx ihy =>
    simp only [lowSideVal, lowZwei] at h
    cases hx : lowSideVal u Γ Λ fn x with
    | error e => simp [hx] at h
    | ok lx =>
      cases hy : lowSideVal u Γ Λ fn y with
      | error e => simp [hx, hy] at h
      | ok ly =>
        simp only [hx, hy] at h
        unfold LowSide.xoder at h
        split at h
        · rename_i h0
          split at h
          · rename_i h0'
            split at h
            · rename_i hw1
              split at h
              · rename_i hw2
                cases h
                cases hsx : sideExpr u fn x with
                | none => simp [sideExpr, hsx, binE] at hb
                | some ex =>
                  cases hsy : sideExpr u fn y with
                  | none => simp [sideExpr, hsx, hsy, binE] at hb
                  | some ey =>
                    simp only [sideExpr, hsx, hsy, binE, Option.some.injEq] at hb
                    subst hb
                    have h1 := ihx hx hsx
                    have h2 := ihy hy hsy
                    have ha : 0 ≤ (eval σ₀ lx.term σ ρ : Zahl lx.weit.1 lx.weit.2).n :=
                      Int.le_trans h0 (eval σ₀ lx.term σ ρ : Zahl lx.weit.1 lx.weit.2).lo_le
                    have hb0 : 0 ≤ (eval σ₀ ly.term σ ρ : Zahl ly.weit.1 ly.weit.2).n :=
                      Int.le_trans h0' (eval σ₀ ly.term σ ρ : Zahl ly.weit.1 ly.weit.2).lo_le
                    show Gabbro.Body.eval ⟨w, β⟩ (.bin .bxor ex ey) = _
                    rw [show Gabbro.Body.eval ⟨w, β⟩ (.bin .bxor ex ey) =
                      (match Gabbro.Body.eval ⟨w, β⟩ ex, Gabbro.Body.eval ⟨w, β⟩ ey with
                        | some x, some y => Gabbro.Body.binop .bxor x y
                        | _, _ => none) from rfl]
                    rw [h1, h2]
                    simp only [valOf_int, Gabbro.Body.binop, Gabbro.Body.bits, if_pos (And.intro ha hb0)]
                    rfl
              · cases h
            · cases h
          · cases h
        · cases h

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

theorem ensSide_vor {fn : UFn} {a a' : Acc} {sd : USide} {x : Gabbro.Body.Expr}
    (h : ensSide u fn a sd = some (x, a')) : Vor a a' := by
  cases sd with
  | add _ _ | sub _ _ | mul _ _ | conv _ _ _ | band _ _ | bor _ _ | bxor _ _ => simp [ensSide, sideExpr] at h
  | alt b f ix =>
    simp only [ensSide] at h
    cases hp : slotPlace u fn (.alt b f ix) with
    | none => rw [hp] at h; cases h
    | some pl =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨⟨[pl], rfl⟩, id⟩
  | erg =>
    simp only [ensSide, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨⟨[], by simp⟩, fun _ => rfl⟩
  | lit n =>
    simp only [ensSide, sideExpr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; exact Vor.refl _
  | param p =>
    simp only [ensSide, sideExpr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; exact Vor.refl _
  | slot b f ix =>
    simp only [ensSide, sideExpr] at h
    cases hp : slotPlace u fn (.slot b f ix) with
    | none => rw [hp] at h; cases h
    | some pl =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact Vor.refl _
  | tab b f ix =>
    simp only [ensSide, sideExpr] at h
    cases hp : slotPlace u fn (.tab b f ix) with
    | none => rw [hp] at h; cases h
    | some pl =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact Vor.refl _

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

/-- **The binding an `ensures` clause is evaluated under** (`clauseAux` builds it): the
    parameters as in the entry state, `result` as the answer (the G context's first entry when
    there is a result), and the `i`th `old` name as the value the `i`th entry read has in the
    entry state `s₀`. -/
structure EnsBind {D : Deklaration} {Γ : Ctx} (fn : UFn) (er : Option (Int × Int))
    (ρ : Env D Γ) (s₀ : Gabbro.Body.State) (A : Acc) (β : Gabbro.Body.Binding) : Prop where
  par : LRel fn (if er.isSome then 1 else 0) ρ β
  res : A.result = true → β "result" = nthVal ρ 0
  old : ∀ i (hi : i < A.olds.length), Gabbro.Body.eval s₀ (A.olds[i]) = some (β (oldName i))

end Gabbro.Bruecke
