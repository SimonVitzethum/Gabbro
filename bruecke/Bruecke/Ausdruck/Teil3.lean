module

public import Bruecke.Kodierung
public import Bruecke.Pflichten
public import Bruecke.Ausdruck.Accumulator

@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

theorem ergFind_none {fn : UFn} (hA : ArtStimmt fn) : fn.params.find? (·.1 == "#erg") = none :=
  List.find?_eq_none.mpr fun q hq => by
    have := hA.2.2 q hq
    simp only [ParamSchlicht, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    simpa using this.2

private theorem lowWertE_erg_inv {Γ : Ctx} {Λ : List (Res (declOf u))}
    {fn : UFn} {er : Option Ty} {wv : LowWert u Γ Λ}
    (h : lowWertE u Γ Λ fn er .erg = .ok wv) (hA : ArtStimmt fn) :
    ∃ (lo hi : Int) (v : Var Γ (.int lo hi)),
      er = some (.int lo hi) ∧ lowVar Γ 0 (.int lo hi) = .ok v ∧
        wv = ({ range := (lo, hi), term := Expr.var v } : LowSide u Γ Λ).wert := by
  cases er with
  | none =>
    cases position : paramPos fn.params "#erg" with
    | error error => simp only [lowWertE, position, ergFind_none hA, reduceCtorEq] at h
    | ok j => simp only [lowWertE, position, ergFind_none hA, reduceCtorEq] at h
  | some ty =>
    cases ty with
    | int lo hi =>
      cases hv : lowVar Γ 0 (.int lo hi) with
      | error error => simp only [lowWertE, hv, reduceCtorEq] at h
      | ok v =>
        simp only [lowWertE, hv, Except.ok.injEq] at h
        exact ⟨lo, hi, v, rfl, hv, h.symm⟩
    | bool | opt _ | sum _ | why _ | never | fl _ _ | fnptr _ | ptr _ | ref _
    | arr _ _ | str _ | prod _ _ =>
      simp only [lowWertE, reduceCtorEq] at h

/-- An `ensures` side with a Body form lowers to a number (`old(..)`, `result` and every side of
    `lowWertE_sim`). -/
theorem lowWertEns_int {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {er : Option Ty}
    {sd : USide} {wv : LowWert u Γ Λ} {a a' : Acc} {x : Gabbro.Body.Expr}
    (h : lowWertE u Γ Λ fn er sd = .ok wv) (hb : ensSide u fn a sd = some (x, a'))
    (hA : ArtStimmt fn) (hT : TabEindeutig u) (σ₀ : World (declOf u)) (ρ : Env (declOf u) Γ)
    (s₀ : Gabbro.Body.State) (hW₀ : WGRel u σ₀ s₀.world)
    (hL₀ : LRel fn (if er.isSome then 1 else 0) ρ s₀.local') :
    ∃ ls : LowSide u Γ Λ, wv = ls.wert := by
  by_cases hold : ∃ b f ix, sd = .old b f ix
  · obtain ⟨b, f, ix, rfl⟩ := hold
    simp only [lowWertE] at h
    cases hr : lowAltRead u Γ Λ fn (if er.isSome then 1 else 0) b f ix with
    | error e => simp [hr, Except.map] at h
    | ok ls =>
      simp only [hr, Except.map, Except.ok.injEq] at h
      exact ⟨ls, h.symm⟩
  · by_cases herg : sd = .erg
    · subst herg
      obtain ⟨lo, hi, v, _, _, same⟩ := lowWertE_erg_inv h hA
      exact ⟨{ range := (lo, hi), term := Expr.var v }, same⟩
    · obtain ⟨hs, _⟩ := ensSide_sonst hb (fun b f ix e => hold ⟨b, f, ix, e⟩) herg
      obtain ⟨ls, hls, _⟩ := lowWertE_sim h hs hA hT σ₀ σ₀ ρ s₀.world s₀.local' hW₀ hL₀
      exact ⟨ls, hls⟩

theorem lowSideEns_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option Ty} {sd : USide} {ls : LowSide u Γ Λ} {a a' A : Acc}
    {x : Gabbro.Body.Expr}
    (h : lowSideEns u Γ Λ fn er sd = .ok ls) (hb : ensSide u fn a sd = some (x, a'))
    (hpre : Vor a' A) (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s₀ : Gabbro.Body.State)
    (w : Gabbro.Body.World) (β : Gabbro.Body.Binding)
    (hW₀ : WGRel u σ₀ s₀.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) ρ s₀.local')
    (hW : WGRel u σ w) (hB : EnsBind fn er ρ s₀ A β) :
    Gabbro.Body.eval ⟨w, β⟩ x = some (valOf (.int ls.range.1 ls.range.2) (eval σ₀ ls.term σ ρ)) := by
  by_cases hold : ∃ b f ix, sd = .old b f ix
  · obtain ⟨b, f, ix, rfl⟩ := hold
    cases hr : lowAltRead u Γ Λ fn (if er.isSome then 1 else 0) b f ix with
    | error e => simp [lowSideEns, zahlVon, lowWertE, hr, Except.map] at h
    | ok ls' =>
      simp only [lowSideEns, zahlVon, lowWertE, hr, Except.map, LowSide.wert, LowWert.zahl,
        Except.ok.injEq] at h
      subst h
      simp only [ensSide] at hb
      cases hc : ptrTab u fn b with
      | none => simp [slotPlace, hc] at hb
      | some c =>
        simp only [slotPlace, hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨⟨l, hl⟩, _⟩ := hpre
        have hlen : a.olds.length < A.olds.length := by
          rw [hl]; simp
        have hget : A.olds[a.olds.length] = .place c (idxExpr ix) f := by
          simp only [hl, List.append_assoc]
          simp
        have ho := hB.old a.olds.length hlen
        rw [hget] at ho
        have hv := lowAltRead_sim hr hA hT c hc σ₀ σ ρ s₀.world s₀.local' hW₀.1 hL₀
        simp only [Gabbro.Body.eval]
        cases s₀ with
        | mk w₀ β₀ =>
          rw [hv] at ho
          exact ho.symm
  · by_cases herg : sd = .erg
    · subst herg
      cases hw : lowWertE u Γ Λ fn er .erg with
      | error e => simp [lowSideEns, zahlVon, hw] at h
      | ok wv =>
        simp only [lowSideEns, zahlVon, hw] at h
        obtain ⟨lo, hi, v, rfl, hv, rfl⟩ := lowWertE_erg_inv hw hA
        simp only [LowSide.wert, LowWert.zahl, Except.ok.injEq] at h
        subst h
        simp only [ensSide, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        simp only [Gabbro.Body.eval]
        rw [hB.res (hpre.2 rfl), nthVal_lowVar Γ 0 _ v ρ hv]
        rfl
    · obtain ⟨hs, rfl⟩ := ensSide_sonst hb (fun b f ix e => hold ⟨b, f, ix, e⟩) herg
      cases hw : lowWertE u Γ Λ fn er sd with
      | error e => simp [lowSideEns, zahlVon, hw] at h
      | ok wv =>
        obtain ⟨ls', rfl, he⟩ := lowWertE_sim hw hs hA hT σ₀ σ ρ w β hW hB.par
        simp only [lowSideEns, zahlVon, hw, LowSide.wert, LowWert.zahl, Except.ok.injEq] at h
        subst h
        exact he

theorem opOf_some {op : String} {o : Gabbro.Body.BinOp} (h : opOf op = some o) :
    (op = "==" ∧ o = .eq) ∨ (op = "<" ∧ o = .lt) ∨ (op = "<=" ∧ o = .le) ∨
      (op = ">" ∧ o = .gt) ∨ (op = ">=" ∧ o = .ge) ∨ (op = "!=" ∧ o = .ne) := by
  unfold opOf at h
  split at h <;> simp_all

/-- **An `ensures` predicate**: its Body term, under the clause binding, is the G truth value. -/
theorem lowEns_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option Ty} (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s₀ : Gabbro.Body.State)
    (w : Gabbro.Body.World) (β : Gabbro.Body.Binding) (A : Acc)
    (hW₀ : WGRel u σ₀ s₀.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) ρ s₀.local')
    (hW : WGRel u σ w) (hB : EnsBind fn er ρ s₀ A β) :
    ∀ (e : UEns) {a a' : Acc} {x : Gabbro.Body.Expr} {g : Expr (declOf u) Γ Λ .bool},
      ensExpr u fn a e = some (x, a') → lowEns u Γ Λ fn er e = .ok g →
      Vor a' A →
      Gabbro.Body.eval ⟨w, β⟩ x = some (.bool (wahr? (eval σ₀ g σ ρ)))
  | .tru, a, a', x, g, hb, h, _ => by
      simp only [lowEns] at h; cases h
      simp only [ensExpr, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, _⟩ := hb; rfl
  | .fls, a, a', x, g, hb, h, _ => by
      simp only [lowEns] at h; cases h
      simp only [ensExpr, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, _⟩ := hb; rfl
  | .cmp op l r, a, a', x, g, hb, h, hpre => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i o le a1 hop hl
        split at hb
        · rename_i re a2 hr
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [lowEns, ensSide_ohneCount hl, ensSide_ohneCount hr,
            Bool.false_or, Bool.false_eq_true, ↓reduceIte, lowCmp, lowVglWert] at h
          split at h
          · rename_i hx1 _
            obtain ⟨_, hls⟩ := lowWertEns_int hx1 hl hA hT σ₀ ρ s₀ hW₀ hL₀
            simp [LowSide.wert] at hls
          · rename_i hx1 _
            obtain ⟨_, hls⟩ := lowWertEns_int hx1 hl hA hT σ₀ ρ s₀ hW₀ hL₀
            simp [LowSide.wert] at hls
          · rename_i hx1 _
            obtain ⟨_, hls⟩ := lowWertEns_int hx1 hl hA hT σ₀ ρ s₀ hW₀ hL₀
            simp [LowSide.wert] at hls
          · rename_i hx1 _
            obtain ⟨_, hls⟩ := lowWertEns_int hx1 hl hA hT σ₀ ρ s₀ hW₀ hL₀
            simp [LowSide.wert] at hls
          · split at h
            · cases h
            · rename_i s1 hs1
              split at h
              · cases h
              · rename_i s2 hs2
                have p1 := (ensSide_vor hr).trans hpre
                have e1 := lowSideEns_sim hs1 hl p1 hA hT σ₀ σ ρ s₀ w β hW₀ hL₀ hW hB
                have e2 := lowSideEns_sim hs2 hr hpre hA hT σ₀ σ ρ s₀ w β hW₀ hL₀ hW hB
                rcases opOf_some hop with
                  ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                all_goals
                  cases h
                  simp only [Gabbro.Body.eval, e1, e2, valOf_int, Gabbro.Body.binop]
                  simp [Grammatik.eval, wahr?]
        · cases hb
      · cases hb
  | .and x y, a, a', z, g, hb, h, hpre => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i xe a1 hx
        split at hb
        · rename_i ye a2 hy
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [lowEns] at h
          split at h
          · cases h
          · rename_i gx hgx
            split at h
            · cases h
            · rename_i gy hgy
              cases h
              have p1 := (ensExpr_vor y hy).trans hpre
              have e1 := lowEns_sim hA hT σ₀ σ ρ s₀ w β A hW₀ hL₀ hW hB x hx hgx p1
              have e2 := lowEns_sim hA hT σ₀ σ ρ s₀ w β A hW₀ hL₀ hW hB y hy hgy hpre
              simp only [Gabbro.Body.eval, e1, e2, Gabbro.Body.andBool_some]
              rfl
        · cases hb
      · cases hb
  | .or x y, a, a', z, g, hb, h, hpre => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i xe a1 hx
        split at hb
        · rename_i ye a2 hy
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [lowEns] at h
          split at h
          · cases h
          · rename_i gx hgx
            split at h
            · cases h
            · rename_i gy hgy
              cases h
              have p1 := (ensExpr_vor y hy).trans hpre
              have e1 := lowEns_sim hA hT σ₀ σ ρ s₀ w β A hW₀ hL₀ hW hB x hx hgx p1
              have e2 := lowEns_sim hA hT σ₀ σ ρ s₀ w β A hW₀ hL₀ hW hB y hy hgy hpre
              simp only [Gabbro.Body.eval, e1, e2, Gabbro.Body.orBool_some]
              rfl
        · cases hb
      · cases hb
  | .not x, a, a', z, g, hb, h, hpre => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i xe a1 hx
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        simp only [lowEns] at h
        split at h
        · cases h
        · rename_i gx hgx
          cases h
          have e1 := lowEns_sim hA hT σ₀ σ ρ s₀ w β A hW₀ hL₀ hW hB x hx hgx hpre
          simp only [Gabbro.Body.eval, e1, Gabbro.Body.unop]
          rfl
      · cases hb
  | .var p, a, a', x, g, hb, h, _ => by
      simp only [ensExpr, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      simp only [lowEns] at h
      split at h
      · cases h
      · rename_i j hj
        split at h
        · cases h
        · rename_i v hv
          cases h
          simp only [Gabbro.Body.eval]
          rw [hB.par p j hj, nthVal_lowVar Γ _ .bool v ρ hv]
          rfl
  -- Unrepresented predicates contradict the existing `ensExpr` premise.
  | .slotB .., _, _, _, _, hb, _, _ | .tabB .., _, _, _, _, hb, _, _
  | .globB .., _, _, _, _, hb, _, _
  | .alle .., _, _, _, _, hb, _, _ | .einige .., _, _, _, _, hb, _, _
  | .ergB, _, _, _, _, hb, _, _ | .istSome .., _, _, _, _, hb, _, _
  | .held .., _, _, _, _, hb, _, _ | .imp .., _, _, _, _, hb, _, _
  | .reach .., _, _, _, _, hb, _, _ | .member .., _, _, _, _, hb, _, _
  | .filtered .., _, _, _, _, hb, _, _ | .arrayElements .., _, _, _, _, hb, _, _ => by cases hb

/-- What a lowered side adds to the accumulator: `old` reads that evaluate in the entry state,
    and `result` only where the function has one. -/
def Zuwachs (s₀ : Gabbro.Body.State) (er : Option Ty) (a a' : Acc) : Prop :=
  (∀ o ∈ a'.olds, o ∈ a.olds ∨ ∃ v, Gabbro.Body.eval s₀ o = some v) ∧
  (a'.result = true → a.result = true ∨ er.isSome = true)

theorem Zuwachs.refl (s₀ : Gabbro.Body.State) (er : Option Ty) (a : Acc) :
    Zuwachs s₀ er a a := ⟨fun _ h => .inl h, .inl⟩

theorem Zuwachs.trans {s₀ : Gabbro.Body.State} {er : Option Ty} {a b c : Acc}
    (_hv : Vor a b) (h1 : Zuwachs s₀ er a b) (h2 : Zuwachs s₀ er b c) : Zuwachs s₀ er a c := by
  refine ⟨fun o ho => ?_, fun h => ?_⟩
  · rcases h2.1 o ho with hb | hv'
    · exact h1.1 o hb
    · exact .inr hv'
  · rcases h2.2 h with hb | he
    · exact h1.2 hb
    · exact .inr he

theorem ensSide_zuwachs {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option Ty} {sd : USide} {ls : LowSide u Γ Λ} {a a' : Acc}
    {x : Gabbro.Body.Expr}
    (h : lowSideEns u Γ Λ fn er sd = .ok ls) (hb : ensSide u fn a sd = some (x, a'))
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s₀ : Gabbro.Body.State)
    (hW₀ : WGRel u σ₀ s₀.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) ρ s₀.local') :
    Zuwachs s₀ er a a' := by
  by_cases hold : ∃ b f ix, sd = .old b f ix
  · obtain ⟨b, f, ix, rfl⟩ := hold
    cases hr : lowAltRead u Γ Λ fn (if er.isSome then 1 else 0) b f ix with
    | error e => simp [lowSideEns, zahlVon, lowWertE, hr, Except.map] at h
    | ok ls' =>
      simp only [ensSide] at hb
      cases hc : ptrTab u fn b with
      | none => simp [slotPlace, hc] at hb
      | some c =>
        simp only [slotPlace, hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        refine ⟨fun o ho => ?_, fun hr => .inl hr⟩
        simp only [List.mem_append, List.mem_singleton] at ho
        rcases ho with ho | rfl
        · exact .inl ho
        · have hv := lowAltRead_sim hr hA hT c hc σ₀ σ ρ s₀.world s₀.local' hW₀.1 hL₀
          cases s₀
          exact .inr ⟨_, hv⟩
  · by_cases herg : sd = .erg
    · subst herg
      simp only [ensSide, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine ⟨fun o ho => .inl ho, fun _ => .inr ?_⟩
      cases hw : lowWertE u Γ Λ fn er .erg with
      | error e => simp [lowSideEns, zahlVon, hw] at h
      | ok wv =>
        obtain ⟨lo, hi, v, rfl, _, _⟩ := lowWertE_erg_inv hw hA
        rfl
    · obtain ⟨_, rfl⟩ := ensSide_sonst hb (fun b f ix e => hold ⟨b, f, ix, e⟩) herg
      exact Zuwachs.refl _ _ _

theorem ensExpr_zuwachs {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option Ty} (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s₀ : Gabbro.Body.State)
    (hW₀ : WGRel u σ₀ s₀.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) ρ s₀.local') :
    ∀ (e : UEns) {a a' : Acc} {x : Gabbro.Body.Expr} {g : Expr (declOf u) Γ Λ .bool},
      ensExpr u fn a e = some (x, a') → lowEns u Γ Λ fn er e = .ok g → Zuwachs s₀ er a a'
  | .tru, a, a', x, g, hb, h => by
      simp only [ensExpr, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨_, rfl⟩ := hb; exact Zuwachs.refl _ _ _
  | .fls, a, a', x, g, hb, h => by
      simp only [ensExpr, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨_, rfl⟩ := hb; exact Zuwachs.refl _ _ _
  | .cmp op l r, a, a', x, g, hb, h => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i o le a1 hop hl
        split at hb
        · rename_i re a2 hr
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [lowEns, ensSide_ohneCount hl, ensSide_ohneCount hr,
            Bool.false_or, Bool.false_eq_true, ↓reduceIte, lowCmp, lowVglWert] at h
          split at h
          · rename_i hx1 _
            obtain ⟨_, hls⟩ := lowWertEns_int hx1 hl hA hT σ₀ ρ s₀ hW₀ hL₀
            simp [LowSide.wert] at hls
          · rename_i hx1 _
            obtain ⟨_, hls⟩ := lowWertEns_int hx1 hl hA hT σ₀ ρ s₀ hW₀ hL₀
            simp [LowSide.wert] at hls
          · rename_i hx1 _
            obtain ⟨_, hls⟩ := lowWertEns_int hx1 hl hA hT σ₀ ρ s₀ hW₀ hL₀
            simp [LowSide.wert] at hls
          · rename_i hx1 _
            obtain ⟨_, hls⟩ := lowWertEns_int hx1 hl hA hT σ₀ ρ s₀ hW₀ hL₀
            simp [LowSide.wert] at hls
          · split at h
            · cases h
            · rename_i s1 hs1
              split at h
              · cases h
              · rename_i s2 hs2
                exact Zuwachs.trans (ensSide_vor hl)
                  (ensSide_zuwachs hs1 hl hA hT σ₀ σ ρ s₀ hW₀ hL₀)
                  (ensSide_zuwachs hs2 hr hA hT σ₀ σ ρ s₀ hW₀ hL₀)
        · cases hb
      · cases hb
  | .and x y, a, a', z, g, hb, h => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i xe a1 hx
        split at hb
        · rename_i ye a2 hy
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [lowEns] at h
          split at h
          · cases h
          · rename_i gx hgx
            split at h
            · cases h
            · rename_i gy hgy
              exact Zuwachs.trans (ensExpr_vor x hx)
                (ensExpr_zuwachs hA hT σ₀ σ ρ s₀ hW₀ hL₀ x hx hgx)
                (ensExpr_zuwachs hA hT σ₀ σ ρ s₀ hW₀ hL₀ y hy hgy)
        · cases hb
      · cases hb
  | .or x y, a, a', z, g, hb, h => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i xe a1 hx
        split at hb
        · rename_i ye a2 hy
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [lowEns] at h
          split at h
          · cases h
          · rename_i gx hgx
            split at h
            · cases h
            · rename_i gy hgy
              exact Zuwachs.trans (ensExpr_vor x hx)
                (ensExpr_zuwachs hA hT σ₀ σ ρ s₀ hW₀ hL₀ x hx hgx)
                (ensExpr_zuwachs hA hT σ₀ σ ρ s₀ hW₀ hL₀ y hy hgy)
        · cases hb
      · cases hb
  | .not x, a, a', z, g, hb, h => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i xe a1 hx
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        simp only [lowEns] at h
        split at h
        · cases h
        · rename_i gx hgx
          exact ensExpr_zuwachs hA hT σ₀ σ ρ s₀ hW₀ hL₀ x hx hgx
      · cases hb
  | .var p, a, a', x, g, hb, h => by
      simp only [ensExpr, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨_, rfl⟩ := hb
      exact Zuwachs.refl _ _ _
  -- Unrepresented predicates contradict the existing `ensExpr` premise.
  | .slotB .., _, _, _, _, hb, _ | .tabB .., _, _, _, _, hb, _
  | .globB .., _, _, _, _, hb, _
  | .alle .., _, _, _, _, hb, _ | .einige .., _, _, _, _, hb, _
  | .ergB, _, _, _, _, hb, _ | .istSome .., _, _, _, _, hb, _
  | .held .., _, _, _, _, hb, _ | .imp .., _, _, _, _, hb, _
  | .reach .., _, _, _, _, hb, _ | .member .., _, _, _, _, hb, _
  | .filtered .., _, _, _, _, hb, _ | .arrayElements .., _, _, _, _, hb, _ => by cases hb

end Gabbro.Bruecke
