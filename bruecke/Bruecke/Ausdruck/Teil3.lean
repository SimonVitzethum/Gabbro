module

public import Bruecke.Kodierung
public import Bruecke.Pflichten
public import Bruecke.Ausdruck.Teil2

@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

theorem lowSideEns_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option (Int × Int)} {sd : USide} {ls : LowSide u Γ Λ} {a a' A : Acc}
    {x : Gabbro.Body.Expr}
    (h : lowSideEns u Γ Λ fn er sd = .ok ls) (hb : ensSide u fn a sd = some (x, a'))
    (hpre : Vor a' A) (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s₀ : Gabbro.Body.State)
    (w : Gabbro.Body.World) (β : Gabbro.Body.Binding)
    (hW₀ : WRel u σ₀ s₀.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) ρ s₀.local')
    (hW : WRel u σ w) (hB : EnsBind fn er ρ s₀ A β) :
    Gabbro.Body.eval ⟨w, β⟩ x = some (valOf (.int ls.weit.1 ls.weit.2) (eval σ₀ ls.term σ ρ)) := by
  cases sd with
  | add _ _ | sub _ _ | mul _ _ | conv _ _ _ | band _ _ | bor _ _ | bxor _ _ => simp [ensSide, sideExpr] at hb
  | lit n =>
    simp only [lowSideEns] at h; cases h
    simp only [ensSide, sideExpr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, _⟩ := hb
    rfl
  | param p =>
    simp only [lowSideEns] at h
    simp only [ensSide, sideExpr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, _⟩ := hb
    simp only [Gabbro.Body.eval]
    rw [lowParamSide_sim h σ₀ σ ρ β hB.par]
  | slot b f ix =>
    simp only [lowSideEns] at h
    obtain ⟨c, hc, hv⟩ := lowDurch_sim h hA hT σ₀ σ ρ w β hW hB.par
    simp only [ensSide, sideExpr, slotPlace, hc, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, _⟩ := hb
    exact hv
  | tab b f ix =>
    simp only [lowSideEns] at h
    simp only [ensSide, sideExpr, slotPlace, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, _⟩ := hb
    exact lowTabRead_sim h σ₀ σ ρ w β hW hB.par
  | alt b f ix =>
    simp only [lowSideEns] at h
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
      have hv := lowAltRead_sim h hA hT c hc σ₀ σ ρ s₀.world s₀.local' hW₀ hL₀
      simp only [Gabbro.Body.eval]
      cases s₀ with
      | mk w₀ β₀ =>
        rw [hv] at ho
        exact ho.symm
  | erg =>
    simp only [lowSideEns] at h
    split at h
    · rename_i _ lo hi
      split at h
      · cases h
      · rename_i v hv
        cases h
        simp only [ensSide, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        simp only [Gabbro.Body.eval]
        rw [hB.res (hpre.2 rfl), nthVal_lowVar Γ 0 _ v ρ hv]
        rfl
    · cases h

theorem opOf_some {op : String} {o : Gabbro.Body.BinOp} (h : opOf op = some o) :
    (op = "==" ∧ o = .eq) ∨ (op = "<" ∧ o = .lt) ∨ (op = "<=" ∧ o = .le) := by
  unfold opOf at h
  split at h <;> simp_all

/-- **An `ensures` predicate**: its Body term, under the clause binding, is the G truth value. -/
theorem lowEns_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option (Int × Int)} (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s₀ : Gabbro.Body.State)
    (w : Gabbro.Body.World) (β : Gabbro.Body.Binding) (A : Acc)
    (hW₀ : WRel u σ₀ s₀.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) ρ s₀.local')
    (hW : WRel u σ w) (hB : EnsBind fn er ρ s₀ A β) :
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
          simp only [lowEns, lowCmp] at h
          split at h
          · cases h
          · rename_i s1 hs1
            split at h
            · cases h
            · rename_i s2 hs2
              have p1 := (ensSide_vor hr).trans hpre
              have e1 := lowSideEns_sim hs1 hl p1 hA hT σ₀ σ ρ s₀ w β hW₀ hL₀ hW hB
              have e2 := lowSideEns_sim hs2 hr hpre hA hT σ₀ σ ρ s₀ w β hW₀ hL₀ hW hB
              rcases opOf_some hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · cases h
                simp only [Gabbro.Body.eval, e1, e2, valOf_int, Gabbro.Body.binop]
                simp [Grammatik.eval, wahr?]
              · cases h
                simp only [Gabbro.Body.eval, e1, e2, valOf_int, Gabbro.Body.binop]
                simp [Grammatik.eval, wahr?]
              · cases h
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

/-- What a lowered side adds to the accumulator: `old` reads that evaluate in the entry state,
    and `result` only where the function has one. -/
def Zuwachs (s₀ : Gabbro.Body.State) (er : Option (Int × Int)) (a a' : Acc) : Prop :=
  (∀ o ∈ a'.olds, o ∈ a.olds ∨ ∃ v, Gabbro.Body.eval s₀ o = some v) ∧
  (a'.result = true → a.result = true ∨ er.isSome = true)

theorem Zuwachs.refl (s₀ : Gabbro.Body.State) (er : Option (Int × Int)) (a : Acc) :
    Zuwachs s₀ er a a := ⟨fun _ h => .inl h, .inl⟩

theorem Zuwachs.trans {s₀ : Gabbro.Body.State} {er : Option (Int × Int)} {a b c : Acc}
    (_hv : Vor a b) (h1 : Zuwachs s₀ er a b) (h2 : Zuwachs s₀ er b c) : Zuwachs s₀ er a c := by
  refine ⟨fun o ho => ?_, fun h => ?_⟩
  · rcases h2.1 o ho with hb | hv'
    · exact h1.1 o hb
    · exact .inr hv'
  · rcases h2.2 h with hb | he
    · exact h1.2 hb
    · exact .inr he

theorem ensSide_zuwachs {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option (Int × Int)} {sd : USide} {ls : LowSide u Γ Λ} {a a' : Acc}
    {x : Gabbro.Body.Expr}
    (h : lowSideEns u Γ Λ fn er sd = .ok ls) (hb : ensSide u fn a sd = some (x, a'))
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s₀ : Gabbro.Body.State)
    (hW₀ : WRel u σ₀ s₀.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) ρ s₀.local') :
    Zuwachs s₀ er a a' := by
  cases sd with
  | add _ _ | sub _ _ | mul _ _ | conv _ _ _ | band _ _ | bor _ _ | bxor _ _ => simp [ensSide, sideExpr] at hb
  | alt b f ix =>
    simp only [lowSideEns] at h
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
      · have hv := lowAltRead_sim h hA hT c hc σ₀ σ ρ s₀.world s₀.local' hW₀ hL₀
        cases s₀
        exact .inr ⟨_, hv⟩
  | erg =>
    simp only [lowSideEns] at h
    split at h
    · rename_i _ lo hi
      simp only [ensSide, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨fun o ho => .inl ho, fun _ => .inr rfl⟩
    · cases h
  | lit n =>
    simp only [ensSide, sideExpr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨_, rfl⟩ := hb; exact Zuwachs.refl _ _ _
  | param p =>
    simp only [ensSide, sideExpr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨_, rfl⟩ := hb; exact Zuwachs.refl _ _ _
  | slot b f ix =>
    simp only [ensSide, sideExpr] at hb
    cases hp : slotPlace u fn (.slot b f ix) with
    | none => rw [hp] at hb; cases hb
    | some pl =>
      rw [hp] at hb
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨_, rfl⟩ := hb; exact Zuwachs.refl _ _ _
  | tab b f ix =>
    simp only [ensSide, sideExpr] at hb
    cases hp : slotPlace u fn (.tab b f ix) with
    | none => rw [hp] at hb; cases hb
    | some pl =>
      rw [hp] at hb
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨_, rfl⟩ := hb; exact Zuwachs.refl _ _ _

theorem ensExpr_zuwachs {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option (Int × Int)} (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s₀ : Gabbro.Body.State)
    (hW₀ : WRel u σ₀ s₀.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) ρ s₀.local') :
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
          simp only [lowEns, lowCmp] at h
          split at h
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

/-! ## 5. One `ensures` clause, as the duty file states it -/

theorem oldName_inj : ∀ a < 9, ∀ b < 9, oldName a = oldName b → a = b := by decide

theorem oldName_ne_result : ∀ a, oldName a ≠ "result" := by
  intro a
  match a with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => decide
  | _ + 8 => simp [oldName]

/-- The binding `clauseAux` builds: the `n`th, `n+1`st, … `old` name bound to the value its read
    has in the entry state. -/
def oldsBind (s : Gabbro.Body.State) : List Gabbro.Body.Expr → Nat → Gabbro.Body.Binding →
    Gabbro.Body.Binding
  | [], _, β => β
  | o :: os, n, β =>
      oldsBind s os (n + 1) (Gabbro.Body.bindLocal β (oldName n) ((Gabbro.Body.eval s o).getD .absent))

/-- The end of a clause: evaluated in the exit world under the built binding (with `result`
    bound to the answer, where the clause names it). -/
def Schluss (t : Gabbro.Body.Expr) (uses : Bool) (s' : Gabbro.Body.State)
    (r : Option Gabbro.Body.Value) (β : Gabbro.Body.Binding) : Prop :=
  if uses then ∃ v, r = some v ∧
      Gabbro.Body.eval ⟨s'.world, Gabbro.Body.bindLocal β "result" v⟩ t = some (.bool true)
  else Gabbro.Body.eval ⟨s'.world, β⟩ t = some (.bool true)

/-- Where every `old` read evaluates, the universally bound `old` values of `clauseAux` ARE those
    values. -/
theorem clauseAux_iff (t : Gabbro.Body.Expr) (uses : Bool) (s s' : Gabbro.Body.State)
    (r : Option Gabbro.Body.Value) :
    ∀ (olds : List Gabbro.Body.Expr) (n : Nat) (β : Gabbro.Body.Binding),
      (∀ o ∈ olds, ∃ v, Gabbro.Body.eval s o = some v) →
      (clauseAux t uses s s' r olds n β ↔ Schluss t uses s' r (oldsBind s olds n β))
  | [], n, β, _ => by
      unfold clauseAux Schluss oldsBind
      cases uses <;> simp
  | o :: os, n, β, hev => by
      obtain ⟨v, hv⟩ := hev o (List.mem_cons_self ..)
      have ih := clauseAux_iff t uses s s' r os (n + 1)
        (Gabbro.Body.bindLocal β (oldName n) v) (fun o' h => hev o' (List.mem_cons_of_mem _ h))
      simp only [clauseAux, oldsBind, hv, Option.getD_some]
      constructor
      · intro h; exact ih.mp (h v rfl)
      · intro h ov hov; cases hov; exact ih.mpr h

theorem oldsBind_fremd (s : Gabbro.Body.State) (m : String) :
    ∀ (olds : List Gabbro.Body.Expr) (n : Nat) (β : Gabbro.Body.Binding),
      (∀ i, i < olds.length → m ≠ oldName (n + i)) → oldsBind s olds n β m = β m
  | [], _, _, _ => rfl
  | o :: os, n, β, h => by
      simp only [oldsBind]
      rw [oldsBind_fremd s m os (n + 1) _ (fun i hi => by
        have := h (i + 1) (by simp; omega)
        rwa [show n + (i + 1) = n + 1 + i by omega] at this)]
      exact Gabbro.Body.bindLocal_elsewhere _ _ _ _ (by simpa using h 0 (by simp))

theorem oldsBind_hier (s : Gabbro.Body.State) :
    ∀ (olds : List Gabbro.Body.Expr) (n : Nat) (β : Gabbro.Body.Binding) (i : Nat)
      (hi : i < olds.length), n + olds.length ≤ 9 →
      oldsBind s olds n β (oldName (n + i)) = (Gabbro.Body.eval s olds[i]).getD .absent
  | [], _, _, _, hi, _ => by simp at hi
  | o :: os, n, β, 0, _, hn => by
      simp only [oldsBind, Nat.add_zero]
      rw [oldsBind_fremd s _ os (n + 1) _ (fun i hi h => by
        have := oldName_inj n (by simp at hn; omega) (n + 1 + i) (by simp at hn; omega) h
        omega)]
      simp
  | o :: os, n, β, i + 1, hi, hn => by
      simp only [oldsBind]
      rw [show n + (i + 1) = n + 1 + i by omega]
      exact oldsBind_hier s os (n + 1) _ i (by simpa using hi) (by simp at hn; omega)
      
/-- No parameter is called `result` or `old#…` -- the names a clause binds on top of the entry
    binding. Checked per unit. -/
def NamenFrei (fn : UFn) : Prop :=
  ∀ q ∈ fn.params, q.1 ≠ "result" ∧ ∀ i, q.1 ≠ oldName i

theorem LRel.ueber {D : Deklaration} {Γ : Ctx} {fn : UFn} {sh : Nat} {ρ : Env D Γ}
    {β β' : Gabbro.Body.Binding} (hN : NamenFrei fn) (h : LRel fn sh ρ β)
    (hβ : ∀ p, p ≠ "result" → (∀ i, p ≠ oldName i) → β' p = β p) : LRel fn sh ρ β' := by
  intro p j hj
  obtain ⟨τ, hτ⟩ := paramPos_name _ _ _ hj
  have hm : (p, τ) ∈ fn.params := List.mem_of_getElem? hτ
  obtain ⟨h1, h2⟩ := hN _ hm
  rw [hβ p h1 h2]
  exact h p j hj

/-- **One clause of a promise**: the Prop the duty file states (`clauseProp`) holds exactly when
    the lowered G predicate is true -- over the entry world `σ₀`, the exit world `σ'` and the
    `ensures` environment `E` (the answer first, where there is one). -/
end Gabbro.Bruecke
