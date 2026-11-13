module

public import Bruecke.Ausdruck.Teil2

@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

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

/-- Scalar arithmetic with a Body form cannot select the separate bounded-count lowering. -/
theorem sideExpr_ohneCount {fn : UFn} {sd : USide} {x : Gabbro.Body.Expr}
    (h : sideExpr u fn sd = some x) : usideHatZaehle sd = false := by
  have recurse (sd' : USide) (hlt : sizeOf sd' < sizeOf sd) {x' : Gabbro.Body.Expr}
      (h' : sideExpr u fn sd' = some x') : usideHatZaehle sd' = false :=
    sideExpr_ohneCount h'
  cases sd with
  | add l r | sub l r | mul l r =>
    cases hl : sideExpr u fn l with
    | none => simp [sideExpr, hl, binE] at h
    | some le =>
      cases hr : sideExpr u fn r with
      | none => simp [sideExpr, hl, hr, binE] at h
      | some re =>
        simp only [usideHatZaehle, recurse l (by simp_wf <;> omega) hl,
          recurse r (by simp_wf <;> omega) hr, Bool.false_or]
  | _ => simp_all [sideExpr, usideHatZaehle]
termination_by sizeOf sd
decreasing_by assumption

/-- The represented comparison sides cannot select the separate bounded-count lowering. -/
theorem ensSide_ohneCount {fn : UFn} {a a' : Acc} {sd : USide} {x : Gabbro.Body.Expr}
    (h : ensSide u fn a sd = some (x, a')) : usideHatZaehle sd = false := by
  by_cases hold : ∃ b f ix, sd = .old b f ix
  · obtain ⟨b, f, ix, rfl⟩ := hold
    rfl
  · by_cases herg : sd = .erg
    · subst herg
      rfl
    · exact sideExpr_ohneCount
        (ensSide_sonst h (fun b f ix e => hold ⟨b, f, ix, e⟩) herg).1

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
  | .slotB .., _, _, _, h | .tabB .., _, _, _, h
  | .globB .., _, _, _, h | .var .., _, _, _, h
  | .alle .., _, _, _, h | .einige .., _, _, _, h
  | .ergB, _, _, _, h | .istSome .., _, _, _, h
  | .held .., _, _, _, h | .imp .., _, _, _, h
  | .reach .., _, _, _, h | .member .., _, _, _, h
  | .filtered .., _, _, _, h | .arrayElements .., _, _, _, h => by cases h

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
