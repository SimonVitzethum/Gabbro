module

public import Grammatik.Parser.Elab.UebersetzeAllg2
public import Grammatik.Nebenlaeufigkeit.Sperren.RessourcenBlatt.Teil3
public import Grammatik.Kern.Syntax.Satz
public import Gabbro.Body
public import Bruecke.Pflichten
public import Bruecke.Kodierung.Teil1

@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
variable (u : UProg)

theorem fieldHit_of (t : Fin u.tabellen.length) (fld : String) (w : Int × Int)
    (hB : (tabAt u t).bools = [])
    (h : fieldAtPos (tabAt u t).felder fld = some w) : ∃ fh, fieldHit u t fld = .ok fh ∧ fh.weit = w := by
  unfold fieldHit
  split
  · rename_i h'; rw [h] at h'; cases h'
  · rename_i w' h'
    rw [h] at h'
    cases h'
    have hnb : ∀ f : Fin (fieldCount u t), boolFeldAt u t f = false := by
      intro f; unfold boolFeldAt; rw [hB]; cases (tabAt u t).felder[f.wert]? <;> simp
    rw [dif_pos (hnb _)]
    exact ⟨_, rfl, rfl⟩

/-- **A related world is well-typed** (the duty file's `wellFormed`, hypothesis `U2`). -/
theorem wf_of_wrel {σ : World (declOf u)} {w : Gabbro.Body.World}
    (hB : ∀ t : Fin u.tabellen.length, (tabAt u t).bools = []) (hW : WRel u σ w) :
    Gabbro.Body.WF (shapeOfU u) w := by
  intro p sh hp
  cases p with
  | slot c k fld =>
    obtain ⟨t, ht, hf⟩ := slotShape_tabIdx u.tabellen c fld sh hp
    cases hq : (u.tabellen.get t).felder.find? (fun q => q.1 == fld) with
    | none => rw [hq] at hf; cases hf
    | some q =>
      rw [hq] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      subst hf
      have hfa : fieldAtPos (tabAt u t).felder fld = some q.2 := by
        rw [fieldAtPos_find]; simp only [tabAt]; rw [hq]; rfl
      obtain ⟨fh, hfh, hw⟩ := fieldHit_of u t fld q.2 (hB t) hfa
      rw [wrel_lies_k u hW c t ht fld fh hfh k]
      obtain ⟨n, hn, hlo, hhi⟩ := valOf_feld u t fh (σ.slots t k fh.idx)
      rw [hn, ← hw]
      simp [hlo, hhi]
  | field c n => simp [shapeOfU] at hp
  | global n => simp [shapeOfU] at hp

/-! ## 5. Transport along type equations -/

/-- What `rw … ; exact b` builds is `b` up to `HEq`. -/
theorem mpr_heq {α β : Sort _} (h : α = β) (b : β) : HEq (Eq.mpr h b) b := by
  subst h; rfl

theorem mp_heq {α β : Sort _} (h : α = β) (a : α) : HEq (Eq.mp h a) a := by
  subst h; rfl

theorem mpr3id_heq {α β γ δ : Sort _} (h1 : α = β) (h2 : β = γ) (h3 : γ = δ) (x : δ) :
    HEq (Eq.mpr h1 (Eq.mpr h2 (Eq.mpr h3 (id x)))) x := by
  subst h1; subst h2; subst h3; rfl

theorem mpr3_heq {α β γ δ : Sort _} (h1 : α = β) (h2 : β = γ) (h3 : γ = δ) (x : δ) :
    HEq (Eq.mpr h1 (Eq.mpr h2 (Eq.mpr h3 x))) x := by
  subst h1; subst h2; subst h3; rfl

theorem mpr2_heq {α β γ : Sort _} (h1 : α = β) (h2 : β = γ) (x : γ) :
    HEq (id (Eq.mpr h1 (Eq.mpr h2 x))) x := by
  subst h1; subst h2; rfl

theorem eval_heq {D : Deklaration} {Γ : Ctx} {Λ₁ Λ₂ : List (Res D)} {τ₁ τ₂ : Ty}
    (hΛ : Λ₁ = Λ₂) (hτ : τ₁ = τ₂)
    (e₁ : Expr D Γ Λ₁ τ₁) (e₂ : Expr D Γ Λ₂ τ₂) (he : HEq e₁ e₂)
    (σ₀ σ : World D) (ρ : Env D Γ) : HEq (eval σ₀ e₁ σ ρ) (eval σ₀ e₂ σ ρ) := by
  subst hΛ; subst hτ; cases he; rfl

theorem orte_heq {D : Deklaration} {Γ : Ctx} {Λ₁ Λ₂ : List (Res D)} {τ₁ τ₂ : Ty}
    (hΛ : Λ₁ = Λ₂) (hτ : τ₁ = τ₂)
    (e₁ : Expr D Γ Λ₁ τ₁) (e₂ : Expr D Γ Λ₂ τ₂) (he : HEq e₁ e₂) : e₁.orte = e₂.orte := by
  subst hΛ; subst hτ; cases he; rfl

/-- The value of a transported term, read as a Body value, is the value of the term. -/
theorem valOf_eval_heq {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ₁ τ₂ : Ty}
    (hτ : τ₁ = τ₂) (e₁ : Expr D Γ Λ τ₁) (e₂ : Expr D Γ Λ τ₂) (he : HEq e₁ e₂)
    (σ₀ σ : World D) (ρ : Env D Γ) :
    valOf τ₁ (eval σ₀ e₁ σ ρ) = valOf τ₂ (eval σ₀ e₂ σ ρ) :=
  valOf_heq hτ _ _ (eval_heq rfl hτ e₁ e₂ he σ₀ σ ρ)

end Gabbro.Bruecke
