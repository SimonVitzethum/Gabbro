module
public import Bruecke.Realisierung
@[expose] public section


/-!
# Shared simulation infrastructure

The answer-table environment agrees with every recorded call and retains the realization
elsewhere. The transport lemmas relate runs across the lowering's type equations; `eintritt`
encodes the canonical G entry state. `Kette/` assembles these ingredients into the source bridge.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- O43 is a separate user duty for the actual lowered pointer contracts.
    Structural conformance and Body duties do not establish this refinement. -/
def SchnittstellenPflicht (u : UProg) : Prop :=
  ∀ (P : Programm (declOf u)) (fs : List (declOf u).Fn),
    lowerAllg u = .ok (P, fs) → PtrVerfeinert P

/-! ## 2. The environment of a table -/

theorem schluessel_eind {A : List Eintrag} (hA : Schluessel A) :
    ∀ e₁ ∈ A, ∀ e₂ ∈ A, e₁.name = e₂.name → e₁.ein = e₂.ein → e₁ = e₂ := by
  induction A with
  | nil => intro e₁ h; cases h
  | cons a l ih =>
    intro e₁ h₁ e₂ h₂ hn he
    rcases List.mem_cons.mp h₁ with r₁ | m₁
    · rcases List.mem_cons.mp h₂ with r₂ | m₂
      · rw [r₁, r₂]
      · subst r₁; exact absurd ⟨hn, he⟩ (List.rel_of_pairwise_cons hA m₂)
    · rcases List.mem_cons.mp h₂ with r₂ | m₂
      · subst r₂; exact absurd ⟨hn.symm, he.symm⟩ (List.rel_of_pairwise_cons hA m₁)
      · exact ih hA.of_cons e₁ m₁ e₂ m₂ hn he

/-- The table's answer where the table has one, `ρP`'s everywhere else. -/
noncomputable def tabEnv (A : List Eintrag) (ρP : Gabbro.Body.Env) : Gabbro.Body.Env := fun n t =>
  haveI := Classical.propDecidable (∃ e ∈ A, e.name = n ∧ e.ein = t)
  if h : ∃ e ∈ A, e.name = n ∧ e.ein = t then (Classical.choose h).aus else ρP n t

theorem tabEnv_treu {A : List Eintrag} (hA : Schluessel A) (ρP : Gabbro.Body.Env) :
    Treu A (tabEnv A ρP) := by
  intro e he
  have hex : ∃ e' ∈ A, e'.name = e.name ∧ e'.ein = e.ein := ⟨e, he, rfl, rfl⟩
  simp only [tabEnv, dif_pos hex]
  obtain ⟨hm, hn, hi⟩ := Classical.choose_spec hex
  rw [schluessel_eind hA _ hm e he hn hi]

/-! ## 3. Transport of a run along the lowering's type equations -/

theorem execEnd_heq {D : Deklaration} {V : Vertrag D} {Γ₁ Γ₂ : Ctx} {Λ₁ Λ₂ : List (Res D)}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hΓ : Γ₁ = Γ₂) (hΛ : Λ₁ = Λ₂) (b₁ : Endblock D V false Γ₁ Λ₁) (b₂ : Endblock D V false Γ₂ Λ₂)
    (hb : HEq b₁ b₂) (σ : World D) (ρ₁ : Env D Γ₁) (ρ₂ : Env D Γ₂) (hρ : HEq ρ₁ ρ₂) :
    HEq (execEnd O passes R b₁ σ ρ₁) (execEnd O passes R b₂ σ ρ₂) := by
  subst hΓ; subst hΛ; cases hb; cases hρ; rfl

theorem zurueck_heq {D : Deklaration} {V : Vertrag D} {Γ₁ Γ₂ : Ctx} (hΓ : Γ₁ = Γ₂)
    (x₁ : EndAusgang V false Γ₁) (x₂ : EndAusgang V false Γ₂) (hx : HEq x₁ x₂)
    (σ' : World D) (v : ErgVal D V.erg) :
    x₁ = .zurueck σ' v ↔ x₂ = .zurueck σ' v := by
  subst hΓ; cases hx; rfl

theorem logik_heq {D : Deklaration} {V : Vertrag D} {Γ₁ Γ₂ : Ctx} (hΓ : Γ₁ = Γ₂)
    (x₁ : EndAusgang V false Γ₁) (x₂ : EndAusgang V false Γ₂) (hx : HEq x₁ x₂) (e : Logik D) :
    x₁ = .logik e ↔ x₂ = .logik e := by
  subst hΓ; cases hx; rfl

/-! ## 4. The simulation theorem -/

/-- The Body entry state of `c` at a G entry: the G world written over a zero world, every
    parameter name bound to its position's value. -/
def eintritt (u : UProg) (c : Fin u.fns.length) (σ : World (declOf u))
    (ρ : Env (declOf u) ((declOf u).params c)) : Gabbro.Body.State :=
  ⟨encG u σ (fun _ => .int 0), fun p => match paramPos (fnAt u c).params p with
    | .ok j => nthVal ρ j
    | .error _ => .absent⟩

theorem eintritt_lrel (c : Fin u.fns.length) (σ : World (declOf u))
    (ρ : Env (declOf u) ((declOf u).params c)) : LRel (fnAt u c) 0 ρ (eintritt u c σ ρ).local' := by
  intro p j hj
  simp [eintritt, hj]

end Gabbro.Bruecke
