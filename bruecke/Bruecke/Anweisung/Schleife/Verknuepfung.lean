module
public import Bruecke.Anweisung.Schleife.Kontrolle
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {C : Fin u.fns.length → Prop} {c : Fin u.fns.length}
  {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
  {l : Bool} {Γ : Ctx} {fn : UFn} {ids : List String}
  {out : Ausgang (verOf u c) l Γ} {s s₁ : Gabbro.Body.State}
  {xs ys : List Gabbro.Body.Stmt}

/-- Change only the execution presentation, preserving all four pass channels. -/
theorem ausgangZiel_map
    (h : AusgangZiel_G u C c R fn ids out s xs)
    (he : ∀ ρB, Gabbro.Body.exec ρB ys s = Gabbro.Body.exec ρB xs s) :
    AusgangZiel_G u C c R fn ids out s ys := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro σ v hv
    obtain ⟨A, hg, ho, hk, hr⟩ := h.2.1 σ v hv
    exact ⟨A, hg, ho, hk, fun ρB hT hF => by rw [he]; exact hr ρB hT hF⟩
  · intro σ ρ hv
    obtain ⟨A, t, ht, hw, hl⟩ := h.2.2.1 σ ρ hv
    exact ⟨A, t, { ht with lauf := fun ρB hT hF => by rw [he]; exact ht.lauf ρB hT hF }, hw, hl⟩
  · intro leave hloop σ ρ hv
    obtain ⟨A, t, ht, hw, hl⟩ := h.2.2.2 leave hloop σ ρ hv
    exact ⟨A, t, { ht with lauf := fun ρB hT hF => by rw [he]; exact ht.lauf ρB hT hF }, hw, hl⟩

/-- A running prefix composes with normal completion, returns and either loop exit. -/
theorem ausgangZiel_nach {A : List Eintrag}
    (hp : Strecke_G u C A s s₁ xs) (h : AusgangZiel_G u C c R fn ids out s₁ ys) :
    AusgangZiel_G u C c R fn ids out s (xs ++ ys) := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro σ v hv
    obtain ⟨B, hr⟩ := h.2.1 σ v hv
    exact ⟨A ++ B, RueckZ_G.nach hp hr⟩
  · intro σ ρ hv
    obtain ⟨B, t, ht, hw, hl⟩ := h.2.2.1 σ ρ hv
    exact ⟨A ++ B, t, hp.append ht, hw, hl⟩
  · intro leave hloop σ ρ hv
    obtain ⟨B, t, ht, hw, hl⟩ := h.2.2.2 leave hloop σ ρ hv
    exact ⟨A ++ B, t, hp.append ht, hw, hl⟩

/-- Every non-running canonical outcome skips the rest of the source block. -/
theorem ausgangZiel_suffix (h : AusgangZiel_G u C c R fn ids out s xs)
    (hn : ∀ σ ρ, out ≠ .ok σ ρ) (zs : List Gabbro.Body.Stmt) :
    AusgangZiel_G u C c R fn ids out s (xs ++ zs) := by
  refine ⟨h.1, ?_, fun σ ρ he => (hn σ ρ he).elim, ?_⟩
  · intro σ v hv
    obtain ⟨A, hr⟩ := h.2.1 σ v hv
    exact ⟨A, hr.append zs⟩
  · intro leave hloop σ ρ hv
    obtain ⟨A, t, ht, hw, hl⟩ := h.2.2.2 leave hloop σ ρ hv
    exact ⟨A, t, ht.control_append zs, hw, hl⟩

/-- Leaving a local scope removes its source entry on both control channels too. -/
theorem ausgangZiel_schrumpf {τ : Ty} {fn' : UFn} {ids' : List String}
    {a : Ausgang (verOf u c) l (τ :: Γ)} {A : List Eintrag}
    (hp : Strecke_G u C A s s₁ xs)
    (tail : ∀ (ρ : Env (declOf u) (τ :: Γ)) β,
      PositionalLRel fn' ids' 0 ρ β → PositionalLRel fn ids 0 ρ.tail β)
    (h : AusgangZiel_G u C c R fn' ids' a s₁ ys) :
    AusgangZiel_G u C c R fn ids a.schrumpf s (xs ++ ys) := by
  apply ausgangZiel_nach hp
  refine ⟨fun e he => h.1 e (schrumpfZ_logik he),
    fun σ v he => h.2.1 σ v (schrumpfZ_zurueck he), ?_, ?_⟩
  · intro σ ρ he
    obtain ⟨ρ', hin, rfl⟩ := schrumpfZ_ok he
    obtain ⟨B, t, ht, hw, hl⟩ := h.2.2.1 σ ρ' hin
    exact ⟨B, t, ht, hw, tail _ _ hl⟩
  · intro leave hloop σ ρ he
    obtain ⟨ρ', hin, rfl⟩ := schrumpfZ_control he
    obtain ⟨B, t, ht, hw, hl⟩ := h.2.2.2 leave hloop σ ρ' hin
    exact ⟨B, t, ht, hw, tail _ _ hl⟩

end Gabbro.Bruecke
