/- Shared read, oracle-key and optional-result transports for foreign simulation. -/
module
public import Grammatik.Zielsatz.Einbettung.Koerper.Teil7
@[expose] public section

namespace Gabbro.Grammatik.Einbettung
open Gabbro.Grammatik
namespace Einbettung
variable {D D' : Deklaration} (E : Einbettung D D') (hZ : E.Rueck)

/-- Bind an optional answer across its actual declared result equalities. -/
theorem foreign_result_env {Γ : Ctx} {ρ : Env D Γ} {ρ' : Env D' (Γ.map E.tyE)}
    (hρ : E.EnvR hZ ρ ρ') {e source target : Option Ty}
    (he : source = e) (he' : target = e.map E.tyE) (ha : target = source.map E.tyE)
    (v : ErgVal D source) :
    E.EnvR hZ (ergEnv e (he ▸ v) ρ)
      (castE (E.ergCtxE Γ e).symm
        (ergEnv (e.map E.tyE) (he' ▸ castV ha.symm (E.ergE source v)) ρ')) := by
  subst source
  subst target
  apply (E.envR_um hZ (E.ergCtxE Γ e).symm _ _).mpr
  cases e with
  | none => exact hρ
  | some τ => exact E.envR_cons hZ hρ _ _ rfl (E.vrel_valE hZ τ v)

/-- Optional success drops exactly the local introduced by its result option. -/
theorem ausRel_weiterOpt {M : Keys D D'} {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx}
    {e : Option Ty} {o : Ausgang V l (ErgCtx Γ e)}
    {o' : Ausgang (E.vertragE V) l (ErgCtx Γ' (e.map E.tyE))}
    (h : E.AusRel hZ M o o') :
    E.AusRel hZ M (Ausgang.weiterOpt e o) (Ausgang.weiterOpt (e.map E.tyE) o') := by
  cases e with
  | none => exact h
  | some _ => exact E.ausRel_schrumpf h

theorem endRel_weiterOpt {M : Keys D D'} {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx}
    {e : Option Ty} {o : EndAusgang V l (ErgCtx Γ e)}
    {o' : EndAusgang (E.vertragE V) l (ErgCtx Γ' (e.map E.tyE))}
    (h : E.EndRel hZ M o o') :
    E.EndRel hZ M (EndAusgang.weiterOpt e o) (EndAusgang.weiterOpt (e.map E.tyE) o') := by
  cases e with
  | none => exact h
  | some _ => exact E.endRel_schrumpf h

variable (pad : List (Ereignis D)) (S : SperrInv D) (T : D.Tab ⊕ D.Glob → Prop)
  (S' : SperrInv D') (T' : D'.Tab ⊕ D'.Glob → Prop) (O' : Orakel D')
  (U' : Umwelt D') (A' : AUmwelt D') (hB : E.Bed hZ pad S T S' T' U' A')
include hB

/-- Read the full argument footprint, then reuse the canonical oracle key once.
    Every answer world remains related under the same enlarged key set. -/
theorem foreign_read {Γ : Ctx} {Λ : List (Res D)} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) {M : Keys D D'} {σ : World D} {σ' : World D'}
    {ρ : Env D Γ} {ρ' : Env D' (Γ.map E.tyE)}
    (hM : E.Inv hZ M σ σ') (hρ : E.EnvR hZ ρ ρ') :
    let readWorld := leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)
    ∃ (M₁ : Keys D D') (σ₁ : World D), Teil M M₁ ∧
      (∀ Φ, Passt Φ M₁ → leseA (E.aumweltΦ hZ Φ T A') σ Λ args.orte = σ₁) ∧
      (∀ Φ, Passt Φ M₁ → (E.orakelΦ hZ pad Φ O').wirkt a (σ₁.fragt (.inl a))
        (evalArgs σ₁ args σ₁ ρ) =
          (E.antwortWelt hZ pad (σ₁.fragt (.inl a))
            (O'.wirkt (E.ax a) (readWorld.fragt (.inl (E.ax a)))
              (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1,
            (O'.wirkt (E.ax a) (readWorld.fragt (.inl (E.ax a)))
              (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2)) ∧
      (∀ W, E.Inv hZ M₁ (E.antwortWelt hZ pad (σ₁.fragt (.inl a)) W) W) ∧
      evalArgs readWorld (exA E args) readWorld ρ' = E.envE (evalArgs σ₁ args σ₁ ρ) := by
  dsimp only
  obtain ⟨M₁, σ₁, hs, hread, hI, _⟩ := E.lese_eval hZ hM T hB.havocA hB.atom
    Λ (Λ.map E.resE) args.orte
  obtain ⟨M₂, hs2, hOracle, hI2⟩ := E.ax_schluessel hZ pad O'
    hI a (evalArgs σ₁ args σ₁ ρ)
  exact ⟨M₂, σ₁, teil_trans hs hs2, fun Φ hP => hread Φ (passt_teil hP hs2),
    hOracle, fun W => E.inv_antwort hZ hB.pad hI2 W,
    E.envR_eq_frei hZ (hZ.frei.aparamsFrei a) _ _
      (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)⟩

end Einbettung
end Gabbro.Grammatik.Einbettung
