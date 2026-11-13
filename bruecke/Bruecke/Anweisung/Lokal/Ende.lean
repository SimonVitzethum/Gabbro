module
public import Bruecke.Anweisung.Lokal.Werte
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- **The trailing return**, in every scope: a returned value may read a local. -/
theorem lowEnd_simB (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {ns : BodyNames} {Λ : List (Res (declOf u))}
    {r : URet} {eb : Endblock (declOf u) (verOf u c) false Γ Λ} {eB : List Gabbro.Body.Stmt}
    (h : lowEnd u c Γ Λ fn r = .ok eb) (hb : namedEnd u fn ns r = some eB)
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ σ' v, execEnd O passes R eb σ ρ = .zurueck σ' v ∧ WGRel u σ' s.world ∧
      ∀ ρB : Gabbro.Body.Env, Gabbro.Body.finalState (Gabbro.Body.exec ρB eB s) = some s ∧
        Gabbro.Body.finalValue (Gabbro.Body.exec ρB eB s) = ergValOf (verOf u c).erg v := by
  have hA := hU.art
  cases r
  case empty =>
    simp only [namedEnd, Option.some.injEq] at hb
    subst hb
    simp only [lowEnd] at h
    split at h
    · cases h
    · rename_i E hE
      split at h
      · cases h
        refine ⟨_, _, rfl, wgrel_same u rfl rfl hW, fun ρB => ⟨rfl, ?_⟩⟩
        simp only [lowErg] at hE
        split at hE
        · rename_i hErg
          have he : (verOf u c).erg = none := by
            show (vertragVon (declOf u) c).erg = none
            rw [vErg_eq u c, hErg]
          rw [ergValOf_none _ he]
          rfl
        · cases hE
      · cases h
  case val sd =>
    simp only [namedEnd] at hb
    cases hs : namedSide u fn ns sd with
    | none => rw [hs] at hb; cases hb
    | some e =>
      rw [hs] at hb
      simp only [Option.map_some, Option.some.injEq] at hb
      subst hb
      simp only [lowEnd] at h
      split at h
      · cases h
      · rename_i E hE
        split at h
        · cases h
          simp only [lowErg] at hE
          split at hE
          · rename_i lo hi hErg
            split at hE
            · cases hE
            · rename_i ve hve
              cases hE
              refine ⟨_, _, rfl, wgrel_same u rfl rfl hW, fun ρB => ?_⟩
              obtain ⟨sw, sl⟩ := s
              have herg : (verOf u c).erg = some (.int lo hi) := by
                show (vertragVon (declOf u) c).erg = _
                rw [vErg_eq u c, hErg]
              generalize hσl : σ.lese _ _ = σl
              have hWl : WGRel u σl sw := by rw [← hσl]; exact wgrel_same u rfl rfl hW
              have hv := lowWertAt_named_sim hve hs hA hT σl σl ρ ⟨sw, sl⟩ hWl hL
              rw [ergValOf_heq herg _ (evalErg σl (ErgExpr.val (D := declOf u) ve) σl ρ)
                (evalErg_heq herg _ _ (mpr3_heq _ _ _ _) _ _ _)]
              simp only [Gabbro.Body.exec, Gabbro.Body.step, hv, Gabbro.Body.finalState,
                Gabbro.Body.finalValue]
              trivial
          · cases hE
          · cases hE
        · cases h
  all_goals simp only [namedEnd, reduceCtorEq] at hb

end Gabbro.Bruecke
