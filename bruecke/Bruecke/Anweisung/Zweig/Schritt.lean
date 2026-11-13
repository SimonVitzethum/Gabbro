module
public import Bruecke.Anweisung.Zweig.Strecke
public import Bruecke.Anweisung.Zweig.Lesen
public import Bruecke.Anweisung.Lokal.Werte
@[expose] public section

/-!
# Return-statement simulation

`lowRet_sim` relates a canonical lowered return to Body's translated return in any related
scope and world. The consolidated chain supplies the surrounding carried statement claim.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- **`return [v];` inside a block** (`lowRetStmt` without crossed scopes): the G statement returns
    the value the Body `ret` returns, the world kept. -/
theorem lowRet_sim (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {ns : BodyNames} {Λ : List (Res (declOf u))}
    {r : URet} {st : Stmt (declOf u) (verOf u c) false Γ Λ Λ} {bst : Gabbro.Body.Stmt}
    (h : lowRetStmt (l := false) u c Γ fn Λ [] r = .ok st) (hb : retZ u fn ns r = some bst)
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ σ' v, execStmt O passes R st σ ρ = .zurueck σ' v ∧ WGRel u σ' s.world ∧
      ∀ ρB : Gabbro.Body.Env,
        Gabbro.Body.step ρB bst s = .returned s (ergValOf (verOf u c).erg v) := by
  have hA := hU.art
  cases r
  case empty =>
    simp only [retZ, Option.some.injEq] at hb
    subst hb
    simp only [lowRetStmt] at h
    cases hE : lowErg u c Γ Λ fn .empty with
    | error e => simp only [hE, Except.bind] at h <;> cases h
    | ok E =>
      simp only [hE, Except.bind] at h
      split at h
      · cases h
        refine ⟨_, _, rfl, wgrel_same u rfl rfl hW, fun ρB => ?_⟩
        simp only [lowErg] at hE
        split at hE
        · rename_i hErg
          have he : (verOf u c).erg = none := by
            show (vertragVon (declOf u) c).erg = none
            rw [vErg_eq u c, hErg]
          rw [ergValOf_none _ he]
          all_goals first
            | rfl
            | simp only [Gabbro.Body.step]
        · cases hE
      · cases h
  case val sd =>
    simp only [retZ] at hb
    cases hs : namedSide u fn ns sd with
    | none => rw [hs] at hb; cases hb
    | some e =>
      rw [hs] at hb
      simp only [Option.map_some, Option.some.injEq] at hb
      subst hb
      simp only [lowRetStmt] at h
      cases hE : lowErg u c Γ Λ fn (.val sd) with
      | error err => simp only [hE, Except.bind] at h <;> cases h
      | ok E =>
        simp only [hE, Except.bind] at h
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
              simp only [Gabbro.Body.step, hv]
              all_goals first
                | rfl
                | trivial
          · cases hE
          · cases hE
        · cases h
  all_goals simp [retZ] at hb

end Gabbro.Bruecke
