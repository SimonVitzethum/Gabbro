module
public import Bruecke.Anweisung.Lokal.Werte
public import Bruecke.Anweisung.Lokal.UmbenennungSchritt
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- A pointer store reads caller expressions through the positional visible projection. -/
theorem lowAssignDurch_named_sim (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {ns : BodyNames}
    {Λ : List (Res (declOf u))} {b fname : String} {ix : UIdx} {v : USide}
    {g : Stmt (declOf u) (verOf u c) false Γ Λ Λ} {bst : Gabbro.Body.Stmt}
    (h : lowAssignDurchL (l := false) u c Γ fn Λ b fname ix v = .ok g)
    (hb : namedStmt u fn ns (.assign b fname ix v) = some bst)
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ σ₁ cn k fld val, execStmt O passes R g σ ρ = .ok σ₁ ρ ∧
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB bst s =
        .running ⟨Gabbro.Body.store s.world (.slot cn k fld) val, s.local'⟩) ∧
      WGRel u σ₁ (Gabbro.Body.store s.world (.slot cn k fld) val) ∧
      (fnAt u c).puts.any (· == cn) = true := by
  obtain ⟨raw, hr, hn⟩ := namedStmt_some hb
  obtain ⟨σ₁, cn, k, fld, val, hex, hs, hw, hp⟩ := lowAssignDurch_simB c h hr hU hT
    O passes R σ ρ ⟨s.world, ns.visible fn s.local'⟩ hW (hL.visible (ns := ns))
  refine ⟨σ₁, cn, k, fld, val, hex, fun ρB => ?_, hw, hp⟩
  rw [step_renameStep (ns.lookup fn) ρB s raw bst hn]
  have hs' := hs ρB
  change Gabbro.Body.step ρB raw ⟨s.world, visibleBinding (ns.lookup fn) s.local'⟩ = _ at hs'
  rw [hs']

/-- A table store uses the same renaming and leaves every positional local unchanged. -/
theorem lowAssignTab_named_sim (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {ns : BodyNames}
    {Λ : List (Res (declOf u))} {b fname : String} {ix : UIdx} {v : USide}
    {g : Stmt (declOf u) (verOf u c) false Γ Λ Λ} {bst : Gabbro.Body.Stmt}
    (h : lowAssignTabL (l := false) u c Γ fn Λ b fname ix v = .ok g)
    (hb : namedStmt u fn ns (.assignTab b fname ix v) = some bst)
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ σ₁ cn k fld val, execStmt O passes R g σ ρ = .ok σ₁ ρ ∧
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB bst s =
        .running ⟨Gabbro.Body.store s.world (.slot cn k fld) val, s.local'⟩) ∧
      WGRel u σ₁ (Gabbro.Body.store s.world (.slot cn k fld) val) ∧
      (fnAt u c).puts.any (· == cn) = true := by
  obtain ⟨raw, hr, hn⟩ := namedStmt_some hb
  obtain ⟨σ₁, cn, k, fld, val, hex, hs, hw, hp⟩ := lowAssignTab_simB c h hr hU hT
    O passes R σ ρ ⟨s.world, ns.visible fn s.local'⟩ hW (hL.visible (ns := ns))
  refine ⟨σ₁, cn, k, fld, val, hex, fun ρB => ?_, hw, hp⟩
  rw [step_renameStep (ns.lookup fn) ρB s raw bst hn]
  have hs' := hs ρB
  change Gabbro.Body.step ρB raw ⟨s.world, visibleBinding (ns.lookup fn) s.local'⟩ = _ at hs'
  rw [hs']

end Gabbro.Bruecke
