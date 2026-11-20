module
public import Bruecke.Anweisung.Match.Werte
public import Bruecke.Anweisung.Option.Scope
public import Bruecke.Ausdruck.Option
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

/-- Optional indices use the same visible projection as numeric and record values. -/
theorem lowOption_named_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {ns : BodyNames} {num : Nat} {hn : num < u.tabs.length} {v : UOpt}
    {ev : Expr (declOf u) Γ Λ (.opt ((declOf u).count ⟨num, hn⟩))} {e : Gabbro.Body.Expr}
    (h : lowOpt u Γ Λ fn 0 num hn v = .ok ev) (hb : namedOption u fn ns v = some e)
    (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    Gabbro.Body.eval s e = some (valOf (.opt ((declOf u).count ⟨num, hn⟩)) (eval σ₀ ev σ ρ)) := by
  cases v with
  | nichts =>
    have he : optionZ fn ns .nichts = some e := by
      simpa only [namedOption, optionExpr, bind, Option.bind_some, renameScalar, optionZ] using hb
    exact lowOpt_named_sim h he σ₀ σ ρ s hL
  | etwas ix =>
    have he : optionZ fn ns (.etwas ix) = some e := by
      simpa only [namedOption, optionExpr, bind, Option.bind_some, renameScalar, optionZ] using hb
    exact lowOpt_named_sim h he σ₀ σ ρ s hL
  | var x =>
    unfold namedOption at hb
    cases hr : optionExpr u fn (.var x) with
    | none => simp [hr] at hb
    | some raw =>
      simp only [hr, bind, Option.bind_some] at hb
      rw [eval_renameScalar (ns.lookup fn) s raw e hb]
      exact lowOpt_sim h hr hT σ₀ σ ρ ⟨s.world, ns.visible fn s.local'⟩ hW.1
        (hL.visible (ns := ns))
  | tab t fld ix =>
    unfold namedOption at hb
    cases hr : optionExpr u fn (.tab t fld ix) with
    | none => simp [hr] at hb
    | some raw =>
      simp only [hr, bind, Option.bind_some] at hb
      rw [eval_renameScalar (ns.lookup fn) s raw e hb]
      exact lowOpt_sim h hr hT σ₀ σ ρ ⟨s.world, ns.visible fn s.local'⟩ hW.1
        (hL.visible (ns := ns))
  | slot p fld ix =>
    unfold namedOption at hb
    cases hr : optionExpr u fn (.slot p fld ix) with
    | none => simp [hr] at hb
    | some raw =>
      simp only [hr, bind, Option.bind_some] at hb
      rw [eval_renameScalar (ns.lookup fn) s raw e hb]
      exact lowOpt_sim h hr hT σ₀ σ ρ ⟨s.world, ns.visible fn s.local'⟩ hW.1
        (hL.visible (ns := ns))
  | glob => simp only [namedOption, optionExpr, bind, Option.bind_none, reduceCtorEq] at hb

/-- A source option binder preserves its exact table identity and all outer entries. -/
theorem lowBindOpt_named_sim {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {ns : BodyNames} {x : String} {num : Nat} {hn : num < u.tabs.length} {v : UOpt}
    {ev : Expr (declOf u) Γ Λ (.opt ((declOf u).count ⟨num, hn⟩))} {e : Gabbro.Body.Expr}
    (h : lowOpt u Γ Λ fn 0 num hn v = .ok ev) (hb : namedOption u fn ns v = some e)
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ bv : Gabbro.Body.Value,
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB (.bindName (ns.fresh x) e) s =
        .running ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩) ∧
      WGRel u (σ.lese Λ ev.orte) s.world ∧
      PositionalLRel (fn.mitOpt x num ((declOf u).count ⟨num, hn⟩)) (ns.push x).active 0
        (Env.cons (eval (σ.lese Λ ev.orte) ev (σ.lese Λ ev.orte) ρ) ρ)
        (Gabbro.Body.bindLocal s.local' (ns.fresh x) bv) := by
  have hWl := wgrel_lese u hW Λ ev.orte
  have hv := lowOption_named_sim h hb hT (σ.lese Λ ev.orte) (σ.lese Λ ev.orte) ρ s hWl hL
  refine ⟨_, fun ρB => ?_, hWl, hL.pushOpt x (ns.fresh x) num _
    (BodyNames.fresh_not_active hU.valid x) _⟩
  simp only [Gabbro.Body.step, hv]

/-- Assigning an option updates its resolved position, including a shadowed scope. -/
theorem lowSetVarOpt_named_sim {loopMode : Bool} (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn}
    {ns : BodyNames} {Λ : List (Res (declOf u))} {x id : String} {num : Nat} {v : UOpt}
    {g : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ} {e : Gabbro.Body.Expr}
    (h : lowSetVarOptL (l := loopMode) u c Γ fn Λ x num v = .ok g)
    (hid : ns.lookup fn x = some id) (hb : namedOption u fn ns v = some e)
    (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ (σ₁ : World (declOf u)) (ρ₁ : Env (declOf u) Γ) (bv : Gabbro.Body.Value),
      execStmt O passes R g σ ρ = .ok σ₁ ρ₁ ∧ WGRel u σ₁ s.world ∧
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB (.bindName id e) s =
        .running ⟨s.world, Gabbro.Body.bindLocal s.local' id bv⟩) ∧
      PositionalLRel fn ns.active 0 ρ₁ (Gabbro.Body.bindLocal s.local' id bv) := by
  unfold lowSetVarOptL at h
  split at h
  · rename_i hn
    split at h
    · cases h
    · rename_i j hj
      have hid' : ns.active[j]? = some id := by
        simpa only [BodyNames.lookup, hj] using hid
      split at h
      · cases h
      · rename_i var hvar
        split at h
        · cases h
        · rename_i ev hev
          cases h
          have hWl := wgrel_lese u hW Λ ev.orte
          have hv := lowOption_named_sim hev hb hT (σ.lese Λ ev.orte) (σ.lese Λ ev.orte) ρ s hWl hL
          refine ⟨σ.lese Λ ev.orte,
            ρ.set var (eval (σ.lese Λ ev.orte) ev (σ.lese Λ ev.orte) ρ),
            _, rfl, hWl, fun ρB => ?_, hL.set hid' var hvar _⟩
          simp only [Gabbro.Body.step, hv]
  · cases h

end Gabbro.Bruecke
