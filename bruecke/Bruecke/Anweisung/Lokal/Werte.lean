module
public import Bruecke.Anweisung.Lokal.RecordScope
public import Bruecke.Anweisung.Lokal.Benannt
public import Bruecke.Anweisung.Lokal.Bindung
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- Conditions, bool bindings and bool returns share the same positional expression path. -/
theorem lowEns_named_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {ns : BodyNames} {v : UEns} {ev : Expr (declOf u) Γ Λ .bool} {e : Gabbro.Body.Expr}
    (h : lowEns u Γ Λ fn none v = .ok ev) (hb : condZ u fn ns v = some e)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW₀ : WGRel u σ₀ s.world) (hW : WGRel u σ s.world)
    (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    Gabbro.Body.eval s e = some (valOf .bool (eval σ₀ ev σ ρ)) := by
  obtain ⟨raw, a, hens, hold, hres, hn⟩ := condZ_some hb
  have hvL := hL.visible (ns := ns)
  let sv : Gabbro.Body.State := ⟨s.world, ns.visible fn s.local'⟩
  have hB : EnsBind fn none ρ sv a sv.local' :=
    ⟨hvL, fun hr => (by rw [hres] at hr; cases hr),
      fun i hi => (by rw [hold] at hi; exact absurd hi (Nat.not_lt_zero _))⟩
  have hv := lowEns_sim (er := none) hA hT σ₀ σ ρ sv s.world sv.local' a
    hW₀ hvL hW hB v hens h (Vor.refl a)
  change Gabbro.Body.eval ⟨s.world, visibleBinding (ns.lookup fn) s.local'⟩ raw =
    some (valOf .bool (eval σ₀ ev σ ρ)) at hv
  exact (eval_renameScalar (ns.lookup fn) s raw e hn).trans hv

/-- Scalar simulation reuses the source reader through the positional visible projection. -/
theorem lowSideVal_named_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {ns : BodyNames} {v : USide} {ls : LowSide u Γ Λ} {e : Gabbro.Body.Expr}
    (h : lowSideVal u Γ Λ fn v = .ok ls) (hb : namedSide u fn ns v = some e)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    Gabbro.Body.eval s e =
      some (valOf (.int ls.range.1 ls.range.2) (eval σ₀ ls.term σ ρ)) := by
  obtain ⟨raw, hr, hn⟩ := namedSide_some hb
  rw [eval_renameScalar (ns.lookup fn) s raw e hn]
  exact lowSideVal_sim h hr hA hT σ₀ σ ρ s.world (ns.visible fn s.local') hW
    (hL.visible (ns := ns))

/-- Fitting the scalar at a declared range commutes with identifier renaming. -/
theorem lowWertAt_named_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {ns : BodyNames} {lo hi : Int} {v : USide}
    {ev : Expr (declOf u) Γ Λ (.int lo hi)} {e : Gabbro.Body.Expr}
    (h : lowWertAt u Γ Λ fn lo hi v = .ok ev) (hb : namedSide u fn ns v = some e)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    Gabbro.Body.eval s e = some (valOf (.int lo hi) (eval σ₀ ev σ ρ)) := by
  obtain ⟨raw, hr, hn⟩ := namedSide_some hb
  rw [eval_renameScalar (ns.lookup fn) s raw e hn]
  exact lowWertAt_sim h hr hA hT σ₀ σ ρ s.world (ns.visible fn s.local') hW
    (hL.visible (ns := ns))

/-- Record checking mode uses the same visible positional scope as scalar values. -/
theorem lowWertAtE_named_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {ns : BodyNames} {ty : Ty} {v : USide}
    {ev : Expr (declOf u) Γ Λ ty} {e : Gabbro.Body.Expr}
    (h : lowWertAtE u Γ Λ fn none ty v = .ok ev) (hb : namedSide u fn ns v = some e)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    Gabbro.Body.eval s e = some (valOf ty (eval σ₀ ev σ ρ)) := by
  obtain ⟨raw, hr, hn⟩ := namedSide_some hb
  rw [eval_renameScalar (ns.lookup fn) s raw e hn]
  exact lowWertAtE_rec_sim (er := none) h hr hA hT σ₀ σ ρ s.world
    (ns.visible fn s.local') hW (hL.visible (ns := ns))

/-- A numeric source binder pushes a fresh Body identifier even when its source name exists. -/
theorem lowBind_named_sim {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {ns : BodyNames} {x : String} {d : Option (Int × Int)} {v : USide}
    {ls : LowSide u Γ Λ} {e : Gabbro.Body.Expr}
    (h : lowBindWert u Γ Λ fn d v = .ok ls) (hb : namedSide u fn ns v = some e)
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u) (hN : ns.Valid)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ bv : Gabbro.Body.Value,
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB (.bindName (ns.fresh x) e) s =
        .running ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩) ∧
      WGRel u (σ.lese Λ ls.term.orte) s.world ∧
      PositionalLRel (fn.mitBindung x ls.range) (ns.push x).active 0
        (Env.cons (eval (σ.lese Λ ls.term.orte) ls.term (σ.lese Λ ls.term.orte) ρ) ρ)
        (Gabbro.Body.bindLocal s.local' (ns.fresh x) bv) := by
  have hWl : WGRel u (σ.lese Λ ls.term.orte) s.world := wgrel_same u rfl rfl hW
  have hv := lowSideVal_named_sim (lowBindWert_side h) hb hU.art hT
    (σ.lese Λ ls.term.orte) (σ.lese Λ ls.term.orte) ρ s hWl hL
  refine ⟨_, fun ρB => ?_, hWl, hL.push x (ns.fresh x) ls.range
    (BodyNames.fresh_not_active hN x) _⟩
  simp only [Gabbro.Body.step, hv]

/-- A mutable numeric source binder uses the same positional push. -/
theorem lowBindMut_named_sim {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {ns : BodyNames} {x : String} {lo hi : Int} {v : USide}
    {ev : Expr (declOf u) Γ Λ (.int lo hi)} {e : Gabbro.Body.Expr}
    (h : lowWertAt u Γ Λ fn lo hi v = .ok ev) (hb : namedSide u fn ns v = some e)
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u) (hN : ns.Valid)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ bv : Gabbro.Body.Value,
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB (.bindName (ns.fresh x) e) s =
        .running ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩) ∧
      WGRel u (σ.lese Λ ev.orte) s.world ∧
      PositionalLRel (fn.mitBindung x (lo, hi)) (ns.push x).active 0
        (Env.cons (eval (σ.lese Λ ev.orte) ev (σ.lese Λ ev.orte) ρ) ρ)
        (Gabbro.Body.bindLocal s.local' (ns.fresh x) bv) := by
  have hWl : WGRel u (σ.lese Λ ev.orte) s.world := wgrel_same u rfl rfl hW
  have hv := lowWertAt_named_sim h hb hU.art hT
    (σ.lese Λ ev.orte) (σ.lese Λ ev.orte) ρ s hWl hL
  refine ⟨_, fun ρB => ?_, hWl, hL.push x (ns.fresh x) (lo, hi)
    (BodyNames.fresh_not_active hN x) _⟩
  simp only [Gabbro.Body.step, hv]

/-- A typed record binder allocates once and retains all outer positional values. -/
theorem lowBindRecord_named_sim {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {ns : BodyNames} {x : String} {id : Nat} {fs : List Ty} {v : USide}
    {ev : Expr (declOf u) Γ Λ (.prod id fs)} {e : Gabbro.Body.Expr}
    (h : lowWertAtE u Γ Λ fn none (.prod id fs) v = .ok ev)
    (hb : namedSide u fn ns v = some e) (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ bv : Gabbro.Body.Value,
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB (.bindName (ns.fresh x) e) s =
        .running ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩) ∧
      WGRel u (σ.lese Λ ev.orte) s.world ∧
      PositionalLRel (fn.mitWert x (.prod id fs)) (ns.push x).active 0
        (Env.cons (eval (σ.lese Λ ev.orte) ev (σ.lese Λ ev.orte) ρ) ρ)
        (Gabbro.Body.bindLocal s.local' (ns.fresh x) bv) := by
  have hWl : WGRel u (σ.lese Λ ev.orte) s.world := wgrel_same u rfl rfl hW
  have hv := lowWertAtE_named_sim h hb hU.art hT
    (σ.lese Λ ev.orte) (σ.lese Λ ev.orte) ρ s hWl hL
  refine ⟨_, fun ρB => ?_, hWl, hL.pushRecord x (ns.fresh x) id fs
    (BodyNames.fresh_not_active hU.valid x) _⟩
  simp only [Gabbro.Body.step, hv]

/-- Assignment updates the identifier at the source's first-match position. -/
theorem lowSetVar_named_sim {loopMode : Bool} (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn}
    {ns : BodyNames} {Λ : List (Res (declOf u))} {x id : String} {v : USide}
    {g : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ} {e : Gabbro.Body.Expr}
    (h : lowSetVarL (l := loopMode) u c Γ fn Λ x v = .ok g)
    (_hn : assignableParam fn x = true) (hid : ns.lookup fn x = some id)
    (hb : namedSide u fn ns v = some e) (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ (σ₁ : World (declOf u)) (ρ₁ : Env (declOf u) Γ) (bv : Gabbro.Body.Value),
      execStmt O passes R g σ ρ = .ok σ₁ ρ₁ ∧ WGRel u σ₁ s.world ∧
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB (.bindName id e) s =
        .running ⟨s.world, Gabbro.Body.bindLocal s.local' id bv⟩) ∧
      PositionalLRel fn ns.active 0 ρ₁ (Gabbro.Body.bindLocal s.local' id bv) := by
  obtain ⟨raw, hr, he⟩ := namedSide_some hb
  unfold lowSetVarL at h
  split at h
  · cases h
  · rename_i j hj
    have hid' : ns.active[j]? = some id := by
      simpa only [BodyNames.lookup, hj] using hid
    split at h
    · rename_i nm ty hty
      split at h
      · cases h
      · rename_i var hvar
        split at h
        · cases h
        · rename_i ev hev
          cases h
          have hWl : WGRel u (σ.lese Λ ev.orte) s.world := wgrel_same u rfl rfl hW
          have hv : Gabbro.Body.eval s e = some (valOf ty
              (eval (σ.lese Λ ev.orte) ev (σ.lese Λ ev.orte) ρ)) := by
            rw [eval_renameScalar (ns.lookup fn) s raw e he]
            exact lowWertAtE_rec_sim (er := none) hev hr hU.art hT (σ.lese Λ ev.orte)
              (σ.lese Λ ev.orte) ρ s.world (ns.visible fn s.local') hWl
              (hL.visible (ns := ns))
          refine ⟨σ.lese Λ ev.orte,
            ρ.set var (eval (σ.lese Λ ev.orte) ev (σ.lese Λ ev.orte) ρ),
            _, rfl, hWl, fun ρB => ?_, hL.set hid' var hvar _⟩
          simp only [Gabbro.Body.step, hv]
    · cases h

/-- Bool bindings allocate once and retain hidden scalar entries, just like number bindings. -/
theorem lowBindB_named_sim {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {ns : BodyNames} {x : String} {v : UEns}
    {ev : Expr (declOf u) Γ Λ .bool} {e : Gabbro.Body.Expr}
    (h : lowEns u Γ Λ fn none v = .ok ev) (hb : condZ u fn ns v = some e)
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ bv : Gabbro.Body.Value,
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB (.bindName (ns.fresh x) e) s =
        .running ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩) ∧
      WGRel u (σ.lese Λ ev.orte) s.world ∧
      PositionalLRel (fn.mitBindungB x) (ns.push x).active 0
        (Env.cons (eval (σ.lese Λ ev.orte) ev (σ.lese Λ ev.orte) ρ) ρ)
        (Gabbro.Body.bindLocal s.local' (ns.fresh x) bv) := by
  have hWl : WGRel u (σ.lese Λ ev.orte) s.world := wgrel_same u rfl rfl hW
  have hv := lowEns_named_sim h hb hU.art hT
    (σ.lese Λ ev.orte) (σ.lese Λ ev.orte) ρ s hWl hWl hL
  refine ⟨_, fun ρB => ?_, hWl, hL.pushB x (ns.fresh x)
    (BodyNames.fresh_not_active hU.valid x) _⟩
  simp only [Gabbro.Body.step, hv]

/-- Bool assignment resolves the same first-match position as the canonical lowering. -/
theorem lowSetVarB_named_sim {loopMode : Bool} (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn}
    {ns : BodyNames} {Λ : List (Res (declOf u))} {x id : String} {v : UEns}
    {g : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ} {e : Gabbro.Body.Expr}
    (h : lowSetVarBL (l := loopMode) u c Γ fn Λ x v = .ok g)
    (hid : ns.lookup fn x = some id) (hb : condZ u fn ns v = some e)
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ (σ₁ : World (declOf u)) (ρ₁ : Env (declOf u) Γ) (bv : Gabbro.Body.Value),
      execStmt O passes R g σ ρ = .ok σ₁ ρ₁ ∧ WGRel u σ₁ s.world ∧
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB (.bindName id e) s =
        .running ⟨s.world, Gabbro.Body.bindLocal s.local' id bv⟩) ∧
      PositionalLRel fn ns.active 0 ρ₁ (Gabbro.Body.bindLocal s.local' id bv) := by
  unfold lowSetVarBL at h
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
        have hWl : WGRel u (σ.lese Λ ev.orte) s.world := wgrel_same u rfl rfl hW
        have hv := lowEns_named_sim hev hb hU.art hT
          (σ.lese Λ ev.orte) (σ.lese Λ ev.orte) ρ s hWl hWl hL
        refine ⟨σ.lese Λ ev.orte,
          ρ.set var (eval (σ.lese Λ ev.orte) ev (σ.lese Λ ev.orte) ρ),
          _, rfl, hWl, fun ρB => ?_, hL.set hid' var hvar _⟩
        simp only [Gabbro.Body.step, hv]

end Gabbro.Bruecke
