module
public import Bruecke.Anweisung.Summe.Kopf
public import Bruecke.Anweisung.Option.Werte
public import Bruecke.Kette.Verknuepfung
@[expose] public section

/-! # `let x = T::C;` simulates its Body binding

The lowered value of a bare tagged value evaluates to a value whose encoding (`valOf`, the case
label) is exactly what the Body reading `namedSum` evaluates to; binding it extends the positional
relation by the new tagged local.
-/

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

/-- **The value read**: the Body reading of a bare tagged value evaluates to the encoding of the
    lowered value. -/
theorem lowSVal_named_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {ns : BodyNames}
    {sidx : Nat} {hs : sidx < u.sums.length} {v : USVal}
    {ev : Expr (declOf u) Γ Λ (.sum (u.sums.get ⟨sidx, hs⟩).spec)} {e : Gabbro.Body.Expr}
    (h : lowSVal u Γ Λ fn 0 sidx hs v = .ok ev)
    (hb : namedSum fn ns (u.sums.get ⟨sidx, hs⟩).spec v = some e)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    Gabbro.Body.eval s e = some (valOf (.sum (u.sums.get ⟨sidx, hs⟩).spec) (eval σ₀ ev σ ρ)) := by
  cases v with
  | fall i pl =>
    cases pl with
    | some _ => simp only [namedSum, reduceCtorEq] at hb
    | none =>
      simp only [namedSum] at hb
      split at hb
      · rename_i hi
        cases hb
        simp only [lowSVal, hi, ↓reduceDIte] at h
        split at h
        · cases h
        · rename_i nz hnz
          cases h
          rfl
      · cases hb
  | var p =>
    simp only [namedSum] at hb
    cases hid : ns.lookup fn p with
    | none => rw [hid] at hb; cases hb
    | some id =>
      rw [hid] at hb
      cases hb
      simp only [lowSVal] at h
      split at h
      · cases h
      · rename_i j hj
        have hi : ns.active[j]? = some id := by simpa only [BodyNames.lookup, hj] using hid
        have hvar : ∀ var : Var Γ (.sum (u.sums.get ⟨sidx, hs⟩).spec),
            lowVar Γ (0 + j) (.sum (u.sums.get ⟨sidx, hs⟩).spec) = .ok var → ev = Expr.var var →
            Gabbro.Body.eval s (.name id) =
              some (valOf (.sum (u.sums.get ⟨sidx, hs⟩).spec) (eval σ₀ ev σ ρ)) := by
          intro var hv hev
          subst hev
          simp only [Gabbro.Body.eval]
          rw [hL.values j id hi, Nat.zero_add, nthVal_lowVar _ _ _ _ ρ (by simpa only [Nat.zero_add] using hv)]
          rfl
        split at h
        · split at h
          · split at h
            · cases h
            · rename_i var hv
              cases h
              exact hvar var hv rfl
          · cases h
        · split at h
          · rename_i var hv
            cases h
            exact hvar var hv rfl
          · cases h
  | slot _ _ _ => simp only [namedSum, reduceCtorEq] at hb
  | tab _ _ _ => simp only [namedSum, reduceCtorEq] at hb

/-- **A tagged binder** preserves the world and extends the positional relation. -/
theorem lowBindSum_named_sim {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {ns : BodyNames} {x : String} {sidx : Nat} {hs : sidx < u.sums.length} {v : USVal}
    {ev : Expr (declOf u) Γ Λ (.sum (u.sums.get ⟨sidx, hs⟩).spec)} {e : Gabbro.Body.Expr}
    (h : lowSVal u Γ Λ fn 0 sidx hs v = .ok ev)
    (hb : namedSum fn ns (u.sums.get ⟨sidx, hs⟩).spec v = some e)
    (hU : UmfangB Γ fn ns)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ bv : Gabbro.Body.Value,
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB (.bindName (ns.fresh x) e) s =
        .running ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩) ∧
      WGRel u (σ.lese Λ ev.orte) s.world ∧
      PositionalLRel (fn.mitSum x sidx (u.sums.get ⟨sidx, hs⟩).spec) (ns.push x).active 0
        (Env.cons (eval (σ.lese Λ ev.orte) ev (σ.lese Λ ev.orte) ρ) ρ)
        (Gabbro.Body.bindLocal s.local' (ns.fresh x) bv) := by
  have hWl := wgrel_lese u hW Λ ev.orte
  have hv := lowSVal_named_sim h hb (σ.lese Λ ev.orte) (σ.lese Λ ev.orte) ρ s hL
  refine ⟨_, fun ρB => ?_, hWl, hL.pushSum x (ns.fresh x) sidx _
    (BodyNames.fresh_not_active hU.valid x) _⟩
  simp only [Gabbro.Body.step, hv]

theorem blockZiel_bindSum_G {C : Fin u.fns.length → Prop} {c : Fin u.fns.length}
    {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {loopMode : Bool} {Γ : Ctx} {Λ Λ' : List (Res (declOf u))} {fn : UFn} {ids : List String}
    {num : Nat} {cs : List (Option Ty)}
    {e : Expr (declOf u) Γ Λ (.sum cs)} {rest : Block (declOf u) (verOf u c) loopMode ((.sum cs) :: Γ) Λ Λ'}
    {σ : World (declOf u)} {ρ : Env (declOf u) Γ} {s s₁ : Gabbro.Body.State}
    {x : Gabbro.Body.Stmt} {ys : List Gabbro.Body.Stmt} {y id : String}
    (hstep : ∀ ρB, RahmenAlleC u C ρB → Gabbro.Body.step ρB x s = .running s₁)
    (hgz : ∀ w', gz w' s.world ≤ gz w' s₁.world)
    (h : BlockZiel_G u C c O passes R (fn.mitSum y num cs) (id :: ids) rest (σ.lese Λ e.orte)
      (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) s₁ ys) :
    BlockZiel_G u C c O passes R fn ids (Block.bind e rest) σ ρ s (x :: ys) := by
  simpa only [BlockZiel_G, execBlockZ_bind, List.singleton_append] using
    ausgangZiel_schrumpf (Strecke_G.schritt hstep hgz) (fun _ _ hl => hl.tailSum) h

end Gabbro.Bruecke
