module
public import Bruecke.Anweisung.Ruf.Kopf
public import Bruecke.Teil.Lokal.Ruf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {c : Fin u.fns.length}

theorem resultCall_type {Γ : Ctx} {Λ : List (Res (declOf u))} {fn ft : UFn}
    {ns : BodyNames} {x g : String} {args : List UArg} {k : RufKopf u c Γ Λ}
    {ty bt : Ty} {b : Gabbro.Body.Stmt}
    (hk : lowRufKopf u c Γ fn Λ g args = .ok k)
    (he : (declOf u).erg k.callee = some ty)
    (hb : namedResult u ft ns x g args = some (b, bt)) :
    bt = ty ∧ ∃ sh, shapeOfTy ty = some sh := by
  obtain ⟨hi, _, _⟩ := lowRufKopf_ok hk
  have hf : fnSuch u g = some (fnAt u k.callee) := fnIdx_find _ _ _ hi
  obtain ⟨gf, _, _, sh, hgf, ht, hsh, _⟩ := namedResult_some hb
  rw [hf] at hgf
  cases hgf
  have ht' : some ty = some bt := (he.symm.trans (erg_eq u k.callee)).trans ht
  have hty := (Option.some.inj ht').symm
  exact ⟨hty, sh, hty ▸ hsh⟩

theorem ergValOf_wert {D : Deklaration} {ty : Ty} {e : Option Ty}
    (he : e = some ty) (v : ErgVal D e) :
    ergValOf e v = some (valOf ty (ergWert he v)) := by
  subst e
  rfl

/-- Argument evaluation and the result scope agree with the actual canonical call head. -/
theorem resultCall_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {ns : BodyNames}
    {x g : String} {args : List UArg} {k : RufKopf u c Γ Λ} {ty bt : Ty}
    {b : Gabbro.Body.Stmt} (hk : lowRufKopf u c Γ fn Λ g args = .ok k)
    (he : (declOf u).erg k.callee = some ty)
    (hb : namedResult u fn ns x g args = some (b, bt))
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (hN : NamenEindeutig (fnAt u k.callee))
    (hA : ∀ a ∈ (fnAt u k.callee).kinds, ArtSchlicht a = true)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    bt = ty ∧ ∃ es sh, shapeOfTy ty = some sh ∧ fnSuch u g = some (fnAt u k.callee) ∧
      b = .bindCall (ns.fresh x) g ((fnAt u k.callee).params.map (·.1)) es
        (preExpr (fnAt u k.callee)) ∧
      Gabbro.Body.evalAll s es = some (envVals (evalArgs (σ.lese Λ k.args.orte) k.args
        (σ.lese Λ k.args.orte) ρ)) ∧
      LRel (fnAt u k.callee) 0 (evalArgs (σ.lese Λ k.args.orte) k.args
        (σ.lese Λ k.args.orte) ρ)
        (Gabbro.Body.bindAll ((fnAt u k.callee).params.map (·.1))
          (envVals (evalArgs (σ.lese Λ k.args.orte) k.args (σ.lese Λ k.args.orte) ρ))
          (fun _ => .absent)) ∧
      Gabbro.Body.eval ⟨s.world, Gabbro.Body.bindAll ((fnAt u k.callee).params.map (·.1))
          (envVals (evalArgs (σ.lese Λ k.args.orte) k.args (σ.lese Λ k.args.orte) ρ))
          (fun _ => .absent)⟩ (preExpr (fnAt u k.callee)) = some (.bool true) := by
  obtain ⟨hidx, ha, _⟩ := lowRufKopf_ok hk
  have hfs : fnSuch u g = some (fnAt u k.callee) := fnIdx_find _ _ _ hidx
  obtain ⟨gf, raw, es, sh, hgf, hty, hsh, hraw, hn, rfl⟩ := namedResult_some hb
  rw [hfs] at hgf
  cases hgf
  have hty' : some ty = some bt := (he.symm.trans (erg_eq u k.callee)).trans hty
  have hbt : bt = ty := (Option.some.inj hty').symm
  subst bt
  have hWr : WGRel u (σ.lese Λ k.args.orte) s.world := wgrel_same u rfl rfl hW
  have hv := lowCallArgsAux_simB c hU hT (σ.lese Λ k.args.orte) (σ.lese Λ k.args.orte)
    ρ ⟨s.world, ns.visible fn s.local'⟩ hWr (hL.visible (ns := ns)) _ _ _ k.args raw hA ha hraw
  change Gabbro.Body.evalAll ⟨s.world, visibleBinding (ns.lookup fn) s.local'⟩ raw = _ at hv
  have hv' := (evalAll_renameScalars (ns.lookup fn) s raw es hn).trans hv
  have hlen : (fnAt u k.callee).params.length = ((declOf u).params k.callee).length := by
    rw [params_eq, List.length_map]
  have hLc := lrel_bindAll (fnAt u k.callee)
    (evalArgs (σ.lese Λ k.args.orte) k.args (σ.lese Λ k.args.orte) ρ) hN hlen
  exact ⟨rfl, es, sh, hsh, hfs, rfl, hv', hLc,
    preExpr_wahr (fnAt u k.callee) _ _ s.world hN (params_eq u k.callee) hLc⟩

/-- A result call either gets stuck or changes the world through its declared callee. -/
theorem step_bindCall (ρB : Gabbro.Body.Env) (x g : String) (ps : List String)
    (es : List Gabbro.Body.Expr) (pre : Gabbro.Body.Expr) (s : Gabbro.Body.State) :
    Gabbro.Body.step ρB (.bindCall x g ps es pre) s = .stuck ∨
      ∃ t : Gabbro.Body.State, ∃ v, t.world = s.world ∧
        Gabbro.Body.step ρB (.bindCall x g ps es pre) s =
          .running ⟨(ρB g t).1.world, Gabbro.Body.bindLocal s.local' x v⟩ := by
  simp only [Gabbro.Body.step]
  split
  · rename_i vs _
    split
    · split
      · rename_i v _
        exact .inr ⟨⟨s.world, Gabbro.Body.bindAll ps vs (fun _ => .absent)⟩, v, rfl, rfl⟩
      · exact .inl rfl
    · exact .inl rfl
  · exact .inl rfl

end Gabbro.Bruecke
