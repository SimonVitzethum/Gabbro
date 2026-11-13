module
public import Bruecke.Teil.Pflichten
public import Bruecke.Anweisung.Lokal.Ruf
public import Bruecke.Anweisung.Lokal.Position
public import Bruecke.Anweisung.Lokal.Benannt
public import Bruecke.Anweisung.Lokal.UmbenennungSchritt
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- A call in a binding scope uses shape duties only for its resolved target. -/
theorem lowCall_sim_teilB (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {ns : BodyNames} {Λ Λ' : List (Res (declOf u))}
    {cname : String} {args : List UArg}
    {g : Stmt (declOf u) (verOf u c) false Γ Λ Λ'} {bst : Gabbro.Body.Stmt}
    (h : lowCallL (l := false) u c Γ fn Λ cname args = .ok ⟨Λ', g⟩)
    (hb : namedStmt u fn ns (.call cname args) = some bst)
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (hTarget : ∀ d, fnSuch u cname = some (fnAt u d) →
      NamenEindeutig (fnAt u d) ∧ ∀ k ∈ (fnAt u d).kinds, ArtSchlicht k = true)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ (callee : Fin u.fns.length) (σr : World (declOf u))
      (envA : Env (declOf u) ((declOf u).params callee)),
      cname = (fnAt u callee).name ∧ fnSuch u cname = some (fnAt u callee) ∧ WGRel u σr s.world ∧
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB bst s = .running ⟨(ρB cname
          ⟨s.world, Gabbro.Body.bindAll ((fnAt u callee).params.map (·.1)) (envVals envA)
            (fun _ => .absent)⟩).1.world, s.local'⟩) ∧
      LRel (fnAt u callee) 0 envA
        (Gabbro.Body.bindAll ((fnAt u callee).params.map (·.1)) (envVals envA) (fun _ => .absent)) ∧
      Gabbro.Body.eval ⟨s.world, Gabbro.Body.bindAll ((fnAt u callee).params.map (·.1))
        (envVals envA) (fun _ => .absent)⟩ (preExpr (fnAt u callee)) = some (.bool true) ∧
      ((∃ σ' v, R callee σr envA = .ok σ' v ∧ execStmt O passes R g σ ρ = .ok σ' ρ) ∨
        (∃ e, R callee σr envA = .logik e ∧ execStmt O passes R g σ ρ = .logik e) ∨
        (∃ e, R callee σr envA = .hardware e ∧ execStmt O passes R g σ ρ = .hardware e)) ∧
      (∀ t, writesAt u (fnAt u callee) t = true → writesAt u (fnAt u c) t = true) := by
  obtain ⟨raw, hb, hrename⟩ := namedStmt_some hb
  unfold lowCallL at h
  split at h
  · cases h
  · rename_i k hk
    obtain ⟨hcallee, ha, hWr⟩ := lowRufKopf_ok hk
    obtain ⟨callee, a, hp⟩ := k
    split at h
    · rename_i hr
      cases h
      have hfs : fnSuch u cname = some (fnAt u callee) := fnIdx_find _ _ _ hcallee
      simp only [stmtBody, hfs] at hb
      cases hes : argsExpr u fn args with
      | none => rw [hes] at hb; cases hb
      | some es =>
        rw [hes] at hb
        simp only [Option.some.injEq] at hb
        subst raw
        simp only [renameStep] at hrename
        cases hrenameArgs : renameStep.renameScalars (ns.lookup fn) es with
        | none => rw [hrenameArgs] at hrename; cases hrename
        | some es' =>
          rw [hrenameArgs] at hrename
          simp only [Option.map_some, Option.some.injEq] at hrename
          subst bst
          let σr := σ.lese Λ a.orte
          have hWr' : WGRel u σr s.world := wgrel_same u rfl rfl hW
          have hev := lowCallArgsAux_simB c hU hT σr σr ρ ⟨s.world, ns.visible fn s.local'⟩ hWr' (hL.visible (ns := ns)) _ _ _ a es
            (hTarget callee hfs).2 ha hes
          change Gabbro.Body.evalAll ⟨s.world, visibleBinding (ns.lookup fn) s.local'⟩ es =
            some (envVals (evalArgs σr a σr ρ)) at hev
          have hev' : Gabbro.Body.evalAll s es' = some (envVals (evalArgs σr a σr ρ)) :=
            (evalAll_renameScalars (ns.lookup fn) s es es' hrenameArgs).trans hev
          have hlen : (fnAt u callee).params.length = ((declOf u).params callee).length := by
            rw [params_eq, List.length_map]
          have hLc := lrel_bindAll (fnAt u callee) (evalArgs σr a σr ρ) (hTarget callee hfs).1 hlen
          have hpre := preExpr_wahr (fnAt u callee) (evalArgs σr a σr ρ) _ s.world (hTarget callee hfs).1
            (params_eq u callee) hLc
          refine ⟨callee, σr, evalArgs σr a σr ρ, (fnIdx_name _ _ _ hcallee).symm, hfs, hWr',
            fun ρB => ?_, hLc, hpre, ?_, hWr⟩
          · simp only [Gabbro.Body.step, hev', hpre]
          · simp only [execStmt]
            cases hR : R callee σr (evalArgs σr a σr ρ) with
            | ok σ' v => exact .inl ⟨σ', v, rfl, rfl⟩
            | why σ' r => exact (Nat.not_lt_zero r.val (Nat.lt_of_lt_of_eq r.isLt hr)).elim
            | logik e => exact .inr (.inl ⟨e, rfl, rfl⟩)
            | hardware e => exact .inr (.inr ⟨e, rfl, rfl⟩)
    · cases h

end Gabbro.Bruecke
