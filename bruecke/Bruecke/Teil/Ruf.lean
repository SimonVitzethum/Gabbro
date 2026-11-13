module
public import Bruecke.Teil.Abschluss
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- The call simulation needs shape facts only for the caller and this resolved target. -/
theorem lowCall_sim_teil (c : Fin u.fns.length) {Λ Λ' : List (Res (declOf u))}
    {cname : String} {args : List UArg}
    {g : Stmt (declOf u) (verOf u c) false (ctxOf u c) Λ Λ'}
    {bst : Gabbro.Body.Stmt}
    (h : lowCall u c cname args (Λ := Λ) = .ok ⟨Λ', g⟩)
    (hb : stmtBody u (fnAt u c) (.call cname args) = some bst)
    (hA : ArtStimmt (fnAt u c)) (hT : TabEindeutig u) (hN : NamenEindeutig (fnAt u c))
    (hTarget : ∀ d, fnSuch u cname = some (fnAt u d) →
      NamenEindeutig (fnAt u d) ∧ ∀ k ∈ (fnAt u d).kinds, ArtSchlicht k = true)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) (ctxOf u c)) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel (fnAt u c) 0 ρ s.local') :
    ∃ (callee : Fin u.fns.length) (σr : World (declOf u))
      (envA : Env (declOf u) ((declOf u).params callee)),
      cname = (fnAt u callee).name ∧ fnSuch u cname = some (fnAt u callee) ∧ σr.slots = σ.slots ∧
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
  unfold lowCall lowCallL at h
  split at h
  · cases h
  · rename_i k hk
    obtain ⟨hcallee, ha, hWr⟩ := lowRufKopf_ok hk
    obtain ⟨callee, a, hp⟩ := k
    split at h
    · rename_i hr
      cases h
      -- the Body side
      have hfs : fnSuch u cname = some (fnAt u callee) := fnIdx_find _ _ _ hcallee
      simp only [stmtBody, hfs] at hb
      cases hes : argsExpr u (fnAt u c) args with
      | none => rw [hes] at hb; cases hb
      | some es =>
        rw [hes] at hb
        simp only [Option.some.injEq] at hb
        subst hb
        let σr := σ.lese Λ a.orte
        have hWr' : WRel u σr s.world := wrel_slots u rfl hW
        have hev := lowCallArgsAux_sim c hA hT hN σr σr ρ s hWr' hL _ _ _ a es
          (hTarget callee hfs).2 ha hes
        have hlen : (fnAt u callee).params.length = ((declOf u).params callee).length := by
          rw [params_eq]; simp
        have hLc := lrel_bindAll (fnAt u callee) (evalArgs σr a σr ρ) (hTarget callee hfs).1 hlen
        have hpre := preExpr_wahr (fnAt u callee) (evalArgs σr a σr ρ) _ s.world (hTarget callee hfs).1
          (params_eq u callee) hLc
        refine ⟨callee, σr, evalArgs σr a σr ρ, (fnIdx_name _ _ _ hcallee).symm, hfs, rfl,
          fun ρB => ?_, hLc, hpre, ?_, hWr⟩
        · simp only [Gabbro.Body.step, hev, hpre]
        · simp only [execStmt]
          cases hR : R callee σr (evalArgs σr a σr ρ) with
          | ok σ' v => exact .inl ⟨σ', v, rfl, rfl⟩
          | why σ' r => exact absurd r.isLt (by simp only at hr; omega)
          | logik e => exact .inr (.inl ⟨e, rfl, rfl⟩)
          | hardware e => exact .inr (.inr ⟨e, rfl, rfl⟩)
    · cases h

end Gabbro.Bruecke
