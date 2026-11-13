module
public import Bruecke.Anweisung.Lokal.Schreiben
@[expose] public section

/-!
# C4, part 2: the direct call and the trailing return in every scope

`lowCallArgOne_sim`, `lowCallArgsAux_sim`, `lowCall_sim` (`Anweisung/Teil1.lean`, `Teil2.lean`)
and `lowEnd_sim` (`Nachbedingung.lean`) for every scope `Γ`/`fn` with `UmfangB Γ fn`: an argument
or a returned value may read a local.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- A pointer name reads as `.absent` in a related binding, in every scope. -/
theorem lrel_ptrB {Γ : Ctx} {fn : UFn} {ρ : Env (declOf u) Γ} {β : Gabbro.Body.Binding}
    (hΓ : Γ = fn.params.map (·.2)) (hL : LRel fn 0 ρ β) (p : String) (j : Nat)
    (hj : paramPos fn.params p = .ok j) (cap : DataCapTy)
    (hτ : (fn.params[j]?).map (·.2) = some (.ptr cap)) : β p = .absent := by
  rw [hL p j hj, Nat.zero_add]
  exact nthVal_ptr ρ j cap (by rw [hΓ, List.getElem?_map]; exact hτ)

/-- **One call argument**, in every scope. -/
theorem lowCallArgOne_simB (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {k : UParamArt} {τ : Ty} {a : UArg}
    {e : Expr (declOf u) Γ Λ τ} {eB : Gabbro.Body.Expr}
    (h : lowCallArgOneL u c Γ fn Λ k τ a = .ok e) (hb : argExpr u fn a = some eB)
    (hK : ArtSchlicht k = true) (hU : UmfangB Γ fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    Gabbro.Body.eval s eB = some (valOf τ (eval σ₀ e σ ρ)) := by
  have hA := hU.art
  have hN := hU.namen
  cases a with
  | var p =>
    simp only [argExpr, Option.some.injEq] at hb
    subst hb
    simp only [lowCallArgOneL, bind, Except.bind] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h
         simp only [Gabbro.Body.eval]
         rw [hL p _ ‹paramPos fn.params p = .ok _›, Nat.zero_add,
           nthVal_lowVar _ _ _ _ ρ (by assumption)]
         rfl)
  | freshPtr tname w2 =>
    simp only [argExpr] at hb
    cases hq : ptrParam u fn tname with
    | none => rw [hq] at hb; cases hb
    | some p' =>
      rw [hq] at hb
      simp only [Option.map_some, Option.some.injEq] at hb
      subst hb
      have goal : Gabbro.Body.eval s (.name p') = some .absent := by
        unfold ptrParam at hq
        split at hq
        · rename_i q hfil
          simp only [Option.some.injEq] at hq
          subst hq
          have hmem := hfil ▸ List.mem_singleton_self q
          rw [List.mem_filter] at hmem
          obtain ⟨hqm, hqp⟩ := hmem
          obtain ⟨jq, hjq⟩ := List.mem_iff_getElem?.mp hqm
          have hpos := paramPos_of_nodup _ jq q.1 q.2 hN (by rw [hjq])
          have hty : ∃ cap, q.2 = .ptr cap := by
            revert hqp
            cases q.2 <;> simp
          obtain ⟨cap, htq⟩ := hty
          have hab := lrel_ptrB hU.ctx hL q.1 jq hpos cap (by rw [hjq]; simp [htq])
          simp only [Gabbro.Body.eval, hab]
        · cases hq
      simp only [lowCallArgOneL, bind, Except.bind] at h
      repeat' split at h
      all_goals first | (cases h; exact goal) | cases h
  | val sd =>
    simp only [argExpr] at hb
    cases k with
    | ptr cap =>
      cases τ with
      | ptr target =>
        obtain ⟨space, ⟨read, write, owner⟩, ⟨num⟩⟩ := target
        cases owner <;> simp only [lowCallArgOneL] at h
        all_goals repeat' split at h
        all_goals cases h
      | _ => simp only [lowCallArgOneL] at h; cases h
    | index num =>
      cases τ with
      | int lo hi =>
        simp only [lowCallArgOneL] at h
        by_cases hlt : num < u.tabs.length
        · rw [dif_pos hlt] at h
          by_cases hLo : lo = 0
          · rw [dif_pos hLo] at h
            by_cases hHi : hi = (declOf u).count ⟨num, hlt⟩ - 1
            · rw [dif_pos hHi] at h
              cases hix : uIdxOfSide sd with
              | error error => rw [hix] at h; cases h
              | ok ix =>
                rw [hix] at h
                dsimp only at h
                cases hei : lowIdx u Γ Λ fn 0 ⟨num, hlt⟩ ix with
                | error error => erw [hei] at h; cases h
                | ok ei =>
                  erw [hei] at h
                  cases h
                  rw [uIdxOfSide_expr hix hb]
                  rw [lowIdx_sim hei σ₀ σ ρ s.world s.local' hL]
                  have hτ : Ty.int lo hi = Ty.index ((declOf u).count ⟨num, hlt⟩) := by rw [hLo, hHi]
                  rw [valOf_eval_heq hτ _ ei ((mpr_heq _ _).trans (mpr_heq _ _)) σ₀ σ ρ]
                  rfl
            · rw [dif_neg hHi] at h; cases h
          · rw [dif_neg hLo] at h; cases h
        · rw [dif_neg hlt] at h; cases h
      | _ => simp only [lowCallArgOneL] at h; cases h
    | int =>
      cases τ with
      | int lo hi =>
        simp only [lowCallArgOneL] at h
        cases he' : lowWertAt u Γ Λ fn lo hi sd with
        | error error => rw [he'] at h; cases h
        | ok value =>
          rw [he'] at h
          cases h
          exact lowWertAt_sim he' hb hA hT σ₀ σ ρ s.world s.local' hW hL
      | _ => simp only [lowCallArgOneL] at h; cases h
    | _ => simp [ArtSchlicht] at hK
  | bval _ | oval _ | gval _ | fnref _ => simp [argExpr] at hb

/-- **The argument list**, in every scope. -/
theorem lowCallArgsAux_simB (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} (hU : UmfangB Γ fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    ∀ (ks : List UParamArt) (ts : List Ty) (as : List UArg)
      (a : Args (declOf u) Γ Λ ts) (es : List Gabbro.Body.Expr),
      (∀ k ∈ ks, ArtSchlicht k = true) →
      lowCallArgsAuxL u c Γ fn Λ ks ts as = .ok a → argsExpr u fn as = some es →
      Gabbro.Body.evalAll s es = some (envVals (evalArgs σ₀ a σ ρ))
  | [], ts, as, a, es, _, h, hb => by
      simp only [lowCallArgsAuxL] at h
      split at h
      · cases h
        simp only [argsExpr, Option.some.injEq] at hb
        subst hb
        rfl
      · cases h
  | k :: ks, ts, as, a, es, hKs, h, hb => by
      simp only [lowCallArgsAuxL] at h
      split at h
      · rename_i t ts' x as'
        split at h
        · cases h
        · rename_i e he
          split at h
          · cases h
          · rename_i rest hrest
            cases h
            simp only [argsExpr] at hb
            split at hb
            · rename_i eB esB hx hxs
              simp only [Option.some.injEq] at hb
              subst hb
              have h1 := lowCallArgOne_simB c he hx (hKs k (List.mem_cons_self ..))
                hU hT σ₀ σ ρ s hW hL
              have h2 := lowCallArgsAux_simB c hU hT σ₀ σ ρ s hW hL ks ts' as' rest esB
                (fun k hk => hKs k (List.mem_cons_of_mem _ hk)) hrest hxs
              simp only [Gabbro.Body.evalAll, h1, h2]
              rfl
            · cases hb
      · cases h

/-- **A direct call**, in every scope: the callee's entry state does not see the caller's scope. -/
theorem lowCall_simB (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {Λ Λ' : List (Res (declOf u))}
    {cname : String} {args : List UArg}
    {g : Stmt (declOf u) (verOf u c) false Γ Λ Λ'} {bst : Gabbro.Body.Stmt}
    (h : lowCallL (l := false) u c Γ fn Λ cname args = .ok ⟨Λ', g⟩)
    (hb : stmtBody u fn (.call cname args) = some bst)
    (hU : UmfangB Γ fn) (hT : TabEindeutig u) (hN : ∀ c', NamenEindeutig (fnAt u c'))
    (hKinds : ∀ c', ∀ k ∈ (fnAt u c').kinds, ArtSchlicht k = true)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
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
        subst hb
        let σr := σ.lese Λ a.orte
        have hWr' : WRel u σr s.world := wrel_slots u rfl hW
        have hev := lowCallArgsAux_simB c hU hT σr σr ρ s hWr' hL _ _ _ a es
          (hKinds callee) ha hes
        have hlen : (fnAt u callee).params.length = ((declOf u).params callee).length := by
          rw [params_eq]; simp
        have hLc := lrel_bindAll (fnAt u callee) (evalArgs σr a σr ρ) (hN callee) hlen
        have hpre := preExpr_wahr (fnAt u callee) (evalArgs σr a σr ρ) _ s.world (hN callee)
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

/-- **The trailing return**, in every scope: a returned value may read a local. -/
theorem lowEnd_simB (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {r : URet} {eb : Endblock (declOf u) (verOf u c) false Γ Λ} {eB : List Gabbro.Body.Stmt}
    (h : lowEnd u c Γ Λ fn r = .ok eb) (hb : endBody u fn r = some eB)
    (hU : UmfangB Γ fn) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    ∃ σ' v, execEnd O passes R eb σ ρ = .zurueck σ' v ∧ σ'.slots = σ.slots ∧
      ∀ ρB : Gabbro.Body.Env, Gabbro.Body.finalState (Gabbro.Body.exec ρB eB s) = some s ∧
        Gabbro.Body.finalValue (Gabbro.Body.exec ρB eB s) = ergValOf (verOf u c).erg v := by
  have hA := hU.art
  cases r
  case empty =>
    simp only [endBody, Option.some.injEq] at hb
    subst hb
    simp only [lowEnd] at h
    split at h
    · cases h
    · rename_i E hE
      split at h
      · cases h
        refine ⟨_, _, rfl, rfl, fun ρB => ⟨rfl, ?_⟩⟩
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
    simp only [endBody] at hb
    cases hs : sideExpr u fn sd with
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
              refine ⟨_, _, rfl, rfl, fun ρB => ?_⟩
              obtain ⟨sw, sl⟩ := s
              have herg : (verOf u c).erg = some (.int lo hi) := by
                show (vertragVon (declOf u) c).erg = _
                rw [vErg_eq u c, hErg]
              generalize hσl : σ.lese _ _ = σl
              have hWl : WRel u σl sw := by rw [← hσl]; exact wrel_slots u rfl hW
              have hv := lowWertAt_sim hve hs hA hT σl σl ρ sw sl hWl hL
              rw [ergValOf_heq herg _ (evalErg σl (ErgExpr.val (D := declOf u) ve) σl ρ)
                (evalErg_heq herg _ _ (mpr3_heq _ _ _ _) _ _ _)]
              simp only [Gabbro.Body.exec, Gabbro.Body.step, hv, Gabbro.Body.finalState,
                Gabbro.Body.finalValue]
              trivial
          · cases hE
          · cases hE
        · cases h
  all_goals simp [endBody] at hb

end Gabbro.Bruecke
