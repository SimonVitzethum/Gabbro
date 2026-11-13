module
public import Bruecke.Anweisung.Lokal.Umfang
public import Bruecke.Anweisung.Teil2
@[expose] public section

/-!
# C4, part 1: the slot writes in every scope

`lowAssignDurch_sim` and `lowAssignTab_sim` (`Anweisung/Stores.lean`) are stated in the scope of
the parameters (`ctxOf u c`, `fnAt u c`). Behind a `let` the scope is longer: these are the same
two simulations for every scope `Γ`/`fn` with `UmfangB Γ fn ns`, and the statement readers
(`lowStmtL`) in every scope.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

theorem lowStmtL_assign (hT : TabEindeutig u) (c : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (b f : String) (ix : UIdx) (v : USide) :
    lowStmtL (l := false) u c Γ fn Λ (.assign b f ix v) =
      (lowAssignDurchL (l := false) u c Γ fn Λ b f ix v).map (fun st => ⟨Λ, st⟩) := by
  have hn : lowAssignDurchW (l := false) u c Γ fn Λ b f ix v = none := by
    unfold lowAssignDurchW
    split
    · rfl
    · split
      · rename_i num _
        split
        · rename_i hlt
          rw [fieldHitW_none (hT.2 ⟨num, hlt⟩)]
          rfl
        · rfl
      · rfl
  simp only [lowStmtL, hn, Option.getD_none]
  try rfl

theorem lowStmtL_assignTab (hT : TabEindeutig u) (c : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (b f : String) (ix : UIdx) (v : USide) :
    lowStmtL (l := false) u c Γ fn Λ (.assignTab b f ix v) =
      (lowAssignTabL (l := false) u c Γ fn Λ b f ix v).map (fun st => ⟨Λ, st⟩) := by
  have hn : lowAssignTabW (l := false) u c Γ fn Λ b f ix v = none := by
    unfold lowAssignTabW
    split
    · rfl
    · rename_i t _
      rw [fieldHitW_none (hT.2 t)]
      rfl
  simp only [lowStmtL, hn, Option.getD_none]
  try rfl

/-- **A slot write through a pointer**, in every scope. -/
theorem lowAssignDurch_simB (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {ns : BodyNames}
    {Λ : List (Res (declOf u))} {b fname : String} {ix : UIdx} {v : USide}
    {g : Stmt (declOf u) (verOf u c) false Γ Λ Λ} {bst : Gabbro.Body.Stmt}
    (h : lowAssignDurchL (l := false) u c Γ fn Λ b fname ix v = .ok g)
    (hb : stmtBody u fn (.assign b fname ix v) = some bst)
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    ∃ σ₁ cn k fld val, execStmt O passes R g σ ρ = .ok σ₁ ρ ∧
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB bst s =
        .running ⟨Gabbro.Body.store s.world (.slot cn k fld) val, s.local'⟩) ∧
      WGRel u σ₁ (Gabbro.Body.store s.world (.slot cn k fld) val) ∧
      (fnAt u c).puts.any (· == cn) = true := by
  have hA := hU.art
  unfold lowAssignDurchL at h
  split at h
  · cases h
  · rename_i j hj
    split at h
    · rename_i space read num hp
      split at h
      · rename_i hlt
        split at h
        · cases h
        · rename_i fh hfh
          split at h
          · cases h
          · rename_i pv hpv
            split at h
            · cases h
            · rename_i i hi
              split at h
              · cases h
              · rename_i e he
                split at h
                · rename_i hG
                  split at h
                  · rename_i hw
                    cases hcap : checkedTableCap u space num hlt with
                    | error error =>
                      simp only [hcap] at h
                      change (Except.error error : Except String
                        (Stmt (declOf u) (verOf u c) false Γ Λ Λ)) = .ok g at h
                      cases h
                    | ok cap =>
                      simp only [hcap, bind, Except.bind] at h
                      cases h
                      obtain ⟨e2, he2, heq⟩ := assignDurchStmt_eq Γ Λ (verOf u c)
                        ⟨num, hlt⟩ fh (Expr.var pv) cap.down i e _ hG
                      rw [heq]
                      have hparam : (fn.params[j]?).map (·.2) =
                          some (.ptr ⟨space, ⟨read, true, none⟩, .table num⟩) := by
                        simpa only [hU.ctx, List.getElem?_map] using (lowVar_typ Γ j _ pv hpv)
                      have hpt := ptrTab_of_type fn b j num read true hj hparam hlt
                      simp only [stmtBody, hpt] at hb
                      cases hsv : sideExprG u fn v with
                      | none => rw [hsv] at hb; cases hb
                      | some ve =>
                        rw [hsv] at hb
                        cases hb
                        let σl := σ.lese Λ ((Expr.var (D := declOf u) (Λ := Λ) pv).orte ++ i.orte ++ e2.orte)
                        have hWl : WGRel u σl s.world := wgrel_same u rfl rfl hW
                        have hv := lowWertAt_sim he hsv hA hT σl σl ρ s.world s.local' hWl hL
                        have hk := lowIdx_sim hi σl σl ρ s.world s.local' hL
                        have hx : valOf ((declOf u).typ ⟨num, hlt⟩ fh.idx) (eval σl e2 σl ρ) =
                            valOf (.int fh.range.1 fh.range.2) (eval σl e σl ρ) :=
                          valOf_eval_heq (fh.hint) e2 e he2 σl σl ρ
                        refine ⟨_, (tabAt u ⟨num, hlt⟩).name, (eval σl i σl ρ).n, fname,
                          valOf _ (eval σl e2 σl ρ), rfl, ?_, ?_, ?_⟩
                        · intro ρB
                          simp only [Gabbro.Body.step]
                          rw [hk, hv, ← hx]
                        · exact wgrel_same u rfl rfl (wgrel_store u hWl _ ⟨num, hlt⟩ (hT.1 _) fname fh hfh _ _)
                        · exact hw
                  · cases h
                · cases h
      · cases h
    · rename_i space read owner num hp
      split at h
      · rename_i hlt
        split at h
        · cases h
        · rename_i fh hfh
          split at h
          · cases h
          · rename_i m hm
            split at h
            · cases h
            · rename_i pv hpv
              split at h
              · cases h
              · rename_i i hi
                split at h
                · cases h
                · rename_i e he
                  split at h
                  · rename_i hG
                    split at h
                    · rename_i heig
                      split at h
                      · rename_i hw
                        cases hcap : checkedTableCap u space num hlt with
                        | error error =>
                          simp only [hcap] at h
                          change (Except.error error : Except String
                            (Stmt (declOf u) (verOf u c) false Γ Λ Λ)) = .ok g at h
                          cases h
                        | ok cap =>
                          simp only [hcap, bind, Except.bind] at h
                          cases h
                          obtain ⟨e2, he2, heq⟩ := assignDurchOwnStmt_eq Γ Λ (verOf u c)
                            ⟨num, hlt⟩ fh owner m (Expr.var pv) cap.down i e hm heig _ hG
                          rw [heq]
                          have hparam : (fn.params[j]?).map (·.2) =
                              some (.ptr ⟨space, ⟨read, true, some owner⟩, .table num⟩) := by
                            simpa only [hU.ctx, List.getElem?_map] using (lowVar_typ Γ j _ pv hpv)
                          have hpt := ptrTab_of_type fn b j num read true hj hparam hlt
                          simp only [stmtBody, hpt] at hb
                          cases hsv : sideExprG u fn v with
                          | none => rw [hsv] at hb; cases hb
                          | some ve =>
                            rw [hsv] at hb
                            cases hb
                            let σl := σ.lese Λ ((Expr.var (D := declOf u) (Λ := Λ) pv).orte ++ i.orte ++ e2.orte)
                            have hWl : WGRel u σl s.world := wgrel_same u rfl rfl hW
                            have hv := lowWertAt_sim he hsv hA hT σl σl ρ s.world s.local' hWl hL
                            have hk := lowIdx_sim hi σl σl ρ s.world s.local' hL
                            have hx : valOf ((declOf u).typ ⟨num, hlt⟩ fh.idx) (eval σl e2 σl ρ) =
                                valOf (.int fh.range.1 fh.range.2) (eval σl e σl ρ) :=
                              valOf_eval_heq (fh.hint) e2 e he2 σl σl ρ
                            refine ⟨_, (tabAt u ⟨num, hlt⟩).name, (eval σl i σl ρ).n, fname,
                              valOf _ (eval σl e2 σl ρ), rfl, ?_, ?_, ?_⟩
                            · intro ρB
                              simp only [Gabbro.Body.step]
                              rw [hk, hv, ← hx]
                            · exact wgrel_same u rfl rfl (wgrel_store u hWl _ ⟨num, hlt⟩ (hT.1 _) fname fh hfh _ _)
                            · exact hw
                      · cases h
                    · cases h
                  · cases h
      · cases h
    · cases h

/-- **A slot write at a table**, in every scope. -/
theorem lowAssignTab_simB (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {ns : BodyNames}
    {Λ : List (Res (declOf u))} {b fname : String} {ix : UIdx} {v : USide}
    {g : Stmt (declOf u) (verOf u c) false Γ Λ Λ} {bst : Gabbro.Body.Stmt}
    (h : lowAssignTabL (l := false) u c Γ fn Λ b fname ix v = .ok g)
    (hb : stmtBody u fn (.assignTab b fname ix v) = some bst)
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    ∃ σ₁ cn k fld val, execStmt O passes R g σ ρ = .ok σ₁ ρ ∧
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB bst s =
        .running ⟨Gabbro.Body.store s.world (.slot cn k fld) val, s.local'⟩) ∧
      WGRel u σ₁ (Gabbro.Body.store s.world (.slot cn k fld) val) ∧
      (fnAt u c).puts.any (· == cn) = true := by
  have hA := hU.art
  unfold lowAssignTabL at h
  split at h
  · cases h
  · rename_i t ht
    split at h
    · cases h
    · rename_i fh hfh
      split at h
      · cases h
      · rename_i i hi
        split at h
        · cases h
        · rename_i e he
          split at h
          · rename_i hG
            split at h
            · rename_i hw
              cases h
              obtain ⟨e2, he2, heq⟩ := assignSlotStmt_eq Γ Λ (verOf u c)
                t fh i e _ hG
              rw [heq]
              simp only [stmtBody] at hb
              cases hsv : sideExprG u fn v with
              | none => rw [hsv] at hb; cases hb
              | some ve =>
                rw [hsv] at hb
                cases hb
                let σl := σ.lese Λ (i.orte ++ e2.orte)
                have hWl : WGRel u σl s.world := wgrel_same u rfl rfl hW
                have hv := lowWertAt_sim he hsv hA hT σl σl ρ s.world s.local' hWl hL
                have hk := lowIdx_sim hi σl σl ρ s.world s.local' hL
                have hx : valOf ((declOf u).typ t fh.idx) (eval σl e2 σl ρ) =
                    valOf (.int fh.range.1 fh.range.2) (eval σl e σl ρ) :=
                  valOf_eval_heq (fh.hint) e2 e he2 σl σl ρ
                refine ⟨_, b, (eval σl i σl ρ).n, fname, valOf _ (eval σl e2 σl ρ), rfl, ?_, ?_, ?_⟩
                · intro ρB
                  simp only [Gabbro.Body.step]
                  rw [hk, hv, ← hx]
                · exact wgrel_same u rfl rfl (wgrel_store u hWl b t ht fname fh hfh _ _)
                · have hn := tabIdx_name _ _ _ ht
                  have : writesAt u (fnAt u c) t = true := hw
                  unfold writesAt at this
                  rw [show (tabAt u t).name = b from hn] at this
                  exact this
            · cases h
          · cases h

end Gabbro.Bruecke
