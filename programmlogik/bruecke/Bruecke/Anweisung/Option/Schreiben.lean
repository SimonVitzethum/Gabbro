module
public import Bruecke.Anweisung.Option.Werte
@[expose] public section

/-! # Option field stores in arbitrary related scopes -/

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

theorem assignDurchStmtO_eq {loopMode : Bool} {space : Nat} {read : Bool}
    (Γ : Ctx) (Λ : List (Res (declOf u))) (V : Vertrag (declOf u))
    (t : Fin u.tabs.length) (oh : OptHit u t)
    (p : Expr (declOf u) Γ Λ (.ptr ⟨space, ⟨read, true, none⟩, .table t.val⟩))
    (ht : (declOf u).capTab space t.val = some t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ (.opt oh.n)) (hw : V.schreibt t = true)
    (hL : ∀ w ∈ (declOf u).braucht t, Res.von (declOf u) w ∈ Λ) :
    ∃ e2 : Expr (declOf u) Γ Λ ((declOf u).typ t oh.idx), HEq e2 e ∧
      assignDurchStmtO (l := loopMode) u Γ Λ V t oh p ht i e hw hL =
        Stmt.assignThru (D := declOf u) p t ht oh.idx i e2 hw hL :=
  ⟨_, mpr_heq _ _, rfl⟩

theorem assignSlotStmtO_eq {loopMode : Bool} (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length) (oh : OptHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ (.opt oh.n)) (hw : V.schreibt t = true)
    (hL : ∀ w ∈ (declOf u).braucht t, Res.von (declOf u) w ∈ Λ) :
    ∃ e2 : Expr (declOf u) Γ Λ ((declOf u).typ t oh.idx), HEq e2 e ∧
      assignSlotStmtO (l := loopMode) u Γ Λ V t oh i e hw hL =
        Stmt.assignSlot (D := declOf u) t oh.idx i e2 hw hL :=
  ⟨_, mpr_heq _ _, rfl⟩

theorem lowAssignDurchO_simB {loopMode : Bool} (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {ns : BodyNames}
    {Λ : List (Res (declOf u))} {b fname : String} {ix : UIdx} {v : UOpt}
    {g : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ} {bst : Gabbro.Body.Stmt}
    (h : lowAssignDurchOL (l := loopMode) u c Γ fn Λ b fname ix v = .ok g)
    (hb : stmtBody u fn (.assignOpt b fname ix v) = some bst)
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
  unfold lowAssignDurchOL at h
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
              · rename_i e0 he
                split at h
                · rename_i hG
                  split at h
                  · rename_i hw
                    cases hcap : checkedTableCap u space num hlt with
                    | error error =>
                      simp only [hcap] at h
                      change (Except.error error : Except String
                        (Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ)) = .ok g at h
                      cases h
                    | ok cap =>
                      simp only [hcap, bind, Except.bind] at h
                      cases h
                      obtain ⟨e2, he2, heq⟩ := assignDurchStmtO_eq (loopMode := loopMode) Γ Λ (verOf u c)
                        ⟨num, hlt⟩ fh (Expr.var pv) cap.down i (by rw [← fh.hcnt]; exact e0) _ hG
                      rw [heq]
                      have hparam : (fn.params[j]?).map (·.2) =
                          some (.ptr ⟨space, ⟨read, true, none⟩, .table num⟩) := by
                        simpa only [hU.ctx, List.getElem?_map] using (lowVar_typ Γ j _ pv hpv)
                      have hpt := ptrTab_of_type fn b j num read true hj hparam hlt
                      simp only [stmtBody, hpt] at hb
                      cases hsv : optionExpr u fn v with
                      | none => rw [hsv] at hb; cases hb
                      | some ve =>
                        rw [hsv] at hb
                        cases hb
                        let σl := σ.lese Λ ((Expr.var (D := declOf u) (Λ := Λ) pv).orte ++ i.orte ++ e2.orte)
                        have hWl : WGRel u σl s.world := wgrel_same u rfl rfl hW
                        have hv := lowOpt_sim he hsv hT σl σl ρ s hWl.1 hL
                        have hk := lowIdx_sim hi σl σl ρ s.world s.local' hL
                        have hx : valOf ((declOf u).typ ⟨num, hlt⟩ fh.idx) (eval σl e2 σl ρ) =
                            valOf (.opt ((declOf u).count ⟨fh.tnum, fh.hlt⟩)) (eval σl e0 σl ρ) :=
                          valOf_eval_heq (fh.hopt.trans (congrArg Ty.opt fh.hcnt).symm) e2 e0
                          (he2.trans (mpr_heq _ _)) σl σl ρ
                        refine ⟨_, (tabAt u ⟨num, hlt⟩).name, (eval σl i σl ρ).n, fname,
                          valOf _ (eval σl e2 σl ρ), rfl, ?_, ?_, ?_⟩
                        · intro ρB
                          simp only [Gabbro.Body.step]
                          rw [hk, hv, ← hx]
                        · exact wgrel_same u rfl rfl (wgrel_store_index u hWl _ ⟨num, hlt⟩ (hT.1 _) fname fh.idx (fieldIndex_opt hfh) _ _)
                        · exact hw
                  · cases h
                · cases h
      · cases h
    · cases h

theorem lowAssignTabO_simB {loopMode : Bool} (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {ns : BodyNames}
    {Λ : List (Res (declOf u))} {b fname : String} {ix : UIdx} {v : UOpt}
    {g : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ} {bst : Gabbro.Body.Stmt}
    (h : lowAssignTabOL (l := loopMode) u c Γ fn Λ b fname ix v = .ok g)
    (hb : stmtBody u fn (.assignTabOpt b fname ix v) = some bst)
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
  unfold lowAssignTabOL at h
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
        · rename_i e0 he
          split at h
          · rename_i hG
            split at h
            · rename_i hw
              cases h
              obtain ⟨e2, he2, heq⟩ := assignSlotStmtO_eq (loopMode := loopMode) Γ Λ (verOf u c)
                t fh i (by rw [← fh.hcnt]; exact e0) _ hG
              rw [heq]
              simp only [stmtBody] at hb
              cases hsv : optionExpr u fn v with
              | none => rw [hsv] at hb; cases hb
              | some ve =>
                rw [hsv] at hb
                cases hb
                let σl := σ.lese Λ (i.orte ++ e2.orte)
                have hWl : WGRel u σl s.world := wgrel_same u rfl rfl hW
                have hv := lowOpt_sim he hsv hT σl σl ρ s hWl.1 hL
                have hk := lowIdx_sim hi σl σl ρ s.world s.local' hL
                have hx : valOf ((declOf u).typ t fh.idx) (eval σl e2 σl ρ) =
                    valOf (.opt ((declOf u).count ⟨fh.tnum, fh.hlt⟩)) (eval σl e0 σl ρ) :=
                  valOf_eval_heq (fh.hopt.trans (congrArg Ty.opt fh.hcnt).symm) e2 e0
                          (he2.trans (mpr_heq _ _)) σl σl ρ
                refine ⟨_, b, (eval σl i σl ρ).n, fname, valOf _ (eval σl e2 σl ρ), rfl, ?_, ?_, ?_⟩
                · intro ρB
                  simp only [Gabbro.Body.step]
                  rw [hk, hv, ← hx]
                · exact wgrel_same u rfl rfl (wgrel_store_index u hWl b t ht fname fh.idx (fieldIndex_opt hfh) _ _)
                · have hn := tabIdx_name _ _ _ ht
                  have : writesAt u (fnAt u c) t = true := hw
                  unfold writesAt at this
                  rw [show (tabAt u t).name = b from hn] at this
                  exact this
            · cases h
          · cases h

end Gabbro.Bruecke
