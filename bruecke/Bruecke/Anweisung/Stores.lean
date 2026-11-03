module
public import Bruecke.Ausdruck
public import Grammatik.Parser.Elab.UebersetzeAllg3
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

abbrev StmtC (u : UProg) (c : Fin u.fns.length) :=
  Stmt (declOf u) (verOf u c) false (ctxOf u c) (resOf u c) (resOf u c)

def lowAssignDurch (u : UProg) (c : Fin u.fns.length) (b fname : String) (ix : UIdx) (v : USide) :
    Except String (StmtC u c) :=
  lowAssignDurchL u c (ctxOf u c) (fnAt u c) (resOf u c) b fname ix v

def lowAssignTab (u : UProg) (c : Fin u.fns.length) (b fname : String) (ix : UIdx) (v : USide) :
    Except String (StmtC u c) :=
  lowAssignTabL u c (ctxOf u c) (fnAt u c) (resOf u c) b fname ix v

/-! ## 1. The writes: the lowering's casts are the constructors -/

theorem assignDurchStmt_eq {space : Nat} {read : Bool} (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length)
    (fh : FieldHit u t) (p : Expr (declOf u) Γ Λ (.ptr ⟨space, ⟨read, true, none⟩, .table t.val⟩))
    (ht : (declOf u).capTab space t.val = some t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2))
    (hw : V.schreibt t = true)
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    ∃ e2 : Expr (declOf u) Γ Λ ((declOf u).typ t fh.idx), HEq e2 e ∧
      assignDurchStmt (l := false) u Γ Λ V t fh p ht i e hw hL =
        Stmt.assignThru (D := declOf u) p t ht fh.idx i e2 hw hL :=
  ⟨_, mpr_heq _ _, rfl⟩

theorem assignSlotStmt_eq (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length)
    (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2))
    (hw : V.schreibt t = true)
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    ∃ e2 : Expr (declOf u) Γ Λ ((declOf u).typ t fh.idx), HEq e2 e ∧
      assignSlotStmt (l := false) u Γ Λ V t fh i e hw hL =
        Stmt.assignSlot (D := declOf u) t fh.idx i e2 hw hL :=
  ⟨_, mpr_heq _ _, rfl⟩

theorem assignDurchOwnStmt_eq {space : Nat} {read : Bool}
    (Γ : Ctx) (Λ : List (Res (declOf u))) (V : Vertrag (declOf u))
    (t : Fin u.tabs.length) (fh : FieldHit u t) (owner : Nat) (m : Fin u.marken.length)
    (p : Expr (declOf u) Γ Λ (.ptr ⟨space, ⟨read, true, some owner⟩, .table t.val⟩))
    (hc : (declOf u).capTab space t.val = some t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2))
    (hm : eignerMarke u owner = some m) (he : m ∈ eignerAt u t)
    (hw : V.schreibt t = true)
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    let guards := ownGuard_holds u Λ t owner m hm he hL
    ∃ e2 : Expr (declOf u) Γ Λ ((declOf u).typ t fh.idx), HEq e2 e ∧
      assignDurchOwnStmt (l := false) u Γ Λ V t fh owner m p hc i e hm he hw hL =
        Stmt.assignThruOwn (D := declOf u) p t hc fh.idx i e2 m 0
          guards.1 guards.2.1 guards.2.2 hw hL :=
  ⟨_, mpr_heq _ _, rfl⟩

/-- **A slot write through a pointer parameter**: the G write and the Body write take related
    states to related states, and the place's carrier is a table the function writes. -/
theorem lowAssignDurch_sim (c : Fin u.fns.length) {b fname : String} {ix : UIdx} {v : USide}
    {g : Stmt (declOf u) (verOf u c) false (ctxOf u c) (resOf u c) (resOf u c)}
    {bst : Gabbro.Body.Stmt}
    (h : lowAssignDurch u c b fname ix v = .ok g)
    (hb : stmtBody u (fnAt u c) (.assign b fname ix v) = some bst)
    (hA : ArtStimmt (fnAt u c)) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) (ctxOf u c)) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel (fnAt u c) 0 ρ s.local') :
    ∃ σ₁ cn k fld val, execStmt O passes R g σ ρ = .ok σ₁ ρ ∧
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB bst s =
        .running ⟨Gabbro.Body.store s.world (.slot cn k fld) val, s.local'⟩) ∧
      WRel u σ₁ (Gabbro.Body.store s.world (.slot cn k fld) val) ∧
      (fnAt u c).puts.any (· == cn) = true := by
  unfold lowAssignDurch lowAssignDurchL at h
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
                    | error error => simp [hcap] at h
                    | ok cap =>
                      simp only [hcap, bind, Except.bind] at h
                      cases h
                      obtain ⟨e2, he2, heq⟩ := assignDurchStmt_eq (ctxOf u c) (resOf u c) (verOf u c)
                        ⟨num, hlt⟩ fh (Expr.var pv) cap.down i e _ hG
                      rw [heq]
                      have hparam : ((fnAt u c).params[j]?).map (·.2) =
                          some (.ptr ⟨space, ⟨read, true, none⟩, .table num⟩) := by
                        simpa only [ctxOf, List.getElem?_map] using
                          (lowVar_typ (ctxOf u c) j _ pv hpv)
                      have hpt := ptrTab_of_type (fnAt u c) b j num read true hj hparam hlt
                      simp only [stmtBody, hpt] at hb
                      cases hsv : sideExpr u (fnAt u c) v with
                      | none => rw [hsv] at hb; cases hb
                      | some ve =>
                        rw [hsv] at hb
                        cases hb
                        let σl := σ.lese (resOf u c) ((Expr.var (D := declOf u) (Λ := resOf u c) pv).orte ++ i.orte ++ e2.orte)
                        have hWl : WRel u σl s.world := wrel_slots u rfl hW
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
                        · exact wrel_slots u rfl (wrel_store u hWl _ ⟨num, hlt⟩ (hT.1 _) fname fh hfh _ _)
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
                        | error error => simp [hcap] at h
                        | ok cap =>
                          simp only [hcap, bind, Except.bind] at h
                          cases h
                          obtain ⟨e2, he2, heq⟩ := assignDurchOwnStmt_eq (ctxOf u c) (resOf u c) (verOf u c)
                            ⟨num, hlt⟩ fh owner m (Expr.var pv) cap.down i e hm heig _ hG
                          rw [heq]
                          have hparam : ((fnAt u c).params[j]?).map (·.2) =
                              some (.ptr ⟨space, ⟨read, true, some owner⟩, .table num⟩) := by
                            simpa only [ctxOf, List.getElem?_map] using
                              (lowVar_typ (ctxOf u c) j _ pv hpv)
                          have hpt := ptrTab_of_type (fnAt u c) b j num read true hj hparam hlt
                          simp only [stmtBody, hpt] at hb
                          cases hsv : sideExpr u (fnAt u c) v with
                          | none => rw [hsv] at hb; cases hb
                          | some ve =>
                            rw [hsv] at hb
                            cases hb
                            let σl := σ.lese (resOf u c) ((Expr.var (D := declOf u) (Λ := resOf u c) pv).orte ++ i.orte ++ e2.orte)
                            have hWl : WRel u σl s.world := wrel_slots u rfl hW
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
                            · exact wrel_slots u rfl (wrel_store u hWl _ ⟨num, hlt⟩ (hT.1 _) fname fh hfh _ _)
                            · exact hw
                      · cases h
                    · cases h
                  · cases h
      · cases h
    · cases h

/-- **A slot write at a table.** -/
theorem lowAssignTab_sim (c : Fin u.fns.length) {b fname : String} {ix : UIdx} {v : USide}
    {g : Stmt (declOf u) (verOf u c) false (ctxOf u c) (resOf u c) (resOf u c)}
    {bst : Gabbro.Body.Stmt}
    (h : lowAssignTab u c b fname ix v = .ok g)
    (hb : stmtBody u (fnAt u c) (.assignTab b fname ix v) = some bst)
    (hA : ArtStimmt (fnAt u c)) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) (ctxOf u c)) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel (fnAt u c) 0 ρ s.local') :
    ∃ σ₁ cn k fld val, execStmt O passes R g σ ρ = .ok σ₁ ρ ∧
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB bst s =
        .running ⟨Gabbro.Body.store s.world (.slot cn k fld) val, s.local'⟩) ∧
      WRel u σ₁ (Gabbro.Body.store s.world (.slot cn k fld) val) ∧
      (fnAt u c).puts.any (· == cn) = true := by
  unfold lowAssignTab lowAssignTabL at h
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
              obtain ⟨e2, he2, heq⟩ := assignSlotStmt_eq (ctxOf u c) (resOf u c) (verOf u c)
                t fh i e _ hG
              rw [heq]
              simp only [stmtBody] at hb
              cases hsv : sideExpr u (fnAt u c) v with
              | none => rw [hsv] at hb; cases hb
              | some ve =>
                rw [hsv] at hb
                cases hb
                let σl := σ.lese (resOf u c) (i.orte ++ e2.orte)
                have hWl : WRel u σl s.world := wrel_slots u rfl hW
                have hv := lowWertAt_sim he hsv hA hT σl σl ρ s.world s.local' hWl hL
                have hk := lowIdx_sim hi σl σl ρ s.world s.local' hL
                have hx : valOf ((declOf u).typ t fh.idx) (eval σl e2 σl ρ) =
                    valOf (.int fh.range.1 fh.range.2) (eval σl e σl ρ) :=
                  valOf_eval_heq (fh.hint) e2 e he2 σl σl ρ
                refine ⟨_, b, (eval σl i σl ρ).n, fname, valOf _ (eval σl e2 σl ρ), rfl, ?_, ?_, ?_⟩
                · intro ρB
                  simp only [Gabbro.Body.step]
                  rw [hk, hv, ← hx]
                · exact wrel_slots u rfl (wrel_store u hWl b t ht fname fh hfh _ _)
                · have hn := tabIdx_name _ _ _ ht
                  have : writesAt u (fnAt u c) t = true := hw
                  unfold writesAt at this
                  rw [show (tabAt u t).name = b from hn] at this
                  exact this
            · cases h
          · cases h

end Gabbro.Bruecke
