module
public import Bruecke.Teil.Ruf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem stmt_statisch_teil (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (st : UStmt)
    (hmem : st ∈ (fnAt u c).body)
    {Λ Λ' : List (Res (declOf u))}
    {g : Stmt (declOf u) (verOf u c) false (ctxOf u c) Λ Λ'}
    (h : lowStmt u c st (Λ := Λ) = .ok ⟨Λ', g⟩) {bst : Gabbro.Body.Stmt}
    (hb : stmtBody u (fnAt u c) st = some bst) :
    (∃ cn idx fld ve, bst = .assign cn idx fld ve ∧ cn ∈ (fnAt u c).puts) ∨
    (∃ cname ps es pre gf, bst = .call cname ps es pre ∧ fnSuch u cname = some gf ∧
      ∀ w ∈ gf.puts, w ∈ (fnAt u c).puts) := by
  cases st
  case assign b fname ix v =>
    rw [lowStmt_assign S.tab c b fname ix v (Λ := Λ)] at h
    have pointerWrite {space num j : Nat} {read : Bool} {owner : Option Nat}
        (pv : Var (ctxOf u c) (.ptr ⟨space, ⟨read, true, owner⟩, .table num⟩))
        (hj : paramPos (fnAt u c).params b = .ok j)
        (hpv : lowVar (ctxOf u c) j
          (.ptr ⟨space, ⟨read, true, owner⟩, .table num⟩) = .ok pv)
        (hlt : num < u.tabs.length) (hw : writesAt u (fnAt u c) ⟨num, hlt⟩ = true) :
        ∃ cn idx fld ve, bst = .assign cn idx fld ve ∧ cn ∈ (fnAt u c).puts := by
      have hparam : ((fnAt u c).params[j]?).map (·.2) =
          some (.ptr ⟨space, ⟨read, true, owner⟩, .table num⟩) := by
        simpa only [ctxOf, List.getElem?_map] using
          (lowVar_typ (ctxOf u c) j _ pv hpv)
      have hpt := ptrTab_of_type (fnAt u c) b j num read true hj hparam hlt
      simp only [stmtBody, hpt] at hb
      cases hsv : sideExpr u (fnAt u c) v with
      | none => rw [hsv] at hb; cases hb
      | some ve =>
        rw [hsv] at hb
        cases hb
        exact ⟨_, _, _, _, rfl, any_mem hw⟩
    cases stored : lowAssignDurch u c b fname ix v (Λ := Λ) with
    | error error => simp only [stored, Except.map] at h; cases h
    | ok statement =>
      simp only [stored, Except.map] at h
      cases h
      have h := stored
      unfold lowAssignDurch lowAssignDurchL at h
      split at h
      · cases h
      · rename_i j hj
        split at h
        · rename_i space read num _
          split at h
          · rename_i hlt
            split at h
            · cases h
            · rename_i fh _
              split at h
              · cases h
              · rename_i pv hpv
                split at h
                · cases h
                · split at h
                  · cases h
                  · split at h
                    · split at h
                      · rename_i hw
                        exact .inl (pointerWrite pv hj hpv hlt hw)
                      · cases h
                    · cases h
          · cases h
        · rename_i space read owner num _
          split at h
          · rename_i hlt
            split at h
            · cases h
            · rename_i fh _
              split at h
              · cases h
              · rename_i m _
                split at h
                · cases h
                · rename_i pv hpv
                  split at h
                  · cases h
                  · split at h
                    · cases h
                    · split at h
                      · split at h
                        · split at h
                          · rename_i hw
                            exact .inl (pointerWrite pv hj hpv hlt hw)
                          · cases h
                        · cases h
                      · cases h
          · cases h
        · cases h
  case assignTab b fname ix v =>
    rw [lowStmt_assignTab S.tab c b fname ix v (Λ := Λ)] at h
    cases stored : lowAssignTab u c b fname ix v (Λ := Λ) with
    | error error => simp only [stored, Except.map] at h; cases h
    | ok statement =>
      simp only [stored, Except.map] at h
      cases h
      have h := stored
      simp only [lowAssignTab, lowAssignTabL] at h
      split at h
      · cases h
      · rename_i t ht
        repeat' split at h
        all_goals try cases h
        rename_i hw
        left
        simp only [stmtBody] at hb
        cases hsv : sideExpr u (fnAt u c) v with
        | none => rw [hsv] at hb; cases hb
        | some ve =>
          rw [hsv] at hb
          cases hb
          have hn := tabIdx_name _ _ _ ht
          have hw' : writesAt u (fnAt u c) t = true := hw
          unfold writesAt at hw'
          rw [show (tabAt u t).name = b from hn] at hw'
          exact ⟨_, _, _, _, rfl, any_mem hw'⟩
  case call cname args =>
    rw [lowStmt_call (u := u) c cname args (Λ := Λ)] at h
    unfold lowCall lowCallL at h
    split at h
    · cases h
    · rename_i k hk
      obtain ⟨hcallee, _, hWr⟩ := lowRufKopf_ok hk
      right
      have hfs : fnSuch u cname = some (fnAt u k.callee) := fnIdx_find _ _ _ hcallee
      simp only [stmtBody, hfs] at hb
      cases hes : argsExpr u (fnAt u c) args with
      | none => rw [hes] at hb; cases hb
      | some es =>
        rw [hes] at hb
        cases hb
        refine ⟨_, _, _, _, _, rfl, hfs, fun w hw => ?_⟩
        obtain ⟨t, rfl⟩ := S.schreibt k.callee (callee_getragen_teil S hc hmem hfs) w hw
        have h1 : writesAt u (fnAt u k.callee) t = true := by
          unfold writesAt; exact List.any_eq_true.mpr ⟨_, hw, by simp⟩
        have h2 := hWr t h1
        unfold writesAt at h2
        exact any_mem h2
  all_goals simp [stmtBody] at hb

theorem exec_rahmen_teil (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (ρ : Gabbro.Body.Env)
    (eB : List Gabbro.Body.Stmt) (heB : ∀ x ∈ eB, ∃ e, x = .ret (some e)) :
    ∀ (ss : List UStmt) (bs : List Gabbro.Body.Stmt),
      (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      (∀ st ∈ ss, ∃ (Λ : List (Res (declOf u)))
        (g : Σ Λ', Stmt (declOf u) (verOf u c) false (ctxOf u c) Λ Λ'),
        lowStmt u c st (Λ := Λ) = .ok g) → stmtsBody u (fnAt u c) ss = some bs →
      (∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ ss) →
        Gabbro.Body.Frame ρ cname gf.puts) →
      ∀ t s', Gabbro.Body.finalState (Gabbro.Body.exec ρ (bs ++ eB) t) = some s' →
        ∀ p, p.carrier ∉ (fnAt u c).puts → s'.world p = t.world p
  | [], bs, _, _, hbs, _, t, s', h, p, _ => by
      simp only [stmtsBody, Option.some.injEq] at hbs
      subst hbs
      rw [exec_rets ρ eB heB t s' h]
  | st :: ss, bs, hmem, hlow, hbs, hF, t, s', h, p, hp => by
      simp only [stmtsBody] at hbs
      split at hbs
      · rename_i x xs hx hxs
        simp only [Option.some.injEq] at hbs
        subst hbs
        obtain ⟨Λ, ⟨Λ', g⟩, hg⟩ := hlow st (List.mem_cons_self ..)
        have IH := exec_rahmen_teil S c hc ρ eB heB ss xs
          (fun st' hm => hmem st' (List.mem_cons_of_mem _ hm)) (fun st' hm => hlow st' (List.mem_cons_of_mem _ hm))
          hxs (fun cn gf hgf ⟨args, hm⟩ => hF cn gf hgf ⟨args, List.mem_cons_of_mem _ hm⟩)
        rcases stmt_statisch_teil S c hc st (hmem st (List.mem_cons_self ..)) hg hx with ⟨cn, idx, fld, ve, rfl, hcn⟩ |
            ⟨cname, ps, es, pre, gf, rfl, hgf, hsub⟩
        · rcases step_assign ρ cn idx fld ve t with hs | ⟨k, v, hs⟩
          · simp [List.cons_append, Gabbro.Body.exec, hs, Gabbro.Body.finalState] at h
          · simp only [List.cons_append, Gabbro.Body.exec, hs] at h
            rw [IH _ s' h p hp]
            apply Gabbro.Body.store_elsewhere
            intro e
            apply hp
            rw [e]
            exact hcn
        · have hcall : ∃ args, UStmt.call cname args ∈ st :: ss := by
            cases st
            case call cn args =>
              simp only [stmtBody] at hx
              split at hx
              · rename_i gf' es' _ _
                simp only [Option.some.injEq] at hx
                cases hx
                exact ⟨args, List.mem_cons_self ..⟩
              · cases hx
            case assign b f ix v =>
              simp only [stmtBody] at hx
              split at hx
              · simp only [Option.some.injEq] at hx; cases hx
              · cases hx
            case assignTab b f ix v =>
              simp only [stmtBody] at hx
              cases hsv : sideExpr u (fnAt u c) v with
              | none => rw [hsv] at hx; cases hx
              | some ve => rw [hsv] at hx; simp at hx
            all_goals simp [stmtBody] at hx
          rcases step_call ρ cname ps es pre t with hs | ⟨t', ht', hs⟩
          · simp [List.cons_append, Gabbro.Body.exec, hs, Gabbro.Body.finalState] at h
          · simp only [List.cons_append, Gabbro.Body.exec, hs] at h
            rw [IH _ s' h p hp]
            show (ρ cname t').1.world p = t.world p
            rw [hF cname gf hgf hcall t' p (fun hm => hp (hsub _ hm)), ht']
      · cases hbs

end Gabbro.Bruecke
