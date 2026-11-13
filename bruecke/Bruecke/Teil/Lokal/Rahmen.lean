module
public import Bruecke.Teil.Lokal.Ruf
public import Bruecke.Anweisung.Lokal.Rahmen
@[expose] public section

/-! Partial frames in every binding scope; only actual carried callees need shape duties. -/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- A lowered body statement writes a carrier the function declares, or calls a function it
    finds by name whose declared writes are its own -- in every scope. -/
theorem stmt_statisch_teilB (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) {Γ : Ctx} {fn : UFn}
    (hΓ : Γ = fn.params.map (·.2)) (st : UStmt)
    (hmem : st ∈ (fnAt u c).body) {Λ Λ' : List (Res (declOf u))}
    {g : Stmt (declOf u) (verOf u c) false Γ Λ Λ'}
    (h : lowStmtL (l := false) u c Γ fn Λ st = .ok ⟨Λ', g⟩) {bst : Gabbro.Body.Stmt}
    (hb : stmtBody u fn st = some bst) :
    (∃ cn idx fld ve, bst = .assign cn idx fld ve ∧ cn ∈ (fnAt u c).puts) ∨
    (∃ cname ps es pre gf, bst = .call cname ps es pre ∧ fnSuch u cname = some gf ∧
      ∀ w ∈ gf.puts, w ∈ (fnAt u c).puts) := by
  cases st
  case assign b fname ix v =>
    rw [lowStmtL_assign S.tab c Γ fn Λ b fname ix v] at h
    have pointerWrite {space num j : Nat} {read : Bool} {owner : Option Nat}
        (pv : Var Γ (.ptr ⟨space, ⟨read, true, owner⟩, .table num⟩))
        (hj : paramPos fn.params b = .ok j)
        (hpv : lowVar Γ j (.ptr ⟨space, ⟨read, true, owner⟩, .table num⟩) = .ok pv)
        (hlt : num < u.tabs.length) (hw : writesAt u (fnAt u c) ⟨num, hlt⟩ = true) :
        ∃ cn idx fld ve, bst = .assign cn idx fld ve ∧ cn ∈ (fnAt u c).puts := by
      have hparam : (fn.params[j]?).map (·.2) =
          some (.ptr ⟨space, ⟨read, true, owner⟩, .table num⟩) := by
        simpa only [hΓ, List.getElem?_map] using (lowVar_typ Γ j _ pv hpv)
      have hpt := ptrTab_of_type fn b j num read true hj hparam hlt
      simp only [stmtBody, hpt] at hb
      cases hsv : sideExpr u fn v with
      | none => rw [hsv] at hb; cases hb
      | some ve =>
        rw [hsv] at hb
        cases hb
        exact ⟨_, _, _, _, rfl, any_mem hw⟩
    cases stored : lowAssignDurchL (l := false) u c Γ fn Λ b fname ix v with
    | error error => simp only [stored, Except.map] at h <;> cases h
    | ok statement =>
      simp only [stored, Except.map] at h
      cases h
      have h := stored
      unfold lowAssignDurchL at h
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
    rw [lowStmtL_assignTab S.tab c Γ fn Λ b fname ix v] at h
    cases stored : lowAssignTabL (l := false) u c Γ fn Λ b fname ix v with
    | error error => simp only [stored, Except.map] at h <;> cases h
    | ok statement =>
      simp only [stored, Except.map] at h
      cases h
      have h := stored
      simp only [lowAssignTabL] at h
      split at h
      · cases h
      · rename_i t ht
        repeat' split at h
        all_goals try cases h
        rename_i hw
        left
        simp only [stmtBody] at hb
        cases hsv : sideExpr u fn v with
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
    have h' : lowCallL (l := false) u c Γ fn Λ cname args = .ok ⟨Λ', g⟩ := h
    unfold lowCallL at h'
    split at h'
    · cases h'
    · rename_i k hk
      obtain ⟨hcallee, _, hWr⟩ := lowRufKopf_ok hk
      right
      have hfs : fnSuch u cname = some (fnAt u k.callee) := fnIdx_find _ _ _ hcallee
      simp only [stmtBody, hfs] at hb
      cases hes : argsExpr u fn args with
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

/-- A slot write or a call keeps every carrier the function does not declare. -/
theorem rahmen_schritt_teilB (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (ρB : Gabbro.Body.Env)
    {Γ : Ctx} {fn : UFn} (hΓ : Γ = fn.params.map (·.2)) (st : UStmt) (ss : List UStmt)
    (hmem : st ∈ (fnAt u c).body)
    {Λ Λ' : List (Res (declOf u))} {g : Stmt (declOf u) (verOf u c) false Γ Λ Λ'}
    (hgst : lowStmtL (l := false) u c Γ fn Λ st = .ok ⟨Λ', g⟩) {bB : Gabbro.Body.Stmt}
    (hx : stmtBody u fn st = some bB)
    (hF : ∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ st :: ss) →
      Gabbro.Body.Frame ρB cname gf.puts)
    {bs' : List Gabbro.Body.Stmt}
    (IH : ∀ t s', Gabbro.Body.finalState (Gabbro.Body.exec ρB bs' t) = some s' →
      ∀ p, p.carrier ∉ (fnAt u c).puts → s'.world p = t.world p) :
    ∀ t s', Gabbro.Body.finalState (Gabbro.Body.exec ρB (bB :: bs') t) = some s' →
      ∀ p, p.carrier ∉ (fnAt u c).puts → s'.world p = t.world p := by
  intro t s' h p hp
  rcases stmt_statisch_teilB S c hc hΓ st hmem hgst hx with ⟨cn, idx, fld, ve, rfl, hcn⟩ |
      ⟨cname, ps, es, pre, gf, rfl, hgf, hsub⟩
  · rcases step_assign ρB cn idx fld ve t with hs | ⟨k, v, hs⟩
    · simp [Gabbro.Body.exec, hs, Gabbro.Body.finalState] at h
    · simp only [Gabbro.Body.exec, hs] at h
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
        cases hsv : sideExpr u fn v with
        | none => rw [hsv] at hx; cases hx
        | some ve => rw [hsv] at hx; simp at hx
      all_goals simp [stmtBody] at hx
    rcases step_call ρB cname ps es pre t with hs | ⟨t', ht', hs⟩
    · simp [Gabbro.Body.exec, hs, Gabbro.Body.finalState] at h
    · simp only [Gabbro.Body.exec, hs] at h
      rw [IH _ s' h p hp]
      show (ρB cname t').1.world p = t.world p
      rw [hF cname gf hgf hcall t' p (fun hm => hp (hsub _ hm)), ht']

/-- **A body with local bindings changes only the carriers its function declares** -- given the
    frames of the functions it calls. -/
theorem exec_rahmen_teilB (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (ρB : Gabbro.Body.Env) (r : URet) :
    ∀ (n : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) {Λ : List (Res (declOf u))}
      (b0 : Endblock (declOf u) (verOf u c) false Γ Λ) (bs : List Gabbro.Body.Stmt),
      Γ = fn.params.map (·.2) → Sicht u fT fn →
      (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      lowBodyF u c Γ fn n Λ ss r = .ok b0 → stmtsBodyB u fT ss r = some bs →
      (∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ ss) →
        Gabbro.Body.Frame ρB cname gf.puts) →
      ∀ t s', Gabbro.Body.finalState (Gabbro.Body.exec ρB bs t) = some s' →
        ∀ p, p.carrier ∉ (fnAt u c).puts → s'.world p = t.world p
  | 0, ss, Γ, fn, fT, Λ, b0, bs, hΓ, hS, hmem, hlow, hbs, hF => by
      simp only [lowBodyF] at hlow <;> cases hlow
  | n + 1, [], Γ, fn, fT, Λ, b0, bs, hΓ, hS, hmem, hlow, hbs, hF => by
      intro t s' h p _
      rw [exec_rets ρB bs (endBody_rets (fn := fT) (r := r) hbs) t s' h]
  | n + 1, s0 :: ss, Γ, fn, fT, Λ, b0, bs, hΓ, hS, hmem, hlow, hbs, hF => by
      obtain ⟨bB, fT', bs', hstep0, hbs', rfl⟩ := stmtsBodyB_cons hbs
      have hFss : ∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ ss) →
          Gabbro.Body.Frame ρB cname gf.puts :=
        fun cn gf hgf ⟨args, hm⟩ => hF cn gf hgf ⟨args, List.mem_cons_of_mem _ hm⟩
      have hmemss : ∀ st ∈ ss, st ∈ (fnAt u c).body :=
        fun st hm => hmem st (List.mem_cons_of_mem _ hm)
      have hhead : s0 ∈ (fnAt u c).body := hmem s0 (List.mem_cons_self ..)
      cases s0
      case bind x d v =>
        obtain ⟨eT, heT, rfl, rfl⟩ := schrittB_bind hstep0
        obtain ⟨ls, rest, hls, hrest, rfl⟩ := lowBodyF_bind_ok c hlow
        exact rahmen_bind ρB x eT bs' _ (exec_rahmen_teilB S c hc ρB r n ss (fn.mitBindung x ls.range)
          (fT.mitBindung x (0, 0)) rest bs' (by rw [mitBindung_ctx]; exact congrArg (List.cons _) hΓ)
          (hS.bind x (0, 0) ls.range) hmemss hrest hbs' hFss)
      case bindMut x lo hi v =>
        obtain ⟨eT, heT, rfl, rfl⟩ := schrittB_bindMut hstep0
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindMut_ok c hlow
        exact rahmen_bind ρB x eT bs' _ (exec_rahmen_teilB S c hc ρB r n ss (fn.mitBindung x (lo, hi))
          (fT.mitBindung x (lo, hi)) rest bs' (by rw [mitBindung_ctx]; exact congrArg (List.cons _) hΓ)
          (hS.bind x (lo, hi) (lo, hi)) hmemss hrest hbs' hFss)
      case setVar x v =>
        obtain ⟨_, eT, heT, rfl, rfl⟩ := schrittB_setVar hstep0
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r (.setVar x v) ss trivial hlow
        exact rahmen_bind ρB x eT bs' _
          (exec_rahmen_teilB S c hc ρB r n ss fn _ rest bs' hΓ hS hmemss hrest hbs' hFss)
      case assign b' f i v =>
        obtain ⟨hxT, rfl⟩ := schrittB_stmt hstep0 (fun _ _ _ h => by cases h)
          (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
        have hx : stmtBody u fn (.assign b' f i v) = some bB :=
          (stmtBody_sicht hS _).symm.trans hxT
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r (.assign b' f i v) ss trivial hlow
        exact rahmen_schritt_teilB S c hc ρB hΓ _ ss hhead hgst hx hF
          (exec_rahmen_teilB S c hc ρB r n ss fn _ rest bs' hΓ hS hmemss hrest hbs' hFss)
      case assignTab b' f i v =>
        obtain ⟨hxT, rfl⟩ := schrittB_stmt hstep0 (fun _ _ _ h => by cases h)
          (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
        have hx : stmtBody u fn (.assignTab b' f i v) = some bB :=
          (stmtBody_sicht hS _).symm.trans hxT
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r (.assignTab b' f i v) ss trivial hlow
        exact rahmen_schritt_teilB S c hc ρB hΓ _ ss hhead hgst hx hF
          (exec_rahmen_teilB S c hc ρB r n ss fn _ rest bs' hΓ hS hmemss hrest hbs' hFss)
      case call cname args =>
        obtain ⟨hxT, rfl⟩ := schrittB_stmt hstep0 (fun _ _ _ h => by cases h)
          (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
        have hx : stmtBody u fn (.call cname args) = some bB :=
          (stmtBody_sicht hS _).symm.trans hxT
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r (.call cname args) ss trivial hlow
        exact rahmen_schritt_teilB S c hc ρB hΓ _ ss hhead hgst hx hF
          (exec_rahmen_teilB S c hc ρB r n ss fn _ rest bs' hΓ hS hmemss hrest hbs' hFss)
      all_goals simp [schrittB, stmtBody] at hstep0

end Gabbro.Bruecke
