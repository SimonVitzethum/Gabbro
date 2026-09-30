import Bruecke.Lauf

/-!
# S3, part 6: a Body environment that keeps every contract -- where the call graph is ordered

The duty `meetsU` quantifies over every environment that keeps the callees' contracts
(`Contract`, for EVERY entry state) and frames. To use a duty, one such environment must EXIST.
For a call graph with a rank (every call goes to a strictly smaller rank, `Rang`) it does: the
environment that runs each body with the environments of the smaller ranks (`realisiert`). The
rank is not a convenience: with a cycle, a contract nothing can keep (`ensures false`, a
function that only calls itself) makes every duty that calls it true by vacuity, while the G
handler class of `KoerperGutR` asks the contract only where a call is made -- see the report.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. Static facts of the lowered statements -/

theorem any_mem {l : List String} {x : String} (h : l.any (· == x) = true) : x ∈ l := by
  rw [List.any_eq_true] at h
  obtain ⟨y, hy, he⟩ := h
  have : y = x := by simpa using he
  exact this ▸ hy

/-- A lowered body statement writes a carrier the function declares, or calls a function it
    finds by name whose declared writes are its own. -/
theorem stmt_statisch (S : Stimmig u) (c : Fin u.fns.length) (st : UStmt)
    {g : Stmt (declOf u) (verOf u c) false (ctxOf u c) (resOf u c) (resOf u c)}
    (h : lowStmt u c st = .ok g) {bst : Gabbro.Body.Stmt}
    (hb : stmtBody u (fnAt u c) st = some bst) :
    (∃ cn idx fld ve, bst = .assign cn idx fld ve ∧ cn ∈ (fnAt u c).schreibt) ∨
    (∃ cname ps es pre gf, bst = .call cname ps es pre ∧ fnSuch u cname = some gf ∧
      ∀ w ∈ gf.schreibt, w ∈ (fnAt u c).schreibt) := by
  cases st with
  | assignB _ _ _ _ => simp [stmtBody] at hb
  | assignTabB _ _ _ _ => simp [stmtBody] at hb
  | sperrtAuf _ => simp [stmtBody] at hb
  | sperrtZu => simp [stmtBody] at hb
  | assign b fname ix v =>
    simp only [lowStmt, lowAssignDurch, lowAssignDurchL] at h
    split at h
    · cases h
    · rename_i j hj
      split at h
      · rename_i num hp
        split at h
        · rename_i hlt
          repeat' split at h
          all_goals try cases h
          rename_i hw
          left
          have hpt := ptrTab_of (fnAt u c) (S.art c) b j num true hj hp hlt
          simp only [stmtBody, hpt] at hb
          cases hsv : sideExpr u (fnAt u c) v with
          | none => rw [hsv] at hb; cases hb
          | some ve =>
            rw [hsv] at hb
            cases hb
            exact ⟨_, _, _, _, rfl, any_mem hw⟩
        · cases h
      · cases h
  | assignTab b fname ix v =>
    simp only [lowStmt, lowAssignTab, lowAssignTabL] at h
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
  | call cname args =>
    simp only [lowStmt, lowCall, lowCallL] at h
    split at h
    · cases h
    · rename_i callee hcallee
      split at h
      · cases h
      · rename_i a ha
        split at h
        · rename_i hWr
          right
          have hfs : fnSuch u cname = some (fnAt u callee) := fnIdx_find _ _ _ hcallee
          simp only [stmtBody, hfs] at hb
          cases hes : argsExpr u (fnAt u c) args with
          | none => rw [hes] at hb; cases hb
          | some es =>
            rw [hes] at hb
            cases hb
            refine ⟨_, _, _, _, _, rfl, hfs, fun w hw => ?_⟩
            obtain ⟨t, rfl⟩ := S.schreibt callee w hw
            have h1 : writesAt u (fnAt u callee) t = true := by
              unfold writesAt; exact List.any_eq_true.mpr ⟨_, hw, by simp⟩
            have h2 := hWr t h1
            unfold writesAt at h2
            exact any_mem h2
        · cases h

/-! ## 2. The Body frame of a body -/

theorem lowBody_stmts (c : Fin u.fns.length) (r : URet) : ∀ (ss : List UStmt)
    (b0 : Endblock (declOf u) (verOf u c) false (ctxOf u c) (resOf u c)),
    (∀ st ∈ ss, (stmtBody u (fnAt u c) st).isSome = true) →
    lowBody u c ss r = .ok b0 → ∀ st ∈ ss, ∃ g, lowStmt u c st = .ok g
  | [], _, _, _, st, hm => absurd hm List.not_mem_nil
  | s :: ss, b0, hsome, h, st, hm => by
      rw [lowBody_cons c r s ss (stmtBody_nomark _ s (hsome s List.mem_cons_self))] at h
      split at h
      · cases h
      · rename_i g hg
        split at h
        · cases h
        · rename_i rest hrest
          rcases List.mem_cons.mp hm with rfl | hm
          · exact ⟨g, hg⟩
          · exact lowBody_stmts c r ss rest (fun x hx => hsome x (List.mem_cons_of_mem _ hx)) hrest st hm

theorem step_assign (ρ : Gabbro.Body.Env) (cn : String) (idx : Gabbro.Body.Expr) (fld : String)
    (ve : Gabbro.Body.Expr) (t : Gabbro.Body.State) :
    Gabbro.Body.step ρ (.assign cn idx fld ve) t = .stuck ∨
      ∃ k v, Gabbro.Body.step ρ (.assign cn idx fld ve) t =
        .running ⟨Gabbro.Body.store t.world (.slot cn k fld) v, t.local'⟩ := by
  simp only [Gabbro.Body.step]
  split
  · rename_i k v _ _
    exact .inr ⟨k, v, rfl⟩
  · exact .inl rfl

theorem step_call (ρ : Gabbro.Body.Env) (g : String) (ps : List String) (es : List Gabbro.Body.Expr)
    (pre : Gabbro.Body.Expr) (t : Gabbro.Body.State) :
    Gabbro.Body.step ρ (.call g ps es pre) t = .stuck ∨
      ∃ t' : Gabbro.Body.State, t'.world = t.world ∧ Gabbro.Body.step ρ (.call g ps es pre) t =
        .running ⟨(ρ g t').1.world, t.local'⟩ := by
  simp only [Gabbro.Body.step]
  split
  · rename_i vs _
    split
    · exact .inr ⟨⟨t.world, Gabbro.Body.bindAll ps vs (fun _ => .absent)⟩, rfl, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

theorem exec_rets (ρ : Gabbro.Body.Env) : ∀ (eB : List Gabbro.Body.Stmt),
    (∀ x ∈ eB, ∃ e, x = .ret (some e)) → ∀ t s',
    Gabbro.Body.finalState (Gabbro.Body.exec ρ eB t) = some s' → s' = t
  | [], _, t, s', h => by
      simp only [Gabbro.Body.exec, Gabbro.Body.finalState, Option.some.injEq] at h
      exact h.symm
  | x :: rest, hx, t, s', h => by
      obtain ⟨e, rfl⟩ := hx x (List.mem_cons_self ..)
      simp only [Gabbro.Body.exec, Gabbro.Body.step] at h
      cases hv : Gabbro.Body.eval t e with
      | none => simp [hv, Gabbro.Body.finalState] at h
      | some v =>
        simp only [hv, Gabbro.Body.finalState, Option.some.injEq] at h
        exact h.symm

/-- **A body changes only the carriers its function declares** -- given the frames of the
    functions it calls. -/
theorem exec_rahmen (S : Stimmig u) (c : Fin u.fns.length) (ρ : Gabbro.Body.Env)
    (eB : List Gabbro.Body.Stmt) (heB : ∀ x ∈ eB, ∃ e, x = .ret (some e)) :
    ∀ (ss : List UStmt) (bs : List Gabbro.Body.Stmt),
      (∀ st ∈ ss, ∃ g, lowStmt u c st = .ok g) → stmtsBody u (fnAt u c) ss = some bs →
      (∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ ss) →
        Gabbro.Body.Frame ρ cname gf.schreibt) →
      ∀ t s', Gabbro.Body.finalState (Gabbro.Body.exec ρ (bs ++ eB) t) = some s' →
        ∀ p, p.carrier ∉ (fnAt u c).schreibt → s'.world p = t.world p
  | [], bs, _, hbs, _, t, s', h, p, _ => by
      simp only [stmtsBody, Option.some.injEq] at hbs
      subst hbs
      rw [exec_rets ρ eB heB t s' h]
  | st :: ss, bs, hlow, hbs, hF, t, s', h, p, hp => by
      simp only [stmtsBody] at hbs
      split at hbs
      · rename_i x xs hx hxs
        simp only [Option.some.injEq] at hbs
        subst hbs
        obtain ⟨g, hg⟩ := hlow st (List.mem_cons_self ..)
        have IH := exec_rahmen S c ρ eB heB ss xs (fun st' hm => hlow st' (List.mem_cons_of_mem _ hm))
          hxs (fun cn gf hgf ⟨args, hm⟩ => hF cn gf hgf ⟨args, List.mem_cons_of_mem _ hm⟩)
        rcases stmt_statisch S c st hg hx with ⟨cn, idx, fld, ve, rfl, hcn⟩ |
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
            cases st with
            | assignB _ _ _ _ => simp [stmtBody] at hx
            | assignTabB _ _ _ _ => simp [stmtBody] at hx
            | sperrtAuf _ => simp [stmtBody] at hx
            | sperrtZu => simp [stmtBody] at hx
            | call cn args =>
              simp only [stmtBody] at hx
              split at hx
              · rename_i gf' es' _ _
                simp only [Option.some.injEq] at hx
                cases hx
                exact ⟨args, List.mem_cons_self ..⟩
              · cases hx
            | assign b f ix v =>
              simp only [stmtBody] at hx
              split at hx
              · simp only [Option.some.injEq] at hx; cases hx
              · cases hx
            | assignTab b f ix v =>
              simp only [stmtBody] at hx
              cases hsv : sideExpr u (fnAt u c) v with
              | none => rw [hsv] at hx; cases hx
              | some ve => rw [hsv] at hx; simp at hx
          rcases step_call ρ cname ps es pre t with hs | ⟨t', ht', hs⟩
          · simp [List.cons_append, Gabbro.Body.exec, hs, Gabbro.Body.finalState] at h
          · simp only [List.cons_append, Gabbro.Body.exec, hs] at h
            rw [IH _ s' h p hp]
            show (ρ cname t').1.world p = t.world p
            rw [hF cname gf hgf hcall t' p (fun hm => hp (hsub _ hm)), ht']
      · cases hbs

/-! ## 3. The environment, rank by rank -/

/-- **The call graph has a rank**: every call goes to a name of strictly smaller rank. Checked
    per unit (`rangB`). -/
def Rang (u : UProg) (rk : String → Nat) : Prop :=
  ∀ c : Fin u.fns.length, ∀ cname args, UStmt.call cname args ∈ (fnAt u c).saetze →
    rk cname < rk (fnAt u c).name

/-- The promise of `gf` as the duty file states it. -/
def postP (u : UProg) (gf : UFn) : Gabbro.Body.State → Gabbro.Body.State →
    Option Gabbro.Body.Value → Prop :=
  fun s s' r => (postU u (wfU u) gf s s' r).getD False

/-- `ρ` keeps contract and frame of every function of rank below `k`. -/
def Realisiert (u : UProg) (rk : String → Nat) (k : Nat) (ρ : Gabbro.Body.Env) : Prop :=
  ∀ n gf, fnSuch u n = some gf → rk n < k →
    Gabbro.Body.Contract ρ n (preProp (wfU u) gf) (postP u gf) ∧ Gabbro.Body.Frame ρ n gf.schreibt

theorem hyps_elim (wf : Gabbro.Body.State → Prop) (ρ : Gabbro.Body.Env) : ∀ (gs : List String) (C : Prop),
    (∀ g ∈ gs, ∃ gf, fnSuch u g = some gf ∧
      Gabbro.Body.Contract ρ g (preProp wf gf) (fun s s' r => (postU u wf gf s s' r).getD False) ∧
      Gabbro.Body.Frame ρ g gf.schreibt) → hyps u wf ρ gs C → C
  | [], C, _, h => h
  | g :: gs, C, hg, h => by
      obtain ⟨gf, hgf, hc, hfr⟩ := hg g (List.mem_cons_self ..)
      simp only [hyps, hgf] at h
      exact hyps_elim wf ρ gs C (fun g' hm => hg g' (List.mem_cons_of_mem _ hm)) (h hc hfr)

theorem mem_insertS {x y : String} : ∀ {l : List String}, y ∈ insertS x l → y = x ∨ y ∈ l
  | [], h => by simp [insertS] at h; exact .inl h
  | z :: zs, h => by
      unfold insertS at h
      split at h
      · simpa using h
      · split at h
        · exact .inr h
        · rcases List.mem_cons.mp h with h | h
          · exact .inr (h ▸ List.mem_cons_self ..)
          · rcases mem_insertS h with h | h
            · exact .inl h
            · exact .inr (List.mem_cons_of_mem _ h)

theorem mem_sortDedup {y : String} : ∀ {l : List String}, y ∈ sortDedup l → y ∈ l
  | [], h => h
  | x :: xs, h => by
      rcases mem_insertS h with h | h
      · exact h ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_sortDedup h)

theorem mem_calleesOf {f : UFn} {g : String} (h : g ∈ calleesOf f) :
    ∃ args, UStmt.call g args ∈ f.saetze := by
  have h' := mem_sortDedup h
  rw [List.mem_filterMap] at h'
  obtain ⟨st, hst, hg⟩ := h'
  cases st with
  | call cn args =>
    simp only [Option.some.injEq] at hg
    subst hg
    exact ⟨args, hst⟩
  | assign a b c d => simp at hg
  | assignTab a b c d => simp at hg
  | assignB a b c d => simp at hg
  | assignTabB a b c d => simp at hg
  | sperrtAuf a => simp at hg
  | sperrtZu => simp at hg

theorem stmtsBody_mem {f : UFn} : ∀ {ss : List UStmt} {bs : List Gabbro.Body.Stmt},
    stmtsBody u f ss = some bs → ∀ st ∈ ss, ∃ x, stmtBody u f st = some x
  | [], _, _, st, hm => absurd hm List.not_mem_nil
  | s :: ss, bs, h, st, hm => by
      simp only [stmtsBody] at h
      split at h
      · rename_i x xs hx hxs
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨x, hx⟩
        · exact stmtsBody_mem hxs st hm
      · cases h

theorem callee_gefunden {f : UFn} {ss : List UStmt} {bs : List Gabbro.Body.Stmt}
    (h : stmtsBody u f ss = some bs) {g : String} {args : List UArg} (hm : UStmt.call g args ∈ ss) :
    ∃ gf, fnSuch u g = some gf := by
  obtain ⟨x, hx⟩ := stmtsBody_mem h _ hm
  simp only [stmtBody] at hx
  split at hx
  · rename_i gf es hgf _
    exact ⟨gf, hgf⟩
  · cases hx

theorem fnSuch_mem {n : String} {gf : UFn} (h : fnSuch u n = some gf) :
    ∃ c : Fin u.fns.length, fnAt u c = gf ∧ gf.name = n := by
  have hm := List.mem_of_find?_eq_some h
  have hn := List.find?_some h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  exact ⟨⟨i, hi⟩, rfl, by simpa using hn⟩

/-- **The environment exists, rank by rank.** -/
theorem realisiert (S : Stimmig u)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBody u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hlow : ∀ c : Fin u.fns.length, ∃ b0, lowBody u c (fnAt u c).saetze (fnAt u c).rueck = .ok b0)
    (rk : String → Nat) (hR : Rang u rk) : ∀ k, ∃ ρ, Realisiert u rk k ρ
  | 0 => ⟨fun _ t => (t, none), fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1 => by
      classical
      obtain ⟨ρk, hk⟩ := realisiert S hZ hlow rk hR k
      let ant : UFn → Gabbro.Body.State → Gabbro.Body.State × Option Gabbro.Body.Value :=
        fun gf t =>
          if preProp (wfU u) gf t then
            match Gabbro.Body.finalState (Gabbro.Body.exec ρk ((zuBody u gf).getD []) t) with
            | some s' => (s', Gabbro.Body.finalValue (Gabbro.Body.exec ρk ((zuBody u gf).getD []) t))
            | none => (t, none)
          else (t, none)
      let ρ' : Gabbro.Body.Env := fun n t =>
        if rk n = k then
          match fnSuch u n with
          | some gf => ant gf t
          | none => ρk n t
        else ρk n t
      refine ⟨ρ', fun n gf hgf hlt => ?_⟩
      by_cases hkn : rk n = k
      · have hρ' : ∀ t, ρ' n t = ant gf t := fun t => by simp only [ρ', hkn, ↓reduceIte, hgf]
        obtain ⟨c, rfl, hname⟩ := fnSuch_mem hgf
        obtain ⟨body, hbody, hmeets⟩ := hZ c
        obtain ⟨b0, hb0⟩ := hlow c
        rw [zuBody_eq] at hbody
        cases hbs : stmtsBody u (fnAt u c) (fnAt u c).saetze with
        | none => rw [hbs] at hbody; cases hbody
        | some bs =>
          rw [hbs] at hbody
          cases heB : endBody u (fnAt u c) (fnAt u c).rueck with
          | none => rw [heB] at hbody; cases hbody
          | some eB =>
            rw [heB] at hbody
            simp only [Option.map_some, Option.some.injEq] at hbody
            have hz : zuBody u (fnAt u c) = some (bs ++ eB) := by
              rw [zuBody_eq, hbs, heB]; rfl
            -- the callees: found, of smaller rank, so kept by `ρk`
            have hcallee : ∀ cn gf', fnSuch u cn = some gf' →
                (∃ args, UStmt.call cn args ∈ (fnAt u c).saetze) →
                Gabbro.Body.Contract ρk cn (preProp (wfU u) gf') (postP u gf') ∧
                Gabbro.Body.Frame ρk cn gf'.schreibt := fun cn gf' hgf' ⟨args, hm⟩ =>
              hk cn gf' hgf' (by have := hR c cn args hm; rw [hname] at this; omega)
            have heBr : ∀ x ∈ eB, ∃ e, x = .ret (some e) := by
              intro x hx
              cases hr : (fnAt u c).rueck with
              | keine => rw [hr] at heB; simp [endBody] at heB; subst heB; cases hx
              | bool _ => rw [hr] at heB; simp [endBody] at heB
              | wert v =>
                rw [hr] at heB
                simp only [endBody] at heB
                cases hs : sideExpr u (fnAt u c) v with
                | none => rw [hs] at heB; cases heB
                | some e =>
                  rw [hs] at heB
                  simp only [Option.map_some, Option.some.injEq] at heB
                  subst heB
                  simp at hx; exact ⟨e, hx⟩
            constructor
            · intro t hpre
              rw [hρ' t]
              simp only [ant, hpre, ↓reduceIte, hz, Option.getD_some]
              have hm := hmeets ρk t hpre.1 hpre.2
              subst hbody
              obtain ⟨s', hs', hpost⟩ := hyps_elim (wfU u) ρk (calleesOf (fnAt u c)) _ (fun g hg => by
                obtain ⟨args, hm'⟩ := mem_calleesOf hg
                obtain ⟨gf', hgf'⟩ := callee_gefunden hbs hm'
                exact ⟨gf', hgf', hcallee g gf' hgf' ⟨args, hm'⟩⟩) hm
              rw [hs']
              exact hpost
            · intro t p hp
              rw [hρ' t]
              simp only [ant]
              split
              · rw [hz, Option.getD_some]
                split
                · rename_i s' hs'
                  exact exec_rahmen S c ρk eB heBr _ bs (lowBody_stmts c _ _ b0 (stmtsBody_isSome hbs) hb0) hbs
                    (fun cn gf' hgf' hm => (hcallee cn gf' hgf' hm).2) t s' hs' p hp
                · rfl
              · rfl
      · obtain ⟨hc, hf⟩ := hk n gf hgf (by omega)
        refine ⟨fun t ht => ?_, fun t p hp => ?_⟩
        · simp only [ρ', if_neg hkn]; exact hc t ht
        · simp only [ρ', if_neg hkn]; exact hf t p hp

end Gabbro.Bruecke
