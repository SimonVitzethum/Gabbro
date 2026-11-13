module
public import Bruecke.Anweisung.Zweig.Strecke
@[expose] public section

/-!
# C6, part 4: one statement against one Body statement

The statements the body and the block reader pass to `lowStmtL` (an assignment to a number
local, a slot write through a pointer or at a table, a direct call), a `return` inside a block,
and a conditional, each as a `StmtZiel`: the same simulations as `laufB`'s cases
(`lowSetVar_sim`, `lowAssignDurch_simB`, `lowAssignTab_simB`, `lowCall_simB`), cut at the
statement so that the body reader (`laufZ`) and the block reader (`laufSeq`) share them. A branch
condition is an `ensures` predicate without `old` and `result` (`lowEns_sim` with an empty
accumulator).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- A statement that falls through to related states. -/
theorem stmtZiel_ok {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ Λ₁ : List (Res (declOf u))} {fn : UFn}
    {st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁} {σ σ₁ : World (declOf u)}
    {ρ ρ₁ : Env (declOf u) Γ} {s s₁ : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    {A : List Eintrag} (hex : execStmt O passes R st σ ρ = .ok σ₁ ρ₁)
    (hS : Strecke u A s s₁ [x]) (hW₁ : WRel u σ₁ s₁.world) (hL₁ : LRel fn 0 ρ₁ s₁.local') :
    StmtZiel u c O passes R fn st σ ρ s x :=
  ⟨fun e h => (by rw [hex] at h; cases h), fun σ' v h => (by rw [hex] at h; cases h),
    fun σ' ρ' h => by
      rw [hex] at h
      cases h
      exact ⟨A, s₁, hS, hW₁, hL₁⟩⟩

/-- **The statements `lowStmtL` reads**, each against its Body statement. -/
theorem stmtZiel_einzeln {P : Programm (declOf u)} (G : Gesenkt u P) (S : Stimmig u)
    (c : Fin u.fns.length) (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) {Γ : Ctx} {fn : UFn} {Λ Λ' : List (Res (declOf u))}
    {st0 : UStmt} {gst : Stmt (declOf u) (verOf u c) false Γ Λ Λ'} {bB : Gabbro.Body.Stmt}
    (hs : LeseEinzeln st0) (hgst : lowStmtL (l := false) u c Γ fn Λ st0 = .ok ⟨Λ', gst⟩)
    (hb : schrittB u fn st0 = some (bB, fn)) (hU : UmfangB Γ fn)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    StmtZiel u c O passes R fn gst σ ρ s bB := by
  cases st0
  case setVar x v =>
    obtain ⟨hn, eT, heT, rfl, -⟩ := schrittB_setVar hb
    simp only [lowStmtL] at hgst
    cases hsv : lowSetVarL (l := false) u c Γ fn Λ x v with
    | error err => simp only [hsv, Except.map] at hgst <;> cases hgst
    | ok st1 =>
      simp only [hsv, Except.map] at hgst
      cases hgst
      obtain ⟨σ₁, ρ₁, bv, hex, hsl, hstep, hL'⟩ :=
        lowSetVar_sim c hsv hn heT hU S.tab O passes R σ ρ s hW hL
      exact stmtZiel_ok hex (Strecke.schritt (fun ρB _ => hstep ρB) (fun w => Int.le_refl _))
        (wrel_slots u hsl hW) hL'
  case assign b' f i v =>
    obtain ⟨hx, -⟩ := schrittB_stmt hb (fun _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
    rw [lowStmtL_assign S.tab c Γ fn Λ b' f i v] at hgst
    cases stored : lowAssignDurchL (l := false) u c Γ fn Λ b' f i v with
    | error err => simp only [stored, Except.map] at hgst <;> cases hgst
    | ok statement =>
      simp only [stored, Except.map] at hgst
      cases hgst
      obtain ⟨σ₁, cn, k, fld, val, hex, hstep, hW₁, _⟩ :=
        lowAssignDurch_simB c stored hx hU S.tab O passes R σ ρ s hW hL
      exact stmtZiel_ok hex (Strecke.schritt (fun ρB _ => hstep ρB)
        (fun w => Int.le_of_eq (gz_store_slot w cn k fld s.world val).symm)) hW₁ hL
  case assignTab b' f i v =>
    obtain ⟨hx, -⟩ := schrittB_stmt hb (fun _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
    rw [lowStmtL_assignTab S.tab c Γ fn Λ b' f i v] at hgst
    cases stored : lowAssignTabL (l := false) u c Γ fn Λ b' f i v with
    | error err => simp only [stored, Except.map] at hgst <;> cases hgst
    | ok statement =>
      simp only [stored, Except.map] at hgst
      cases hgst
      obtain ⟨σ₁, cn, k, fld, val, hex, hstep, hW₁, _⟩ :=
        lowAssignTab_simB c stored hx hU S.tab O passes R σ ρ s hW hL
      exact stmtZiel_ok hex (Strecke.schritt (fun ρB _ => hstep ρB)
        (fun w => Int.le_of_eq (gz_store_slot w cn k fld s.world val).symm)) hW₁ hL
  case call cname args =>
    obtain ⟨hx, -⟩ := schrittB_stmt hb (fun _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
    have hgst' : lowCallL (l := false) u c Γ fn Λ cname args = .ok ⟨Λ', gst⟩ := hgst
    obtain ⟨callee, σr, envA, hname, hfs, hsl, hstep, hLt, _, hcases, _⟩ :=
      lowCall_simB c hgst' hx hU S.tab S.namen (fun c' => (S.art c').2.1) O passes R σ ρ s hW hL
    have hWr : WRel u σr s.world := wrel_slots u hsl hW
    rcases hcases with ⟨σ', v, hR, hex⟩ | ⟨e, hR, hex⟩ | ⟨e, hR, hex⟩
    · have hfr := (hRR.2 callee σr envA σ' v hR).1.1
      cases hwc : (fnAt u callee).puts with
      | nil =>
        -- a callee that writes nothing: the world stays
        have hsl' : σ'.slots = σ.slots := by
          funext t' k' f'
          rw [← hsl]
          apply hfr
          show ((declOf u).signatur callee).schreibt t' = false
          refine (sigSchreibt_eq u callee t').trans ?_
          unfold writesAt
          rw [hwc]; rfl
        refine stmtZiel_ok (A := []) (s₁ := s) hex
          (Strecke.schritt (s₁ := s) (fun ρB hF => ?_) (fun w => Int.le_refl _))
          (wrel_slots u hsl' hW) hL
        have hstay : ∀ t, (ρB cname t).1.world = t.world := by
          intro t
          funext p
          exact hF cname _ hfs t p (by rw [hwc]; simp)
        rw [hstep ρB, hstay]
      | cons w ws =>
        -- a writer: one entry, its ghost bumped
        let t : Gabbro.Body.State := ⟨s.world, Gabbro.Body.bindAll
          ((fnAt u callee).params.map (·.1)) (envVals envA) (fun _ => .absent)⟩
        let e0 : Eintrag := ⟨cname, t, antwort w σ' t (ergValOf ((declOf u).erg callee) v)⟩
        let s₁ : Gabbro.Body.State := ⟨bump w (enc u σ' s.world), s.local'⟩
        have hW₁ : WRel u σ' s₁.world := wrel_bump w (wrel_enc u σ' s.world)
        have hgeist : geistVon u cname = some w := by
          simp [geistVon, hfs, hwc]
        have hgz1 : gz w s₁.world = gz w s.world + 1 := by
          show gz w (bump w (enc u σ' s.world)) = _
          rw [gz_bump_self, gz_enc]
        have hS : Strecke u [e0] s s₁ [bB] :=
          { gut := fun e he => by
              rcases List.mem_singleton.mp he with rfl
              exact eintrag_gut G S R hRR callee σr σ' envA v hR t hWr hLt w ws hwc cname hfs
            oben := fun e he => by
              rcases List.mem_singleton.mp he with rfl
              exact ⟨w, hgeist, Int.le_refl _⟩
            unten := fun e he => by
              rcases List.mem_singleton.mp he with rfl
              refine ⟨w, hgeist, ?_⟩
              show gz w s.world < gz w s₁.world
              rw [hgz1]
              omega
            schluessel := List.pairwise_singleton _ _
            mono := fun w' => by
              have := gz_bump_le w w' (enc u σ' s.world)
              rw [gz_enc] at this
              exact this
            lauf := fun ρB hT hF => by
              have he0 : ρB cname t = e0.aus := hT e0 (List.mem_singleton_self _)
              have hs : Gabbro.Body.step ρB bB s = .running s₁ := by
                rw [hstep ρB, he0]; rfl
              simp only [Gabbro.Body.exec, hs] }
        exact stmtZiel_ok hex hS hW₁ hL
    · exact ⟨fun e' h => by rw [hex] at h; cases h; exact ⟨callee, σr, envA, hR⟩,
        fun σ' v h => (by rw [hex] at h; cases h), fun σ' ρ' h => by rw [hex] at h; cases h⟩
    · exact ⟨fun e' h => (by rw [hex] at h; cases h), fun σ' v h => (by rw [hex] at h; cases h),
        fun σ' ρ' h => by rw [hex] at h; cases h⟩
  all_goals simp [LeseEinzeln] at hs

/-- **`return [v];` inside a block** (`lowRetStmt` without crossed scopes): the G statement returns
    the value the Body `ret` returns, the world kept. -/
theorem lowRet_sim (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {r : URet} {st : Stmt (declOf u) (verOf u c) false Γ Λ Λ} {bst : Gabbro.Body.Stmt}
    (h : lowRetStmt (l := false) u c Γ fn Λ [] r = .ok st) (hb : retZ u fn r = some bst)
    (hU : UmfangB Γ fn) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    ∃ σ' v, execStmt O passes R st σ ρ = .zurueck σ' v ∧ σ'.slots = σ.slots ∧
      ∀ ρB : Gabbro.Body.Env,
        Gabbro.Body.step ρB bst s = .returned s (ergValOf (verOf u c).erg v) := by
  have hA := hU.art
  cases r
  case empty =>
    simp only [retZ, Option.some.injEq] at hb
    subst hb
    simp only [lowRetStmt] at h
    cases hE : lowErg u c Γ Λ fn .empty with
    | error e => simp only [hE, Except.bind] at h <;> cases h
    | ok E =>
      simp only [hE, Except.bind] at h
      split at h
      · cases h
        refine ⟨_, _, rfl, rfl, fun ρB => ?_⟩
        simp only [lowErg] at hE
        split at hE
        · rename_i hErg
          have he : (verOf u c).erg = none := by
            show (vertragVon (declOf u) c).erg = none
            rw [vErg_eq u c, hErg]
          rw [ergValOf_none _ he]
          all_goals first
            | rfl
            | simp only [Gabbro.Body.step]
        · cases hE
      · cases h
  case val sd =>
    simp only [retZ] at hb
    cases hs : sideExpr u fn sd with
    | none => rw [hs] at hb; cases hb
    | some e =>
      rw [hs] at hb
      simp only [Option.map_some, Option.some.injEq] at hb
      subst hb
      simp only [lowRetStmt] at h
      cases hE : lowErg u c Γ Λ fn (.val sd) with
      | error err => simp only [hE, Except.bind] at h <;> cases h
      | ok E =>
        simp only [hE, Except.bind] at h
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
              simp only [Gabbro.Body.step, hv]
              all_goals first
                | rfl
                | trivial
          · cases hE
          · cases hE
        · cases h
  all_goals simp [retZ] at hb

theorem stmtZiel_ret (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {r : URet} {st : Stmt (declOf u) (verOf u c) false Γ Λ Λ} {bst : Gabbro.Body.Stmt}
    (h : lowRetStmt (l := false) u c Γ fn Λ [] r = .ok st) (hb : retZ u fn r = some bst)
    (hU : UmfangB Γ fn) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    StmtZiel u c O passes R fn st σ ρ s bst := by
  obtain ⟨σ', v, hex, hsl, hstep⟩ := lowRet_sim c h hb hU hT O passes R σ ρ s hW hL
  refine ⟨fun e h' => (by rw [hex] at h'; cases h'), fun σ'' v' h' => ?_,
    fun σ'' ρ'' h' => by rw [hex] at h'; cases h'⟩
  rw [hex] at h'
  cases h'
  refine ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    List.Pairwise.nil, fun ρB _ _ => ⟨s, ?_, wrel_slots u hsl hW⟩⟩
  simp only [Gabbro.Body.exec, hstep ρB]

/-- **A conditional**: its condition reads in Body as the G truth value, so the Body `ite` runs
    the branch the G statement runs. -/
theorem stmtZiel_ite (S : Stimmig u) {c : Fin u.fns.length} {O : Orakel (declOf u)}
    {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {fn fT : UFn} {Λ Λ₁ : List (Res (declOf u))} {cnd : UEns}
    {cv : Expr (declOf u) Γ Λ .bool} {tb eb : Block (declOf u) (verOf u c) false Γ Λ Λ₁}
    {ce : Gabbro.Body.Expr} {tt te : List Gabbro.Body.Stmt}
    (hU : UmfangB Γ fn) (hS : Sicht u fT fn) (hcv : lowEns u Γ Λ fn none cnd = .ok cv)
    (hce : condZ u fT cnd = some ce)
    (hBt : ∀ σ ρ s, WRel u σ s.world → LRel fn 0 ρ s.local' →
      BlockZiel u c O passes R fn tb σ ρ s tt)
    (hBe : ∀ σ ρ s, WRel u σ s.world → LRel fn 0 ρ s.local' →
      BlockZiel u c O passes R fn eb σ ρ s te)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    StmtZiel u c O passes R fn (Stmt.ite cv tb eb) σ ρ s (.ite ce tt te) := by
  have hceN : condZ u fn cnd = some ce := (condZ_sicht hS cnd).symm.trans hce
  obtain ⟨a, hens, hold, hres⟩ := condZ_some hceN
  have hWl : WRel u (σ.lese Λ cv.orte) s.world := wrel_slots u rfl hW
  have hB : EnsBind fn none ρ s a s.local' :=
    ⟨hL, fun hr => (by rw [hres] at hr; cases hr),
      fun i hi => by rw [hold] at hi; exact absurd hi (Nat.not_lt_zero _)⟩
  have hcond : Gabbro.Body.eval s ce =
      some (.bool (wahr? (eval (σ.lese Λ cv.orte) cv (σ.lese Λ cv.orte) ρ))) :=
    lowEns_sim (er := none) hU.art S.tab (σ.lese Λ cv.orte) (σ.lese Λ cv.orte) ρ s s.world
      s.local' a hWl hL hWl hB cnd hens hcv (Vor.refl a)
  cases hb : wahr? (eval (σ.lese Λ cv.orte) cv (σ.lese Λ cv.orte) ρ) with
  | true =>
    rw [hb] at hcond
    have hG : execStmt O passes R (Stmt.ite cv tb eb) σ ρ =
        execBlock O passes R tb (σ.lese Λ cv.orte) ρ := by
      rw [execStmtZ_ite, hb]
      try exact if_pos rfl
    exact stmtZiel_of hG (fun ρB => step_ite_wahr ρB hcond) (hBt _ ρ s hWl hL)
  | false =>
    rw [hb] at hcond
    have hG : execStmt O passes R (Stmt.ite cv tb eb) σ ρ =
        execBlock O passes R eb (σ.lese Λ cv.orte) ρ := by
      rw [execStmtZ_ite, hb]
      try exact if_neg Bool.false_ne_true
    exact stmtZiel_of hG (fun ρB => step_ite_falsch ρB hcond) (hBe _ ρ s hWl hL)

end Gabbro.Bruecke
