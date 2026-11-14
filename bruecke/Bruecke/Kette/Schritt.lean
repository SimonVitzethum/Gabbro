module
public import Bruecke.Kette.Verknuepfung
public import Bruecke.Anweisung.Zweig.Schritt
public import Bruecke.Teil.Lokal.Ruf
public import Bruecke.Anweisung.Lokal.Glob
public import Bruecke.Anweisung.Lokal.Ende
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem stmtZiel_ok_G {loopMode : Bool} {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {ids : List String} {Γ : Ctx} {Λ Λ₁ : List (Res (declOf u))} {fn : UFn}
    {st : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ₁} {σ σ₁ : World (declOf u)}
    {ρ ρ₁ : Env (declOf u) Γ} {s s₁ : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    {A : List Eintrag} (hex : execStmt O passes R st σ ρ = .ok σ₁ ρ₁)
    (hS : Strecke_G u C A s s₁ [x]) (hW₁ : WGRel u σ₁ s₁.world) (hL₁ : PositionalLRel fn ids 0 ρ₁ s₁.local') :
    StmtZiel_G u C c O passes R fn ids st σ ρ s x :=
  ⟨fun e h => (by rw [hex] at h; cases h), fun σ' v h => (by rw [hex] at h; cases h),
    fun σ' ρ' h => (by
      rw [hex] at h
      cases h
      exact ⟨A, s₁, hS, hW₁, hL₁⟩)⟩

theorem stmtZiel_einzeln_G {loopMode : Bool} {P : Programm (declOf u)} (G : GesenktC u C P) (S : Getragen u C)
    (c : Fin u.fns.length) (hc : C c) (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) {Γ : Ctx} {fn : UFn} {ns : BodyNames} {Λ Λ' : List (Res (declOf u))}
    {st0 : UStmt} {gst : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ'} {bB : Gabbro.Body.Stmt}
    (hmem : st0 ∈ (fnAt u c).body) (hs : LeseEinzeln st0) (hgst : lowStmtL (l := loopMode) u c Γ fn Λ st0 = .ok ⟨Λ', gst⟩)
    (hb : schrittB u fn ns st0 = some (bB, fn, ns)) (hU : UmfangB Γ fn ns)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    StmtZiel_G u C c O passes R fn ns.active gst σ ρ s bB := by
  cases st0
  case setVar x v =>
    obtain ⟨hn, id, eT, hid, heT, rfl, -, -⟩ := schrittB_setVar hb
    simp only [lowStmtL] at hgst
    cases hsv : lowSetVarL (l := loopMode) u c Γ fn Λ x v with
    | error err => simp only [hsv, Except.map] at hgst <;> cases hgst
    | ok st1 =>
      simp only [hsv, Except.map] at hgst
      cases hgst
      obtain ⟨σ₁, ρ₁, bv, hex, hsl, hstep, hL'⟩ :=
        lowSetVar_named_sim c hsv hn hid heT hU S.tab O passes R σ ρ s hW hL
      exact stmtZiel_ok_G hex (Strecke_G.schritt (fun ρB _ => hstep ρB) (fun w => Int.le_refl _))
        hsl hL'
  case setVarB x v =>
    obtain ⟨id, eT, hid, heT, rfl, -, -⟩ := schrittB_setVarB hb
    simp only [lowStmtL] at hgst
    cases hsv : lowSetVarBL (l := loopMode) u c Γ fn Λ x v with
    | error err => simp only [hsv, Except.map] at hgst; cases hgst
    | ok st1 =>
      simp only [hsv, Except.map] at hgst
      cases hgst
      obtain ⟨σ₁, ρ₁, bv, hex, hsl, hstep, hL'⟩ :=
        lowSetVarB_named_sim c hsv hid heT hU S.tab O passes R σ ρ s hW hL
      exact stmtZiel_ok_G hex (Strecke_G.schritt (fun ρB _ => hstep ρB) (fun w => Int.le_refl _))
        hsl hL'
  case assign b' f i v =>
    obtain ⟨hx, -, -⟩ := schrittB_stmt hb (fun _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
    rw [lowStmtL_assign S.tab c Γ fn Λ b' f i v] at hgst
    cases stored : lowAssignDurchL (l := loopMode) u c Γ fn Λ b' f i v with
    | error err => simp only [stored, Except.map] at hgst <;> cases hgst
    | ok statement =>
      simp only [stored, Except.map] at hgst
      cases hgst
      obtain ⟨σ₁, cn, k, fld, val, hex, hstep, hW₁, _⟩ :=
        lowAssignDurch_named_sim c stored hx hU S.tab O passes R σ ρ s hW hL
      exact stmtZiel_ok_G hex (Strecke_G.schritt (fun ρB _ => hstep ρB)
        (fun w => Int.le_of_eq (gz_store_slot w cn k fld s.world val).symm)) hW₁ hL
  case assignTab b' f i v =>
    obtain ⟨hx, -, -⟩ := schrittB_stmt hb (fun _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
    rw [lowStmtL_assignTab S.tab c Γ fn Λ b' f i v] at hgst
    cases stored : lowAssignTabL (l := loopMode) u c Γ fn Λ b' f i v with
    | error err => simp only [stored, Except.map] at hgst <;> cases hgst
    | ok statement =>
      simp only [stored, Except.map] at hgst
      cases hgst
      obtain ⟨σ₁, cn, k, fld, val, hex, hstep, hW₁, _⟩ :=
        lowAssignTab_named_sim c stored hx hU S.tab O passes R σ ρ s hW hL
      exact stmtZiel_ok_G hex (Strecke_G.schritt (fun ρB _ => hstep ρB)
        (fun w => Int.le_of_eq (gz_store_slot w cn k fld s.world val).symm)) hW₁ hL
  case assignGlob n v =>
    obtain ⟨hx, -, -⟩ := schrittB_stmt hb (fun _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
    simp only [lowStmtL] at hgst
    cases stored : lowAssignGlobL (l := loopMode) u c Γ fn Λ n v with
    | error err => simp only [stored, Except.map] at hgst; cases hgst
    | ok statement =>
      simp only [stored, Except.map] at hgst
      cases hgst
      obtain ⟨σ₁, val, hex, hstep, hW₁, _⟩ :=
        lowAssignGlob_sim c stored hx S.statics hU S.tab O passes R σ ρ s hW hL
      exact stmtZiel_ok_G hex (Strecke_G.schritt (fun ρB _ => hstep ρB)
        (fun w => Int.le_of_eq (gz_store_global w n s.world val).symm)) hW₁ hL
  case call cname args =>

    obtain ⟨hx, -, -⟩ := schrittB_stmt hb (fun _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
    have hgst' : lowCallL (l := loopMode) u c Γ fn Λ cname args = .ok ⟨Λ', gst⟩ := hgst
    obtain ⟨callee, σr, envA, hname, hfs, hsl, hstep, hLt, _, hcases, _⟩ :=
      lowCall_sim_teilB c hgst' hx hU S.tab (fun d hd =>
        ⟨S.namen d (callee_getragen_teil S hc hmem hd),
          (S.art d (callee_getragen_teil S hc hmem hd)).2.1⟩) O passes R σ ρ s hW hL
    have hcc : C callee := callee_getragen_teil S hc hmem hfs
    have hWr : WGRel u σr s.world := hsl
    rcases hcases with ⟨σ', v, hR, hex⟩ | ⟨e, hR, hex⟩ | ⟨e, hR, hex⟩
    · have hfr := (hRR.2 callee σr envA σ' v hR).1.1
      cases hwc : (writesU (fnAt u callee)) with
      | nil =>
        -- a callee that writes nothing: the world stays
        have hW' : WGRel u σ' s.world :=
          wgrel_rahmen_leer callee hWr (hRR.2 callee σr envA σ' v hR).1 hwc
        refine stmtZiel_ok_G (A := []) (s₁ := s) hex
          (Strecke_G.schritt (s₁ := s) (fun ρB hF => ?_) (fun w => Int.le_refl _)) hW' hL
        have hstay : ∀ t, (ρB cname t).1.world = t.world := by
          intro t
          funext p
          exact hF cname callee hcc hfs t p (by rw [hwc]; simp)
        rw [hstep ρB, hstay]
      | cons w ws =>
        -- a writer: one entry, its ghost bumped
        let t : Gabbro.Body.State := ⟨s.world, Gabbro.Body.bindAll
          ((fnAt u callee).params.map (·.1)) (envVals envA) (fun _ => .absent)⟩
        let e0 : Eintrag := ⟨cname, t, antwort w σ' t (ergValOf ((declOf u).erg callee) v)⟩
        let s₁ : Gabbro.Body.State := ⟨bump w (encG u σ' s.world), s.local'⟩
        have hW₁ : WGRel u σ' s₁.world := wgrel_bump w (wgrel_enc u σ' s.world)
        have hgeist : geistVon u cname = some w := by
          simp [geistVon, hfs, hwc]
        have hgz1 : gz w s₁.world = gz w s.world + 1 := by
          show gz w (bump w (encG u σ' s.world)) = _
          rw [gz_bump_self, gz_enc]
        have hS : Strecke_G u C [e0] s s₁ [bB] :=
          { gut := fun e he => by
              rcases List.mem_singleton.mp he with rfl
              exact eintrag_gut_teil G S R hRR callee hcc σr σ' envA v hR t hWr hLt w ws hwc cname hfs
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
              have := gz_bump_le w w' (encG u σ' s.world)
              rw [gz_enc] at this
              exact this
            lauf := fun ρB hT hF => by
              have he0 : ρB cname t = e0.aus := hT e0 (List.mem_singleton_self _)
              have hs : Gabbro.Body.step ρB bB s = .running s₁ := by
                rw [hstep ρB, he0] <;> rfl
              simp only [Gabbro.Body.exec, hs] }
        exact stmtZiel_ok_G hex hS hW₁ hL
    · exact ⟨fun e' h => (by rw [hex] at h; cases h; exact ⟨callee, σr, envA, hcc, hR⟩),
        fun σ' v h => (by rw [hex] at h; cases h), fun σ' ρ' h => (by rw [hex] at h; cases h)⟩
    · exact ⟨fun e' h => (by rw [hex] at h; cases h), fun σ' v h => (by rw [hex] at h; cases h),
        fun σ' ρ' h => (by rw [hex] at h; cases h)⟩
  all_goals simp [LeseEinzeln] at hs

theorem stmtZiel_ret_G {loopMode : Bool} (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {ns : BodyNames} {Λ : List (Res (declOf u))}
    {r : URet} {st : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ} {bst : Gabbro.Body.Stmt}
    (h : lowRetStmt (l := loopMode) u c Γ fn Λ [] r = .ok st) (hb : retZ u fn ns r = some bst)
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    StmtZiel_G u C c O passes R fn ns.active st σ ρ s bst := by
  obtain ⟨σ', v, hex, hsl, hstep⟩ := lowRet_sim c h hb hU hT O passes R σ ρ s hW hL
  refine ⟨fun e h' => (by rw [hex] at h'; cases h'), fun σ'' v' h' => ?_,
    fun σ'' ρ'' h' => (by rw [hex] at h'; cases h')⟩
  rw [hex] at h'
  cases h'
  refine ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    List.Pairwise.nil, fun ρB _ _ => ⟨s, ?_, hsl⟩⟩
  simp only [Gabbro.Body.exec, hstep ρB]

theorem stmtZiel_ite_G {loopMode : Bool} (hT : TabEindeutig u) {c : Fin u.fns.length} {O : Orakel (declOf u)}
    {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {fn fT : UFn} {ns : BodyNames} {Λ Λ₁ : List (Res (declOf u))} {cnd : UEns}
    {cv : Expr (declOf u) Γ Λ .bool} {tb eb : Block (declOf u) (verOf u c) loopMode Γ Λ Λ₁}
    {ce : Gabbro.Body.Expr} {tt te : List Gabbro.Body.Stmt}
    (hU : UmfangB Γ fn ns) (hS : Sicht u fT fn) (hcv : lowEns u Γ Λ fn none cnd = .ok cv)
    (hce : condZ u fT ns cnd = some ce)
    (hBt : ∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
      BlockZiel_G u C c O passes R fn ns.active tb σ ρ s tt)
    (hBe : ∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
      BlockZiel_G u C c O passes R fn ns.active eb σ ρ s te)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    StmtZiel_G u C c O passes R fn ns.active (Stmt.ite cv tb eb) σ ρ s (.ite ce tt te) := by
  have hceN : condZ u fn ns cnd = some ce := (condZ_sicht hS ns cnd).symm.trans hce
  obtain ⟨raw, a, hens, hold, hres, hrename⟩ := condZ_some hceN
  have hWl : WGRel u (σ.lese Λ cv.orte) s.world := wgrel_same u rfl rfl hW
  have hvL := hL.visible (ns := ns)
  let sv : Gabbro.Body.State := ⟨s.world, ns.visible fn s.local'⟩
  have hB : EnsBind fn none ρ sv a sv.local' :=
    ⟨hvL, fun hr => (by rw [hres] at hr; cases hr),
      fun i hi => (by rw [hold] at hi; exact absurd hi (Nat.not_lt_zero _))⟩
  have hraw := lowEns_sim (er := none) hU.art hT (σ.lese Λ cv.orte) (σ.lese Λ cv.orte)
    ρ sv s.world sv.local' a hWl hvL hWl hB cnd hens hcv (Vor.refl a)
  change Gabbro.Body.eval ⟨s.world, visibleBinding (ns.lookup fn) s.local'⟩ raw =
    some (.bool (wahr? (eval (σ.lese Λ cv.orte) cv (σ.lese Λ cv.orte) ρ))) at hraw
  have hcond : Gabbro.Body.eval s ce =
      some (.bool (wahr? (eval (σ.lese Λ cv.orte) cv (σ.lese Λ cv.orte) ρ))) :=
    (eval_renameScalar (ns.lookup fn) s raw ce hrename).trans hraw
  cases hb : wahr? (eval (σ.lese Λ cv.orte) cv (σ.lese Λ cv.orte) ρ) with
  | true =>
    rw [hb] at hcond
    have hG : execStmt O passes R (Stmt.ite cv tb eb) σ ρ =
        execBlock O passes R tb (σ.lese Λ cv.orte) ρ := by
      rw [execStmtZ_ite, hb]
      try exact if_pos rfl
    exact stmtZiel_of_G hG (fun ρB => step_ite_wahr ρB hcond) (hBt _ ρ s hWl hL)
  | false =>
    rw [hb] at hcond
    have hG : execStmt O passes R (Stmt.ite cv tb eb) σ ρ =
        execBlock O passes R eb (σ.lese Λ cv.orte) ρ := by
      rw [execStmtZ_ite, hb]
      try exact if_neg Bool.false_ne_true
    exact stmtZiel_of_G hG (fun ρB => step_ite_falsch ρB hcond) (hBe _ ρ s hWl hL)

end Gabbro.Bruecke
