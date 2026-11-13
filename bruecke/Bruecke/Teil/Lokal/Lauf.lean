module
public import Bruecke.Teil.Lokal.Kopf
public import Bruecke.Anweisung.Lokal.Lauf
@[expose] public section

/-! Binding-aware run simulation restricted to the carried call-closed set. -/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- **The run of a lowered body with local bindings.** From related states in a scope the body
    reader reached, with fresh binders: the G run never blames a caller's `requires`, and where it
    returns there is an answer table under which the Body run of `stmtsBodyB` ends in a related
    state with the same answer. -/
theorem lauf_teilB {P : Programm (declOf u)} (G : GesenktC u C P) (S : Getragen u C) (c : Fin u.fns.length) (hc : C c)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) (r : URet) :
    ∀ (n : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) {Λ : List (Res (declOf u))}
      (b0 : Endblock (declOf u) (verOf u c) false Γ Λ) (bs : List Gabbro.Body.Stmt),
      UmfangB Γ fn → Sicht u fT fn →
      (∀ st ∈ ss, st ∈ (fnAt u c).body) → BindFrischL (fn.params.map (·.1)) ss →
      lowBodyF u c Γ fn n Λ ss r = .ok b0 → stmtsBodyB u fT ss r = some bs →
      ∀ (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State),
        WRel u σ s.world → LRel fn 0 ρ s.local' →
        LaufZielTeilB u C c O passes R b0 σ ρ s bs
  | 0, ss, Γ, fn, fT, Λ, b0, bs, hU, hS, hmem, hF, hlow, hbs, σ, ρ, s, hW, hL => by
      simp only [lowBodyF] at hlow <;> cases hlow
  | n + 1, [], Γ, fn, fT, Λ, b0, bs, hU, hS, hmem, hF, hlow, hbs, σ, ρ, s, hW, hL => by
      simp only [lowBodyF] at hlow
      have heB : endBody u fn r = some bs := by
        rw [← endBody_sicht hS r]
        exact hbs
      obtain ⟨σ', v, hex, hsl, hB⟩ := lowEnd_simB c hlow heB hU S.tab O passes R σ ρ s hW hL
      refine ⟨fun e h => (by rw [hex] at h; cases h), fun σ'' v' h => ?_⟩
      rw [hex] at h
      cases h
      exact ⟨[], by simp, by simp [Oben], List.Pairwise.nil, fun ρB _ _ =>
        ⟨s, (hB ρB).1, (hB ρB).2, wrel_slots u hsl hW⟩⟩
  | n + 1, s0 :: ss, Γ, fn, fT, Λ, b0, bs, hU, hS, hmem, hF, hlow, hbs, σ, ρ, s, hW, hL => by
      obtain ⟨bB, fT', bs', hstep0, hbs', rfl⟩ := stmtsBodyB_cons hbs
      have hmemss : ∀ st ∈ ss, st ∈ (fnAt u c).body :=
        fun st hm => hmem st (List.mem_cons_of_mem _ hm)
      have hhead : s0 ∈ (fnAt u c).body := hmem s0 (List.mem_cons_self ..)
      cases s0
      case bind x d v =>
        obtain ⟨eT, heT, rfl, rfl⟩ := schrittB_bind hstep0
        obtain ⟨hx, hF'⟩ := bindFrischL_bind hF
        obtain ⟨ls, rest, hls, hrest, rfl⟩ := lowBodyF_bind_ok c hlow
        have heB : sideExpr u fn v = some eT := (sideExpr_sicht hS v).symm.trans heT
        obtain ⟨bv, hstep, hWl, hL'⟩ := lowBind_sim (x := x) hls heB hU S.tab σ ρ s hW hL
        have IH := lauf_teilB G S c hc O passes R hRR r n ss (fn.mitBindung x ls.range)
          (fT.mitBindung x (0, 0)) rest bs' (hU.bind hx ls.range) (hS.bind x (0, 0) ls.range)
          hmemss (by rw [mitBindung_namen]; exact hF') hrest hbs' _ _
          ⟨s.world, Gabbro.Body.bindLocal s.local' x bv⟩ hWl hL'
        exact laufZiel_schritt_teilB (bind_lauf O passes R ls.term rest σ ρ) (fun ρB _ => hstep ρB)
          (fun w => Int.le_refl _) IH
      case bindMut x lo hi v =>
        obtain ⟨eT, heT, rfl, rfl⟩ := schrittB_bindMut hstep0
        obtain ⟨hx, hF'⟩ := bindFrischL_bindMut hF
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindMut_ok c hlow
        have heB : sideExpr u fn v = some eT := (sideExpr_sicht hS v).symm.trans heT
        obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindMut_sim (x := x) hev heB hU S.tab σ ρ s hW hL
        have hU' : UmfangB (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) := hU.bind hx (lo, hi)
        have IH := lauf_teilB G S c hc O passes R hRR r n ss (fn.mitBindung x (lo, hi))
          (fT.mitBindung x (lo, hi)) rest bs' hU' (hS.bind x (lo, hi) (lo, hi))
          hmemss (by rw [mitBindung_namen]; exact hF') hrest hbs' _ _
          ⟨s.world, Gabbro.Body.bindLocal s.local' x bv⟩ hWl hL'
        exact laufZiel_schritt_teilB (bind_lauf O passes R ev rest σ ρ) (fun ρB _ => hstep ρB)
          (fun w => Int.le_refl _) IH
      case setVar x v =>
        obtain ⟨hnT, eT, heT, rfl, rfl⟩ := schrittB_setVar hstep0
        have hF' := bindFrischL_sonst (s := .setVar x v) rfl hF
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r (.setVar x v) ss trivial hlow
        simp only [lowStmtL] at hgst
        cases hsv : lowSetVarL (l := false) u c Γ fn Λ x v with
        | error err => simp only [hsv, Except.map] at hgst <;> cases hgst
        | ok st0 =>
          simp only [hsv, Except.map] at hgst
          cases hgst
          have hn : numericParam fn x = true := (hS.1 x).symm.trans hnT
          have heB : sideExpr u fn v = some eT := (sideExpr_sicht hS v).symm.trans heT
          obtain ⟨σ₁, ρ₁, bv, hex, hsl, hstep, hL'⟩ :=
            lowSetVar_sim c hsv hn heB hU S.tab O passes R σ ρ s hW hL
          have IH := lauf_teilB G S c hc O passes R hRR r n ss fn _ rest bs' hU hS hmemss hF' hrest hbs'
            σ₁ ρ₁ ⟨s.world, Gabbro.Body.bindLocal s.local' x bv⟩ (wrel_slots u hsl hW) hL'
          exact laufZiel_schritt_teilB (cons_lauf O passes R _ rest σ σ₁ ρ ρ₁ hex)
            (fun ρB _ => hstep ρB) (fun w => Int.le_refl _) IH
      case assign b' f i v =>
        obtain ⟨hxT, rfl⟩ := schrittB_stmt hstep0 (fun _ _ _ h => by cases h)
          (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
        have hx : stmtBody u fn (.assign b' f i v) = some bB :=
          (stmtBody_sicht hS _).symm.trans hxT
        have hF' := bindFrischL_sonst (s := .assign b' f i v) rfl hF
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r (.assign b' f i v) ss trivial hlow
        rw [lowStmtL_assign S.tab c Γ fn Λ b' f i v] at hgst
        cases stored : lowAssignDurchL (l := false) u c Γ fn Λ b' f i v with
        | error err => simp only [stored, Except.map] at hgst <;> cases hgst
        | ok statement =>
          simp only [stored, Except.map] at hgst
          cases hgst
          obtain ⟨σ₁, cn, k, fld, val, hex, hstep, hW₁, _⟩ :=
            lowAssignDurch_simB c stored hx hU S.tab O passes R σ ρ s hW hL
          have IH := lauf_teilB G S c hc O passes R hRR r n ss fn _ rest bs' hU hS hmemss hF' hrest hbs'
            σ₁ ρ ⟨Gabbro.Body.store s.world (.slot cn k fld) val, s.local'⟩ hW₁ hL
          exact laufZiel_schritt_teilB (cons_lauf O passes R _ rest σ σ₁ ρ ρ hex)
            (fun ρB _ => hstep ρB)
            (fun w => Int.le_of_eq (gz_store_slot w cn k fld s.world val).symm) IH
      case assignTab b' f i v =>
        obtain ⟨hxT, rfl⟩ := schrittB_stmt hstep0 (fun _ _ _ h => by cases h)
          (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
        have hx : stmtBody u fn (.assignTab b' f i v) = some bB :=
          (stmtBody_sicht hS _).symm.trans hxT
        have hF' := bindFrischL_sonst (s := .assignTab b' f i v) rfl hF
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r (.assignTab b' f i v) ss trivial hlow
        rw [lowStmtL_assignTab S.tab c Γ fn Λ b' f i v] at hgst
        cases stored : lowAssignTabL (l := false) u c Γ fn Λ b' f i v with
        | error err => simp only [stored, Except.map] at hgst <;> cases hgst
        | ok statement =>
          simp only [stored, Except.map] at hgst
          cases hgst
          obtain ⟨σ₁, cn, k, fld, val, hex, hstep, hW₁, _⟩ :=
            lowAssignTab_simB c stored hx hU S.tab O passes R σ ρ s hW hL
          have IH := lauf_teilB G S c hc O passes R hRR r n ss fn _ rest bs' hU hS hmemss hF' hrest hbs'
            σ₁ ρ ⟨Gabbro.Body.store s.world (.slot cn k fld) val, s.local'⟩ hW₁ hL
          exact laufZiel_schritt_teilB (cons_lauf O passes R _ rest σ σ₁ ρ ρ hex)
            (fun ρB _ => hstep ρB)
            (fun w => Int.le_of_eq (gz_store_slot w cn k fld s.world val).symm) IH
      case call cname args =>
        obtain ⟨hxT, rfl⟩ := schrittB_stmt hstep0 (fun _ _ _ h => by cases h)
          (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
        have hx : stmtBody u fn (.call cname args) = some bB :=
          (stmtBody_sicht hS _).symm.trans hxT
        have hF' := bindFrischL_sonst (s := .call cname args) rfl hF
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r (.call cname args) ss trivial hlow
        have hgst' : lowCallL (l := false) u c Γ fn Λ cname args = .ok ⟨Λ', gst⟩ := hgst
        obtain ⟨callee, σr, envA, hname, hfs, hsl, hstep, hLt, _, hcases, _⟩ :=
          lowCall_sim_teilB c hgst' hx hU S.tab
            (fun d hd => by
              have hdC := callee_getragen_teil S hc hhead hd
              exact ⟨S.namen d hdC, (S.art d hdC).2.1⟩) O passes R σ ρ s hW hL
        have hcc : C callee := callee_getragen_teil S hc hhead hfs
        have hWr : WRel u σr s.world := wrel_slots u hsl hW
        rcases hcases with ⟨σ', v, hR, hex⟩ | ⟨e, hR, hex⟩ | ⟨e, hR, hex⟩
        · have hrun := cons_lauf O passes R gst rest σ σ' ρ ρ hex
          have hfr := (hRR.2 callee σr envA σ' v hR).1.1
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
            have IH := lauf_teilB G S c hc O passes R hRR r n ss fn _ rest bs' hU hS hmemss hF' hrest hbs'
              σ' ρ s (wrel_slots u hsl' hW) hL
            refine laufZiel_schritt_teilB hrun (fun ρB hF => ?_) (fun w => Int.le_refl _) IH
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
            let s₁ : Gabbro.Body.State := ⟨bump w (enc u σ' s.world), s.local'⟩
            have hW₁ : WRel u σ' s₁.world := wrel_bump w (wrel_enc u σ' s.world)
            have ih := lauf_teilB G S c hc O passes R hRR r n ss fn _ rest bs' hU hS hmemss hF' hrest hbs'
              σ' ρ s₁ hW₁ hL
            refine ⟨fun e h => ih.1 e (hrun.1 e h), fun σ'' v' h => ?_⟩
            obtain ⟨A, hg, ho, hk, hb⟩ := ih.2 σ'' v' (hrun.2 σ'' v' h)
            have hgeist : geistVon u cname = some w := by
              simp [geistVon, hfs, hwc]
            have hgz : ∀ w', gz w' s.world ≤ gz w' s₁.world := fun w' => by
              have := gz_bump_le w w' (enc u σ' s.world)
              rw [gz_enc] at this
              exact this
            refine ⟨e0 :: A, ?_, ?_, ?_, fun ρB hT hF => ?_⟩
            · intro e he
              rcases List.mem_cons.mp he with rfl | he
              · exact eintrag_gut_teil G S R hRR callee hcc σr σ' envA v hR t hWr hLt w ws hwc cname hfs
              · exact hg e he
            · intro e he
              rcases List.mem_cons.mp he with rfl | he
              · exact ⟨w, hgeist, Int.le_refl _⟩
              · exact oben_mono hgz ho e he
            · refine List.Pairwise.cons (fun e he hkey => ?_) hk
              obtain ⟨w', hw', hle⟩ := ho e he
              rw [← hkey.1, hgeist] at hw'
              cases hw'
              have : gz w s₁.world = gz w s.world + 1 := by
                show gz w (bump w (enc u σ' s.world)) = _
                rw [gz_bump_self, gz_enc]
              rw [this, ← hkey.2] at hle
              exact absurd hle (by show ¬ (gz w s.world + 1 ≤ gz w s.world); omega)
            · have he0 : ρB cname t = e0.aus := hT e0 (List.mem_cons_self ..)
              have hs : Gabbro.Body.step ρB bB s = .running s₁ := by
                rw [hstep ρB, he0]; rfl
              obtain ⟨s', h1, h2, h3⟩ := hb ρB (fun e he => hT e (List.mem_cons_of_mem _ he)) hF
              refine ⟨s', ?_, ?_, h3⟩
              · rw [exec_cons_running ρB bB bs' s s₁ hs]; exact h1
              · rw [exec_cons_running ρB bB bs' s s₁ hs]; exact h2
        · have hrun : execEnd O passes R (Endblock.cons gst rest) σ ρ = .logik e := by
            simp only [execEnd, hex]
          refine ⟨fun e' h => ⟨callee, σr, envA, hcc, ?_⟩, fun σ' v h => ?_⟩
          · rw [hrun] at h
            cases h
            exact hR
          · rw [hrun] at h
            cases h
        · have hrun : execEnd O passes R (Endblock.cons gst rest) σ ρ = .hardware e := by
            simp only [execEnd, hex]
          refine ⟨fun e' h => ?_, fun σ' v h => ?_⟩
          · rw [hrun] at h
            cases h
          · rw [hrun] at h
            cases h
      all_goals simp [schrittB, stmtBody] at hstep0

end Gabbro.Bruecke
