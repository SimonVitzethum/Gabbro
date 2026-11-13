module
public import Bruecke.Teil.Realisierung
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- Only frames of carried targets are required by a carried Body execution. -/
def RahmenAlleC (u : UProg) (C : Fin u.fns.length → Prop) (ρB : Gabbro.Body.Env) : Prop :=
  ∀ n c, C c → fnSuch u n = some (fnAt u c) → Gabbro.Body.Frame ρB n (fnAt u c).puts

theorem reqAmEintritt_wahr_teil {P : Programm (declOf u)} (G : GesenktC u C P)
    (f : Fin u.fns.length) (hf : C f) (σ : World (declOf u))
    (ρ : Env (declOf u) ((declOf u).params f)) : ReqAmEintritt P f σ ρ := by
  unfold ReqAmEintritt
  rw [G.req f hf]
  rfl

theorem eintrag_gut_teil {P : Programm (declOf u)} (G : GesenktC u C P) (S : Getragen u C)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) (callee : Fin u.fns.length) (hc : C callee) (σr σ' : World (declOf u))
    (envA : Env (declOf u) ((declOf u).params callee)) (v : ErgVal (declOf u) ((declOf u).erg callee))
    (hR : R callee σr envA = .ok σ' v) (t : Gabbro.Body.State) (hWt : WRel u σr t.world)
    (hLt : LRel (fnAt u callee) 0 envA t.local') (w : String) (ws : List String)
    (hw : (fnAt u callee).puts = w :: ws) (n : String) (hn : fnSuch u n = some (fnAt u callee)) :
    EintragGut u ⟨n, t, antwort w σ' t (ergValOf ((declOf u).erg callee) v)⟩ := by
  intro gf hgf
  rw [hn] at hgf
  cases hgf
  constructor
  · intro _
    have hens := hRR.1 callee σr envA (reqAmEintritt_wahr_teil G callee hc σr envA) σ' v hR
    exact (post_iff_teil G callee hc (S.art callee hc) S.tab (S.frei callee hc) (S.olds callee hc) (S.post callee hc)
      (S.boolErg callee hc) S.boolTab σr σ' envA v t _ hWt hLt (wrel_bump w (wrel_enc u σ' t.world))).mpr hens
  · intro p hp
    have hgp : p ≠ geistOrt w := by
      intro e; subst e; apply hp; simp [geistOrt, Gabbro.Body.Place.carrier, hw]
    simp only [antwort, bump, Gabbro.Body.store, hgp, ↓reduceIte]
    cases p with
    | slot c k fld =>
      simp only [enc]
      cases hsw : slotWert u σ' c k fld with
      | none => rfl
      | some val =>
        simp only [Option.getD_some]
        unfold slotWert at hsw
        split at hsw
        · rename_i t' ht'
          split at hsw
          · rename_i fh' hf'
            cases hsw
            rw [wrel_lies_k u hWt c t' ht' fld fh' hf' k]
            congr 1
            have hfr := (hRR.2 callee σr envA σ' v hR).1.1 t'
            have hwf : (declOf u).schreibt callee t' = false := by
              show ((declOf u).signatur callee).schreibt t' = false
              rw [sigSchreibt_eq]
              unfold writesAt
              rw [show (tabAt u t').name = c from tabIdx_name _ _ _ ht']
              simp only [Gabbro.Body.Place.carrier] at hp
              simp only [List.any_eq_false, beq_iff_eq]
              intro x hx e
              subst e
              exact hp hx
            exact hfr hwf k fh'.idx
          · cases hsw
        · cases hsw
    | field c n => rfl
    | global n => rfl

theorem lauf_teil {P : Programm (declOf u)} (G : GesenktC u C P) (S : Getragen u C) (c : Fin u.fns.length) (hc : C c)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) (r : URet) (eB : List Gabbro.Body.Stmt)
    (hr : endBody u (fnAt u c) r = some eB) :
    ∀ (ss : List UStmt) {Λ : List (Res (declOf u))}
      (b0 : Endblock (declOf u) (verOf u c) false (ctxOf u c) Λ)
      (bs : List Gabbro.Body.Stmt),
      (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      lowBodyAt u c Λ ss r = .ok b0 → stmtsBody u (fnAt u c) ss = some bs →
      ∀ (σ : World (declOf u)) (ρ : Env (declOf u) (ctxOf u c)) (s : Gabbro.Body.State),
        WRel u σ s.world → LRel (fnAt u c) 0 ρ s.local' →
        (∀ e, execEnd O passes R b0 σ ρ = .logik e →
          ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)), C g ∧ R g σr envA = .logik e) ∧
        (∀ σ' v, execEnd O passes R b0 σ ρ = .zurueck σ' v →
          ∃ A : List Eintrag, (∀ e ∈ A, EintragGut u e) ∧ Oben u A s.world ∧ Schluessel A ∧
            ∀ ρB, Treu A ρB → RahmenAlleC u C ρB →
              ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB (bs ++ eB) s) = some s' ∧
                Gabbro.Body.finalValue (Gabbro.Body.exec ρB (bs ++ eB) s) =
                  ergValOf (verOf u c).erg v ∧
                WRel u σ' s'.world)
  | [], Λ, b0, bs, _, hlow, hbs, σ, ρ, s, hW, hL => by
      simp only [stmtsBody, Option.some.injEq] at hbs
      subst hbs
      simp only [lowBodyAt, List.length_nil, lowBodyF] at hlow
      obtain ⟨σ', v, hex, hsl, hB⟩ := lowEnd_sim c hlow hr (S.art c hc) S.tab O passes R σ ρ s hW hL
      refine ⟨fun e h => (by rw [hex] at h; cases h), fun σ'' v' h => ?_⟩
      rw [hex] at h
      cases h
      refine ⟨[], by simp, by simp [Oben], List.Pairwise.nil, fun ρB _ _ =>
        ⟨s, (hB ρB).1, (hB ρB).2, wrel_slots u hsl hW⟩⟩
  | st :: ss, Λ, b0, bs, hmem, hlow, hbs, σ, ρ, s, hW, hL => by
      obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
        lowBody_cons_ok c r st ss (stmtsBody_isSome hbs st List.mem_cons_self) hlow
      simp only [stmtsBody] at hbs
      split at hbs
      · rename_i x xs hx hxs
        simp only [Option.some.injEq] at hbs
        subst hbs
        have IH := lauf_teil G S c hc O passes R hRR r eB hr ss rest xs
          (fun st' hm => hmem st' (List.mem_cons_of_mem _ hm)) hrest hxs
        -- a slot write: both sides take one step to related states
        have schreib : ∀ (σ₁ : World (declOf u)) (cn : String) (k : Int) (fld : String)
            (val : Gabbro.Body.Value), execStmt O passes R gst σ ρ = .ok σ₁ ρ →
            (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB x s =
              .running ⟨Gabbro.Body.store s.world (.slot cn k fld) val, s.local'⟩) →
            WRel u σ₁ (Gabbro.Body.store s.world (.slot cn k fld) val) →
            ((∀ e, execEnd O passes R (Endblock.cons gst rest) σ ρ = .logik e →
              ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)), C g ∧ R g σr envA = .logik e) ∧
            (∀ σ' v, execEnd O passes R (Endblock.cons gst rest) σ ρ = .zurueck σ' v →
              ∃ A : List Eintrag, (∀ e ∈ A, EintragGut u e) ∧ Oben u A s.world ∧ Schluessel A ∧
                ∀ ρB, Treu A ρB → RahmenAlleC u C ρB →
                  ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB (x :: xs ++ eB) s) = some s' ∧
                    Gabbro.Body.finalValue (Gabbro.Body.exec ρB (x :: xs ++ eB) s) =
                      ergValOf (verOf u c).erg v ∧
                    WRel u σ' s'.world)) := by
          intro σ₁ cn k fld val hex hstep hW₁
          have ih := IH σ₁ ρ ⟨Gabbro.Body.store s.world (.slot cn k fld) val, s.local'⟩ hW₁ hL
          have hrun : execEnd O passes R (Endblock.cons gst rest) σ ρ =
              execEnd O passes R rest σ₁ ρ := by
            simp only [execEnd, hex]
          rw [hrun]
          refine ⟨ih.1, fun σ' v h => ?_⟩
          obtain ⟨A, hg, ho, hk, hb⟩ := ih.2 σ' v h
          refine ⟨A, hg, oben_mono (fun w => by rw [gz_store_slot]; exact Int.le_refl _) ho, hk,
            fun ρB hT hF => ?_⟩
          obtain ⟨s', h1, h2, h3⟩ := hb ρB hT hF
          refine ⟨s', ?_, ?_, h3⟩
          · simp only [List.cons_append, Gabbro.Body.exec, hstep ρB]; exact h1
          · simp only [List.cons_append, Gabbro.Body.exec, hstep ρB]; exact h2
        cases st
        case assign b fname ix val =>
          rw [lowStmt_assign S.tab c b fname ix val (Λ := Λ)] at hgst
          cases stored : lowAssignDurch u c b fname ix val (Λ := Λ) with
          | error error => simp only [stored, Except.map] at hgst; cases hgst
          | ok statement =>
            simp only [stored, Except.map] at hgst
            cases hgst
            obtain ⟨σ₁, cn, k, fld, v', hex, hstep, hW₁, _⟩ :=
              lowAssignDurch_sim c stored hx (S.art c hc) S.tab O passes R σ ρ s hW hL
            exact schreib σ₁ cn k fld v' hex hstep hW₁
        case assignTab b fname ix val =>
          rw [lowStmt_assignTab S.tab c b fname ix val (Λ := Λ)] at hgst
          cases stored : lowAssignTab u c b fname ix val (Λ := Λ) with
          | error error => simp only [stored, Except.map] at hgst; cases hgst
          | ok statement =>
            simp only [stored, Except.map] at hgst
            cases hgst
            obtain ⟨σ₁, cn, k, fld, v', hex, hstep, hW₁, _⟩ :=
              lowAssignTab_sim c stored hx (S.art c hc) S.tab O passes R σ ρ s hW hL
            exact schreib σ₁ cn k fld v' hex hstep hW₁
        case call cname args =>
          rw [lowStmt_call (u := u) c cname args (Λ := Λ)] at hgst
          obtain ⟨callee, σr, envA, hname, hfs, hsl, hstep, hLt, _, hcases, _⟩ :=
            lowCall_sim_teil c hgst hx (S.art c hc) S.tab (S.namen c hc)
              (fun d hd => by
                have hdC := callee_getragen_teil S hc (hmem _ (List.mem_cons_self ..)) hd
                exact ⟨S.namen d hdC, (S.art d hdC).2.1⟩) O passes R σ ρ s hW hL
          have hcc : C callee := callee_getragen_teil S hc (hmem _ (List.mem_cons_self ..)) hfs
          have hWr : WRel u σr s.world := wrel_slots u hsl hW
          rcases hcases with ⟨σ', v, hR, hex⟩ | ⟨e, hR, hex⟩ | ⟨e, hR, hex⟩
          · have hrun : execEnd O passes R (Endblock.cons gst rest) σ ρ =
                execEnd O passes R rest σ' ρ := by
              simp only [execEnd, hex]
            rw [hrun]
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
              have ih := IH σ' ρ s (wrel_slots u hsl' hW) hL
              refine ⟨ih.1, fun σ'' v' h => ?_⟩
              obtain ⟨A, hg, ho, hk, hb⟩ := ih.2 σ'' v' h
              refine ⟨A, hg, ho, hk, fun ρB hT hF => ?_⟩
              have hstay : ∀ t, (ρB cname t).1.world = t.world := by
                intro t
                funext p
                exact hF cname callee hcc hfs t p (by rw [hwc]; simp)
              have hs : Gabbro.Body.step ρB x s = .running s := by
                rw [hstep ρB, hstay]
              obtain ⟨s', h1, h2, h3⟩ := hb ρB hT hF
              refine ⟨s', ?_, ?_, h3⟩
              · simp only [List.cons_append, Gabbro.Body.exec, hs]; exact h1
              · simp only [List.cons_append, Gabbro.Body.exec, hs]; exact h2
            | cons w ws =>
              -- a writer: one entry, its ghost bumped
              let t : Gabbro.Body.State := ⟨s.world, Gabbro.Body.bindAll
                ((fnAt u callee).params.map (·.1)) (envVals envA) (fun _ => .absent)⟩
              let e0 : Eintrag := ⟨cname, t, antwort w σ' t (ergValOf ((declOf u).erg callee) v)⟩
              let s₁ : Gabbro.Body.State := ⟨bump w (enc u σ' s.world), s.local'⟩
              have hW₁ : WRel u σ' s₁.world := wrel_bump w (wrel_enc u σ' s.world)
              have ih := IH σ' ρ s₁ hW₁ hL
              refine ⟨ih.1, fun σ'' v' h => ?_⟩
              obtain ⟨A, hg, ho, hk, hb⟩ := ih.2 σ'' v' h
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
                have hs : Gabbro.Body.step ρB x s = .running s₁ := by
                  rw [hstep ρB, he0]; rfl
                obtain ⟨s', h1, h2, h3⟩ := hb ρB (fun e he => hT e (List.mem_cons_of_mem _ he)) hF
                refine ⟨s', ?_, ?_, h3⟩
                · simp only [List.cons_append, Gabbro.Body.exec, hs]; exact h1
                · simp only [List.cons_append, Gabbro.Body.exec, hs]; exact h2
          · have hrun : execEnd O passes R (Endblock.cons gst rest) σ ρ = .logik e := by
              simp only [execEnd, hex]
            rw [hrun]
            exact ⟨fun e' h => ⟨callee, σr, envA, hcc, by cases h; exact hR⟩,
              fun σ' v h => by cases h⟩
          · have hrun : execEnd O passes R (Endblock.cons gst rest) σ ρ = .hardware e := by
              simp only [execEnd, hex]
            rw [hrun]
            exact ⟨fun e' h => (by cases h), fun σ' v h => (by cases h)⟩
        all_goals simp [stmtBody] at hx
      · cases hbs

end Gabbro.Bruecke
