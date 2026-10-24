import Grammatik.Bausteine.Arena.Ownership.Machine.Return

/-! **Every step of machine G keeps ownership.** One case per step rule:
the running activation's state moves by the step lemmas of this folder,
a call pushes (`ownInv_push`), a return pops (`ownInv_pop`); the one
assumption is the rely `pendWord` for the other threads. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

section Helpers

variable {A : FreiForm D} {I : Interfaces A} {fr : Frame} {s : State} {σ : World D} {f : D.Fn}

/-- A running activation outside every allocator form realises its context. -/
theorem head_run {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D f) l Γ Λ}
    (h : Head A I fr s σ f ⟨l, Γ, Λ, ρ, r⟩) (hp : pendWord A r = none) :
    ∃ k c g, k.references.length ≤ Γ.length ∧ FrameOk c g s fr ρ ∧ OR A I (I f).output k c r := by
  cases h with
  | run _ _ hk hf hr => exact ⟨_, _, _, hk, hf, hr⟩
  | list => simp [pendWord] at hp
  | counter => simp [pendWord] at hp
  | store => simp [pendWord] at hp
  | release => simp [pendWord] at hp

theorem meta_lese (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) {σ₁ : World D}
    (h : σ₁ = σ.lese Λ os) {A : FreiForm D} : MetaSame A σ σ₁ := by
  rw [h]; exact MetaSame.reads A σ Λ os

/-- **A leaf step of the running activation**, whatever its state. -/
theorem head_leaf {O : Orakel D} {passes : Nat} (hO : GutO O) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    {ρ : Env D Γ} {st : Stmt D (vertragVon D f) l Γ Λ Λ'} {rest : Block D (vertragVon D f) l Γ Λ' Λ''}
    {k : GRest D (vertragVon D f) l Γ Λ''} (h : Head A I fr s σ f ⟨l, Γ, Λ, ρ, .dann (.cons st rest) k⟩)
    (ha : s.agrees A σ) (ho : A.FreiOk σ) (hleaf : st.istBlatt = true) {σ' : World D} {ρ' : Env D Γ}
    (hstep : execStmt O passes keinRuf st σ ρ = .ok σ' ρ') :
    Next A I fr s σ σ' f ⟨l, Γ, Λ', ρ', .dann rest k⟩ :=
  match h, hstep with
  | .run _ _ hk hf hr, hstep => run_leaf hO hk hf ha ho hr hleaf hstep
  | .list x ρ0 e2 hw hL _ _ he2 hx hlt hk hf hr, hstep => list_step x ρ0 e2 hw hL he2 hx hlt hk hf hr ha ho hstep
  | .counter x ρ0 e2 hw hL _ _ he2 hx _ hk hf hr, hstep => counter_step x ρ0 e2 hw hL he2 hx hk hf hr ha ho hstep
  | .store x ρ0 t f' i ev hws hLs hn e2 hw hL b r he2 hx hlt hk hf hr, hstep =>
    store_step x ρ0 t f' i ev hws hLs hn e2 hw hL b r he2 hx hlt hk hf hr ha ho hstep
  | .release ρ0 e2 hw hL b r p o hh he2 hp ho' hg hlink hk hf hr, hstep =>
    release_step ρ0 e2 hw hL b r p o hh he2 hp ho' hg hlink hk hf hr ha ho hstep

theorem dropContextB_refs (c : Context) (owner : Bool) : (dropContextB c owner).references = c.references := by
  cases owner <;> simp [dropContextB, Context.bindFresh, Context.drop]

/-- The caller of the running activation, suspended on it. -/
theorem caller_susp {t : Faden} {g : D.Fn} {caller : RufRahmenG D} {rst : List (RufRahmenG D)}
    {stack : List (RufRahmenG D)} (h : StackOk A I s t g stack) (hpop : stack = caller :: rst) :
    Susp A I ⟨t, rst.length⟩ s g caller.f caller.rest := by
  subst hpop; exact h.1

/-- The callee of an indirect call at its entry. -/
theorem callee_ind {c : Context} {gh : Ghost} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ} {n : Nat}
    {J : Modes (D.sigNr n).params} {args : Args D Γ Λ (D.sigNr n).params} {g : D.Fn} (hg : D.passt g n = true)
    (hJ : modeList (I g).parameters = modeList J) {depth : Nat → Nat} {t a : Nat}
    (hd : s.Disciplined depth) (hdepth : depth t = a) (hR : Realizes c gh A ⟨t, a⟩ s σ ρ)
    (hp : planFits c (modeList J) (originList c args) = true) (σa σb : World D) :
    FrameOk (Flow.parameterContext (I g).parameters) (calleeGhost gh (modeList J) (originList c args) s.next)
      (s.handoff ⟨t, a + 1⟩ (movedHandles gh (modeList J) (originList c args))
        (lentHandles gh (modeList J) (originList c args))) ⟨t, a + 1⟩ (umsig hg (evalArgs σa args σb ρ)) := by
  have h := Push.callee_frame J args rfl rfl hd hdepth hR hp σa σb
  have hpc := parameterContext_eq (I g).parameters J hJ
  rw [hpc]
  exact ⟨h.1, References.transport (D.passt_sig hg).params.symm (umsig_heq hg _).symm h.2.1, h.2.2.1, h.2.2.2⟩

/-- **After a plain call**, whatever the shape of the caller's state. -/
theorem resume_plainX {depth : Nat → Nat} {t a : Nat} (hd : s.Disciplined depth) (hdepth : depth t = a + 1)
    {g f : D.Fn} {x : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D f) l Γ Λ}
    (hs : Susp A I ⟨t, a⟩ s g f x) (hw : x.2.2.2.2.wartend = false) (v : ErgVal D (D.erg g))
    (hres : (I g).output.result A ⟨t, a + 1⟩ s v) :
    Head A I ⟨t, a⟩ (s.pop ⟨t, a + 1⟩ ⟨t, a⟩) σ f x := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := x
  exact resume_plain hd hdepth hs hw v hres

/-- The checked return value of the running activation. -/
theorem ret_result {Γ : Ctx} {Λ : List (Res D)} {c : Context} {gh : Ghost} {ρ : Env D Γ}
    {e : ErgExpr D Γ Λ (vertragVon D f).erg} (hf : FrameOk c gh s fr ρ)
    (hcheck : (I f).output.check A c e = true) (σ0 σ1 : World D) :
    (I f).output.result A fr s (evalErg σ0 e σ1 ρ) :=
  Flow.Output.check_sound A c gh fr s (I f).output e σ0 σ1 ρ hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 hcheck

end Helpers

/-! ## The step -/

/-- **Every step of machine G keeps ownership on the machine**, given the rely for other threads. -/
theorem ownInv_step {P : Programm D} {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat}
    (hO : GutO O) (hc : Checked P A I) {M M' : RufMaschineG D} {u : Faden} (hinv : OwnInv A I M)
    (hrely : ∀ t, t ≠ u → ∀ g, pendWord A (M.faeden t).kopf.rest.2.2.2.2 = some g →
      M'.speicher.globs g = M.speicher.globs g)
    (hstep : RufSchrittG P O passes M u M') : OwnInv A I M' := by
  obtain ⟨s, hag, hfo, hd, hth⟩ := hinv
  have hW : MetaSame A (M.speicher.welt []) (M.weltVon u) := MetaSame.of_cells A rfl rfl (fun _ => rfl)
  have ha : s.agrees A (M.weltVon u) := State.agrees_meta hag hW
  have ho : A.FreiOk (M.weltVon u) := freiOk_meta hfo hW
  have hH : Head A I ⟨u, (M.faeden u).stapel.length⟩ s (M.weltVon u) (M.faeden u).kopf.f
      (M.faeden u).kopf.rest := (hth u).1.meta hW
  have fin : ∀ {M' : RufMaschineG D} {σ' : World D}
      {x' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ}
      {rho' : Env D (D.params (M.faeden u).kopf.f)} {s0' : World D} {spur' : List (Ereignis D)}
      {log' : List (RufEreignisF D)},
      Next A I ⟨u, (M.faeden u).stapel.length⟩ s (M.weltVon u) σ' (M.faeden u).kopf.f x' →
      M'.speicher = σ'.speicher →
      M'.faeden = rufUpdateG M.faeden u ⟨(M.faeden u).stapel, ⟨(M.faeden u).kopf.f, rho', s0', x'⟩, spur', log'⟩ →
      (∀ t, t ≠ u → ∀ g, pendWord A (M.faeden t).kopf.rest.2.2.2.2 = some g →
        M'.speicher.globs g = M.speicher.globs g) → OwnInv A I M' := by
    intro M' σ' x' rho' s0' spur' log' hn hmem hM' hr
    exact ownInv_local hag hfo hd hth hW (by rw [hmem]; exact welt_meta A σ') hr hM' hn
  cases hstep with
  | blatt l Γ Λ Λ' st rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    rw [hhead] at hH
    obtain ⟨k, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_leaf_ende hO hk hf ha ho hr hleaf hstep) rfl rfl hrely
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    obtain ⟨c2, hs, hcont⟩ := hor.stmtEnde
    obtain ⟨_, hplan, rfl⟩ := os_top hs
    subst hrho
    have hR : Realizes c gh A ⟨u, (M.faeden u).stapel.length⟩ s (M.speicher.welt []) ρ :=
      ⟨hag, hfo, hf.1, hf.2.1, hf.2.2.1⟩
    rw [dropContext_isOwner] at hcont
    exact ownInv_push hc hag hfo hd hth hf hplan hk
      (Push.callee_frame (I g).parameters args rfl rfl hd rfl hR hplan s0 s0)
      (.plain _ (cont_real hcont (by rw [dropContextB_refs]; exact hf.length))) rfl rfl
  | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    cases hor with
    | ende _ he =>
      cases he with
      | ret _ _ hcheck =>
        have hdu : depthOf M u = rst.length + 1 := by
          show (M.faeden u).stapel.length = _
          rw [hpop]; rfl
        have hsusp := caller_susp (hth u).2 hpop
        subst hfg
        subst hv
        have hres := ret_result hf hcheck s1 s1
        rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hres
        exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl (resume_plainX hd hdu hsusp hnw _ hres)
  | endeEntf l Γ Λ Λ' st rest ρ hent hhead =>
    rw [hhead] at hH
    obtain ⟨k, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_entf hk hf ha ho hr) rfl rfl hrely
  | endeForm l Γ Λ e ρ hl hent hhead =>
    rw [hhead] at hH
    obtain ⟨k, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_endeForm hk hf ha ho hr) rfl rfl hrely
  | dannBlatt l Γ Λ Λ' Λ'' st rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    rw [hhead] at hH
    exact fin (head_leaf hO hH ha ho hleaf hstep) rfl rfl hrely
  | dannLeer l Γ Λ k ρ hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_leer hk hf ha ho hr) rfl rfl hrely
  | dannIteWahr l Γ Λ Λ' Λ'' cnd t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_ite hk hf ha ho hr (meta_lese _ _ _ hs₁) true) (by subst hs₁; rfl) rfl hrely
  | dannIteFalsch l Γ Λ Λ' Λ'' cnd t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_ite hk hf ha ho hr (meta_lese _ _ _ hs₁) false) (by subst hs₁; rfl) rfl hrely
  | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_onOptionSome hk hf ha ho hr (meta_lese _ _ _ hs₁) v) (by subst hs₁; rfl) rfl hrely
  | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_onOptionNone hk hf ha ho hr (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_onTagSome hk hf ha ho hr (meta_lese _ _ _ hs₁) _ hw) (by subst hs₁; rfl) rfl hrely
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_onTagNone hk hf ha ho hr (meta_lese _ _ _ hs₁) _ hw) (by subst hs₁; rfl) rfl hrely
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    subst hw
    exact fin (run_onWhy hk hf ha ho hr (meta_lese _ _ _ hs₁) _) (by subst hs₁; rfl) rfl hrely
  | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    subst hs₁
    exact fin (run_bindEnde hk hf ha ho hr) rfl rfl hrely
  | endeBindAxiom l Γ Λ τ a args he hw hg hd' hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    subst hs₁
    exact fin (run_bindAxiomEnde hO hk hf ha ho hr hax _) rfl rfl hrely
  | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    subst hs₁
    exact fin (run_bind hk hf ha ho hr) rfl rfl hrely
  | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    subst hs₁
    exact fin (run_narrow hk hf ha ho hr h) rfl rfl hrely
  | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    subst hs₁
    exact fin (run_narrowElse hk hf ha ho hr) rfl rfl hrely
  | dannPruefWahr l Γ Λ Λ' Λ'' cnd sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_check hk hf ha ho hr (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely
  | dannPruefFalsch l Γ Λ Λ' Λ'' cnd sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_checkSonst hk hf ha ho hr (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely
  | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_breaking hk hf ha ho hr) rfl rfl hrely
  | dannLocks l Γ Λ Λ'' L hrk body rest k ρ hhead hself hrang hfrei =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_locks hk hf ha ho hr (MetaSame.refl A _)) rfl rfl hrely
  | freiGib l Γ Λ L k ρ hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_frei hk hf ha ho hr) rfl rfl hrely
  | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_schrumpf hf ha ho hr) rfl rfl hrely
  | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_traverse hk hf ha ho hr _) rfl rfl hrely
  | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_travNext hf ha ho hr (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely
  | travFort l Γ Λ t inv body is k i ρ hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_travFort hf ha ho hr) rfl rfl hrely
  | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_travDone hf ha ho hr (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely
  | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_retry hk hf ha ho hr) rfl rfl hrely
  | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_wiederUeber hf ha ho hr) rfl rfl hrely
  | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_wiederWeiter hf ha ho hr (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely
  | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_wiederSchritt hf ha ho hr (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely
  | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_wiederFort hf ha ho hr) rfl rfl hrely
  | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_forever hk hf ha ho hr _) rfl rfl hrely
  | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_ewigWeiter hf ha ho hr (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely
  | ewigFort l Γ Λ a n inv body k ρ hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_ewigFort hf ha ho hr) rfl rfl hrely
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    obtain ⟨c2, hs, hcont⟩ := hor.stmt trivial
    obtain ⟨_, hplan, rfl⟩ := os_top hs
    subst hrho
    have hR : Realizes c gh A ⟨u, (M.faeden u).stapel.length⟩ s (M.speicher.welt []) ρ :=
      ⟨hag, hfo, hf.1, hf.2.1, hf.2.2.1⟩
    rw [dropContext_isOwner] at hcont
    exact ownInv_push hc hag hfo hd hth hf hplan hk
      (Push.callee_frame (I g).parameters args rfl rfl hd rfl hR hplan s0 s0)
      (.plain _ (cont_real hcont (by rw [dropContextB_refs]; exact hf.length))) rfl rfl
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    obtain ⟨c2, hs, hcont⟩ := hor.stmt trivial
    obtain ⟨J, owner, hJ, _, _, hplan, rfl⟩ := os_top hs
    subst hrho
    have hR : Realizes c gh A ⟨u, (M.faeden u).stapel.length⟩ s (M.speicher.welt []) ρ :=
      ⟨hag, hfo, hf.1, hf.2.1, hf.2.2.1⟩
    obtain ⟨hJm, hJo⟩ := hJ g hg
    rw [← hJo] at hcont
    exact ownInv_push hc hag hfo hd hth hf hplan hk (callee_ind hg hJm hd rfl hR hplan s0 s0)
      (.plain _ (cont_real hcont (by rw [dropContextB_refs]; exact hf.length))) rfl rfl
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    obtain ⟨c2, hs, hcont⟩ := hor.stmtEnde
    obtain ⟨J, owner, hJ, _, _, hplan, rfl⟩ := os_top hs
    subst hrho
    have hR : Realizes c gh A ⟨u, (M.faeden u).stapel.length⟩ s (M.speicher.welt []) ρ :=
      ⟨hag, hfo, hf.1, hf.2.1, hf.2.2.1⟩
    obtain ⟨hJm, hJo⟩ := hJ g hg
    rw [← hJo] at hcont
    exact ownInv_push hc hag hfo hd hth hf hplan hk (callee_ind hg hJm hd rfl hR hplan s0 s0)
      (.plain _ (cont_real hcont (by rw [dropContextB_refs]; exact hf.length))) rfl rfl
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    obtain ⟨cout, hb, hcont⟩ := hor.dann_inv
    obtain ⟨_, hplan, c1, hrest, hdw⟩ := ob_top hb
    subst hrho
    have hR : Realizes c gh A ⟨u, (M.faeden u).stapel.length⟩ s (M.speicher.welt []) ρ :=
      ⟨hag, hfo, hf.1, hf.2.1, hf.2.2.1⟩
    have hor' := OR.binder hrest hdw hk hcont
    rw [resultContext_isOwner] at hor'
    exact ownInv_push hc hag hfo hd hth hf hplan hk
      (Push.callee_frame (I g).parameters args rfl rfl hd rfl hR hplan s0 s0) (.wartet _ _ hor') rfl rfl
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    obtain ⟨cout, hb, hcont⟩ := hor.dann_inv
    obtain ⟨J, owner, hJ, _, _, hplan, c1, hrest, hdw⟩ := ob_top hb
    subst hrho
    have hR : Realizes c gh A ⟨u, (M.faeden u).stapel.length⟩ s (M.speicher.welt []) ρ :=
      ⟨hag, hfo, hf.1, hf.2.1, hf.2.2.1⟩
    obtain ⟨hJm, hJo⟩ := hJ g hg
    have hor' := OR.binder hrest hdw hk hcont
    rw [← hJo] at hor'
    exact ownInv_push hc hag hfo hd hth hf hplan hk (callee_ind hg hJm hd rfl hR hplan s0 s0)
      (.wartet _ _ hor') rfl rfl
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    obtain ⟨cout, hb, hcont⟩ := hor.dann_inv
    obtain ⟨_, hplan, herr, c1, hrest, hdw⟩ := ob_top hb
    subst hrho
    have hR : Realizes c gh A ⟨u, (M.faeden u).stapel.length⟩ s (M.speicher.welt []) ρ :=
      ⟨hag, hfo, hf.1, hf.2.1, hf.2.2.1⟩
    have hor' := OR.binder hrest hdw hk hcont
    rw [resultContext_isOwner] at hor'
    exact ownInv_push hc hag hfo hd hth hf hplan hk
      (Push.callee_frame (I g).parameters args rfl rfl hd rfl hR hplan s0 s0)
      (.wartetSonst _ _ _ _ hor' (OR.sonst herr (.schrumpf _ hk hcont.exits))) rfl rfl
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1
      v hv he neu hneu =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    cases hor with
    | ende _ hee =>
      cases hee with
      | ret _ _ hcheck =>
        have hdu : depthOf M u = rst.length + 1 := by
          show (M.faeden u).stapel.length = _
          rw [hpop]; rfl
        have hsusp := caller_susp (hth u).2 hpop
        subst hfg
        subst hv
        have hres := ret_result hf hcheck s1 s1
        rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hres
        rcases hcaller with hc' | ⟨n, err, hc'⟩
        · rw [hc'] at hsusp
          exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl
            (resume_bind hd hdu hsusp (Or.inl rfl) _ he hres)
        · rw [hc'] at hsusp
          exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl
            (resume_bind hd hdu hsusp (Or.inr ⟨n, err, rfl⟩) _ he hres)
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw neu₁ hneu₁ hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    obtain ⟨hx, hX⟩ := exit_leave hr
    simp only [execStmt] at hstep
    cases hstep
    exact fin (run_leaveTrav hf ha ho hx hX (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    obtain ⟨hx, hX⟩ := exit_next hr
    simp only [execStmt] at hstep
    cases hstep
    exact fin (run_nextTrav hf ha ho hx hX (MetaSame.refl A _)) rfl rfl hrely
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    obtain ⟨hx, hX⟩ := exit_leave hr
    simp only [execStmt] at hstep
    cases hstep
    exact fin (run_leaveWieder hf ha ho hx hX (MetaSame.refl A _)) rfl rfl hrely
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    obtain ⟨hx, hX⟩ := exit_next hr
    simp only [execStmt] at hstep
    cases hstep
    exact fin (run_nextWieder hf ha ho hx hX (MetaSame.refl A _)) rfl rfl hrely
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    obtain ⟨hx, hX⟩ := exit_leave hr
    simp only [execStmt] at hstep
    cases hstep
    exact fin (run_leaveEwig hf ha ho hx hX (MetaSame.refl A _)) rfl rfl hrely
  | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    obtain ⟨hx, hX⟩ := exit_next hr
    simp only [execStmt] at hstep
    cases hstep
    exact fin (run_nextEwig hf ha ho hx hX (MetaSame.refl A _)) rfl rfl hrely
  | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    obtain ⟨hx, hX⟩ := exit_leave hr
    exact fin (run_peel hk hf ha ho (.leave hleave hx) (ox_top hX)) rfl rfl hrely
  | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    obtain ⟨hx, hX⟩ := exit_next hr
    exact fin (run_peel hk hf ha ho (.next hnext hx) (ox_top hX)) rfl rfl hrely
  | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    obtain ⟨hx, hX⟩ := exit_leave hr
    obtain ⟨hk', hX'⟩ := ox_top hX
    cases ρ with
    | cons v ρ0 =>
      exact fin (run_peelSchrumpf hk' hf ha ho (.leave hleave (exitsTo_shrink hf hx hk')) hX') rfl rfl hrely
  | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    obtain ⟨hx, hX⟩ := exit_next hr
    obtain ⟨hk', hX'⟩ := ox_top hX
    cases ρ with
    | cons v ρ0 =>
      exact fin (run_peelSchrumpf hk' hf ha ho (.next hnext (exitsTo_shrink hf hx hk')) hX') rfl rfl hrely
  | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    obtain ⟨hx, hX⟩ := exit_leave hr
    exact fin (run_peel hk hf ha ho (.leave hleave hx) (ox_top hX)) rfl rfl hrely
  | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    obtain ⟨hx, hX⟩ := exit_next hr
    exact fin (run_peel hk hf ha ho (.next hnext hx) (ox_top hX)) rfl rfl hrely
  | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    obtain ⟨hx, hX⟩ := exit_leave hr
    exact fin (run_peel hk hf ha ho (.leave hleave hx) (ox_top hX)) rfl rfl hrely
  | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    obtain ⟨hx, hX⟩ := exit_next hr
    exact fin (run_peel hk hf ha ho (.next hnext hx) (ox_top hX)) rfl rfl hrely
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv neu hneu hnw =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    obtain ⟨c2, hs, _⟩ := hor.stmt trivial
    have hcheck := os_top hs
    have hdu : depthOf M u = rst.length + 1 := by
      show (M.faeden u).stapel.length = _
      rw [hpop]; rfl
    have hsusp := caller_susp (hth u).2 hpop
    subst hfg
    subst hv
    have hres := ret_result hf hcheck s1 s1
    rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hres
    exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl (resume_plainX hd hdu hsusp hnw _ hres)
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    obtain ⟨c2, hs, _⟩ := hor.stmtEnde
    have hcheck := os_top hs
    have hdu : depthOf M u = rst.length + 1 := by
      show (M.faeden u).stapel.length = _
      rw [hpop]; rfl
    have hsusp := caller_susp (hth u).2 hpop
    subst hfg
    subst hv
    have hres := ret_result hf hcheck s1 s1
    rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hres
    exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl (resume_plainX hd hdu hsusp hnw _ hres)
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ s1 hs1
      g hfg rho hrho s0 hs0 v hv he neu hneu =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    obtain ⟨c2, hs, _⟩ := hor.stmt trivial
    have hcheck := os_top hs
    have hdu : depthOf M u = rst.length + 1 := by
      show (M.faeden u).stapel.length = _
      rw [hpop]; rfl
    have hsusp := caller_susp (hth u).2 hpop
    subst hfg
    subst hv
    have hres := ret_result hf hcheck s1 s1
    rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hres
    rcases hcaller with hc' | ⟨n, err, hc'⟩
    · rw [hc'] at hsusp
      exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl
        (resume_bind hd hdu hsusp (Or.inl rfl) _ he hres)
    · rw [hc'] at hsusp
      exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl
        (resume_bind hd hdu hsusp (Or.inr ⟨n, err, rfl⟩) _ he hres)
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ s1 hs1
      g hfg rho hrho s0 hs0 v hv he neu hneu =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    obtain ⟨c2, hs, _⟩ := hor.stmtEnde
    have hcheck := os_top hs
    have hdu : depthOf M u = rst.length + 1 := by
      show (M.faeden u).stapel.length = _
      rw [hpop]; rfl
    have hsusp := caller_susp (hth u).2 hpop
    subst hfg
    subst hv
    have hres := ret_result hf hcheck s1 s1
    rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hres
    rcases hcaller with hc' | ⟨n, err, hc'⟩
    · rw [hc'] at hsusp
      exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl
        (resume_bind hd hdu hsusp (Or.inl rfl) _ he hres)
    · rw [hc'] at hsusp
      exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl
        (resume_bind hd hdu hsusp (Or.inr ⟨n, err, rfl⟩) _ he hres)
  | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0
      rg hrg hn =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    cases hor with
    | ende _ hee =>
      cases hee with
      | retWhy _ _ hfin =>
        have hdu : depthOf M u = rst.length + 1 := by
          show (M.faeden u).stapel.length = _
          rw [hpop]; rfl
        have hsusp := caller_susp (hth u).2 hpop
        rw [hcaller] at hsusp
        have hcl := finish_void hf.1 hf.2.2.2 hfin
        rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hcl
        exact ownInv_pop hag hfo hd hth hpop rfl rfl rfl (resume_why hd hdu hsusp hcl _)
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho
      s0 hs0 rg hrg hn =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    obtain ⟨c2, hs, _⟩ := hor.stmtEnde
    have hfin := os_top hs
    have hdu : depthOf M u = rst.length + 1 := by
      show (M.faeden u).stapel.length = _
      rw [hpop]; rfl
    have hsusp := caller_susp (hth u).2 hpop
    rw [hcaller] at hsusp
    have hcl := finish_void hf.1 hf.2.2.2 hfin
    rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hcl
    exact ownInv_pop hag hfo hd hth hpop rfl rfl rfl (resume_why hd hdu hsusp hcl _)
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho
      s0 hs0 rg hrg hn =>
    rw [hhead] at hH
    obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
    obtain ⟨c2, hs, _⟩ := hor.stmt trivial
    have hfin := os_top hs
    have hdu : depthOf M u = rst.length + 1 := by
      show (M.faeden u).stapel.length = _
      rw [hpop]; rfl
    have hsusp := caller_susp (hth u).2 hpop
    rw [hcaller] at hsusp
    have hcl := finish_void hf.1 hf.2.2.2 hfin
    rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hcl
    exact ownInv_pop hag hfo hd hth hpop rfl rfl rfl (resume_why hd hdu hsusp hcl _)
  | dannRegLies l Γ Λ Λ' r hk' rest k ρ hhead v hv hz hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_regRead hk hf ha ho hr v) rfl rfl hrely
  | dannRegLiesElseWahr l Γ Λ Λ' r hk' zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_regReadElse hk hf ha ho hr (meta_lese _ _ _ hs₁) v) (by subst hs₁; rfl) rfl hrely
  | dannRegLiesElseFalsch l Γ Λ Λ' r hk' zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_regReadSonst hk hf ha ho hr (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely
  | dannAwaits l Γ Λ Λ' gl payload hp hL hat rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_awaits hk hf ha ho hr (meta_lese _ _ _ hs₁) _) (by subst hs₁; rfl) rfl hrely
  | dannExchange l Γ Λ Λ' gl neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    subst hs₂
    exact fin (run_exchange hk hf ha ho hr σ₁ (meta_lese _ _ _ hs₁) _ _) rfl rfl hrely
  | dannGleit l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_float hk hf ha ho hr (meta_lese _ _ _ hs₁) v) (by subst hs₁; rfl) rfl hrely
  | dannGleitLit l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_floatLit hk hf ha ho hr v) rfl rfl hrely
  | dannGleitVon l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_floatOf hk hf ha ho hr (meta_lese _ _ _ hs₁) v) (by subst hs₁; rfl) rfl hrely
  | dannGleitNarrowOk l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_floatNarrow hk hf ha ho hr (meta_lese _ _ _ hs₁) v) (by subst hs₁; rfl) rfl hrely
  | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    exact fin (run_floatNarrowSonst hk hf ha ho hr (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd' hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    subst hs₁
    exact fin (run_bindAxiom hO hk hf ha ho hr hax _) rfl rfl hrely
  | dannBindAxiomElseOk l Γ Λ Λ' τ a args he hr0 hw hg hd' hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    subst hs₁
    exact fin (run_bindAxiomElse hO hk hf ha ho hr hax _) rfl rfl hrely
  | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr0 hw hg hd' hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    subst hs₁
    exact fin (run_bindAxiomGrund hO hk hf ha ho hr hax r) rfl rfl hrely
  | endeBindAxiomElseOk l Γ Λ τ a args he hr0 hw hg hd' hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    subst hs₁
    exact fin ((run_bindAxiomElseEnde hO hk hf ha ho hr hax).1 _) rfl rfl hrely
  | endeBindAxiomElseGrund l Γ Λ τ a args he hr0 hw hg hd' hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
    subst hs₁
    exact fin ((run_bindAxiomElseEnde hO hk hf ha ho hr hax).2 r) rfl rfl hrely

#print axioms ownInv_step

end Gabbro.Grammatik.ArenaOwnership.Machine
