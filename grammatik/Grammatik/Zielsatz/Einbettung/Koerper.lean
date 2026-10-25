import Grammatik.Zielsatz.Einbettung.Simulation

/-!
  File:      Grammatik/Zielsatz/Einbettung/Koerper.lean
  Subject:   **The simulation, form by form** (stage E2c): every statement, block, end block and
             arm list of `D` runs beside its image (`sim_stmt`, `sim_block`, `sim_end`, `sim_arms`,
             `sim_grund`).
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

namespace Einbettung

variable (E : Einbettung D D')

theorem ortE_inl (t : D.Tab) : (Sum.inl (E.tab t) : D'.Tab ⊕ D'.Glob) = E.ortE (.inl t) := rfl
theorem ortE_inr (g : D.Glob) : (Sum.inr (E.glob g) : D'.Tab ⊕ D'.Glob) = E.ortE (.inr g) := rfl

theorem aparamsUm_falt (a : D.Ax) (ρ : Env D (D.aparams a)) :
    castE (E.aparams a).symm (E.envE ρ) = E.aparamsUm a ρ := rfl

variable (hZ : E.Rueck) (hS : E.SigTreu) (pad : List (Ereignis D)) (S : SperrInv D)
  (T : D.Tab ⊕ D.Glob → Prop) (S' : SperrInv D') (T' : D'.Tab ⊕ D'.Glob → Prop) (O' : Orakel D')
  (U' : Umwelt D') (A' : AUmwelt D') (passes : Nat)
  (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f)

/-- **A call through the keys**: the pair before the call as a main key, the callee of `D'` and
    its arguments as a call key; the induced handler answers as the `D'`-callee there, and every
    answer world is a world beside its restriction. -/
theorem ruf_schritt {M : Keys D D'} {σ : World D} {σ' : World D'} (hp : PadOk pad)
    (h : E.Inv hZ M σ σ') (g : D.Fn) (ρa : Env D (D.params g)) (f' : D'.Fn)
    (a' : Env D' (D'.params f')) (hr : E.EnvR hZ ρa a') (hk : E.Konform hZ g f') :
    ∃ M₁ : Keys D D', Teil M M₁ ∧
      (∀ Φ, Passt Φ M₁ → E.rufΦ hZ hS pad Φ R' g σ ρa =
        E.antwortR hZ pad g σ (konform_sig hS hk).2.1 (konform_sig hS hk).2.2 (R' f' σ' a')) ∧
      ∀ W, E.Inv hZ M₁ (E.antwortWelt hZ pad σ W) W := by
  refine ⟨⟨(σ, σ') :: M.haupt, M.atom, (σ, ⟨f', a'⟩) :: M.ruf⟩,
    ⟨fun _ hq => List.mem_cons_of_mem _ hq, fun _ hq => hq, fun _ hq => List.mem_cons_of_mem _ hq⟩,
    fun Φ hP => ?_, fun W => ?_⟩
  · have h1 : Φ.haupt σ = σ' := hP.1 _ List.mem_cons_self
    have h2 : Φ.ruf σ = some ⟨f', a'⟩ := hP.2.2 _ List.mem_cons_self
    unfold rufΦ
    rw [h2]
    simp only []
    rw [dif_pos ⟨hr, hk⟩, h1]
  · exact (h.merke E).merkeRuf E ⟨f', a'⟩ (E.antwortWelt_laenge hZ hp σ W) (E.treu_antwortWelt hZ pad σ W)

/-- An axiom through the keys. -/
theorem ax_schluessel {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv hZ M σ σ') (a : D.Ax) (ρa : Env D (D.aparams a)) :
    ∃ M₁ : Keys D D', Teil M M₁ ∧
      (∀ Φ, Passt Φ M₁ → (E.orakelΦ hZ pad Φ O').wirkt a σ ρa =
        (E.antwortWelt hZ pad σ (O'.wirkt (E.ax a) σ' (E.aparamsUm a ρa)).1,
          (O'.wirkt (E.ax a) σ' (E.aparamsUm a ρa)).2)) ∧ E.Inv hZ M₁ σ σ' := by
  obtain ⟨hk, hs, hΦ⟩ := E.schluessel h
  exact ⟨_, hs, fun Φ hP => by simp only [orakelΦ, hΦ Φ hP], hk⟩

/-- Pointer-free values beside each other are equal through the embedding. -/
theorem frei_eq {τ : Ty} {v : Wert D τ} {v' : Wert D' (E.tyE τ)} (h : E.VRel hZ τ v v')
    (hτ : τ.zeigerfrei = true) : v' = E.valE τ v :=
  (E.vrel_frei hZ τ hτ v v').mp h

/-- **Pointer-free expressions evaluate as their images**, in environments beside each other. -/
theorem frei_alle {σ₁ : World D} {σ₁' : World D'}
    (hev : ∀ {Γ : Ctx} {Λ₀ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ₀ τ) (ρ : Env D Γ)
      (ρ' : Env D' (Γ.map E.tyE)), E.EnvR hZ ρ ρ' →
      E.VRel hZ τ (eval σ₁ e σ₁ ρ) (eval σ₁' (exE E e) σ₁' ρ'))
    {Γ : Ctx} {ρ : Env D Γ} {ρ' : Env D' (Γ.map E.tyE)} (hρ : E.EnvR hZ ρ ρ') :
    ∀ (Λ₀ : List (Res D)) (τ : Ty) (e : Expr D Γ Λ₀ τ), τ.zeigerfrei = true →
      eval σ₁' (exE E e) σ₁' ρ' = E.valE τ (eval σ₁ e σ₁ ρ) :=
  fun _ _ e hτ => E.frei_eq hZ (hev e ρ ρ' hρ) hτ

theorem zf_int {a b : Int} : (Ty.int a b).zeigerfrei = true := rfl
theorem zf_index {c : Int} : (Ty.index c).zeigerfrei = true := rfl
theorem zf_bool : Ty.bool.zeigerfrei = true := rfl
theorem zf_opt {n : Int} : (Ty.opt n).zeigerfrei = true := rfl
theorem zf_sum {cs : List (Option (Int × Int))} : (Ty.sum cs).zeigerfrei = true := rfl
theorem zf_why {n : Nat} : (Ty.why n).zeigerfrei = true := rfl
theorem zf_fl {lo hi : Int × Int} : (Ty.fl lo hi).zeigerfrei = true := rfl
theorem zf_ref {n : Nat} : (Ty.ref n).zeigerfrei = true := rfl

/-- A value written through a type equation, beside its source. -/
theorem vrel_um {τ T' : Ty} (e : T' = E.tyE τ) {v : Wert D τ} {v' : Wert D' (E.tyE τ)}
    (h : E.VRel hZ τ v v') : E.VRel hZ τ v (castW e (castW e.symm v')) := by
  rw [castW_symm]; exact h

/-- **Pointer-free arguments beside each other are equal through the embedding.** -/
theorem envR_eq_frei : ∀ {Γ : Ctx}, (∀ τ ∈ Γ, τ.zeigerfrei = true) →
    ∀ (ρ : Env D Γ) (ρ' : Env D' (Γ.map E.tyE)), E.EnvR hZ ρ ρ' → ρ' = E.envE ρ
  | [], _, .nil, .nil, _ => rfl
  | τ :: Γ, hf, .cons v ρ, .cons v' ρ', h => by
      obtain ⟨⟨e, hv⟩, h2⟩ := h
      rw [castW_self] at hv
      rw [E.frei_eq hZ hv (hf τ List.mem_cons_self),
        envR_eq_frei (fun τ' h' => hf τ' (List.mem_cons_of_mem _ h')) ρ ρ' h2]
      rfl

theorem castW_index_n {D₀ : Deklaration} {c c' : Int} (h : Ty.index c = Ty.index c')
    (v : Wert D₀ (Ty.index c)) : (castW h v).n = v.n := castW_n h v

theorem valE_index_n {c : Int} (v : Wert D (Ty.index c)) : (E.valE (Ty.index c) v).n = v.n := rfl

theorem umsig_heq {D₀ : Deklaration} {f : D₀.Fn} {n : Nat} (hf : D₀.passt f n = true)
    (ρ : Env D₀ (D₀.sigNr n).params) : HEq (umsig hf ρ) ρ := by
  unfold umsig
  simp only [_root_.id]
  exact cast_heq _ _

theorem castE_heq {D₀ : Deklaration} {Γ Γ' : Ctx} (h : Γ = Γ') (ρ : Env D₀ Γ) : HEq (castE h ρ) ρ := by
  subst h; rfl

theorem envE_heq {Γ₁ Γ₂ : Ctx} (h : Γ₁ = Γ₂) (ρ₁ : Env D Γ₁) (ρ₂ : Env D Γ₂) (e : HEq ρ₁ ρ₂) :
    HEq (E.envE ρ₁) (E.envE ρ₂) := by
  subst h; cases e; rfl

theorem umsig_castE {D₀ : Deklaration} {f : D₀.Fn} {n : Nat} (hf : D₀.passt f n = true)
    (ρ : Env D₀ (D₀.sigNr n).params) :
    umsig hf ρ = castE (by unfold Deklaration.params; rw [(D₀.passt_sig hf).params]) ρ :=
  eq_of_heq ((umsig_heq hf ρ).trans (castE_heq _ ρ).symm)

/-- **The arguments of an indirect call, on both sides**, beside each other. -/
theorem envR_umsig {f : D.Fn} {f' : D'.Fn} {n n' : Nat} (hf : D.passt f n = true)
    (hf' : D'.passt f' n' = true) (x : Env D (D.sigNr n).params) (x' : Env D' (D'.sigNr n').params)
    (h : E.EnvR hZ x x') : E.EnvR hZ (umsig hf x) (umsig hf' x') := by
  rw [umsig_castE, umsig_castE, E.envR_umD hZ, E.envR_um hZ]; exact h

/-- A slot read through a type equation, on both sides. -/
theorem zahl_cast_n {T T' : Ty} {lo hi : Int} (hτ : T = .int lo hi) (hτ' : T' = .int lo hi)
    (e : T' = E.tyE T) (x : Wert D T) (x' : Wert D' T') (hx : E.VRel hZ T x (castW e x')) :
    (hτ' ▸ x' : Zahl _ _).n = (hτ ▸ x : Zahl _ _).n := by
  subst hτ; subst hτ'
  exact congrArg Zahl.n hx

/-- A state value written through a type equation, on both sides. -/
theorem zahl_cast_wert {T T' : Ty} {lo hi : Int} (hτ : T = .int lo hi) (hτ' : T' = .int lo hi)
    (e : T' = E.tyE T) (z : Zahl lo hi) :
    E.VRel hZ T (hτ ▸ (z : Zahl _ _)) (castW e (hτ' ▸ (z : Zahl _ _))) := by
  subst hτ; subst hτ'; rfl

theorem logikRel_kein {e : Logik D} {e' : Logik D'} (h : ∀ g', e' ≠ .vorbedingung g') :
    LogikRel e e' := fun g' he => absurd he (h g')

theorem wahr_valE (v : Wert D .bool) : wahr? (D := D') (E.valE .bool v) = wahr? v := rfl

theorem zelle_valE {n : Nat} (v : Wert D (.ref n)) : (E.valE (.ref n) v).zelle = v.zelle := rfl

@[simp] theorem valE_ref {n : Nat} (v : Wert D (.ref n)) : E.valE (.ref n) v = v := rfl

theorem orakelΦ_regLies (Φ : Phi D D') (r : D.Reg) (σ : World D) :
    (E.orakelΦ hZ pad Φ O').regLies r σ = O'.regLies (E.reg r) (Φ.haupt σ) := rfl

theorem orakelΦ_sichtbar (Φ : Phi D D') (g : D.Glob) (σ : World D) (h : (D.gtyp g).zeigerfrei = true) :
    (E.orakelΦ hZ pad Φ O').sichtbar g σ = O'.sichtbar (E.glob g) (Φ.haupt σ) := by
  simp only [orakelΦ, h, if_true]

theorem orakelΦ_zeiger (Φ : Phi D D') :
    (E.orakelΦ hZ pad Φ O').zeiger = fun _ => Option.none := rfl

/-- A block whose image is transported along its scope. -/
theorem koerperSim_block_um {V : Vertrag D} {l : Bool} {Δ : Ctx} {Δ₁ Δ₂ : Ctx}
    {Λ₁ Λ₂ : List (Res D')} (h : Δ₁ = Δ₂)
    (lauf : Phi D D' → World D → Env D Δ → Ausgang V l Δ)
    (b : Block D' (E.vertragE V) l Δ₁ Λ₁ Λ₂)
    (hs : E.KoerperSim hZ lauf (execBlockHA S' O' U' A' passes R' b)) :
    E.KoerperSim hZ lauf (execBlockHA S' O' U' A' passes R' (Block.umΓ h b)) := by
  intro M σ σ' ρ ρ' hI hρ
  obtain ⟨M₁, o, hs1, hΦ, hR⟩ := hs M σ σ' ρ (castE h.symm ρ') hI ((E.envR_um hZ h.symm ρ ρ').mpr hρ)
  refine ⟨M₁, o, hs1, hΦ, ?_⟩
  rw [execBlock_umΓ]
  exact (E.ausRel_um h o _).mpr hR

/-- An end block whose image is transported along its scope. -/
theorem endSim_end_um {V : Vertrag D} {l : Bool} {Δ : Ctx} {Δ₁ Δ₂ : Ctx}
    {Λ₁ : List (Res D')} (h : Δ₁ = Δ₂)
    (lauf : Phi D D' → World D → Env D Δ → EndAusgang V l Δ)
    (b : Endblock D' (E.vertragE V) l Δ₁ Λ₁)
    (hs : E.EndSim hZ lauf (execEndHA S' O' U' A' passes R' b)) :
    E.EndSim hZ lauf (execEndHA S' O' U' A' passes R' (Endblock.umΓ h b)) := by
  intro M σ σ' ρ ρ' hI hρ
  obtain ⟨M₁, o, hs1, hΦ, hR⟩ := hs M σ σ' ρ (castE h.symm ρ') hI ((E.envR_um hZ h.symm ρ ρ').mpr hρ)
  refine ⟨M₁, o, hs1, hΦ, ?_⟩
  rw [execEnd_umΓ]
  exact (E.endRel_um h o _).mpr hR

section Sim

variable (hB : E.Bed hZ pad S T S' T' U' A')
include hB

set_option maxHeartbeats 4000000 in
mutual

/-- **A statement beside its image.** -/
theorem sim_stmt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') →
    E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') s)
      (execStmtHA S' O' U' A' passes R' (exS hS s))
  | .assignSlot t f i e hw hL => by
      intro M σ σ' ρ ρ' h hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ h T hB.havocA hB.atom Λ (Λ.map E.resE)
        (i.orte ++ e.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      refine ⟨M₁, .ok (σ₁.schreibSlot t Λ (eval σ₁ i σ₁ ρ).n f (eval σ₁ e σ₁ ρ)) ρ, hs,
        fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, castW_index_n, valE_index_n]
        exact ⟨hI.schreibSlot E t Λ _ _ f _ _ (E.vrel_um hZ (E.typ t f) (hev e ρ ρ' hρ)), hρ⟩
  | .assignVar x e => by
      intro M σ σ' ρ ρ' h hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ h T hB.havocA hB.atom Λ (Λ.map E.resE) e.orte
      have hev0 := E.frei_alle hZ (@hev) hρ
      refine ⟨M₁, .ok σ₁ (ρ.set x (eval σ₁ e σ₁ ρ)), hs, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
        exact ⟨hI, E.envR_set hZ ρ ρ' x _ _ hρ (hev e ρ ρ' hρ)⟩
  | .assignThru p t ht f i e hw hL => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (p.orte ++ i.orte ++ e.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      refine ⟨M₁, .ok (σ₁.schreibSlot t Λ (eval σ₁ i σ₁ ρ).n f (eval σ₁ e σ₁ ρ)) ρ, hs,
        fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
        exact ⟨hI.schreibSlot E t Λ _ _ f _ _ (E.vrel_um hZ (E.typ t f) (hev e ρ ρ' hρ)), hρ⟩
  | .assignSlotRef r t ht ho f e hw hL => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (r.orte ++ e.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      refine ⟨M₁, .ok (σ₁.schreibSlot t Λ ((eval σ₁ r σ₁ ρ).zelle : Int) f (eval σ₁ e σ₁ ρ)) ρ, hs,
        fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, zelle_valE]
        exact ⟨hI.schreibSlot E t Λ _ _ f _ _ (E.vrel_um hZ (E.typ t f) (hev e ρ ρ' hρ)), hρ⟩
  | .assignGlob g e hw hL => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      refine ⟨M₁, .ok (σ₁.schreibGlob g Λ (eval σ₁ e σ₁ ρ)) ρ, hs, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
        exact ⟨hI.schreibGlob E g Λ _ _ _ (E.vrel_um hZ (E.gtyp g) (hev e ρ ρ' hρ)), hρ⟩
  | .putBytes t f hf n i hlo hhi e hw hL => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (i.orte ++ e.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      refine ⟨M₁, .ok (σ₁.schreibBytes t f hf Λ (eval σ₁ i σ₁ ρ).n (zahlZuBytes n (eval σ₁ e σ₁ ρ).n)) ρ,
        hs, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int]
        exact ⟨hI.schreibBytes E t f hf _ Λ _ _ _, hρ⟩
  | .shift t f hτ i von nach hn he hw hL => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (Sum.inl t :: i.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      have hn' := E.zahl_cast_n hZ hτ ((E.typ t f).trans (by rw [hτ])) (E.typ t f)
        (σ₁.slots t (eval σ₁ i σ₁ ρ).n f) _ (hI.treu.1 t (eval σ₁ i σ₁ ρ).n f)
      by_cases hc : (hτ ▸ σ₁.slots t (eval σ₁ i σ₁ ρ).n f : Zahl _ _).n = von
      · refine ⟨M₁, .ok (σ₁.schreibSlot t Λ (eval σ₁ i σ₁ ρ).n f (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))) ρ,
          hs, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ hP]
          rw [if_pos hc]
        · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
          rw [if_pos (hn'.trans hc)]
          exact ⟨hI.schreibSlot E t Λ _ _ f _ _ (E.zahl_cast_wert hZ hτ ((E.typ t f).trans (by rw [hτ])) (E.typ t f) _), hρ⟩
      · refine ⟨M₁, .logik .vorzustand, hs, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ hP]
          rw [if_neg hc]
        · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
          rw [if_neg (fun h' => hc (hn'.symm.trans h'))]
          exact ⟨logikRel_kein (fun _ h' => by cases h'), hI.keyOk E⟩
  | .ite c t e => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (c.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      cases hb : wahr? (eval σ₁ c σ₁ ρ)
      · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block e M₁ σ₁ _ ρ ρ' hI hρ
        refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hb, Bool.false_eq_true, ↓reduceIte]
          exact hΦ2 Φ hP
        · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, wahr_valE, hb, Bool.false_eq_true, ↓reduceIte]
          exact hR
      · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block t M₁ σ₁ _ ρ ρ' hI hρ
        refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hb, ↓reduceIte]
          exact hΦ2 Φ hP
        · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, wahr_valE, hb, ↓reduceIte]
          exact hR
  | .onOption (n := n) o p a => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (o.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      cases hv : eval σ₁ o σ₁ ρ with
      | none =>
          obtain ⟨M₂, o', hs2, hΦ2, hR⟩ := sim_block a M₁ σ₁ _ ρ ρ' hI hρ
          refine ⟨M₂, o', teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hv]
            exact hΦ2 Φ hP
          · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_opt, hv]
            exact hR
      | some k =>
          obtain ⟨M₂, o', hs2, hΦ2, hR⟩ := sim_block p M₁ σ₁ _ (Env.cons (τ := Ty.index n) k ρ)
            (Env.cons (τ := Ty.index n) k ρ') hI (E.envR_cons hZ hρ _ _ rfl rfl)
          refine ⟨M₂, o'.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hv]
            exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
          · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_opt, hv]
            exact E.ausRel_schrumpf hR
  | .onTag v arms => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (v.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_arms arms (eval σ₁ v σ₁ ρ) M₁ σ₁ _ ρ ρ' hI hρ
      refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2)]
        exact hΦ2 Φ hP
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
        exact hR
  | .onWhy r arms => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (r.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_grund arms (eval σ₁ r σ₁ ρ) M₁ σ₁ _ ρ ρ' hI hρ
      refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2)]
        exact hΦ2 Φ hP
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_why]
        exact hR
  | .call f args hp hr => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (evalArgs σ₁ args σ₁ ρ) (E.fn f)
        (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ'))
        ((E.envR_um hZ (paramsE hS f) _ _).mpr (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)) (Or.inl rfl)
      generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
        (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ')) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · refine ⟨M₂, .ok (E.antwortWelt hZ pad σ₁ W) ρ, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, evalArgs_umτs, ha]
          exact ⟨hI2 W, hρ⟩
      · exact (Fin.cast (by rw [gruendeE hS, hr]) r' : Fin 0).elim0
      · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, evalArgs_umτs, ha]
          exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, evalArgs_umτs, ha]
          trivial
  | .callInd (n := n) p args hp hr => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (p.orte ++ args.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      rcases hvd : eval σ₁ p σ₁ ρ with ⟨f, hf⟩
      have hp' := hev p ρ ρ' hρ
      rw [hvd] at hp'
      rcases hvd' : eval (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exE E p) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ' with ⟨f', hf'⟩
      rw [hvd'] at hp'
      have hk : E.Konform hZ f f' := by
        rcases hp' with h | ⟨hz, hr⟩
        · exact Or.inl h
        · exact Or.inr ⟨n, hz, hr, hf'⟩
      have hsig : (D.sigNr n).params.map E.tyE = (D'.sigNr (E.num n)).params := by rw [hS.sigNr]; rfl
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (umsig hf (evalArgs σ₁ args σ₁ ρ)) f'
        (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ')))
        (E.envR_umsig hZ hf hf' _ _ ((E.envR_um hZ hsig _ _).mpr
          (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ))) hk
      generalize ha : R' f' (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ'))) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · refine ⟨M₂, .ok (E.antwortWelt hZ pad σ₁ W) ρ, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
        · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
          exact ⟨hI2 W, hρ⟩
      · have h0 : D'.gruende f' = 0 := (konform_sig hS hk).2.2.trans ((D.passt_sig hf).gruende.trans hr)
        exact (Fin.cast h0 r').elim0
      · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
        · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
          exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
        · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
          trivial
  | .locks L hr body => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI⟩ := E.umwelt_schritt hM S hB.havocU hB.orte L
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block body M₁ (σ₁.nimmt L) _ ρ ρ'
        hI hρ
      refine ⟨M₂, freiH S L o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2)]
        exact congrArg (freiH S L) (hΦ2 Φ hP)
      · simp only [exS, execStmtHA]
        exact E.freiH_rel S hB.inv L hR
  | .breaking i body => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o, hs, hΦ, hR⟩ := sim_block body M σ σ' ρ ρ' hM hρ
      exact ⟨M₁, o, hs, fun Φ hP => by simp only [execStmtHA]; exact hΦ Φ hP,
        by simp only [exS, execStmtHA]; exact hR⟩
  | .traverse t inv body => by
      intro M σ σ' ρ ρ' hM hρ
      have hsb := E.koerperSim_block_um hZ S' O' U' A' passes R'
        (show (Ty.index (D.count t) :: Γ).map E.tyE = Ty.index (D'.count (E.tab t)) :: Γ.map E.tyE by
          rw [List.map_cons, E.count]) _ _ (sim_block body)
      have hi := E.pruef_sim hZ T hB.havocA hB.atom inv
      exact E.traverse_sim (l := l) _ _ _ _ hsb hi
        (fun k => castW (D := D') (show Ty.index (D.count t) = Ty.index (D'.count (E.tab t)) by
          rw [E.count]) k)
        (fun k => ⟨(show Ty.index (D.count t) = Ty.index (D'.count (E.tab t)) by rw [E.count]).symm,
          castW_symm (D := D') (τ := Ty.index (D'.count (E.tab t))) (σ := Ty.index (D.count t)) _ k⟩)
        (alleIndizes (D.count t))
        (alleIndizes (D'.count (E.tab t)))
        (Einbettung.alleIndizes_bild (D' := D') (E.count t)) M σ σ' ρ ρ' hM hρ
  | .retry n bis body ueber => by
      intro M σ σ' ρ ρ' hM hρ
      exact E.retry_sim _ _ _ _ _ _ (sim_block body) (E.pruef_sim hZ T hB.havocA hB.atom bis)
        (sim_block ueber) n M σ σ' ρ ρ' hM hρ
  | .forever a inv body => by
      intro M σ σ' ρ ρ' hM hρ
      exact E.forever_sim a (E.annahme a) _ _ _ _ (sim_block body)
        (E.pruef_sim hZ T hB.havocA hB.atom inv) passes M σ σ' ρ ρ' hM hρ
  | .axiomCall a args h hw hg hd hgd => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, hs2, hOΦ, hI2⟩ := E.ax_schluessel hZ pad O' hI a (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.envR_eq_frei hZ (hZ.frei.aparamsFrei a) _ _ (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)
      have hw' := E.axiom_wert hZ (fun _ => Option.none) O'.zeiger a
        (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
          (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 (E.aerg a)
      cases hx : einpassenErg (fun _ => Option.none) (D.aerg a)
          (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
            (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 with
      | none =>
          refine ⟨M₂, .hardware (.annahme a), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execStmtHA, axiomAntwort, hΦ Φ (passt_teil hP hs2), hOΦ Φ hP, orakelΦ_zeiger]
            rw [hx]
          · simp only [exS, execStmtHA, axiomAntwort, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
              evalArgs_umτs, hargs, aparamsUm_falt, hw']
            rw [hx]
            trivial
      | some v =>
          refine ⟨M₂, .ok (E.antwortWelt hZ pad σ₁ (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE)
            (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1) ρ, teil_trans hs hs2,
            fun Φ hP => ?_, ?_⟩
          · simp only [execStmtHA, axiomAntwort, hΦ Φ (passt_teil hP hs2), hOΦ Φ hP, orakelΦ_zeiger, hx]
          · simp only [exS, execStmtHA, axiomAntwort, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, evalArgs_umτs, hargs, aparamsUm_falt, hw', hx,
              Option.map_some]
            exact ⟨E.inv_antwort hZ hB.pad hI2 _, hρ⟩
  | .regWrite r hk e => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      refine ⟨M₁, .ok σ₁ ρ, hs, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr]
        exact ⟨hI, hρ⟩
  | .transition r hk m hm hl maske bits => by
      intro M σ σ' ρ ρ' hM hρ
      exact ⟨M, .ok σ ρ, teil_refl M, fun Φ hP => by simp only [execStmtHA],
        by simp only [exS, execStmtHA]; exact ⟨hM, hρ⟩⟩
  | .publish g e payload hp hw hL => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      refine ⟨M₁, .ok (σ₁.schreibGlob g Λ (eval σ₁ e σ₁ ρ)) ρ, hs, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
        exact ⟨hI.schreibGlob E g Λ _ _ _ (E.vrel_um hZ (E.gtyp g) (hev e ρ ρ' hρ)), hρ⟩
  | .advances m a h hs => by
      intro M σ σ' ρ ρ' hM hρ
      exact ⟨M, .ok σ ρ, teil_refl M, fun Φ hP => by simp only [execStmtHA],
        by simp only [exS, exec_nachΛ, execStmtHA]; exact ⟨hM, hρ⟩⟩
  | .retires m s h a => by
      intro M σ σ' ρ ρ' hM hρ
      exact ⟨M, .ok σ ρ, teil_refl M, fun Φ hP => by simp only [execStmtHA],
        by simp only [exS, exec_nachΛ, execStmtHA]; exact ⟨hM, hρ⟩⟩
  | .ret e hΛ => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T hM hB.havocA hB.atom Λ (Λ.map E.resE)
        e.orte (E.exErg e).orte (E.orte_exErg e).symm
      have hev0 := E.frei_alle hZ (@hev) hρ
      have he := E.evalErg_exErg hZ hI.treu hI.treu e ρ ρ' hρ
      refine ⟨M₁, .zurueck σ₁ (evalErg σ₁ e σ₁ ρ), hs, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · exact ⟨hI, he⟩
  | .retWhy r hΛ => by
      intro M σ σ' ρ ρ' hM hρ
      exact ⟨M, .why σ r, teil_refl M, fun Φ hP => by simp only [execStmtHA],
        by simp only [exS, execStmtHA]; exact ⟨hM, rfl⟩⟩
  | .leave h => by
      intro M σ σ' ρ ρ' hM hρ
      exact ⟨M, .leave h σ ρ, teil_refl M, fun Φ hP => by simp only [execStmtHA],
        by simp only [exS, execStmtHA]; exact ⟨hM, hρ⟩⟩
  | .next h => by
      intro M σ σ' ρ ρ' hM hρ
      exact ⟨M, .next h σ ρ, teil_refl M, fun Φ hP => by simp only [execStmtHA],
        by simp only [exS, execStmtHA]; exact ⟨hM, hρ⟩⟩

/-- **A block beside its image.** -/
theorem sim_block {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') →
    E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') b)
      (execBlockHA S' O' U' A' passes R' (exB hS b))
  | .nil => by
      intro M σ σ' ρ ρ' h hρ
      exact ⟨M, .ok σ ρ, teil_refl M, fun _ _ => rfl, h, hρ⟩
  | .cons s rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o₁, hs, hΦ, hR⟩ := sim_stmt s M σ σ' ρ ρ' hM hρ
      generalize ho : execStmtHA S' O' U' A' passes R' (exS hS s) σ' ρ' = o₁' at hR
      rcases o₁ with ⟨σ₂, ρ₂⟩ | ⟨σ₂, v⟩ | ⟨σ₂, r⟩ | ⟨h₂, σ₂, ρ₂⟩ | ⟨h₂, σ₂, ρ₂⟩ | e | e <;>
      rcases o₁' with ⟨σ₂', ρ₂'⟩ | ⟨σ₂', v'⟩ | ⟨σ₂', r'⟩ | ⟨h₂', σ₂', ρ₂'⟩ | ⟨h₂', σ₂', ρ₂'⟩ | e' | e' <;>
      simp only [AusRel] at hR <;> (try exact hR.elim)
      · obtain ⟨M₂, o, hs2, hΦ2, hR2⟩ := sim_block rest M₁ σ₂ σ₂' ρ₂ ρ₂' hR.1 hR.2
        refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
          exact hΦ2 Φ hP
        · simp only [exB, execBlockHA, ho]
          exact hR2
      all_goals
        refine ⟨M₁, _, hs, fun Φ hP => by simp only [execBlockHA, hΦ Φ hP]; rfl, ?_⟩
        simp only [exB, execBlockHA, ho]
        exact hR
  | .bind e rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block rest M₁ σ₁ _ (.cons (eval σ₁ e σ₁ ρ) ρ)
        (.cons (eval (leseA A' σ' (Λ.map E.resE) (e.orte.map E.ortE)) (exE E e) (leseA A' σ' (Λ.map E.resE) (e.orte.map E.ortE)) ρ') ρ') hI (E.envR_cons hZ hρ _ _ rfl (hev e ρ ρ' hρ))
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
        exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
      · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
        exact E.ausRel_schrumpf hR
  | .bindCall (τ := τ) f args he hp hr rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (evalArgs σ₁ args σ₁ ρ) (E.fn f)
        (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ'))
        ((E.envR_um hZ (paramsE hS f) _ _).mpr (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)) (Or.inl rfl)
      generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
        (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ')) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · have he' : D'.erg (E.fn f) = some (E.tyE τ) := by rw [← ergE_fn hS, he]; rfl
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_block rest M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (ergWert he (E.ergZ hZ (D.erg f) (castV (ergE_fn hS f).symm v'))) ρ)
          (.cons (ergWert he' v') ρ')
          (hI2 W)
          (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergZ hZ (ergE_fn hS f) he he' v'))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
        · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha,
            execBlock_vorΛ]
          exact E.ausRel_schrumpf hR3
      · exact (Fin.cast (by rw [gruendeE hS, hr]) r' : Fin 0).elim0
      · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
          exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
          trivial
  | .bindCallInd (n := n) (τ := τ) p args he hp hr rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (p.orte ++ args.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      rcases hvd : eval σ₁ p σ₁ ρ with ⟨f, hf⟩
      have hp' := hev p ρ ρ' hρ
      rw [hvd] at hp'
      rcases hvd' : eval (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exE E p) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ' with ⟨f', hf'⟩
      rw [hvd'] at hp'
      have hk : E.Konform hZ f f' := by
        rcases hp' with h | ⟨hz, hr⟩
        · exact Or.inl h
        · exact Or.inr ⟨n, hz, hr, hf'⟩
      have hsig : (D.sigNr n).params.map E.tyE = (D'.sigNr (E.num n)).params := by rw [hS.sigNr]; rfl
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (umsig hf (evalArgs σ₁ args σ₁ ρ)) f'
        (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ')))
        (E.envR_umsig hZ hf hf' _ _ ((E.envR_um hZ hsig _ _).mpr
          (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ))) hk
      generalize ha : R' f' (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ'))) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · have he₁ : D.erg f = some τ := ergSig hf he
        have heS : (D'.sigNr (E.num n)).erg = some (E.tyE τ) := by
          rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl
        have he' : D'.erg f' = some (E.tyE τ) := ergSig hf' heS
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_block rest M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (ergWert he₁ (E.ergZ hZ (D.erg f) (castV (konform_sig hS hk).2.1 v'))) ρ)
          (.cons (ergWert he' v') ρ')
          (hI2 W)
          (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergZ hZ (konform_sig hS hk).2.1.symm he₁ he' v'))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hvd, hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
        · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha,
            execBlock_vorΛ]
          exact E.ausRel_schrumpf hR3
      · have h0 : D'.gruende f' = 0 := (konform_sig hS hk).2.2.trans ((D.passt_sig hf).gruende.trans hr)
        exact (Fin.cast h0 r').elim0
      · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
        · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
          exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
        · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
          trivial
  | .bindCallElse (τ := τ) f args he hp hr err rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (evalArgs σ₁ args σ₁ ρ) (E.fn f)
        (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ'))
        ((E.envR_um hZ (paramsE hS f) _ _).mpr (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)) (Or.inl rfl)
      generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
        (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ')) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · have he' : D'.erg (E.fn f) = some (E.tyE τ) := by rw [← ergE_fn hS, he]; rfl
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_block rest M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (ergWert he (E.ergZ hZ (D.erg f) (castV (ergE_fn hS f).symm v'))) ρ)
          (.cons (ergWert he' v') ρ')
          (hI2 W)
          (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergZ hZ (ergE_fn hS f) he he' v'))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
        · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha,
            execBlock_vorΛ]
          exact E.ausRel_schrumpf hR3
      · have hc : (Ty.why (D.gruende f) :: Γ).map E.tyE = Ty.why (D'.gruende (E.fn f)) :: Γ.map E.tyE := by
          rw [gruendeE hS]; rfl
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_end err M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (Fin.cast (gruendeE hS f) r') ρ) (castE hc.symm (.cons r' ρ'))
          (hI2 W)
          ((E.envR_um hZ hc.symm _ _).mpr (E.envR_cons hZ hρ _ _ (by rw [gruendeE hS])
            (by rw [castW_why]; rfl)))
        refine ⟨M₃, o.schrumpf.zuAusgang, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg (fun x => x.schrumpf.zuAusgang) (hΦ3 Φ hP)
        · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha,
            execEnd_umΓ, execEnd_umΛ]
          exact E.endRel_zuAusgang (E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR3))
      · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
          exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
          trivial
  | .bindAxiom (τ := τ) a args he hw hg hd hgd rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, hs2, hOΦ, hI2⟩ := E.ax_schluessel hZ pad O' hI a (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.envR_eq_frei hZ (hZ.frei.aparamsFrei a) _ _ (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)
      have hw' := E.axiom_wert hZ (fun _ => Option.none) O'.zeiger a (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 (E.aerg a)
      have he' : D'.aerg (E.ax a) = some (E.tyE τ) := by rw [E.aerg, he]; rfl
      cases hx : einpassenErg (fun _ => Option.none) (D.aerg a) (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 with
      | none =>
          refine ⟨M₂, .hardware (.annahme a), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, axiomAntwort, hΦ Φ (passt_teil hP hs2), hOΦ Φ hP, orakelΦ_zeiger]
            rw [hx]
          · simp only [exB, execBlockHA, axiomAntwort, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
              evalArgs_umτs, hargs, aparamsUm_falt, hw']
            rw [hx]
            trivial
      | some v =>
          obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_block rest M₂ (E.antwortWelt hZ pad σ₁ (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1) (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1
            (.cons (ergWert he v) ρ) (.cons (ergWert he' (castV (E.aerg a).symm (E.ergE _ v))) ρ')
            (E.inv_antwort hZ hB.pad hI2 _) (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergE hZ (E.aerg a) he he' v))
          refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, axiomAntwort, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)),
              hOΦ Φ (passt_teil hP hs3), orakelΦ_zeiger]
            rw [hx]
            exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
          · simp only [exB, execBlockHA, axiomAntwort, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
              evalArgs_umτs, hargs, aparamsUm_falt, hw']
            rw [hx]
            exact E.ausRel_schrumpf hR3
  | .bindAxiomElse (τ := τ) a args he hr hw hg hd hgd err rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, hs2, hOΦ, hI2⟩ := E.ax_schluessel hZ pad O' hI a (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.envR_eq_frei hZ (hZ.frei.aparamsFrei a) _ _ (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)
      have hw' := E.axiomSonst_wert hZ (fun _ => Option.none) O'.zeiger a (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 (E.aerg a) (E.agruende a)
      have he' : D'.aerg (E.ax a) = some (E.tyE τ) := by rw [E.aerg, he]; rfl
      rcases hx : sonstPasst (fun _ => Option.none) (D.aerg a) (D.agruende a) (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 with _ | (v | r)
      · refine ⟨M₂, .hardware (.annahme a), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, axiomAntwortSonst, hΦ Φ (passt_teil hP hs2), hOΦ Φ hP, orakelΦ_zeiger]
          rw [hx]
        · simp only [exB, execBlockHA, axiomAntwortSonst, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
            evalArgs_umτs, hargs, aparamsUm_falt, hw']
          rw [hx]
          trivial
      · obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_block rest M₂ (E.antwortWelt hZ pad σ₁ (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1) (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1
          (.cons (ergWert he v) ρ) (.cons (ergWert he' (castV (E.aerg a).symm (E.ergE _ v))) ρ')
          (E.inv_antwort hZ hB.pad hI2 _) (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergE hZ (E.aerg a) he he' v))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, axiomAntwortSonst, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)),
            hOΦ Φ (passt_teil hP hs3), orakelΦ_zeiger]
          rw [hx]
          exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
        · simp only [exB, execBlockHA, axiomAntwortSonst, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
            evalArgs_umτs, hargs, aparamsUm_falt, hw']
          rw [hx]
          exact E.ausRel_schrumpf hR3
      · have hc : (Ty.why (D.agruende a) :: Γ).map E.tyE = Ty.why (D'.agruende (E.ax a)) :: Γ.map E.tyE := by
          rw [E.agruende]; rfl
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_end err M₂ (E.antwortWelt hZ pad σ₁ (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1) (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1
          (.cons r ρ) (castE hc.symm (.cons (Fin.cast (E.agruende a).symm r) ρ'))
          (E.inv_antwort hZ hB.pad hI2 _)
          ((E.envR_um hZ hc.symm _ _).mpr (E.envR_cons hZ hρ _ _ (by rw [E.agruende])
            (by rw [castW_why]; exact Fin.ext rfl)))
        refine ⟨M₃, o.schrumpf.zuAusgang, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, axiomAntwortSonst, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)),
            hOΦ Φ (passt_teil hP hs3), orakelΦ_zeiger]
          rw [hx]
          exact congrArg (fun x => x.schrumpf.zuAusgang) (hΦ3 Φ hP)
        · simp only [exB, execBlockHA, axiomAntwortSonst, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
            evalArgs_umτs, hargs, aparamsUm_falt, hw']
          rw [hx]
          simp only [execEnd_umΓ]
          exact E.endRel_zuAusgang (E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR3))
  | .regRead r hk rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨hk1, hs1, hΦ1⟩ := E.schluessel hM
      have hw' := E.regLies_wert hZ (fun _ => Option.none) O'.zeiger r (O'.regLies (E.reg r) σ') (E.rtyp r)
      have hc : (D.rtyp r :: Γ).map E.tyE = D'.rtyp (E.reg r) :: Γ.map E.tyE := by
        rw [List.map_cons, E.rtyp]
      cases hx : einpassen (fun _ => Option.none) (D.rtyp r) (O'.regLies (E.reg r) σ') with
      | none =>
          refine ⟨_, .hardware (.register r), hs1, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ hP]
            rw [hx]
          · simp only [exB, execBlockHA]
            rw [hw'.1 hx]
            trivial
      | some v =>
          have hz := hS.rzusage r v
          cases hzv : D.rzusage r v
          · refine ⟨_, .hardware (.geraet r), hs1, fun Φ hP => ?_, ?_⟩
            · simp only [execBlockHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ hP]
              rw [hx]
              simp only [hzv, Bool.false_eq_true, ↓reduceIte]
            · simp only [exB, execBlockHA]
              rw [hw'.2 v hx]
              simp only [hz, hzv, Bool.false_eq_true, ↓reduceIte]
              trivial
          · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := E.koerperSim_block_um hZ S' O' U' A' passes R' hc _ _ (sim_block rest)
              _ σ σ' (.cons v ρ) (.cons ((E.rtyp r).symm ▸ E.valE _ v) ρ') hk1
              (E.envR_cons hZ hρ _ _ (E.rtyp r) (E.vrel_um hZ (E.rtyp r) (E.vrel_valE hZ _ v)))
            refine ⟨M₂, o.schrumpf, teil_trans hs1 hs2, fun Φ hP => ?_, ?_⟩
            · simp only [execBlockHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ (passt_teil hP hs2)]
              rw [hx]
              simp only [hzv, ↓reduceIte]
              exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
            · simp only [exB, execBlockHA]
              rw [hw'.2 v hx]
              simp only [hz, hzv, ↓reduceIte]
              exact E.ausRel_schrumpf hR
  | .regReadElse r hk zusage sonst rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨hk1, hs1, hΦ1⟩ := E.schluessel hM
      have hw' := E.regLies_wert hZ (fun _ => Option.none) O'.zeiger r (O'.regLies (E.reg r) σ') (E.rtyp r)
      have hc : (D.rtyp r :: Γ).map E.tyE = D'.rtyp (E.reg r) :: Γ.map E.tyE := by
        rw [List.map_cons, E.rtyp]
      cases hx : einpassen (fun _ => Option.none) (D.rtyp r) (O'.regLies (E.reg r) σ') with
      | none =>
          refine ⟨_, .hardware (.register r), hs1, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ hP]
            rw [hx]
          · simp only [exB, execBlockHA]
            rw [hw'.1 hx]
            trivial
      | some v =>
          obtain ⟨M₂, σ₁, hs2, hΦ2, hI, hev⟩ := E.lese_eval hZ hk1 T hB.havocA hB.atom Λ (Λ.map E.resE)
            zusage.orte
          have hev0 := E.frei_alle hZ (@hev) hρ
          have hrel := (E.envR_um hZ hc.symm (.cons v ρ)
              (.cons ((E.rtyp r).symm ▸ E.valE _ v) ρ' : Env D' (D'.rtyp (E.reg r) :: Γ.map E.tyE))).mpr
              (E.envR_cons hZ hρ _ _ (E.rtyp r) (E.vrel_um hZ (E.rtyp r) (E.vrel_valE hZ _ v)))
          have hz' := E.frei_eq hZ (hev zusage _ _ hrel) rfl
          cases hb : wahr? (eval σ₁ zusage σ₁ (.cons v ρ))
          · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := sim_end sonst M₂ σ₁ _ ρ ρ' hI hρ
            refine ⟨M₃, o.zuAusgang, teil_trans (teil_trans hs1 hs2) hs3, fun Φ hP => ?_, ?_⟩
            · simp only [execBlockHA, orakelΦ_regLies, orakelΦ_zeiger,
                hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3))]
              rw [hx]
              simp only [hΦ2 Φ (passt_teil hP hs3), hb, Bool.false_eq_true, ↓reduceIte]
              exact congrArg EndAusgang.zuAusgang (hΦ3 Φ hP)
            · simp only [exB, execBlockHA]
              rw [hw'.2 v hx]
              simp only [Expr.orte_umΓ, Einbettung.orte_exE, eval_umΓ, hz', wahr_valE, hb,
                Bool.false_eq_true, ↓reduceIte]
              exact E.endRel_zuAusgang hR
          · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := E.koerperSim_block_um hZ S' O' U' A' passes R' hc _ _ (sim_block rest)
              M₂ σ₁ _ (.cons v ρ) (.cons ((E.rtyp r).symm ▸ E.valE _ v) ρ') hI
              (E.envR_cons hZ hρ _ _ (E.rtyp r) (E.vrel_um hZ (E.rtyp r) (E.vrel_valE hZ _ v)))
            refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs1 hs2) hs3, fun Φ hP => ?_, ?_⟩
            · simp only [execBlockHA, orakelΦ_regLies, orakelΦ_zeiger,
                hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3))]
              rw [hx]
              simp only [hΦ2 Φ (passt_teil hP hs3), hb, ↓reduceIte]
              exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
            · simp only [exB, execBlockHA]
              rw [hw'.2 v hx]
              simp only [Expr.orte_umΓ, Einbettung.orte_exE, eval_umΓ, hz', wahr_valE, hb, ↓reduceIte]
              exact E.ausRel_schrumpf hR
  | .awaits g payload hp hL hat rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T hM hB.havocA hB.atom Λ (Λ.map E.resE)
        [Sum.inr g] [Sum.inr (E.glob g)] rfl
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨hk2, hs2, hΦ2⟩ := E.schluessel hI
      have hc : (D.gtyp g :: Γ).map E.tyE = D'.gtyp (E.glob g) :: Γ.map E.tyE := by
        rw [List.map_cons, E.gtyp]
      have hzf := hZ.frei.atomFrei g hat
      cases hvis : O'.sichtbar (E.glob g) (leseA A' σ' (Λ.map E.resE) [Sum.inr (E.glob g)])
      · refine ⟨_, .hardware (.sichtbarkeit D.a10), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), orakelΦ_sichtbar, hzf, hΦ2 Φ hP, hvis,
            Bool.false_eq_true, ↓reduceIte]
        · simp only [exB, execBlockHA, hvis, Bool.false_eq_true, ↓reduceIte]
          trivial
      · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := E.koerperSim_block_um hZ S' O' U' A' passes R' hc _ _ (sim_block rest)
          _ σ₁ _ (.cons (σ₁.globs g) ρ) (.cons ((leseA A' σ' (Λ.map E.resE) [Sum.inr (E.glob g)]).globs
            (E.glob g)) ρ') hk2 (E.envR_cons hZ hρ _ _ (E.gtyp g) (hk2.treu.2 g))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), orakelΦ_sichtbar, hzf,
            hΦ2 Φ (passt_teil hP hs3), hvis, ↓reduceIte]
          exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
        · simp only [exB, execBlockHA, hvis, ↓reduceIte]
          exact E.ausRel_schrumpf hR
  | .exchange g neu hw hL rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (Sum.inr g :: neu.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      have hc : (D.gtyp g :: Γ).map E.tyE = D'.gtyp (E.glob g) :: Γ.map E.tyE := by
        rw [List.map_cons, E.gtyp]
      have hrel := E.envR_cons hZ hρ (σ₁.globs g)
        ((leseA A' σ' (Λ.map E.resE) ((Sum.inr g :: neu.orte).map E.ortE)).globs (E.glob g))
        (E.gtyp g) (hI.treu.2 g)
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := E.koerperSim_block_um hZ S' O' U' A' passes R' hc _ _ (sim_block rest)
        M₁ (σ₁.schreibGlob g Λ (eval σ₁ neu σ₁ (.cons (σ₁.globs g) ρ))) _ (.cons (σ₁.globs g) ρ) _
        (hI.schreibGlob E g Λ (Λ.map E.resE) _ _
          (E.vrel_um hZ (E.gtyp g) (hev neu _ _ ((E.envR_um hZ hc.symm _ _).mpr hrel)))) hrel
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
        exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
      · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umΓ, eval_umTy, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
        exact E.ausRel_schrumpf hR
  | .narrow e lo' hi' sonst rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      by_cases hc : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi'
      · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block rest M₁ σ₁ _ (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ)
          (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ') hI
          (E.envR_cons hZ hρ _ _ rfl rfl)
        refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
          rw [dif_pos hc]
          exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
        · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int]
          rw [dif_pos hc]
          exact E.ausRel_schrumpf hR
      · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_end sonst M₁ σ₁ _ ρ ρ' hI hρ
        refine ⟨M₂, o.zuAusgang, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
          rw [dif_neg hc]
          exact congrArg EndAusgang.zuAusgang (hΦ2 Φ hP)
        · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int]
          rw [dif_neg hc]
          exact E.endRel_zuAusgang hR
  | .check c sonst rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (c.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      cases hb : wahr? (eval σ₁ c σ₁ ρ)
      · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_end sonst M₁ σ₁ _ ρ ρ' hI hρ
        refine ⟨M₂, o.zuAusgang, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hb, Bool.false_eq_true, ↓reduceIte]
          exact congrArg EndAusgang.zuAusgang (hΦ2 Φ hP)
        · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, wahr_valE, hb, Bool.false_eq_true, ↓reduceIte]
          exact E.endRel_zuAusgang hR
      · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block rest M₁ σ₁ _ ρ ρ' hI hρ
        refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hb, ↓reduceIte]
          exact hΦ2 Φ hP
        · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, wahr_valE, hb, ↓reduceIte]
          exact hR
  | .float op a b lo hi rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (a.orte ++ b.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      cases hg : gleitPasst lo hi (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x) with
      | none =>
          refine ⟨M₁, .logik .bereich, hs, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hΦ Φ hP, hg]
          · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_fl, hg]
            exact ⟨logikRel_kein (fun _ h' => by cases h'), hI.keyOk E⟩
      | some w =>
          obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hI
            (E.envR_cons hZ hρ _ _ rfl rfl)
          refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
            exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
          · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_fl, hg]
            exact E.ausRel_schrumpf hR
  | .floatLit q lo hi rest => by
      intro M σ σ' ρ ρ' hM hρ
      cases hg : gleitPasst lo hi (bruch q) with
      | none =>
          refine ⟨M, .logik .bereich, teil_refl M, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hg]
          · simp only [exB, execBlockHA, hg]
            exact ⟨logikRel_kein (fun _ h' => by cases h'), hM.keyOk E⟩
      | some w =>
          obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block rest M σ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hM
            (E.envR_cons hZ hρ _ _ rfl rfl)
          refine ⟨M₂, o.schrumpf, hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hg]
            exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
          · simp only [exB, execBlockHA, hg]
            exact E.ausRel_schrumpf hR
  | .floatOf e lo hi rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      cases hg : gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n) with
      | none =>
          refine ⟨M₁, .logik .bereich, hs, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hΦ Φ hP, hg]
          · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int, hg]
            exact ⟨logikRel_kein (fun _ h' => by cases h'), hI.keyOk E⟩
      | some w =>
          obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hI
            (E.envR_cons hZ hρ _ _ rfl rfl)
          refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
            exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
          · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int, hg]
            exact E.ausRel_schrumpf hR
  | .floatNarrow e lo hi sonst rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      cases hg : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x with
      | none =>
          obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_end sonst M₁ σ₁ _ ρ ρ' hI hρ
          refine ⟨M₂, o.zuAusgang, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
            exact congrArg EndAusgang.zuAusgang (hΦ2 Φ hP)
          · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_fl, hg]
            exact E.endRel_zuAusgang hR
      | some w =>
          obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hI
            (E.envR_cons hZ hρ _ _ rfl rfl)
          refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
            exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
          · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_fl, hg]
            exact E.ausRel_schrumpf hR

/-- **An end block beside its image.** -/
theorem sim_end {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) →
    E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') b)
      (execEndHA S' O' U' A' passes R' (exEnd hS b))
  | .ret e hΛ => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T hM hB.havocA hB.atom Λ (Λ.map E.resE)
        e.orte (E.exErg e).orte (E.orte_exErg e).symm
      have hev0 := E.frei_alle hZ (@hev) hρ
      have he := E.evalErg_exErg hZ hI.treu hI.treu e ρ ρ' hρ
      refine ⟨M₁, .zurueck σ₁ (evalErg σ₁ e σ₁ ρ), hs, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, hΦ Φ hP]
      · exact ⟨hI, he⟩
  | .retWhy r hΛ => by
      intro M σ σ' ρ ρ' hM hρ
      exact ⟨M, .why σ r, teil_refl M, fun Φ hP => by simp only [execEndHA],
        by simp only [exEnd, execEndHA]; exact ⟨hM, rfl⟩⟩
  | .leave h => by
      intro M σ σ' ρ ρ' hM hρ
      exact ⟨M, .leave h σ ρ, teil_refl M, fun Φ hP => by simp only [execEndHA],
        by simp only [exEnd, execEndHA]; exact ⟨hM, hρ⟩⟩
  | .next h => by
      intro M σ σ' ρ ρ' hM hρ
      exact ⟨M, .next h σ ρ, teil_refl M, fun Φ hP => by simp only [execEndHA],
        by simp only [exEnd, execEndHA]; exact ⟨hM, hρ⟩⟩
  | .cons s rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o₁, hs, hΦ, hR⟩ := sim_stmt s M σ σ' ρ ρ' hM hρ
      generalize ho : execStmtHA S' O' U' A' passes R' (exS hS s) σ' ρ' = o₁' at hR
      rcases o₁ with ⟨σ₂, ρ₂⟩ | ⟨σ₂, v⟩ | ⟨σ₂, r⟩ | ⟨h₂, σ₂, ρ₂⟩ | ⟨h₂, σ₂, ρ₂⟩ | e | e <;>
      rcases o₁' with ⟨σ₂', ρ₂'⟩ | ⟨σ₂', v'⟩ | ⟨σ₂', r'⟩ | ⟨h₂', σ₂', ρ₂'⟩ | ⟨h₂', σ₂', ρ₂'⟩ | e' | e' <;>
      simp only [AusRel] at hR <;> (try exact hR.elim)
      · obtain ⟨M₂, o, hs2, hΦ2, hR2⟩ := sim_end rest M₁ σ₂ σ₂' ρ₂ ρ₂' hR.1 hR.2
        refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2)]
          exact hΦ2 Φ hP
        · simp only [exEnd, execEndHA, ho]
          exact hR2
      · exact ⟨M₁, .zurueck σ₂ v, hs, fun Φ hP => by simp only [execEndHA, hΦ Φ hP],
          by simp only [exEnd, execEndHA, ho]; exact hR⟩
      · exact ⟨M₁, .why σ₂ r, hs, fun Φ hP => by simp only [execEndHA, hΦ Φ hP],
          by simp only [exEnd, execEndHA, ho]; exact hR⟩
      · exact ⟨M₁, .leave h₂ σ₂ ρ₂, hs, fun Φ hP => by simp only [execEndHA, hΦ Φ hP],
          by simp only [exEnd, execEndHA, ho]; exact hR⟩
      · exact ⟨M₁, .next h₂ σ₂ ρ₂, hs, fun Φ hP => by simp only [execEndHA, hΦ Φ hP],
          by simp only [exEnd, execEndHA, ho]; exact hR⟩
      · exact ⟨M₁, .logik e, hs, fun Φ hP => by simp only [execEndHA, hΦ Φ hP],
          by simp only [exEnd, execEndHA, ho]; exact hR⟩
      · exact ⟨M₁, .hardware e, hs, fun Φ hP => by simp only [execEndHA, hΦ Φ hP],
          by simp only [exEnd, execEndHA, ho]; exact hR⟩
  | .bind e rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_end rest M₁ σ₁ _ (.cons (eval σ₁ e σ₁ ρ) ρ)
        (.cons (eval (leseA A' σ' (Λ.map E.resE) (e.orte.map E.ortE)) (exE E e) (leseA A' σ' (Λ.map E.resE) (e.orte.map E.ortE)) ρ') ρ') hI (E.envR_cons hZ hρ _ _ rfl (hev e ρ ρ' hρ))
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, hΦ Φ (passt_teil hP hs2)]
        exact congrArg EndAusgang.schrumpf (hΦ2 Φ hP)
      · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
        exact E.endRel_schrumpf hR
  | .bindCall (τ := τ) f args he hp hr rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (evalArgs σ₁ args σ₁ ρ) (E.fn f)
        (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ'))
        ((E.envR_um hZ (paramsE hS f) _ _).mpr (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)) (Or.inl rfl)
      generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
        (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ')) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · have he' : D'.erg (E.fn f) = some (E.tyE τ) := by rw [← ergE_fn hS, he]; rfl
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_end rest M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (ergWert he (E.ergZ hZ (D.erg f) (castV (ergE_fn hS f).symm v'))) ρ)
          (.cons (ergWert he' v') ρ')
          (hI2 W)
          (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergZ hZ (ergE_fn hS f) he he' v'))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
        · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha,
            execEnd_umΛ]
          exact E.endRel_schrumpf hR3
      · exact (Fin.cast (by rw [gruendeE hS, hr]) r' : Fin 0).elim0
      · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
          exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
          trivial
  | .bindCallInd (n := n) (τ := τ) p args he hp hr rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (p.orte ++ args.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      rcases hvd : eval σ₁ p σ₁ ρ with ⟨f, hf⟩
      have hp' := hev p ρ ρ' hρ
      rw [hvd] at hp'
      rcases hvd' : eval (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exE E p) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ' with ⟨f', hf'⟩
      rw [hvd'] at hp'
      have hk : E.Konform hZ f f' := by
        rcases hp' with h | ⟨hz, hr⟩
        · exact Or.inl h
        · exact Or.inr ⟨n, hz, hr, hf'⟩
      have hsig : (D.sigNr n).params.map E.tyE = (D'.sigNr (E.num n)).params := by rw [hS.sigNr]; rfl
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (umsig hf (evalArgs σ₁ args σ₁ ρ)) f'
        (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ')))
        (E.envR_umsig hZ hf hf' _ _ ((E.envR_um hZ hsig _ _).mpr
          (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ))) hk
      generalize ha : R' f' (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ'))) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · have he₁ : D.erg f = some τ := ergSig hf he
        have heS : (D'.sigNr (E.num n)).erg = some (E.tyE τ) := by
          rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl
        have he' : D'.erg f' = some (E.tyE τ) := ergSig hf' heS
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_end rest M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (ergWert he₁ (E.ergZ hZ (D.erg f) (castV (konform_sig hS hk).2.1 v'))) ρ)
          (.cons (ergWert he' v') ρ')
          (hI2 W)
          (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergZ hZ (konform_sig hS hk).2.1.symm he₁ he' v'))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hvd, hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
        · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha,
            execEnd_umΛ]
          exact E.endRel_schrumpf hR3
      · have h0 : D'.gruende f' = 0 := (konform_sig hS hk).2.2.trans ((D.passt_sig hf).gruende.trans hr)
        exact (Fin.cast h0 r').elim0
      · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
        · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
          exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
        · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
          trivial
  | .bindCallElse (τ := τ) f args he hp hr err rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (evalArgs σ₁ args σ₁ ρ) (E.fn f)
        (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ'))
        ((E.envR_um hZ (paramsE hS f) _ _).mpr (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)) (Or.inl rfl)
      generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
        (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ')) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · have he' : D'.erg (E.fn f) = some (E.tyE τ) := by rw [← ergE_fn hS, he]; rfl
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_end rest M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (ergWert he (E.ergZ hZ (D.erg f) (castV (ergE_fn hS f).symm v'))) ρ)
          (.cons (ergWert he' v') ρ')
          (hI2 W)
          (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergZ hZ (ergE_fn hS f) he he' v'))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
        · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha,
            execEnd_umΛ]
          exact E.endRel_schrumpf hR3
      · have hc : (Ty.why (D.gruende f) :: Γ).map E.tyE = Ty.why (D'.gruende (E.fn f)) :: Γ.map E.tyE := by
          rw [gruendeE hS]; rfl
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_end err M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (Fin.cast (gruendeE hS f) r') ρ) (castE hc.symm (.cons r' ρ'))
          (hI2 W)
          ((E.envR_um hZ hc.symm _ _).mpr (E.envR_cons hZ hρ _ _ (by rw [gruendeE hS])
            (by rw [castW_why]; rfl)))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
        · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha,
            execEnd_umΓ, execEnd_umΛ]
          exact E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR3)
      · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
          exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
          trivial
  | .bindAxiom (τ := τ) a args he hw hg hd hgd rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, hs2, hOΦ, hI2⟩ := E.ax_schluessel hZ pad O' hI a (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.envR_eq_frei hZ (hZ.frei.aparamsFrei a) _ _ (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)
      have hw' := E.axiom_wert hZ (fun _ => Option.none) O'.zeiger a (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 (E.aerg a)
      have he' : D'.aerg (E.ax a) = some (E.tyE τ) := by rw [E.aerg, he]; rfl
      cases hx : einpassenErg (fun _ => Option.none) (D.aerg a) (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 with
      | none =>
          refine ⟨M₂, .hardware (.annahme a), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execEndHA, axiomAntwort, hΦ Φ (passt_teil hP hs2), hOΦ Φ hP, orakelΦ_zeiger]
            rw [hx]
          · simp only [exEnd, execEndHA, axiomAntwort, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
              evalArgs_umτs, hargs, aparamsUm_falt, hw']
            rw [hx]
            trivial
      | some v =>
          obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_end rest M₂ (E.antwortWelt hZ pad σ₁ (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1) (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1
            (.cons (ergWert he v) ρ) (.cons (ergWert he' (castV (E.aerg a).symm (E.ergE _ v))) ρ')
            (E.inv_antwort hZ hB.pad hI2 _) (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergE hZ (E.aerg a) he he' v))
          refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
          · simp only [execEndHA, axiomAntwort, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)),
              hOΦ Φ (passt_teil hP hs3), orakelΦ_zeiger]
            rw [hx]
            exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
          · simp only [exEnd, execEndHA, axiomAntwort, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
              evalArgs_umτs, hargs, aparamsUm_falt, hw']
            rw [hx]
            exact E.endRel_schrumpf hR3
  | .bindAxiomElse (τ := τ) a args he hr hw hg hd hgd err rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, hs2, hOΦ, hI2⟩ := E.ax_schluessel hZ pad O' hI a (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.envR_eq_frei hZ (hZ.frei.aparamsFrei a) _ _ (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)
      have hw' := E.axiomSonst_wert hZ (fun _ => Option.none) O'.zeiger a (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 (E.aerg a) (E.agruende a)
      have he' : D'.aerg (E.ax a) = some (E.tyE τ) := by rw [E.aerg, he]; rfl
      rcases hx : sonstPasst (fun _ => Option.none) (D.aerg a) (D.agruende a) (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 with _ | (v | r)
      · refine ⟨M₂, .hardware (.annahme a), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, axiomAntwortSonst, hΦ Φ (passt_teil hP hs2), hOΦ Φ hP, orakelΦ_zeiger]
          rw [hx]
        · simp only [exEnd, execEndHA, axiomAntwortSonst, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
            evalArgs_umτs, hargs, aparamsUm_falt, hw']
          rw [hx]
          trivial
      · obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_end rest M₂ (E.antwortWelt hZ pad σ₁ (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1) (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1
          (.cons (ergWert he v) ρ) (.cons (ergWert he' (castV (E.aerg a).symm (E.ergE _ v))) ρ')
          (E.inv_antwort hZ hB.pad hI2 _) (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergE hZ (E.aerg a) he he' v))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, axiomAntwortSonst, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)),
            hOΦ Φ (passt_teil hP hs3), orakelΦ_zeiger]
          rw [hx]
          exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
        · simp only [exEnd, execEndHA, axiomAntwortSonst, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
            evalArgs_umτs, hargs, aparamsUm_falt, hw']
          rw [hx]
          exact E.endRel_schrumpf hR3
      · have hc : (Ty.why (D.agruende a) :: Γ).map E.tyE = Ty.why (D'.agruende (E.ax a)) :: Γ.map E.tyE := by
          rw [E.agruende]; rfl
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_end err M₂ (E.antwortWelt hZ pad σ₁ (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1) (O'.wirkt (E.ax a) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1
          (.cons r ρ) (castE hc.symm (.cons (Fin.cast (E.agruende a).symm r) ρ'))
          (E.inv_antwort hZ hB.pad hI2 _)
          ((E.envR_um hZ hc.symm _ _).mpr (E.envR_cons hZ hρ _ _ (by rw [E.agruende])
            (by rw [castW_why]; exact Fin.ext rfl)))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, axiomAntwortSonst, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)),
            hOΦ Φ (passt_teil hP hs3), orakelΦ_zeiger]
          rw [hx]
          exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
        · simp only [exEnd, execEndHA, axiomAntwortSonst, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
            evalArgs_umτs, hargs, aparamsUm_falt, hw']
          rw [hx]
          simp only [execEnd_umΓ]
          exact E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR3)
  | .regRead r hk rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨hk1, hs1, hΦ1⟩ := E.schluessel hM
      have hw' := E.regLies_wert hZ (fun _ => Option.none) O'.zeiger r (O'.regLies (E.reg r) σ') (E.rtyp r)
      have hc : (D.rtyp r :: Γ).map E.tyE = D'.rtyp (E.reg r) :: Γ.map E.tyE := by
        rw [List.map_cons, E.rtyp]
      cases hx : einpassen (fun _ => Option.none) (D.rtyp r) (O'.regLies (E.reg r) σ') with
      | none =>
          refine ⟨_, .hardware (.register r), hs1, fun Φ hP => ?_, ?_⟩
          · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ hP]
            rw [hx]
          · simp only [exEnd, execEndHA]
            rw [hw'.1 hx]
            trivial
      | some v =>
          have hz := hS.rzusage r v
          cases hzv : D.rzusage r v
          · refine ⟨_, .hardware (.geraet r), hs1, fun Φ hP => ?_, ?_⟩
            · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ hP]
              rw [hx]
              simp only [hzv, Bool.false_eq_true, ↓reduceIte]
            · simp only [exEnd, execEndHA]
              rw [hw'.2 v hx]
              simp only [hz, hzv, Bool.false_eq_true, ↓reduceIte]
              trivial
          · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := E.endSim_end_um hZ S' O' U' A' passes R' hc _ _ (sim_end rest)
              _ σ σ' (.cons v ρ) (.cons ((E.rtyp r).symm ▸ E.valE _ v) ρ') hk1
              (E.envR_cons hZ hρ _ _ (E.rtyp r) (E.vrel_um hZ (E.rtyp r) (E.vrel_valE hZ _ v)))
            refine ⟨M₂, o.schrumpf, teil_trans hs1 hs2, fun Φ hP => ?_, ?_⟩
            · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ (passt_teil hP hs2)]
              rw [hx]
              simp only [hzv, ↓reduceIte]
              exact congrArg EndAusgang.schrumpf (hΦ2 Φ hP)
            · simp only [exEnd, execEndHA]
              rw [hw'.2 v hx]
              simp only [hz, hzv, ↓reduceIte]
              exact E.endRel_schrumpf hR
  | .regReadElse r hk zusage sonst rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨hk1, hs1, hΦ1⟩ := E.schluessel hM
      have hw' := E.regLies_wert hZ (fun _ => Option.none) O'.zeiger r (O'.regLies (E.reg r) σ') (E.rtyp r)
      have hc : (D.rtyp r :: Γ).map E.tyE = D'.rtyp (E.reg r) :: Γ.map E.tyE := by
        rw [List.map_cons, E.rtyp]
      cases hx : einpassen (fun _ => Option.none) (D.rtyp r) (O'.regLies (E.reg r) σ') with
      | none =>
          refine ⟨_, .hardware (.register r), hs1, fun Φ hP => ?_, ?_⟩
          · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ hP]
            rw [hx]
          · simp only [exEnd, execEndHA]
            rw [hw'.1 hx]
            trivial
      | some v =>
          obtain ⟨M₂, σ₁, hs2, hΦ2, hI, hev⟩ := E.lese_eval hZ hk1 T hB.havocA hB.atom Λ (Λ.map E.resE)
            zusage.orte
          have hev0 := E.frei_alle hZ (@hev) hρ
          have hrel := (E.envR_um hZ hc.symm (.cons v ρ)
              (.cons ((E.rtyp r).symm ▸ E.valE _ v) ρ' : Env D' (D'.rtyp (E.reg r) :: Γ.map E.tyE))).mpr
              (E.envR_cons hZ hρ _ _ (E.rtyp r) (E.vrel_um hZ (E.rtyp r) (E.vrel_valE hZ _ v)))
          have hz' := E.frei_eq hZ (hev zusage _ _ hrel) rfl
          cases hb : wahr? (eval σ₁ zusage σ₁ (.cons v ρ))
          · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := sim_end sonst M₂ σ₁ _ ρ ρ' hI hρ
            refine ⟨M₃, o, teil_trans (teil_trans hs1 hs2) hs3, fun Φ hP => ?_, ?_⟩
            · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger,
                hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3))]
              rw [hx]
              simp only [hΦ2 Φ (passt_teil hP hs3), hb, Bool.false_eq_true, ↓reduceIte]
              exact hΦ3 Φ hP
            · simp only [exEnd, execEndHA]
              rw [hw'.2 v hx]
              simp only [Expr.orte_umΓ, Einbettung.orte_exE, eval_umΓ, hz', wahr_valE, hb,
                Bool.false_eq_true, ↓reduceIte]
              exact hR
          · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := E.endSim_end_um hZ S' O' U' A' passes R' hc _ _ (sim_end rest)
              M₂ σ₁ _ (.cons v ρ) (.cons ((E.rtyp r).symm ▸ E.valE _ v) ρ') hI
              (E.envR_cons hZ hρ _ _ (E.rtyp r) (E.vrel_um hZ (E.rtyp r) (E.vrel_valE hZ _ v)))
            refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs1 hs2) hs3, fun Φ hP => ?_, ?_⟩
            · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger,
                hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3))]
              rw [hx]
              simp only [hΦ2 Φ (passt_teil hP hs3), hb, ↓reduceIte]
              exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
            · simp only [exEnd, execEndHA]
              rw [hw'.2 v hx]
              simp only [Expr.orte_umΓ, Einbettung.orte_exE, eval_umΓ, hz', wahr_valE, hb, ↓reduceIte]
              exact E.endRel_schrumpf hR
  | .awaits g payload hp hL hat rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T hM hB.havocA hB.atom Λ (Λ.map E.resE)
        [Sum.inr g] [Sum.inr (E.glob g)] rfl
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨hk2, hs2, hΦ2⟩ := E.schluessel hI
      have hc : (D.gtyp g :: Γ).map E.tyE = D'.gtyp (E.glob g) :: Γ.map E.tyE := by
        rw [List.map_cons, E.gtyp]
      have hzf := hZ.frei.atomFrei g hat
      cases hvis : O'.sichtbar (E.glob g) (leseA A' σ' (Λ.map E.resE) [Sum.inr (E.glob g)])
      · refine ⟨_, .hardware (.sichtbarkeit D.a10), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), orakelΦ_sichtbar, hzf, hΦ2 Φ hP, hvis,
            Bool.false_eq_true, ↓reduceIte]
        · simp only [exEnd, execEndHA, hvis, Bool.false_eq_true, ↓reduceIte]
          trivial
      · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := E.endSim_end_um hZ S' O' U' A' passes R' hc _ _ (sim_end rest)
          _ σ₁ _ (.cons (σ₁.globs g) ρ) (.cons ((leseA A' σ' (Λ.map E.resE) [Sum.inr (E.glob g)]).globs
            (E.glob g)) ρ') hk2 (E.envR_cons hZ hρ _ _ (E.gtyp g) (hk2.treu.2 g))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), orakelΦ_sichtbar, hzf,
            hΦ2 Φ (passt_teil hP hs3), hvis, ↓reduceIte]
          exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
        · simp only [exEnd, execEndHA, hvis, ↓reduceIte]
          exact E.endRel_schrumpf hR


/-- **Arms beside their images.** -/
theorem sim_arms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → ∀ w : Wert D (.sum cs),
    E.KoerperSim hZ (fun Φ => execArmsHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') a w)
      (execArmsHA S' O' U' A' passes R' (exArms hS a) (E.valE _ w))
  | .nil, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | .cons (c := none) b _, ⟨⟨0, _⟩, nutz⟩ => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o, hs, hΦ, hR⟩ := sim_block b M σ σ' ρ ρ' hM hρ
      exact ⟨M₁, o, hs, fun Φ hP => by
          simp only [execArmsHA, armEnv, Ausgang.schrumpfArm]; exact hΦ Φ hP,
        by simp only [exArms, valE_sum, execArmsHA, armEnv, Ausgang.schrumpfArm]; exact hR⟩
  | .cons (c := some (lo, hi)) b _, ⟨⟨0, _⟩, nutz⟩ => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o, hs, hΦ, hR⟩ := sim_block b M σ σ' (Env.cons (τ := .int lo hi) nutz ρ)
        (Env.cons (τ := .int lo hi) nutz ρ') hM
        (E.envR_cons hZ (τ := .int lo hi) (τ' := .int lo hi) hρ nutz nutz rfl rfl)
      exact ⟨M₁, o.schrumpf, hs, fun Φ hP => by
          simp only [execArmsHA, armEnv, Ausgang.schrumpfArm]; exact congrArg Ausgang.schrumpf (hΦ Φ hP),
        by simp only [exArms, valE_sum, execArmsHA, armEnv, Ausgang.schrumpfArm]
           exact E.ausRel_schrumpf hR⟩
  | .cons (c := none) _ rest, ⟨⟨i + 1, h⟩, nutz⟩ => by
      have := sim_arms rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o, hs, hΦ, hR⟩ := this M σ σ' ρ ρ' hM hρ
      exact ⟨M₁, o, hs, fun Φ hP => by simp only [execArmsHA]; exact hΦ Φ hP,
        by simp only [exArms, valE_sum, execArmsHA]; exact hR⟩
  | .cons (c := some (lo, hi)) _ rest, ⟨⟨i + 1, h⟩, nutz⟩ => by
      have := sim_arms rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o, hs, hΦ, hR⟩ := this M σ σ' ρ ρ' hM hρ
      exact ⟨M₁, o, hs, fun Φ hP => by simp only [execArmsHA]; exact hΦ Φ hP,
        by simp only [exArms, valE_sum, execArmsHA]; exact hR⟩

/-- **Reason arms beside their images.** -/
theorem sim_grund {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → ∀ r : Fin n,
    E.KoerperSim hZ (fun Φ => execGrundHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') a r)
      (execGrundHA S' O' U' A' passes R' (exGArms hS a) r)
  | .nil, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | .cons b _, ⟨0, _⟩ => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o, hs, hΦ, hR⟩ := sim_block b M σ σ' ρ ρ' hM hρ
      exact ⟨M₁, o, hs, fun Φ hP => by simp only [execGrundHA]; exact hΦ Φ hP,
        by simp only [exGArms, execGrundHA]; exact hR⟩
  | .cons _ rest, ⟨i + 1, h⟩ => by
      have := sim_grund rest ⟨i, Nat.lt_of_succ_lt_succ h⟩
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o, hs, hΦ, hR⟩ := this M σ σ' ρ ρ' hM hρ
      exact ⟨M₁, o, hs, fun Φ hP => by simp only [execGrundHA]; exact hΦ Φ hP,
        by simp only [exGArms, execGrundHA]; exact hR⟩

end

end Sim

end Einbettung

end Gabbro.Grammatik.Einbettung
