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

theorem paramsUm_falt (hS : E.SigTreu) (f : D.Fn) (ρ : Env D (D.params f)) :
    castE (paramsE hS f) (E.envE ρ) = E.paramsUm hS f ρ := rfl

theorem aparamsUm_falt (a : D.Ax) (ρ : Env D (D.aparams a)) :
    castE (E.aparams a).symm (E.envE ρ) = E.aparamsUm a ρ := rfl

variable (hZ : ZeigerfreiD D) (hS : E.SigTreu) (pad : List (Ereignis D)) (S : SperrInv D)
  (T : D.Tab ⊕ D.Glob → Prop) (S' : SperrInv D') (T' : D'.Tab ⊕ D'.Glob → Prop) (O' : Orakel D')
  (U' : Umwelt D') (A' : AUmwelt D') (passes : Nat)
  (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f)

/-- A call through the keys: the induced handler answers as the `D'`-handler at the key. -/
theorem ruf_schluessel {M : List (World D × World D')} {σ : World D} {σ' : World D'}
    (h : E.Inv M σ σ') (g : D.Fn) (ρa : Env D (D.params g)) :
    ∃ M₁ : List (World D × World D'), (∀ p ∈ M, p ∈ M₁) ∧
      (∀ Φ, Passt Φ M₁ → E.rufΦ hZ hS pad Φ R' g σ ρa =
        E.antwortR hZ hS pad g σ (R' (E.fn g) σ' (castE (paramsE hS g) (E.envE ρa)))) ∧
      E.Inv M₁ σ σ' := by
  obtain ⟨hk, hs, hΦ⟩ := E.schluessel h
  exact ⟨_, hs, fun Φ hP => by simp only [rufΦ, paramsUm, hΦ Φ hP], hk⟩

/-- An axiom through the keys. -/
theorem ax_schluessel {M : List (World D × World D')} {σ : World D} {σ' : World D'}
    (h : E.Inv M σ σ') (a : D.Ax) (ρa : Env D (D.aparams a)) :
    ∃ M₁ : List (World D × World D'), (∀ p ∈ M, p ∈ M₁) ∧
      (∀ Φ, Passt Φ M₁ → (E.orakelΦ hZ pad Φ O').wirkt a σ ρa =
        (E.antwortWelt hZ pad σ (O'.wirkt (E.ax a) σ' (E.aparamsUm a ρa)).1,
          (O'.wirkt (E.ax a) σ' (E.aparamsUm a ρa)).2)) ∧ E.Inv M₁ σ σ' := by
  obtain ⟨hk, hs, hΦ⟩ := E.schluessel h
  exact ⟨_, hs, fun Φ hP => by simp only [orakelΦ, hΦ Φ hP], hk⟩

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

/-- The arguments of an indirect call, on both sides. -/
theorem umsig_E (hS : E.SigTreu) {f : D.Fn} {n : Nat} (hf : D.passt f n = true)
    (hf' : D'.passt (E.fn f) (E.num n) = true)
    (h : (D.sigNr n).params.map E.tyE = (D'.sigNr (E.num n)).params) (x : Env D (D.sigNr n).params) :
    umsig hf' (castE h (E.envE x)) = E.paramsUm hS f (umsig hf x) := by
  apply eq_of_heq
  refine (umsig_heq hf' _).trans ((castE_heq h _).trans ?_)
  show HEq (E.envE x) (castE (paramsE hS f) (E.envE (umsig hf x)))
  refine HEq.trans ?_ (castE_heq _ _).symm
  exact E.envE_heq (D.passt_sig hf).params.symm x (umsig hf x) (umsig_heq hf x).symm

/-- A slot read through a type equation, on both sides. -/
theorem zahl_cast_n {T T' : Ty} {lo hi : Int} (hτ : T = .int lo hi) (hτ' : T' = .int lo hi)
    (e : T' = E.tyE T) (x : Wert D T) (x' : Wert D' T') (hx : castW e x' = E.valE T x) :
    (hτ' ▸ x' : Zahl _ _).n = (hτ ▸ x : Zahl _ _).n := by
  subst hτ; subst hτ'
  exact congrArg Zahl.n hx

/-- A state value written through a type equation, on both sides. -/
theorem zahl_cast_wert {T T' : Ty} {lo hi : Int} (hτ : T = .int lo hi) (hτ' : T' = .int lo hi)
    (e : T' = E.tyE T) (z : Zahl lo hi) :
    castW e (hτ' ▸ (z : Zahl _ _)) = E.valE T (hτ ▸ (z : Zahl _ _)) := by
  subst hτ; subst hτ'; rfl

theorem logikRel_kein {e : Logik D} {e' : Logik D'} (h : ∀ g', e' ≠ .vorbedingung g') :
    E.LogikRel e e' := fun g' he => absurd he (h g')

theorem wahr_valE (v : Wert D .bool) : wahr? (D := D') (E.valE .bool v) = wahr? v := rfl

theorem zelle_valE {n : Nat} (v : Wert D (.ref n)) : (E.valE (.ref n) v).zelle = v.zelle := rfl

@[simp] theorem valE_ref {n : Nat} (v : Wert D (.ref n)) : E.valE (.ref n) v = v := rfl

theorem orakelΦ_regLies (Φ : World D → World D') (r : D.Reg) (σ : World D) :
    (E.orakelΦ hZ pad Φ O').regLies r σ = O'.regLies (E.reg r) (Φ σ) := rfl

theorem orakelΦ_sichtbar (Φ : World D → World D') (g : D.Glob) (σ : World D) :
    (E.orakelΦ hZ pad Φ O').sichtbar g σ = O'.sichtbar (E.glob g) (Φ σ) := rfl

theorem orakelΦ_zeiger (Φ : World D → World D') :
    (E.orakelΦ hZ pad Φ O').zeiger = fun _ => Option.none := rfl

/-- A block whose image is transported along its scope. -/
theorem koerperSim_block_um {V : Vertrag D} {l : Bool} {Δ : Ctx} {Δ₁ Δ₂ : Ctx}
    {Λ₁ Λ₂ : List (Res D')} (h : Δ₁ = Δ₂)
    (lauf : (World D → World D') → World D → Env D Δ → Ausgang V l Δ)
    (b : Block D' (E.vertragE V) l Δ₁ Λ₁ Λ₂)
    (hs : E.KoerperSim lauf (execBlockHA S' O' U' A' passes R' b)) :
    E.KoerperSim lauf (execBlockHA S' O' U' A' passes R' (Block.umΓ h b)) := by
  intro M σ σ' ρ ρ' hI hρ
  obtain ⟨M₁, o, hs1, hΦ, hR⟩ := hs M σ σ' ρ (castE h.symm ρ') hI ((E.envR_um h.symm ρ ρ').mpr hρ)
  refine ⟨M₁, o, hs1, hΦ, ?_⟩
  rw [execBlock_umΓ]
  exact (E.ausRel_um h o _).mpr hR

/-- An end block whose image is transported along its scope. -/
theorem endSim_end_um {V : Vertrag D} {l : Bool} {Δ : Ctx} {Δ₁ Δ₂ : Ctx}
    {Λ₁ : List (Res D')} (h : Δ₁ = Δ₂)
    (lauf : (World D → World D') → World D → Env D Δ → EndAusgang V l Δ)
    (b : Endblock D' (E.vertragE V) l Δ₁ Λ₁)
    (hs : E.EndSim lauf (execEndHA S' O' U' A' passes R' b)) :
    E.EndSim lauf (execEndHA S' O' U' A' passes R' (Endblock.umΓ h b)) := by
  intro M σ σ' ρ ρ' hI hρ
  obtain ⟨M₁, o, hs1, hΦ, hR⟩ := hs M σ σ' ρ (castE h.symm ρ') hI ((E.envR_um h.symm ρ ρ').mpr hρ)
  refine ⟨M₁, o, hs1, hΦ, ?_⟩
  rw [execEnd_umΓ]
  exact (E.endRel_um h o _).mpr hR

section Sim

variable (hB : E.Bed hZ pad S T S' T' U' A' R')
include hB

set_option maxHeartbeats 4000000 in
mutual

/-- **A statement beside its image.** -/
theorem sim_stmt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') →
    E.KoerperSim (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') s)
      (execStmtHA S' O' U' A' passes R' (exS hS s))
  | .assignSlot t f i e hw hL => by
      intro M σ σ' ρ ρ' h hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ h T hB.havocA hB.atom Λ (Λ.map E.resE)
        (i.orte ++ e.orte)
      refine ⟨M₁, .ok (σ₁.schreibSlot t Λ (eval σ₁ i σ₁ ρ).n f (eval σ₁ e σ₁ ρ)) ρ, hs,
        fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, hev, castW_index_n, valE_index_n]
        exact ⟨hI.schreibSlot E t Λ _ _ f _ _ (castW_symm (E.typ t f) _), E.envR_envE ρ⟩
  | .assignVar x e => by
      intro M σ σ' ρ ρ' h hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ h T hB.havocA hB.atom Λ (Λ.map E.resE) e.orte
      refine ⟨M₁, .ok σ₁ (ρ.set x (eval σ₁ e σ₁ ρ)), hs, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, E.envE_set]
        exact ⟨hI, E.envR_envE _⟩
  | .assignThru p t ht f i e hw hL => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (p.orte ++ i.orte ++ e.orte)
      refine ⟨M₁, .ok (σ₁.schreibSlot t Λ (eval σ₁ i σ₁ ρ).n f (eval σ₁ e σ₁ ρ)) ρ, hs,
        fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev]
        exact ⟨hI.schreibSlot E t Λ _ _ f _ _ (castW_symm (E.typ t f) _), E.envR_envE ρ⟩
  | .assignSlotRef r t ht ho f e hw hL => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (r.orte ++ e.orte)
      refine ⟨M₁, .ok (σ₁.schreibSlot t Λ ((eval σ₁ r σ₁ ρ).zelle : Int) f (eval σ₁ e σ₁ ρ)) ρ, hs,
        fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev, zelle_valE]
        exact ⟨hI.schreibSlot E t Λ _ _ f _ _ (castW_symm (E.typ t f) _), E.envR_envE ρ⟩
  | .assignGlob g e hw hL => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      refine ⟨M₁, .ok (σ₁.schreibGlob g Λ (eval σ₁ e σ₁ ρ)) ρ, hs, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev]
        exact ⟨hI.schreibGlob E g Λ _ _ _ (castW_symm (E.gtyp g) _), E.envR_envE ρ⟩
  | .putBytes t f hf n i hlo hhi e hw hL => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (i.orte ++ e.orte)
      refine ⟨M₁, .ok (σ₁.schreibBytes t f hf Λ (eval σ₁ i σ₁ ρ).n (zahlZuBytes n (eval σ₁ e σ₁ ρ).n)) ρ,
        hs, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev, valE_int]
        exact ⟨hI.schreibBytes E t f hf _ Λ _ _ _, E.envR_envE ρ⟩
  | .shift t f hτ i von nach hn he hw hL => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (Sum.inl t :: i.orte)
      have hn' := E.zahl_cast_n hτ ((E.typ t f).trans (by rw [hτ])) (E.typ t f)
        (σ₁.slots t (eval σ₁ i σ₁ ρ).n f) _ (hI.treu.1 t (eval σ₁ i σ₁ ρ).n f)
      by_cases hc : (hτ ▸ σ₁.slots t (eval σ₁ i σ₁ ρ).n f : Zahl _ _).n = von
      · refine ⟨M₁, .ok (σ₁.schreibSlot t Λ (eval σ₁ i σ₁ ρ).n f (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))) ρ,
          hs, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ hP]
          rw [if_pos hc]
        · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev]
          rw [if_pos (hn'.trans hc)]
          exact ⟨hI.schreibSlot E t Λ _ _ f _ _ (E.zahl_cast_wert hτ ((E.typ t f).trans (by rw [hτ])) (E.typ t f) _), E.envR_envE ρ⟩
      · refine ⟨M₁, .logik .vorzustand, hs, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ hP]
          rw [if_neg hc]
        · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev]
          rw [if_neg (fun h' => hc (hn'.symm.trans h'))]
          exact E.logikRel_kein (fun _ h' => by cases h')
  | .ite c t e => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (c.orte)
      cases hb : wahr? (eval σ₁ c σ₁ ρ)
      · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block e M₁ σ₁ _ ρ (E.envE ρ) hI (E.envR_envE ρ)
        refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hb, Bool.false_eq_true, ↓reduceIte]
          exact hΦ2 Φ hP
        · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, wahr_valE, hb, Bool.false_eq_true, ↓reduceIte]
          exact hR
      · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block t M₁ σ₁ _ ρ (E.envE ρ) hI (E.envR_envE ρ)
        refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hb, ↓reduceIte]
          exact hΦ2 Φ hP
        · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, wahr_valE, hb, ↓reduceIte]
          exact hR
  | .onOption (n := n) o p a => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (o.orte)
      cases hv : eval σ₁ o σ₁ ρ with
      | none =>
          obtain ⟨M₂, o', hs2, hΦ2, hR⟩ := sim_block a M₁ σ₁ _ ρ (E.envE ρ) hI (E.envR_envE ρ)
          refine ⟨M₂, o', teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hv]
            exact hΦ2 Φ hP
          · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, valE_opt, hv]
            exact hR
      | some k =>
          obtain ⟨M₂, o', hs2, hΦ2, hR⟩ := sim_block p M₁ σ₁ _ (Env.cons (τ := Ty.index n) k ρ)
            (Env.cons (τ := Ty.index n) k (E.envE ρ)) hI (E.envR_envE (Env.cons (τ := Ty.index n) k ρ))
          refine ⟨M₂, o'.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hv]
            exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
          · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, valE_opt, hv]
            exact E.ausRel_schrumpf hR
  | .onTag v arms => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (v.orte)
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_arms arms (eval σ₁ v σ₁ ρ) M₁ σ₁ _ ρ (E.envE ρ) hI (E.envR_envE ρ)
      refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2)]
        exact hΦ2 Φ hP
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev]
        exact hR
  | .onWhy r arms => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (r.orte)
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_grund arms (eval σ₁ r σ₁ ρ) M₁ σ₁ _ ρ (E.envE ρ) hI (E.envR_envE ρ)
      refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2)]
        exact hΦ2 Φ hP
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, valE_why]
        exact hR
  | .call f args hp hr => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schluessel hZ hS pad R' hI f (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.evalArgs_exA hI.treu hI.treu args ρ
      generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
        (castE (paramsE hS f) (E.envE (evalArgs σ₁ args σ₁ ρ))) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · refine ⟨M₂, .ok (E.antwortWelt hZ pad σ₁ W) ρ, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, evalArgs_umτs, hargs, ha]
          exact ⟨E.inv_antwort hZ hB.pad hI2 W, E.envR_envE ρ⟩
      · exact (Fin.cast (by rw [gruendeE hS, hr]) r' : Fin 0).elim0
      · refine ⟨M₂, .logik (E.logikZ e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, evalArgs_umτs, hargs, ha]
          exact E.logikRel_logikZ (fun g' he' => hB.vorb f _ _ g' (ha.trans (congrArg RufAusgang.logik he')))
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, evalArgs_umτs, hargs, ha]
          trivial
  | .callInd (n := n) p args hp hr => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (p.orte ++ args.orte)
      rcases hvd : eval σ₁ p σ₁ ρ with ⟨f, hf⟩
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schluessel hZ hS pad R' hI f (umsig hf (evalArgs σ₁ args σ₁ ρ))
      have hargs := E.evalArgs_exA hI.treu hI.treu args ρ
      have hp' := hev p ρ
      rw [hvd] at hp'
      generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE))
        (castE (paramsE hS f) (E.envE (umsig hf (evalArgs σ₁ args σ₁ ρ)))) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · refine ⟨M₂, .ok (E.antwortWelt hZ pad σ₁ W) ρ, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
        · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hp', valE, evalArgs_umτs, hargs,
            E.umsig_E hS hf, paramsUm, ha]
          exact ⟨E.inv_antwort hZ hB.pad hI2 W, E.envR_envE ρ⟩
      · have h0 : D'.gruende (E.fn f) = 0 := by
          rw [gruendeE hS]; exact (D.passt_sig hf).gruende.trans hr
        exact (Fin.cast h0 r').elim0
      · refine ⟨M₂, .logik (E.logikZ e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
        · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hp', valE, evalArgs_umτs, hargs,
            E.umsig_E hS hf, paramsUm, ha]
          exact E.logikRel_logikZ (fun g' he' => hB.vorb f _ _ g' (ha.trans (congrArg RufAusgang.logik he')))
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
        · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hp', valE, evalArgs_umτs, hargs,
            E.umsig_E hS hf, paramsUm, ha]
          trivial
  | .locks L hr body => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI⟩ := E.umwelt_schritt hZ hM S hB.havocU hB.orte L
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block body M₁ (σ₁.nimmt L) _ ρ (E.envE ρ)
        (hI.nimmt E L (E.lock L)) (E.envR_envE ρ)
      refine ⟨M₂, freiH S L o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2)]
        exact congrArg (freiH S L) (hΦ2 Φ hP)
      · simp only [exS, execStmtHA]
        exact E.freiH_rel hZ S hB.inv L hR
  | .breaking i body => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, o, hs, hΦ, hR⟩ := sim_block body M σ σ' ρ (E.envE ρ) hM (E.envR_envE ρ)
      exact ⟨M₁, o, hs, fun Φ hP => by simp only [execStmtHA]; exact hΦ Φ hP,
        by simp only [exS, execStmtHA]; exact hR⟩
  | .traverse t inv body => by
      intro M σ σ' ρ ρ' hM hρ
      have hsb := E.koerperSim_block_um S' O' U' A' passes R'
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
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      obtain ⟨M₂, hs2, hOΦ, hI2⟩ := E.ax_schluessel hZ pad O' hI a (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.evalArgs_exA hI.treu hI.treu args ρ
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
            exact ⟨E.inv_antwort hZ hB.pad hI2 _, E.envR_envE ρ⟩
  | .regWrite r hk e => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      refine ⟨M₁, .ok σ₁ ρ, hs, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr]
        exact ⟨hI, E.envR_envE ρ⟩
  | .transition r hk m hm hl maske bits => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      exact ⟨M, .ok σ ρ, fun _ hp => hp, fun Φ hP => by simp only [execStmtHA],
        by simp only [exS, execStmtHA]; exact ⟨hM, E.envR_envE ρ⟩⟩
  | .publish g e payload hp hw hL => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      refine ⟨M₁, .ok (σ₁.schreibGlob g Λ (eval σ₁ e σ₁ ρ)) ρ, hs, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev]
        exact ⟨hI.schreibGlob E g Λ _ _ _ (castW_symm (E.gtyp g) _), E.envR_envE ρ⟩
  | .advances m a h hs => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      exact ⟨M, .ok σ ρ, fun _ hp => hp, fun Φ hP => by simp only [execStmtHA],
        by simp only [exS, exec_nachΛ, execStmtHA]; exact ⟨hM, E.envR_envE ρ⟩⟩
  | .retires m s h a => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      exact ⟨M, .ok σ ρ, fun _ hp => hp, fun Φ hP => by simp only [execStmtHA],
        by simp only [exS, exec_nachΛ, execStmtHA]; exact ⟨hM, E.envR_envE ρ⟩⟩
  | .ret e hΛ => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T hM hB.havocA hB.atom Λ (Λ.map E.resE)
        e.orte (E.exErg e).orte (E.orte_exErg e).symm
      have he := E.evalErg_exErg hI.treu hI.treu e ρ
      refine ⟨M₁, .zurueck σ₁ (evalErg σ₁ e σ₁ ρ), hs, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP]
      · exact ⟨hI, he⟩
  | .retWhy r hΛ => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      exact ⟨M, .why σ r, fun _ hp => hp, fun Φ hP => by simp only [execStmtHA],
        by simp only [exS, execStmtHA]; exact ⟨hM, rfl⟩⟩
  | .leave h => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      exact ⟨M, .leave h σ ρ, fun _ hp => hp, fun Φ hP => by simp only [execStmtHA],
        by simp only [exS, execStmtHA]; exact ⟨hM, E.envR_envE ρ⟩⟩
  | .next h => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      exact ⟨M, .next h σ ρ, fun _ hp => hp, fun Φ hP => by simp only [execStmtHA],
        by simp only [exS, execStmtHA]; exact ⟨hM, E.envR_envE ρ⟩⟩

/-- **A block beside its image.** -/
theorem sim_block {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') →
    E.KoerperSim (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') b)
      (execBlockHA S' O' U' A' passes R' (exB hS b))
  | .nil => by
      intro M σ σ' ρ ρ' h hρ
      exact ⟨M, .ok σ ρ, fun _ hp => hp, fun _ _ => rfl, h, hρ⟩
  | .cons s rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, o₁, hs, hΦ, hR⟩ := sim_stmt s M σ σ' ρ (E.envE ρ) hM (E.envR_envE ρ)
      generalize ho : execStmtHA S' O' U' A' passes R' (exS hS s) σ' (E.envE ρ) = o₁' at hR
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
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block rest M₁ σ₁ _ (.cons (eval σ₁ e σ₁ ρ) ρ)
        (.cons (E.valE _ (eval σ₁ e σ₁ ρ)) (E.envE ρ)) hI (E.envR_envE (.cons (eval σ₁ e σ₁ ρ) ρ))
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
        exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
      · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev]
        exact E.ausRel_schrumpf hR
  | .bindCall (τ := τ) f args he hp hr rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schluessel hZ hS pad R' hI f (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.evalArgs_exA hI.treu hI.treu args ρ
      generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
        (castE (paramsE hS f) (E.envE (evalArgs σ₁ args σ₁ ρ))) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · have he' : D'.erg (E.fn f) = some (E.tyE τ) := by rw [← ergE_fn hS, he]; rfl
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_block rest M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (ergWert he (E.ergZ (D.erg f) (hZ.erg f) (castV (ergE_fn hS f).symm v'))) ρ)
          (.cons (ergWert he' v') (E.envE ρ))
          (E.inv_antwort hZ hB.pad hI2 W)
          (E.envR_cons (E.envR_envE ρ) _ _ rfl (E.ergWert_ergZ hZ (ergE_fn hS f) he he' (hZ.erg f) v'))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
        · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, hargs, ha,
            execBlock_vorΛ]
          exact E.ausRel_schrumpf hR3
      · exact (Fin.cast (by rw [gruendeE hS, hr]) r' : Fin 0).elim0
      · refine ⟨M₂, .logik (E.logikZ e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, hargs, ha]
          exact E.logikRel_logikZ (fun g' he' => hB.vorb f _ _ g' (ha.trans (congrArg RufAusgang.logik he')))
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, hargs, ha]
          trivial
  | .bindCallInd (n := n) (τ := τ) p args he hp hr rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (p.orte ++ args.orte)
      rcases hvd : eval σ₁ p σ₁ ρ with ⟨f, hf⟩
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schluessel hZ hS pad R' hI f (umsig hf (evalArgs σ₁ args σ₁ ρ))
      have hargs := E.evalArgs_exA hI.treu hI.treu args ρ
      have hp' := hev p ρ
      rw [hvd] at hp'
      generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE))
        (castE (paramsE hS f) (E.envE (umsig hf (evalArgs σ₁ args σ₁ ρ)))) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · have he₁ : D.erg f = some τ := ergSig hf he
        have heS : (D'.sigNr (E.num n)).erg = some (E.tyE τ) := by
          rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl
        have he' : D'.erg (E.fn f) = some (E.tyE τ) := ergSig ((E.passt f n).trans hf) heS
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_block rest M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (ergWert he₁ (E.ergZ (D.erg f) (hZ.erg f) (castV (ergE_fn hS f).symm v'))) ρ)
          (.cons (ergWert he' v') (E.envE ρ))
          (E.inv_antwort hZ hB.pad hI2 W)
          (E.envR_cons (E.envR_envE ρ) _ _ rfl (E.ergWert_ergZ hZ (ergE_fn hS f) he₁ he' (hZ.erg f) v'))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hvd, hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
        · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hp', valE, evalArgs_umτs, hargs, E.umsig_E hS hf, paramsUm, ha,
            execBlock_vorΛ]
          exact E.ausRel_schrumpf hR3
      · have h0 : D'.gruende (E.fn f) = 0 := by
          rw [gruendeE hS]; exact (D.passt_sig hf).gruende.trans hr
        exact (Fin.cast h0 r').elim0
      · refine ⟨M₂, .logik (E.logikZ e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
        · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hp', valE, evalArgs_umτs, hargs, E.umsig_E hS hf, paramsUm, ha]
          exact E.logikRel_logikZ (fun g' he' => hB.vorb f _ _ g' (ha.trans (congrArg RufAusgang.logik he')))
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
        · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hp', valE, evalArgs_umτs, hargs, E.umsig_E hS hf, paramsUm, ha]
          trivial
  | .bindCallElse (τ := τ) f args he hp hr err rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schluessel hZ hS pad R' hI f (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.evalArgs_exA hI.treu hI.treu args ρ
      generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
        (castE (paramsE hS f) (E.envE (evalArgs σ₁ args σ₁ ρ))) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · have he' : D'.erg (E.fn f) = some (E.tyE τ) := by rw [← ergE_fn hS, he]; rfl
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_block rest M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (ergWert he (E.ergZ (D.erg f) (hZ.erg f) (castV (ergE_fn hS f).symm v'))) ρ)
          (.cons (ergWert he' v') (E.envE ρ))
          (E.inv_antwort hZ hB.pad hI2 W)
          (E.envR_cons (E.envR_envE ρ) _ _ rfl (E.ergWert_ergZ hZ (ergE_fn hS f) he he' (hZ.erg f) v'))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
        · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, hargs, ha,
            execBlock_vorΛ]
          exact E.ausRel_schrumpf hR3
      · have hc : (Ty.why (D.gruende f) :: Γ).map E.tyE = Ty.why (D'.gruende (E.fn f)) :: Γ.map E.tyE := by
          rw [gruendeE hS]; rfl
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_end err M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (Fin.cast (gruendeE hS f) r') ρ) (castE hc.symm (.cons r' (E.envE ρ)))
          (E.inv_antwort hZ hB.pad hI2 W)
          ((E.envR_um hc.symm _ _).mpr (E.envR_cons (E.envR_envE ρ) _ _ (by rw [gruendeE hS])
            (by rw [castW_why]; rfl)))
        refine ⟨M₃, o.schrumpf.zuAusgang, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg (fun x => x.schrumpf.zuAusgang) (hΦ3 Φ hP)
        · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, hargs, ha,
            execEnd_umΓ, execEnd_umΛ]
          exact E.endRel_zuAusgang (E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR3))
      · refine ⟨M₂, .logik (E.logikZ e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, hargs, ha]
          exact E.logikRel_logikZ (fun g' he' => hB.vorb f _ _ g' (ha.trans (congrArg RufAusgang.logik he')))
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, hargs, ha]
          trivial
  | .bindAxiom (τ := τ) a args he hw hg hd hgd rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      obtain ⟨M₂, hs2, hOΦ, hI2⟩ := E.ax_schluessel hZ pad O' hI a (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.evalArgs_exA hI.treu hI.treu args ρ
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
            (.cons (ergWert he v) ρ) (.cons (ergWert he' (castV (E.aerg a).symm (E.ergE _ v))) (E.envE ρ))
            (E.inv_antwort hZ hB.pad hI2 _) (E.envR_cons (E.envR_envE ρ) _ _ rfl (E.ergWert_ergE (E.aerg a) he he' v))
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
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      obtain ⟨M₂, hs2, hOΦ, hI2⟩ := E.ax_schluessel hZ pad O' hI a (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.evalArgs_exA hI.treu hI.treu args ρ
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
          (.cons (ergWert he v) ρ) (.cons (ergWert he' (castV (E.aerg a).symm (E.ergE _ v))) (E.envE ρ))
          (E.inv_antwort hZ hB.pad hI2 _) (E.envR_cons (E.envR_envE ρ) _ _ rfl (E.ergWert_ergE (E.aerg a) he he' v))
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
          (.cons r ρ) (castE hc.symm (.cons (Fin.cast (E.agruende a).symm r) (E.envE ρ)))
          (E.inv_antwort hZ hB.pad hI2 _)
          ((E.envR_um hc.symm _ _).mpr (E.envR_cons (E.envR_envE ρ) _ _ (by rw [E.agruende])
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
      obtain rfl := E.envR_eq ρ ρ' hρ
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
          · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := E.koerperSim_block_um S' O' U' A' passes R' hc _ _ (sim_block rest)
              _ σ σ' (.cons v ρ) (.cons ((E.rtyp r).symm ▸ E.valE _ v) (E.envE ρ)) hk1
              (E.envR_cons (E.envR_envE ρ) _ _ (E.rtyp r) (castW_symm (E.rtyp r) _))
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
      obtain rfl := E.envR_eq ρ ρ' hρ
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
          have henv : castE hc.symm (.cons ((E.rtyp r).symm ▸ E.valE _ v)
              (E.envE ρ) : Env D' (D'.rtyp (E.reg r) :: Γ.map E.tyE)) = E.envE (.cons v ρ) :=
            E.envR_eq _ _ ((E.envR_um hc.symm _ _).mpr
              (E.envR_cons (E.envR_envE ρ) _ _ (E.rtyp r) (castW_symm (E.rtyp r) _)))
          cases hb : wahr? (eval σ₁ zusage σ₁ (.cons v ρ))
          · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := sim_end sonst M₂ σ₁ _ ρ (E.envE ρ) hI (E.envR_envE ρ)
            refine ⟨M₃, o.zuAusgang, teil_trans (teil_trans hs1 hs2) hs3, fun Φ hP => ?_, ?_⟩
            · simp only [execBlockHA, orakelΦ_regLies, orakelΦ_zeiger,
                hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3))]
              rw [hx]
              simp only [hΦ2 Φ (passt_teil hP hs3), hb, Bool.false_eq_true, ↓reduceIte]
              exact congrArg EndAusgang.zuAusgang (hΦ3 Φ hP)
            · simp only [exB, execBlockHA]
              rw [hw'.2 v hx]
              simp only [Expr.orte_umΓ, Einbettung.orte_exE, eval_umΓ, henv, hev, wahr_valE, hb,
                Bool.false_eq_true, ↓reduceIte]
              exact E.endRel_zuAusgang hR
          · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := E.koerperSim_block_um S' O' U' A' passes R' hc _ _ (sim_block rest)
              M₂ σ₁ _ (.cons v ρ) (.cons ((E.rtyp r).symm ▸ E.valE _ v) (E.envE ρ)) hI
              (E.envR_cons (E.envR_envE ρ) _ _ (E.rtyp r) (castW_symm (E.rtyp r) _))
            refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs1 hs2) hs3, fun Φ hP => ?_, ?_⟩
            · simp only [execBlockHA, orakelΦ_regLies, orakelΦ_zeiger,
                hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3))]
              rw [hx]
              simp only [hΦ2 Φ (passt_teil hP hs3), hb, ↓reduceIte]
              exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
            · simp only [exB, execBlockHA]
              rw [hw'.2 v hx]
              simp only [Expr.orte_umΓ, Einbettung.orte_exE, eval_umΓ, henv, hev, wahr_valE, hb, ↓reduceIte]
              exact E.ausRel_schrumpf hR
  | .awaits g payload hp hL hat rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T hM hB.havocA hB.atom Λ (Λ.map E.resE)
        [Sum.inr g] [Sum.inr (E.glob g)] rfl
      obtain ⟨hk2, hs2, hΦ2⟩ := E.schluessel hI
      have hc : (D.gtyp g :: Γ).map E.tyE = D'.gtyp (E.glob g) :: Γ.map E.tyE := by
        rw [List.map_cons, E.gtyp]
      cases hvis : O'.sichtbar (E.glob g) (leseA A' σ' (Λ.map E.resE) [Sum.inr (E.glob g)])
      · refine ⟨_, .hardware (.sichtbarkeit D.a10), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), orakelΦ_sichtbar, hΦ2 Φ hP, hvis,
            Bool.false_eq_true, ↓reduceIte]
        · simp only [exB, execBlockHA, hvis, Bool.false_eq_true, ↓reduceIte]
          trivial
      · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := E.koerperSim_block_um S' O' U' A' passes R' hc _ _ (sim_block rest)
          _ σ₁ _ (.cons (σ₁.globs g) ρ) (.cons ((leseA A' σ' (Λ.map E.resE) [Sum.inr (E.glob g)]).globs
            (E.glob g)) (E.envE ρ)) hk2 (E.envR_cons (E.envR_envE ρ) _ _ (E.gtyp g) (hk2.treu.2 g))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), orakelΦ_sichtbar,
            hΦ2 Φ (passt_teil hP hs3), hvis, ↓reduceIte]
          exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
        · simp only [exB, execBlockHA, hvis, ↓reduceIte]
          exact E.ausRel_schrumpf hR
  | .exchange g neu hw hL rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (Sum.inr g :: neu.orte)
      have hc : (D.gtyp g :: Γ).map E.tyE = D'.gtyp (E.glob g) :: Γ.map E.tyE := by
        rw [List.map_cons, E.gtyp]
      have hrel := E.envR_cons (E.envR_envE ρ) (σ₁.globs g)
        ((leseA A' σ' (Λ.map E.resE) ((Sum.inr g :: neu.orte).map E.ortE)).globs (E.glob g))
        (E.gtyp g) (hI.treu.2 g)
      have henv := E.envR_eq _ _ ((E.envR_um hc.symm _ _).mpr hrel)
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := E.koerperSim_block_um S' O' U' A' passes R' hc _ _ (sim_block rest)
        M₁ (σ₁.schreibGlob g Λ (eval σ₁ neu σ₁ (.cons (σ₁.globs g) ρ))) _ (.cons (σ₁.globs g) ρ) _
        (hI.schreibGlob E g Λ (Λ.map E.resE) _ _ (castW_symm (E.gtyp g) _)) hrel
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
        exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
      · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umΓ, eval_umTy, henv, hev]
        exact E.ausRel_schrumpf hR
  | .narrow e lo' hi' sonst rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      by_cases hc : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi'
      · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block rest M₁ σ₁ _ (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ)
          (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ (E.envE ρ)) hI
          (E.envR_envE (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ))
        refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
          rw [dif_pos hc]
          exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
        · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, valE_int]
          rw [dif_pos hc]
          exact E.ausRel_schrumpf hR
      · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_end sonst M₁ σ₁ _ ρ (E.envE ρ) hI (E.envR_envE ρ)
        refine ⟨M₂, o.zuAusgang, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
          rw [dif_neg hc]
          exact congrArg EndAusgang.zuAusgang (hΦ2 Φ hP)
        · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, valE_int]
          rw [dif_neg hc]
          exact E.endRel_zuAusgang hR
  | .check c sonst rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (c.orte)
      cases hb : wahr? (eval σ₁ c σ₁ ρ)
      · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_end sonst M₁ σ₁ _ ρ (E.envE ρ) hI (E.envR_envE ρ)
        refine ⟨M₂, o.zuAusgang, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hb, Bool.false_eq_true, ↓reduceIte]
          exact congrArg EndAusgang.zuAusgang (hΦ2 Φ hP)
        · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, wahr_valE, hb, Bool.false_eq_true, ↓reduceIte]
          exact E.endRel_zuAusgang hR
      · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block rest M₁ σ₁ _ ρ (E.envE ρ) hI (E.envR_envE ρ)
        refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hb, ↓reduceIte]
          exact hΦ2 Φ hP
        · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, wahr_valE, hb, ↓reduceIte]
          exact hR
  | .float op a b lo hi rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (a.orte ++ b.orte)
      cases hg : gleitPasst lo hi (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x) with
      | none =>
          refine ⟨M₁, .logik .bereich, hs, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hΦ Φ hP, hg]
          · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, valE_fl, hg]
            exact E.logikRel_kein (fun _ h' => by cases h')
      | some w =>
          obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w (E.envE ρ)) hI
            (E.envR_envE (Env.cons (τ := .fl lo hi) w ρ))
          refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
            exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
          · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, valE_fl, hg]
            exact E.ausRel_schrumpf hR
  | .floatLit q lo hi rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      cases hg : gleitPasst lo hi (bruch q) with
      | none =>
          refine ⟨M, .logik .bereich, fun _ hp => hp, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hg]
          · simp only [exB, execBlockHA, hg]
            exact E.logikRel_kein (fun _ h' => by cases h')
      | some w =>
          obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block rest M σ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w (E.envE ρ)) hM
            (E.envR_envE (Env.cons (τ := .fl lo hi) w ρ))
          refine ⟨M₂, o.schrumpf, hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hg]
            exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
          · simp only [exB, execBlockHA, hg]
            exact E.ausRel_schrumpf hR
  | .floatOf e lo hi rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      cases hg : gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n) with
      | none =>
          refine ⟨M₁, .logik .bereich, hs, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hΦ Φ hP, hg]
          · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, valE_int, hg]
            exact E.logikRel_kein (fun _ h' => by cases h')
      | some w =>
          obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w (E.envE ρ)) hI
            (E.envR_envE (Env.cons (τ := .fl lo hi) w ρ))
          refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
            exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
          · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, valE_int, hg]
            exact E.ausRel_schrumpf hR
  | .floatNarrow e lo hi sonst rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      cases hg : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x with
      | none =>
          obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_end sonst M₁ σ₁ _ ρ (E.envE ρ) hI (E.envR_envE ρ)
          refine ⟨M₂, o.zuAusgang, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
            exact congrArg EndAusgang.zuAusgang (hΦ2 Φ hP)
          · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, valE_fl, hg]
            exact E.endRel_zuAusgang hR
      | some w =>
          obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_block rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w (E.envE ρ)) hI
            (E.envR_envE (Env.cons (τ := .fl lo hi) w ρ))
          refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
          · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
            exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
          · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev, valE_fl, hg]
            exact E.ausRel_schrumpf hR

/-- **An end block beside its image.** -/
theorem sim_end {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) →
    E.EndSim (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') b)
      (execEndHA S' O' U' A' passes R' (exEnd hS b))
  | .ret e hΛ => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T hM hB.havocA hB.atom Λ (Λ.map E.resE)
        e.orte (E.exErg e).orte (E.orte_exErg e).symm
      have he := E.evalErg_exErg hI.treu hI.treu e ρ
      refine ⟨M₁, .zurueck σ₁ (evalErg σ₁ e σ₁ ρ), hs, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, hΦ Φ hP]
      · exact ⟨hI, he⟩
  | .retWhy r hΛ => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      exact ⟨M, .why σ r, fun _ hp => hp, fun Φ hP => by simp only [execEndHA],
        by simp only [exEnd, execEndHA]; exact ⟨hM, rfl⟩⟩
  | .leave h => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      exact ⟨M, .leave h σ ρ, fun _ hp => hp, fun Φ hP => by simp only [execEndHA],
        by simp only [exEnd, execEndHA]; exact ⟨hM, E.envR_envE ρ⟩⟩
  | .next h => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      exact ⟨M, .next h σ ρ, fun _ hp => hp, fun Φ hP => by simp only [execEndHA],
        by simp only [exEnd, execEndHA]; exact ⟨hM, E.envR_envE ρ⟩⟩
  | .cons s rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, o₁, hs, hΦ, hR⟩ := sim_stmt s M σ σ' ρ (E.envE ρ) hM (E.envR_envE ρ)
      generalize ho : execStmtHA S' O' U' A' passes R' (exS hS s) σ' (E.envE ρ) = o₁' at hR
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
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (e.orte)
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_end rest M₁ σ₁ _ (.cons (eval σ₁ e σ₁ ρ) ρ)
        (.cons (E.valE _ (eval σ₁ e σ₁ ρ)) (E.envE ρ)) hI (E.envR_envE (.cons (eval σ₁ e σ₁ ρ) ρ))
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, hΦ Φ (passt_teil hP hs2)]
        exact congrArg EndAusgang.schrumpf (hΦ2 Φ hP)
      · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev]
        exact E.endRel_schrumpf hR
  | .bindCall (τ := τ) f args he hp hr rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schluessel hZ hS pad R' hI f (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.evalArgs_exA hI.treu hI.treu args ρ
      generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
        (castE (paramsE hS f) (E.envE (evalArgs σ₁ args σ₁ ρ))) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · have he' : D'.erg (E.fn f) = some (E.tyE τ) := by rw [← ergE_fn hS, he]; rfl
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_end rest M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (ergWert he (E.ergZ (D.erg f) (hZ.erg f) (castV (ergE_fn hS f).symm v'))) ρ)
          (.cons (ergWert he' v') (E.envE ρ))
          (E.inv_antwort hZ hB.pad hI2 W)
          (E.envR_cons (E.envR_envE ρ) _ _ rfl (E.ergWert_ergZ hZ (ergE_fn hS f) he he' (hZ.erg f) v'))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
        · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, hargs, ha,
            execEnd_umΛ]
          exact E.endRel_schrumpf hR3
      · exact (Fin.cast (by rw [gruendeE hS, hr]) r' : Fin 0).elim0
      · refine ⟨M₂, .logik (E.logikZ e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, hargs, ha]
          exact E.logikRel_logikZ (fun g' he' => hB.vorb f _ _ g' (ha.trans (congrArg RufAusgang.logik he')))
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, hargs, ha]
          trivial
  | .bindCallInd (n := n) (τ := τ) p args he hp hr rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (p.orte ++ args.orte)
      rcases hvd : eval σ₁ p σ₁ ρ with ⟨f, hf⟩
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schluessel hZ hS pad R' hI f (umsig hf (evalArgs σ₁ args σ₁ ρ))
      have hargs := E.evalArgs_exA hI.treu hI.treu args ρ
      have hp' := hev p ρ
      rw [hvd] at hp'
      generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE))
        (castE (paramsE hS f) (E.envE (umsig hf (evalArgs σ₁ args σ₁ ρ)))) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · have he₁ : D.erg f = some τ := ergSig hf he
        have heS : (D'.sigNr (E.num n)).erg = some (E.tyE τ) := by
          rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl
        have he' : D'.erg (E.fn f) = some (E.tyE τ) := ergSig ((E.passt f n).trans hf) heS
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_end rest M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (ergWert he₁ (E.ergZ (D.erg f) (hZ.erg f) (castV (ergE_fn hS f).symm v'))) ρ)
          (.cons (ergWert he' v') (E.envE ρ))
          (E.inv_antwort hZ hB.pad hI2 W)
          (E.envR_cons (E.envR_envE ρ) _ _ rfl (E.ergWert_ergZ hZ (ergE_fn hS f) he₁ he' (hZ.erg f) v'))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hvd, hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
        · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hp', valE, evalArgs_umτs, hargs, E.umsig_E hS hf, paramsUm, ha,
            execEnd_umΛ]
          exact E.endRel_schrumpf hR3
      · have h0 : D'.gruende (E.fn f) = 0 := by
          rw [gruendeE hS]; exact (D.passt_sig hf).gruende.trans hr
        exact (Fin.cast h0 r').elim0
      · refine ⟨M₂, .logik (E.logikZ e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
        · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hp', valE, evalArgs_umτs, hargs, E.umsig_E hS hf, paramsUm, ha]
          exact E.logikRel_logikZ (fun g' he' => hB.vorb f _ _ g' (ha.trans (congrArg RufAusgang.logik he')))
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
        · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hp', valE, evalArgs_umτs, hargs, E.umsig_E hS hf, paramsUm, ha]
          trivial
  | .bindCallElse (τ := τ) f args he hp hr err rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schluessel hZ hS pad R' hI f (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.evalArgs_exA hI.treu hI.treu args ρ
      generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
        (castE (paramsE hS f) (E.envE (evalArgs σ₁ args σ₁ ρ))) = a' at hRΦ
      rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
      · have he' : D'.erg (E.fn f) = some (E.tyE τ) := by rw [← ergE_fn hS, he]; rfl
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_end rest M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (ergWert he (E.ergZ (D.erg f) (hZ.erg f) (castV (ergE_fn hS f).symm v'))) ρ)
          (.cons (ergWert he' v') (E.envE ρ))
          (E.inv_antwort hZ hB.pad hI2 W)
          (E.envR_cons (E.envR_envE ρ) _ _ rfl (E.ergWert_ergZ hZ (ergE_fn hS f) he he' (hZ.erg f) v'))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
        · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, hargs, ha,
            execEnd_umΛ]
          exact E.endRel_schrumpf hR3
      · have hc : (Ty.why (D.gruende f) :: Γ).map E.tyE = Ty.why (D'.gruende (E.fn f)) :: Γ.map E.tyE := by
          rw [gruendeE hS]; rfl
        obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := sim_end err M₂ (E.antwortWelt hZ pad σ₁ W) W
          (.cons (Fin.cast (gruendeE hS f) r') ρ) (castE hc.symm (.cons r' (E.envE ρ)))
          (E.inv_antwort hZ hB.pad hI2 W)
          ((E.envR_um hc.symm _ _).mpr (E.envR_cons (E.envR_envE ρ) _ _ (by rw [gruendeE hS])
            (by rw [castW_why]; rfl)))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
            antwortR]
          exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
        · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, hargs, ha,
            execEnd_umΓ, execEnd_umΛ]
          exact E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR3)
      · refine ⟨M₂, .logik (E.logikZ e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, hargs, ha]
          exact E.logikRel_logikZ (fun g' he' => hB.vorb f _ _ g' (ha.trans (congrArg RufAusgang.logik he')))
      · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
        · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, hargs, ha]
          trivial
  | .bindAxiom (τ := τ) a args he hw hg hd hgd rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      obtain ⟨M₂, hs2, hOΦ, hI2⟩ := E.ax_schluessel hZ pad O' hI a (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.evalArgs_exA hI.treu hI.treu args ρ
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
            (.cons (ergWert he v) ρ) (.cons (ergWert he' (castV (E.aerg a).symm (E.ergE _ v))) (E.envE ρ))
            (E.inv_antwort hZ hB.pad hI2 _) (E.envR_cons (E.envR_envE ρ) _ _ rfl (E.ergWert_ergE (E.aerg a) he he' v))
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
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (args.orte)
      obtain ⟨M₂, hs2, hOΦ, hI2⟩ := E.ax_schluessel hZ pad O' hI a (evalArgs σ₁ args σ₁ ρ)
      have hargs := E.evalArgs_exA hI.treu hI.treu args ρ
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
          (.cons (ergWert he v) ρ) (.cons (ergWert he' (castV (E.aerg a).symm (E.ergE _ v))) (E.envE ρ))
          (E.inv_antwort hZ hB.pad hI2 _) (E.envR_cons (E.envR_envE ρ) _ _ rfl (E.ergWert_ergE (E.aerg a) he he' v))
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
          (.cons r ρ) (castE hc.symm (.cons (Fin.cast (E.agruende a).symm r) (E.envE ρ)))
          (E.inv_antwort hZ hB.pad hI2 _)
          ((E.envR_um hc.symm _ _).mpr (E.envR_cons (E.envR_envE ρ) _ _ (by rw [E.agruende])
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
      obtain rfl := E.envR_eq ρ ρ' hρ
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
          · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := E.endSim_end_um S' O' U' A' passes R' hc _ _ (sim_end rest)
              _ σ σ' (.cons v ρ) (.cons ((E.rtyp r).symm ▸ E.valE _ v) (E.envE ρ)) hk1
              (E.envR_cons (E.envR_envE ρ) _ _ (E.rtyp r) (castW_symm (E.rtyp r) _))
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
      obtain rfl := E.envR_eq ρ ρ' hρ
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
          have henv : castE hc.symm (.cons ((E.rtyp r).symm ▸ E.valE _ v)
              (E.envE ρ) : Env D' (D'.rtyp (E.reg r) :: Γ.map E.tyE)) = E.envE (.cons v ρ) :=
            E.envR_eq _ _ ((E.envR_um hc.symm _ _).mpr
              (E.envR_cons (E.envR_envE ρ) _ _ (E.rtyp r) (castW_symm (E.rtyp r) _)))
          cases hb : wahr? (eval σ₁ zusage σ₁ (.cons v ρ))
          · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := sim_end sonst M₂ σ₁ _ ρ (E.envE ρ) hI (E.envR_envE ρ)
            refine ⟨M₃, o, teil_trans (teil_trans hs1 hs2) hs3, fun Φ hP => ?_, ?_⟩
            · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger,
                hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3))]
              rw [hx]
              simp only [hΦ2 Φ (passt_teil hP hs3), hb, Bool.false_eq_true, ↓reduceIte]
              exact hΦ3 Φ hP
            · simp only [exEnd, execEndHA]
              rw [hw'.2 v hx]
              simp only [Expr.orte_umΓ, Einbettung.orte_exE, eval_umΓ, henv, hev, wahr_valE, hb,
                Bool.false_eq_true, ↓reduceIte]
              exact hR
          · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := E.endSim_end_um S' O' U' A' passes R' hc _ _ (sim_end rest)
              M₂ σ₁ _ (.cons v ρ) (.cons ((E.rtyp r).symm ▸ E.valE _ v) (E.envE ρ)) hI
              (E.envR_cons (E.envR_envE ρ) _ _ (E.rtyp r) (castW_symm (E.rtyp r) _))
            refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs1 hs2) hs3, fun Φ hP => ?_, ?_⟩
            · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger,
                hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3))]
              rw [hx]
              simp only [hΦ2 Φ (passt_teil hP hs3), hb, ↓reduceIte]
              exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
            · simp only [exEnd, execEndHA]
              rw [hw'.2 v hx]
              simp only [Expr.orte_umΓ, Einbettung.orte_exE, eval_umΓ, henv, hev, wahr_valE, hb, ↓reduceIte]
              exact E.endRel_schrumpf hR
  | .awaits g payload hp hL hat rest => by
      intro M σ σ' ρ ρ' hM hρ
      obtain rfl := E.envR_eq ρ ρ' hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T hM hB.havocA hB.atom Λ (Λ.map E.resE)
        [Sum.inr g] [Sum.inr (E.glob g)] rfl
      obtain ⟨hk2, hs2, hΦ2⟩ := E.schluessel hI
      have hc : (D.gtyp g :: Γ).map E.tyE = D'.gtyp (E.glob g) :: Γ.map E.tyE := by
        rw [List.map_cons, E.gtyp]
      cases hvis : O'.sichtbar (E.glob g) (leseA A' σ' (Λ.map E.resE) [Sum.inr (E.glob g)])
      · refine ⟨_, .hardware (.sichtbarkeit D.a10), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), orakelΦ_sichtbar, hΦ2 Φ hP, hvis,
            Bool.false_eq_true, ↓reduceIte]
        · simp only [exEnd, execEndHA, hvis, Bool.false_eq_true, ↓reduceIte]
          trivial
      · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := E.endSim_end_um S' O' U' A' passes R' hc _ _ (sim_end rest)
          _ σ₁ _ (.cons (σ₁.globs g) ρ) (.cons ((leseA A' σ' (Λ.map E.resE) [Sum.inr (E.glob g)]).globs
            (E.glob g)) (E.envE ρ)) hk2 (E.envR_cons (E.envR_envE ρ) _ _ (E.gtyp g) (hk2.treu.2 g))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), orakelΦ_sichtbar,
            hΦ2 Φ (passt_teil hP hs3), hvis, ↓reduceIte]
          exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
        · simp only [exEnd, execEndHA, hvis, ↓reduceIte]
          exact E.endRel_schrumpf hR


/-- **Arms beside their images.** -/
theorem sim_arms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → ∀ w : Wert D (.sum cs),
    E.KoerperSim (fun Φ => execArmsHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
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
        (E.envR_cons (τ := .int lo hi) (τ' := .int lo hi) hρ nutz nutz rfl rfl)
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
    E.KoerperSim (fun Φ => execGrundHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
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
