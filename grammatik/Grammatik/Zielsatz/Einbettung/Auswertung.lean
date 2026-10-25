import Grammatik.Zielsatz.Einbettung.Welt

/-!
  File:      Grammatik/Zielsatz/Einbettung/Auswertung.lean
  Subject:   Evaluation commutes with the embedding (stage E2a).

  `Treu s σ'`: the world `σ'` of `D'` carries, on the image of `D`, the values of the memory `s`
  of `D`. Every embedded memory is such a world (`treu_speicherE`). On such worlds the translated
  expression evaluates to the translated value (`eval_exE`); the trace plays no part.
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

theorem eval_umTy {Γ : Ctx} {Λ : List (Res D)} {τ τ' : Ty} (h : τ = τ') (e : Expr D Γ Λ τ)
    (σ₀ σ : World D) (ρ : Env D Γ) : eval σ₀ (Expr.umTy h e) σ ρ = castW h (eval σ₀ e σ ρ) := by
  subst h; rfl

theorem castW_n {a b c d : Int} (h : Ty.int a b = Ty.int c d) (v : Wert D (.int a b)) :
    (castW h v).n = v.n := by
  cases h; rfl

namespace Einbettung

variable (E : Einbettung D D')

variable (K : E.Rueck)

/-- **`σ'` carries `s` on the image**: every image carrier holds a value beside `s`'s. -/
def Treu (s : Speicher D) (σ' : World D') : Prop :=
  (∀ t k f, E.VRel K (D.typ t f) (s.slots t k f) (castW (E.typ t f) (σ'.slots (E.tab t) k (E.feld t f)))) ∧
  (∀ g, E.VRel K (D.gtyp g) (s.globs g) (castW (E.gtyp g) (σ'.globs (E.glob g))))

theorem treu_speicherE (ctx : Speicher D') (s : Speicher D) (sp : List (Ereignis D')) :
    E.Treu K s ((E.speicherE ctx s).welt sp) := by
  refine ⟨fun t k f => ?_, fun g => ?_⟩
  · show E.VRel K _ _ (castW _ (E.slotE ctx s (E.tab t) k (E.feld t f)))
    rw [E.slotE_bild, E.slotBild_feld, castW_castW, castW_self]
    exact E.vrel_valE K _ _
  · show E.VRel K _ _ (castW _ (E.globE ctx s (E.glob g)))
    rw [E.globE_bild, castW_castW, castW_self]
    exact E.vrel_valE K _ _

/-! ## Environments -/

/-- An environment of `D` beside one of `D'`, value by value (the scopes may differ by a
    transport). -/
def EnvR : {Γ : Ctx} → Env D Γ → {Γ' : Ctx} → Env D' Γ' → Prop
  | _, .nil, _, .nil => True
  | _, .cons (τ := τ) v ρ, _, .cons (τ := τ') v' ρ' =>
      (∃ h : τ' = E.tyE τ, E.VRel K τ v (castW h v')) ∧ EnvR ρ ρ'
  | _, _, _, _ => False

theorem envR_envE : ∀ {Γ : Ctx} (ρ : Env D Γ), E.EnvR K ρ (E.envE ρ)
  | _, .nil => trivial
  | _, .cons v ρ => ⟨⟨rfl, E.vrel_valE K _ v⟩, envR_envE ρ⟩

theorem envR_get : ∀ {Γ : Ctx} {τ : Ty} (ρ : Env D Γ) (ρ' : Env D' (Γ.map E.tyE)) (x : Var Γ τ),
    E.EnvR K ρ ρ' → E.VRel K τ (ρ.get x) (ρ'.get (varE E x))
  | _ :: _, _, .cons v ρ, .cons v' ρ', .here, h => by
      simp only [EnvR] at h
      obtain ⟨⟨_, hv⟩, _⟩ := h
      exact hv
  | _ :: _, _, .cons v ρ, .cons v' ρ', .there x, h => by
      simp only [EnvR] at h
      exact envR_get ρ ρ' x h.2

theorem envR_cons {τ τ' : Ty} {Γ Γ' : Ctx} {ρ : Env D Γ} {ρ' : Env D' Γ'} (h : E.EnvR K ρ ρ')
    (v : Wert D τ) (v' : Wert D' τ') (e : τ' = E.tyE τ) (hv : E.VRel K τ v (castW e v')) :
    E.EnvR K (Env.cons v ρ) (Env.cons v' ρ') := ⟨⟨e, hv⟩, h⟩

/-- A quantifier over the slots of an image table: its count is the table's. -/
theorem alle_count {t : D.Tab} {G : Ctx} {Λ : List (Res D')} (c : Int) (hc : c = D.count t)
    (h : (Ty.index (D.count t) :: G) = (Ty.index c :: G)) (e : Expr D' (Ty.index (D.count t) :: G) Λ .bool)
    (σ₀ σ : World D') (ρ : Env D' G) :
    (alleIndizes c).all (fun k => wahr? (eval σ₀ (Expr.umΓ h e) σ (.cons k ρ))) =
      (alleIndizes (D.count t)).all (fun k => wahr? (eval σ₀ e σ (.cons k ρ))) := by
  subst hc; rfl

theorem any_count {t : D.Tab} {G : Ctx} {Λ : List (Res D')} (c : Int) (hc : c = D.count t)
    (h : (Ty.index (D.count t) :: G) = (Ty.index c :: G)) (e : Expr D' (Ty.index (D.count t) :: G) Λ .bool)
    (σ₀ σ : World D') (ρ : Env D' G) :
    (alleIndizes c).any (fun k => wahr? (eval σ₀ (Expr.umΓ h e) σ (.cons k ρ))) =
      (alleIndizes (D.count t)).any (fun k => wahr? (eval σ₀ e σ (.cons k ρ))) := by
  subst hc; rfl

/-- A byte of an image field is the field's byte. -/
theorem byte_treu {T' T : Ty} (x' : Wert D' T') (x : Wert D T) (eT : T' = E.tyE T)
    (h : E.VRel K T x (castW eT x')) (hT : T = .int 0 255) (hT' : T' = .int 0 255) :
    (cast (congrArg (Wert D') hT') x' : Wert D' (.int 0 255)) = (cast (congrArg (Wert D) hT) x : Wert D (.int 0 255)) := by
  subst hT
  subst eT
  rw [cast_eq, cast_eq]
  exact h

/-- An `option index` of an image field is the field's. -/
theorem opt_treu {T' T : Ty} (x' : Wert D' T') (x : Wert D T) (eT : T' = E.tyE T)
    (h : E.VRel K T x (castW eT x')) {n n' : Int} (hT : T = .opt n) (hT' : T' = .opt n') :
    ((hT' ▸ x' : Wert D' (.opt n')) : Option (Zahl 0 (n' - 1))).map Zahl.n =
      ((hT ▸ x : Wert D (.opt n)) : Option (Zahl 0 (n - 1))).map Zahl.n := by
  subst hT
  subst eT
  cases hT'
  exact congrArg (Option.map Zahl.n) h

/-- Two chains with the same steps agree. -/
theorem kette_gleich {n n' : Int} (hn : n' = n) (w' : Int → Option (Zahl 0 (n' - 1)))
    (w : Int → Option (Zahl 0 (n - 1))) (hw : ∀ k, (w' k).map Zahl.n = (w k).map Zahl.n) (a b : Int) :
    kette w' n'.toNat a b = kette w n.toNat a b := by
  subst hn
  have e : w' = w := by
    funext k
    have := hw k
    rcases h1 : w' k with _ | z1 <;> rcases h2 : w k with _ | z2 <;> rw [h1, h2] at this <;>
      simp at this
    all_goals first
      | rfl
      | (cases z1; cases z2; simp only at this; subst this; rfl)
  rw [e]

/-- The bytes of an image field are the field's bytes. -/
theorem bytesAb_treu {s : Speicher D} {σ' : World D'} (h : E.Treu K s σ') (σ : World D)
    (hs : σ.speicher = s) (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (hf' : D'.typ (E.tab t) (E.feld t f) = .int 0 255) :
    ∀ (n : Nat) (k : Int), σ'.bytesAb (E.tab t) (E.feld t f) hf' n k = σ.bytesAb t f hf n k
  | 0, _ => rfl
  | n + 1, k => by
      simp only [World.bytesAb]
      rw [bytesAb_treu h σ hs t f hf hf' n (k + 1)]
      congr 1
      subst hs
      exact E.byte_treu K _ _ (E.typ t f) (h.1 t k f) hf hf'

/-! ## The commutation -/

variable {σ₀ σ : World D} {σ₀' σ' : World D'}

mutual

/-- **Evaluation commutes with the embedding**: beside related worlds and environments, an
    expression and its image evaluate to related values. -/
theorem eval_exE (h₀ : E.Treu K σ₀.speicher σ₀') (h : E.Treu K σ.speicher σ') :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (ρ : Env D Γ)
      (ρ' : Env D' (Γ.map E.tyE)), E.EnvR K ρ ρ' →
      E.VRel K τ (eval σ₀ e σ ρ) (eval σ₀' (exE E e) σ' ρ')
  | _, _, _, .lit _, _, _, _ => rfl
  | _, _, _, .tru, _, _, _ => rfl
  | _, _, _, .fls, _, _, _ => rfl
  | _, _, _, .var x, ρ, ρ', hρ => E.envR_get K ρ ρ' x hρ
  | _, _, _, .glob g _, _, _, _ => by
      simp only [exE, eval_umTy, eval]; exact h.2 g
  | _, _, _, .slot t f i _, ρ, ρ', hρ => by
      have hi := eval_exE h₀ h i ρ ρ' hρ
      simp only [VRel] at hi
      simp only [exE, eval_umTy, eval]
      rw [castW_n, hi]
      exact h.1 t _ f
  | _, _, _, .thru _ t _ f i _, ρ, ρ', hρ => by
      have hi := eval_exE h₀ h i ρ ρ' hρ
      simp only [VRel] at hi
      simp only [exE, eval_umTy, eval]
      rw [castW_n, hi]
      exact h.1 t _ f
  | _, _, _, .ptrOf _ _ _ _, _, _, _ => rfl
  | _, _, _, .fnref _ _ _, _, _, _ => Or.inl rfl
  | _, _, _, .refEq a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .slotRef r t _ _ f _, ρ, ρ', hρ => by
      have hr := eval_exE h₀ h r ρ ρ' hρ
      simp only [VRel] at hr
      simp only [exE, eval_umTy, eval]
      rw [hr]
      exact h.1 t _ f
  | _, _, _, .oldG g _, _, _, _ => by
      simp only [exE, eval_umTy, eval]; exact h₀.2 g
  | _, _, _, .oldS t f i _, ρ, ρ', hρ => by
      have hi := eval_exE h₀ h i ρ ρ' hρ
      simp only [VRel] at hi
      simp only [exE, eval_umTy, eval]
      rw [castW_n, hi]
      exact h₀.1 t _ f
  | _, _, _, .widen _ _ a, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ
      simp only [VRel] at ha ⊢; simp only [exE, eval]; rw [ha]; rfl
  | _, _, _, .add a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .sub a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .neg a, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ
      simp only [VRel] at ha ⊢; simp only [exE, eval]; rw [ha]; rfl
  | _, _, _, .mul a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .div _ _ a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .rem _ _ a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .sdiv _ a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .srem _ a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .getBytes t f hf n i _ _ _, ρ, ρ', hρ => by
      have hi := eval_exE h₀ h i ρ ρ' hρ
      simp only [VRel] at hi ⊢
      simp only [exE, eval]
      show (⟨_, _, _⟩ : Zahl _ _) = ⟨_, _, _⟩
      congr 1
      rw [hi]
      exact congrArg bytesZuZahl (E.bytesAb_treu K h σ rfl t f hf _ n _)
  | _, _, _, .band _ _ a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .bor _ _ _ _ _ a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .bxor _ _ _ _ _ a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .shl _ _ _ _ _ a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .shr _ _ _ _ _ a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .lt a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .le a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .eq a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .fllt a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .flle a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .and a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .or a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢; simp only [exE, eval]; rw [ha, hb]; rfl
  | _, _, _, .not a, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ
      simp only [VRel] at ha ⊢; simp only [exE, eval]; rw [ha]; rfl
  | _, _, _, .none _, _, _, _ => rfl
  | _, _, _, .some a, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ
      simp only [VRel] at ha ⊢; simp only [exE, eval]; rw [ha]; rfl
  | _, _, _, .istSome a, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ
      simp only [VRel] at ha ⊢; simp only [exE, eval]; rw [ha]; rfl
  | _, _, _, .case _ _ nutz, ρ, ρ', hρ => by
      simp only [VRel]; simp only [exE, eval]; rw [evalNutz_exN h₀ h nutz ρ ρ' hρ]; rfl
  | _, _, _, .why _ _, _, _, _ => rfl
  | _, _, _, .forallSlots t body _, ρ, ρ', hρ => by
      simp only [VRel]
      simp only [exE, eval]
      rw [alle_count _ (E.count t)]
      show _ = (alleIndizes (D.count t)).all (fun k => wahr? (eval σ₀ body σ (.cons k ρ)))
      congr 1
      funext k
      have hk := eval_exE h₀ h body (.cons k ρ) (.cons k ρ') (E.envR_cons K (τ := Ty.index (D.count t)) (τ' := Ty.index (D.count t)) hρ k k rfl rfl)
      simp only [VRel] at hk
      rw [hk]; rfl
  | _, _, _, .existsSlots t body _, ρ, ρ', hρ => by
      simp only [VRel]
      simp only [exE, eval]
      rw [any_count _ (E.count t)]
      show _ = (alleIndizes (D.count t)).any (fun k => wahr? (eval σ₀ body σ (.cons k ρ)))
      congr 1
      funext k
      have hk := eval_exE h₀ h body (.cons k ρ) (.cons k ρ') (E.envR_cons K (τ := Ty.index (D.count t)) (τ' := Ty.index (D.count t)) hρ k k rfl rfl)
      simp only [VRel] at hk
      rw [hk]; rfl
  | _, _, _, .reaches t f hf a b _, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel] at ha hb ⊢
      simp only [exE, eval, eval_umTy]
      rw [castW_n, castW_n, ha, hb]
      exact kette_gleich (E.count t) _ _
        (fun k => E.opt_treu K _ _ (E.typ t f) (h.1 t k f) hf _) _ _
  | _, _, _, .arrNil, _, _, _ => fun j => j.elim0
  | _, _, _, .arrCons a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      intro j
      show E.VRel K _ (arrConsW _ _ j) (arrConsW _ _ j)
      unfold arrConsW
      split
      · exact ha
      · exact hb _
  | _, _, _, .arrGet a i, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hi := eval_exE h₀ h i ρ ρ' hρ
      simp only [VRel, valE] at hi
      show E.VRel K _ ((eval σ₀ a σ ρ) (eval σ₀ i σ ρ).fin)
        ((eval σ₀' (exE E a) σ' ρ') (eval σ₀' (exE E i) σ' ρ').fin)
      rw [hi]
      exact ha _
  | _, _, _, .arrSet a i v, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hi := eval_exE h₀ h i ρ ρ' hρ
      have hv := eval_exE h₀ h v ρ ρ' hρ
      simp only [VRel, valE] at hi
      intro j
      show E.VRel K _ (arrSetW _ _ _ j) (arrSetW _ _ _ j)
      unfold arrSetW
      rw [hi]
      by_cases hj : j = Zahl.fin (eval σ₀ i σ ρ)
      · simp only [hj, if_true]
        exact hv
      · simp only [hj, if_false]
        exact ha j
  | _, _, _, .strLit _ _, _, _, _ => rfl
  | _, _, _, .strLen e, ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ
      simp only [VRel] at he ⊢
      show strLenW _ = strLenW _
      rw [he]
      rfl
  | _, _, _, .strCat e e', ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ; have he' := eval_exE h₀ h e' ρ ρ' hρ
      simp only [VRel] at he he' ⊢
      show strCatW _ _ = strCatW _ _
      rw [he, he']
      rfl
  | _, _, _, .strGet e e', ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ; have he' := eval_exE h₀ h e' ρ ρ' hρ
      simp only [VRel, valE] at he he' ⊢
      show strGetW _ _ = strGetW _ _
      rw [he, he']
  | _, _, _, .strEq e e', ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ; have he' := eval_exE h₀ h e' ρ ρ' hρ
      simp only [VRel, valE] at he he' ⊢
      show strEqW _ _ = strEqW _ _
      rw [he, he']
  | _, _, _, .strLt e e', ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ; have he' := eval_exE h₀ h e' ρ ρ' hρ
      simp only [VRel, valE] at he he' ⊢
      show strLtW _ _ = strLtW _ _
      rw [he, he']
  | _, _, _, .strWeit _ e, ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ
      simp only [VRel] at he ⊢
      show strWeitW _ _ = strWeitW _ _
      rw [he]
      rfl

/-- Payloads. -/
theorem evalNutz_exN (h₀ : E.Treu K σ₀.speicher σ₀') (h : E.Treu K σ.speicher σ') :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)} (n : NutzlastExpr D Γ Λ c) (ρ : Env D Γ)
      (ρ' : Env D' (Γ.map E.tyE)), E.EnvR K ρ ρ' →
      evalNutz σ₀' (exN E n) σ' ρ' = evalNutz σ₀ n σ ρ
  | _, _, _, .empty, _, _, _ => rfl
  | _, _, _, .num e, ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ
      simp only [VRel] at he
      exact he

end

end Einbettung

end Gabbro.Grammatik.Einbettung
