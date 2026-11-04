module
public import Grammatik.Zielsatz.Einbettung.Welt
public import Grammatik.Kern.Syntax.Typen.Fall
@[expose] public section


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

private theorem eval_umTy_n {Γ : Ctx} {Λ : List (Res D)} {a b c d : Int}
    (h : Ty.int a b = Ty.int c d) (e : Expr D Γ Λ (.int a b))
    (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ (Expr.umTy h e) σ ρ).n = (eval σ₀ e σ ρ).n :=
  (congrArg (fun v : Zahl c d => v.n) (eval_umTy h e σ₀ σ ρ)).trans (castW_n h _)

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
  change x' = x
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
      simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at this
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

/-- A builtin with one operand commutes with the embedding: the image operation is the same operation. -/
theorem vrel_ib1 {τ1 τ : Ty} (op : IntBuiltin [τ1] τ) (x : Wert D τ1) (x' : Wert D' (E.tyE τ1))
    (hx : E.VRel K τ1 x x') :
    E.VRel K τ (evalIntBuiltin1 op x) (evalIntBuiltin1 (E.ibE op) x') := by
  cases op <;> (simp only [VRel] at hx ⊢; subst hx; rfl)

/-- A builtin with two operands commutes with the embedding. -/
theorem vrel_ib2 {τ1 τ2 τ : Ty} (op : IntBuiltin [τ1, τ2] τ) (x : Wert D τ1) (y : Wert D τ2)
    (x' : Wert D' (E.tyE τ1)) (y' : Wert D' (E.tyE τ2)) (hx : E.VRel K τ1 x x')
    (hy : E.VRel K τ2 y y') :
    E.VRel K τ (evalIntBuiltin2 op x y) (evalIntBuiltin2 (E.ibE op) x' y') := by
  cases op <;> (simp only [VRel] at hx hy ⊢; subst hx; subst hy; rfl)

/-! ## The commutation -/

variable {σ₀ σ : World D} {σ₀' σ' : World D'}

private theorem binary_congr {α β γ : Type} (f : α → β → γ) {a a' : α} {b b' : β}
    (ha : a = a') (hb : b = b') : f a b = f a' b' :=
  congr (congrArg f ha) hb

private theorem index_exE_n {Γ : Ctx} {Λ : List (Res D)} {t : D.Tab}
    (i : Expr D Γ Λ (.index (D.count t))) (ρ : Env D Γ) (ρ' : Env D' (Γ.map E.tyE))
    (hi : E.VRel K (.index (D.count t)) (eval σ₀ i σ ρ) (eval σ₀' (exE E i) σ' ρ')) :
    (eval σ₀' (Expr.umTy (E.countE t) (exE E i)) σ' ρ').n = (eval σ₀ i σ ρ).n :=
  (eval_umTy_n (E.countE t) (exE E i) σ₀' σ' ρ').trans
    (congrArg (fun v : Zahl 0 (D.count t - 1) => v.n) hi)

private theorem treu_slot_index {s : Speicher D} (h : E.Treu K s σ')
    (t : D.Tab) (f : D.Feld t) {k k' : Int} (hk : k' = k) :
    E.VRel K (D.typ t f) (s.slots t k f)
      (castW (E.typ t f) (σ'.slots (E.tab t) k' (E.feld t f))) :=
  (congrArg (fun j => E.VRel K (D.typ t f) (s.slots t k f)
    (castW (E.typ t f) (σ'.slots (E.tab t) j (E.feld t f)))) hk).mpr (h.1 t k f)

private theorem related_if {α β ι : Type} (rel : α → β → Prop) (p : ι → Prop)
    [DecidablePred p] {i j : ι} (h : j = i) {a b : α} {a' b' : β}
    (ha : rel a a') (hb : rel b b') :
    rel (if p i then a else b) (if p j then a' else b') := by
  have hp : p j ↔ p i := by rw [h]
  by_cases hi : p i
  · rw [if_pos hi, if_pos (hp.mpr hi)]; exact ha
  · rw [if_neg hi, if_neg (fun hj => hi (hp.mp hj))]; exact hb

private theorem restrict_prod_get : ∀ {fs : List Ty} {τ : Ty} (i : FieldAt fs τ)
    (v : ProdVal D'.Fn D'.passt (Ty.mapFields E.num E.tnum fs)),
    E.valZ K τ (prodGetW (FieldAt.mapNumbers E.num E.tnum i) v) =
      prodGetW i (ProdVal.restrict E.num E.tnum (fun n v => K.zeiger n v.1 v.2) fs v)
  | _, _, .head, _ => rfl
  | _, _, .tail i, v => restrict_prod_get i v.2

private theorem restrict_prod_set : ∀ {fs : List Ty} {τ : Ty} (i : FieldAt fs τ)
    (v : ProdVal D'.Fn D'.passt (Ty.mapFields E.num E.tnum fs)) (x : Wert D' (E.tyE τ)),
    ProdVal.restrict E.num E.tnum (fun n v => K.zeiger n v.1 v.2) fs
      (prodSetW (FieldAt.mapNumbers E.num E.tnum i) v x) =
      prodSetW i (ProdVal.restrict E.num E.tnum (fun n v => K.zeiger n v.1 v.2) fs v) (E.valZ K τ x)
  | _, _, .head, _, _ => rfl
  | _, _, .tail i, v, x => ProdVal.pcons_congr rfl (restrict_prod_set i v.2 x)

private theorem evalProd_cast_cons {Γ : Ctx} {Λ : List (Res D')} {τ : Ty} {fs fs' : List Ty}
    (h : fs = fs') (e : Expr D' Γ Λ τ) (args : Args D' Γ Λ fs)
    (σ₀ σ : World D') (ρ : Env D' Γ) :
    evalProd σ₀ (Args.umτs (congrArg (τ :: ·) h) (.cons e args)) σ ρ =
      (eval σ₀ e σ ρ, evalProd σ₀ (Args.umτs h args) σ ρ) := by
  subst h; rfl

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
      simpa only [exE, eval_umTy, eval] using
        (treu_slot_index E K h t f (index_exE_n E K i ρ ρ' (eval_exE h₀ h i ρ ρ' hρ)))
  | _, _, _, .thru _ t _ f i _, ρ, ρ', hρ => by
      simpa only [exE, eval_umTy, eval] using
        (treu_slot_index E K h t f (index_exE_n E K i ρ ρ' (eval_exE h₀ h i ρ ρ' hρ)))
  | _, _, _, .thruOwn _ t _ f i _ _ _ _ _ _, ρ, ρ', hρ => by
      simpa only [exE, eval_umTy, eval] using
        (treu_slot_index E K h t f (index_exE_n E K i ρ ρ' (eval_exE h₀ h i ρ ρ' hρ)))
  | _, _, _, .ptrOf _ _ _ _, _, _, _ => rfl
  | _, _, _, .fnref _ _ _, _, _, _ => Or.inl rfl
  | _, _, _, .refEq a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (fun (a b : Nat) => decide (a = b)) ha hb
  | _, _, _, .slotRef r t _ _ f _, ρ, ρ', hρ => by
      have hr := eval_exE h₀ h r ρ ρ' hρ
      simp only [VRel] at hr
      simp only [exE, eval_umTy, eval]
      erw [hr]
      exact h.1 t _ f
  | _, _, _, .oldG g _, _, _, _ => by
      simp only [exE, eval_umTy, eval]; exact h₀.2 g
  | _, _, _, .oldS t f i _, ρ, ρ', hρ => by
      simpa only [exE, eval_umTy, eval] using
        (treu_slot_index E K h₀ t f (index_exE_n E K i ρ ρ' (eval_exE h₀ h i ρ ρ' hρ)))
  | _, _, _, .widen h1 h2 a, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ
      exact congrArg (Zahl.weiter h1 h2) ha
  | _, _, _, .add a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr Zahl.add ha hb
  | _, _, _, .sub a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr Zahl.sub ha hb
  | _, _, _, .neg a, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ
      exact congrArg Zahl.neg ha
  | _, _, _, .mul a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr Zahl.mul ha hb
  | _, _, _, .div h0 h1 a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (Zahl.div h0 h1) ha hb
  | _, _, _, .rem h0 h1 a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (Zahl.rem h0 h1) ha hb
  | _, _, _, .sdiv h0 a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (Zahl.sdiv h0) ha hb
  | _, _, _, .srem h0 a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (Zahl.srem h0) ha hb
  | _, _, _, .getBytes t f hf n i _ _ _, ρ, ρ', hρ => by
      have hi := eval_exE h₀ h i ρ ρ' hρ
      simp only [VRel] at hi ⊢
      simp only [exE, eval]
      show (⟨_, _, _⟩ : Zahl _ _) = ⟨_, _, _⟩
      congr 1
      erw [hi]
      exact congrArg bytesZuZahl (E.bytesAb_treu K h σ rfl t f hf _ n _)
  | _, _, _, .band h0 h1 a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (Zahl.band h0 h1) ha hb
  | _, _, _, .bor w h0 h1 hw0 hw1 a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (Zahl.bor w h0 h1 hw0 hw1) ha hb
  | _, _, _, .bxor w h0 h1 hw0 hw1 a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (Zahl.bxor w h0 h1 hw0 hw1) ha hb
  | _, _, _, .shl w hw0 hw1 h0 h1 a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (Zahl.shl w hw0 hw1 h0 h1) ha hb
  | _, _, _, .shr w hw0 hw1 h0 h1 a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (Zahl.shr w hw0 hw1 h0 h1) ha hb
  | _, _, _, .lt a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (fun (a : Zahl _ _) (b : Zahl _ _) => decide (a.n < b.n)) ha hb
  | _, _, _, .le a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (fun (a : Zahl _ _) (b : Zahl _ _) => decide (a.n ≤ b.n)) ha hb
  | _, _, _, .eq a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (fun (a : Zahl _ _) (b : Zahl _ _) => decide (a.n = b.n)) ha hb
  | _, _, _, .fllt a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (fun (a : Gleit _ _) (b : Gleit _ _) => gleitLt a.x b.x) ha hb
  | _, _, _, .flle a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (fun (a : Gleit _ _) (b : Gleit _ _) => gleitLe a.x b.x) ha hb
  | _, _, _, .and a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (fun (a b : Bool) => wahr? a && wahr? b) ha hb
  | _, _, _, .or a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      exact binary_congr (fun (a b : Bool) => wahr? a || wahr? b) ha hb
  | _, _, _, .not a, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ
      exact congrArg (fun a : Bool => !wahr? a) ha
  | _, _, _, .none _, _, _, _ => rfl
  | _, _, _, .some a, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ
      exact congrArg some ha
  | _, _, _, .istSome a, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ
      exact congrArg Option.isSome ha
  | _, _, _, .case cs i nutz, ρ, ρ', hρ => by
      have hn := E.nrel_valZ K (cs.get i) _ _ (evalNutz_exN h₀ h nutz ρ ρ' hρ)
      simp only [VRel, exE, eval, evalNutz_cast]
      change Val.restrictSum E.num E.tnum (fun n value => K.zeiger n value.1 value.2) cs
        ⟨⟨i.val, by rw [Ty.mapCases_length]; exact i.isLt⟩,
          Fall.ofNutzlast _ _ _ _ ((Ty.mapCases_get E.num E.tnum cs i).symm ▸ evalNutz σ₀' (exN E nutz) σ' ρ')⟩ = _
      rw [Val.restrictSum_mk]
      exact congrArg (fun payload => (⟨i, Fall.ofNutzlast _ _ _ _ payload⟩ : Wert D (.sum cs))) hn
  | _, _, _, .why _ _, _, _, _ => rfl
  | _, _, _, .forallSlots t body _, ρ, ρ', hρ => by
      simp only [VRel]
      simp only [exE, eval]
      erw [alle_count _ (E.count t)]
      show _ = (alleIndizes (D.count t)).all (fun k => wahr? (eval σ₀ body σ (.cons k ρ)))
      congr 1
      funext k
      have hk := eval_exE h₀ h body (.cons k ρ) (.cons k ρ') (E.envR_cons K (τ := Ty.index (D.count t)) (τ' := Ty.index (D.count t)) hρ k k rfl rfl)
      exact congrArg wahr? hk
  | _, _, _, .existsSlots t body _, ρ, ρ', hρ => by
      simp only [VRel]
      simp only [exE, eval]
      erw [any_count _ (E.count t)]
      show _ = (alleIndizes (D.count t)).any (fun k => wahr? (eval σ₀ body σ (.cons k ρ)))
      congr 1
      funext k
      have hk := eval_exE h₀ h body (.cons k ρ) (.cons k ρ') (E.envR_cons K (τ := Ty.index (D.count t)) (τ' := Ty.index (D.count t)) hρ k k rfl rfl)
      exact congrArg wahr? hk
  | _, _, _, .reaches t f hf a b _, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [VRel, exE, eval]
      have hf' : D'.typ (E.tab t) (E.feld t f) = .opt (D'.count (E.tab t)) := by
        rw [E.typ, hf, E.count]; rfl
      let w' : Int → Option (Zahl 0 (D'.count (E.tab t) - 1)) :=
        fun k => castW (D := D') hf' (σ'.slots (E.tab t) k (E.feld t f))
      let w : Int → Option (Zahl 0 (D.count t - 1)) := fun k => castW (D := D) hf (σ.slots t k f)
      exact (binary_congr (kette w' (D'.count (E.tab t)).toNat)
        (index_exE_n E K a ρ ρ' ha) (index_exE_n E K b ρ ρ' hb)).trans
        (kette_gleich (E.count t) w' w
          (fun k => E.opt_treu K _ _ (E.typ t f) (h.1 t k f) hf hf') _ _)
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
      intro j
      show E.VRel K _ (arrSetW _ _ _ j) (arrSetW _ _ _ j)
      unfold arrSetW
      exact related_if (E.VRel K _) (fun k => j = k) (congrArg Zahl.fin hi) hv (ha j)
  | _, _, _, .strLit _ _, _, _, _ => rfl
  | _, _, _, .strLen e, ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ
      exact congrArg strLenW he
  | _, _, _, .strCat e e', ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ; have he' := eval_exE h₀ h e' ρ ρ' hρ
      exact binary_congr strCatW he he'
  | _, _, _, .strGet e e', ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ; have he' := eval_exE h₀ h e' ρ ρ' hρ
      exact binary_congr (fun s (i : Zahl _ _) => strGetW s i.n) he he'
  | _, _, _, .strEq e e', ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ; have he' := eval_exE h₀ h e' ρ ρ' hρ
      exact binary_congr strEqW he he'
  | _, _, _, .strLt e e', ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ; have he' := eval_exE h₀ h e' ρ ρ' hρ
      exact binary_congr strLtW he he'
  | _, _, _, .strWeit m e, ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ
      exact congrArg (strWeitW m) he
  | _, _, _, .wenn c a b, ρ, ρ', hρ => by
      have hc := eval_exE h₀ h c ρ ρ' hρ; have ha := eval_exE h₀ h a ρ ρ' hρ
      have hb := eval_exE h₀ h b ρ ρ' hρ
      exact related_if (E.VRel K _) (fun b : Bool => b = true) (congrArg wahr? hc) ha hb
  | _, _, _, .eng e lo' hi' s, ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ; have hs := eval_exE h₀ h s ρ ρ' hρ
      exact binary_congr (fun (v : Zahl _ _) (s : Zahl lo' hi') =>
        if h : lo' ≤ v.n ∧ v.n ≤ hi' then (⟨v.n, h.1, h.2⟩ : Zahl lo' hi') else s) he hs
  | _, _, _, .intBuiltin1 op a, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ
      simp only [exE, eval]
      exact E.vrel_ib1 K op _ _ ha
  | _, _, _, .intBuiltin2 op a b, ρ, ρ', hρ => by
      have ha := eval_exE h₀ h a ρ ρ' hρ; have hb := eval_exE h₀ h b ρ ρ' hρ
      simp only [exE, eval]
      exact E.vrel_ib2 K op _ _ _ _ ha hb
  | _, _, _, .count n body, ρ, ρ', hρ => by
      simp only [VRel]
      simp only [exE, eval]
      show _ = zaehleWahr n (fun k => wahr? (eval σ₀ body σ (.cons k ρ)))
      refine zaehleWahr_congr n _ _ (fun k _ => ?_)
      have hk := eval_exE h₀ h body (.cons k ρ) (.cons k ρ')
        (E.envR_cons K (τ := Ty.index (n : Int)) (τ' := Ty.index (n : Int)) hρ k k rfl rfl)
      simp only [VRel] at hk
      exact congrArg wahr? hk
  | _, _, _, .prod r args, ρ, ρ', hρ => evalProd_exA h₀ h args ρ ρ' hρ
  | _, _, _, .prodGet v i, ρ, ρ', hρ => by
      have hv := eval_exE h₀ h v ρ ρ' hρ
      apply (E.vrel_iff_valZ K _ _ _).mpr
      exact (restrict_prod_get E K i _).trans (congrArg (prodGetW i) hv)
  | _, _, _, .prodSet v i e, ρ, ρ', hρ => by
      have hv := eval_exE h₀ h v ρ ρ' hρ
      have he := E.valZ_vrel K _ (eval_exE h₀ h e ρ ρ' hρ)
      exact (restrict_prod_set E K i _ _).trans (binary_congr (prodSetW i) hv he)

/-- Payloads. -/
theorem evalNutz_exN (h₀ : E.Treu K σ₀.speicher σ₀') (h : E.Treu K σ.speicher σ') :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option Ty} (n : NutzlastExpr D Γ Λ c) (ρ : Env D Γ)
      (ρ' : Env D' (Γ.map E.tyE)), E.EnvR K ρ ρ' →
      E.NRel K c (evalNutz σ₀ n σ ρ) (evalNutz σ₀' (exN E n) σ' ρ')
  | _, _, _, .empty, _, _, _ => trivial
  | _, _, _, .val e, ρ, ρ', hρ => by
      have he := eval_exE h₀ h e ρ ρ' hρ
      exact he

/-- Restriction of the complete translated field-argument tuple. -/
theorem evalProd_exA (h₀ : E.Treu K σ₀.speicher σ₀') (h : E.Treu K σ.speicher σ') :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {fs : List Ty} (args : Args D Γ Λ fs) (ρ : Env D Γ)
      (ρ' : Env D' (Γ.map E.tyE)), E.EnvR K ρ ρ' →
      ProdVal.restrict E.num E.tnum (fun n v => K.zeiger n v.1 v.2) fs
        (evalProd σ₀' (Args.umτs (E.mapFieldsE fs) (exA E args)) σ' ρ') = evalProd σ₀ args σ ρ
  | _, _, _, .nil, _, _, _ => rfl
  | _, _, τ :: fs, .cons e rest, ρ, ρ', hρ => by
      exact (congrArg (ProdVal.restrict E.num E.tnum (fun n v => K.zeiger n v.1 v.2) (τ :: fs))
        (evalProd_cast_cons (τ := E.tyE τ) (E.mapFieldsE fs)
          (exE E e) (exA E rest) σ₀' σ' ρ')).trans
        (ProdVal.pcons_congr (E.valZ_vrel K _ (eval_exE h₀ h e ρ ρ' hρ))
          (evalProd_exA h₀ h rest ρ ρ' hρ))

end

end Einbettung

end Gabbro.Grammatik.Einbettung
