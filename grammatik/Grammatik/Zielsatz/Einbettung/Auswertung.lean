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

/-- **`σ'` carries `s` on the image.** -/
def Treu (s : Speicher D) (σ' : World D') : Prop :=
  (∀ t k f, castW (E.typ t f) (σ'.slots (E.tab t) k (E.feld t f)) = E.valE _ (s.slots t k f)) ∧
  (∀ g, castW (E.gtyp g) (σ'.globs (E.glob g)) = E.valE _ (s.globs g))

theorem treu_speicherE (ctx : Speicher D') (s : Speicher D) (sp : List (Ereignis D')) :
    E.Treu s ((E.speicherE ctx s).welt sp) := by
  refine ⟨fun t k f => ?_, fun g => ?_⟩
  · show castW _ (E.slotE ctx s (E.tab t) k (E.feld t f)) = _
    rw [E.slotE_bild, E.slotBild_feld, castW_castW, castW_self]
  · show castW _ (E.globE ctx s (E.glob g)) = _
    rw [E.globE_bild, castW_castW, castW_self]

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
    (h : castW eT x' = E.valE T x) (hT : T = .int 0 255) (hT' : T' = .int 0 255) :
    (cast (congrArg (Wert D') hT') x' : Wert D' (.int 0 255)) = (cast (congrArg (Wert D) hT) x : Wert D (.int 0 255)) := by
  subst hT
  subst eT
  rw [cast_eq, cast_eq]
  exact h

/-- An `option index` of an image field is the field's. -/
theorem opt_treu {T' T : Ty} (x' : Wert D' T') (x : Wert D T) (eT : T' = E.tyE T)
    (h : castW eT x' = E.valE T x) {n n' : Int} (hT : T = .opt n) (hT' : T' = .opt n') :
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
theorem bytesAb_treu {s : Speicher D} {σ' : World D'} (h : E.Treu s σ') (σ : World D)
    (hs : σ.speicher = s) (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (hf' : D'.typ (E.tab t) (E.feld t f) = .int 0 255) :
    ∀ (n : Nat) (k : Int), σ'.bytesAb (E.tab t) (E.feld t f) hf' n k = σ.bytesAb t f hf n k
  | 0, _ => rfl
  | n + 1, k => by
      simp only [World.bytesAb]
      rw [bytesAb_treu h σ hs t f hf hf' n (k + 1)]
      congr 1
      subst hs
      exact E.byte_treu _ _ (E.typ t f) (h.1 t k f) hf hf'

/-! ## The commutation -/

variable {σ₀ σ : World D} {σ₀' σ' : World D'}

mutual

/-- **Evaluation commutes with the embedding.** -/
theorem eval_exE (h₀ : E.Treu σ₀.speicher σ₀') (h : E.Treu σ.speicher σ') :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (ρ : Env D Γ),
      eval σ₀' (exE E e) σ' (E.envE ρ) = E.valE τ (eval σ₀ e σ ρ)
  | _, _, _, .lit _, _ => rfl
  | _, _, _, .tru, _ => rfl
  | _, _, _, .fls, _ => rfl
  | _, _, _, .var x, ρ => E.envE_get ρ x
  | _, _, _, .glob g _, _ => by
      simp only [exE, eval_umTy, eval]; exact h.2 g
  | _, _, _, .slot t f i _, ρ => by
      simp only [exE, eval_umTy, eval]
      rw [castW_n, eval_exE h₀ h i ρ]
      exact h.1 t _ f
  | _, _, _, .thru _ t _ f i _, ρ => by
      simp only [exE, eval_umTy, eval]
      rw [castW_n, eval_exE h₀ h i ρ]
      exact h.1 t _ f
  | _, _, _, .ptrOf _ _ _ _, _ => rfl
  | _, _, _, .fnref _ _ _, _ => rfl
  | _, _, _, .refEq a b, ρ => by
      simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .slotRef r t _ _ f _, ρ => by
      simp only [exE, eval_umTy, eval]
      rw [eval_exE h₀ h r ρ]
      exact h.1 t _ f
  | _, _, _, .oldG g _, _ => by
      simp only [exE, eval_umTy, eval]; exact h₀.2 g
  | _, _, _, .oldS t f i _, ρ => by
      simp only [exE, eval_umTy, eval]
      rw [castW_n, eval_exE h₀ h i ρ]
      exact h₀.1 t _ f
  | _, _, _, .widen _ _ a, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ]; rfl
  | _, _, _, .add a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .sub a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .neg a, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ]; rfl
  | _, _, _, .mul a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .div _ _ a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .rem _ _ a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .sdiv _ a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .srem _ a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .getBytes t f hf n i _ _ _, ρ => by
      simp only [exE, eval]
      show (⟨_, _, _⟩ : Zahl _ _) = ⟨_, _, _⟩
      congr 1
      rw [eval_exE h₀ h i ρ]
      exact congrArg bytesZuZahl (E.bytesAb_treu h σ rfl t f hf _ n _)
  | _, _, _, .band _ _ a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .bor _ _ _ _ _ a b, ρ => by
      simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .bxor _ _ _ _ _ a b, ρ => by
      simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .shl _ _ _ _ _ a b, ρ => by
      simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .shr _ _ _ _ _ a b, ρ => by
      simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .lt a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .le a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .eq a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .fllt a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .flle a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .and a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .or a b, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]; rfl
  | _, _, _, .not a, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ]; rfl
  | _, _, _, .none _, _ => rfl
  | _, _, _, .some a, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ]; rfl
  | _, _, _, .istSome a, ρ => by simp only [exE, eval]; rw [eval_exE h₀ h a ρ]; rfl
  | _, _, _, .case _ _ nutz, ρ => by simp only [exE, eval]; rw [evalNutz_exN h₀ h nutz ρ]; rfl
  | _, _, _, .why _ _, _ => rfl
  | _, _, _, .forallSlots t body _, ρ => by
      simp only [exE, eval]
      rw [alle_count _ (E.count t)]
      show _ = (alleIndizes (D.count t)).all (fun k => wahr? (eval σ₀ body σ (.cons k ρ)))
      congr 1
      funext k
      exact congrArg wahr? (eval_exE h₀ h body (.cons k ρ))
  | _, _, _, .existsSlots t body _, ρ => by
      simp only [exE, eval]
      rw [any_count _ (E.count t)]
      show _ = (alleIndizes (D.count t)).any (fun k => wahr? (eval σ₀ body σ (.cons k ρ)))
      congr 1
      funext k
      exact congrArg wahr? (eval_exE h₀ h body (.cons k ρ))
  | _, _, _, .reaches t f hf a b _, ρ => by
      simp only [exE, eval, eval_umTy]
      rw [castW_n, castW_n, eval_exE h₀ h a ρ, eval_exE h₀ h b ρ]
      exact kette_gleich (E.count t) _ _
        (fun k => E.opt_treu _ _ (E.typ t f) (h.1 t k f) hf _) _ _

/-- Payloads. -/
theorem evalNutz_exN (h₀ : E.Treu σ₀.speicher σ₀') (h : E.Treu σ.speicher σ') :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)} (n : NutzlastExpr D Γ Λ c) (ρ : Env D Γ),
      evalNutz σ₀' (exN E n) σ' (E.envE ρ) = evalNutz σ₀ n σ ρ
  | _, _, _, .empty, _ => rfl
  | _, _, _, .num e, ρ => eval_exE h₀ h e ρ

end

end Einbettung

end Gabbro.Grammatik.Einbettung
