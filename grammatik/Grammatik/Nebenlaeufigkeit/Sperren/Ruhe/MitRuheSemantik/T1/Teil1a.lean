module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Environments, worlds, events -/

theorem envR_get : ∀ {Γ : Ctx} {τ : Ty} (ρ : Env D Γ) (x : Var Γ τ),
    (envR ρ).get (varR x) = valR τ (ρ.get x)
  | _, _, .cons _ _, .here => rfl
  | _, _, .cons _ ρ, .there x => envR_get ρ x

theorem envZ_envR : ∀ {Γ : Ctx} (ρ : Env D Γ), envZ (envR ρ) = ρ
  | [], .nil => rfl
  | τ :: _, .cons v ρ => by
      show Env.cons (valZ τ (valR τ v)) (envZ (envR ρ)) = _
      rw [valZ_valR, envZ_envR ρ]

theorem worldZ_worldR (σ : World D) : worldZ (worldR σ) = σ := by
  cases σ with
  | mk slots globs spur =>
      simp only [worldZ, worldR, valZ_valR, List.map_map]
      congr 1
      conv => rhs; rw [← List.map_id spur]
      exact List.map_congr_left fun e _ => evZ_evR e

theorem offen_map_evR : ∀ s : List (Ereignis D), offen (s.map (evR (D := D))) = offen s
  | [] => rfl
  | .nimmt L h :: s => congrArg (L :: ·) (offen_map_evR s)
  | .gibt L :: s => congrArg (fun l => List.erase l L) (offen_map_evR s)
  | .zugriff .. :: s => offen_map_evR s
  | .gzugriff .. :: s => offen_map_evR s
  | .fremd .. :: s => offen_map_evR s

theorem haelt_worldR (σ : World D) : (worldR σ).haelt = σ.haelt := offen_map_evR σ.spur

theorem welt_ext {σ τ : World D} (h1 : σ.slots = τ.slots) (h2 : σ.globs = τ.globs)
    (h3 : σ.spur = τ.spur) : σ = τ := by
  cases σ; cases τ; simp only at h1 h2 h3; subst h1 h2 h3; rfl

theorem leseEv_worldR (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    leseEv (worldR σ) (Λ.map resR) os = (leseEv σ Λ os).map evR := by
  unfold leseEv
  rw [List.map_map, haelt_worldR]
  apply List.map_congr_left
  intro o _
  cases o <;> rfl

theorem lese_worldR (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    (worldR σ).lese (Λ.map resR) os = worldR (σ.lese Λ os) := by
  refine welt_ext rfl rfl ?_
  show leseEv (worldR σ) (Λ.map resR) os ++ (worldR σ).spur = (leseEv σ Λ os ++ σ.spur).map evR
  rw [List.map_append, leseEv_worldR]
  rfl

theorem nimmt_worldR (σ : World D) (L : D.Lock) : (worldR σ).nimmt L = worldR (σ.nimmt L) := by
  refine welt_ext rfl rfl ?_
  show Ereignis.nimmt (D := D.mitRuhe) L (worldR σ).haelt :: (worldR σ).spur =
    (Ereignis.nimmt L σ.haelt :: σ.spur).map (evR (D := D))
  rw [haelt_worldR]
  rfl

theorem gibt_worldR (σ : World D) (L : D.Lock) : (worldR σ).gibt L = worldR (σ.gibt L) := by rfl

theorem gibt_foldl_worldR (σ : World D) (Ls : List D.Lock) :
    Ls.foldl World.gibt (worldR σ) = worldR (Ls.foldl World.gibt σ) := by
  induction Ls generalizing σ with
  | nil => rfl
  | cons L Ls ih =>
      simp only [List.foldl_cons, gibt_worldR]
      exact ih (σ.gibt L)

theorem kongr₃ {α β γ δ : Sort _} (f : α → β → γ → δ) {a a' : α} {b b' : β} {c c' : γ}
    (ha : a = a') (hb : b = b') (hc : c = c') : f a b c = f a' b' c' := by
  subst ha; subst hb; subst hc; rfl

theorem cast_byte_gen (τ : Ty) (h : τ = .int 0 255) (h' : tyR τ = .int 0 255)
    (x : Val D.Fn D.passt τ) :
    (cast (congrArg (Val (Option D.Fn) (passtM D)) h') (valR τ x) : Byte) =
      (cast (congrArg (Val D.Fn D.passt) h) x : Byte) := by
  subst h; rfl

theorem cast_byte_worldR (σ : World D) (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (hf' : (D.mitRuhe).typ t f = .int 0 255) (k : Int) :
    (cast (congrArg (Wert D.mitRuhe) hf') ((worldR σ).slots t k f) : Byte) =
      (cast (congrArg (Wert D) hf) (σ.slots t k f) : Byte) :=
  cast_byte_gen (D.typ t f) hf hf' (σ.slots t k f)

theorem opt_cast_gen (τ : Ty) (m : Int) (h : τ = .opt m) (h' : tyR τ = .opt m)
    (x : Val D.Fn D.passt τ) :
    @Eq (Option (Zahl 0 (m - 1))) (h' ▸ valR τ x : Val (Option D.Fn) (passtM D) (.opt m))
      (h ▸ x : Val D.Fn D.passt (.opt m)) := by
  subst h; rfl

theorem bytesAb_worldR (σ : World D) (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (hf' : (D.mitRuhe).typ t f = .int 0 255) :
    ∀ (n : Nat) (k : Int), (worldR σ).bytesAb t f hf' n k = σ.bytesAb t f hf n k
  | 0, _ => rfl
  | n + 1, k => kongr₂ List.cons (cast_byte_worldR σ t f hf hf' k) (bytesAb_worldR σ t f hf hf' n (k + 1))

theorem slot_cast_worldR (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .opt (D.count t)) (hf' : (D.mitRuhe).typ t f = .opt ((D.mitRuhe).count t))
    (k : Int) :
    @Eq (Option (Zahl 0 (D.count t - 1)))
      (hf' ▸ (worldR σ).slots t k f : Wert D.mitRuhe (.opt ((D.mitRuhe).count t)))
      (hf ▸ σ.slots t k f : Wert D (.opt (D.count t))) :=
  opt_cast_gen (D.typ t f) (D.count t) hf hf' (σ.slots t k f)

/-- The translated builtin on a translated operand is the translated result. -/
theorem eval_ib1_ru {τ1 τ : Ty} (op : IntBuiltin [τ1] τ) (x : Wert D τ1) :
    evalIntBuiltin1 (D := D.mitRuhe) (ibR op) (valR τ1 x) = valR τ (evalIntBuiltin1 op x) := by
  cases op <;> rfl

theorem eval_ib2_ru {τ1 τ2 τ : Ty} (op : IntBuiltin [τ1, τ2] τ) (x : Wert D τ1) (y : Wert D τ2) :
    evalIntBuiltin2 (D := D.mitRuhe) (ibR op) (valR τ1 x) (valR τ2 y) = valR τ (evalIntBuiltin2 op x y) := by
  cases op <;> rfl

/-! ## 2. Expressions -/

private theorem evalProd_cast_eq {D' : Deklaration} {Γ : Ctx} {Λ : List (Res D')}
    {fs fs' : List Ty} (h : fs = fs') (σ₀ σ : World D') (args : Args D' Γ Λ fs)
    (ρ : Env D' Γ) (v : ProdVal D'.Fn D'.passt fs')
    (hv : evalProd σ₀ args σ ρ = (h.symm ▸ v)) :
    evalProd σ₀ (h ▸ args) σ ρ = v := by
  subst h; exact hv

private theorem prodVal_cast_cons {D' : Deklaration} {τ : Ty} {fs fs' : List Ty}
    (h : fs = fs') (v : Wert D' τ) (vs : ProdVal D'.Fn D'.passt fs) :
    ((congrArg (τ :: ·) h) ▸ ProdVal.pcons v vs) = ProdVal.pcons v (h ▸ vs) := by
  subst h; rfl

mutual

/-- **An expression of `P.mitRuhe` evaluates to the translated value** of
    the expression of `P`, on the translated worlds and environment. -/
theorem eval_ru (σ₀ σ : World D) : ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (ρ : Env D Γ), eval (worldR σ₀) (ruE e) (worldR σ) (envR ρ) = valR τ (eval σ₀ e σ ρ)
  | _, _, _, .lit _, _ => rfl
  | _, _, _, .tru, _ => rfl
  | _, _, _, .fls, _ => rfl
  | _, _, _, .var x, ρ => envR_get ρ x
  | _, _, _, .glob _ _, _ => rfl
  | _, _, _, .slot t f i _, ρ =>
      congrArg (fun z : Zahl 0 (D.count t - 1) => valR (D.typ t f) (σ.slots t z.n f))
        (eval_ru σ₀ σ i ρ)
  | _, _, _, .thru _ t _ f i _, ρ =>
      congrArg (fun z : Zahl 0 (D.count t - 1) => valR (D.typ t f) (σ.slots t z.n f))
        (eval_ru σ₀ σ i ρ)
  | _, _, _, .thruOwn _ t _ f i _ _ _ _ _ _, ρ =>
      congrArg (fun z : Zahl 0 (D.count t - 1) => valR (D.typ t f) (σ.slots t z.n f))
        (eval_ru σ₀ σ i ρ)
  | _, _, _, .ptrOf .., _ => rfl
  | _, _, _, .fnref .., _ => rfl
  | _, _, _, .refEq a b, ρ => by
      show decide (_ = _) = decide (_ = _)
      erw [eval_ru σ₀ σ a ρ, eval_ru σ₀ σ b ρ]
      rfl
  | _, _, _, .slotRef r t _ _ f _, ρ =>
      congrArg (fun z : Nat => valR (D.typ t f) (σ.slots t (z : Int) f))
        (eval_ru σ₀ σ r ρ)
  | _, _, _, .oldG _ _, _ => rfl
  | _, _, _, .oldS t f i _, ρ =>
      congrArg (fun z : Zahl 0 (D.count t - 1) => valR (D.typ t f) (σ₀.slots t z.n f))
        (eval_ru σ₀ σ i ρ)
  | _, _, _, .widen h1 h2 e, ρ => congrArg (Zahl.weiter h1 h2) (eval_ru σ₀ σ e ρ)
  | _, _, _, .add a b, ρ => kongr₂ Zahl.add (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .sub a b, ρ => kongr₂ Zahl.sub (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .neg a, ρ => congrArg Zahl.neg (eval_ru σ₀ σ a ρ)
  | _, _, _, .mul a b, ρ => kongr₂ Zahl.mul (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .div h0 h1 a b, ρ => kongr₂ (Zahl.div h0 h1) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .rem h0 h1 a b, ρ => kongr₂ (Zahl.rem h0 h1) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .sdiv hb a b, ρ => kongr₂ (Zahl.sdiv hb) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .srem hb a b, ρ => kongr₂ (Zahl.srem hb) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .getBytes t f hf n i _ _ _, ρ =>
      zahl_ext (congrArg bytesZuZahl ((bytesAb_worldR σ t f hf _ n _).trans
        (congrArg (σ.bytesAb t f hf n) (congrArg Zahl.n (eval_ru σ₀ σ i ρ)))))
  | _, _, _, .band h0 h0' a b, ρ =>
      kongr₂ (Zahl.band h0 h0') (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .bor w h0 h0' hw1 hw2 a b, ρ =>
      kongr₂ (Zahl.bor w h0 h0' hw1 hw2) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .bxor w h0 h0' hw1 hw2 a b, ρ =>
      kongr₂ (Zahl.bxor w h0 h0' hw1 hw2) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .shl w hw1 hw2 h0 h0' a b, ρ =>
      kongr₂ (Zahl.shl w hw1 hw2 h0 h0') (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .shr w hw1 hw2 h0 h0' a b, ρ =>
      kongr₂ (Zahl.shr w hw1 hw2 h0 h0') (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .lt (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, ρ =>
      kongr₂ (fun (x : Zahl l1 h1) (y : Zahl l2 h2) => decide (x.n < y.n))
        (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .le (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, ρ =>
      kongr₂ (fun (x : Zahl l1 h1) (y : Zahl l2 h2) => decide (x.n ≤ y.n))
        (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .eq (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, ρ =>
      kongr₂ (fun (x : Zahl l1 h1) (y : Zahl l2 h2) => decide (x.n = y.n))
        (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .fllt (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, ρ =>
      kongr₂ (fun (x : Gleit l1 h1) (y : Gleit l2 h2) => gleitLt x.x y.x)
        (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .flle (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, ρ =>
      kongr₂ (fun (x : Gleit l1 h1) (y : Gleit l2 h2) => gleitLe x.x y.x)
        (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .and a b, ρ =>
      kongr₂ (fun (x y : Bool) => (x && y)) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .or a b, ρ =>
      kongr₂ (fun (x y : Bool) => (x || y)) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .not a, ρ => congrArg (fun (x : Bool) => !x) (eval_ru σ₀ σ a ρ)
  | _, _, _, .none _, _ => rfl
  | _, _, _, .some e, ρ => congrArg Option.some (eval_ru σ₀ σ e ρ)
  | _, _, _, .istSome (n := n) e, ρ =>
      congrArg (fun (x : Option (Zahl 0 (n - 1))) => x.isSome) (eval_ru σ₀ σ e ρ)
  | _, _, _, .case cs i nutz, ρ => by
      simp only [eval, ruE, evalNutz_cast]
      rw [evalNutz_ru σ₀ σ nutz ρ]
      exact (Val.relocateSum_mk (fun n => n + 1) id
        (fun _ v => ⟨some v.1, v.2⟩) cs i (evalNutz σ₀ nutz σ ρ)).symm
  | _, _, _, .why _ _, _ => rfl
  | _, _, _, .forallSlots t body _, ρ =>
      congrArg (fun p => (alleIndizes (D.count t)).all p)
        (funext fun k => eval_ru σ₀ σ body (Env.cons k ρ))
  | _, _, _, .existsSlots t body _, ρ =>
      congrArg (fun p => (alleIndizes (D.count t)).any p)
        (funext fun k => eval_ru σ₀ σ body (Env.cons k ρ))
  | _, _, _, .reaches t f hf a b _, ρ =>
      kongr₃ (fun F (x y : Zahl 0 (D.count t - 1)) => kette F (D.count t).toNat x.n y.n)
        (funext fun k => slot_cast_worldR σ t f hf _ k) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .arrNil, _ => funext fun j => j.elim0
  | _, _, _, .arrCons a b, ρ => by
      show arrConsW _ _ = valR (.arr _ _) (arrConsW (eval σ₀ a σ ρ) (eval σ₀ b σ ρ))
      erw [eval_ru σ₀ σ a ρ, eval_ru σ₀ σ b ρ]
      funext j
      simp only [arrConsW, valR]
      split <;> rfl
  | _, _, _, .arrGet a i, ρ => by
      show (eval (worldR σ₀) (ruE a) (worldR σ) (envR ρ)) _ = _
      erw [eval_ru σ₀ σ a ρ, eval_ru σ₀ σ i ρ]
      rfl
  | _, _, _, .arrSet a i v, ρ => by
      show arrSetW _ _ _ = valR (.arr _ _) (arrSetW (eval σ₀ a σ ρ) (eval σ₀ i σ ρ).fin (eval σ₀ v σ ρ))
      erw [eval_ru σ₀ σ a ρ, eval_ru σ₀ σ i ρ, eval_ru σ₀ σ v ρ]
      funext j
      simp only [arrSetW, valR]
      split <;> rfl
  | _, _, _, .strLit _ _, _ => rfl
  | _, _, _, .strLen e, ρ => by
      show strLenW _ = _
      erw [eval_ru σ₀ σ e ρ]
      rfl
  | _, _, _, .strCat e e', ρ => by
      show strCatW _ _ = _
      erw [eval_ru σ₀ σ e ρ, eval_ru σ₀ σ e' ρ]
      rfl
  | _, _, _, .strGet e e', ρ => by
      show strGetW _ _ = _
      erw [eval_ru σ₀ σ e ρ, eval_ru σ₀ σ e' ρ]
      rfl
  | _, _, _, .strEq e e', ρ => by
      show strEqW _ _ = _
      erw [eval_ru σ₀ σ e ρ, eval_ru σ₀ σ e' ρ]
      rfl
  | _, _, _, .strLt e e', ρ => by
      show strLtW _ _ = _
      erw [eval_ru σ₀ σ e ρ, eval_ru σ₀ σ e' ρ]
      rfl
  | _, _, _, .strWeit _ e, ρ => by
      show strWeitW _ _ = _
      erw [eval_ru σ₀ σ e ρ]
      rfl
  | _, _, _, .wenn c a b, ρ => by
      show (if wahr? (eval _ (ruE c) _ _) then eval _ (ruE a) _ _ else eval _ (ruE b) _ _) = _
      erw [eval_ru σ₀ σ c ρ, eval_ru σ₀ σ a ρ, eval_ru σ₀ σ b ρ]
      show (if wahr? (eval σ₀ c σ ρ) then _ else _) = valR _ (if wahr? (eval σ₀ c σ ρ) then _ else _)
      split <;> rfl
  | _, _, _, .eng e lo' hi' s, ρ => by
      show (if h : lo' ≤ (eval _ (ruE e) _ _).n ∧ (eval _ (ruE e) _ _).n ≤ hi' then _ else eval _ (ruE s) _ _) = _
      rw [eval_ru σ₀ σ s ρ]
      exact eng_kongr (eval_ru σ₀ σ e ρ) _
  | _, _, _, .intBuiltin1 op a, ρ => by
      show evalIntBuiltin1 (ibR op) (eval (worldR σ₀) (ruE a) (worldR σ) (envR ρ)) =
        valR _ (evalIntBuiltin1 op (eval σ₀ a σ ρ))
      rw [eval_ru σ₀ σ a ρ]
      exact eval_ib1_ru op _
  | _, _, _, .intBuiltin2 op a b, ρ => by
      show evalIntBuiltin2 (ibR op) (eval (worldR σ₀) (ruE a) (worldR σ) (envR ρ))
          (eval (worldR σ₀) (ruE b) (worldR σ) (envR ρ)) =
        valR _ (evalIntBuiltin2 op (eval σ₀ a σ ρ) (eval σ₀ b σ ρ))
      rw [eval_ru σ₀ σ a ρ, eval_ru σ₀ σ b ρ]
      exact eval_ib2_ru op _ _
  | _, _, _, .count n body, ρ => by
      show zaehleWahr n (fun k => wahr? (eval (worldR σ₀) (ruE body) (worldR σ) (Env.cons k (envR ρ)))) =
        zaehleWahr n (fun k => wahr? (eval σ₀ body σ (Env.cons k ρ)))
      refine zaehleWahr_congr n _ _ (fun k _ => ?_)
      exact congrArg wahr? (eval_ru σ₀ σ body (Env.cons k ρ))
  | _, _, _, .prod r args, ρ => by
      exact evalProd_cast_eq (Ty.map_eq_mapFields (fun n => n + 1) id _)
        (worldR σ₀) (worldR σ) (ruA args) (envR ρ) _ (evalProd_ru σ₀ σ args ρ)
  | _, _, _, .prodGet v i, ρ => by
      show prodGetW (FieldAt.mapNumbers (fun n => n + 1) id i)
        (eval (worldR σ₀) (ruE v) (worldR σ) (envR ρ)) = _
      rw [eval_ru σ₀ σ v ρ]
      show prodGetW (FieldAt.mapNumbers (fun n => n + 1) id i)
          (ProdVal.relocate (fun n => n + 1) id (fun _ v => ⟨some v.1, v.2⟩) _
            (eval σ₀ v σ ρ)) = _
      exact ProdVal.relocate_get _ _ _ _ i _
  | _, _, _, .prodSet v i e, ρ => by
      show prodSetW (FieldAt.mapNumbers (fun n => n + 1) id i)
        (eval (worldR σ₀) (ruE v) (worldR σ) (envR ρ))
        (eval (worldR σ₀) (ruE e) (worldR σ) (envR ρ)) = _
      rw [eval_ru σ₀ σ v ρ, eval_ru σ₀ σ e ρ]
      show prodSetW (FieldAt.mapNumbers (fun n => n + 1) id i)
          (ProdVal.relocate (fun n => n + 1) id (fun _ v => ⟨some v.1, v.2⟩) _
            (eval σ₀ v σ ρ))
          (Val.relocate (fun n => n + 1) id (fun _ v => ⟨some v.1, v.2⟩) _ (eval σ₀ e σ ρ)) = _
      exact (ProdVal.relocate_set _ _ _ _ i _ _).symm

/-- Field arguments evaluate to the relocated tuple (C01): the idle root shifts
    every field value through the same signature-aware map as `Val.relocate`. -/
theorem evalProd_ru (σ₀ σ : World D) : ∀ {Γ : Ctx} {Λ : List (Res D)} {fs : List Ty}
    (args : Args D Γ Λ fs) (ρ : Env D Γ),
    evalProd (worldR σ₀) (ruA args) (worldR σ) (envR ρ) =
      ((Ty.map_eq_mapFields (fun n => n + 1) id fs).symm ▸
        ProdVal.relocate (fun n => n + 1) id (fun _ v => ⟨some v.1, v.2⟩) fs (evalProd σ₀ args σ ρ))
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons e rest, ρ => by
      exact (ProdVal.pcons_congr (eval_ru σ₀ σ e ρ) (evalProd_ru σ₀ σ rest ρ)).trans
        (prodVal_cast_cons (D' := D.mitRuhe)
          (Ty.map_eq_mapFields (fun n => n + 1) id _).symm _ _).symm

theorem evalNutz_ru (σ₀ σ : World D) : ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option Ty}
    (n : NutzlastExpr D Γ Λ c) (ρ : Env D Γ),
    evalNutz (worldR σ₀) (ruN n) (worldR σ) (envR ρ) = nutzR c (evalNutz σ₀ n σ ρ)
  | _, _, _, .empty, _ => rfl
  | _, _, _, .val e, ρ => eval_ru σ₀ σ e ρ

end
theorem evalArgs_ru (σ₀ σ : World D) : ∀ {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty}
    (as : Args D Γ Λ τs) (ρ : Env D Γ),
    evalArgs (worldR σ₀) (ruA as) (worldR σ) (envR ρ) = envR (evalArgs σ₀ as σ ρ)
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons e rest, ρ => kongr₂ Env.cons (eval_ru σ₀ σ e ρ) (evalArgs_ru σ₀ σ rest ρ)

/-! ## 3. Contracts -/

end Gabbro.Grammatik
