/-
  File:      Grammatik/MitRuheSemantik.lean
  Subject:   EVERY FUNCTION OF `P` BEHAVES IN `P.mitRuhe` AS IN `P`
             (MitRuhe.lean): expressions evaluate to the translated value
             (`eval_ru`), reads record the translated events (`lese_worldR`),
             and the contracts of `P.mitRuhe` at `some f` hold exactly when
             those of `P` at `f` hold (`req_mitRuhe_iff`).
-/
import Grammatik.MitRuheStatisch

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Environments, worlds, events -/

theorem envR_get : ∀ {Γ : Ctx} {τ : Ty} (ρ : Env D Γ) (x : Var Γ τ),
    (envR ρ).get (varR x) = valR τ (ρ.get x)
  | _, _, .cons _ _, .hier => rfl
  | _, _, .cons _ ρ, .dort x => envR_get ρ x

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

theorem gibt_worldR (σ : World D) (L : D.Lock) : (worldR σ).gibt L = worldR (σ.gibt L) := rfl

theorem zahl_ext {lo hi : Int} {a b : Zahl lo hi} (h : a.n = b.n) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

theorem kongr₃ {α β γ δ : Sort _} (f : α → β → γ → δ) {a a' : α} {b b' : β} {c c' : γ}
    (ha : a = a') (hb : b = b') (hc : c = c') : f a b c = f a' b' c' := by
  subst ha; subst hb; subst hc; rfl

theorem cast_byte_gen (τ : Ty) (h : τ = .int 0 255) (h' : tyR τ = .int 0 255)
    (x : Val D.Fn D.sig τ) :
    (cast (congrArg (Val (Option D.Fn) (sigM D)) h') (valR τ x) : Byte) =
      (cast (congrArg (Val D.Fn D.sig) h) x : Byte) := by
  subst h; rfl

theorem cast_byte_worldR (σ : World D) (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (hf' : (D.mitRuhe).typ t f = .int 0 255) (k : Int) :
    (cast (congrArg (Wert D.mitRuhe) hf') ((worldR σ).slots t k f) : Byte) =
      (cast (congrArg (Wert D) hf) (σ.slots t k f) : Byte) :=
  cast_byte_gen (D.typ t f) hf hf' (σ.slots t k f)

theorem opt_cast_gen (τ : Ty) (m : Int) (h : τ = .opt m) (h' : tyR τ = .opt m)
    (x : Val D.Fn D.sig τ) :
    @Eq (Option (Zahl 0 (m - 1))) (h' ▸ valR τ x : Val (Option D.Fn) (sigM D) (.opt m))
      (h ▸ x : Val D.Fn D.sig (.opt m)) := by
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

/-! ## 2. Expressions -/

mutual

/-- **An expression of `P.mitRuhe` evaluates to the translated value** of
    the expression of `P`, on the translated worlds and environment. -/
theorem eval_ru (σ₀ σ : World D) : ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (ρ : Env D Γ), eval (worldR σ₀) (ruE e) (worldR σ) (envR ρ) = valR τ (eval σ₀ e σ ρ)
  | _, _, _, .lit _, _ => rfl
  | _, _, _, .wahr, _ => rfl
  | _, _, _, .falsch, _ => rfl
  | _, _, _, .var x, ρ => envR_get ρ x
  | _, _, _, .glob _ _, _ => rfl
  | _, _, _, .slot t f i _, ρ =>
      congrArg (fun z : Zahl 0 (D.count t - 1) => valR (D.typ t f) (σ.slots t z.n f))
        (eval_ru σ₀ σ i ρ)
  | _, _, _, .durch _ t _ f i _, ρ =>
      congrArg (fun z : Zahl 0 (D.count t - 1) => valR (D.typ t f) (σ.slots t z.n f))
        (eval_ru σ₀ σ i ρ)
  | _, _, _, .ptrOf .., _ => rfl
  | _, _, _, .fnref .., _ => rfl
  | _, _, _, .altGlob _ _, _ => rfl
  | _, _, _, .altSlot t f i _, ρ =>
      congrArg (fun z : Zahl 0 (D.count t - 1) => valR (D.typ t f) (σ₀.slots t z.n f))
        (eval_ru σ₀ σ i ρ)
  | _, _, _, .weiter h1 h2 e, ρ => congrArg (Zahl.weiter h1 h2) (eval_ru σ₀ σ e ρ)
  | _, _, _, .add a b, ρ => kongr₂ Zahl.add (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .sub a b, ρ => kongr₂ Zahl.sub (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .neg a, ρ => congrArg Zahl.neg (eval_ru σ₀ σ a ρ)
  | _, _, _, .mul a b, ρ => kongr₂ Zahl.mul (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .div h0 h1 a b, ρ => kongr₂ (Zahl.div h0 h1) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .rem h0 h1 a b, ρ => kongr₂ (Zahl.rem h0 h1) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .sdiv hb a b, ρ => kongr₂ (Zahl.sdiv hb) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .srem hb a b, ρ => kongr₂ (Zahl.srem hb) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .leseBytes t f hf n i _ _ _, ρ =>
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
  | _, _, _, .und a b, ρ =>
      kongr₂ (fun (x y : Bool) => (x && y)) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .oder a b, ρ =>
      kongr₂ (fun (x y : Bool) => (x || y)) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)
  | _, _, _, .nicht a, ρ => congrArg (fun (x : Bool) => !x) (eval_ru σ₀ σ a ρ)
  | _, _, _, .none _, _ => rfl
  | _, _, _, .some e, ρ => congrArg Option.some (eval_ru σ₀ σ e ρ)
  | _, _, _, .istSome (n := n) e, ρ =>
      congrArg (fun (x : Option (Zahl 0 (n - 1))) => x.isSome) (eval_ru σ₀ σ e ρ)
  | _, _, _, .fall cs i nutz, ρ =>
      congrArg (fun z => (⟨i, z⟩ : Σ i : Fin cs.length, Nutzlast (cs.get i)))
        (evalNutz_ru σ₀ σ nutz ρ)
  | _, _, _, .grund _ _, _ => rfl
  | _, _, _, .forallSlots t body _, ρ =>
      congrArg (fun p => (alleIndizes (D.count t)).all p)
        (funext fun k => eval_ru σ₀ σ body (Env.cons k ρ))
  | _, _, _, .existsSlots t body _, ρ =>
      congrArg (fun p => (alleIndizes (D.count t)).any p)
        (funext fun k => eval_ru σ₀ σ body (Env.cons k ρ))
  | _, _, _, .reaches t f hf a b _, ρ =>
      kongr₃ (fun F (x y : Zahl 0 (D.count t - 1)) => kette F (D.count t).toNat x.n y.n)
        (funext fun k => slot_cast_worldR σ t f hf _ k) (eval_ru σ₀ σ a ρ) (eval_ru σ₀ σ b ρ)

theorem evalNutz_ru (σ₀ σ : World D) : ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)}
    (n : NutzlastExpr D Γ Λ c) (ρ : Env D Γ),
    evalNutz (worldR σ₀) (ruN n) (worldR σ) (envR ρ) = evalNutz σ₀ n σ ρ
  | _, _, _, .keine, _ => rfl
  | _, _, _, .zahl e, ρ => eval_ru σ₀ σ e ρ

end

theorem evalArgs_ru (σ₀ σ : World D) : ∀ {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty}
    (as : Args D Γ Λ τs) (ρ : Env D Γ),
    evalArgs (worldR σ₀) (ruA as) (worldR σ) (envR ρ) = envR (evalArgs σ₀ as σ ρ)
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons e rest, ρ => kongr₂ Env.cons (eval_ru σ₀ σ e ρ) (evalArgs_ru σ₀ σ rest ρ)

/-! ## 3. Contracts -/

theorem eval_umΓ {Γ Γ' : Ctx} {Λ : List (Res D)} {τ : Ty} (h : Γ = Γ') (e : Expr D Γ Λ τ)
    (σ₀ σ : World D) (ρ : Env D Γ') : eval σ₀ (Expr.umΓ h e) σ ρ = eval σ₀ e σ (h ▸ ρ) := by
  subst h; rfl

theorem eval_umΛ' {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (h : Λ = Λ') (e : Expr D Γ Λ τ)
    (σ₀ σ : World D) (ρ : Env D Γ) : eval σ₀ (Expr.umΛ h e) σ ρ = eval σ₀ e σ ρ := by
  subst h; rfl

/-- **`requires` of `P.mitRuhe` at `some f` is `requires` of `P` at `f`**, on
    the translated world and parameters. -/
theorem req_mitRuhe_iff (P : Programm D) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) :
    ReqAmEintritt P.mitRuhe (some f) (worldR σ) (envR ρ) ↔ ReqAmEintritt P f σ ρ := by
  have e : eval (worldR σ) (P.mitRuhe.requires (some f)) (worldR σ) (envR ρ) =
      valR .bool (eval σ (P.requires f) σ ρ) := (eval_umΛ' _ _ _ _ _).trans (eval_ru σ σ _ ρ)
  show wahr? (eval (worldR σ) (P.mitRuhe.requires (some f)) (worldR σ) (envR ρ)) = true ↔
    wahr? (eval σ (P.requires f) σ ρ) = true
  rw [e]
  rfl

#print axioms Gabbro.Grammatik.eval_ru
#print axioms Gabbro.Grammatik.evalArgs_ru
#print axioms Gabbro.Grammatik.lese_worldR
#print axioms Gabbro.Grammatik.req_mitRuhe_iff

end Gabbro.Grammatik
