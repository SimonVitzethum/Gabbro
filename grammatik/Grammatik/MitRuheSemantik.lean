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


/-! ## 4. Outcomes, writes, the oracle -/

/-- A result value, translated. -/
def ergR : (e : Option Ty) → ErgVal D e → ErgVal D.mitRuhe (e.map tyR)
  | none, _ => ()
  | some τ, v => valR τ v

/-- A logic outcome, translated (`f ↦ some f`). -/
def logikR : Logik D → Logik D.mitRuhe
  | .vorbedingung f => .vorbedingung (some f)
  | .nachbedingung f => .nachbedingung (some f)
  | .invariante i => .invariante i
  | .schleife => .schleife
  | .abstieg f => .abstieg (some f)
  | .vorzustand => .vorzustand

/-- A hardware outcome, translated. -/
def hwR : Hardware D → Hardware D.mitRuhe
  | .annahme a => .annahme a
  | .fortschritt a => .fortschritt a
  | .ieee => .ieee
  | .register r => .register r
  | .geraet r => .geraet r
  | .sichtbarkeit a => .sichtbarkeit a

/-- A statement outcome, translated. -/
def ausR {V : Vertrag D} {l : Bool} {Γ : Ctx} :
    Ausgang V l Γ → Ausgang (vertragR V) l (Γ.map tyR)
  | .ok σ ρ => .ok (worldR σ) (envR ρ)
  | .zurueck σ v => .zurueck (worldR σ) (ergR V.erg v)
  | .grund σ r => .grund (worldR σ) r
  | .leave h σ ρ => .leave h (worldR σ) (envR ρ)
  | .next h σ ρ => .next h (worldR σ) (envR ρ)
  | .logik e => .logik (logikR e)
  | .hardware e => .hardware (hwR e)

/-- An end-block outcome, translated. -/
def endR {V : Vertrag D} {l : Bool} {Γ : Ctx} :
    EndAusgang V l Γ → EndAusgang (vertragR V) l (Γ.map tyR)
  | .zurueck σ v => .zurueck (worldR σ) (ergR V.erg v)
  | .grund σ r => .grund (worldR σ) r
  | .leave h σ ρ => .leave h (worldR σ) (envR ρ)
  | .next h σ ρ => .next h (worldR σ) (envR ρ)
  | .logik e => .logik (logikR e)
  | .hardware e => .hardware (hwR e)

/-- A call outcome, translated. -/
def rufR {f : D.Fn} : RufAusgang f → RufAusgang (D := D.mitRuhe) (some f)
  | .ok σ v => .ok (worldR σ) (ergR (D.erg f) v)
  | .grund σ r => .grund (worldR σ) r
  | .logik e => .logik (logikR e)
  | .hardware e => .hardware (hwR e)

/-- **A handler of `D.mitRuhe` that answers translated calls with the
    translated answers of `R`.** -/
def RufRu (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) →
      RufAusgang f) : Prop :=
  ∀ g σ ρ, R' (some g) (worldR σ) (envR ρ) = rufR (R g σ ρ)

section Aus

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem envR_tail {τ : Ty} (ρ : Env D (τ :: Γ)) : (envR ρ).tail = envR ρ.tail := by
  cases ρ; rfl

theorem ausR_schrumpf {τ : Ty} (a : Ausgang V l (τ :: Γ)) :
    (ausR a).schrumpf = ausR a.schrumpf := by
  cases a <;> simp only [ausR, Ausgang.schrumpf, envR_tail]

theorem endR_schrumpf {τ : Ty} (a : EndAusgang V l (τ :: Γ)) :
    (endR a).schrumpf = endR a.schrumpf := by
  cases a <;> simp only [endR, EndAusgang.schrumpf, envR_tail]

theorem endR_zuAusgang (a : EndAusgang V l Γ) : (endR a).zuAusgang = ausR a.zuAusgang := by
  cases a <;> rfl

theorem ausR_gibt (L : D.Lock) (a : Ausgang V l Γ) :
    (ausR a).mapWelt (fun x : World D.mitRuhe => x.gibt L) =
      ausR (a.mapWelt (fun x : World D => x.gibt L)) := by
  cases a <;> rfl

theorem ausR_ausSchleife (a : Ausgang V true Γ) :
    (ausR a).ausSchleife (l := l) = ausR (a.ausSchleife (l := l)) := by
  cases a <;> rfl

end Aus

theorem storeSlot_worldR (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) :
    (worldR σ).storeSlot t k f (valR (D.typ t f) v) = worldR (σ.storeSlot t k f v) := by
  refine welt_ext ?_ rfl rfl
  funext t' k' f'
  simp only [World.storeSlot, worldR]
  by_cases ht : t' = t
  · subst ht
    simp only [dite_true]
    by_cases hk : k' = k
    · by_cases hf : f' = f
      · subst hf; simp [hk]
      · simp [hk, hf]
    · simp [hk]
  · simp [ht]

theorem storeGlob_worldR (σ : World D) (g : D.Glob) (v : Wert D (D.gtyp g)) :
    (worldR σ).storeGlob g (valR (D.gtyp g) v) = worldR (σ.storeGlob g v) := by
  refine welt_ext rfl ?_ rfl
  funext g'
  simp only [World.storeGlob, worldR]
  by_cases hg : g' = g
  · subst hg; simp
  · simp [hg]

theorem schreibSlot_worldR (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) :
    (worldR σ).schreibSlot t (Λ.map resR) k f (valR (D.typ t f) v) =
      worldR (σ.schreibSlot t Λ k f v) := by
  unfold World.schreibSlot
  rw [storeSlot_worldR]
  refine welt_ext rfl rfl ?_
  show [Ereignis.zugriff (D := D.mitRuhe) t true (Λ.map resR) (worldR σ).haelt] ++ _ =
    ([Ereignis.zugriff t true Λ σ.haelt] ++ _).map (evR (D := D))
  rw [haelt_worldR]
  rfl

theorem schreibGlob_worldR (σ : World D) (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) :
    (worldR σ).schreibGlob g (Λ.map resR) (valR (D.gtyp g) v) = worldR (σ.schreibGlob g Λ v) := by
  unfold World.schreibGlob
  rw [storeGlob_worldR]
  refine welt_ext rfl rfl ?_
  show [Ereignis.gzugriff (D := D.mitRuhe) g true (Λ.map resR) (worldR σ).haelt] ++ _ =
    ([Ereignis.gzugriff g true Λ σ.haelt] ++ _).map (evR (D := D))
  rw [haelt_worldR]
  rfl

theorem cast_symm_gen (τ : Ty) (h : τ = .int 0 255) (h' : tyR τ = .int 0 255) (b : Byte) :
    (cast (congrArg (Val (Option D.Fn) (sigM D)) h').symm b : Val (Option D.Fn) (sigM D) (tyR τ)) =
      valR τ (cast (congrArg (Val D.Fn D.sig) h).symm b) := by
  subst h; rfl

theorem schreibBytes_worldR (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (hf' : (D.mitRuhe).typ t f = .int 0 255) (Λ : List (Res D)) :
    ∀ (bs : List Byte) (σ : World D) (k : Int),
      (worldR σ).schreibBytes t f hf' (Λ.map resR) k bs = worldR (σ.schreibBytes t f hf Λ k bs)
  | [], _, _ => rfl
  | b :: bs, σ, k => by
      simp only [World.schreibBytes]
      have e : (cast (congrArg (Wert D.mitRuhe) hf').symm (b : Wert D.mitRuhe (.int 0 255)) :
          Wert D.mitRuhe ((D.mitRuhe).typ t f)) =
          valR (D.typ t f) (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255))) :=
        cast_symm_gen (D.typ t f) hf hf' b
      rw [e, schreibSlot_worldR, schreibBytes_worldR t f hf hf' Λ bs]

theorem wirkt_mitRuhe (O : Orakel D) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    O.mitRuhe.wirkt a (worldR σ) (envR ρ) = (worldR (O.wirkt a σ ρ).1, (O.wirkt a σ ρ).2) := by
  show (worldR (O.wirkt a (worldZ (worldR σ)) (envZ (envR ρ))).1,
    (O.wirkt a (worldZ (worldR σ)) (envZ (envR ρ))).2) = _
  rw [worldZ_worldR, envZ_envR]

theorem einpassen_ru : ∀ (τ : Ty) (n : Int),
    einpassen (D := D.mitRuhe) (tyR τ) n = (einpassen (D := D) τ n).map (valR τ)
  | .int lo hi, n => by
      show einpassen (D := D.mitRuhe) (.int lo hi) n =
        Option.map (valR (.int lo hi)) (einpassen (D := D) (.int lo hi) n)
      simp only [einpassen]
      split <;> rfl
  | .bool, _ => rfl
  | .opt m, n => by
      show einpassen (D := D.mitRuhe) (.opt m) n =
        Option.map (valR (.opt m)) (einpassen (D := D) (.opt m) n)
      simp only [einpassen]
      split
      · rfl
      · split <;> rfl
  | .sum _, _ => rfl
  | .grund m, n => by
      show einpassen (D := D.mitRuhe) (.grund m) n =
        Option.map (valR (.grund m)) (einpassen (D := D) (.grund m) n)
      simp only [einpassen]
      split <;> rfl
  | .never, _ => rfl
  | .fl _ _, _ => rfl
  | .fnptr _, _ => rfl
  | .ptr _ _, _ => rfl

theorem einpassenErg_ru : ∀ (e : Option Ty) (n : Int),
    einpassenErg (D := D.mitRuhe) (e.map tyR) n = (einpassenErg (D := D) e n).map (ergR e)
  | none, _ => rfl
  | some τ, n => einpassen_ru τ n

theorem axiomAntwort_ru (O : Orakel D) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    axiomAntwort O.mitRuhe a (worldR σ) (envR ρ) =
      (worldR (axiomAntwort O a σ ρ).1, (axiomAntwort O a σ ρ).2.map (ergR (D.aerg a))) := by
  unfold axiomAntwort
  rw [wirkt_mitRuhe]
  exact congrArg _ (einpassenErg_ru (D.aerg a) _)

theorem regLies_mitRuhe (O : Orakel D) (r : D.Reg) (σ : World D) :
    O.mitRuhe.regLies r (worldR σ) = O.regLies r σ := by
  show O.regLies r (worldZ (worldR σ)) = _
  rw [worldZ_worldR]

theorem sichtbar_mitRuhe (O : Orakel D) (g : D.Glob) (σ : World D) :
    O.mitRuhe.sichtbar g (worldR σ) = O.sichtbar g σ := by
  show O.sichtbar g (worldZ (worldR σ)) = _
  rw [worldZ_worldR]

theorem rzusage_mitRuhe (r : D.Reg) (v : Wert D (D.rtyp r)) :
    (D.mitRuhe).rzusage r (valR (D.rtyp r) v) = D.rzusage r v := by
  show D.rzusage r (valZ (D.rtyp r) (valR (D.rtyp r) v)) = _
  rw [valZ_valR]



/-! ## 5. Statement helpers -/

section Hilfen

variable (O : Orakel D) (passes : Nat)

theorem execStmt_nachΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (s : Stmt D V l Γ Λ Λ₁) (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R (Stmt.nachΛ h s) σ ρ = execStmt O passes R s σ ρ := by
  subst h; rfl

theorem execBlock_vorΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ Λ' : List (Res D)} (h : Λ₁ = Λ₂)
    (b : Block D V l Γ Λ₁ Λ') (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (Block.vorΛ h b) σ ρ = execBlock O passes R b σ ρ := by
  subst h; rfl

theorem execEnd_umΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (e : Endblock D V l Γ Λ₁) (σ : World D) (ρ : Env D Γ) :
    execEnd O passes R (Endblock.umΛ h e) σ ρ = execEnd O passes R e σ ρ := by
  subst h; rfl

end Hilfen

theorem envR_set : ∀ {Γ : Ctx} {τ : Ty} (ρ : Env D Γ) (x : Var Γ τ) (v : Wert D τ),
    (envR ρ).set (varR x) (valR τ v) = envR (ρ.set x v)
  | _, _, .cons _ _, .hier, _ => rfl
  | _, _, .cons w ρ, .dort x, v => congrArg (Env.cons _) (envR_set ρ x v)

theorem evalErg_ru (σ₀ σ : World D) {Γ : Ctx} {Λ : List (Res D)} :
    ∀ {e : Option Ty} (a : ErgExpr D Γ Λ e) (ρ : Env D Γ),
      evalErg (worldR σ₀) (ruErg a) (worldR σ) (envR ρ) = ergR e (evalErg σ₀ a σ ρ)
  | _, .keine, _ => rfl
  | _, .wert e, ρ => eval_ru σ₀ σ e ρ

theorem ergWert_ru {τ : Ty} : ∀ {e : Option Ty} (he : e = some τ)
    (he' : e.map tyR = some (tyR τ)) (v : ErgVal D e),
    ergWert (D := D.mitRuhe) he' (ergR e v) = valR τ (ergWert he v)
  | _, rfl, _, _ => rfl

theorem armEnv_ru {Γ : Ctx} : ∀ {c : Option (Int × Int)} (nutz : Nutzlast c) (ρ : Env D Γ),
    HEq (envR (armEnv nutz ρ)) (armEnv (D := D.mitRuhe) nutz (envR ρ))
  | none, _, _ => HEq.rfl
  | some (_, _), _, _ => HEq.rfl

theorem map_valR_int (lo hi : Int) (l : List (Zahl lo hi)) :
    l.map (valR (D := D) (.int lo hi)) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (a :: ·) ih

theorem umsig_ru {f : D.Fn} {n : Nat} (hf : D.sig f = n)
    (hf' : (D.mitRuhe).sig (some f) = n + 1) (ρ : Env D (D.sigNr n).params) :
    umsig (D := D.mitRuhe) hf' (envR ρ) = envR (umsig hf ρ) := by
  subst hf
  rfl

theorem int_cast_gen (τ : Ty) (lo hi : Int) (h : τ = .int lo hi) (h' : tyR τ = .int lo hi)
    (x : Val D.Fn D.sig τ) :
    @Eq (Zahl lo hi) (h' ▸ valR τ x : Val (Option D.Fn) (sigM D) (.int lo hi))
      (h ▸ x : Val D.Fn D.sig (.int lo hi)) := by
  subst h; rfl

theorem int_cast_gen' (τ : Ty) (lo hi : Int) (h : τ = .int lo hi) (h' : tyR τ = .int lo hi)
    (z : Zahl lo hi) :
    (h' ▸ (z : Val (Option D.Fn) (sigM D) (.int lo hi)) : Val (Option D.Fn) (sigM D) (tyR τ)) =
      valR τ (h ▸ (z : Val D.Fn D.sig (.int lo hi)) : Val D.Fn D.sig τ) := by
  subst h; rfl

/-! ## 6. Loops -/

section Schleifen

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem traverseLauf_ru {τ : Ty}
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (schritt' : World D.mitRuhe → Env D.mitRuhe (tyR τ :: Γ.map tyR) →
      Ausgang (vertragR V) true (tyR τ :: Γ.map tyR))
    (inv : World D → Env D Γ → World D × Bool)
    (inv' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → World D.mitRuhe × Bool)
    (hs : ∀ σ ρ, schritt' (worldR σ) (envR ρ) = ausR (schritt σ ρ))
    (hi : ∀ σ ρ, inv' (worldR σ) (envR ρ) = (worldR (inv σ ρ).1, (inv σ ρ).2)) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ),
      traverseLauf (l := l) schritt' inv' (ks.map (valR τ)) (worldR σ) (envR ρ) =
        ausR (traverseLauf (l := l) schritt inv ks σ ρ)
  | [], σ, ρ => by
      simp only [List.map_nil, traverseLauf, hi]
      by_cases hc : (inv σ ρ).2 = true <;> simp only [hc, if_true, if_false] <;> rfl
  | k :: ks, σ, ρ => by
      simp only [List.map_cons, traverseLauf, hi]
      by_cases hc : (inv σ ρ).2 = false
      · simp only [hc, if_true]; rfl
      · simp only [hc, if_false]
        have e := hs (inv σ ρ).1 (Env.cons k ρ)
        change schritt' (worldR (inv σ ρ).1) (Env.cons (valR τ k) (envR ρ)) = _ at e
        rw [e]
        cases schritt (inv σ ρ).1 (Env.cons k ρ) with
        | ok σ' ρ' =>
            simp only [ausR, envR_tail]
            exact traverseLauf_ru schritt schritt' inv inv' hs hi ks σ' ρ'.tail
        | next h σ' ρ' =>
            simp only [ausR, envR_tail]
            exact traverseLauf_ru schritt schritt' inv inv' hs hi ks σ' ρ'.tail
        | leave h σ' ρ' =>
            simp only [ausR, envR_tail, hi]
            by_cases hc' : (inv σ' ρ'.tail).2 = true <;> simp only [hc', if_true, if_false] <;> rfl
        | zurueck => rfl
        | grund => rfl
        | logik => rfl
        | hardware => rfl

theorem retryLauf_ru
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (schritt' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → Ausgang (vertragR V) true (Γ.map tyR))
    (bis : World D → Env D Γ → World D × Bool)
    (bis' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → World D.mitRuhe × Bool)
    (ueber : World D → Env D Γ → Ausgang V l Γ)
    (ueber' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → Ausgang (vertragR V) l (Γ.map tyR))
    (hs : ∀ σ ρ, schritt' (worldR σ) (envR ρ) = ausR (schritt σ ρ))
    (hb : ∀ σ ρ, bis' (worldR σ) (envR ρ) = (worldR (bis σ ρ).1, (bis σ ρ).2))
    (hu : ∀ σ ρ, ueber' (worldR σ) (envR ρ) = ausR (ueber σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      retryLauf schritt' bis' ueber' n (worldR σ) (envR ρ) =
        ausR (retryLauf schritt bis ueber n σ ρ)
  | 0, σ, ρ => by
      simp only [retryLauf, hb]
      by_cases hc : (bis σ ρ).2 = true <;> simp only [hc, if_true, if_false, hu] <;> rfl
  | n + 1, σ, ρ => by
      simp only [retryLauf, hb]
      by_cases hc : (bis σ ρ).2 = true
      · simp only [hc, if_true]; rfl
      · simp only [hc, if_false, Bool.false_eq_true]
        rw [hs]
        cases schritt (bis σ ρ).1 ρ with
        | ok σ' ρ' => exact retryLauf_ru schritt schritt' bis bis' ueber ueber' hs hb hu n σ' ρ'
        | next h σ' ρ' => exact retryLauf_ru schritt schritt' bis bis' ueber ueber' hs hb hu n σ' ρ'
        | leave h σ' ρ' => rfl
        | zurueck => rfl
        | grund => rfl
        | logik => rfl
        | hardware => rfl

theorem foreverLauf_ru (a : D.Annahme)
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (schritt' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → Ausgang (vertragR V) true (Γ.map tyR))
    (inv : World D → Env D Γ → World D × Bool)
    (inv' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → World D.mitRuhe × Bool)
    (hs : ∀ σ ρ, schritt' (worldR σ) (envR ρ) = ausR (schritt σ ρ))
    (hi : ∀ σ ρ, inv' (worldR σ) (envR ρ) = (worldR (inv σ ρ).1, (inv σ ρ).2)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      foreverLauf (D := D.mitRuhe) (l := l) a schritt' inv' n (worldR σ) (envR ρ) =
        ausR (foreverLauf (l := l) a schritt inv n σ ρ)
  | 0, _, _ => rfl
  | n + 1, σ, ρ => by
      simp only [foreverLauf, hi]
      by_cases hc : (inv σ ρ).2 = false
      · simp only [hc, if_true]; rfl
      · simp only [hc, if_false]
        rw [hs]
        cases schritt (inv σ ρ).1 ρ with
        | ok σ' ρ' => exact foreverLauf_ru a schritt schritt' inv inv' hs hi n σ' ρ'
        | next h σ' ρ' => exact foreverLauf_ru a schritt schritt' inv inv' hs hi n σ' ρ'
        | leave h σ' ρ' => rfl
        | zurueck => rfl
        | grund => rfl
        | logik => rfl
        | hardware => rfl

end Schleifen


#print axioms Gabbro.Grammatik.eval_ru
#print axioms Gabbro.Grammatik.evalArgs_ru
#print axioms Gabbro.Grammatik.lese_worldR
#print axioms Gabbro.Grammatik.req_mitRuhe_iff

end Gabbro.Grammatik
