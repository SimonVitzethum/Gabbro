/-
  File:      Grammatik/MitRuheSemantik.lean
  Subject:   EVERY FUNCTION OF P BEHAVES IN P.mitRuhe AS IN P (MitRuhe.lean).
             Expressions evaluate to the translated value (eval_ru); reads
             record the translated events (lese_worldR); every statement,
             block and end block of a translated body runs, from the
             translated world and environment under O.mitRuhe, to the
             translated outcome, given call handlers that answer translated
             calls with translated answers (execStmt_ru, execBlock_ru,
             execEnd_ru); hence the body of some f in P.mitRuhe runs as the
             body of f in P (rumpf_mitRuhe_verhalten), requires holds at some f
             exactly when it holds at f (req_mitRuhe_iff), and every CALL --
             requires, body, ensures, owed invariants, at every depth -- of
             P.mitRuhe at some f behaves as the call of P at f
             (rufAt_mitRuhe; the generic form of gPB_wie_gP, Schlusssatz104).

  NOT here (open): the same for execEndH, the lock-aware semantics the user
  obligation KoerperGutS is stated against (it quantifies over oracles,
  environment moves and handlers on the D.mitRuhe side, each of which is the
  translation of one on the D side); with it the user obligation on P
  transfers to P.mitRuhe.
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
  | .bereich => .bereich

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

theorem slotInt_cast_worldR {lo hi : Int} (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hτ : D.typ t f = .int lo hi) (hτ' : (D.mitRuhe).typ t f = .int lo hi) (k : Int) :
    @Eq (Zahl lo hi) (hτ' ▸ (worldR σ).slots t k f : Wert D.mitRuhe (.int lo hi))
      (hτ ▸ σ.slots t k f : Wert D (.int lo hi)) :=
  int_cast_gen (D.typ t f) lo hi hτ hτ' (σ.slots t k f)

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



/-! ## 7. Every statement, block and end block behaves as translated -/

theorem valR_bool (b : Bool) : valR (D := D) .bool b = b := rfl
theorem valR_int {lo hi : Int} (z : Zahl lo hi) : valR (D := D) (.int lo hi) z = z := rfl
theorem valR_opt {n : Int} (z : Option (Zahl 0 (n - 1))) : valR (D := D) (.opt n) z = z := rfl
theorem valR_fl {lo hi : Int × Int} (z : Gleit lo hi) : valR (D := D) (.fl lo hi) z = z := rfl
theorem valR_fnptr {n : Nat} (f : D.Fn) (h : D.sig f = n) :
    valR (D := D) (.fnptr n) ⟨f, h⟩ = ⟨some f, congrArg (· + 1) h⟩ := rfl

theorem orte2 {Γ : Ctx} {Λ : List (Res D)} {τ₁ τ₂ : Ty} (a : Expr D Γ Λ τ₁) (b : Expr D Γ Λ τ₂) :
    (ruE a).orte ++ (ruE b).orte = a.orte ++ b.orte := kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)

section Haupt

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
  (hR : RufRu R R')

include hR

set_option maxHeartbeats 4000000 in
mutual

/-- **A translated statement runs as the statement**: from the translated
    world and environment to the translated outcome, given a handler that
    answers translated calls with translated answers. -/
theorem execStmt_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    execStmt O.mitRuhe passes R' (ruS s) (worldR σ) (envR ρ) = ausR (execStmt O passes R s σ ρ)
  | _, _, Λ, _, .assignSlot t f i e hw hL, σ, ρ => by
      simp only [ruS, execStmt]
      rw [orte2, lese_worldR, eval_ru, eval_ru, schreibSlot_worldR]
      rfl
  | _, _, Λ, _, .assignDurch p t ht f i e hw hL, σ, ρ => by
      simp only [ruS, execStmt]
      rw [show (ruE p).orte ++ (ruE i).orte ++ (ruE e).orte = p.orte ++ i.orte ++ e.orte from
        kongr₂ (· ++ ·) (orte2 p i) (ruE_orte e), lese_worldR, eval_ru, eval_ru, schreibSlot_worldR]
      rfl
  | _, _, Λ, _, .assignGlob g e hw hL, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR, eval_ru, schreibGlob_worldR]
      rfl
  | _, _, Λ, _, .schreibBytes t f hf n i hlo hhi e hw hL, σ, ρ => by
      simp only [ruS, execStmt]
      rw [orte2, lese_worldR, eval_ru, eval_ru, schreibBytes_worldR t f hf]
      rfl
  | _, _, Λ, _, .assignVar x e, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR, eval_ru, envR_set]
      rfl
  | _, _, Λ, _, .uebergang (lo := lo) (hi := hi) t f hτ i von nach hn he hw hL, σ, ρ => by
      simp only [ruS, execStmt]
      erw [show (Sum.inl t :: (ruE i).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
        Sum.inl t :: i.orte from congrArg (Sum.inl t :: ·) (ruE_orte i)]
      erw [lese_worldR, eval_ru]
      erw [slotInt_cast_worldR _ t f hτ (congrArg tyR hτ)]
      by_cases hc : (hτ ▸ (σ.lese Λ (Sum.inl t :: i.orte)).slots t
          (eval (σ.lese Λ (Sum.inl t :: i.orte)) i (σ.lese Λ (Sum.inl t :: i.orte)) ρ).n f :
          Wert D (.int lo hi)).n = von
      · erw [if_pos hc, if_pos hc, int_cast_gen' (D.typ t f) lo hi hτ (congrArg tyR hτ) _, schreibSlot_worldR]
        rfl
      · erw [if_neg hc, if_neg hc]
        rfl
  | _, _, Λ, _, .ite c t e, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR, eval_ru]
      cases h : (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ : Bool)
      · simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
        exact execBlock_ru e _ ρ
      · simp only [wahr?, valR_bool, h, if_true]
        exact execBlock_ru t _ ρ
  | _, _, Λ, _, .onOption o p a, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases h : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ with
      | none => exact execBlock_ru a _ ρ
      | some k =>
          simp only
          rw [← ausR_schrumpf, ← execBlock_ru p _ (Env.cons k ρ)]
          rfl
  | _, _, Λ, _, .onTag v arms, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR, eval_ru]
      exact execArms_ru arms _ _ ρ
  | _, _, Λ, _, .onGrund r arms, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR, eval_ru]
      exact execGrund_ru arms _ _ ρ
  | _, _, Λ, _, .call g args hp hr, σ, ρ => by
      simp only [ruS]
      erw [execStmt_nachΛ]
      simp only [execStmt]
      erw [ruA_orte, lese_worldR, evalArgs_ru, hR]
      cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | ok σ' v => (try erw [hx]); rfl
      | grund σ' r => exact (Fin.cast hr r).elim0
      | logik e => (try erw [hx]); rfl
      | hardware e => (try erw [hx]); rfl
  | _, _, Λ, _, .callInd (n := n) p args hp hr, σ, ρ => by
      simp only [ruS]
      erw [execStmt_nachΛ]
      simp only [execStmt]
      erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
        kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
      erw [lese_worldR, eval_ru, evalArgs_ru]
      cases h : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ with
      | mk g hg =>
          rw [valR_fnptr]
          dsimp only
          erw [umsig_ru hg, hR]
          cases hx : R g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
          | ok σ' v => (try erw [hx]); rfl
          | grund σ' r => exact keinGrundSig hg hr r
          | logik e => (try erw [hx]); rfl
          | hardware e => (try erw [hx]); rfl
  | _, _, Λ, _, .locks L hr body, σ, ρ => by
      simp only [ruS, execStmt]
      rw [nimmt_worldR]
      exact (congrArg _ (execBlock_ru body (σ.nimmt L) ρ)).trans (ausR_gibt L _)
  | _, _, _, _, .breaking _ body, σ, ρ => by
      simp only [ruS, execStmt]
      exact execBlock_ru body σ ρ
  | _, _, Λ, _, .traverse t inv body, σ, ρ => by
      simp only [ruS, execStmt]
      conv => lhs; rw [← map_valR_int (D := D) 0 (D.count t - 1) (alleIndizes (D.count t))]
      refine traverseLauf_ru (execBlock O passes R body) (execBlock O.mitRuhe passes R' (ruB body))
        (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
        (fun σ ρ => (σ.lese (Λ.map resR) (ruE inv).orte,
          wahr? (eval (σ.lese (Λ.map resR) (ruE inv).orte) (ruE inv) (σ.lese (Λ.map resR) (ruE inv).orte) ρ)))
        (fun σ ρ => execBlock_ru body σ ρ) (fun σ ρ => ?_) (alleIndizes (D.count t)) σ ρ
      simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?]
  | _, _, Λ, _, .retry n bis body ueber, σ, ρ => by
      simp only [ruS, execStmt]
      refine retryLauf_ru (execBlock O passes R body) (execBlock O.mitRuhe passes R' (ruB body))
        (fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ)))
        (fun σ ρ => (σ.lese (Λ.map resR) (ruE bis).orte,
          wahr? (eval (σ.lese (Λ.map resR) (ruE bis).orte) (ruE bis) (σ.lese (Λ.map resR) (ruE bis).orte) ρ)))
        (execBlock O passes R ueber) (execBlock O.mitRuhe passes R' (ruB ueber))
        (fun σ ρ => execBlock_ru body σ ρ) (fun σ ρ => ?_) (fun σ ρ => execBlock_ru ueber σ ρ) n σ ρ
      simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?]
  | _, _, Λ, _, .forever a inv body, σ, ρ => by
      simp only [ruS, execStmt]
      refine foreverLauf_ru a (execBlock O passes R body) (execBlock O.mitRuhe passes R' (ruB body))
        (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
        (fun σ ρ => (σ.lese (Λ.map resR) (ruE inv).orte,
          wahr? (eval (σ.lese (Λ.map resR) (ruE inv).orte) (ruE inv) (σ.lese (Λ.map resR) (ruE inv).orte) ρ)))
        (fun σ ρ => execBlock_ru body σ ρ) (fun σ ρ => ?_) passes σ ρ
      simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?]
  | _, _, Λ, _, .axiomCall a args h hw hg hd hgd, σ, ρ => by
      simp only [ruS, execStmt]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ru]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => rfl
          | some _ => rfl
  | _, _, Λ, _, .regSchreib r hk e, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR]
      rfl
  | _, _, _, _, .transition .., σ, ρ => rfl
  | _, _, Λ, _, .publish g e payload hp hw hL, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR, eval_ru, schreibGlob_worldR]
      rfl
  | _, _, _, _, .advances .., σ, ρ => by
      simp only [ruS]
      erw [execStmt_nachΛ]
      rfl
  | _, _, _, _, .retires .., σ, ρ => by
      simp only [ruS]
      erw [execStmt_nachΛ]
      rfl
  | _, _, Λ, _, .ret e hΛ, σ, ρ => by
      simp only [ruS, execStmt]
      erw [ruErg_orte, lese_worldR, evalErg_ru]
      rfl
  | _, _, _, _, .retGrund .., σ, ρ => rfl
  | _, _, _, _, .leave _, σ, ρ => rfl
  | _, _, _, _, .next _, σ, ρ => rfl

theorem execBlock_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    execBlock O.mitRuhe passes R' (ruB b) (worldR σ) (envR ρ) = ausR (execBlock O passes R b σ ρ)
  | _, _, _, _, .nil, σ, ρ => rfl
  | _, _, _, _, .cons s rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [execStmt_ru s σ ρ]
      cases execStmt O passes R s σ ρ with
      | ok σ' ρ' => exact execBlock_ru rest σ' ρ'
      | _ => rfl
  | _, _, Λ, _, .bind e rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [ruE_orte, lese_worldR, eval_ru, ← ausR_schrumpf, ← execBlock_ru rest _ _]
      rfl
  | _, _, Λ, _, .bindCall g args he hp hr rest, σ, ρ => by
      simp only [ruB, execBlock]
      erw [ruA_orte, lese_worldR, evalArgs_ru, hR]
      cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | ok σ' v =>
          try erw [hx]
          simp only [rufR]
          erw [execBlock_vorΛ, ergWert_ru he]
          exact (congrArg Ausgang.schrumpf (execBlock_ru rest σ' (Env.cons (ergWert he v) ρ))).trans
            (ausR_schrumpf _)
      | grund σ' r => exact (Fin.cast hr r).elim0
      | logik e => (try erw [hx]); rfl
      | hardware e => (try erw [hx]); rfl
  | _, _, Λ, _, .bindCallInd (n := n) p args he hp hr rest, σ, ρ => by
      simp only [ruB, execBlock]
      erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
        kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
      erw [lese_worldR, eval_ru, evalArgs_ru]
      cases h : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ with
      | mk g hg =>
          rw [valR_fnptr]
          dsimp only
          erw [umsig_ru hg, hR]
          cases hx : R g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
          | ok σ' v =>
              try erw [hx]
              simp only [rufR]
              erw [execBlock_vorΛ, ergWert_ru (ergSig hg he)]
              exact (congrArg Ausgang.schrumpf
                (execBlock_ru rest σ' (Env.cons (ergWert (ergSig hg he) v) ρ))).trans (ausR_schrumpf _)
          | grund σ' r => exact keinGrundSig hg hr r
          | logik e => (try erw [hx]); rfl
          | hardware e => (try erw [hx]); rfl
  | _, _, Λ, _, .bindCallElse g args he hp hr err rest, σ, ρ => by
      simp only [ruB, execBlock]
      erw [ruA_orte, lese_worldR, evalArgs_ru, hR]
      cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | ok σ' v =>
          try erw [hx]
          simp only [rufR]
          erw [execBlock_vorΛ, ergWert_ru he]
          exact (congrArg Ausgang.schrumpf (execBlock_ru rest σ' (Env.cons (ergWert he v) ρ))).trans
            (ausR_schrumpf _)
      | grund σ' r =>
          try erw [hx]
          simp only [rufR]
          erw [execEnd_umΛ]
          exact (congrArg (fun a => EndAusgang.zuAusgang (EndAusgang.schrumpf a))
            (execEnd_ru err σ' (Env.cons r ρ))).trans
            ((congrArg EndAusgang.zuAusgang (endR_schrumpf _)).trans (endR_zuAusgang _))
      | logik e => (try erw [hx]); rfl
      | hardware e => (try erw [hx]); rfl
  | _, _, Λ, _, .bindAxiom a args he hw hg hd hgd rest, σ, ρ => by
      simp only [ruB, execBlock]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ru]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => rfl
          | some v =>
              simp only [Option.map]
              rw [ergWert_ru he, ← ausR_schrumpf, ← execBlock_ru rest σ' (Env.cons _ ρ)]
              rfl
  | _, _, _, _, .regLies r hk rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [regLies_mitRuhe, einpassen_ru]
      cases einpassen (D.rtyp r) (O.regLies r σ) with
      | none => rfl
      | some v =>
          simp only [Option.map]
          erw [rzusage_mitRuhe]
          cases D.rzusage r v with
          | false => rfl
          | true =>
              simp only [if_true]
              rw [← ausR_schrumpf, ← execBlock_ru rest σ (Env.cons v ρ)]
              rfl
  | _, _, Λ, _, .regLiesElse r hk zusage sonst rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [regLies_mitRuhe, einpassen_ru]
      cases einpassen (D.rtyp r) (O.regLies r σ) with
      | none => rfl
      | some v =>
          simp only [Option.map]
          rw [ruE_orte, lese_worldR]
          have ez := eval_ru (σ.lese Λ zusage.orte) (σ.lese Λ zusage.orte) zusage (Env.cons v ρ)
          change eval _ (ruE zusage) _ (Env.cons (valR _ v) (envR ρ)) = _ at ez
          rw [ez]
          cases h : (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (Env.cons v ρ) : Bool) with
          | false =>
              simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
              rw [← endR_zuAusgang, execEnd_ru sonst _ ρ]
          | true =>
              simp only [wahr?, valR_bool, h, if_true]
              rw [← ausR_schrumpf, ← execBlock_ru rest _ (Env.cons v ρ)]
              rfl
  | _, _, Λ, _, .awaits g payload hp hL rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [sichtbar_mitRuhe]
      cases O.sichtbar g σ with
      | false => rfl
      | true =>
          simp only [if_true]
          rw [show ([Sum.inr g] : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) = [Sum.inr g] from rfl,
            lese_worldR, ← ausR_schrumpf, ← execBlock_ru rest _ (Env.cons _ ρ)]
          rfl
  | _, _, Λ, _, .exchange g neu hw hL rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [show (Sum.inr g :: (ruE neu).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
        Sum.inr g :: neu.orte from congrArg (Sum.inr g :: ·) (ruE_orte neu), lese_worldR]
      have ez := eval_ru (σ.lese Λ (Sum.inr g :: neu.orte)) (σ.lese Λ (Sum.inr g :: neu.orte)) neu
        (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ)
      change eval _ (ruE neu) _ (Env.cons (valR _ _) (envR ρ)) = _ at ez
      rw [show ((worldR (σ.lese Λ (Sum.inr g :: neu.orte))).globs g) =
        valR _ ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) from rfl, ez, schreibGlob_worldR,
        ← ausR_schrumpf, ← execBlock_ru rest _ (Env.cons _ ρ)]
      rfl
  | _, _, Λ, _, .narrow e lo' hi' sonst rest, σ, ρ => by
      simp only [ruB, execBlock]
      simp only [ruE_orte, lese_worldR, eval_ru, valR_int]
      by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
          (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
      · erw [dif_pos hc, dif_pos hc]
        exact (congrArg Ausgang.schrumpf (execBlock_ru rest _
          (Env.cons (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))).trans
          (ausR_schrumpf _)
      · erw [dif_neg hc, dif_neg hc, ← endR_zuAusgang, execEnd_ru sonst _ ρ]
  | _, _, Λ, _, .pruefung c sonst rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [ruE_orte, lese_worldR, eval_ru]
      cases h : (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ : Bool) with
      | false =>
          simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
          rw [← endR_zuAusgang, execEnd_ru sonst _ ρ]
      | true =>
          simp only [wahr?, valR_bool, h, if_true]
          exact execBlock_ru rest _ ρ
  | _, _, Λ, _, .gleit op a b lo hi rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [orte2, lese_worldR, eval_ru, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases gleitPasst lo hi (gleitRechne op
          (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
          (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) with
      | none => rfl
      | some v =>
          rw [← ausR_schrumpf, ← execBlock_ru rest _ (Env.cons v ρ)]
          rfl
  | _, _, _, _, .gleitLit q lo hi rest, σ, ρ => by
      simp only [ruB, execBlock]
      cases gleitPasst lo hi (bruch q) with
      | none => rfl
      | some v =>
          rw [← ausR_schrumpf, ← execBlock_ru rest _ (Env.cons v ρ)]
          rfl
  | _, _, Λ, _, .gleitVon e lo hi rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [ruE_orte, lese_worldR, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) with
      | none => rfl
      | some v =>
          rw [← ausR_schrumpf, ← execBlock_ru rest _ (Env.cons v ρ)]
          rfl
  | _, _, Λ, _, .gleitNarrow e lo hi sonst rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [ruE_orte, lese_worldR, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x with
      | none => rw [← endR_zuAusgang, execEnd_ru sonst _ ρ]
      | some v =>
          rw [← ausR_schrumpf, ← execBlock_ru rest _ (Env.cons v ρ)]
          rfl

theorem execEnd_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
    execEnd O.mitRuhe passes R' (ruEnd e) (worldR σ) (envR ρ) = endR (execEnd O passes R e σ ρ)
  | _, _, Λ, .ret e hΛ, σ, ρ => by
      simp only [ruEnd, execEnd]
      erw [ruErg_orte, lese_worldR, evalErg_ru]
      rfl
  | _, _, _, .retGrund .., σ, ρ => rfl
  | _, _, _, .leave _, σ, ρ => rfl
  | _, _, _, .next _, σ, ρ => rfl
  | _, _, _, .cons s rest, σ, ρ => by
      simp only [ruEnd, execEnd]
      rw [execStmt_ru s σ ρ]
      cases execStmt O passes R s σ ρ with
      | ok σ' ρ' => exact execEnd_ru rest σ' ρ'
      | _ => rfl
  | _, _, Λ, .bind e rest, σ, ρ => by
      simp only [ruEnd, execEnd]
      rw [ruE_orte, lese_worldR, eval_ru, ← endR_schrumpf, ← execEnd_ru rest _ _]
      rfl

theorem execArms_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs))
    (σ : World D) (ρ : Env D Γ),
    execArms O.mitRuhe passes R' (ruArms arms) (valR (.sum cs) v) (worldR σ) (envR ρ) =
      ausR (execArms O passes R arms v σ ρ)
  | _, _, _, _, _, .cons (c := none) b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ => execBlock_ru b σ ρ
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ => by
      exact (congrArg Ausgang.schrumpf (execBlock_ru b σ (Env.cons nutz ρ))).trans (ausR_schrumpf _)
  | _, _, _, _, _, .cons (c := none) b rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArms_ru rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArms_ru rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ

theorem execGrund_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    execGrund O.mitRuhe passes R' (ruGArms arms) r (worldR σ) (envR ρ) =
      ausR (execGrund O passes R arms r σ ρ)
  | _, _, _, _, _, .cons b _, ⟨0, _⟩, σ, ρ => execBlock_ru b σ ρ
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, h⟩, σ, ρ =>
      execGrund_ru rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ σ ρ

end

end Haupt



/-! ## 8. Every function behaves as in `P` -/

/-- **EVERY FUNCTION OF `P` BEHAVES IN `P.mitRuhe` AS IN `P`**: the body of
    `some f` in `P.mitRuhe`, run under the oracle `O.mitRuhe` from the
    translated world and parameters, ends in the translated outcome of the
    body of `f` in `P` under `O` -- for every budget and every pair of call
    handlers that answer translated calls with translated answers
    (`RufRu`). The generic form of `gPB_wie_gP_einzahlen`/`gPB_wie_gP_lies`
    (Schlusssatz104.lean). -/
theorem rumpf_mitRuhe_verhalten (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) →
      RufAusgang f)
    (hR : RufRu R R') (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) :
    execEnd O.mitRuhe passes R' (P.mitRuhe.rumpf (some f)) (worldR σ) (envR ρ) =
      endR (execEnd O passes R (P.rumpf f) σ ρ) :=
  (execEnd_umΛ O.mitRuhe passes R' _ _ _ _).trans (execEnd_ru O passes R R' hR (P.rumpf f) σ ρ)

/-- The root's body returns at once, touching nothing. -/
theorem rumpf_ruhe_verhalten (P : Programm D) (O : Orakel D) (passes : Nat)
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) →
      RufAusgang f) (σ : World D.mitRuhe) (ρ : Env D.mitRuhe (D.mitRuhe.params none)) :
    execEnd O.mitRuhe passes R' (P.mitRuhe.rumpf none) σ ρ = .zurueck σ () := rfl


/-! ## 9. Every call behaves as in `P` (`rufAt`) -/

theorem eval_umΓ_ergEnv {Γ : Ctx} {Λ' : List (Res D.mitRuhe)} :
    ∀ (e : Option Ty) (h : (ErgCtx Γ e).map tyR = ErgCtx (Γ.map tyR) (e.map tyR))
      (x : Expr D.mitRuhe ((ErgCtx Γ e).map tyR) Λ' .bool) (σ₀ σ : World D.mitRuhe)
      (v : ErgVal D e) (ρ : Env D Γ),
      eval σ₀ (Expr.umΓ h x) σ (ergEnv (e.map tyR) (ergR e v) (envR ρ)) =
        eval σ₀ x σ (envR (ergEnv e v ρ))
  | none, _, _, _, _, _, _ => rfl
  | some _, _, _, _, _, _, _ => rfl

theorem ens_mitRuhe_eval (P : Programm D) (f : D.Fn) (σ₀ σ : World D) (v : ErgVal D (D.erg f))
    (ρ : Env D (D.params f)) :
    eval (worldR σ₀) (P.mitRuhe.ensures (some f)) (worldR σ)
        (ergEnv ((D.erg f).map tyR) (ergR (D.erg f) v) (envR ρ)) =
      eval σ₀ (P.ensures f) σ (ergEnv (D.erg f) v ρ) :=
  (eval_umΓ_ergEnv (D.erg f) _ _ _ _ v ρ).trans
    ((eval_umΛ' _ _ _ _ _).trans (eval_ru σ₀ σ (P.ensures f) (ergEnv (D.erg f) v ρ)))

theorem inv_mitRuhe_eval (P : Programm D) (i : D.Inv) (σ : World D) :
    eval (worldR σ) (P.mitRuhe.invariante i) (worldR σ) Env.nil =
      eval σ (P.invariante i) σ Env.nil :=
  (eval_umΛ' _ _ _ _ _).trans (eval_ru σ σ (P.invariante i) Env.nil)

theorem invFold_mitRuhe (P : Programm D) : ∀ (l : List D.Inv) (σ : World D),
    l.foldl (fun σ' i => σ'.lese (invSicht D.mitRuhe i) (P.mitRuhe.invariante i).orte) (worldR σ) =
      worldR (l.foldl (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ)
  | [], _ => rfl
  | i :: l, σ => by
      simp only [List.foldl_cons]
      rw [invariante_mitRuhe_orte, ← invSicht_map, lese_worldR]
      exact invFold_mitRuhe P l _

theorem lese_anfang_mitRuhe (P : Programm D) (f : D.Fn) (σ : World D) :
    (worldR σ).lese (Signatur.anfang D.mitRuhe (D.mitRuhe.signatur (some f)))
        (P.mitRuhe.requires (some f)).orte =
      worldR (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) := by
  rw [requires_mitRuhe_orte]
  erw [← anfang_map (D.signatur f)]
  rw [lese_worldR]

theorem lese_ende_mitRuhe (P : Programm D) (f : D.Fn) (σ : World D) :
    (worldR σ).lese (vertragVon D.mitRuhe (some f)).ende (P.mitRuhe.ensures (some f)).orte =
      worldR (σ.lese (vertragVon D f).ende (P.ensures f).orte) := by
  rw [ensures_mitRuhe_orte]
  erw [← ende_map (vertragVon D f)]
  rw [lese_worldR]

/-- **EVERY CALL OF `P.mitRuhe` AT `some f` BEHAVES AS THE CALL OF `P` AT `f`**
    -- `requires`, body, `ensures` and owed invariants, at every depth and
    every budget: the depth-`n` call semantics of the two programs answer
    translated calls with translated answers. -/
theorem rufAt_mitRuhe (P : Programm D) (O : Orakel D) (passes : Nat) :
    ∀ n, RufRu (rufAt P O passes n) (rufAt P.mitRuhe O.mitRuhe passes n)
  | 0 => fun _ _ _ => rfl
  | n + 1 => by
      intro g σ ρ
      have ih := rufAt_mitRuhe P O passes n
      simp only [rufAt]
      rw [lese_anfang_mitRuhe]
      erw [(eval_umΛ' _ _ _ _ _).trans (eval_ru _ _ (P.requires g) ρ)]
      cases hq : (eval (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) (P.requires g)
          (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ : Bool)
      · simp only [wahr?, valR_bool, hq, if_true]
        rfl
      · simp only [wahr?, valR_bool, hq, Bool.true_eq_false, if_false]
        erw [rumpf_mitRuhe_verhalten P O passes _ _ ih g _ ρ]
        cases execEnd O passes (rufAt P O passes n) (P.rumpf g)
            (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ with
        | zurueck σ' v =>
            simp only [endR]
            erw [lese_ende_mitRuhe]
            have he := ens_mitRuhe_eval P g (σ.lese (Signatur.anfang D (D.signatur g))
              (P.requires g).orte) (σ'.lese (vertragVon D g).ende (P.ensures g).orte) v ρ
            erw [he]
            cases hs : (eval (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte)
                (P.ensures g) (σ'.lese (vertragVon D g).ende (P.ensures g).orte)
                (ergEnv (D.erg g) v ρ) : Bool)
            · simp only [wahr?, hs, if_true]
              rfl
            · simp only [wahr?, hs, Bool.true_eq_false, if_false]
              erw [invFold_mitRuhe P]
              have hf : (fun i => schuldet (D := D.mitRuhe) (some g) i &&
                  !wahr? (eval (worldR ((D.invs.filter (schuldet g)).foldl
                    (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                    (σ'.lese (vertragVon D g).ende (P.ensures g).orte)))
                    (P.mitRuhe.invariante i) (worldR ((D.invs.filter (schuldet g)).foldl
                    (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                    (σ'.lese (vertragVon D g).ende (P.ensures g).orte))) Env.nil)) =
                  (fun i => schuldet g i && !wahr? (eval ((D.invs.filter (schuldet g)).foldl
                    (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                    (σ'.lese (vertragVon D g).ende (P.ensures g).orte))
                    (P.invariante i) ((D.invs.filter (schuldet g)).foldl
                    (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                    (σ'.lese (vertragVon D g).ende (P.ensures g).orte)) Env.nil)) := by
                funext i
                rw [inv_mitRuhe_eval]
                rfl
              erw [hf]
              cases hx : D.invs.find? (fun i => schuldet g i && !wahr? (eval
                  ((D.invs.filter (schuldet g)).foldl
                    (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                    (σ'.lese (vertragVon D g).ende (P.ensures g).orte))
                  (P.invariante i) ((D.invs.filter (schuldet g)).foldl
                    (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                    (σ'.lese (vertragVon D g).ende (P.ensures g).orte)) Env.nil)) with
              | none => (try erw [hx]); rfl
              | some i => (try erw [hx]); rfl
        | grund σ' r => rfl
        | leave h _ _ => exact absurd h (by decide)
        | next h _ _ => exact absurd h (by decide)
        | logik e => rfl
        | hardware e => rfl

#print axioms Gabbro.Grammatik.eval_ru
#print axioms Gabbro.Grammatik.evalArgs_ru
#print axioms Gabbro.Grammatik.lese_worldR
#print axioms Gabbro.Grammatik.req_mitRuhe_iff
#print axioms Gabbro.Grammatik.execStmt_ru
#print axioms Gabbro.Grammatik.execEnd_ru
#print axioms Gabbro.Grammatik.rumpf_mitRuhe_verhalten
#print axioms Gabbro.Grammatik.rufAt_mitRuhe

end Gabbro.Grammatik
