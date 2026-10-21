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
             (rufAt_mitRuhe; the generic form of gPB_wie_gP).

  NOT here (open): the same for execEndH, the lock-aware semantics the user
  obligation KoerperGutS is stated against (it quantifies over oracles,
  environment moves and handlers on the D.mitRuhe side, each of which is the
  translation of one on the D side); with it the user obligation on P
  transfers to P.mitRuhe.
-/
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheStatisch

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

/-! ## 2. Expressions -/

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
  | _, _, _, .ptrOf .., _ => rfl
  | _, _, _, .fnref .., _ => rfl
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
  | _, _, _, .case cs i nutz, ρ =>
      congrArg (fun z => (⟨i, z⟩ : Σ i : Fin cs.length, Nutzlast (cs.get i)))
        (evalNutz_ru σ₀ σ nutz ρ)
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

theorem evalNutz_ru (σ₀ σ : World D) : ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)}
    (n : NutzlastExpr D Γ Λ c) (ρ : Env D Γ),
    evalNutz (worldR σ₀) (ruN n) (worldR σ) (envR ρ) = evalNutz σ₀ n σ ρ
  | _, _, _, .empty, _ => rfl
  | _, _, _, .num e, ρ => eval_ru σ₀ σ e ρ

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
  | .why σ r => .why (worldR σ) r
  | .leave h σ ρ => .leave h (worldR σ) (envR ρ)
  | .next h σ ρ => .next h (worldR σ) (envR ρ)
  | .logik e => .logik (logikR e)
  | .hardware e => .hardware (hwR e)

/-- An end-block outcome, translated. -/
def endR {V : Vertrag D} {l : Bool} {Γ : Ctx} :
    EndAusgang V l Γ → EndAusgang (vertragR V) l (Γ.map tyR)
  | .zurueck σ v => .zurueck (worldR σ) (ergR V.erg v)
  | .why σ r => .why (worldR σ) r
  | .leave h σ ρ => .leave h (worldR σ) (envR ρ)
  | .next h σ ρ => .next h (worldR σ) (envR ρ)
  | .logik e => .logik (logikR e)
  | .hardware e => .hardware (hwR e)

/-- A call outcome, translated. -/
def rufR {f : D.Fn} : RufAusgang f → RufAusgang (D := D.mitRuhe) (some f)
  | .ok σ v => .ok (worldR σ) (ergR (D.erg f) v)
  | .why σ r => .why (worldR σ) r
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
    (cast (congrArg (Val (Option D.Fn) (passtM D)) h').symm b : Val (Option D.Fn) (passtM D) (tyR τ)) =
      valR τ (cast (congrArg (Val D.Fn D.passt) h).symm b) := by
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

/-- **An oracle of `D.mitRuhe` answering like `O`** on translated worlds and arguments. Until
    2026-09-15 the only such oracle the transfer used was `O.mitRuhe` itself, and every oracle
    of `D.mitRuhe` was one (`zurueck_mitRuhe`). Since the loaded image joined the oracle (G1
    repair, `Orakel.zeiger`), an oracle of `D.mitRuhe` may place the runtime's root at an
    address, which no oracle of `D` can: `O.mitRuhe` is then not `O'`, but it still ANSWERS
    like `O'` on every translated type -- the root has signature number `0`, which no
    translated `fnptr` type names (`einpassen_ru`). -/
structure OrakelRu (O : Orakel D) (O' : Orakel D.mitRuhe) : Prop where
  wirkt : ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)),
    O'.wirkt a (worldR σ) (envR ρ) = (worldR (O.wirkt a σ ρ).1, (O.wirkt a σ ρ).2)
  regLies : ∀ (r : D.Reg) (σ : World D), O'.regLies r (worldR σ) = O.regLies r σ
  sichtbar : ∀ (g : D.Glob) (σ : World D), O'.sichtbar g (worldR σ) = O.sichtbar g σ
  zeiger : ∀ k, (O'.zeiger k).bind id = O.zeiger k

/-- A raw answer decodes in `D.mitRuhe` as in `D`, under images that agree off the root. -/
theorem einpassen_ru (z : Int → Option D.Fn) (z' : Int → Option D.mitRuhe.Fn)
    (hz : ∀ k, (z' k).bind id = z k) : ∀ (τ : Ty) (n : Int),
    einpassen (D := D.mitRuhe) z' (tyR τ) n = (einpassen (D := D) z τ n).map (valR τ)
  | .int lo hi, n => by
      show einpassen (D := D.mitRuhe) z' (.int lo hi) n =
        Option.map (valR (.int lo hi)) (einpassen (D := D) z (.int lo hi) n)
      simp only [einpassen]
      split <;> rfl
  | .bool, _ => rfl
  | .opt m, n => by
      show einpassen (D := D.mitRuhe) z' (.opt m) n =
        Option.map (valR (.opt m)) (einpassen (D := D) z (.opt m) n)
      simp only [einpassen]
      split
      · rfl
      · split <;> rfl
  | .sum cs, n => by
      show summePasst cs n = Option.map (valR (D := D) (.sum cs)) (summePasst cs n)
      cases summePasst cs n <;> rfl
  | .why m, n => by
      show einpassen (D := D.mitRuhe) z' (.why m) n =
        Option.map (valR (.why m)) (einpassen (D := D) z (.why m) n)
      simp only [einpassen]
      split <;> rfl
  | .never, _ => rfl
  | .fl lo hi, n => by
      show gleitWortPasst lo hi n = Option.map (valR (D := D) (.fl lo hi)) (gleitWortPasst lo hi n)
      cases gleitWortPasst lo hi n <;> rfl
  | .fnptr m, n => by
      show zeigerPasst (D := D.mitRuhe) z' (m + 1) n =
        Option.map (valR (D := D) (.fnptr m)) (zeigerPasst z m n)
      have h := hz n
      cases hz' : z' n with
      | none =>
          have hzn : z n = Option.none := by rw [← h, hz']; rfl
          simp only [zeigerPasst, hz', hzn]
          try rfl
      | some g =>
          cases g with
          | none =>
              have hzn : z n = Option.none := by rw [← h, hz']; rfl
              have hs : ¬ (D.mitRuhe).passt Option.none (m + 1) = true := by
                show ¬ decide (m + 1 = 0) = true
                simp
              simp only [zeigerPasst, hz', hzn, dif_neg hs]
              try rfl
          | some f =>
              have hzn : z n = some f := by rw [← h, hz']; rfl
              by_cases h2 : D.passt f m = true
              · have h2' : (D.mitRuhe).passt (some f) (m + 1) = true := h2
                simp only [zeigerPasst, hz', hzn, dif_pos h2, dif_pos h2']
                try rfl
              · have h2' : ¬ (D.mitRuhe).passt (some f) (m + 1) = true := h2
                simp only [zeigerPasst, hz', hzn, dif_neg h2, dif_neg h2']
                try rfl
  | .ptr _ _, _ => rfl

theorem einpassenErg_ru (z : Int → Option D.Fn) (z' : Int → Option D.mitRuhe.Fn)
    (hz : ∀ k, (z' k).bind id = z k) : ∀ (e : Option Ty) (n : Int),
    einpassenErg (D := D.mitRuhe) z' (e.map tyR) n = (einpassenErg (D := D) z e n).map (ergR e)
  | none, _ => rfl
  | some τ, n => einpassen_ru z z' hz τ n

/-- The translated image agrees with `O`'s off the root (it never names the root). -/
theorem zeiger_mitRuhe (O : Orakel D) (k : Int) : (O.mitRuhe.zeiger k).bind id = O.zeiger k := by
  show (Option.map some (O.zeiger k)).bind id = O.zeiger k
  cases O.zeiger k <;> rfl

theorem orakelRu_mitRuhe (O : Orakel D) : OrakelRu O O.mitRuhe :=
  ⟨wirkt_mitRuhe O, fun r σ => by
      show O.regLies r (worldZ (worldR σ)) = _
      rw [worldZ_worldR],
    fun g σ => by
      show O.sichtbar g (worldZ (worldR σ)) = _
      rw [worldZ_worldR],
    zeiger_mitRuhe O⟩

theorem axiomAntwort_ruG {O : Orakel D} {O' : Orakel D.mitRuhe} (hO : OrakelRu O O') (a : D.Ax)
    (σ : World D) (ρ : Env D (D.aparams a)) :
    axiomAntwort O' a (worldR σ) (envR ρ) =
      (worldR (axiomAntwort O a σ ρ).1, (axiomAntwort O a σ ρ).2.map (ergR (D.aerg a))) := by
  unfold axiomAntwort
  rw [hO.wirkt]
  exact congrArg _ (einpassenErg_ru O.zeiger O'.zeiger hO.zeiger (D.aerg a) _)

theorem axiomAntwort_ru (O : Orakel D) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    axiomAntwort O.mitRuhe a (worldR σ) (envR ρ) =
      (worldR (axiomAntwort O a σ ρ).1, (axiomAntwort O a σ ρ).2.map (ergR (D.aerg a))) :=
  axiomAntwort_ruG (orakelRu_mitRuhe O) a σ ρ


end Gabbro.Grammatik
