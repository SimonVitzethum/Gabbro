import Grammatik.Zielsatz.Einbettung.Schritt

/-!
  File:      Grammatik/Zielsatz/Einbettung/Handler.lean
  Subject:   The handlers of `D` that a run of `D'` induces (stage E2c, part 1).

  A body of `D` meets callees, axioms, lock moves and atomic reads through handlers that are
  functions of the `D`-world. Its image in `D'` meets the handlers of `D'`, functions of the
  `D'`-world. Given a map `Φ` from `D`-worlds to `D'`-worlds (on the run: the keys, `Inv`), every
  handler of `D'` gives one of `D`: ask the `D'`-handler at `Φ σ` and bring the answer back --
  memory restricted to the image (`speicherZ`), the caller's trace with the neutral piece `pad`
  on top (`antwortWelt`), values back by `valZ`, a `logik` outcome to the same kind.

  Also here: the reads of a translated expression are the images of its reads (`orte_exE`), and
  arguments and results evaluate as their images (`evalArgs_exA`, `evalErg_exErg`).
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

theorem Expr.orte_umTy {Γ : Ctx} {Λ : List (Res D)} {τ τ' : Ty} (h : τ = τ') (e : Expr D Γ Λ τ) :
    (Expr.umTy h e).orte = e.orte := by subst h; rfl

theorem Expr.orte_umΓ {Γ Γ' : Ctx} {Λ : List (Res D)} {τ : Ty} (h : Γ = Γ') (e : Expr D Γ Λ τ) :
    (Expr.umΓ h e).orte = e.orte := by subst h; rfl

theorem Args.orte_umτs {Γ : Ctx} {Λ : List (Res D)} {τs τs' : List Ty} (h : τs = τs')
    (a : Args D Γ Λ τs) : (Args.umτs h a).orte = a.orte := by subst h; rfl

namespace Einbettung

variable (E : Einbettung D D')

/-! ## Reads of a translated expression -/

mutual

theorem orte_exE : ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ),
    (exE E e).orte = e.orte.map E.ortE
  | _, _, _, .lit _ => rfl
  | _, _, _, .tru => rfl
  | _, _, _, .fls => rfl
  | _, _, _, .var _ => rfl
  | _, _, _, .glob _ _ => by simp only [exE, Expr.orte_umTy]; rfl
  | _, _, _, .slot t f i _ => by
      simp only [exE, Expr.orte_umTy, Expr.orte, orte_exE i, List.map_cons]; rfl
  | _, _, _, .thru p t _ f i _ => by
      simp only [exE, Expr.orte_umTy, Expr.orte, orte_exE i, orte_exE p, List.map_cons,
        List.map_append]; rfl
  | _, _, _, .ptrOf _ _ _ _ => rfl
  | _, _, _, .fnref _ _ _ => rfl
  | _, _, _, .refEq a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .slotRef r t _ _ f _ => by
      simp only [exE, Expr.orte_umTy, Expr.orte, orte_exE r, List.map_cons]; rfl
  | _, _, _, .oldG _ _ => by simp only [exE, Expr.orte_umTy]; rfl
  | _, _, _, .oldS t f i _ => by
      simp only [exE, Expr.orte_umTy, Expr.orte, orte_exE i, List.map_cons]; rfl
  | _, _, _, .widen _ _ a => by simp only [exE, Expr.orte, orte_exE a]
  | _, _, _, .add a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .sub a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .neg a => by simp only [exE, Expr.orte, orte_exE a]
  | _, _, _, .mul a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .div _ _ a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .rem _ _ a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .sdiv _ a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .srem _ a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .getBytes t f hf n i _ _ _ => by
      simp only [exE, Expr.orte, orte_exE i, List.map_cons]; rfl
  | _, _, _, .band _ _ a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .bor _ _ _ _ _ a b => by
      simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .bxor _ _ _ _ _ a b => by
      simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .shl _ _ _ _ _ a b => by
      simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .shr _ _ _ _ _ a b => by
      simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .lt a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .le a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .eq a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .fllt a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .flle a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .and a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .or a b => by simp only [exE, Expr.orte, orte_exE a, orte_exE b, List.map_append]
  | _, _, _, .not a => by simp only [exE, Expr.orte, orte_exE a]
  | _, _, _, .none _ => rfl
  | _, _, _, .some a => by simp only [exE, Expr.orte, orte_exE a]
  | _, _, _, .istSome a => by simp only [exE, Expr.orte, orte_exE a]
  | _, _, _, .case _ _ nutz => by simp only [exE, Expr.orte, orteN_exN nutz]
  | _, _, _, .why _ _ => rfl
  | _, _, _, .forallSlots t body _ => by
      simp only [exE, Expr.orte, Expr.orte_umΓ, orte_exE body, List.map_cons]; rfl
  | _, _, _, .existsSlots t body _ => by
      simp only [exE, Expr.orte, Expr.orte_umΓ, orte_exE body, List.map_cons]; rfl
  | _, _, _, .reaches t f hf a b _ => by
      simp only [exE, Expr.orte, Expr.orte_umTy, orte_exE a, orte_exE b, List.map_cons,
        List.map_append]; rfl

theorem orteN_exN : ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)} (n : NutzlastExpr D Γ Λ c),
    (exN E n).orte = n.orte.map E.ortE
  | _, _, _, .empty => rfl
  | _, _, _, .num e => orte_exE e

end

theorem orte_exA : ∀ {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} (a : Args D Γ Λ τs),
    (exA E a).orte = a.orte.map E.ortE
  | _, _, _, .nil => rfl
  | _, _, _, .cons e rest => by
      simp only [exA, Args.orte, E.orte_exE e, orte_exA rest, List.map_append]

theorem orte_exErg : ∀ {Γ : Ctx} {Λ : List (Res D)} {e : Option Ty} (x : ErgExpr D Γ Λ e),
    (exErg E x).orte = x.orte.map E.ortE
  | _, _, _, .empty => rfl
  | _, _, _, .val e => E.orte_exE e

/-! ## Arguments and results -/

section Werte

variable {σ₀ σ : World D} {σ₀' σ' : World D'}

theorem evalArgs_exA (h₀ : E.Treu σ₀.speicher σ₀') (h : E.Treu σ.speicher σ') :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} (a : Args D Γ Λ τs) (ρ : Env D Γ),
      evalArgs σ₀' (exA E a) σ' (E.envE ρ) = E.envE (evalArgs σ₀ a σ ρ)
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons e rest, ρ => by
      simp only [exA, evalArgs, E.eval_exE h₀ h e ρ, evalArgs_exA h₀ h rest ρ]; rfl

theorem evalErg_exErg (h₀ : E.Treu σ₀.speicher σ₀') (h : E.Treu σ.speicher σ') :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {e : Option Ty} (x : ErgExpr D Γ Λ e) (ρ : Env D Γ),
      evalErg σ₀' (exErg E x) σ' (E.envE ρ) = E.ergE e (evalErg σ₀ x σ ρ)
  | _, _, _, .empty, _ => rfl
  | _, _, _, .val e, ρ => E.eval_exE h₀ h e ρ

end Werte

/-! ## Answers back in `D` -/

variable (hZ : ZeigerfreiD D)

/-- A result value of a pointer-free result type, back in `D`. -/
def ergZ : (e : Option Ty) → (∀ τ, e = some τ → τ.zeigerfrei = true) →
    ErgVal D' (e.map E.tyE) → ErgVal D e
  | none, _, v => v
  | some τ, h, v => E.valZ τ (h τ rfl) v

theorem ergE_ergZ : ∀ (e : Option Ty) (h : ∀ τ, e = some τ → τ.zeigerfrei = true)
    (v : ErgVal D' (e.map E.tyE)), E.ergE e (E.ergZ e h v) = v
  | none, _, _ => rfl
  | some τ, h, v => E.valE_valZ τ (h τ rfl) v

/-- The memory of a `D'`-world restricted to `D` is its image memory. -/
theorem treu_speicherZ (W : World D') : E.Treu (E.speicherZ hZ W.speicher) W :=
  ⟨fun t k f => (E.valE_valZ _ _ _).symm, fun g => (E.valE_valZ _ _ _).symm⟩

/-- **The world a foreign answer leaves, in `D`**: its memory restricted, the caller's trace
    with the neutral piece on top. -/
def antwortWelt (pad : List (Ereignis D)) (σ : World D) (W : World D') : World D :=
  (E.speicherZ hZ W.speicher).welt (pad ++ σ.spur)

theorem treu_antwortWelt (pad : List (Ereignis D)) (σ : World D) (W : World D') :
    E.Treu (E.antwortWelt hZ pad σ W).speicher W := by
  rw [antwortWelt, speicher_welt_speicher]; exact E.treu_speicherZ hZ W

theorem antwortWelt_laenge {pad : List (Ereignis D)} (hp : PadOk pad) (σ : World D) (W : World D') :
    σ.spur.length < (E.antwortWelt hZ pad σ W).spur.length := by
  simp only [antwortWelt, Speicher.welt, List.length_append]
  have := hp.lang
  omega

theorem antwortWelt_offen {pad : List (Ereignis D)} (hp : PadOk pad) (σ : World D) (W : World D') :
    Gabbro.Grammatik.offen (E.antwortWelt hZ pad σ W).spur = Gabbro.Grammatik.offen σ.spur :=
  hp.offen σ.spur

/-- A `logik` outcome of `D'` as one of `D`: a blamed caller stays a blamed caller. -/
def logikZ : Logik D' → Logik D
  | .vorbedingung g' => match E.fnZ g' with
    | some g => .vorbedingung g
    | none => .schleife
  | _ => .schleife

theorem logikZ_vorbedingung (g : D.Fn) : E.logikZ (.vorbedingung (E.fn g)) = .vorbedingung g := by
  simp only [logikZ, E.fnZ_fn]

/-- **A `logik` outcome of `D` beside one of `D'`**: where `D'` blames a caller, `D` blames the
    caller it comes from. -/
def LogikRel (e : Logik D) (e' : Logik D') : Prop :=
  ∀ g', e' = .vorbedingung g' → ∃ g, g' = E.fn g ∧ e = .vorbedingung g

/-- A `D'`-outcome that blames only images comes back related. -/
theorem logikRel_logikZ {e' : Logik D'} (h : ∀ g', e' = .vorbedingung g' → ∃ g, g' = E.fn g) :
    E.LogikRel (E.logikZ e') e' := by
  intro g' he
  obtain ⟨g, rfl⟩ := h g' he
  exact ⟨g, rfl, by rw [he, E.logikZ_vorbedingung]⟩

/-- The arguments of a call of `g`, as the parameters of its image. -/
def paramsUm (hS : E.SigTreu) (g : D.Fn) (ρ : Env D (D.params g)) : Env D' (D'.params (E.fn g)) :=
  castE (paramsE hS g) (E.envE ρ)

/-- The arguments of an axiom, as the parameters of its image. -/
def aparamsUm (a : D.Ax) (ρ : Env D (D.aparams a)) : Env D' (D'.aparams (E.ax a)) :=
  castE (E.aparams a).symm (E.envE ρ)

/-- **A callee's answer back in `D`.** -/
def antwortR (hS : E.SigTreu) (pad : List (Ereignis D)) (g : D.Fn) (σ : World D) :
    RufAusgang (D := D') (E.fn g) → RufAusgang g
  | .ok W v => .ok (E.antwortWelt hZ pad σ W) (E.ergZ (D.erg g) (hZ.erg g) (castV (ergE_fn hS g).symm v))
  | .why W r => .why (E.antwortWelt hZ pad σ W) (Fin.cast (gruendeE hS g) r)
  | .logik e => .logik (E.logikZ e)
  | .hardware _ => .hardware .ieee

/-! ## The induced handlers -/

section Induziert

variable (hS : E.SigTreu) (pad : List (Ereignis D)) (Φ : World D → World D')

/-- **The induced call handler.** -/
def rufΦ (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f) :
    ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g :=
  fun g σ ρ => E.antwortR hZ hS pad g σ (R' (E.fn g) (Φ σ) (E.paramsUm hS g ρ))

/-- **The induced lock move**: the protected carriers from the `D'`-move. -/
def umweltΦ (S : SperrInv D) (U' : Umwelt D') : Umwelt D :=
  fun L σ => mischU S L σ (E.speicherZ hZ (U' (E.lock L) (Φ σ)).speicher)

/-- **The induced atomic environment**: the read shared atomics from the `D'`-environment. -/
noncomputable def aumweltΦ (T : D.Tab ⊕ D.Glob → Prop) (A' : AUmwelt D') : AUmwelt D :=
  fun X σ => mischT T X σ (E.speicherZ hZ (A' (X.map E.ortE) (Φ σ)).speicher)

/-- **The induced oracle.** -/
def orakelΦ (O' : Orakel D') : Orakel D where
  wirkt := fun a σ ρ =>
    let x := O'.wirkt (E.ax a) (Φ σ) (E.aparamsUm a ρ)
    (E.antwortWelt hZ pad σ x.1, x.2)
  regLies := fun r σ => O'.regLies (E.reg r) (Φ σ)
  regSchreib := fun _ _ => ()
  sichtbar := fun g σ => O'.sichtbar (E.glob g) (Φ σ)
  zeiger := fun _ => Option.none

end Induziert

end Einbettung

end Gabbro.Grammatik.Einbettung
