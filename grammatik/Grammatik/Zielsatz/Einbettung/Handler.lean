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

variable (hZ : E.Rueck) {σ₀ σ : World D} {σ₀' σ' : World D'}

theorem evalArgs_exA (h₀ : E.Treu hZ σ₀.speicher σ₀') (h : E.Treu hZ σ.speicher σ') :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} (a : Args D Γ Λ τs) (ρ : Env D Γ)
      (ρ' : Env D' (Γ.map E.tyE)), E.EnvR hZ ρ ρ' →
      E.EnvR hZ (evalArgs σ₀ a σ ρ) (evalArgs σ₀' (exA E a) σ' ρ')
  | _, _, _, .nil, _, _, _ => trivial
  | _, _, _, .cons e rest, ρ, ρ', hρ =>
      ⟨⟨rfl, E.eval_exE hZ h₀ h e ρ ρ' hρ⟩, evalArgs_exA h₀ h rest ρ ρ' hρ⟩

/-- A result value beside one of `D'`. -/
def ErgRel : (e : Option Ty) → ErgVal D e → ErgVal D' (e.map E.tyE) → Prop
  | none, _, _ => True
  | some τ, v, v' => E.VRel hZ τ v v'

theorem evalErg_exErg (h₀ : E.Treu hZ σ₀.speicher σ₀') (h : E.Treu hZ σ.speicher σ') :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {e : Option Ty} (x : ErgExpr D Γ Λ e) (ρ : Env D Γ)
      (ρ' : Env D' (Γ.map E.tyE)), E.EnvR hZ ρ ρ' →
      E.ErgRel hZ e (evalErg σ₀ x σ ρ) (evalErg σ₀' (exErg E x) σ' ρ')
  | _, _, _, .empty, _, _, _ => trivial
  | _, _, _, .val e, ρ, ρ', hρ => E.eval_exE hZ h₀ h e ρ ρ' hρ

end Werte

/-! ## Answers back in `D` -/

variable (hZ : E.Rueck)

/-- A result value of `D'` back in `D`. -/
def ergZ : (e : Option Ty) → ErgVal D' (e.map E.tyE) → ErgVal D e
  | none, v => v
  | some τ, v => E.valZ hZ τ v

theorem ergRel_ergZ : ∀ (e : Option Ty) (v : ErgVal D' (e.map E.tyE)), E.ErgRel hZ e (E.ergZ hZ e v) v
  | none, _ => trivial
  | some τ, v => E.vrel_valZ hZ τ v

theorem ergRel_ergE : ∀ (e : Option Ty) (v : ErgVal D e), E.ErgRel hZ e v (E.ergE e v)
  | none, _ => trivial
  | some τ, v => E.vrel_valE hZ τ v

/-- The memory of a `D'`-world restricted to `D` is its image memory. -/
theorem treu_speicherZ (W : World D') : E.Treu hZ (E.speicherZ hZ W.speicher) W :=
  ⟨fun t k f => E.vrel_valZ hZ _ _, fun g => E.vrel_valZ hZ _ _⟩

/-- **The world a foreign answer leaves, in `D`**: its memory restricted, the caller's trace
    with the neutral piece on top. -/
def antwortWelt (pad : List (Ereignis D)) (σ : World D) (W : World D') : World D :=
  (E.speicherZ hZ W.speicher).welt (pad ++ σ.spur)

theorem treu_antwortWelt (pad : List (Ereignis D)) (σ : World D) (W : World D') :
    E.Treu hZ (E.antwortWelt hZ pad σ W).speicher W := by
  rw [antwortWelt, speicher_welt_speicher]; exact E.treu_speicherZ hZ W

theorem antwortWelt_laenge {pad : List (Ereignis D)} (hp : PadOk pad) (σ : World D) (W : World D') :
    σ.spur.length < (E.antwortWelt hZ pad σ W).spur.length := by
  simp only [antwortWelt, Speicher.welt, List.length_append]
  have := hp.lang
  omega

theorem antwortWelt_offen {pad : List (Ereignis D)} (hp : PadOk pad) (σ : World D) (W : World D') :
    Gabbro.Grammatik.offen (E.antwortWelt hZ pad σ W).spur = Gabbro.Grammatik.offen σ.spur :=
  hp.offen σ.spur

/-- A `logik` outcome of the callee, seen from `D`: a blamed caller stays a blamed caller (of the
    function `D` called). -/
def logikZ (g : D.Fn) : Logik D' → Logik D
  | .vorbedingung _ => .vorbedingung g
  | _ => .schleife

/-- **A `logik` outcome of `D` beside one of `D'`**: where `D'` blames a caller, `D` blames one. -/
def LogikRel (e : Logik D) (e' : Logik D') : Prop :=
  ∀ g', e' = .vorbedingung g' → ∃ g, e = .vorbedingung g

theorem logikRel_logikZ (g : D.Fn) (e' : Logik D') : LogikRel (logikZ g e') e' := by
  intro g' he; subst he; exact ⟨g, rfl⟩

/-- The arguments of a call of `g`, as the parameters of its image. -/
def paramsUm (hS : E.SigTreu) (g : D.Fn) (ρ : Env D (D.params g)) : Env D' (D'.params (E.fn g)) :=
  castE (paramsE hS g) (E.envE ρ)

/-- The arguments of an axiom, as the parameters of its image. -/
def aparamsUm (a : D.Ax) (ρ : Env D (D.aparams a)) : Env D' (D'.aparams (E.ax a)) :=
  castE (E.aparams a).symm (E.envE ρ)

/-- **`f'` may stand where `D` calls `g`**: the image of `g`, or a function outside the image
    that conforms to the image of a signature whose head is `g`. -/
def Konform (g : D.Fn) (f' : D'.Fn) : Prop :=
  f' = E.fn g ∨ ∃ n, E.fnZ f' = none ∧ hZ.rep n = some g ∧ D'.passt f' (E.num n) = true

section Konform

variable {E hZ}

theorem konform_sig (hS : E.SigTreu) {g : D.Fn} {f' : D'.Fn} (h : E.Konform hZ g f') :
    (D'.signatur f').params = (D.signatur g).params.map E.tyE ∧
      (D'.signatur f').erg = (D.signatur g).erg.map E.tyE ∧
      (D'.signatur f').gruende = (D.signatur g).gruende := by
  rcases h with rfl | ⟨n, _, hr, hp⟩
  · rw [hS.signatur]; exact ⟨rfl, rfl, rfl⟩
  · have h1 := D'.passt_sig hp
    have h2 := D.passt_sig (hZ.rep_passt n g hr)
    rw [hS.sigNr] at h1
    refine ⟨?_, ?_, ?_⟩
    · rw [h1.params, h2.params]; rfl
    · rw [h1.erg, h2.erg]; rfl
    · rw [h1.gruende, h2.gruende]; rfl

end Konform

/-- **A callee's answer back in `D`**, from a callee `f'` of `D'` whose result and reasons are
    those of `g`. -/
def antwortR (pad : List (Ereignis D)) (g : D.Fn) (σ : World D) {f' : D'.Fn}
    (he : D'.erg f' = (D.erg g).map E.tyE) (hr : D'.gruende f' = D.gruende g) :
    RufAusgang f' → RufAusgang g
  | .ok W v => .ok (E.antwortWelt hZ pad σ W) (E.ergZ hZ (D.erg g) (castV he v))
  | .why W r => .why (E.antwortWelt hZ pad σ W) (Fin.cast hr r)
  | .logik e => .logik (logikZ g e)
  | .hardware _ => .hardware .ieee

/-! ## The induced handlers -/

/-- The maps from `D`-worlds the keys give: the `D'`-world at a main key, at an atomic key, and
    the callee and arguments at a call key. -/
structure _root_.Gabbro.Grammatik.Einbettung.Phi (D D' : Deklaration) where
  haupt : World D → World D'
  atom : World D → World D'
  ruf : World D → Option (Σ f' : D'.Fn, Env D' (D'.params f'))

section Induziert

variable (hS : E.SigTreu) (pad : List (Ereignis D)) (Φ : Phi D D')

/-- **The induced call handler**: at a call key whose callee may stand for `g` and whose arguments
    stand beside `g`'s, the `D'`-callee's answer; elsewhere the image's. -/
noncomputable def rufΦ (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f) :
    ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g :=
  fun g σ ρ =>
    haveI := Classical.propDecidable
    match Φ.ruf σ with
    | some ⟨f', a'⟩ =>
        if h : E.EnvR hZ ρ a' ∧ E.Konform hZ g f' then
          E.antwortR hZ pad g σ (konform_sig hS h.2).2.1 (konform_sig hS h.2).2.2 (R' f' (Φ.haupt σ) a')
        else E.antwortR hZ pad g σ (ergE_fn hS g).symm (gruendeE hS g)
          (R' (E.fn g) (Φ.haupt σ) (E.paramsUm hS g ρ))
    | none => E.antwortR hZ pad g σ (ergE_fn hS g).symm (gruendeE hS g)
          (R' (E.fn g) (Φ.haupt σ) (E.paramsUm hS g ρ))

/-- **The induced lock move**: the protected carriers from the `D'`-move. -/
def umweltΦ (S : SperrInv D) (U' : Umwelt D') : Umwelt D :=
  fun L σ => mischU S L σ (E.speicherZ hZ (U' (E.lock L) (Φ.haupt σ)).speicher)

/-- **The induced atomic environment**: the read shared atomics from the `D'`-environment. -/
noncomputable def aumweltΦ (T : D.Tab ⊕ D.Glob → Prop) (A' : AUmwelt D') : AUmwelt D :=
  fun X σ => mischT T X σ (E.speicherZ hZ (A' (X.map E.ortE) (Φ.atom σ)).speicher)

/-- **The induced oracle.** -/
def orakelΦ (O' : Orakel D') : Orakel D where
  wirkt := fun a σ ρ =>
    let x := O'.wirkt (E.ax a) (Φ.haupt σ) (E.aparamsUm a ρ)
    (E.antwortWelt hZ pad σ x.1, x.2)
  regLies := fun r σ => O'.regLies (E.reg r) (Φ.haupt σ)
  regSchreib := fun _ _ => ()
  sichtbar := fun g σ => O'.sichtbar (E.glob g) (Φ.haupt σ)
  zeiger := fun _ => Option.none

end Induziert

end Einbettung

end Gabbro.Grammatik.Einbettung
