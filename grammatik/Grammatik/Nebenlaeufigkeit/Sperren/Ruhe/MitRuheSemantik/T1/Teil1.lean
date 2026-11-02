module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T1.Teil1a

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

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
  | .kapazitaet => .kapazitaet
  | .fremdAntwort a => .fremdAntwort a

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
      · subst hf; simp only [hk, ↓reduceIte, ↓reduceDIte]
      · simp only [hk, ↓reduceIte, hf, ↓reduceDIte]
    · simp only [hk, ↓reduceIte]
  · simp only [ht, ↓reduceDIte]

theorem storeGlob_worldR (σ : World D) (g : D.Glob) (v : Wert D (D.gtyp g)) :
    (worldR σ).storeGlob g (valR (D.gtyp g) v) = worldR (σ.storeGlob g v) := by
  refine welt_ext rfl ?_ rfl
  funext g'
  simp only [World.storeGlob, worldR]
  by_cases hg : g' = g
  · subst hg; simp only [↓reduceDIte]
  · simp only [hg, ↓reduceDIte]

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

end Gabbro.Grammatik
