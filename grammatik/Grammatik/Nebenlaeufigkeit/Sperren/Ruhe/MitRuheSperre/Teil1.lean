/-
  File:      Grammatik/MitRuheSperre.lean
  Subject:   THE LOCK-INVARIANT SEMANTICS OF P.mitRuhe BEHAVES AS THE ONE OF
             P (the open piece of MitRuheSemantik.lean's header): every
             statement, block and end block of a translated body runs under
             `execStmtH`/`execBlockH`/`execEndH` (acquire moves, release
             checks) from the translated world and environment to the
             translated outcome -- up to the LABEL of a logic failure that a
             call handler of `D.mitRuhe` answers (`AusRelRu`, `EndRel`).

  Why "up to the label": the user obligation (`KoerperGutS`) quantifies
  over EVERY handler of `D.mitRuhe`, and such a handler may answer a logic
  failure that names the idle root (`nachbedingung none`, `abstieg none`),
  which is the translation of no label of `D`. The relation keeps what the
  obligation reads: a normal, reason, `leave`/`next` or hardware outcome is
  exactly the translated one; a logic outcome is a logic outcome, and it
  blames a caller (`vorbedingung`) only if the one of `D` does
  (`LogikTreu`).

  The inverse direction (`worldZ`, `envZ`, `ergZ`, `rufZ`,
  `Orakel.zurueck`): every world, environment, oracle and move of
  `D.mitRuhe` is the translation of one of `D` (`worldR_worldZ`,
  `envR_envZ`, `zurueck_mitRuhe`).
-/
module
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The inverse translations -/

theorem worldR_worldZ (σ : World D.mitRuhe) : worldR (worldZ σ) = σ := by
  cases σ with
  | mk slots globs spur =>
      simp only [worldZ, worldR, valR_valZ, List.map_map]
      congr 1
      conv => rhs; rw [← List.map_id spur]
      exact List.map_congr_left fun e _ => evR_evZ e

theorem offen_map_evZ : ∀ s : List (Ereignis D.mitRuhe), offen (s.map (evZ (D := D))) = offen s
  | [] => rfl
  | .nimmt L h :: s => congrArg (L :: ·) (offen_map_evZ s)
  | .gibt L :: s => congrArg (fun l => List.erase l L) (offen_map_evZ s)
  | .zugriff .. :: s => offen_map_evZ s
  | .gzugriff .. :: s => offen_map_evZ s
  | .fremd .. :: s => offen_map_evZ s

theorem haelt_worldZ (σ : World D.mitRuhe) : (worldZ σ).haelt = σ.haelt := offen_map_evZ σ.spur

theorem envR_envZ : ∀ {Γ : Ctx} (ρ : Env D.mitRuhe (Γ.map tyR)), envR (envZ ρ) = ρ
  | [], .nil => rfl
  | τ :: _, .cons v ρ => by
      show Env.cons (valR τ (valZ τ v)) (envR (envZ ρ)) = _
      rw [valR_valZ, envR_envZ ρ]

theorem speicherZ_worldR (σ : World D) : speicherZ (worldR σ).speicher = σ.speicher :=
  speicherZ_speicherR σ.speicher

/-- A result value of `D.mitRuhe`, translated back. -/
def ergZ : (e : Option Ty) → ErgVal D.mitRuhe (e.map tyR) → ErgVal D e
  | none, _ => ()
  | some τ, v => valZ τ v

theorem ergZ_ergR : ∀ (e : Option Ty) (v : ErgVal D e), ergZ e (ergR e v) = v
  | none, _ => rfl
  | some τ, v => valZ_valR τ v

theorem ergR_ergZ : ∀ (e : Option Ty) (v : ErgVal D.mitRuhe (e.map tyR)), ergR e (ergZ e v) = v
  | none, _ => rfl
  | some τ, v => valR_valZ τ v

/-- A hardware outcome of `D.mitRuhe`, translated back (every one is a
    translation: the hardware names axioms, assumptions and registers of `D`). -/
def hwZ : Hardware D.mitRuhe → Hardware D
  | .annahme a => .annahme a
  | .fortschritt a => .fortschritt a
  | .ieee => .ieee
  | .register r => .register r
  | .geraet r => .geraet r
  | .sichtbarkeit a => .sichtbarkeit a

theorem hwR_hwZ (e : Hardware D.mitRuhe) : hwR (hwZ e) = e := by cases e <;> rfl

/-- A logic label of `D.mitRuhe`, read back where the measure gate needs it: a descent at a translated function
    stays a descent; every other label becomes `schleife`. -/
def logikZ : Logik D.mitRuhe → Logik D
  | .abstieg (some h) => .abstieg h
  | _ => .schleife

/-- A call outcome of `D.mitRuhe` at `some g`, translated back; a logic
    failure keeps a descent's label (`logikZ`), every other becomes `schleife`. -/
def rufZ {g : D.Fn} : RufAusgang (D := D.mitRuhe) (some g) → RufAusgang g
  | .ok σ v => .ok (worldZ σ) (ergZ (D.erg g) v)
  | .why σ r => .why (worldZ σ) r
  | .logik e => .logik (logikZ e)
  | .hardware e => .hardware (hwZ e)

/-- **The handler of `D` a handler of `D.mitRuhe` answers with.** -/
def rufZuD (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) →
    RufAusgang f) : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g :=
  fun g σ ρ => rufZ (R' (some g) (worldR σ) (envR ρ))

/-- **The oracle of `D` an oracle of `D.mitRuhe` answers with.** -/
def Orakel.zurueck (O' : Orakel D.mitRuhe) : Orakel D where
  wirkt a σ ρ := (worldZ (O'.wirkt a (worldR σ) (envR ρ)).1, (O'.wirkt a (worldR σ) (envR ρ)).2)
  regLies r σ := O'.regLies r (worldR σ)
  regSchreib := O'.regSchreib
  sichtbar g σ := O'.sichtbar g (worldR σ)
  zeiger k := (O'.zeiger k).bind id

/-- **Every oracle of `D.mitRuhe` answers like one of `D`** (`OrakelRu`). Until 2026-09-15
    it WAS the translation of one (`(Orakel.zurueck O').mitRuhe = O'`); since the loaded image
    joined the oracle (G1 repair) an oracle of `D.mitRuhe` may place the root at an address,
    which the translation of an oracle of `D` never does -- but no translated type accepts
    the root, so every run agrees. -/
theorem orakelRu_zurueck (O' : Orakel D.mitRuhe) : OrakelRu (Orakel.zurueck O') O' :=
  ⟨fun a σ ρ => by
      show O'.wirkt a (worldR σ) (envR ρ) =
        (worldR (worldZ (O'.wirkt a (worldR σ) (envR ρ)).1), (O'.wirkt a (worldR σ) (envR ρ)).2)
      rw [worldR_worldZ],
    fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- The move of `D` a move of `D.mitRuhe` makes. -/
def umweltZ (U' : Umwelt D.mitRuhe) : Umwelt D := fun L σ => worldZ (U' L (worldR σ))

theorem umweltZ_ru (U' : Umwelt D.mitRuhe) (L : D.Lock) (σ : World D) :
    U' L (worldR σ) = worldR (umweltZ U' L σ) := (worldR_worldZ _).symm

/-! ## 2. Outcomes up to the label of a logic failure -/

/-- A logic label of `D.mitRuhe` blames a caller only if the one of `D` does, and is a descent at a translated
    function only if the one of `D` is that descent. -/
def LogikTreu (e' : Logik D.mitRuhe) (e : Logik D) : Prop :=
  (∀ g', e' = .vorbedingung g' → ∃ g, e = .vorbedingung g) ∧ ∀ h, e' = .abstieg (some h) → e = .abstieg h

theorem logikTreu_schleife {e' : Logik D.mitRuhe} (h1 : ∀ g', e' ≠ .vorbedingung g')
    (h2 : ∀ h, e' ≠ .abstieg (some h)) : LogikTreu e' .schleife :=
  ⟨fun g' he => absurd he (h1 g'), fun h he => absurd he (h2 h)⟩

section Rel

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

/-- The translated outcome, or two logic failures (`LogikTreu`). -/
def AusRelRu (a' : Ausgang (vertragR V) l (Γ.map tyR)) (a : Ausgang V l Γ) : Prop :=
  a' = ausR a ∨ ∃ e' e, a' = .logik e' ∧ a = .logik e ∧ LogikTreu e' e

/-- The translated end outcome, or two logic failures (`LogikTreu`). -/
def EndRel (a' : EndAusgang (vertragR V) l (Γ.map tyR)) (a : EndAusgang V l Γ) : Prop :=
  a' = endR a ∨ ∃ e' e, a' = .logik e' ∧ a = .logik e ∧ LogikTreu e' e

theorem AusRelRu.schrumpf {τ : Ty} {a' : Ausgang (vertragR V) l ((τ :: Γ).map tyR)}
    {a : Ausgang V l (τ :: Γ)} (h : AusRelRu a' a) : AusRelRu a'.schrumpf a.schrumpf := by
  rcases h with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]; exact Or.inl (ausR_schrumpf a)
  · rw [h1, h2]; exact Or.inr ⟨e', e, rfl, rfl, ht⟩

theorem EndRel.schrumpf {τ : Ty} {a' : EndAusgang (vertragR V) l ((τ :: Γ).map tyR)}
    {a : EndAusgang V l (τ :: Γ)} (h : EndRel a' a) : EndRel a'.schrumpf a.schrumpf := by
  rcases h with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]; exact Or.inl (endR_schrumpf a)
  · rw [h1, h2]; exact Or.inr ⟨e', e, rfl, rfl, ht⟩

theorem EndRel.zuAusgang {a' : EndAusgang (vertragR V) l (Γ.map tyR)} {a : EndAusgang V l Γ}
    (h : EndRel a' a) : AusRelRu a'.zuAusgang a.zuAusgang := by
  rcases h with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]; exact Or.inl (endR_zuAusgang a)
  · rw [h1, h2]; exact Or.inr ⟨e', e, rfl, rfl, ht⟩

theorem sinv_worldR (S : SperrInv D) (L : D.Lock) (σ : World D) :
    S.mitRuhe.inv L (worldR σ).speicher = S.inv L σ.speicher := by
  show S.inv L (speicherZ (worldR σ).speicher) = _
  rw [speicherZ_worldR]

theorem freiH_ausR (S : SperrInv D) (L : D.Lock) (a : Ausgang V l Γ) :
    freiH S.mitRuhe L (ausR a) = ausR (freiH S L a) := by
  cases a with
  | ok σ ρ =>
      show (if S.mitRuhe.inv L (worldR σ).speicher = true then _ else _) = ausR (if _ then _ else _)
      rw [sinv_worldR]
      cases S.inv L σ.speicher <;> rfl
  | leave h σ ρ =>
      show (if S.mitRuhe.inv L (worldR σ).speicher = true then _ else _) = ausR (if _ then _ else _)
      rw [sinv_worldR]
      cases S.inv L σ.speicher <;> rfl
  | next h σ ρ =>
      show (if S.mitRuhe.inv L (worldR σ).speicher = true then _ else _) = ausR (if _ then _ else _)
      rw [sinv_worldR]
      cases S.inv L σ.speicher <;> rfl
  | zurueck => rfl
  | why => rfl
  | logik => rfl
  | hardware => rfl

theorem AusRelRu.frei (S : SperrInv D) (L : D.Lock) {a' : Ausgang (vertragR V) l (Γ.map tyR)}
    {a : Ausgang V l Γ} (h : AusRelRu a' a) : AusRelRu (freiH S.mitRuhe L a') (freiH S L a) := by
  rcases h with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]; exact Or.inl (freiH_ausR S L a)
  · rw [h1, h2]; exact Or.inr ⟨e', e, rfl, rfl, ht⟩

end Rel

/-- **Two handlers answer alike**: at every translated call the translated
    answer, or two logic failures (`LogikTreu`). -/
def RufRel (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) →
      RufAusgang f) : Prop :=
  ∀ g σ ρ, R' (some g) (worldR σ) (envR ρ) = rufR (R g σ ρ) ∨
    ∃ e' e, R' (some g) (worldR σ) (envR ρ) = .logik e' ∧ R g σ ρ = .logik e ∧ LogikTreu e' e

/-! ## 3. Loops, up to the label -/

section Schleifen

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem traverseLauf_rel {τ : Ty}
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (schritt' : World D.mitRuhe → Env D.mitRuhe (tyR τ :: Γ.map tyR) →
      Ausgang (vertragR V) true (tyR τ :: Γ.map tyR))
    (inv : World D → Env D Γ → World D × Bool)
    (inv' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → World D.mitRuhe × Bool)
    (hs : ∀ σ ρ, AusRelRu (Γ := τ :: Γ) (schritt' (worldR σ) (envR ρ)) (schritt σ ρ))
    (hi : ∀ σ ρ, inv' (worldR σ) (envR ρ) = (worldR (inv σ ρ).1, (inv σ ρ).2)) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ),
      AusRelRu (traverseLauf (l := l) schritt' inv' (ks.map (valR τ)) (worldR σ) (envR ρ))
        (traverseLauf (l := l) schritt inv ks σ ρ)
  | [], σ, ρ => by
      refine Or.inl ?_
      simp only [List.map_nil, traverseLauf, hi]
      by_cases hc : (inv σ ρ).2 = true <;> simp only [hc, if_true, if_false] <;> rfl
  | k :: ks, σ, ρ => by
      simp only [List.map_cons, traverseLauf, hi]
      by_cases hc : (inv σ ρ).2 = false
      · simp only [hc, if_true]; exact Or.inl rfl
      · simp only [hc, if_false]
        have e := hs (inv σ ρ).1 (Env.cons k ρ)
        change AusRelRu (Γ := τ :: Γ) (schritt' (worldR (inv σ ρ).1) (Env.cons (valR τ k) (envR ρ)))
          _ at e
        rcases e with e | ⟨e', e0, h1, h2, ht⟩
        · rw [e]
          cases schritt (inv σ ρ).1 (Env.cons k ρ) with
          | ok σ' ρ' =>
              simp only [ausR, envR_tail]
              exact traverseLauf_rel schritt schritt' inv inv' hs hi ks σ' ρ'.tail
          | next h σ' ρ' =>
              simp only [ausR, envR_tail]
              exact traverseLauf_rel schritt schritt' inv inv' hs hi ks σ' ρ'.tail
          | leave h σ' ρ' =>
              refine Or.inl ?_
              simp only [ausR, envR_tail, hi]
              by_cases hc' : (inv σ' ρ'.tail).2 = true <;> simp only [hc', if_true, if_false] <;> rfl
          | zurueck => exact Or.inl rfl
          | why => exact Or.inl rfl
          | logik => exact Or.inl rfl
          | hardware => exact Or.inl rfl
        · rw [h1, h2]
          exact Or.inr ⟨e', e0, rfl, rfl, ht⟩

theorem retryLauf_rel
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (schritt' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → Ausgang (vertragR V) true (Γ.map tyR))
    (bis : World D → Env D Γ → World D × Bool)
    (bis' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → World D.mitRuhe × Bool)
    (ueber : World D → Env D Γ → Ausgang V l Γ)
    (ueber' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → Ausgang (vertragR V) l (Γ.map tyR))
    (hs : ∀ σ ρ, AusRelRu (schritt' (worldR σ) (envR ρ)) (schritt σ ρ))
    (hb : ∀ σ ρ, bis' (worldR σ) (envR ρ) = (worldR (bis σ ρ).1, (bis σ ρ).2))
    (hu : ∀ σ ρ, AusRelRu (ueber' (worldR σ) (envR ρ)) (ueber σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      AusRelRu (retryLauf schritt' bis' ueber' n (worldR σ) (envR ρ))
        (retryLauf schritt bis ueber n σ ρ)
  | 0, σ, ρ => by
      simp only [retryLauf, hb]
      by_cases hc : (bis σ ρ).2 = true
      · simp only [hc, if_true]; exact Or.inl rfl
      · simp only [hc, if_false, Bool.false_eq_true]
        exact hu _ ρ
  | n + 1, σ, ρ => by
      simp only [retryLauf, hb]
      by_cases hc : (bis σ ρ).2 = true
      · simp only [hc, if_true]; exact Or.inl rfl
      · simp only [hc, if_false, Bool.false_eq_true]
        rcases hs (bis σ ρ).1 ρ with e | ⟨e', e0, h1, h2, ht⟩
        · rw [e]
          cases schritt (bis σ ρ).1 ρ with
          | ok σ' ρ' => exact retryLauf_rel schritt schritt' bis bis' ueber ueber' hs hb hu n σ' ρ'
          | next h σ' ρ' => exact retryLauf_rel schritt schritt' bis bis' ueber ueber' hs hb hu n σ' ρ'
          | leave h σ' ρ' => exact Or.inl rfl
          | zurueck => exact Or.inl rfl
          | why => exact Or.inl rfl
          | logik => exact Or.inl rfl
          | hardware => exact Or.inl rfl
        · rw [h1, h2]
          exact Or.inr ⟨e', e0, rfl, rfl, ht⟩

theorem foreverLauf_rel (a : D.Annahme)
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (schritt' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → Ausgang (vertragR V) true (Γ.map tyR))
    (inv : World D → Env D Γ → World D × Bool)
    (inv' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → World D.mitRuhe × Bool)
    (hs : ∀ σ ρ, AusRelRu (schritt' (worldR σ) (envR ρ)) (schritt σ ρ))
    (hi : ∀ σ ρ, inv' (worldR σ) (envR ρ) = (worldR (inv σ ρ).1, (inv σ ρ).2)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      AusRelRu (foreverLauf (D := D.mitRuhe) (l := l) a schritt' inv' n (worldR σ) (envR ρ))
        (foreverLauf (l := l) a schritt inv n σ ρ)
  | 0, _, _ => Or.inl rfl
  | n + 1, σ, ρ => by
      simp only [foreverLauf, hi]
      by_cases hc : (inv σ ρ).2 = false
      · simp only [hc, if_true]; exact Or.inl rfl
      · simp only [hc, if_false]
        rcases hs (inv σ ρ).1 ρ with e | ⟨e', e0, h1, h2, ht⟩
        · rw [e]
          cases schritt (inv σ ρ).1 ρ with
          | ok σ' ρ' => exact foreverLauf_rel a schritt schritt' inv inv' hs hi n σ' ρ'
          | next h σ' ρ' => exact foreverLauf_rel a schritt schritt' inv inv' hs hi n σ' ρ'
          | leave h σ' ρ' => exact Or.inl rfl
          | zurueck => exact Or.inl rfl
          | why => exact Or.inl rfl
          | logik => exact Or.inl rfl
          | hardware => exact Or.inl rfl
        · rw [h1, h2]
          exact Or.inr ⟨e', e0, rfl, rfl, ht⟩

end Schleifen

/-! ## 4. Transport helpers -/

section Hilfen

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)

theorem execStmtH_nachΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (s : Stmt D V l Γ Λ Λ₁) (σ : World D) (ρ : Env D Γ) :
    execStmtH S O U passes R (Stmt.nachΛ h s) σ ρ = execStmtH S O U passes R s σ ρ := by
  subst h; rfl

theorem execBlockH_vorΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ Λ' : List (Res D)} (h : Λ₁ = Λ₂)
    (b : Block D V l Γ Λ₁ Λ') (σ : World D) (ρ : Env D Γ) :
    execBlockH S O U passes R (Block.vorΛ h b) σ ρ = execBlockH S O U passes R b σ ρ := by
  subst h; rfl

theorem execEndH_umΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (e : Endblock D V l Γ Λ₁) (σ : World D) (ρ : Env D Γ) :
    execEndH S O U passes R (Endblock.umΛ h e) σ ρ = execEndH S O U passes R e σ ρ := by
  subst h; rfl

end Hilfen

/-! ## 5. Every statement, block and end block, up to the label -/

section Haupt

variable (S : SperrInv D) (O : Orakel D) (O' : Orakel D.mitRuhe) (hO : OrakelRu O O')
  (U : Umwelt D) (U' : Umwelt D.mitRuhe) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
  (hU : ∀ L σ, U' L (worldR σ) = worldR (U L σ))
  (hR : RufRel R R')

include hO hU hR

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_assignSlot {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (f)
    (i)
    (e)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.assignSlot t f i e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.assignSlot t f i e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtH]
  rw [orte2, lese_worldR, eval_ru, eval_ru, schreibSlot_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_assignThru {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    (p)
    (t)
    (ht)
    (f)
    (i)
    (e)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.assignThru (n := zi_n) (read := zi_read) (space := zi_space) p t ht f i e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.assignThru (n := zi_n) (read := zi_read) (space := zi_space) p t ht f i e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtH]
  rw [show (ruE p).orte ++ (ruE i).orte ++ (ruE e).orte = p.orte ++ i.orte ++ e.orte from
    kongr₂ (· ++ ·) (orte2 p i) (ruE_orte e), lese_worldR, eval_ru, eval_ru, schreibSlot_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_assignSlotRef {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    (r)
    (t)
    (ht)
    (ho)
    (f)
    (e)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.assignSlotRef (n := zi_n) r t ht ho f e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.assignSlotRef (n := zi_n) r t ht ho f e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtH]
  rw [show (ruE r).orte ++ (ruE e).orte = r.orte ++ e.orte from
    kongr₂ (· ++ ·) (ruE_orte r) (ruE_orte e), lese_worldR, eval_ru, eval_ru, schreibSlot_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_assignGlob {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (e)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.assignGlob g e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.assignGlob g e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtH]
  rw [ruE_orte, lese_worldR, eval_ru, schreibGlob_worldR]
  rfl

end Haupt
end Gabbro.Grammatik
