/-
  File:      Grammatik/MitRuheSperre.lean
  Subject:   THE LOCK-INVARIANT SEMANTICS OF P.mitRuhe BEHAVES AS THE ONE OF
             P (the open piece of MitRuheSemantik.lean's header): every
             statement, block and end block of a translated body runs under
             `execStmtH`/`execBlockH`/`execEndH` (acquire moves, release
             checks) from the translated world and environment to the
             translated outcome -- up to the LABEL of a logic failure that a
             call handler of `D.mitRuhe` answers (`AusRel`, `EndRel`).

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
import Grammatik.MitRuheSemantik

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

/-- A call outcome of `D.mitRuhe` at `some g`, translated back; a logic
    failure becomes `schleife` (its label is not read back). -/
def rufZ {g : D.Fn} : RufAusgang (D := D.mitRuhe) (some g) → RufAusgang g
  | .ok σ v => .ok (worldZ σ) (ergZ (D.erg g) v)
  | .grund σ r => .grund (worldZ σ) r
  | .logik _ => .logik .schleife
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

/-- Every oracle of `D.mitRuhe` is the translation of one of `D`. -/
theorem zurueck_mitRuhe (O' : Orakel D.mitRuhe) : (Orakel.zurueck O').mitRuhe = O' := by
  cases O' with
  | mk w r s v =>
      simp only [Orakel.mitRuhe, Orakel.zurueck, worldR_worldZ, envR_envZ]

/-- The move of `D` a move of `D.mitRuhe` makes. -/
def umweltZ (U' : Umwelt D.mitRuhe) : Umwelt D := fun L σ => worldZ (U' L (worldR σ))

theorem umweltZ_ru (U' : Umwelt D.mitRuhe) (L : D.Lock) (σ : World D) :
    U' L (worldR σ) = worldR (umweltZ U' L σ) := (worldR_worldZ _).symm

/-! ## 2. Outcomes up to the label of a logic failure -/

/-- A logic label of `D.mitRuhe` blames a caller only if the one of `D` does. -/
def LogikTreu (e' : Logik D.mitRuhe) (e : Logik D) : Prop :=
  ∀ g', e' = .vorbedingung g' → ∃ g, e = .vorbedingung g

section Rel

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

/-- The translated outcome, or two logic failures (`LogikTreu`). -/
def AusRel (a' : Ausgang (vertragR V) l (Γ.map tyR)) (a : Ausgang V l Γ) : Prop :=
  a' = ausR a ∨ ∃ e' e, a' = .logik e' ∧ a = .logik e ∧ LogikTreu e' e

/-- The translated end outcome, or two logic failures (`LogikTreu`). -/
def EndRel (a' : EndAusgang (vertragR V) l (Γ.map tyR)) (a : EndAusgang V l Γ) : Prop :=
  a' = endR a ∨ ∃ e' e, a' = .logik e' ∧ a = .logik e ∧ LogikTreu e' e

theorem AusRel.schrumpf {τ : Ty} {a' : Ausgang (vertragR V) l ((τ :: Γ).map tyR)}
    {a : Ausgang V l (τ :: Γ)} (h : AusRel a' a) : AusRel a'.schrumpf a.schrumpf := by
  rcases h with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]; exact Or.inl (ausR_schrumpf a)
  · rw [h1, h2]; exact Or.inr ⟨e', e, rfl, rfl, ht⟩

theorem EndRel.schrumpf {τ : Ty} {a' : EndAusgang (vertragR V) l ((τ :: Γ).map tyR)}
    {a : EndAusgang V l (τ :: Γ)} (h : EndRel a' a) : EndRel a'.schrumpf a.schrumpf := by
  rcases h with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]; exact Or.inl (endR_schrumpf a)
  · rw [h1, h2]; exact Or.inr ⟨e', e, rfl, rfl, ht⟩

theorem EndRel.zuAusgang {a' : EndAusgang (vertragR V) l (Γ.map tyR)} {a : EndAusgang V l Γ}
    (h : EndRel a' a) : AusRel a'.zuAusgang a.zuAusgang := by
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
  | grund => rfl
  | logik => rfl
  | hardware => rfl

theorem AusRel.frei (S : SperrInv D) (L : D.Lock) {a' : Ausgang (vertragR V) l (Γ.map tyR)}
    {a : Ausgang V l Γ} (h : AusRel a' a) : AusRel (freiH S.mitRuhe L a') (freiH S L a) := by
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
    (hs : ∀ σ ρ, AusRel (Γ := τ :: Γ) (schritt' (worldR σ) (envR ρ)) (schritt σ ρ))
    (hi : ∀ σ ρ, inv' (worldR σ) (envR ρ) = (worldR (inv σ ρ).1, (inv σ ρ).2)) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ),
      AusRel (traverseLauf (l := l) schritt' inv' (ks.map (valR τ)) (worldR σ) (envR ρ))
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
        change AusRel (Γ := τ :: Γ) (schritt' (worldR (inv σ ρ).1) (Env.cons (valR τ k) (envR ρ)))
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
          | grund => exact Or.inl rfl
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
    (hs : ∀ σ ρ, AusRel (schritt' (worldR σ) (envR ρ)) (schritt σ ρ))
    (hb : ∀ σ ρ, bis' (worldR σ) (envR ρ) = (worldR (bis σ ρ).1, (bis σ ρ).2))
    (hu : ∀ σ ρ, AusRel (ueber' (worldR σ) (envR ρ)) (ueber σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      AusRel (retryLauf schritt' bis' ueber' n (worldR σ) (envR ρ))
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
          | grund => exact Or.inl rfl
          | logik => exact Or.inl rfl
          | hardware => exact Or.inl rfl
        · rw [h1, h2]
          exact Or.inr ⟨e', e0, rfl, rfl, ht⟩

theorem foreverLauf_rel (a : D.Annahme)
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (schritt' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → Ausgang (vertragR V) true (Γ.map tyR))
    (inv : World D → Env D Γ → World D × Bool)
    (inv' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → World D.mitRuhe × Bool)
    (hs : ∀ σ ρ, AusRel (schritt' (worldR σ) (envR ρ)) (schritt σ ρ))
    (hi : ∀ σ ρ, inv' (worldR σ) (envR ρ) = (worldR (inv σ ρ).1, (inv σ ρ).2)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      AusRel (foreverLauf (D := D.mitRuhe) (l := l) a schritt' inv' n (worldR σ) (envR ρ))
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
          | grund => exact Or.inl rfl
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

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (U' : Umwelt D.mitRuhe) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
  (hU : ∀ L σ, U' L (worldR σ) = worldR (U L σ))
  (hR : RufRel R R')

include hU hR

set_option maxHeartbeats 4000000 in
mutual

/-- **A translated statement runs as the statement under the lock-invariant
    semantics**, up to the label of a logic failure. -/
theorem execStmtH_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    AusRel (execStmtH S.mitRuhe O.mitRuhe U' passes R' (ruS s) (worldR σ) (envR ρ))
      (execStmtH S O U passes R s σ ρ)
  | _, _, Λ, _, .assignSlot t f i e hw hL, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtH]
      rw [orte2, lese_worldR, eval_ru, eval_ru, schreibSlot_worldR]
      rfl
  | _, _, Λ, _, .assignDurch p t ht f i e hw hL, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtH]
      rw [show (ruE p).orte ++ (ruE i).orte ++ (ruE e).orte = p.orte ++ i.orte ++ e.orte from
        kongr₂ (· ++ ·) (orte2 p i) (ruE_orte e), lese_worldR, eval_ru, eval_ru, schreibSlot_worldR]
      rfl
  | _, _, Λ, _, .assignGlob g e hw hL, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtH]
      rw [ruE_orte, lese_worldR, eval_ru, schreibGlob_worldR]
      rfl
  | _, _, Λ, _, .schreibBytes t f hf n i hlo hhi e hw hL, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtH]
      rw [orte2, lese_worldR, eval_ru, eval_ru, schreibBytes_worldR t f hf]
      rfl
  | _, _, Λ, _, .assignVar x e, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtH]
      rw [ruE_orte, lese_worldR, eval_ru, envR_set]
      rfl
  | _, _, Λ, _, .uebergang (lo := lo) (hi := hi) t f hτ i von nach hn he hw hL, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtH]
      erw [show (Sum.inl t :: (ruE i).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
        Sum.inl t :: i.orte from congrArg (Sum.inl t :: ·) (ruE_orte i)]
      erw [lese_worldR, eval_ru]
      erw [slotInt_cast_worldR _ t f hτ (congrArg tyR hτ)]
      by_cases hc : (hτ ▸ (σ.lese Λ (Sum.inl t :: i.orte)).slots t
          (eval (σ.lese Λ (Sum.inl t :: i.orte)) i (σ.lese Λ (Sum.inl t :: i.orte)) ρ).n f :
          Wert D (.int lo hi)).n = von
      · erw [if_pos hc, if_pos hc, int_cast_gen' (D.typ t f) lo hi hτ (congrArg tyR hτ) _,
          schreibSlot_worldR]
        rfl
      · erw [if_neg hc, if_neg hc]
        rfl
  | _, _, Λ, _, .ite c t e, σ, ρ => by
      simp only [ruS, execStmtH]
      rw [ruE_orte, lese_worldR, eval_ru]
      cases h : (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ : Bool)
      · simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
        exact execBlockH_ru e _ ρ
      · simp only [wahr?, valR_bool, h, if_true]
        exact execBlockH_ru t _ ρ
  | _, _, Λ, _, .onOption o p a, σ, ρ => by
      simp only [ruS, execStmtH]
      rw [ruE_orte, lese_worldR, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases h : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ with
      | none => exact execBlockH_ru a _ ρ
      | some k =>
          simp only
          exact AusRel.schrumpf (execBlockH_ru p _ (Env.cons k ρ))
  | _, _, Λ, _, .onTag v arms, σ, ρ => by
      simp only [ruS, execStmtH]
      rw [ruE_orte, lese_worldR, eval_ru]
      exact execArmsH_ru arms _ _ ρ
  | _, _, Λ, _, .onGrund r arms, σ, ρ => by
      simp only [ruS, execStmtH]
      rw [ruE_orte, lese_worldR, eval_ru]
      exact execGrundH_ru arms _ _ ρ
  | _, _, Λ, _, .call g args hp hr, σ, ρ => by
      simp only [ruS]
      erw [execStmtH_nachΛ]
      simp only [execStmtH]
      erw [ruA_orte, lese_worldR, evalArgs_ru]
      rcases hR g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        with hx' | ⟨e', e, h1, h2, ht⟩
      · erw [hx']
        cases hx : R g (σ.lese Λ args.orte)
            (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        | ok σ' v => (try erw [hx]); exact Or.inl rfl
        | grund σ' r => exact (Fin.cast hr r).elim0
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩
  | _, _, Λ, _, .callInd (n := n) p args hp hr, σ, ρ => by
      simp only [ruS]
      erw [execStmtH_nachΛ]
      simp only [execStmtH]
      erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
        kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
      erw [lese_worldR, eval_ru, evalArgs_ru]
      cases h : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ with
      | mk g hg =>
          rw [valR_fnptr]
          dsimp only
          erw [umsig_ru hg]
          rcases hR g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
              (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ))
            with hx' | ⟨e', e, h1, h2, ht⟩
          · erw [hx']
            cases hx : R g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
                (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
            | ok σ' v => (try erw [hx]); exact Or.inl rfl
            | grund σ' r => exact keinGrundSig hg hr r
            | logik e => (try erw [hx]); exact Or.inl rfl
            | hardware e => (try erw [hx]); exact Or.inl rfl
          · erw [h1, h2]
            exact Or.inr ⟨e', e, rfl, rfl, ht⟩
  | _, _, Λ, _, .locks L hr body, σ, ρ => by
      simp only [ruS, execStmtH]
      rw [hU, nimmt_worldR]
      exact AusRel.frei S L (execBlockH_ru body ((U L σ).nimmt L) ρ)
  | _, _, _, _, .breaking _ body, σ, ρ => by
      simp only [ruS, execStmtH]
      exact execBlockH_ru body σ ρ
  | l, _, Λ, _, .traverse t inv body, σ, ρ => by
      simp only [ruS, execStmtH]
      have hL := traverseLauf_rel (l := l) (fun σ ρ => execBlockH S O U passes R body σ ρ)
        (fun σ ρ => execBlockH S.mitRuhe O.mitRuhe U' passes R' (ruB body) σ ρ)
        (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
        (fun σ ρ => (σ.lese (Λ.map resR) (ruE inv).orte,
          wahr? (eval (σ.lese (Λ.map resR) (ruE inv).orte) (ruE inv)
            (σ.lese (Λ.map resR) (ruE inv).orte) ρ)))
        (fun σ ρ => execBlockH_ru body σ ρ)
        (fun σ ρ => by simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?])
        (alleIndizes (D.count t)) σ ρ
      rw [map_valR_int] at hL
      exact hL
  | _, _, Λ, _, .retry n bis body ueber, σ, ρ => by
      simp only [ruS, execStmtH]
      exact retryLauf_rel (fun σ ρ => execBlockH S O U passes R body σ ρ)
        (fun σ ρ => execBlockH S.mitRuhe O.mitRuhe U' passes R' (ruB body) σ ρ)
        (fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ)))
        (fun σ ρ => (σ.lese (Λ.map resR) (ruE bis).orte,
          wahr? (eval (σ.lese (Λ.map resR) (ruE bis).orte) (ruE bis)
            (σ.lese (Λ.map resR) (ruE bis).orte) ρ)))
        (fun σ ρ => execBlockH S O U passes R ueber σ ρ)
        (fun σ ρ => execBlockH S.mitRuhe O.mitRuhe U' passes R' (ruB ueber) σ ρ)
        (fun σ ρ => execBlockH_ru body σ ρ)
        (fun σ ρ => by simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?])
        (fun σ ρ => execBlockH_ru ueber σ ρ) n σ ρ
  | _, _, Λ, _, .forever a inv body, σ, ρ => by
      simp only [ruS, execStmtH]
      exact foreverLauf_rel a (fun σ ρ => execBlockH S O U passes R body σ ρ)
        (fun σ ρ => execBlockH S.mitRuhe O.mitRuhe U' passes R' (ruB body) σ ρ)
        (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
        (fun σ ρ => (σ.lese (Λ.map resR) (ruE inv).orte,
          wahr? (eval (σ.lese (Λ.map resR) (ruE inv).orte) (ruE inv)
            (σ.lese (Λ.map resR) (ruE inv).orte) ρ)))
        (fun σ ρ => execBlockH_ru body σ ρ)
        (fun σ ρ => by simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?]) passes σ ρ
  | _, _, Λ, _, .axiomCall a args h hw hg hd hgd, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtH]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ru]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => rfl
          | some _ => rfl
  | _, _, Λ, _, .regSchreib r hk e, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtH]
      rw [ruE_orte, lese_worldR]
      rfl
  | _, _, _, _, .transition .., σ, ρ => Or.inl rfl
  | _, _, Λ, _, .publish g e payload hp hw hL, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtH]
      rw [ruE_orte, lese_worldR, eval_ru, schreibGlob_worldR]
      rfl
  | _, _, _, _, .advances .., σ, ρ => by
      refine Or.inl ?_
      simp only [ruS]
      erw [execStmtH_nachΛ]
      rfl
  | _, _, _, _, .retires .., σ, ρ => by
      refine Or.inl ?_
      simp only [ruS]
      erw [execStmtH_nachΛ]
      rfl
  | _, _, Λ, _, .ret e hΛ, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtH]
      erw [ruErg_orte, lese_worldR, evalErg_ru]
      rfl
  | _, _, _, _, .retGrund .., σ, ρ => Or.inl rfl
  | _, _, _, _, .leave _, σ, ρ => Or.inl rfl
  | _, _, _, _, .next _, σ, ρ => Or.inl rfl

theorem execBlockH_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    AusRel (execBlockH S.mitRuhe O.mitRuhe U' passes R' (ruB b) (worldR σ) (envR ρ))
      (execBlockH S O U passes R b σ ρ)
  | _, _, _, _, .nil, σ, ρ => Or.inl rfl
  | _, _, _, _, .cons s rest, σ, ρ => by
      simp only [ruB, execBlockH]
      rcases execStmtH_ru s σ ρ with h | ⟨e', e, h1, h2, ht⟩
      · rw [h]
        cases execStmtH S O U passes R s σ ρ with
        | ok σ' ρ' => exact execBlockH_ru rest σ' ρ'
        | _ => exact Or.inl rfl
      · rw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩
  | _, _, Λ, _, .bind e rest, σ, ρ => by
      simp only [ruB, execBlockH]
      rw [ruE_orte, lese_worldR, eval_ru]
      exact AusRel.schrumpf (execBlockH_ru rest (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ))
  | _, _, Λ, _, .bindCall g args he hp hr rest, σ, ρ => by
      simp only [ruB, execBlockH]
      erw [ruA_orte, lese_worldR, evalArgs_ru]
      rcases hR g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        with hx' | ⟨e', e, h1, h2, ht⟩
      · erw [hx']
        cases hx : R g (σ.lese Λ args.orte)
            (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        | ok σ' v =>
            try erw [hx]
            simp only [rufR]
            erw [execBlockH_vorΛ, ergWert_ru he]
            exact AusRel.schrumpf (execBlockH_ru rest σ' (Env.cons (ergWert he v) ρ))
        | grund σ' r => exact (Fin.cast hr r).elim0
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩
  | _, _, Λ, _, .bindCallInd (n := n) p args he hp hr rest, σ, ρ => by
      simp only [ruB, execBlockH]
      erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
        kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
      erw [lese_worldR, eval_ru, evalArgs_ru]
      cases h : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ with
      | mk g hg =>
          rw [valR_fnptr]
          dsimp only
          erw [umsig_ru hg]
          rcases hR g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
              (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ))
            with hx' | ⟨e', e, h1, h2, ht⟩
          · erw [hx']
            cases hx : R g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
                (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
            | ok σ' v =>
                try erw [hx]
                simp only [rufR]
                erw [execBlockH_vorΛ, ergWert_ru (ergSig hg he)]
                exact AusRel.schrumpf
                  (execBlockH_ru rest σ' (Env.cons (ergWert (ergSig hg he) v) ρ))
            | grund σ' r => exact keinGrundSig hg hr r
            | logik e => (try erw [hx]); exact Or.inl rfl
            | hardware e => (try erw [hx]); exact Or.inl rfl
          · erw [h1, h2]
            exact Or.inr ⟨e', e, rfl, rfl, ht⟩
  | _, _, Λ, _, .bindCallElse g args he hp hr err rest, σ, ρ => by
      simp only [ruB, execBlockH]
      erw [ruA_orte, lese_worldR, evalArgs_ru]
      rcases hR g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        with hx' | ⟨e', e, h1, h2, ht⟩
      · erw [hx']
        cases hx : R g (σ.lese Λ args.orte)
            (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        | ok σ' v =>
            try erw [hx]
            simp only [rufR]
            erw [execBlockH_vorΛ, ergWert_ru he]
            exact AusRel.schrumpf (execBlockH_ru rest σ' (Env.cons (ergWert he v) ρ))
        | grund σ' r =>
            try erw [hx]
            simp only [rufR]
            erw [execEndH_umΛ]
            exact EndRel.zuAusgang (EndRel.schrumpf (execEndH_ru err σ' (Env.cons r ρ)))
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩
  | _, _, Λ, _, .bindAxiom a args he hw hg hd hgd rest, σ, ρ => by
      simp only [ruB, execBlockH]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ru]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => exact Or.inl rfl
          | some v =>
              simp only [Option.map]
              rw [ergWert_ru he]
              exact AusRel.schrumpf (execBlockH_ru rest σ' (Env.cons (ergWert he v) ρ))
  | _, _, _, _, .regLies r hk rest, σ, ρ => by
      simp only [ruB, execBlockH]
      rw [regLies_mitRuhe, einpassen_ru]
      cases einpassen (D.rtyp r) (O.regLies r σ) with
      | none => exact Or.inl rfl
      | some v =>
          simp only [Option.map]
          erw [rzusage_mitRuhe]
          cases D.rzusage r v with
          | false => exact Or.inl rfl
          | true =>
              simp only [if_true]
              exact AusRel.schrumpf (execBlockH_ru rest σ (Env.cons v ρ))
  | _, _, Λ, _, .regLiesElse r hk zusage sonst rest, σ, ρ => by
      simp only [ruB, execBlockH]
      rw [regLies_mitRuhe, einpassen_ru]
      cases einpassen (D.rtyp r) (O.regLies r σ) with
      | none => exact Or.inl rfl
      | some v =>
          simp only [Option.map]
          rw [ruE_orte, lese_worldR]
          have ez := eval_ru (σ.lese Λ zusage.orte) (σ.lese Λ zusage.orte) zusage (Env.cons v ρ)
          change eval _ (ruE zusage) _ (Env.cons (valR _ v) (envR ρ)) = _ at ez
          rw [ez]
          cases h : (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (Env.cons v ρ) : Bool) with
          | false =>
              simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
              exact EndRel.zuAusgang (execEndH_ru sonst _ ρ)
          | true =>
              simp only [wahr?, valR_bool, h, if_true]
              exact AusRel.schrumpf (execBlockH_ru rest _ (Env.cons v ρ))
  | _, _, Λ, _, .awaits g payload hp hL rest, σ, ρ => by
      simp only [ruB, execBlockH]
      rw [sichtbar_mitRuhe]
      cases O.sichtbar g σ with
      | false => exact Or.inl rfl
      | true =>
          simp only [if_true]
          rw [show ([Sum.inr g] : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) = [Sum.inr g] from rfl,
            lese_worldR]
          exact AusRel.schrumpf (execBlockH_ru rest (σ.lese Λ [Sum.inr g])
            (Env.cons ((σ.lese Λ [Sum.inr g]).globs g) ρ))
  | _, _, Λ, _, .exchange g neu hw hL rest, σ, ρ => by
      simp only [ruB, execBlockH]
      rw [show (Sum.inr g :: (ruE neu).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
        Sum.inr g :: neu.orte from congrArg (Sum.inr g :: ·) (ruE_orte neu), lese_worldR]
      have ez := eval_ru (σ.lese Λ (Sum.inr g :: neu.orte)) (σ.lese Λ (Sum.inr g :: neu.orte)) neu
        (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ)
      change eval _ (ruE neu) _ (Env.cons (valR _ _) (envR ρ)) = _ at ez
      rw [show ((worldR (σ.lese Λ (Sum.inr g :: neu.orte))).globs g) =
        valR _ ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) from rfl, ez, schreibGlob_worldR]
      exact AusRel.schrumpf (execBlockH_ru rest
        ((σ.lese Λ (Sum.inr g :: neu.orte)).schreibGlob g Λ (eval (σ.lese Λ (Sum.inr g :: neu.orte)) neu
          (σ.lese Λ (Sum.inr g :: neu.orte)) (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ)))
        (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ))
  | _, _, Λ, _, .narrow e lo' hi' sonst rest, σ, ρ => by
      simp only [ruB, execBlockH]
      simp only [ruE_orte, lese_worldR, eval_ru, valR_int]
      by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
          (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
      · erw [dif_pos hc, dif_pos hc]
        exact AusRel.schrumpf (execBlockH_ru rest _
          (Env.cons (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
      · erw [dif_neg hc, dif_neg hc]
        exact EndRel.zuAusgang (execEndH_ru sonst _ ρ)
  | _, _, Λ, _, .pruefung c sonst rest, σ, ρ => by
      simp only [ruB, execBlockH]
      rw [ruE_orte, lese_worldR, eval_ru]
      cases h : (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ : Bool) with
      | false =>
          simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
          exact EndRel.zuAusgang (execEndH_ru sonst _ ρ)
      | true =>
          simp only [wahr?, valR_bool, h, if_true]
          exact execBlockH_ru rest _ ρ
  | _, _, Λ, _, .gleit op a b lo hi rest, σ, ρ => by
      simp only [ruB, execBlockH]
      rw [orte2, lese_worldR, eval_ru, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases gleitPasst lo hi (gleitRechne op
          (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
          (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) with
      | none => exact Or.inl rfl
      | some v => exact AusRel.schrumpf (execBlockH_ru rest _ (Env.cons v ρ))
  | _, _, _, _, .gleitLit q lo hi rest, σ, ρ => by
      simp only [ruB, execBlockH]
      cases gleitPasst lo hi (bruch q) with
      | none => exact Or.inl rfl
      | some v => exact AusRel.schrumpf (execBlockH_ru rest _ (Env.cons v ρ))
  | _, _, Λ, _, .gleitVon e lo hi rest, σ, ρ => by
      simp only [ruB, execBlockH]
      rw [ruE_orte, lese_worldR, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) with
      | none => exact Or.inl rfl
      | some v => exact AusRel.schrumpf (execBlockH_ru rest _ (Env.cons v ρ))
  | _, _, Λ, _, .gleitNarrow e lo hi sonst rest, σ, ρ => by
      simp only [ruB, execBlockH]
      rw [ruE_orte, lese_worldR, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x with
      | none => exact EndRel.zuAusgang (execEndH_ru sonst _ ρ)
      | some v => exact AusRel.schrumpf (execBlockH_ru rest _ (Env.cons v ρ))

theorem execEndH_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
    EndRel (execEndH S.mitRuhe O.mitRuhe U' passes R' (ruEnd e) (worldR σ) (envR ρ))
      (execEndH S O U passes R e σ ρ)
  | _, _, Λ, .ret e hΛ, σ, ρ => by
      refine Or.inl ?_
      simp only [ruEnd, execEndH]
      erw [ruErg_orte, lese_worldR, evalErg_ru]
      rfl
  | _, _, _, .retGrund .., σ, ρ => Or.inl rfl
  | _, _, _, .leave _, σ, ρ => Or.inl rfl
  | _, _, _, .next _, σ, ρ => Or.inl rfl
  | _, _, _, .cons s rest, σ, ρ => by
      simp only [ruEnd, execEndH]
      rcases execStmtH_ru s σ ρ with h | ⟨e', e, h1, h2, ht⟩
      · rw [h]
        cases execStmtH S O U passes R s σ ρ with
        | ok σ' ρ' => exact execEndH_ru rest σ' ρ'
        | _ => exact Or.inl rfl
      · rw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩
  | _, _, Λ, .bind e rest, σ, ρ => by
      simp only [ruEnd, execEndH]
      rw [ruE_orte, lese_worldR, eval_ru]
      exact EndRel.schrumpf (execEndH_ru rest (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ))

theorem execArmsH_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs))
    (σ : World D) (ρ : Env D Γ),
    AusRel (execArmsH S.mitRuhe O.mitRuhe U' passes R' (ruArms arms) (valR (.sum cs) v)
        (worldR σ) (envR ρ))
      (execArmsH S O U passes R arms v σ ρ)
  | _, _, _, _, _, .cons (c := none) b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ => execBlockH_ru b σ ρ
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ =>
      AusRel.schrumpf (execBlockH_ru b σ (Env.cons nutz ρ))
  | _, _, _, _, _, .cons (c := none) b rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArmsH_ru rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArmsH_ru rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ

theorem execGrundH_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    AusRel (execGrundH S.mitRuhe O.mitRuhe U' passes R' (ruGArms arms) r (worldR σ) (envR ρ))
      (execGrundH S O U passes R arms r σ ρ)
  | _, _, _, _, _, .cons b _, ⟨0, _⟩, σ, ρ => execBlockH_ru b σ ρ
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, h⟩, σ, ρ =>
      execGrundH_ru rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ σ ρ

end

end Haupt

/-- **The body of `some f` in `P.mitRuhe` under the lock-invariant semantics
    runs as the body of `f` in `P`**, up to the label of a logic failure. -/
theorem rumpfH_mitRuhe (P : Programm D) (S : SperrInv D) (O : Orakel D) (U : Umwelt D)
    (U' : Umwelt D.mitRuhe) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) →
      RufAusgang f)
    (hU : ∀ L σ, U' L (worldR σ) = worldR (U L σ)) (hR : RufRel R R')
    (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) :
    @EndRel D (vertragVon D f) false (D.params f)
      (execEndH S.mitRuhe O.mitRuhe U' passes R' (P.mitRuhe.rumpf (some f)) (worldR σ) (envR ρ))
      (execEndH S O U passes R (P.rumpf f) σ ρ) := by
  have e := execEndH_umΛ S.mitRuhe O.mitRuhe U' passes R' (anfang_map (D.signatur f))
    (ruEnd (P.rumpf f)) (worldR σ) (envR ρ)
  show @EndRel D (vertragVon D f) false (D.params f) (execEndH S.mitRuhe O.mitRuhe U' passes R'
    (Endblock.umΛ (anfang_map (D.signatur f)) (ruEnd (P.rumpf f))) (worldR σ) (envR ρ)) _
  rw [e]
  exact execEndH_ru S O U U' passes R R' hU hR (P.rumpf f) σ ρ

#print axioms Gabbro.Grammatik.worldR_worldZ
#print axioms Gabbro.Grammatik.envR_envZ
#print axioms Gabbro.Grammatik.zurueck_mitRuhe
#print axioms Gabbro.Grammatik.execStmtH_ru
#print axioms Gabbro.Grammatik.execEndH_ru
#print axioms Gabbro.Grammatik.rumpfH_mitRuhe

end Gabbro.Grammatik
