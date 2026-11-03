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
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre.Teil1
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

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

/-- A consuming run, up to the label: selection, measure and invariant
    transport worlds (`hsel`, `hm`, `hi`), the body by `hs`. By induction
    on the fuel; every failing check is `.logik .schleife` on both sides. -/
theorem verbrauchLauf_rel (t : D.Tab)
    (schritt : World D → Env D (.index (D.count t) :: Γ) →
      Ausgang V true (.index (D.count t) :: Γ))
    (schritt' : World D.mitRuhe →
      Env D.mitRuhe (tyR (.index (D.count t)) :: Γ.map tyR) →
      Ausgang (vertragR V) true (tyR (.index (D.count t)) :: Γ.map tyR))
    (inv : World D → Env D Γ → World D × Bool)
    (inv' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) →
      World D.mitRuhe × Bool)
    (sel : World D → Env D Γ →
      World D × Option (Wert D (.index (D.count t))) × Bool)
    (sel' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) →
      World D.mitRuhe × Option (Wert D.mitRuhe (tyR (.index (D.count t)))) × Bool)
    (massW : World D → Env D Γ → World D × Int)
    (massW' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) →
      World D.mitRuhe × Int)
    (bound : Int)
    (hs : ∀ σ ρ, AusRelRu (Γ := .index (D.count t) :: Γ)
      (schritt' (worldR σ) (envR ρ)) (schritt σ ρ))
    (hi : ∀ σ ρ, inv' (worldR σ) (envR ρ) =
      (worldR (inv σ ρ).1, (inv σ ρ).2))
    (hsel : ∀ σ ρ, sel' (worldR σ) (envR ρ) =
      (worldR (sel σ ρ).1, ((sel σ ρ).2.1).map (valR _), (sel σ ρ).2.2))
    (hm : ∀ σ ρ, massW' (worldR σ) (envR ρ) =
      (worldR (massW σ ρ).1, (massW σ ρ).2)) :
    ∀ (fuel : Nat) (σ : World D) (ρ : Env D Γ),
      AusRelRu (verbrauchLauf (l := l) t schritt' inv' sel' massW' bound fuel
        (worldR σ) (envR ρ))
        (verbrauchLauf (l := l) t schritt inv sel massW bound fuel σ ρ)
  | 0, σ, ρ => by
      refine Or.inl ?_
      simp only [verbrauchLauf, ausR, logikR]
  | n + 1, σ, ρ => by
      simp only [verbrauchLauf, hi]
      by_cases hc : (inv σ ρ).2 = false
      · refine Or.inl ?_
        simp only [hc, if_true, ausR, logikR]
      · simp only [hc, if_false]
        have hselc := hsel (inv σ ρ).1 ρ
        generalize hgen : sel (inv σ ρ).1 ρ = sw at hselc ⊢
        obtain ⟨σr, w, b⟩ := sw
        rw [hselc]
        cases w with
        | none =>
            simp only [Option.map_none]
            cases b with
            | false =>
                refine Or.inl ?_
                simp only [ausR]
            | true =>
                refine Or.inl ?_
                simp only [ausR, logikR]
        | some v =>
            simp only [Option.map_some]
            have hmc := hm σr ρ
            generalize hgm : massW σr ρ = mw at hmc ⊢
            obtain ⟨σm, m⟩ := mw
            rw [hmc]
            simp only []
            have e := hs σm (Env.cons v ρ)
            change AusRelRu (Γ := .index (D.count t) :: Γ)
              (schritt' (worldR σm) (Env.cons (valR _ v) (envR ρ))) _ at e
            rcases e with e | ⟨e', e0, h1, h2, ht⟩
            · rw [e]
              cases schritt σm (Env.cons v ρ) with
              | ok σ' ρ' =>
                  simp only [ausR, envR_tail]
                  have hmc' := hm σ' ρ'.tail
                  generalize hgm' : massW σ' ρ'.tail = mw' at hmc' ⊢
                  obtain ⟨σm', m'⟩ := mw'
                  rw [hmc']
                  simp only []
                  by_cases hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < m
                  · simp only [hfall, if_true]
                    exact verbrauchLauf_rel t schritt schritt' inv inv' sel sel'
                      massW massW' bound hs hi hsel hm n σm' ρ'.tail
                  · refine Or.inl ?_
                    simp only [hfall, if_false, ausR, logikR]
              | next h σ' ρ' =>
                  simp only [ausR, envR_tail]
                  have hmc' := hm σ' ρ'.tail
                  generalize hgm' : massW σ' ρ'.tail = mw' at hmc' ⊢
                  obtain ⟨σm', m'⟩ := mw'
                  rw [hmc']
                  simp only []
                  by_cases hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < m
                  · simp only [hfall, if_true]
                    exact verbrauchLauf_rel t schritt schritt' inv inv' sel sel'
                      massW massW' bound hs hi hsel hm n σm' ρ'.tail
                  · refine Or.inl ?_
                    simp only [hfall, if_false, ausR, logikR]
              | leave h σ' ρ' =>
                  simp only [ausR, envR_tail]
                  have hmc' := hm σ' ρ'.tail
                  generalize hgm' : massW σ' ρ'.tail = mw' at hmc' ⊢
                  obtain ⟨σm', m'⟩ := mw'
                  rw [hmc']
                  simp only []
                  by_cases hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < m
                  · simp only [hfall, if_true]
                    by_cases hc' : (inv σm' ρ'.tail).2 = true
                    · refine Or.inl ?_
                      simp only [hc', if_true, ausR]
                    · have hcf : (inv σm' ρ'.tail).2 = false := by
                        cases h' : (inv σm' ρ'.tail).2 with
                        | false => rfl
                        | true => exact absurd h' hc'
                      refine Or.inl ?_
                      simp only [hcf, if_false, ausR, logikR]
                  · refine Or.inl ?_
                    simp only [hfall, if_false, ausR, logikR]
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
