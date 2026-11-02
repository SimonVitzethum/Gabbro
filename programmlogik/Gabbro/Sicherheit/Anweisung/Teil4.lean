module

public import Gabbro.Sicherheit.Ausdruck
public import Gabbro.Sicherheit.Anweisung.Teil3

@[expose] public section

namespace Gabbro.Sicherheit
open Gabbro.Body

theorem rufPasst_eq {P : Programm} {Δ : Lokal} {f : String} {ps : List String} {as : List Expr}
    {pre : Expr} {S : Signatur} (h : rufPasst P Δ f ps as pre = some S) :
    P.sig f = some S ∧ ps = S.params.map (·.1) ∧ namenFrei ps = true ∧
    argumentePassen P Δ S.params as = true ∧
    schluss P.D (formen (paramUmgebung S.params)) pre = some .bool := by
  unfold rufPasst at h
  split at h
  · rename_i S' hS
    split at h
    · rename_i hc; cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      exact ⟨hS, hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩
    · cases h
  · cases h

/-- Beim Eintritt: die Argumente werten aus, die Parameter liegen in ihrem Sichtbereich, und
    die Vorbedingung ist ein Wahrheitswert -- WELCHER, sagt die Logik. -/
theorem ruf_eintritt {P : Programm} {Γ : Typing} (hD : Deklariert P.D Γ) {Δ : Umgebung}
    {s : State} (hw : Welt P.D Γ s.world) (hl : WFU Δ s.local') {f : String}
    {ps : List String} {as : List Expr} {pre : Expr} {S : Signatur}
    (h : rufPasst P (formen Δ) f ps as pre = some S) :
    ∃ vs, evalAll s as = some vs ∧ ∃ b, eval (eintritt s ps vs) pre = some (.bool b) := by
  obtain ⟨_, hps, hfrei, hargs, hpre⟩ := rufPasst_eq h
  subst hps
  obtain ⟨vs, hvs, hwfu⟩ := argumente_sicher hD hw hl S.params as (fun _ => .absent) hfrei hargs
  refine ⟨vs, hvs, ?_⟩
  have hw' : Welt P.D Γ (eintritt s (S.params.map (·.1)) vs).world := hw
  obtain ⟨v, hv, hvs'⟩ := schluss_sicher' hD hw' hwfu hpre
  obtain ⟨b, rfl⟩ := Value.hasShape_bool_true v hvs'
  exact ⟨b, hv⟩

/-! ### 6.2 `match` -- der Fall ist da, und der Arm passt zu ihm -/

theorem fall_gefunden : ∀ (cs : List (String × Option (Option (Int × Int)))) (x : String)
    (p : Option Int), namenEindeutig cs = true → Shape.caseOk cs x p = true →
    ∃ pl, suchFall cs x = some pl ∧ Shape.payloadOk pl p = true := by
  intro cs
  induction cs with
  | nil => intro x p _ h; simp only [Shape.caseOk_nil, Bool.false_eq_true] at h
  | cons c rest ih =>
      intro x p hu h
      obtain ⟨t, pl⟩ := c
      simp only [namenEindeutig, Bool.and_eq_true, Bool.not_eq_true'] at hu
      obtain ⟨hnot, hu'⟩ := hu
      simp only [Shape.caseOk_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      simp only [suchFall]
      rcases h with ⟨rfl, hpl⟩ | h
      · exact ⟨pl, by simp only [↓reduceIte], hpl⟩
      · have hne : t ≠ x := by
          intro heq; subst heq
          -- `x` haette dann einen Fall in `rest`, gegen `hnot`
          have : rest.any (fun c => c.1 == t) = true := by
            unfold Shape.caseOk at h
            simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h ⊢
            obtain ⟨c, hc, hct, _⟩ := h
            exact ⟨c, hc, hct⟩
          rw [this] at hnot; cases hnot
        simp only [hne, ↓reduceIte]
        exact ih x p hu' h

theorem grund_hat_arm : ∀ (arms : List (String × List Stmt)) (cs : List String) (r : String),
    alleGruendeHabenArm arms cs = true → r ∈ cs → arms.any (fun a => a.1 == r) = true := by
  intro arms cs
  induction cs with
  | nil => intro r _ h; simp only [List.not_mem_nil] at h
  | cons c rest ih =>
      intro r h hr
      simp only [alleGruendeHabenArm, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hr with rfl | hr
      · exact h.1
      · exact ih r h.2 hr

theorem fall_hat_arm : ∀ (arms : List (String × Option String × List Stmt))
    (cs : List (String × Option (Option (Int × Int)))) (x : String) (pl : Option (Option (Int × Int))),
    alleFaelleHabenArm arms cs = true → suchFall cs x = some pl →
    arms.any (fun a => a.1 == x) = true := by
  intro arms cs
  induction cs with
  | nil => intro x pl _ h; simp only [suchFall, reduceCtorEq] at h
  | cons c rest ih =>
      intro x pl h hs
      obtain ⟨t, pl'⟩ := c
      simp only [alleFaelleHabenArm, Bool.and_eq_true] at h
      simp only [suchFall] at hs
      split at hs
      · rename_i heq; subst heq; exact h.1
      · exact ih x pl h.2 hs

/-! ### 6.3 Der Satz -/

/-- Die Antwort eines Gerufenen ohne Fehlerkanal, wie (U1) sie zusagt. -/
theorem antwort_ohne_kanal {P : Programm} {Γ : Typing} {ρ : Env} (hU : UmgebungOK P Γ ρ)
    {f : String} {S : Signatur} (hS : P.sig f = some S) (hg : S.gruende = [])
    {t : State} (hw : Welt P.D Γ t.world) :
    Welt P.D Γ (ρ f t).1.world ∧ AntwortPasst S.ergebnis [] (ρ f t).2 := by
  obtain ⟨hw', hr, _⟩ := hU f S hS t hw
  refine ⟨hw', ?_⟩
  cases he : S.ergebnis with
  | none =>
      rw [he] at hr
      rcases hr with hr | ⟨r, hr, _⟩
      · rw [hr]; trivial
      · rw [hg] at hr; simp only [List.not_mem_nil] at hr
  | some sh =>
      rw [he] at hr
      obtain ⟨v, hv, hvs⟩ := hr
      rw [hv]
      rcases hvs with hvs | ⟨r, hr, _⟩
      · exact Or.inl hvs
      · rw [hg] at hr; simp only [List.not_mem_nil] at hr

/-- Die Antwort eines Gerufenen MIT Fehlerkanal, wie (U1) sie zusagt -- in die Antwort
    des Rufers (F6): die Gestalt muss treffen (`antwortGestaltPasst`), und ein Grund muss
    im Kanal des Rufers liegen (`gruendePassen`). -/
theorem antwort_mit_kanal {P : Programm} {Γ : Typing} {ρ : Env} (hU : UmgebungOK P Γ ρ)
    {f : String} {S : Signatur} (hS : P.sig f = some S)
    {t : State} (hw : Welt P.D Γ t.world)
    {erg : Option Shape} (hpass : antwortGestaltPasst erg S.ergebnis = true)
    (hsub : gruendePassen S.gruende P.ruferR = true) :
    Welt P.D Γ (ρ f t).1.world ∧ AntwortPasst erg P.ruferR (ρ f t).2 := by
  obtain ⟨hw', hres, _⟩ := hU f S hS t hw
  refine ⟨hw', ?_⟩
  cases he : S.ergebnis with
  | none =>
      rw [he] at hres
      cases erg with
      | none =>
          rcases hres with hres | ⟨r, hr, hres⟩
          · rw [hres]; trivial
          · rw [hres]; exact ⟨r, gruendePassen_mem hsub hr, rfl⟩
      | some _ => simp only [antwortGestaltPasst, he, Bool.false_eq_true] at hpass
  | some sh =>
      rw [he] at hres
      cases erg with
      | none => simp only [antwortGestaltPasst, he, Bool.false_eq_true] at hpass
      | some _ =>
          simp only [antwortGestaltPasst, he] at hpass
          obtain ⟨v, hv, hvs⟩ := hres
          rw [hv]
          rcases hvs with hvs | ⟨r, hr, rfl⟩
          · exact Or.inl (passt_hasShape hpass hvs)
          · exact Or.inr ⟨r, gruendePassen_mem hsub hr, rfl⟩


theorem ausgang_nicht_running (ρ : Env) (sig : String → Option Signatur)
    (hdiv : DivergenzOK sig) (a : Stmt) (s s' : State) (h : istAusgang sig a = true) :
    step ρ a s ≠ .running s' := by
  intro hx
  cases a <;> simp only [istAusgang, Bool.false_eq_true] at h
  case retCall f ps as pre =>
    simp only [step] at hx
    split at hx
    · split at hx <;> simp only [reduceCtorEq] at hx
    · simp only [reduceCtorEq] at hx
  case ret v =>
    cases v
    · simp only [step, reduceCtorEq] at hx
    · simp only [step] at hx; split at hx <;> simp only [reduceCtorEq] at hx
  case call f ps as pre =>
    cases hs : sig f with
    | none => simp only [hs, Bool.false_eq_true] at h
    | some S =>
        simp only [hs, istAusgang] at h
        have hnb := hdiv f S hs
        rw [h] at hnb
        simp only [Bool.true_eq_false] at hnb
  case exit => simp only [step, reduceCtorEq] at hx
  case leave => simp only [step, reduceCtorEq] at hx

theorem endet_nicht_running (ρ : Env) (sig : String → Option Signatur) (hdiv : DivergenzOK sig) :
    ∀ (b : List Stmt) (s s' : State), endetMitAusgang sig b = true → exec ρ b s ≠ .running s'
  | [], s, s', h, _ => by simp only [endetMitAusgang, Bool.false_eq_true] at h
  | [a], s, s', h, hx => by
      simp only [endetMitAusgang] at h
      simp only [exec] at hx
      split at hx
      · rename_i t ht; exact ausgang_nicht_running ρ sig hdiv a s t h ht
      · rename_i o ho; exact ho _ hx
  | a :: b :: rest, s, s', h, hx => by
      have h' : endetMitAusgang sig (b :: rest) = true := h
      simp only [exec] at hx
      split at hx
      · exact endet_nicht_running ρ sig hdiv (b :: rest) _ s' h' hx
      · rename_i o ho; exact ho _ hx

/-- Ein Ausgang, der KEIN `running` ist, braucht nur den Eintritts-Sichtbereich. -/
theorem Ergebnis_ausgang {P : Programm} {Γ : Typing} {erg : Option Shape}
    {Δ0 Δ1 Δ' Δ'' : Umgebung} {o : Outcome} (h0 : erweitert Δ0 Δ1)
    (hnr : ∀ s', o ≠ .running s') (h : Ergebnis P Γ erg Δ1 Δ'' o) : Ergebnis P Γ erg Δ0 Δ' o := by
  cases o <;> simp only [Ergebnis] at h ⊢
  · exact absurd rfl (hnr _)
  · exact ⟨h.1, WFU_erweitert h0 h.2.1, h.2.2⟩
  · exact ⟨h.1, WFU_erweitert h0 h.2⟩
  · exact ⟨h.1, WFU_erweitert h0 h.2⟩

theorem antwort_uebertragen {erg z : Option Shape} {R : List String} {v : Option Value}
    (h : antwortGestaltPasst erg z = true) (hv : AntwortPasst z R v) : AntwortPasst erg R v := by
  cases erg with
  | none =>
      cases z with
      | none =>
          cases v with
          | none => trivial
          | some _ => exact hv
      | some _ => simp only [antwortGestaltPasst, Bool.false_eq_true] at h
  | some _ =>
      cases z with
      | none => simp only [antwortGestaltPasst, Bool.false_eq_true] at h
      | some sh =>
          simp only [antwortGestaltPasst] at h
          cases v with
          | none => simp only [AntwortPasst] at hv
          | some w =>
              simp only [AntwortPasst] at hv ⊢
              rcases hv with hv | ⟨r, hr, rfl⟩
              · exact Or.inl (passt_hasShape h hv)
              · exact Or.inr ⟨r, hr, rfl⟩

theorem pruefeArme_gibt_Δ (P : Programm) (erg : Option Shape) (Δ : Umgebung) :
    ∀ (arms : List (String × List Stmt)) (Δ' : Umgebung),
      pruefeArme P erg Δ arms = some Δ' → Δ' = Δ
  | [], Δ', h => by simp only [pruefeArme] at h; cases h; rfl
  | (n, b) :: rest, Δ', h => by
      simp only [pruefeArme] at h; split at h
      · exact pruefeArme_gibt_Δ P erg Δ rest Δ' h
      · cases h

theorem pruefeTags_gibt_Δ (P : Programm) (erg : Option Shape) (Δ : Umgebung)
    (cs : List (String × Option (Option (Int × Int)))) :
    ∀ (arms : List (String × Option String × List Stmt)) (Δ' : Umgebung),
      pruefeTags P erg Δ cs arms = some Δ' → Δ' = Δ
  | [], Δ', h => by simp only [pruefeTags] at h; cases h; rfl
  | (t, bd, b) :: rest, Δ', h => by
      simp only [pruefeTags] at h; split at h
      · split at h
        · split at h
          · split at h
            · split at h
              · exact pruefeTags_gibt_Δ P erg Δ cs rest Δ' h
              · cases h
            · cases h
          · cases h
        · split at h
          · split at h
            · exact pruefeTags_gibt_Δ P erg Δ cs rest Δ' h
            · cases h
          · cases h
      · cases h

/-- `let n = f() else (e) { … }`, und der Gerufene antwortet mit einem WERT: die Bindung
    bekommt ihn, und er hat die Gestalt der Signatur. -/
theorem bindCallElse_wert {P : Programm} {Γ : Typing} {ρ : Env} {erg : Option Shape}
    {Δ Δ' : Umgebung} {n f err : String} {ps : List String} {as : List Expr} {pre : Expr}
    {onErr : List Stmt} {S : Signatur} {s : State} {vs : List Value} {v : Value}
    (h : (match S.ergebnis with
          | some sh => binde Δ n (.form sh)
          | none => binde Δ n (.form .opt)) = some Δ')
    (hres : match S.ergebnis with
            | some sh => ∃ w, (ρ f (eintritt s ps vs)).2 = some w ∧
                (w.hasShape sh = true ∨ ∃ r, r ∈ S.gruende ∧ w = .reason r)
            | none => (ρ f (eintritt s ps vs)).2 = none ∨
                ∃ r, r ∈ S.gruende ∧ (ρ f (eintritt s ps vs)).2 = some (.reason r))
    (hr2 : (ρ f { world := s.world, local' := bindAll ps vs fun _ => Value.absent }).2 = some v)
    (hnr : ∀ x, v ≠ .reason x)
    (hw' : Welt P.D Γ (ρ f (eintritt s ps vs)).1.world) (hl : WFU Δ s.local') :
    Ergebnis P Γ erg Δ Δ'
      (.running { world := (ρ f { world := s.world, local' := bindAll ps vs fun _ => Value.absent }).1.world,
                  local' := bindLocal s.local' n v })
    ∨ LogikS ρ (.bindCallElse n f ps as pre err onErr) s := by
  left
  simp only [Ergebnis]
  refine ⟨hw', ?_⟩
  cases he : S.ergebnis with
  | none =>
      rw [he] at h hres
      simp only [eintritt, hr2] at hres
      rcases hres with hres | ⟨r, _, hres⟩
      · cases hres
      · cases hres; exact absurd rfl (hnr r)
  | some sh =>
      rw [he] at h hres
      simp only [eintritt, hr2] at hres
      obtain ⟨w, hw2, hws⟩ := hres
      cases hw2
      rcases hws with hws | ⟨r, _, rfl⟩
      · exact WFU_binde h hl hws
      · exact absurd rfl (hnr r)


set_option linter.unusedSectionVars false in
theorem pruefe_sicher_assign (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (c)
    (i)
    (f)
    (e)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.assign c i f e : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    : Ergebnis P Γ erg Δ Δ' (step ρ (.assign c i f e : Stmt) s) ∨ LogikS ρ (.assign c i f e : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i lo hi sh hi' he
    split at h
    · rename_i hc; cases h
      obtain ⟨hlo, hhi, hp⟩ := hc
      obtain ⟨vi, hvi, hvis⟩ := schluss_sicher' hD hw hl hi'
      obtain ⟨k, rfl, hk0, hk1⟩ := Value.hasShape_intIn_true vi lo hi hvis
      obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl he
      left
      simp only [step, hvi, hv, Ergebnis]
      exact ⟨Welt_store_slot hD hw c k f v sh (by omega) (by omega) hvs hp, hl⟩
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_assignField (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (c)
    (f)
    (e)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.assignField c f e : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    : Ergebnis P Γ erg Δ Δ' (step ρ (.assignField c f e : Stmt) s) ∨ LogikS ρ (.assignField c f e : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i sh he
    split at h
    · rename_i hp; cases h
      obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl he
      left
      simp only [step, hv, Ergebnis]
      exact ⟨Welt_store_field hD hw c f v sh hvs hp, hl⟩
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_assignGlobal (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (g)
    (e)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.assignGlobal g e : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    : Ergebnis P Γ erg Δ Δ' (step ρ (.assignGlobal g e : Stmt) s) ∨ LogikS ρ (.assignGlobal g e : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i sh he
    split at h
    · rename_i hp; cases h
      obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl he
      left
      simp only [step, hv, Ergebnis]
      exact ⟨Welt_store_global hD hw g v sh hvs hp, hl⟩
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_bindName (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (n)
    (e)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.bindName n e : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    : Ergebnis P Γ erg Δ Δ' (step ρ (.bindName n e : Stmt) s) ∨ LogikS ρ (.bindName n e : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i sh he
    obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl he
    left
    simp only [step, hv, Ergebnis]
    exact ⟨hw, WFU_binde h hl hvs⟩
  · cases h

end Gabbro.Sicherheit
