module

public import Gabbro.Sicherheit.Ausdruck
public import Gabbro.Sicherheit.Anweisung.Teil4

@[expose] public section

namespace Gabbro.Sicherheit
open Gabbro.Body

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_ite (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (c)
    (t)
    (e)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.ite c t e : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    (ih_pruefeBlock_sicher_e : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape), ∀ (Δ : Umgebung), ∀ (Δ' : Umgebung), ∀ (s : State), pruefeBlock P erg Δ e = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (exec ρ e s) ∨ LogikB ρ e s)
    (ih_pruefeBlock_sicher_t : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape), ∀ (Δ : Umgebung), ∀ (Δ' : Umgebung), ∀ (s : State), pruefeBlock P erg Δ t = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (exec ρ t s) ∨ LogikB ρ t s)
    : Ergebnis P Γ erg Δ Δ' (step ρ (.ite c t e : Stmt) s) ∨ LogikS ρ (.ite c t e : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i Δt Δe hc ht he; cases h
    obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl hc
    obtain ⟨b, rfl⟩ := Value.hasShape_bool_true v hvs
    cases b
    · simp only [step, hv]
      have hlE : WFU (verfeinere Δ c false) s.local' := by simpa [verfeinere] using hl
      rcases ih_pruefeBlock_sicher_e P Γ ρ hD hU hS erg (verfeinere Δ c false) Δe s he hw hlE with hr | hlog
      · left
        by_cases heq : Δt = Δe
        · have h1 : erweitert Δt Δe := by rw [heq]; exact erweitert_refl _
          simp only [vereinige]
          rw [if_pos heq]
          exact Ergebnis_schwaecher (verfeinere_erweitert Δ c false) h1 hr
        · simp only [vereinige]
          rw [if_neg heq]
          exact Ergebnis_schwaecher (verfeinere_erweitert Δ c false)
            (erweitert_trans (verfeinere_erweitert Δ c false) (pruefeBlock_erweitert P erg e _ _ he)) hr
      · right; exact LogikS.sonst hv hlog
    · simp only [step, hv]
      have hlT : WFU (verfeinere Δ c true) s.local' := by simpa [verfeinere] using hl
      rcases ih_pruefeBlock_sicher_t P Γ ρ hD hU hS erg (verfeinere Δ c true) Δt s ht hw hlT with hr | hlog
      · left
        by_cases heq : Δt = Δe
        · have h1 : erweitert Δt Δt := erweitert_refl _
          simp only [vereinige]
          rw [if_pos heq]
          exact Ergebnis_schwaecher (verfeinere_erweitert Δ c true) h1 hr
        · simp only [vereinige]
          rw [if_neg heq]
          exact Ergebnis_schwaecher (verfeinere_erweitert Δ c true)
            (erweitert_trans (verfeinere_erweitert Δ c true) (pruefeBlock_erweitert P erg t _ _ ht)) hr
      · right; exact LogikS.dann hv hlog
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_onOption (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (g)
    (bn)
    (onP)
    (onA)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.onOption g bn onP onA : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    (ih_pruefeBlock_sicher_onA : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape), ∀ (Δ : Umgebung), ∀ (Δ' : Umgebung), ∀ (s : State), pruefeBlock P erg Δ onA = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (exec ρ onA s) ∨ LogikB ρ onA s)
    (ih_pruefeBlock_sicher_onP : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape), ∀ (Δ : Umgebung), ∀ (Δ' : Umgebung), ∀ (s : State), pruefeBlock P erg Δ onP = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (exec ρ onP s) ∨ LogikB ρ onP s)
    : Ergebnis P Γ erg Δ Δ' (step ρ (.onOption g bn onP onA : Stmt) s) ∨ LogikS ρ (.onOption g bn onP onA : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i ΔP hg hb
    split at h
    · rename_i ΔP' ΔA hP hA; cases h
      obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl hg
      rcases Value.hasShape_opt_true v hvs with rfl | ⟨k, rfl⟩
      · simp only [step, hv]
        rcases ih_pruefeBlock_sicher_onA P Γ ρ hD hU hS erg Δ ΔA s hA hw hl with hr | hlog
        · left; exact Ergebnis_schwaecher (erweitert_refl _) (pruefeBlock_erweitert P erg onA Δ ΔA hA) hr
        · right; exact LogikS.abwesend hv hlog
      · simp only [step, hv]
        have hl' : WFU ΔP (bindLocal s.local' bn (.int k)) :=
          WFU_binde hb hl (by simp only [Ge.haelt, Value.hasShape])
        rcases ih_pruefeBlock_sicher_onP P Γ ρ hD hU hS erg ΔP ΔP'
            ⟨s.world, bindLocal s.local' bn (.int k)⟩ hP hw hl' with hr | hlog
        · left
          exact Ergebnis_schwaecher (binde_erweitert hb)
            (erweitert_trans (binde_erweitert hb) (pruefeBlock_erweitert P erg onP ΔP ΔP' hP)) hr
        · right; exact LogikS.vorhanden hv hlog
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_call (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (f)
    (ps)
    (as)
    (pre)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.call f ps as pre : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    : Ergebnis P Γ erg Δ Δ' (step ρ (.call f ps as pre : Stmt) s) ∨ LogikS ρ (.call f ps as pre : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i S hr
    split at h
    · rename_i hg; cases h
      obtain ⟨vs, hvs, b, hb⟩ := ruf_eintritt hD hw hl hr
      obtain ⟨hsig, _⟩ := rufPasst_eq hr
      cases b
      · right; exact LogikS.ruf hvs (by rw [hb]; simp only [ne_eq, Option.some.injEq, Value.bool.injEq, Bool.false_eq_true, not_false_eq_true])
      · left
        simp only [step, hvs, eintritt] at hb ⊢
        simp only [hb, Ergebnis]
        exact ⟨(antwort_ohne_kanal hU hsig hg (t := eintritt s ps vs) hw).1, hl⟩
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_bindCall (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (n)
    (f)
    (ps)
    (as)
    (pre)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.bindCall n f ps as pre : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    : Ergebnis P Γ erg Δ Δ' (step ρ (.bindCall n f ps as pre : Stmt) s) ∨ LogikS ρ (.bindCall n f ps as pre : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i S hr
    split at h
    · rename_i sh he
      split at h
      · rename_i hg
        obtain ⟨vs, hvs, b, hb⟩ := ruf_eintritt hD hw hl hr
        obtain ⟨hsig, _⟩ := rufPasst_eq hr
        cases b
        · right; exact LogikS.rufGebunden hvs (by rw [hb]; simp only [ne_eq, Option.some.injEq, Value.bool.injEq, Bool.false_eq_true, not_false_eq_true])
        · left
          obtain ⟨hw', ha⟩ := antwort_ohne_kanal hU hsig hg (t := eintritt s ps vs) hw
          rw [he] at ha
          simp only [step, hvs, eintritt] at hb ⊢
          simp only [hb]
          cases hres : (ρ f { world := s.world, local' := bindAll ps vs fun _ => Value.absent }).2 with
          | none => simp only [eintritt, hres, AntwortPasst] at ha
          | some v =>
              simp only [eintritt, hres, AntwortPasst] at ha
              rcases ha with ha | ⟨r, hr, _⟩
              · simp only [Ergebnis]
                exact ⟨hw', WFU_binde h hl ha⟩
              · simp only [List.not_mem_nil] at hr
      · cases h
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_bindCallElse (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (n)
    (f)
    (ps)
    (as)
    (pre)
    (err)
    (onErr)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.bindCallElse n f ps as pre err onErr : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    (ih_pruefeBlock_sicher_onErr : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape), ∀ (Δ : Umgebung), ∀ (Δ' : Umgebung), ∀ (s : State), pruefeBlock P erg Δ onErr = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (exec ρ onErr s) ∨ LogikB ρ onErr s)
    : Ergebnis P Γ erg Δ Δ' (step ρ (.bindCallElse n f ps as pre err onErr : Stmt) s) ∨ LogikS ρ (.bindCallElse n f ps as pre err onErr : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i S hr
    split at h
    · cases h
    · rename_i hg
      split at h
      · cases h
      · rename_i hEnd'
        have hEnd : endetMitAusgang P.sig onErr = true := by simpa using hEnd'
        split at h
        · rename_i ΔE hE
          split at h
          · rename_i ΔE' hErr
            obtain ⟨vs, hvs, b, hb⟩ := ruf_eintritt hD hw hl hr
            obtain ⟨hsig, _⟩ := rufPasst_eq hr
            cases b
            · right; exact LogikS.rufSonst hvs (by rw [hb]; simp only [ne_eq, Option.some.injEq, Value.bool.injEq, Bool.false_eq_true, not_false_eq_true])
            · obtain ⟨hw', hres, hdivP⟩ := hU f S hsig (eintritt s ps vs) hw
              simp only [step, hvs, eintritt] at hb ⊢
              simp only [hb]
              -- Drei Antworten: ein Grund, ein Wert, keine.
              cases hr2 : (ρ f { world := s.world, local' := bindAll ps vs fun _ => Value.absent }).2 with
              | none =>
                  simp only
                  split at h
                  · rename_i sh he
                    -- Signatur verspricht einen Wert; (U1) widerspricht `none`.
                    rw [he] at hres; simp only [eintritt, hr2] at hres
                    obtain ⟨v, hv, _⟩ := hres; cases hv
                  · rename_i he
                    left
                    simp only [Ergebnis]
                    exact ⟨hw', WFU_binde h hl (by simp only [Ge.haelt, Value.hasShape])⟩
              | some v =>
                  cases v with
                  | reason x =>
                      simp only
                      have hx : x ∈ S.gruende := by
                        cases he : S.ergebnis with
                        | none =>
                            rw [he] at hres; simp only [eintritt, hr2] at hres
                            rcases hres with hres | ⟨r, hr', hr''⟩
                            · cases hres
                            · cases hr''; exact hr'
                        | some sh =>
                            rw [he] at hres; simp only [eintritt, hr2] at hres
                            obtain ⟨w, hw2, hws⟩ := hres
                            cases hw2
                            rcases hws with hws | ⟨r, hr', hr''⟩
                            · cases sh <;> simp only [Value.hasShape, Bool.false_eq_true] at hws
                            · cases hr''; exact hr'
                      have hlE : WFU ΔE (bindLocal s.local' err (.reason x)) :=
                        WFU_binde hE hl ⟨x, hx, rfl⟩
                      rcases ih_pruefeBlock_sicher_onErr P Γ ρ hD hU hS erg ΔE ΔE'
                          ⟨(ρ f { world := s.world, local' := bindAll ps vs fun _ => Value.absent }).1.world,
                           bindLocal s.local' err (.reason x)⟩ hErr hw' hlE with hr3 | hlog
                      · left
                        exact Ergebnis_ausgang (binde_erweitert hE)
                          (fun s' => endet_nicht_running ρ P.sig hdivP onErr _ s' hEnd) hr3
                      · right; exact LogikS.fehlerzweig hvs hr2 hlog
                  | int k => exact bindCallElse_wert h hres hr2 (by simp only [ne_eq, reduceCtorEq, not_false_eq_true, implies_true]) hw' hl
                  | bool t => exact bindCallElse_wert h hres hr2 (by simp only [ne_eq, reduceCtorEq, not_false_eq_true, implies_true]) hw' hl
                  | absent => exact bindCallElse_wert h hres hr2 (by simp only [ne_eq, reduceCtorEq, not_false_eq_true, implies_true]) hw' hl
                  | present k => exact bindCallElse_wert h hres hr2 (by simp only [ne_eq, reduceCtorEq, not_false_eq_true, implies_true]) hw' hl
                  | tagged t q => exact bindCallElse_wert h hres hr2 (by simp only [ne_eq, reduceCtorEq, not_false_eq_true, implies_true]) hw' hl
                  | record vs => exact bindCallElse_wert h hres hr2 (by simp only [ne_eq, reduceCtorEq, not_false_eq_true, implies_true]) hw' hl
          · cases h
        · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_onReason (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (g)
    (arms)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.onReason (.name g) arms : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    (ih_pruefeArme_sicher_arms : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape) (Δ : Umgebung), ∀ (Δ' : Umgebung), ∀ (x : String), ∀ (s : State), pruefeArme P erg Δ arms = some Δ' → arms.any (fun a => a.1 == x) = true → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (pickArm ρ arms x s) ∨ LogikA ρ arms x s)
    : Ergebnis P Γ erg Δ Δ' (step ρ (.onReason (.name g) arms : Stmt) s) ∨ LogikS ρ (.onReason (.name g) arms : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i cs hg
    split at h
    · rename_i hall
      obtain ⟨r, hr, hgr⟩ := hl g _ hg
      simp only [step, eval, hgr]
      rcases ih_pruefeArme_sicher_arms P Γ ρ hD hU hS erg Δ Δ' r s h
          (grund_hat_arm arms cs r hall hr) hw hl with hres | hlog
      · left; exact hres
      · right; exact LogikS.grundArm (by simp only [eval, hgr]) hlog
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_onTag (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (g)
    (arms)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.onTag g arms : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    (ih_pruefeTags_sicher_arms : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape) (Δ : Umgebung) (cs : List (String × Option (Option (Int × Int)))), ∀ (Δ' : Umgebung), ∀ (x : String), ∀ (p : Option Int), ∀ (s : State), pruefeTags P erg Δ cs arms = some Δ' → namenEindeutig cs = true → arms.any (fun a => a.1 == x) = true → Shape.caseOk cs x p = true → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (pickTag ρ arms x p s) ∨ LogikT ρ arms x p s)
    : Ergebnis P Γ erg Δ Δ' (step ρ (.onTag g arms : Stmt) s) ∨ LogikS ρ (.onTag g arms : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i cs hg
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl hg
      obtain ⟨x, p, rfl, hok⟩ := Value.hasShape_sum_true v cs hvs
      obtain ⟨pl, hpl, hpok⟩ := fall_gefunden cs x p hc.1 hok
      simp only [step, hv]
      rcases ih_pruefeTags_sicher_arms P Γ ρ hD hU hS erg Δ cs Δ' x p s h hc.1
          (fall_hat_arm arms cs x pl hc.2 hpl) hok hw hl with hres | hlog
      · left; exact hres
      · right; exact LogikS.fallArm hv hlog
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_retCall (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (f)
    (ps)
    (as)
    (pre)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.retCall f ps as pre : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    : Ergebnis P Γ erg Δ Δ' (step ρ (.retCall f ps as pre : Stmt) s) ∨ LogikS ρ (.retCall f ps as pre : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i S hr
    split at h
    · rename_i hc; cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨vs, hvs, b, hb⟩ := ruf_eintritt hD hw hl hr
      obtain ⟨hsig, _⟩ := rufPasst_eq hr
      cases b
      · right; exact LogikS.rufZurueck hvs (by rw [hb]; simp only [ne_eq, Option.some.injEq, Value.bool.injEq, Bool.false_eq_true, not_false_eq_true])
      · left
        obtain ⟨hw', ha⟩ := antwort_mit_kanal hU hsig (t := eintritt s ps vs) hw hc.2 hc.1
        simp only [step, hvs, eintritt] at hb ⊢
        simp only [hb, Ergebnis]
        exact ⟨hw', hl, ha⟩
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_loop (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (id)
    (inv)
    (body)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.loop id inv body : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    : Ergebnis P Γ erg Δ Δ' (step ρ (.loop id inv body : Stmt) s) ∨ LogikS ρ (.loop id inv body : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i ΔS hreg hinv
    split at h
    · rename_i heq; subst heq
      split at h
      · cases h
        obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl hinv
        obtain ⟨b, rfl⟩ := Value.hasShape_bool_true v hvs
        cases b
        · right; exact LogikS.invariante (by rw [hv]; simp only [ne_eq, Option.some.injEq, Value.bool.injEq, Bool.false_eq_true, not_false_eq_true])
        · left
          simp only [step, hv, Ergebnis]
          exact hS id _ hreg s hw hl
      · cases h
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_locked (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (l)
    (b)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.locked l b : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    (ih_pruefeBlock_sicher_b : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape), ∀ (Δ : Umgebung), ∀ (Δ' : Umgebung), ∀ (s : State), pruefeBlock P erg Δ b = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (exec ρ b s) ∨ LogikB ρ b s)
    : Ergebnis P Γ erg Δ Δ' (step ρ (.locked l b : Stmt) s) ∨ LogikS ρ (.locked l b : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i Δb hb; cases h
    simp only [step]
    rcases ih_pruefeBlock_sicher_b P Γ ρ hD hU hS erg Δ Δb s hb hw hl with hr | hlog
    · left; exact Ergebnis_schwaecher (erweitert_refl _) (pruefeBlock_erweitert P erg b Δ Δb hb) hr
    · right; exact LogikS.gesperrt hlog
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_breaking (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (i)
    (b)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.breaking i b : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    (ih_pruefeBlock_sicher_b : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape), ∀ (Δ : Umgebung), ∀ (Δ' : Umgebung), ∀ (s : State), pruefeBlock P erg Δ b = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (exec ρ b s) ∨ LogikB ρ b s)
    : Ergebnis P Γ erg Δ Δ' (step ρ (.breaking i b : Stmt) s) ∨ LogikS ρ (.breaking i b : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i Δb hb; cases h
    simp only [step]
    rcases ih_pruefeBlock_sicher_b P Γ ρ hD hU hS erg Δ Δb s hb hw hl with hr | hlog
    · left; exact Ergebnis_schwaecher (erweitert_refl _) (pruefeBlock_erweitert P erg b Δ Δb hb) hr
    · right; exact LogikS.ausgesetzt hlog
  · cases h

end Gabbro.Sicherheit
