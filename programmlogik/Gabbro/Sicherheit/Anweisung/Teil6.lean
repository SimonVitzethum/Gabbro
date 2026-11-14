module

public import Gabbro.Sicherheit.Ausdruck
public import Gabbro.Sicherheit.Anweisung.Teil5

@[expose] public section

namespace Gabbro.Sicherheit
open Gabbro.Body

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_publish (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (a)
    (e)
    (pl)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.publish a e pl : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    : Ergebnis P Γ erg Δ Δ' (step ρ (.publish a e pl : Stmt) s) ∨ LogikS ρ (.publish a e pl : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i sh he
    split at h
    · rename_i hp; cases h
      obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl he
      left
      simp only [step, hv, Ergebnis]
      exact ⟨Welt_store_global hD hw a v sh hvs hp, hl⟩
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_awaitLoad (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (n)
    (a)
    (pl)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.awaitLoad n a pl : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    : Ergebnis P Γ erg Δ Δ' (step ρ (.awaitLoad n a pl : Stmt) s) ∨ LogikS ρ (.awaitLoad n a pl : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i sh ha
    left
    simp only [step, Ergebnis]
    refine ⟨hw, WFU_binde h hl ?_⟩
    show Value.hasShape _ _ = true
    apply hw.1 (.global a) sh
    rw [hD.2.2 a]; exact ha
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_sicher_exchangeWith (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (n)
    (a)
    (e)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefe P erg Δ (.exchangeWith n a e : Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    : Ergebnis P Γ erg Δ Δ' (step ρ (.exchangeWith n a e : Stmt) s) ∨ LogikS ρ (.exchangeWith n a e : Stmt) s :=
  by
  simp only [pruefe] at h
  split at h
  · rename_i sh za he ha
    split at h
    · rename_i hp
      obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl he
      left
      simp only [step, hv, Ergebnis]
      refine ⟨Welt_store_global hD hw a v sh hvs (by unfold passtIn; rw [ha]; exact hp),
              WFU_binde h hl ?_⟩
      show Value.hasShape _ _ = true
      apply hw.1 (.global a) za
      rw [hD.2.2 a]; exact ha
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefeBlock_sicher_a (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (a)
    (rest)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (s : State)
    (h : pruefeBlock P erg Δ (a :: rest : List Stmt) = some Δ')
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    (ih_pruefe_sicher_a : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape), ∀ (Δ : Umgebung), ∀ (Δ' : Umgebung), ∀ (s : State), pruefe P erg Δ a = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (step ρ a s) ∨ LogikS ρ a s)
    (ih_pruefeBlock_sicher_rest : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape), ∀ (Δ : Umgebung), ∀ (Δ' : Umgebung), ∀ (s : State), pruefeBlock P erg Δ rest = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (exec ρ rest s) ∨ LogikB ρ rest s)
    : Ergebnis P Γ erg Δ Δ' (exec ρ (a :: rest : List Stmt) s) ∨ LogikB ρ (a :: rest : List Stmt) s :=
  by
  simp only [pruefeBlock] at h
  split at h
  · rename_i Δ1 h1
    rcases ih_pruefe_sicher_a P Γ ρ hD hU hS erg Δ Δ1 s h1 hw hl with hr | hlog
    · simp only [exec]
      cases ho : step ρ a s with
      | running s' =>
          rw [ho] at hr; simp only [Ergebnis] at hr
          rcases ih_pruefeBlock_sicher_rest P Γ ρ hD hU hS erg Δ1 Δ' s' h hr.1 hr.2 with hr2 | hlog2
          · left; exact Ergebnis_schwaecher (pruefe_erweitert P erg a Δ Δ1 h1) (erweitert_refl _) hr2
          · right; exact LogikB.widen ho hlog2
      | returned s' v => rw [ho] at hr; left; exact hr
      | exited s' => rw [ho] at hr; left; exact hr
      | left s' => rw [ho] at hr; left; exact hr
      | stuck => rw [ho] at hr; exact hr.elim
    · right; exact LogikB.kopf hlog
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefeArme_sicher_arm (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape) (Δ : Umgebung)
    (n)
    (b)
    (rest)
    (Δ' : Umgebung)
    (x : String)
    (s : State)
    (h : pruefeArme P erg Δ ((n, b) :: rest : List (String × List Stmt)) = some Δ')
    (hx : ((n, b) :: rest : List (String × List Stmt)).any (fun a => a.1 == x) = true)
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    (ih_pruefeBlock_sicher_b : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape), ∀ (Δ : Umgebung), ∀ (Δ' : Umgebung), ∀ (s : State), pruefeBlock P erg Δ b = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (exec ρ b s) ∨ LogikB ρ b s)
    (ih_pruefeArme_sicher_rest : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape) (Δ : Umgebung), ∀ (Δ' : Umgebung), ∀ (x : String), ∀ (s : State), pruefeArme P erg Δ rest = some Δ' → rest.any (fun a => a.1 == x) = true → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (pickArm ρ rest x s) ∨ LogikA ρ rest x s)
    : Ergebnis P Γ erg Δ Δ' (pickArm ρ ((n, b) :: rest : List (String × List Stmt)) x s) ∨ LogikA ρ ((n, b) :: rest : List (String × List Stmt)) x s :=
  by
  simp only [pruefeArme] at h
  split at h
  · rename_i Δb hb
    simp only [pickArm]
    by_cases hnx : n = x
    · subst hnx
      simp only [↓reduceIte]
      rw [pruefeArme_gibt_Δ P erg Δ rest Δ' h]
      rcases ih_pruefeBlock_sicher_b P Γ ρ hD hU hS erg Δ Δb s hb hw hl with hr | hlog
      · left
        exact Ergebnis_schwaecher (erweitert_refl _) (pruefeBlock_erweitert P erg b Δ Δb hb) hr
      · right; exact LogikA.here rfl hlog
    · simp only [hnx, ↓reduceIte]
      have hx' : rest.any (fun a => a.1 == x) = true := by
        simp only [List.any_cons, Bool.or_eq_true, beq_iff_eq] at hx
        rcases hx with hx | hx
        · exact absurd hx hnx
        · exact hx
      rcases ih_pruefeArme_sicher_rest P Γ ρ hD hU hS erg Δ Δ' x s h hx' hw hl with hr | hlog
      · left; exact hr
      · right; exact LogikA.there hnx hlog
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefeTags_sicher_arm (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape) (Δ : Umgebung) (cs : List (String × Option (Option (Int × Int))))
    (t)
    (bd)
    (b)
    (rest)
    (Δ' : Umgebung)
    (x : String)
    (p : Option Int)
    (s : State)
    (h : pruefeTags P erg Δ cs ((t, bd, b) :: rest : List (String × Option String × List Stmt)) = some Δ')
    (hu : namenEindeutig cs = true)
    (hx : ((t, bd, b) :: rest : List (String × Option String × List Stmt)).any (fun a => a.1 == x) = true)
    (hok : Shape.caseOk cs x p = true)
    (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local')
    (ih_pruefeBlock_sicher_b : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape), ∀ (Δ : Umgebung), ∀ (Δ' : Umgebung), ∀ (s : State), pruefeBlock P erg Δ b = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (exec ρ b s) ∨ LogikB ρ b s)
    (ih_pruefeTags_sicher_rest : ∀ (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape) (Δ : Umgebung) (cs : List (String × Option (Option (Int × Int)))), ∀ (Δ' : Umgebung), ∀ (x : String), ∀ (p : Option Int), ∀ (s : State), pruefeTags P erg Δ cs rest = some Δ' → namenEindeutig cs = true → rest.any (fun a => a.1 == x) = true → Shape.caseOk cs x p = true → Welt P.D Γ s.world → WFU Δ s.local' → Ergebnis P Γ erg Δ Δ' (pickTag ρ rest x p s) ∨ LogikT ρ rest x p s)
    : Ergebnis P Γ erg Δ Δ' (pickTag ρ ((t, bd, b) :: rest : List (String × Option String × List Stmt)) x p s) ∨ LogikT ρ ((t, bd, b) :: rest : List (String × Option String × List Stmt)) x p s :=
  by
  simp only [pruefeTags] at h
  split at h
  · rename_i pl hpl
    by_cases htx : t = x
    · subst htx
      obtain ⟨pl', hpl', hpok⟩ := fall_gefunden cs t p hu hok
      rw [hpl] at hpl'; cases hpl'
      simp only [pickTag, ↓reduceIte]
      split at h
      · -- eine Nutzlast: der Arm muss binden
        rename_i sh hsh
        split at h
        · rename_i v
          split at h
          · rename_i Δv hv
            split at h
            · rename_i Δb hb
              rw [pruefeTags_gibt_Δ P erg Δ cs rest Δ' h]
              obtain ⟨k, rfl⟩ : ∃ k, p = some k := by
                cases pl with
                | none => simp only [nutzlastGestalt, reduceCtorEq] at hsh
                | some q => cases p with
                  | none => cases q with
                    | none => simp only [Shape.payloadOk_some_none_none, Bool.false_eq_true] at hpok
                    | some r => obtain ⟨lo, hi⟩ := r; simp only [Shape.payloadOk_range_none, Bool.false_eq_true] at hpok
                  | some k => exact ⟨k, rfl⟩
              simp only
              have hk : (Value.int k).hasShape sh = true := by
                cases pl with
                | none => simp only [nutzlastGestalt, reduceCtorEq] at hsh
                | some q => cases q with
                  | none => simp only [nutzlastGestalt, Option.some.injEq] at hsh; subst hsh; simp only [Value.hasShape]
                  | some r =>
                      obtain ⟨lo, hi⟩ := r
                      simp only [nutzlastGestalt, Option.some.injEq] at hsh; subst hsh
                      simp only [Shape.payloadOk_range_some, decide_eq_true_eq] at hpok
                      simp only [Value.hasShape, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq]; omega
              have hl' : WFU Δv (bindLocal s.local' v (.int k)) := WFU_binde hv hl hk
              rcases ih_pruefeBlock_sicher_b P Γ ρ hD hU hS erg Δv Δb
                  ⟨s.world, bindLocal s.local' v (.int k)⟩ hb hw hl' with hr | hlog
              · left
                exact Ergebnis_schwaecher (binde_erweitert hv)
                  (erweitert_trans (binde_erweitert hv) (pruefeBlock_erweitert P erg b Δv Δb hb)) hr
              · right; exact LogikT.hierMit rfl hlog
            · cases h
          · cases h
        · cases h
      · -- keine Nutzlast: der Arm bindet nicht
        rename_i hsh
        split at h
        · split at h
          · rename_i Δb hb
            rw [pruefeTags_gibt_Δ P erg Δ cs rest Δ' h]
            have hp : p = none := by
              cases pl with
              | none => simpa using hpok
              | some q => cases q with
                | none => simp only [nutzlastGestalt, reduceCtorEq] at hsh
                | some r => obtain ⟨lo, hi⟩ := r; simp only [nutzlastGestalt, reduceCtorEq] at hsh
            subst hp
            simp only
            rcases ih_pruefeBlock_sicher_b P Γ ρ hD hU hS erg Δ Δb s hb hw hl with hr | hlog
            · left
              exact Ergebnis_schwaecher (erweitert_refl _) (pruefeBlock_erweitert P erg b Δ Δb hb) hr
            · right; exact LogikT.hierOhne rfl hlog
          · cases h
        · cases h
    · simp only [pickTag, htx, ↓reduceIte]
      have hx' : rest.any (fun a => a.1 == x) = true := by
        simp only [List.any_cons, Bool.or_eq_true, beq_iff_eq] at hx
        rcases hx with hx | hx
        · exact absurd hx htx
        · exact hx
      have hrest : pruefeTags P erg Δ cs rest = some Δ' := by
        split at h
        · split at h
          · split at h
            · split at h
              · exact h
              · cases h
            · cases h
          · cases h
        · split at h
          · split at h
            · exact h
            · cases h
          · cases h
      rcases ih_pruefeTags_sicher_rest P Γ ρ hD hU hS erg Δ cs Δ' x p s hrest hu hx' hok hw hl with hr | hlog
      · left; exact hr
      · right; exact LogikT.there htx hlog
  · cases h

mutual

/-- **Der Sicherheitssatz fuer eine Anweisung.** Nimmt der Pruefer sie an, so ist nach dem
    Schritt die Welt wohlgeformt und der Sichtbereich gehalten -- ODER der Schritt steht an
    einer `Logik`-Stelle. `stuck` ohne `Logik` gibt es nicht. -/
theorem pruefe_sicher (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ)
    (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape) :
    ∀ (st : Stmt) (Δ Δ' : Umgebung) (s : State),
      pruefe P erg Δ st = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' →
      Ergebnis P Γ erg Δ Δ' (step ρ st s) ∨ LogikS ρ st s
  | .assign c i f e, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_assign (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (c := c) (i := i) (f := f) (e := e) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl)
  | .assignField c f e, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_assignField (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (c := c) (f := f) (e := e) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl)
  | .assignGlobal g e, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_assignGlobal (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (g := g) (e := e) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl)
  | .bindName n e, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_bindName (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (n := n) (e := e) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl)
  | .ite c t e, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_ite (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (c := c) (t := t) (e := e) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl) (ih_pruefeBlock_sicher_e := fun P Γ ρ hD hU hS erg => pruefeBlock_sicher P Γ ρ hD hU hS erg e) (ih_pruefeBlock_sicher_t := fun P Γ ρ hD hU hS erg => pruefeBlock_sicher P Γ ρ hD hU hS erg t)
  | .onOption g bn onP onA, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_onOption (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (g := g) (bn := bn) (onP := onP) (onA := onA) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl) (ih_pruefeBlock_sicher_onA := fun P Γ ρ hD hU hS erg => pruefeBlock_sicher P Γ ρ hD hU hS erg onA) (ih_pruefeBlock_sicher_onP := fun P Γ ρ hD hU hS erg => pruefeBlock_sicher P Γ ρ hD hU hS erg onP)
  | .call f ps as pre, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_call (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (f := f) (ps := ps) (as := as) (pre := pre) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl)
  | .bindCall n f ps as pre, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_bindCall (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (n := n) (f := f) (ps := ps) (as := as) (pre := pre) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl)
  | .bindCallElse n f ps as pre err onErr, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_bindCallElse (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (n := n) (f := f) (ps := ps) (as := as) (pre := pre) (err := err) (onErr := onErr) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl) (ih_pruefeBlock_sicher_onErr := fun P Γ ρ hD hU hS erg => pruefeBlock_sicher P Γ ρ hD hU hS erg onErr)
  | .onReason (.name g) arms, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_onReason (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (g := g) (arms := arms) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl) (ih_pruefeArme_sicher_arms := fun P Γ ρ hD hU hS erg Δ => pruefeArme_sicher P Γ ρ hD hU hS erg Δ arms)
  | .onReason (.lit _) _, Δ, Δ', s, h, hw, hl => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.global _) _, Δ, Δ', s, h, hw, hl => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.place _ _ _) _, Δ, Δ', s, h, hw, hl => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.un _ _) _, Δ, Δ', s, h, hw, hl => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.bin _ _ _) _, Δ, Δ', s, h, hw, hl => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.someOf _) _, Δ, Δ', s, h, hw, hl => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.fieldOf _ _) _, Δ, Δ', s, h, hw, hl => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.forallSlots _ _ _) _, Δ, Δ', s, h, hw, hl => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.existsSlots _ _ _) _, Δ, Δ', s, h, hw, hl => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.reaches _ _ _ _ _) _, Δ, Δ', s, h, hw, hl => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.chainFrom _ _ _ _ _) _, Δ, Δ', s, h, hw, hl => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.hasShape _ _) _, Δ, Δ', s, h, hw, hl => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.wrapTo _ _ _) _, Δ, Δ', s, h, hw, hl => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.tagOf _ _) _, Δ, Δ', s, h, hw, hl => by simp only [pruefe, reduceCtorEq] at h
  | .onTag g arms, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_onTag (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (g := g) (arms := arms) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl) (ih_pruefeTags_sicher_arms := fun P Γ ρ hD hU hS erg Δ cs => pruefeTags_sicher P Γ ρ hD hU hS erg Δ cs arms)
  | .retCall f ps as pre, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_retCall (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (f := f) (ps := ps) (as := as) (pre := pre) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl)
  | .loop id inv body, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_loop (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (id := id) (inv := inv) (body := body) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl)
  | .locked l b, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_locked (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (l := l) (b := b) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl) (ih_pruefeBlock_sicher_b := fun P Γ ρ hD hU hS erg => pruefeBlock_sicher P Γ ρ hD hU hS erg b)
  | .breaking i b, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_breaking (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (i := i) (b := b) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl) (ih_pruefeBlock_sicher_b := fun P Γ ρ hD hU hS erg => pruefeBlock_sicher P Γ ρ hD hU hS erg b)
  | .publish a e pl, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_publish (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (a := a) (e := e) (pl := pl) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl)
  | .awaitLoad n a pl, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_awaitLoad (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (n := n) (a := a) (pl := pl) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl)
  | .exchangeWith n a e, Δ, Δ', s, h, hw, hl =>
      pruefe_sicher_exchangeWith (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (n := n) (a := a) (e := e) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl)
  | .ret none, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i he; cases h; subst he
        left; simp only [step, Ergebnis]; exact ⟨hw, hl, trivial⟩
      · cases h
  | .ret (some e), Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i sh z he
        split at h
        · rename_i hp; cases h
          obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl he
          left
          simp only [step, hv, Ergebnis, AntwortPasst]
          exact ⟨hw, hl, Or.inl (passt_hasShape hp hvs)⟩
        · cases h
      · cases h
  | .exit, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h; cases h
      left; simp only [step, Ergebnis]; exact ⟨hw, hl⟩
  | .leave, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h; cases h
      left; simp only [step, Ergebnis]; exact ⟨hw, hl⟩
  | .forEach .., _, _, _, h, _, _ => by cases h
  | .retry .., _, _, _, h, _, _ => by cases h

theorem pruefeBlock_sicher (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ)
    (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape) :
    ∀ (b : List Stmt) (Δ Δ' : Umgebung) (s : State),
      pruefeBlock P erg Δ b = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' →
      Ergebnis P Γ erg Δ Δ' (exec ρ b s) ∨ LogikB ρ b s
  | [], Δ, Δ', s, h, hw, hl => by
      simp only [pruefeBlock] at h; cases h
      left; simp only [exec, Ergebnis]; exact ⟨hw, hl⟩
  | a :: rest, Δ, Δ', s, h, hw, hl =>
      pruefeBlock_sicher_a (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (a := a) (rest := rest) (Δ := Δ) (Δ' := Δ') (s := s) (h := h) (hw := hw) (hl := hl) (ih_pruefe_sicher_a := fun P Γ ρ hD hU hS erg => pruefe_sicher P Γ ρ hD hU hS erg a) (ih_pruefeBlock_sicher_rest := fun P Γ ρ hD hU hS erg => pruefeBlock_sicher P Γ ρ hD hU hS erg rest)
theorem pruefeArme_sicher (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ)
    (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape) (Δ : Umgebung) :
    ∀ (arms : List (String × List Stmt)) (Δ' : Umgebung) (x : String) (s : State),
      pruefeArme P erg Δ arms = some Δ' → arms.any (fun a => a.1 == x) = true →
      Welt P.D Γ s.world → WFU Δ s.local' →
      Ergebnis P Γ erg Δ Δ' (pickArm ρ arms x s) ∨ LogikA ρ arms x s
  | [], Δ', x, s, h, hx, hw, hl => by simp only [List.any_nil, Bool.false_eq_true] at hx
  | (n, b) :: rest, Δ', x, s, h, hx, hw, hl =>
      pruefeArme_sicher_arm (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (Δ := Δ) (n := n) (b := b) (rest := rest) (Δ' := Δ') (x := x) (s := s) (h := h) (hx := hx) (hw := hw) (hl := hl) (ih_pruefeBlock_sicher_b := fun P Γ ρ hD hU hS erg => pruefeBlock_sicher P Γ ρ hD hU hS erg b) (ih_pruefeArme_sicher_rest := fun P Γ ρ hD hU hS erg Δ => pruefeArme_sicher P Γ ρ hD hU hS erg Δ rest)
theorem pruefeTags_sicher (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ)
    (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape) (Δ : Umgebung)
    (cs : List (String × Option (Option (Int × Int)))) :
    ∀ (arms : List (String × Option String × List Stmt)) (Δ' : Umgebung) (x : String)
      (p : Option Int) (s : State),
      pruefeTags P erg Δ cs arms = some Δ' → namenEindeutig cs = true →
      arms.any (fun a => a.1 == x) = true → Shape.caseOk cs x p = true →
      Welt P.D Γ s.world → WFU Δ s.local' →
      Ergebnis P Γ erg Δ Δ' (pickTag ρ arms x p s) ∨ LogikT ρ arms x p s
  | [], Δ', x, p, s, h, hu, hx, hok, hw, hl => by simp only [List.any_nil, Bool.false_eq_true] at hx
  | (t, bd, b) :: rest, Δ', x, p, s, h, hu, hx, hok, hw, hl =>
      pruefeTags_sicher_arm (P := P) (Γ := Γ) (ρ := ρ) (hD := hD) (hU := hU) (hS := hS) (erg := erg) (Δ := Δ) (cs := cs) (t := t) (bd := bd) (b := b) (rest := rest) (Δ' := Δ') (x := x) (p := p) (s := s) (h := h) (hu := hu) (hx := hx) (hok := hok) (hw := hw) (hl := hl) (ih_pruefeBlock_sicher_b := fun P Γ ρ hD hU hS erg => pruefeBlock_sicher P Γ ρ hD hU hS erg b) (ih_pruefeTags_sicher_rest := fun P Γ ρ hD hU hS erg Δ cs => pruefeTags_sicher P Γ ρ hD hU hS erg Δ cs rest)
end

end Gabbro.Sicherheit
