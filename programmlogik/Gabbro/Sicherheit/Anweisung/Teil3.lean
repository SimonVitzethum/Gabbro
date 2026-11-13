module

public import Gabbro.Sicherheit.Ausdruck
public import Gabbro.Sicherheit.Anweisung.Teil2

@[expose] public section

namespace Gabbro.Sicherheit
open Gabbro.Body

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_assignGlobal (P : Programm) (erg : Option Shape)
    (g)
    (e)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.assignGlobal g e : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · split at h
    · cases h; exact erweitert_refl _
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_bindName (P : Programm) (erg : Option Shape)
    (n)
    (e)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.bindName n e : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · exact binde_erweitert h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_ite (P : Programm) (erg : Option Shape)
    (c)
    (t)
    (e)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.ite c t e : Stmt) = some Δ')
    (ih_pruefeBlock_erweitert_t : ∀ (P : Programm) (erg : Option Shape), ∀ (Δ : Umgebung), ∀ (Δ' : Umgebung), pruefeBlock P erg Δ t = some Δ' → erweitert Δ Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · rename_i Δt Δe hc ht he
    cases h
    simp only [vereinige]
    by_cases heq : Δt = Δe
    · rw [if_pos heq]
      exact erweitert_trans (verfeinere_erweitert Δ c true) (ih_pruefeBlock_erweitert_t P erg _ _ ht)
    · rw [if_neg heq]
      exact erweitert_refl _
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_onOption (P : Programm) (erg : Option Shape)
    (g)
    (bn)
    (onP)
    (onA)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.onOption g bn onP onA : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · split at h
    · cases h; exact erweitert_refl _
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_call (P : Programm) (erg : Option Shape)
    (f)
    (ps)
    (as)
    (pre)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.call f ps as pre : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · split at h
    · cases h; exact erweitert_refl _
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_bindCall (P : Programm) (erg : Option Shape)
    (n)
    (f)
    (ps)
    (as)
    (pre)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.bindCall n f ps as pre : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · split at h
    · split at h
      · exact binde_erweitert h
      · cases h
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_bindCallElse (P : Programm) (erg : Option Shape)
    (n)
    (f)
    (ps)
    (as)
    (pre)
    (err)
    (onErr)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.bindCallElse n f ps as pre err onErr : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · split at h
          · split at h
            · exact binde_erweitert h
            · exact binde_erweitert h
          · cases h
        · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_onReason (P : Programm) (erg : Option Shape)
    (g)
    (arms)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.onReason (.name g) arms : Stmt) = some Δ')
    (ih_pruefeArme_erweitert_arms : ∀ (P : Programm) (erg : Option Shape) (Δ : Umgebung), ∀ (Δ' : Umgebung), pruefeArme P erg Δ arms = some Δ' → erweitert Δ Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · split at h
    · exact ih_pruefeArme_erweitert_arms P erg Δ Δ' h
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_onTag (P : Programm) (erg : Option Shape)
    (g)
    (arms)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.onTag g arms : Stmt) = some Δ')
    (ih_pruefeTags_erweitert_arms : ∀ (P : Programm) (erg : Option Shape) (Δ : Umgebung) (cs : List (String × Option (Option (Int × Int)))), ∀ (Δ' : Umgebung), pruefeTags P erg Δ cs arms = some Δ' → erweitert Δ Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · split at h
    · exact ih_pruefeTags_erweitert_arms P erg Δ _ Δ' h
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_retCall (P : Programm) (erg : Option Shape)
    (f)
    (ps)
    (as)
    (pre)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.retCall f ps as pre : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · split at h
    · cases h; exact erweitert_refl _
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_loop (P : Programm) (erg : Option Shape)
    (id)
    (inv)
    (body)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.loop id inv body : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · split at h
    · split at h
      · cases h; exact erweitert_refl _
      · cases h
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_locked (P : Programm) (erg : Option Shape)
    (l)
    (b)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.locked l b : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · cases h; exact erweitert_refl _
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_breaking (P : Programm) (erg : Option Shape)
    (i)
    (b)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.breaking i b : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · cases h; exact erweitert_refl _
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_publish (P : Programm) (erg : Option Shape)
    (a)
    (e)
    (pl)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.publish a e pl : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · split at h
    · cases h; exact erweitert_refl _
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_awaitLoad (P : Programm) (erg : Option Shape)
    (n)
    (a)
    (pl)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.awaitLoad n a pl : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · exact binde_erweitert h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_exchangeWith (P : Programm) (erg : Option Shape)
    (n)
    (a)
    (e)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.exchangeWith n a e : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · split at h
    · exact binde_erweitert h
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefeBlock_erweitert_a (P : Programm) (erg : Option Shape)
    (a)
    (rest)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefeBlock P erg Δ (a :: rest : List Stmt) = some Δ')
    (ih_pruefe_erweitert_a : ∀ (P : Programm) (erg : Option Shape), ∀ (Δ : Umgebung), ∀ (Δ' : Umgebung), pruefe P erg Δ a = some Δ' → erweitert Δ Δ')
    (ih_pruefeBlock_erweitert_rest : ∀ (P : Programm) (erg : Option Shape), ∀ (Δ : Umgebung), ∀ (Δ' : Umgebung), pruefeBlock P erg Δ rest = some Δ' → erweitert Δ Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefeBlock] at h; split at h
  · rename_i Δ1 h1
    exact erweitert_trans (ih_pruefe_erweitert_a P erg Δ Δ1 h1)
      (ih_pruefeBlock_erweitert_rest P erg Δ1 Δ' h)
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefeArme_erweitert_arm (P : Programm) (erg : Option Shape) (Δ : Umgebung)
    (n)
    (b)
    (rest)
    (Δ' : Umgebung)
    (h : pruefeArme P erg Δ ((n, b) :: rest : List (String × List Stmt)) = some Δ')
    (ih_pruefeArme_erweitert_rest : ∀ (P : Programm) (erg : Option Shape) (Δ : Umgebung), ∀ (Δ' : Umgebung), pruefeArme P erg Δ rest = some Δ' → erweitert Δ Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefeArme] at h; split at h
  · exact ih_pruefeArme_erweitert_rest P erg Δ Δ' h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefeTags_erweitert_arm (P : Programm) (erg : Option Shape) (Δ : Umgebung) (cs : List (String × Option (Option (Int × Int))))
    (t)
    (bd)
    (b)
    (rest)
    (Δ' : Umgebung)
    (h : pruefeTags P erg Δ cs ((t, bd, b) :: rest : List (String × Option String × List Stmt)) = some Δ')
    (ih_pruefeTags_erweitert_rest : ∀ (P : Programm) (erg : Option Shape) (Δ : Umgebung) (cs : List (String × Option (Option (Int × Int)))), ∀ (Δ' : Umgebung), pruefeTags P erg Δ cs rest = some Δ' → erweitert Δ Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefeTags] at h; split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · exact ih_pruefeTags_erweitert_rest P erg Δ cs Δ' h
          · cases h
        · cases h
      · cases h
    · split at h
      · split at h
        · exact ih_pruefeTags_erweitert_rest P erg Δ cs Δ' h
        · cases h
      · cases h
  · cases h

mutual

theorem pruefe_erweitert (P : Programm) (erg : Option Shape) :
    ∀ (st : Stmt) (Δ Δ' : Umgebung), pruefe P erg Δ st = some Δ' → erweitert Δ Δ'
  | .assign c i f e, Δ, Δ', h =>
      pruefe_erweitert_assign (P := P) (erg := erg) (c := c) (i := i) (f := f) (e := e) (Δ := Δ) (Δ' := Δ') (h := h)
  | .assignField c f e, Δ, Δ', h =>
      pruefe_erweitert_assignField (P := P) (erg := erg) (c := c) (f := f) (e := e) (Δ := Δ) (Δ' := Δ') (h := h)
  | .assignGlobal g e, Δ, Δ', h =>
      pruefe_erweitert_assignGlobal (P := P) (erg := erg) (g := g) (e := e) (Δ := Δ) (Δ' := Δ') (h := h)
  | .bindName n e, Δ, Δ', h =>
      pruefe_erweitert_bindName (P := P) (erg := erg) (n := n) (e := e) (Δ := Δ) (Δ' := Δ') (h := h)
  | .ite c t e, Δ, Δ', h =>
      pruefe_erweitert_ite (P := P) (erg := erg) (c := c) (t := t) (e := e) (Δ := Δ) (Δ' := Δ') (h := h) (ih_pruefeBlock_erweitert_t := fun P erg => pruefeBlock_erweitert P erg t)
  | .onOption g bn onP onA, Δ, Δ', h =>
      pruefe_erweitert_onOption (P := P) (erg := erg) (g := g) (bn := bn) (onP := onP) (onA := onA) (Δ := Δ) (Δ' := Δ') (h := h)
  | .call f ps as pre, Δ, Δ', h =>
      pruefe_erweitert_call (P := P) (erg := erg) (f := f) (ps := ps) (as := as) (pre := pre) (Δ := Δ) (Δ' := Δ') (h := h)
  | .bindCall n f ps as pre, Δ, Δ', h =>
      pruefe_erweitert_bindCall (P := P) (erg := erg) (n := n) (f := f) (ps := ps) (as := as) (pre := pre) (Δ := Δ) (Δ' := Δ') (h := h)
  | .bindCallElse n f ps as pre err onErr, Δ, Δ', h =>
      pruefe_erweitert_bindCallElse (P := P) (erg := erg) (n := n) (f := f) (ps := ps) (as := as) (pre := pre) (err := err) (onErr := onErr) (Δ := Δ) (Δ' := Δ') (h := h)
  | .onReason (.name g) arms, Δ, Δ', h =>
      pruefe_erweitert_onReason (P := P) (erg := erg) (g := g) (arms := arms) (Δ := Δ) (Δ' := Δ') (h := h) (ih_pruefeArme_erweitert_arms := fun P erg Δ => pruefeArme_erweitert P erg Δ arms)
  | .onReason (.lit _) _, Δ, Δ', h => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.global _) _, Δ, Δ', h => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.place _ _ _) _, Δ, Δ', h => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.un _ _) _, Δ, Δ', h => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.bin _ _ _) _, Δ, Δ', h => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.someOf _) _, Δ, Δ', h => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.fieldOf _ _) _, Δ, Δ', h => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.forallSlots _ _ _) _, Δ, Δ', h => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.existsSlots _ _ _) _, Δ, Δ', h => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.reaches _ _ _ _ _) _, Δ, Δ', h => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.chainFrom _ _ _ _ _) _, Δ, Δ', h => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.hasShape _ _) _, Δ, Δ', h => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.wrapTo _ _ _) _, Δ, Δ', h => by simp only [pruefe, reduceCtorEq] at h
  | .onReason (.tagOf _ _) _, Δ, Δ', h => by simp only [pruefe, reduceCtorEq] at h
  | .onTag g arms, Δ, Δ', h =>
      pruefe_erweitert_onTag (P := P) (erg := erg) (g := g) (arms := arms) (Δ := Δ) (Δ' := Δ') (h := h) (ih_pruefeTags_erweitert_arms := fun P erg Δ cs => pruefeTags_erweitert P erg Δ cs arms)
  | .retCall f ps as pre, Δ, Δ', h =>
      pruefe_erweitert_retCall (P := P) (erg := erg) (f := f) (ps := ps) (as := as) (pre := pre) (Δ := Δ) (Δ' := Δ') (h := h)
  | .loop id inv body, Δ, Δ', h =>
      pruefe_erweitert_loop (P := P) (erg := erg) (id := id) (inv := inv) (body := body) (Δ := Δ) (Δ' := Δ') (h := h)
  | .locked l b, Δ, Δ', h =>
      pruefe_erweitert_locked (P := P) (erg := erg) (l := l) (b := b) (Δ := Δ) (Δ' := Δ') (h := h)
  | .breaking i b, Δ, Δ', h =>
      pruefe_erweitert_breaking (P := P) (erg := erg) (i := i) (b := b) (Δ := Δ) (Δ' := Δ') (h := h)
  | .publish a e pl, Δ, Δ', h =>
      pruefe_erweitert_publish (P := P) (erg := erg) (a := a) (e := e) (pl := pl) (Δ := Δ) (Δ' := Δ') (h := h)
  | .awaitLoad n a pl, Δ, Δ', h =>
      pruefe_erweitert_awaitLoad (P := P) (erg := erg) (n := n) (a := a) (pl := pl) (Δ := Δ) (Δ' := Δ') (h := h)
  | .exchangeWith n a e, Δ, Δ', h =>
      pruefe_erweitert_exchangeWith (P := P) (erg := erg) (n := n) (a := a) (e := e) (Δ := Δ) (Δ' := Δ') (h := h)
  | .ret none, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · cases h; exact erweitert_refl _
      · cases h
  | .ret (some e), Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · cases h; exact erweitert_refl _
        · cases h
      · cases h
  | .exit, Δ, Δ', h => by simp only [pruefe] at h; cases h; exact erweitert_refl _
  | .leave, Δ, Δ', h => by simp only [pruefe] at h; cases h; exact erweitert_refl _
  | .forEach .., _, _, h => by cases h
  | .retry .., _, _, h => by cases h

theorem pruefeBlock_erweitert (P : Programm) (erg : Option Shape) :
    ∀ (b : List Stmt) (Δ Δ' : Umgebung), pruefeBlock P erg Δ b = some Δ' → erweitert Δ Δ'
  | [], Δ, Δ', h => by simp only [pruefeBlock] at h; cases h; exact erweitert_refl _
  | a :: rest, Δ, Δ', h =>
      pruefeBlock_erweitert_a (P := P) (erg := erg) (a := a) (rest := rest) (Δ := Δ) (Δ' := Δ') (h := h) (ih_pruefe_erweitert_a := fun P erg => pruefe_erweitert P erg a) (ih_pruefeBlock_erweitert_rest := fun P erg => pruefeBlock_erweitert P erg rest)
theorem pruefeArme_erweitert (P : Programm) (erg : Option Shape) (Δ : Umgebung) :
    ∀ (arms : List (String × List Stmt)) (Δ' : Umgebung),
      pruefeArme P erg Δ arms = some Δ' → erweitert Δ Δ'
  | [], Δ', h => by simp only [pruefeArme] at h; cases h; exact erweitert_refl _
  | (n, b) :: rest, Δ', h =>
      pruefeArme_erweitert_arm (P := P) (erg := erg) (Δ := Δ) (n := n) (b := b) (rest := rest) (Δ' := Δ') (h := h) (ih_pruefeArme_erweitert_rest := fun P erg Δ => pruefeArme_erweitert P erg Δ rest)
theorem pruefeTags_erweitert (P : Programm) (erg : Option Shape) (Δ : Umgebung)
    (cs : List (String × Option (Option (Int × Int)))) :
    ∀ (arms : List (String × Option String × List Stmt)) (Δ' : Umgebung),
      pruefeTags P erg Δ cs arms = some Δ' → erweitert Δ Δ'
  | [], Δ', h => by simp only [pruefeTags] at h; cases h; exact erweitert_refl _
  | (t, bd, b) :: rest, Δ', h =>
      pruefeTags_erweitert_arm (P := P) (erg := erg) (Δ := Δ) (cs := cs) (t := t) (bd := bd) (b := b) (rest := rest) (Δ' := Δ') (h := h) (ih_pruefeTags_erweitert_rest := fun P erg Δ cs => pruefeTags_erweitert P erg Δ cs rest)
end


/-! ### 6.1 Was ein angenommener Ruf beim Eintritt hat -/

end Gabbro.Sicherheit
