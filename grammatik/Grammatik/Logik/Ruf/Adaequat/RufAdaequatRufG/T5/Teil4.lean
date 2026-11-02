module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5.Teil4Basis
import all Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5.Teil4Basis

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T4
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5.Teil3

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section SimOk
variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (stapel : List (RufRahmenG D)) (rho : Env D (D.params fn)) (s0 : World D)
  (A : D.Lock → Prop) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (C : D.Fn → Prop)
variable (hRuf : RufOk P O passes f A R C)
include hRuf

set_option linter.unusedSectionVars false in
theorem stmtAbbR_ite 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (t)
    (e)
    (hs : StmtR A C mr (.ite c t e : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockAbbR_t : ∀ {mr : Bool}, BlockR A C mr t → SimAbbBR P O passes f fn stapel rho s0 A R t)
    (ih_blockAbbR_e : ∀ {mr : Bool}, BlockR A C mr e → SimAbbBR P O passes f fn stapel rho s0 A R e)
    : SimAbbSR P O passes f fn stapel rho s0 A R (.ite c t e : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
  obtain ⟨ht, he⟩ := hs.ite_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  split at hex
  · rename_i hc
    obtain ⟨M1, hs1, hZ1⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ.1
      c t e rest k ρ rfl (by rw [hW]; exact hc)
    rw [hW] at hZ1
    obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := ih_blockAbbR_t ht hl _ _ _ _ _ _ hex M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ2
    exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · rename_i hc
    obtain ⟨M1, hs1, hZ1⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ.1
      c t e rest k ρ rfl (by rw [hW]; simpa using hc)
    rw [hW] at hZ1
    obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := ih_blockAbbR_e he hl _ _ _ _ _ _ hex M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ2
    exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩

set_option linter.unusedSectionVars false in
theorem stmtAbbR_onOption 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (o)
    (p)
    (a)
    (hs : StmtR A C mr (.onOption (n := zi_n) o p a : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockAbbR_p : ∀ {mr : Bool}, BlockR A C mr p → SimAbbBR P O passes f fn stapel rho s0 A R p)
    (ih_blockAbbR_a : ∀ {mr : Bool}, BlockR A C mr a → SimAbbBR P O passes f fn stapel rho s0 A R a)
    : SimAbbSR P O passes f fn stapel rho s0 A R (.onOption (n := zi_n) o p a : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
  obtain ⟨hp, ha⟩ := hs.onOption_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  split at hex
  · rename_i v hv
    obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
    obtain ⟨M1, hs1, hZ1⟩ := w_optSome (P := P) (O := O) (passes := passes) hZ.1
      o p a rest k ρ rfl v (by rw [hW]; exact hv)
    rw [hW] at hZ1
    obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := ih_blockAbbR_p hp hl _ _ _ _ _ _ h1 M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
    obtain ⟨M4, hs4, hZ4⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ3
    exact ⟨M4, e2, _, .nil,
      RufLaufG.schritt hs1 (hr2.trans (RufLaufG.schritt hs3 (RufLaufG.einzeln hs4))), hZ4,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · rename_i hv
    obtain ⟨M1, hs1, hZ1⟩ := w_optNone (P := P) (O := O) (passes := passes) hZ.1
      o p a rest k ρ rfl (by rw [hW]; exact hv)
    rw [hW] at hZ1
    obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := ih_blockAbbR_a ha hl _ _ _ _ _ _ hex M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ2
    exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩

set_option linter.unusedSectionVars false in
theorem stmtAbbR_onTag 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ₀ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_cs}
    (v)
    (arms)
    (hs : StmtR A C mr (.onTag (cs := zi_cs) v arms : Stmt D (vertragVon D fn) l Γ Λ₀ Λ'))
    (ih_armsAbbR_arms : ∀ {mr : Bool}, ArmsR A C mr arms → ∀ (v : Wert D (.sum _)), SimAbbBR P O passes f fn stapel rho s0 A R (armWahlG arms v).2.1)
    : SimAbbSR P O passes f fn stapel rho s0 A R (.onTag (cs := zi_cs) v arms : Stmt D (vertragVon D fn) l Γ Λ₀ Λ') :=
  by
  intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
  have ha := hs.onTag_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  rw [execArms_wahl] at hex
  have hsim := ih_armsAbbR_arms ha (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ)
  generalize hwahl : armWahlG arms (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ) = x
    at hex hsim
  obtain ⟨c, b, nutz⟩ := x
  cases c with
  | none =>
    obtain ⟨M1, hs1, hZ1⟩ := w_tagNone (P := P) (O := O) (passes := passes) hZ.1
      v arms rest k ρ rfl b nutz (by rw [hW]; exact hwahl)
    rw [hW] at hZ1
    obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hsim hl _ _ _ _ _ _ hex M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ2
    exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | some τ =>
    obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
    obtain ⟨M1, hs1, hZ1⟩ := w_tagSome (P := P) (O := O) (passes := passes) hZ.1
      v arms rest k ρ rfl τ b nutz (by rw [hW]; exact hwahl)
    rw [hW] at hZ1
    obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hsim hl _ _ _ _ _ _ h1 M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
    obtain ⟨M4, hs4, hZ4⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ3
    exact ⟨M4, e2, _, .nil,
      RufLaufG.schritt hs1 (hr2.trans (RufLaufG.schritt hs3 (RufLaufG.einzeln hs4))), hZ4,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩

set_option linter.unusedSectionVars false in
theorem stmtAbbR_onWhy 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (r)
    (arms)
    (hs : StmtR A C mr (.onWhy (n := zi_n) r arms : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_grundAbbR_arms : ∀ {mr : Bool}, GrundArmsR A C mr arms → ∀ (r : Fin _), SimAbbBR P O passes f fn stapel rho s0 A R (grundWahlG arms r))
    : SimAbbSR P O passes f fn stapel rho s0 A R (.onWhy (n := zi_n) r arms : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
  have ha := hs.onGrund_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  rw [execGrund_wahlW O passes R arms] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_grund (P := P) (O := O) (passes := passes) hZ.1
    r arms rest k ρ rfl
  rw [hW] at hZ1
  obtain ⟨M2, e2, Λx, r', hr2, hZ2, ho2⟩ := ih_grundAbbR_arms ha _ hl _ _ _ _ _ _ hex M1 _ hZ1
    (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
  obtain ⟨M3, hs3, hZ3⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ2
  exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
    by rw [ho2, (Erw.lese _ _ _).offen]⟩

set_option linter.unusedSectionVars false in
theorem stmtAbbR_call 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (args)
    (hp)
    (hr)
    (zzh1 : StmtR A C mr (.call g args hp hr : Stmt D (vertragVon D fn) l Γ Λ _))
    : SimAbbSR P O passes f fn stapel rho s0 A R (.call g args hp hr : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro hl log σ σ' ρ ρ' w hex
  simp only [execStmt] at hex
  split at hex
  · simp only [Ausgang.abb?, reduceCtorEq] at hex
  · exact (Fin.cast hr ‹_›).elim0
  · simp only [Ausgang.abb?, reduceCtorEq] at hex
  · simp only [Ausgang.abb?, reduceCtorEq] at hex

set_option linter.unusedSectionVars false in
theorem stmtAbbR_locks 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (hr)
    (body)
    (hs : StmtR A C mr (.locks L hr body : Stmt D (vertragVon D fn) l Γ Λ _))
    (ih_blockAbbR_body : ∀ {mr : Bool}, BlockR A C mr body → SimAbbBR P O passes f fn stapel rho s0 A R body)
    : SimAbbSR P O passes f fn stapel rho s0 A R (.locks L hr body : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
  obtain ⟨hAL, hb, hbo⟩ := hs.locks_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  obtain ⟨σ1, hb1, rfl⟩ := abb_mapWelt _ hex
  obtain ⟨M1, hs1, hZ1⟩ := w_locksB (P := P) (O := O) (passes := passes) hZ.1
    L hr body rest k ρ rfl hΛ hbo (hA L hAL)
  rw [hW] at hZ1
  obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := ih_blockAbbR_body hb hl _ _ _ _ _ _ hb1 M1 _ hZ1
    (heldB_locks L hΛ) (hA.lauf (RufLaufG.einzeln hs1))
  obtain ⟨M3, hs3, hZ3⟩ := peelFreiR P O passes f fn stapel rho s0 hl hZ2
  obtain ⟨M4, hs4, hZ4⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ3
  exact ⟨M4, e2, _, .nil,
    RufLaufG.schritt hs1 (hr2.trans (RufLaufG.schritt hs3 (RufLaufG.einzeln hs4))), hZ4,
    offen_gibt_nimmt σ σ1 L ho2⟩

set_option linter.unusedSectionVars false in
theorem stmtAbbR_breaking 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (i)
    (body)
    (hs : StmtR A C mr (.breaking i body : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockAbbR_body : ∀ {mr : Bool}, BlockR A C mr body → SimAbbBR P O passes f fn stapel rho s0 A R body)
    : SimAbbSR P O passes f fn stapel rho s0 A R (.breaking i body : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
  have hb := hs.breaking_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_breaking (P := P) (O := O) (passes := passes) hZ.1
    i body rest k ρ rfl
  rw [hW] at hZ1
  obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := ih_blockAbbR_body hb hl _ _ _ _ _ _ hex M1 _ hZ1
    hΛ (hA.lauf (RufLaufG.einzeln hs1))
  obtain ⟨M3, hs3, hZ3⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ2
  exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩

set_option linter.unusedSectionVars false in
theorem stmtAbbR_traverse 
    {mr : Bool}
    {l0 : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (inv)
    (body)
    (zzh1 : StmtR A C mr (.traverse t inv body : Stmt D (vertragVon D fn) l0 Γ Λ _))
    : SimAbbSR P O passes f fn stapel rho s0 A R (.traverse t inv body : Stmt D (vertragVon D fn) l0 Γ Λ _) :=
  by
  intro hl log σ σ' ρ ρ' w hex
  have h0 : (execStmt O passes R (Stmt.traverse (V := vertragVon D fn) (l := l0) t inv body)
      σ ρ).ohneAbbruch := by simp only [execStmt]; exact traverseLauf_ohneAbbruch _ _ _ _ _
  rw [abb_none_of h0] at hex
  cases hex

end SimOk
end Gabbro.Grammatik
