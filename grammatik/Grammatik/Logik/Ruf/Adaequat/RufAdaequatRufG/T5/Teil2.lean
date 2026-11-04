module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5.Teil2Basis
import all Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5.Teil2Basis

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T4
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5.Teil1

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

-- `hRuf` discharges the calls in `stmtOkR`/`blockOkR`; `armsOkR`/`grundOkR`
-- need it only through their recursive `blockOkR` calls, which the linter
-- does not count as a use.
set_option linter.unusedSectionVars false in
theorem stmtOkR_ite 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (t)
    (e)
    (hs : StmtR A C mr (.ite c t e : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockOkR_t : ∀ {mr : Bool}, BlockR A C mr t → SimOkBR P O passes f fn stapel rho s0 A R t)
    (ih_blockOkR_e : ∀ {mr : Bool}, BlockR A C mr e → SimOkBR P O passes f fn stapel rho s0 A R e)
    : SimOkSR P O passes f fn stapel rho s0 A R (.ite c t e : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
  obtain ⟨ht, he⟩ := hs.ite_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  split at hex
  · rename_i hc
    obtain ⟨M1, hs1, hZ1⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ.1
      c t e rest k ρ rfl (by rw [hW]; exact hc)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_t ht _ _ _ _ _ hex M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · rename_i hc
    obtain ⟨M1, hs1, hZ1⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ.1
      c t e rest k ρ rfl (by rw [hW]; simpa using hc)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_e he _ _ _ _ _ hex M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩

set_option linter.unusedSectionVars false in
theorem stmtOkR_onOption 
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
    (ih_blockOkR_p : ∀ {mr : Bool}, BlockR A C mr p → SimOkBR P O passes f fn stapel rho s0 A R p)
    (ih_blockOkR_a : ∀ {mr : Bool}, BlockR A C mr a → SimOkBR P O passes f fn stapel rho s0 A R a)
    : SimOkSR P O passes f fn stapel rho s0 A R (.onOption (n := zi_n) o p a : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
  obtain ⟨hp, ha⟩ := hs.onOption_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  split at hex
  · rename_i v hv
    obtain ⟨w, hw⟩ := schrumpf_ok hex
    obtain ⟨M1, hs1, hZ1⟩ := w_optSome (P := P) (O := O) (passes := passes) hZ.1
      o p a rest k ρ rfl v (by rw [hW]; exact hv)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_p hp _ _ _ _ _ hw M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
    exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · rename_i hv
    obtain ⟨M1, hs1, hZ1⟩ := w_optNone (P := P) (O := O) (passes := passes) hZ.1
      o p a rest k ρ rfl (by rw [hW]; exact hv)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_a ha _ _ _ _ _ hex M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩

set_option linter.unusedSectionVars false in
theorem stmtOkR_onTag 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ₀ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_cs}
    (v)
    (arms)
    (hs : StmtR A C mr (.onTag (cs := zi_cs) v arms : Stmt D (vertragVon D fn) l Γ Λ₀ Λ'))
    (ih_armsOkR_arms : ∀ {mr : Bool}, ArmsR A C mr arms → ∀ (v : Wert D (.sum _)), SimOkBR P O passes f fn stapel rho s0 A R (armWahlG arms v).2.1)
    : SimOkSR P O passes f fn stapel rho s0 A R (.onTag (cs := zi_cs) v arms : Stmt D (vertragVon D fn) l Γ Λ₀ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
  have ha := hs.onTag_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  rw [execArms_wahl] at hex
  have hsim := ih_armsOkR_arms ha (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ)
  generalize hwahl : armWahlG arms (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ) = w
    at hex hsim
  obtain ⟨c, b, nutz⟩ := w
  cases c with
  | none =>
    obtain ⟨M1, hs1, hZ1⟩ := w_tagNone (P := P) (O := O) (passes := passes) hZ.1
      v arms rest k ρ rfl b nutz (by rw [hW]; exact hwahl)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hsim _ _ _ _ _ hex M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | some τ =>
    obtain ⟨w', hw'⟩ := schrumpf_ok hex
    obtain ⟨M1, hs1, hZ1⟩ := w_tagSome (P := P) (O := O) (passes := passes) hZ.1
      v arms rest k ρ rfl τ b nutz (by rw [hW]; exact hwahl)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hsim _ _ _ _ _ hw' M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
    exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩

set_option linter.unusedSectionVars false in
theorem stmtOkR_onWhy 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (r)
    (arms)
    (hs : StmtR A C mr (.onWhy (n := zi_n) r arms : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_grundOkR_arms : ∀ {mr : Bool}, GrundArmsR A C mr arms → ∀ (r : Fin _), SimOkBR P O passes f fn stapel rho s0 A R (grundWahlG arms r))
    : SimOkSR P O passes f fn stapel rho s0 A R (.onWhy (n := zi_n) r arms : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
  have ha := hs.onGrund_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  rw [execGrund_wahlW O passes R arms] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_grund (P := P) (O := O) (passes := passes) hZ.1
    r arms rest k ρ rfl
  rw [hW] at hZ1
  obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_grundOkR_arms ha _ _ _ _ _ _ hex M1 _ hZ1
    (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
  exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩

set_option linter.unusedSectionVars false in
theorem stmtOkR_call 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (args)
    (hp)
    (hr)
    (hs : StmtR A C mr (.call g args hp hr : Stmt D (vertragVon D fn) l Γ Λ _))
    : SimOkSR P O passes f fn stapel rho s0 A R (.call g args hp hr : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
  have hC := hs.call_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  split at hex
  · rename_i σ2 v hR2
    simp only [Ausgang.ok.injEq] at hex
    obtain ⟨rfl, rfl⟩ := hex
    obtain ⟨M1, hs1, hZ1⟩ := w_rufDann (P := P) (O := O) (passes := passes) hZ.1
      g args hp hr rest k ρ rfl hΛ.heldIn
    rw [hW] at hZ1
    obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf.1 g hC _ _ _ _ hR2 M1 _ stapel _ hZ1 _ (PopArt.wie rfl)
      (heldB_eintritt hp hΛ _ _) (hA.lauf (RufLaufG.einzeln hs1))
    exact ⟨M2, _, RufLaufG.schritt hs1 hl2, gepoppt_zustand hG2 rfl,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · exact (Fin.cast hr ‹_›).elim0
  · cases hex
  · cases hex

set_option linter.unusedSectionVars false in
theorem stmtOkR_locks 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (hr)
    (body)
    (hs : StmtR A C mr (.locks L hr body : Stmt D (vertragVon D fn) l Γ Λ _))
    (ih_blockOkR_body : ∀ {mr : Bool}, BlockR A C mr body → SimOkBR P O passes f fn stapel rho s0 A R body)
    : SimOkSR P O passes f fn stapel rho s0 A R (.locks L hr body : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
  obtain ⟨hAL, hb, hbo⟩ := hs.locks_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  have mapped : (execBlock O passes R body (σ.nimmt L) ρ).mapWelt
      (fun world : World D => world.gibt L) = .ok σ' ρ' := by
    generalize hbody : execBlock O passes R body (σ.nimmt L) ρ = outcome at hex ⊢
    cases outcome <;> simpa only [Ausgang.mapWelt, reduceCtorEq] using hex
  obtain ⟨σ1, hb1, rfl⟩ := mapWelt_ok mapped
  obtain ⟨M1, hs1, hZ1⟩ := w_locksB (P := P) (O := O) (passes := passes) hZ.1
    L hr body rest k ρ rfl hΛ hbo (hA L hAL)
  rw [hW] at hZ1
  obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_body hb _ _ _ _ _ hb1 M1 _ hZ1
    (heldB_locks L hΛ) (hA.lauf (RufLaufG.einzeln hs1))
  have hW2 := hZ2.welt
  obtain ⟨M3, hs3, hZ3⟩ := w_freiGib (P := P) (O := O) (passes := passes) hZ2.1
    L (.dann rest k) ρ' rfl
  rw [hW2] at hZ3
  exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
    offen_gibt_nimmt σ σ1 L ho2⟩

set_option linter.unusedSectionVars false in
theorem stmtOkR_breaking 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (i)
    (body)
    (hs : StmtR A C mr (.breaking i body : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockOkR_body : ∀ {mr : Bool}, BlockR A C mr body → SimOkBR P O passes f fn stapel rho s0 A R body)
    : SimOkSR P O passes f fn stapel rho s0 A R (.breaking i body : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
  have hb := hs.breaking_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_breaking (P := P) (O := O) (passes := passes) hZ.1
    i body rest k ρ rfl
  rw [hW] at hZ1
  obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_body hb _ _ _ _ _ hex M1 _ hZ1
    hΛ (hA.lauf (RufLaufG.einzeln hs1))
  exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, ho2⟩

end SimOk
end Gabbro.Grammatik
