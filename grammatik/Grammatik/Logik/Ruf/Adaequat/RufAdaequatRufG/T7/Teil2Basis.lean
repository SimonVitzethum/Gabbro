module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T6
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T7.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section SimRet
variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (rho : Env D (D.params fn))
  (s0 : World D) (A : D.Lock → Prop)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (C : D.Fn → Prop)
  (ziel : ErgVal D (D.erg fn) → RufRahmenG D) (zielG : Fin (D.gruende fn) → RufRahmenG D)
variable (hRuf : RufOk P O passes f A R C)
include hRuf

-- `hRuf` is used at calls; the arm recursions reach it only through
-- `blockRetR`, which the linter does not count as a use.
set_option linter.unusedSectionVars false in
theorem stmtRetR_ite 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (t)
    (e)
    (hs : StmtR A C true (.ite c t e : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockRetR_t : BlockR A C true t → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG t)
    (ih_blockRetR_e : BlockR A C true e → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG e)
    : SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG (.ite c t e : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
  obtain ⟨ht, he⟩ := hs.ite_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  split at hex
  · rename_i hc
    obtain ⟨M1, hs1, hZ1⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ.1
      c t e rest k ρ rfl (by rw [hW]; exact hc)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_blockRetR_t ht _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · rename_i hc
    obtain ⟨M1, hs1, hZ1⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ.1
      c t e rest k ρ rfl (by rw [hW]; simpa using hc)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_blockRetR_e he _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))

set_option linter.unusedSectionVars false in
theorem stmtRetR_onOption 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (o)
    (p)
    (a)
    (hs : StmtR A C true (.onOption (n := zi_n) o p a : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockRetR_p : BlockR A C true p → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG p)
    (ih_blockRetR_a : BlockR A C true a → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG a)
    : SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG (.onOption (n := zi_n) o p a : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
  obtain ⟨hp, ha⟩ := hs.onOption_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  split at hex
  · rename_i w hw
    rw [ende_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_optSome (P := P) (O := O) (passes := passes) hZ.1
      o p a rest k ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_blockRetR_p hp _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · rename_i hw
    obtain ⟨M1, hs1, hZ1⟩ := w_optNone (P := P) (O := O) (passes := passes) hZ.1
      o p a rest k ρ rfl (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_blockRetR_a ha _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))

set_option linter.unusedSectionVars false in
theorem stmtRetR_onTag 
    {l : Bool}
    {Γ : Ctx}
    {Λ₀ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_cs}
    (w)
    (arms)
    (hs : StmtR A C true (.onTag (cs := zi_cs) w arms : Stmt D (vertragVon D fn) l Γ Λ₀ Λ'))
    (ih_armsRetR_arms : ArmsR A C true arms → ∀ (v : Wert D (.sum _)), SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (armWahlG arms v).2.1)
    : SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG (.onTag (cs := zi_cs) w arms : Stmt D (vertragVon D fn) l Γ Λ₀ Λ') :=
  by
  intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
  have ha := hs.onTag_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  rw [execArms_wahl, ende_schrumpfArm] at hex
  have hsim := ih_armsRetR_arms ha (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ)
  generalize hwahl : armWahlG arms (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ) = x
    at hex hsim
  obtain ⟨c, b, nutz⟩ := x
  cases c with
  | none =>
    obtain ⟨M1, hs1, hZ1⟩ := w_tagNone (P := P) (O := O) (passes := passes) hZ.1
      w arms rest k ρ rfl b nutz (by rw [hW]; exact hwahl)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (hsim _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1)))
  | some τ =>
    obtain ⟨M1, hs1, hZ1⟩ := w_tagSome (P := P) (O := O) (passes := passes) hZ.1
      w arms rest k ρ rfl τ b nutz (by rw [hW]; exact hwahl)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (hsim _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))

set_option linter.unusedSectionVars false in
theorem stmtRetR_onWhy 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (r)
    (arms)
    (hs : StmtR A C true (.onWhy (n := zi_n) r arms : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_grundRetR_arms : GrundArmsR A C true arms → ∀ (r : Fin _), SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (grundWahlG arms r))
    : SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG (.onWhy (n := zi_n) r arms : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
  have ha := hs.onGrund_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  rw [execGrund_wahlW O passes R arms] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_grund (P := P) (O := O) (passes := passes) hZ.1
    r arms rest k ρ rfl
  rw [hW] at hZ1
  exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
    (ih_grundRetR_arms ha _ _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
      (hA.lauf (RufLaufG.einzeln hs1)))

set_option linter.unusedSectionVars false in
theorem stmtRetR_call 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (args)
    (hp)
    (hr)
    (zzh1 : StmtR A C true (.call g args hp hr : Stmt D (vertragVon D fn) l Γ Λ _))
    : SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG (.call g args hp hr : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro log σ ρ E _ hex
  rw [call_ende_none O passes R σ ρ] at hex
  cases hex

set_option linter.unusedSectionVars false in
theorem stmtRetR_locks 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (hr)
    (body)
    (hs : StmtR A C true (.locks L hr body : Stmt D (vertragVon D fn) l Γ Λ _))
    : SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG (.locks L hr body : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro log σ ρ E _ hex
  obtain ⟨_, hb, _⟩ := hs.locks_inv
  simp only [execStmt] at hex
  have hnone := blockKeinR O passes R A C body hb (σ.nimmt L) ρ
  generalize hbody : execBlock O passes R body (σ.nimmt L) ρ = outcome at hex hnone
  cases outcome <;> simp only [Ausgang.mapWelt, Ausgang.ende?, reduceCtorEq] at hex hnone

set_option linter.unusedSectionVars false in
theorem stmtRetR_breaking 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (i)
    (body)
    (hs : StmtR A C true (.breaking i body : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockRetR_body : BlockR A C true body → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG body)
    : SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG (.breaking i body : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
  have hb := hs.breaking_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_breaking (P := P) (O := O) (passes := passes) hZ.1
    i body rest k ρ rfl
  rw [hW] at hZ1
  exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
    (ih_blockRetR_body hb _ _ _ _ hpe hex M1 _ hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))


end SimRet

end Gabbro.Grammatik
