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
  | some lh =>
    obtain ⟨lo, hi⟩ := lh
    obtain ⟨M1, hs1, hZ1⟩ := w_tagSome (P := P) (O := O) (passes := passes) hZ.1
      w arms rest k ρ rfl lo hi b nutz (by rw [hW]; exact hwahl)
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
  rw [ende_mapWelt_none _ (blockKeinR O passes R A C body hb _ _)] at hex
  cases hex

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

set_option linter.unusedSectionVars false in
theorem stmtRetR_traverse 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (inv)
    (body)
    (hs : StmtR A C true (.traverse t inv body : Stmt D (vertragVon D fn) l Γ Λ _))
    (ih_blockRetR_body : BlockR A C true body → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG body)
    : SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG (.traverse t inv body : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
  have hb := hs.traverse_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_dannTrav (P := P) (O := O) (passes := passes) hZ.1
    t inv body rest k ρ rfl
  rw [hW] at hZ1
  exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
    (travRetR P O passes f fn caller rst rho s0 A R ziel zielG t inv body
      (blockOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf body hb)
      (blockAbbR P O passes f fn (caller :: rst) rho s0 A R C hRuf body hb)
      (ih_blockRetR_body hb) (.dann rest k) _ log σ ρ E hpe hex M1 hZ1 hΛ
      (hA.lauf (RufLaufG.einzeln hs1)))

set_option linter.unusedSectionVars false in
theorem stmtRetR_retry 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (n)
    (bis)
    (body)
    (ueber)
    (hs : StmtR A C true (.retry n bis body ueber : Stmt D (vertragVon D fn) l Γ Λ _))
    (ih_blockRetR_body : BlockR A C true body → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG body)
    (ih_blockRetR_ueber : BlockR A C true ueber → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG ueber)
    : SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG (.retry n bis body ueber : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
  obtain ⟨hb, hu⟩ := hs.retry_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_dannRetry (P := P) (O := O) (passes := passes) hZ.1
    n bis body ueber rest k ρ rfl
  rw [hW] at hZ1
  exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
    (retryRetR P O passes f fn caller rst rho s0 A R ziel zielG bis body ueber
      (blockOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf body hb)
      (blockAbbR P O passes f fn (caller :: rst) rho s0 A R C hRuf body hb)
      (ih_blockRetR_body hb) (ih_blockRetR_ueber hu)
      (.dann rest k) n log σ ρ E hpe hex M1 hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))

set_option linter.unusedSectionVars false in
theorem stmtRetR_forever 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (a)
    (inv)
    (body)
    (hs : StmtR A C true (.forever a inv body : Stmt D (vertragVon D fn) l Γ Λ _))
    (ih_blockRetR_body : BlockR A C true body → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG body)
    : SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG (.forever a inv body : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
  have hb := hs.forever_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_dannForever (P := P) (O := O) (passes := passes) hZ.1
    a inv body rest k ρ rfl
  rw [hW] at hZ1
  exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
    (foreverRetR P O passes f fn caller rst rho s0 A R ziel zielG a inv body
      (blockOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf body hb)
      (blockAbbR P O passes f fn (caller :: rst) rho s0 A R C hRuf body hb)
      (ih_blockRetR_body hb) (.dann rest k) passes log σ ρ E hpe hex M1 hZ1 hΛ
      (hA.lauf (RufLaufG.einzeln hs1)))

set_option linter.unusedSectionVars false in
theorem stmtRetR_ret 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (hperm)
    (zzh1 : StmtR A C true (.ret e hperm : Stmt D (vertragVon D fn) l Γ Λ _))
    : SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG (.ret e hperm : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro log σ ρ E hpe hex M _ rest k hZ hΛ _
  have hW := hZ.welt
  simp only [execStmt, Ausgang.ende?, Option.some.injEq] at hex
  subst hex
  obtain ⟨M1, hs1, hG⟩ := w_dannRetP (P := P) (O := O) (passes := passes) hZ.1
    caller rst rfl hpe e hperm rest k ρ rfl hΛ.heldIn
  rw [hW] at hG
  exact ⟨M1, [], RufLaufG.einzeln hs1, hG, (Erw.lese _ _ _).offen⟩

set_option linter.unusedSectionVars false in
theorem stmtRetR_retWhy 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (hperm)
    (zzh1 : StmtR A C true (.retWhy r hperm : Stmt D (vertragVon D fn) l Γ Λ _))
    : SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG (.retWhy r hperm : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro log σ ρ E hpe hex M _ rest k hZ hΛ _
  have hW := hZ.welt
  simp only [execStmt, Ausgang.ende?, Option.some.injEq] at hex
  subst hex
  obtain ⟨M1, hs1, hG⟩ := w_dannRetGrundP (P := P) (O := O) (passes := passes) hZ.1
    caller rst rfl hpe r hperm rest k ρ rfl hΛ.heldIn
  rw [hW] at hG
  exact ⟨M1, [], RufLaufG.einzeln hs1, hG, rfl⟩

set_option linter.unusedSectionVars false in
theorem blockRetR_cons 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (hb : BlockR A C true (.cons (Λ' := zi_Λ') s rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_stmtRetR_s : StmtR A C true s → SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG s)
    (ih_blockRetR_rest : BlockR A C true rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.cons (Λ' := zi_Λ') s rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  obtain ⟨hs, hr⟩ := hb.cons_inv
  rcases execBlock_cons_ende O passes R s rest hex with h | ⟨σ1, ρ1, h1, h2⟩
  · exact ih_stmtRetR_s hs _ _ _ _ hpe h M rest k hZ hΛ hA
  · obtain ⟨M1, e1, hl1, hZ1, ho1⟩ := stmtOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf
      s hs _ _ _ _ _ h1 M rest k hZ hΛ hA
    have hΛ1 := heldB_iff (s.held_iff) hΛ
    rw [← ho1] at hΛ1
    exact gepoppt_laufR P O passes f fn rst rho s0 ziel zielG hl1 ho1
      (ih_blockRetR_rest hr _ _ _ _ hpe h2 M1 k hZ1 hΛ1 (hA.lauf hl1))

set_option linter.unusedSectionVars false in
theorem blockRetR_bind 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (hb : BlockR A C true (.bind (τ := zi_τ) e rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockRetR_rest : BlockR A C true rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.bind (τ := zi_τ) e rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  have hr := hb.bind_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  rw [ende_schrumpf] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_dannBind (P := P) (O := O) (passes := passes) hZ.1
    e rest k ρ rfl
  rw [hW] at hZ1
  exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
    (ih_blockRetR_rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
      (hA.lauf (RufLaufG.einzeln hs1)))

set_option linter.unusedSectionVars false in
theorem blockRetR_bindCall 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_τ}
    (g)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (hb : BlockR A C true (.bindCall (τ := zi_τ) g args he hp hr rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockRetR_rest : BlockR A C true rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.bindCall (τ := zi_τ) g args he hp hr rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  obtain ⟨hC, hrest⟩ := hb.bindCall_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i σ2 w hR2
    rw [ende_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_bindCall (P := P) (O := O) (passes := passes) hZ.1
      g args he hp hr rest k ρ rfl hΛ.heldIn
    rw [hW] at hZ1
    obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf.1 g hC _ _ _ _ hR2 M1 _ (caller :: rst) _ hZ1 _
      (PopArt.bind rest k ρ rfl he) (heldB_eintritt hp hΛ _ _)
      (hA.lauf (RufLaufG.einzeln hs1))
    have hZ2 := gepoppt_zustand hG2 rfl
    have hΛ2 : HeldB (vertragVon D fn).boden (nach D g _) (offen σ2.spur) :=
      heldB_iff (fun L => held_nachSig_iff _ _ L)
        (by rw [ho2, (Erw.lese _ _ _).offen]; exact hΛ)
    have hl12 := RufLaufG.schritt hs1 hl2
    have ho12 : offen σ2.spur = offen σ.spur := by rw [ho2, (Erw.lese _ _ _).offen]
    exact gepoppt_laufR P O passes f fn rst rho s0 ziel zielG hl12 ho12
      (ih_blockRetR_rest hrest _ _ _ _ hpe hex M2 _ hZ2 hΛ2 (hA.lauf hl12))
  · exact (Fin.cast hr ‹_›).elim0
  · simp only [Ausgang.ende?, reduceCtorEq] at hex
  · simp only [Ausgang.ende?, reduceCtorEq] at hex

end SimRet
end Gabbro.Grammatik
