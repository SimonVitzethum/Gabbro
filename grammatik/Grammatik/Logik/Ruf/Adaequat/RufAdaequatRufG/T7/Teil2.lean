module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T7.Teil2Basis
import all Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T7.Teil2Basis

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
