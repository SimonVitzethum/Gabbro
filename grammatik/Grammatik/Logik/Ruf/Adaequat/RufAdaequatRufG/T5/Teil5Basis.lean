module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T4
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5.Teil4

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
theorem stmtAbbR_retry 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (n)
    (bis)
    (body)
    (ueber)
    (hs : StmtR A C mr (.retry n bis body ueber : Stmt D (vertragVon D fn) l Γ Λ _))
    (ih_blockOkR_body : ∀ {mr : Bool}, BlockR A C mr body → SimOkBR P O passes f fn stapel rho s0 A R body)
    (ih_blockAbbR_body : ∀ {mr : Bool}, BlockR A C mr body → SimAbbBR P O passes f fn stapel rho s0 A R body)
    (ih_blockAbbR_ueber : ∀ {mr : Bool}, BlockR A C mr ueber → SimAbbBR P O passes f fn stapel rho s0 A R ueber)
    : SimAbbSR P O passes f fn stapel rho s0 A R (.retry n bis body ueber : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
  obtain ⟨hb, hu⟩ := hs.retry_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_dannRetry (P := P) (O := O) (passes := passes) hZ.1
    n bis body ueber rest k ρ rfl
  rw [hW] at hZ1
  obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := retryAbbR P O passes f fn stapel rho s0 A R hl bis body
    ueber (ih_blockOkR_body hb) (ih_blockAbbR_body hb) (ih_blockAbbR_ueber hu) (.dann rest k) n log
    σ σ' ρ ρ' w hex M1 hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1))
  obtain ⟨M3, hs3, hZ3⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ2
  exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩

set_option linter.unusedSectionVars false in
theorem stmtAbbR_forever 
    {mr : Bool}
    {l0 : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (a)
    (inv)
    (body)
    (zzh1 : StmtR A C mr (.forever a inv body : Stmt D (vertragVon D fn) l0 Γ Λ _))
    : SimAbbSR P O passes f fn stapel rho s0 A R (.forever a inv body : Stmt D (vertragVon D fn) l0 Γ Λ _) :=
  by
  intro hl log σ σ' ρ ρ' w hex
  have h0 : (execStmt O passes R (Stmt.forever (V := vertragVon D fn) (l := l0) a inv body)
      σ ρ).ohneAbbruch := by simp only [execStmt]; exact foreverLauf_ohneAbbruch _ _ _ _ _ _
  rw [abb_none_of h0] at hex
  cases hex

set_option linter.unusedSectionVars false in
theorem stmtAbbR_leave 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (h)
    (zzh1 : StmtR A C mr (.leave h : Stmt D (vertragVon D fn) l Γ Λ _))
    : SimAbbSR P O passes f fn stapel rho s0 A R (.leave h : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
  simp only [execStmt, Ausgang.abb?, Option.some.injEq, Prod.mk.injEq] at hex
  obtain ⟨rfl, rfl, rfl⟩ := hex
  exact ⟨M, [], _, rest, RufLaufG.refl M, hZ, rfl⟩

set_option linter.unusedSectionVars false in
theorem stmtAbbR_next 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (h)
    (zzh1 : StmtR A C mr (.next h : Stmt D (vertragVon D fn) l Γ Λ _))
    : SimAbbSR P O passes f fn stapel rho s0 A R (.next h : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
  simp only [execStmt, Ausgang.abb?, Option.some.injEq, Prod.mk.injEq] at hex
  obtain ⟨rfl, rfl, rfl⟩ := hex
  exact ⟨M, [], _, rest, RufLaufG.refl M, hZ, rfl⟩

set_option linter.unusedSectionVars false in
theorem blockAbbR_cons 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (hb : BlockR A C mr (.cons (Λ' := zi_Λ') s rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_stmtOkR_s : ∀ {mr : Bool}, StmtR A C mr s → SimOkSR P O passes f fn stapel rho s0 A R s)
    (ih_stmtAbbR_s : ∀ {mr : Bool}, StmtR A C mr s → SimAbbSR P O passes f fn stapel rho s0 A R s)
    (ih_blockAbbR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimAbbBR P O passes f fn stapel rho s0 A R rest)
    : SimAbbBR P O passes f fn stapel rho s0 A R (.cons (Λ' := zi_Λ') s rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
  obtain ⟨hs, hr⟩ := hb.cons_inv
  rcases execBlock_cons_abb O passes R s rest hex with h | ⟨σ1, ρ1, h1, h2⟩
  · exact ih_stmtAbbR_s hs hl _ _ _ _ _ _ h M rest k hZ hΛ hA
  · obtain ⟨M1, e1, hl1, hZ1, ho1⟩ := ih_stmtOkR_s hs _ _ _ _ _ h1 M rest k hZ hΛ hA
    have hΛ1 := heldB_iff (s.held_iff) hΛ
    rw [← ho1] at hΛ1
    obtain ⟨M2, e2, Λx, r, hl2, hZ2, ho2⟩ := ih_blockAbbR_rest hr hl _ _ _ _ _ _ h2 M1 k hZ1
      hΛ1 (hA.lauf hl1)
    exact ⟨M2, e2 ++ e1, Λx, r, hl1.trans hl2, by rw [List.append_assoc]; exact hZ2,
      by rw [ho2, ho1]⟩

set_option linter.unusedSectionVars false in
theorem blockAbbR_bind 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (hb : BlockR A C mr (.bind (τ := zi_τ) e rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockAbbR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimAbbBR P O passes f fn stapel rho s0 A R rest)
    : SimAbbBR P O passes f fn stapel rho s0 A R (.bind (τ := zi_τ) e rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
  have hr := hb.bind_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
  obtain ⟨M1, hs1, hZ1⟩ := w_dannBind (P := P) (O := O) (passes := passes) hZ.1
    e rest k ρ rfl
  rw [hW] at hZ1
  obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := ih_blockAbbR_rest hr hl _ _ _ _ _ _ h1 M1 _ hZ1
    (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
  obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
  exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
    by rw [ho2, (Erw.lese _ _ _).offen]⟩

set_option linter.unusedSectionVars false in
theorem blockAbbR_bindCall 
    {mr : Bool}
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
    (hb : BlockR A C mr (.bindCall (τ := zi_τ) g args he hp hr rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockAbbR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimAbbBR P O passes f fn stapel rho s0 A R rest)
    : SimAbbBR P O passes f fn stapel rho s0 A R (.bindCall (τ := zi_τ) g args he hp hr rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
  obtain ⟨hC, hrest⟩ := hb.bindCall_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i σ2 v hR2
    obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
    obtain ⟨M1, hs1, hZ1⟩ := w_bindCall (P := P) (O := O) (passes := passes) hZ.1
      g args he hp hr rest k ρ rfl hΛ.heldIn
    rw [hW] at hZ1
    obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf.1 g hC _ _ _ _ hR2 M1 _ stapel _ hZ1 _
      (PopArt.bind rest k ρ rfl he) (heldB_eintritt hp hΛ _ _)
      (hA.lauf (RufLaufG.einzeln hs1))
    have hZ2 := gepoppt_zustand hG2 rfl
    have hΛ2 : HeldB (vertragVon D fn).boden (nach D g _) (offen σ2.spur) :=
      heldB_iff (fun L => held_nachSig_iff _ _ L)
        (by rw [ho2, (Erw.lese _ _ _).offen]; exact hΛ)
    have hl12 := RufLaufG.schritt hs1 hl2
    obtain ⟨M3, e3, Λx, r, hl3, hZ3, ho3⟩ := ih_blockAbbR_rest hrest hl _ _ _ _ _ _ h1 M2 _ hZ2
      hΛ2 (hA.lauf hl12)
    obtain ⟨M4, hs4, hZ4⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ3
    exact ⟨M4, e3 ++ _, _, .nil, hl12.trans (hl3.trans (RufLaufG.einzeln hs4)),
      by rw [List.append_assoc]; exact hZ4,
      by rw [ho3, ho2, (Erw.lese _ _ _).offen]⟩
  · exact (Fin.cast hr ‹_›).elim0
  · simp only [Ausgang.abb?, reduceCtorEq] at hex
  · simp only [Ausgang.abb?, reduceCtorEq] at hex

end SimOk
end Gabbro.Grammatik
