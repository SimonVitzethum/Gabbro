module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5.Teil5Basis
import all Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5.Teil5Basis

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
theorem blockAbbR_regRead 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (r)
    (hk)
    (rest)
    (hb : BlockR A C mr (.regRead r hk rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockAbbR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimAbbBR P O passes f fn stapel rho s0 A R rest)
    : SimAbbBR P O passes f fn stapel rho s0 A R (.regRead r hk rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
  have hr := hb.regLies_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i v hv
    split at hex
    · rename_i hzs
      obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
      obtain ⟨M1, hs1, hZ1⟩ := w_regLies (P := P) (O := O) (passes := passes) hZ.1
        r hk rest k ρ rfl v (by rw [hW]; exact hv) hzs
      rw [hW] at hZ1
      obtain ⟨M2, e2, Λx, r', hr2, hZ2, ho2⟩ := ih_blockAbbR_rest hr hl _ _ _ _ _ _ h1 M1 _ hZ1
        hΛ (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
      exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        ho2⟩
    · simp only [Ausgang.abb?, reduceCtorEq] at hex
  · simp only [Ausgang.abb?, reduceCtorEq] at hex

set_option linter.unusedSectionVars false in
theorem blockAbbR_awaits 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (g)
    (payload)
    (hp)
    (hL)
    (hat)
    (rest)
    (hb : BlockR A C mr (.awaits g payload hp hL hat rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockAbbR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimAbbBR P O passes f fn stapel rho s0 A R rest)
    : SimAbbBR P O passes f fn stapel rho s0 A R (.awaits g payload hp hL hat rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
  have hr := hb.awaits_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i hvis
    obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
    obtain ⟨M1, hs1, hZ1⟩ := w_awaits (P := P) (O := O) (passes := passes) hZ.1
      g payload hp hL hat rest k ρ rfl (by rw [hW]; exact hvis)
    rw [hW] at hZ1
    obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := ih_blockAbbR_rest hr hl _ _ _ _ _ _ h1 M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
    exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]; rfl⟩
  · simp only [Ausgang.abb?, reduceCtorEq] at hex

set_option linter.unusedSectionVars false in
theorem blockAbbR_exchange 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ₀ : List (Res D)}
    {Λ' : List (Res D)}
    (g)
    (neuE)
    (hw)
    (hL)
    (rest)
    (hb : BlockR A C mr (.exchange g neuE hw hL rest : Block D (vertragVon D fn) l Γ Λ₀ Λ'))
    (ih_blockAbbR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimAbbBR P O passes f fn stapel rho s0 A R rest)
    : SimAbbBR P O passes f fn stapel rho s0 A R (.exchange g neuE hw hL rest : Block D (vertragVon D fn) l Γ Λ₀ Λ') :=
  by
  intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
  have hr := hb.exchange_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
  obtain ⟨M1, hs1, hZ1⟩ := w_exchange (P := P) (O := O) (passes := passes) hZ.1
    g neuE hw hL rest k ρ rfl
  rw [hW] at hZ1
  have herw := (Erw.lese σ Λ₀ (.inr g :: neuE.orte)).trans
    (Erw.schreibGlob _ g Λ₀ (eval (σ.lese Λ₀ (.inr g :: neuE.orte)) neuE
      (σ.lese Λ₀ (.inr g :: neuE.orte))
      (.cons ((σ.lese Λ₀ (.inr g :: neuE.orte)).globs g) ρ)))
  obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := ih_blockAbbR_rest hr hl _ _ _ _ _ _ h1 M1 _ hZ1
    (by rw [herw.offen]; exact hΛ) (hA.lauf (RufLaufG.einzeln hs1))
  obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
  exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
    by rw [ho2, herw.offen]⟩

set_option linter.unusedSectionVars false in
theorem blockAbbR_float 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    {zi_l2}
    {zi_h2}
    (op)
    (a)
    (b)
    (lo)
    (hi)
    (rest)
    (hb : BlockR A C mr (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockAbbR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimAbbBR P O passes f fn stapel rho s0 A R rest)
    : SimAbbBR P O passes f fn stapel rho s0 A R (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
  have hr := hb.gleit_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i v hv
    obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleit (P := P) (O := O) (passes := passes) hZ.1
      op a b lo hi rest k ρ rfl v (by rw [hW]; exact hv)
    rw [hW] at hZ1
    obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := ih_blockAbbR_rest hr hl _ _ _ _ _ _ h1 M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
    exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · simp only [Ausgang.abb?, reduceCtorEq] at hex

set_option linter.unusedSectionVars false in
theorem blockAbbR_floatLit 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (q)
    (lo)
    (hi)
    (rest)
    (hb : BlockR A C mr (.floatLit q lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockAbbR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimAbbBR P O passes f fn stapel rho s0 A R rest)
    : SimAbbBR P O passes f fn stapel rho s0 A R (.floatLit q lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
  have hr := hb.gleitLit_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i v hv
    obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitLit (P := P) (O := O) (passes := passes) hZ.1
      q lo hi rest k ρ rfl v hv
    rw [hW] at hZ1
    obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := ih_blockAbbR_rest hr hl _ _ _ _ _ _ h1 M1 _ hZ1
      hΛ (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
    exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      ho2⟩
  · simp only [Ausgang.abb?, reduceCtorEq] at hex

set_option linter.unusedSectionVars false in
theorem blockAbbR_floatOf 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (rest)
    (hb : BlockR A C mr (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockAbbR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimAbbBR P O passes f fn stapel rho s0 A R rest)
    : SimAbbBR P O passes f fn stapel rho s0 A R (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
  have hr := hb.gleitVon_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i v hv
    obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitVon (P := P) (O := O) (passes := passes) hZ.1
      e lo hi rest k ρ rfl v (by rw [hW]; exact hv)
    rw [hW] at hZ1
    obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := ih_blockAbbR_rest hr hl _ _ _ _ _ _ h1 M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
    exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · simp only [Ausgang.abb?, reduceCtorEq] at hex

end SimOk
end Gabbro.Grammatik
