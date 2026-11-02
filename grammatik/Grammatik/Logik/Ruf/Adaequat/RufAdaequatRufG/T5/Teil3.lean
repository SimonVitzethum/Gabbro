module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5.Teil3Basis
import all Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5.Teil3Basis

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T4
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5.Teil2

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
theorem blockOkR_bindCallElse 
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
    (err)
    (rest)
    (hb : BlockR A C mr (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockOkR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimOkBR P O passes f fn stapel rho s0 A R rest)
    : SimOkBR P O passes f fn stapel rho s0 A R (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M k hZ hΛ hA
  obtain ⟨hC, _, hrest, _, _⟩ := hb.bindCallElse_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i σ2 v hR2
    obtain ⟨w, hw⟩ := schrumpf_ok hex
    obtain ⟨M1, hs1, hZ1⟩ := w_bindCallElse (P := P) (O := O) (passes := passes) hZ.1
      g args he hp hr err rest k ρ rfl hΛ.heldIn
    rw [hW] at hZ1
    obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf.1 g hC _ _ _ _ hR2 M1 _ stapel _ hZ1 _
      (PopArt.bindSonst _ err rest k ρ rfl he) (heldB_eintritt hp hΛ _ _)
      (hA.lauf (RufLaufG.einzeln hs1))
    have hZ2 := gepoppt_zustand hG2 rfl
    have hΛ2 : HeldB (vertragVon D fn).boden (nach D g _) (offen σ2.spur) :=
      heldB_iff (fun L => held_nachSig_iff _ _ L)
        (by rw [ho2, (Erw.lese _ _ _).offen]; exact hΛ)
    have hl12 := RufLaufG.schritt hs1 hl2
    obtain ⟨M3, e3, hl3, hZ3, ho3⟩ := ih_blockOkR_rest hrest _ _ _ _ _ hw M2 _ hZ2 hΛ2
      (hA.lauf hl12)
    obtain ⟨M4, hs4, hZ4⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ3
    exact ⟨M4, e3 ++ _, hl12.trans (hl3.trans (RufLaufG.einzeln hs4)),
      by rw [List.append_assoc]; exact hZ4,
      by rw [ho3, ho2, (Erw.lese _ _ _).offen]⟩
  · exact absurd hex (EndeW.zuAusgang_ne_ok _ _ _)
  · cases hex
  · cases hex

set_option linter.unusedSectionVars false in
theorem blockOkR_regRead 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (r)
    (hk)
    (rest)
    (hb : BlockR A C mr (.regRead r hk rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockOkR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimOkBR P O passes f fn stapel rho s0 A R rest)
    : SimOkBR P O passes f fn stapel rho s0 A R (.regRead r hk rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M k hZ hΛ hA
  have hr := hb.regLies_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i v hv
    split at hex
    · rename_i hzs
      obtain ⟨w, hw⟩ := schrumpf_ok hex
      obtain ⟨M1, hs1, hZ1⟩ := w_regLies (P := P) (O := O) (passes := passes) hZ.1
        r hk rest k ρ rfl v (by rw [hW]; exact hv) hzs
      rw [hW] at hZ1
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_rest hr _ _ _ _ _ hw M1 _ hZ1
        hΛ (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
      exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
    · cases hex
  · cases hex

set_option linter.unusedSectionVars false in
theorem blockOkR_regReadElse 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (r)
    (hk)
    (zusage)
    (sonst)
    (rest)
    (hb : BlockR A C mr (.regReadElse r hk zusage sonst rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockOkR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimOkBR P O passes f fn stapel rho s0 A R rest)
    : SimOkBR P O passes f fn stapel rho s0 A R (.regReadElse r hk zusage sonst rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M k hZ hΛ hA
  have hr := hb.regLiesElse_inv.2.1
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i v hv
    split at hex
    · rename_i hw0
      obtain ⟨w, hw⟩ := schrumpf_ok hex
      obtain ⟨M1, hs1, hZ1⟩ := w_regLiesElseWahr (P := P) (O := O) (passes := passes)
        hZ.1 r hk zusage sonst rest k ρ rfl v (by rw [hW]; exact hv)
        (by rw [hW]; exact hw0)
      rw [hW] at hZ1
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_rest hr _ _ _ _ _ hw M1 _ hZ1
        (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
      exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        by rw [ho2, (Erw.lese _ _ _).offen]; rfl⟩
    · exact absurd hex (zuAusgang_ne_ok _ _ _)
  · cases hex

set_option linter.unusedSectionVars false in
theorem blockOkR_awaits 
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
    (ih_blockOkR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimOkBR P O passes f fn stapel rho s0 A R rest)
    : SimOkBR P O passes f fn stapel rho s0 A R (.awaits g payload hp hL hat rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M k hZ hΛ hA
  have hr := hb.awaits_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i hvis
    obtain ⟨w, hw⟩ := schrumpf_ok hex
    obtain ⟨M1, hs1, hZ1⟩ := w_awaits (P := P) (O := O) (passes := passes) hZ.1
      g payload hp hL hat rest k ρ rfl (by rw [hW]; exact hvis)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_rest hr _ _ _ _ _ hw M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
    exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]; rfl⟩
  · cases hex

set_option linter.unusedSectionVars false in
theorem blockOkR_exchange 
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
    (ih_blockOkR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimOkBR P O passes f fn stapel rho s0 A R rest)
    : SimOkBR P O passes f fn stapel rho s0 A R (.exchange g neuE hw hL rest : Block D (vertragVon D fn) l Γ Λ₀ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M k hZ hΛ hA
  have hr := hb.exchange_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  obtain ⟨w, hw'⟩ := schrumpf_ok hex
  obtain ⟨M1, hs1, hZ1⟩ := w_exchange (P := P) (O := O) (passes := passes) hZ.1
    g neuE hw hL rest k ρ rfl
  rw [hW] at hZ1
  have herw := (Erw.lese σ Λ₀ (.inr g :: neuE.orte)).trans
    (Erw.schreibGlob _ g Λ₀ (eval (σ.lese Λ₀ (.inr g :: neuE.orte)) neuE
      (σ.lese Λ₀ (.inr g :: neuE.orte))
      (.cons ((σ.lese Λ₀ (.inr g :: neuE.orte)).globs g) ρ)))
  obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_rest hr _ _ _ _ _ hw' M1 _ hZ1
    (by rw [herw.offen]; exact hΛ) (hA.lauf (RufLaufG.einzeln hs1))
  obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
  exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
    by rw [ho2, herw.offen]⟩

set_option linter.unusedSectionVars false in
theorem blockOkR_narrow 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (sonst)
    (rest)
    (hb : BlockR A C mr (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockOkR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimOkBR P O passes f fn stapel rho s0 A R rest)
    : SimOkBR P O passes f fn stapel rho s0 A R (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M k hZ hΛ hA
  have hr := hb.narrow_inv.2.1
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i hin
    obtain ⟨w, hw⟩ := schrumpf_ok hex
    obtain ⟨M1, hs1, hZ1⟩ := w_narrowOk (P := P) (O := O) (passes := passes) hZ.1
      lo' hi' e sonst rest k ρ rfl hW hin
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_rest hr _ _ _ _ _ hw M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
    exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · exact absurd hex (zuAusgang_ne_ok _ _ _)

end SimOk
end Gabbro.Grammatik
