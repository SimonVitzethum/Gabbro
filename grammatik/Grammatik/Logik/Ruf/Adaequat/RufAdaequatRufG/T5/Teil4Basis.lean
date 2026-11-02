module

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
theorem blockOkR_check 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (sonst)
    (rest)
    (hb : BlockR A C mr (.check c sonst rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockOkR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimOkBR P O passes f fn stapel rho s0 A R rest)
    : SimOkBR P O passes f fn stapel rho s0 A R (.check c sonst rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M k hZ hΛ hA
  have hr := hb.pruefung_inv.2.1
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i hc
    obtain ⟨M1, hs1, hZ1⟩ := w_pruefWahr (P := P) (O := O) (passes := passes) hZ.1
      c sonst rest k ρ rfl (by rw [hW]; exact hc)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_rest hr _ _ _ _ _ hex M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · exact absurd hex (zuAusgang_ne_ok _ _ _)

set_option linter.unusedSectionVars false in
theorem blockOkR_float 
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
    (ih_blockOkR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimOkBR P O passes f fn stapel rho s0 A R rest)
    : SimOkBR P O passes f fn stapel rho s0 A R (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M k hZ hΛ hA
  have hr := hb.gleit_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i v hv
    obtain ⟨w, hw⟩ := schrumpf_ok hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleit (P := P) (O := O) (passes := passes) hZ.1
      op a b lo hi rest k ρ rfl v (by rw [hW]; exact hv)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_rest hr _ _ _ _ _ hw M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
    exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · cases hex

set_option linter.unusedSectionVars false in
theorem blockOkR_floatLit 
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
    (ih_blockOkR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimOkBR P O passes f fn stapel rho s0 A R rest)
    : SimOkBR P O passes f fn stapel rho s0 A R (.floatLit q lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M k hZ hΛ hA
  have hr := hb.gleitLit_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i v hv
    obtain ⟨w, hw⟩ := schrumpf_ok hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitLit (P := P) (O := O) (passes := passes) hZ.1
      q lo hi rest k ρ rfl v hv
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_rest hr _ _ _ _ _ hw M1 _ hZ1
      hΛ (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
    exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
  · cases hex

set_option linter.unusedSectionVars false in
theorem blockOkR_floatOf 
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
    (ih_blockOkR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimOkBR P O passes f fn stapel rho s0 A R rest)
    : SimOkBR P O passes f fn stapel rho s0 A R (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M k hZ hΛ hA
  have hr := hb.gleitVon_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i v hv
    obtain ⟨w, hw⟩ := schrumpf_ok hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitVon (P := P) (O := O) (passes := passes) hZ.1
      e lo hi rest k ρ rfl v (by rw [hW]; exact hv)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_rest hr _ _ _ _ _ hw M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
    exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · cases hex

set_option linter.unusedSectionVars false in
theorem blockOkR_floatNarrow 
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
    (sonst)
    (rest)
    (hb : BlockR A C mr (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockOkR_rest : ∀ {mr : Bool}, BlockR A C mr rest → SimOkBR P O passes f fn stapel rho s0 A R rest)
    : SimOkBR P O passes f fn stapel rho s0 A R (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M k hZ hΛ hA
  have hr := hb.gleitNarrow_inv.2.1
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i v hv
    obtain ⟨w, hw⟩ := schrumpf_ok hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowOk (P := P) (O := O) (passes := passes)
      hZ.1 e lo hi sonst rest k ρ rfl v (by rw [hW]; exact hv)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_rest hr _ _ _ _ _ hw M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
    exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · exact absurd hex (zuAusgang_ne_ok _ _ _)


end SimOk
end Gabbro.Grammatik
