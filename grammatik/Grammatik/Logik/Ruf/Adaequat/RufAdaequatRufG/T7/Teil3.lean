module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T7.Teil3Basis
import all Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T7.Teil3Basis

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T6
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T7.Teil2

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
theorem blockRetR_narrow 
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
    (hb : BlockR A C true (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockRetR_rest : BlockR A C true rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest)
    (ih_alsRetR_sonst : EndR A C sonst → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG sonst.alsBlock.2)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i hin
    rw [ende_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_narrowOk (P := P) (O := O) (passes := passes) hZ.1
      lo' hi' e sonst rest k ρ rfl hW hin
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_blockRetR_rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · rename_i hin
    rw [ende_zuAusgang] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_narrowElse (P := P) (O := O) (passes := passes) hZ.1
      lo' hi' e sonst rest k ρ rfl (by rw [hW]; exact hin)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_alsRetR_sonst hs _ _ _ _ hpe
          (by rw [Endblock.execBlock_alsBlock, ende_zuAusgang]; exact hex) M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))

set_option linter.unusedSectionVars false in
theorem blockRetR_check 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (sonst)
    (rest)
    (hb : BlockR A C true (.check c sonst rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockRetR_rest : BlockR A C true rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest)
    (ih_alsRetR_sonst : EndR A C sonst → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG sonst.alsBlock.2)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.check c sonst rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i hc
    obtain ⟨M1, hs1, hZ1⟩ := w_pruefWahr (P := P) (O := O) (passes := passes) hZ.1
      c sonst rest k ρ rfl (by rw [hW]; exact hc)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_blockRetR_rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · rename_i hc
    rw [ende_zuAusgang] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_pruefFalsch (P := P) (O := O) (passes := passes) hZ.1
      c sonst rest k ρ rfl (by rw [hW]; simpa using hc)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_alsRetR_sonst hs _ _ _ _ hpe
          (by rw [Endblock.execBlock_alsBlock, ende_zuAusgang]; exact hex) M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))

set_option linter.unusedSectionVars false in
theorem blockRetR_float 
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
    (hb : BlockR A C true (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockRetR_rest : BlockR A C true rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  have hr := hb.gleit_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i w hw
    rw [ende_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleit (P := P) (O := O) (passes := passes) hZ.1
      op a b lo hi rest k ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_blockRetR_rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · simp only [Ausgang.ende?, reduceCtorEq] at hex

set_option linter.unusedSectionVars false in
theorem blockRetR_floatLit 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (q)
    (lo)
    (hi)
    (rest)
    (hb : BlockR A C true (.floatLit q lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockRetR_rest : BlockR A C true rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.floatLit q lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  have hr := hb.gleitLit_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i w hw
    rw [ende_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitLit (P := P) (O := O) (passes := passes) hZ.1
      q lo hi rest k ρ rfl w hw
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
      (ih_blockRetR_rest hr _ _ _ _ hpe hex M1 _ hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))
  · simp only [Ausgang.ende?, reduceCtorEq] at hex

set_option linter.unusedSectionVars false in
theorem blockRetR_floatOf 
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
    (hb : BlockR A C true (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockRetR_rest : BlockR A C true rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  have hr := hb.gleitVon_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i w hw
    rw [ende_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitVon (P := P) (O := O) (passes := passes) hZ.1
      e lo hi rest k ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_blockRetR_rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · simp only [Ausgang.ende?, reduceCtorEq] at hex

set_option linter.unusedSectionVars false in
theorem blockRetR_floatNarrow 
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
    (hb : BlockR A C true (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockRetR_rest : BlockR A C true rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest)
    (ih_alsRetR_sonst : EndR A C sonst → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG sonst.alsBlock.2)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
  have hW := hZ.welt
  simp only [execBlock] at hex
  split at hex
  · rename_i w hw
    rw [ende_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowOk (P := P) (O := O) (passes := passes) hZ.1
      e lo hi sonst rest k ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_blockRetR_rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · rename_i hn
    rw [ende_zuAusgang] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowElse (P := P) (O := O) (passes := passes) hZ.1
      e lo hi sonst rest k ρ rfl (by rw [hW]; exact hn)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_alsRetR_sonst hs _ _ _ _ hpe
          (by rw [Endblock.execBlock_alsBlock, ende_zuAusgang]; exact hex) M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))

set_option linter.unusedSectionVars false in
theorem endRetR_ret 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (hperm)
    (zzh1 : EndR A C (.ret e hperm : Endblock D (vertragVon D fn) l Γ Λ))
    : SimRetER P O passes f fn caller rst rho s0 A R ziel zielG (.ret e hperm : Endblock D (vertragVon D fn) l Γ Λ) :=
  by
  intro log σ ρ E hpe hex M hZ hΛ _
  have hW := hZ.welt
  simp only [execEnd, EndAusgang.ende?, Option.some.injEq] at hex
  subst hex
  obtain ⟨M1, hs1, hG⟩ := w_rueckP (P := P) (O := O) (passes := passes) hZ.1
    caller rst rfl hpe e hperm ρ rfl hΛ.heldIn
  rw [hW] at hG
  exact ⟨M1, [], RufLaufG.einzeln hs1, hG, (Erw.lese _ _ _).offen⟩

end SimRet
end Gabbro.Grammatik
