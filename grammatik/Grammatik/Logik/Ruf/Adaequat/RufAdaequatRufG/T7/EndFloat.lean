module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T2.Teil2EndFloat
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
theorem endRetR_float
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
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
    (hb : EndR A C (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ih_endRetR_rest : EndR A C rest → SimRetER P O passes f fn caller rst rho s0 A R ziel zielG rest)
    : SimRetER P O passes f fn caller rst rho s0 A R ziel zielG (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Endblock D (vertragVon D fn) l Γ Λ) :=
  by
  intro log σ ρ E hpe hex M hZ hΛ hA
  have hr := hb.gleit_inv
  have hW := hZ.welt
  simp only [execEnd] at hex
  split at hex
  · rename_i w hw
    rw [endEnde_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_endeGleit (P := P) (O := O) (passes := passes) hZ.1
      op a b lo hi rest ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_endRetR_rest hr _ _ _ _ hpe hex M1 hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · simp only [EndAusgang.ende?, reduceCtorEq] at hex


theorem endRetR_floatLit
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (q)
    (lo)
    (hi)
    (rest)
    (hb : EndR A C (.floatLit q lo hi rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ih_endRetR_rest : EndR A C rest → SimRetER P O passes f fn caller rst rho s0 A R ziel zielG rest)
    : SimRetER P O passes f fn caller rst rho s0 A R ziel zielG (.floatLit q lo hi rest : Endblock D (vertragVon D fn) l Γ Λ) :=
  by
  intro log σ ρ E hpe hex M hZ hΛ hA
  have hr := hb.gleitLit_inv
  have hW := hZ.welt
  simp only [execEnd] at hex
  split at hex
  · rename_i w hw
    rw [endEnde_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_endeGleitLit (P := P) (O := O) (passes := passes) hZ.1
      q lo hi rest ρ rfl w hw
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
      (ih_endRetR_rest hr _ _ _ _ hpe hex M1 hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))
  · simp only [EndAusgang.ende?, reduceCtorEq] at hex


theorem endRetR_floatOf
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (rest)
    (hb : EndR A C (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ih_endRetR_rest : EndR A C rest → SimRetER P O passes f fn caller rst rho s0 A R ziel zielG rest)
    : SimRetER P O passes f fn caller rst rho s0 A R ziel zielG (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Endblock D (vertragVon D fn) l Γ Λ) :=
  by
  intro log σ ρ E hpe hex M hZ hΛ hA
  have hr := hb.gleitVon_inv
  have hW := hZ.welt
  simp only [execEnd] at hex
  split at hex
  · rename_i w hw
    rw [endEnde_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_endeGleitVon (P := P) (O := O) (passes := passes) hZ.1
      e lo hi rest ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_endRetR_rest hr _ _ _ _ hpe hex M1 hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · simp only [EndAusgang.ende?, reduceCtorEq] at hex


theorem endRetR_floatNarrow
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (sonst)
    (rest)
    (hb : EndR A C (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ih_endRetR_rest : EndR A C rest → SimRetER P O passes f fn caller rst rho s0 A R ziel zielG rest)
    (ih_endRetR_sonst : EndR A C sonst → SimRetER P O passes f fn caller rst rho s0 A R ziel zielG sonst)
    : SimRetER P O passes f fn caller rst rho s0 A R ziel zielG (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Endblock D (vertragVon D fn) l Γ Λ) :=
  by
  intro log σ ρ E hpe hex M hZ hΛ hA
  obtain ⟨hr, hs⟩ := hb.gleitNarrow_inv
  have hW := hZ.welt
  simp only [execEnd] at hex
  split at hex
  · rename_i w hw
    rw [endEnde_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_endeGleitNarrowOk (P := P) (O := O) (passes := passes) hZ.1
      e lo hi sonst rest ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_endRetR_rest hr _ _ _ _ hpe hex M1 hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · rename_i hn
    obtain ⟨M1, hs1, hZ1⟩ := w_endeGleitNarrowElse (P := P) (O := O) (passes := passes) hZ.1
      e lo hi sonst rest ρ rfl (by rw [hW]; exact hn)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_endRetR_sonst hs _ _ _ _ hpe
          hex M1 hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))

theorem alsRetR_float
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
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
    (hb : EndR A C (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ih_alsRetR_rest : EndR A C rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest.alsBlock.2)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Endblock D (vertragVon D fn) l Γ Λ).alsBlock.2 :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  have hr := hb.gleit_inv
  have hW := hZ.welt
  simp only [Endblock.alsBlock, execBlock] at hex
  split at hex
  · rename_i w hw
    rw [ende_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleit (P := P) (O := O) (passes := passes) hZ.1
      op a b lo hi _ k ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_alsRetR_rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · simp only [Ausgang.ende?, reduceCtorEq] at hex


theorem alsRetR_floatLit
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (q)
    (lo)
    (hi)
    (rest)
    (hb : EndR A C (.floatLit q lo hi rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ih_alsRetR_rest : EndR A C rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest.alsBlock.2)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.floatLit q lo hi rest : Endblock D (vertragVon D fn) l Γ Λ).alsBlock.2 :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  have hr := hb.gleitLit_inv
  have hW := hZ.welt
  simp only [Endblock.alsBlock, execBlock] at hex
  split at hex
  · rename_i w hw
    rw [ende_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitLit (P := P) (O := O) (passes := passes) hZ.1
      q lo hi _ k ρ rfl w hw
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
      (ih_alsRetR_rest hr _ _ _ _ hpe hex M1 _ hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))
  · simp only [Ausgang.ende?, reduceCtorEq] at hex


theorem alsRetR_floatOf
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (rest)
    (hb : EndR A C (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ih_alsRetR_rest : EndR A C rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest.alsBlock.2)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Endblock D (vertragVon D fn) l Γ Λ).alsBlock.2 :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  have hr := hb.gleitVon_inv
  have hW := hZ.welt
  simp only [Endblock.alsBlock, execBlock] at hex
  split at hex
  · rename_i w hw
    rw [ende_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitVon (P := P) (O := O) (passes := passes) hZ.1
      e lo hi _ k ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_alsRetR_rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · simp only [Ausgang.ende?, reduceCtorEq] at hex


theorem alsRetR_floatNarrow
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (sonst)
    (rest)
    (hb : EndR A C (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ih_alsRetR_rest : EndR A C rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest.alsBlock.2)
    (ih_alsRetR_sonst : EndR A C sonst → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG sonst.alsBlock.2)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Endblock D (vertragVon D fn) l Γ Λ).alsBlock.2 :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  obtain ⟨hr, hs⟩ := hb.gleitNarrow_inv
  have hW := hZ.welt
  simp only [Endblock.alsBlock, execBlock] at hex
  split at hex
  · rename_i w hw
    rw [ende_schrumpf] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowOk (P := P) (O := O) (passes := passes) hZ.1
      e lo hi sonst _ k ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_alsRetR_rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · rename_i hn
    rw [ende_zuAusgang] at hex
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowElse (P := P) (O := O) (passes := passes) hZ.1
      e lo hi sonst _ k ρ rfl (by rw [hW]; exact hn)
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
      (ih_alsRetR_sonst hs _ _ _ _ hpe
          (by rw [Endblock.execBlock_alsBlock, ende_zuAusgang]; exact hex) M1 _ hZ1 (heldB_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))


end SimRet
end Gabbro.Grammatik
