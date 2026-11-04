module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T2.Teil2EndFloat

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T4
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T5.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section SimRet
variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (rho : Env D (D.params fn))
  (s0 : World D) (log : List (RufEreignisF D)) (A : D.Lock → Prop)
variable (hnw : caller.wartend = false)
include hnw
-- `hnw` is used at the returns; `blockRet` and the arm recursions reach it
-- only through `stmtRet`/`endRet`, which the linter does not count as a use.
set_option linter.unusedSectionVars false

theorem endRet_float {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 l2 h2 : Int × Int} (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2)) (lo hi : Int × Int)
    (rest : Endblock D (vertragVon D fn) l (.fl lo hi :: Γ) Λ)
    (hb : EndG A (.float op a b lo hi rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ihRest : EndG A rest → SimRetE P O passes f fn caller rst rho s0 log A rest)
    : SimRetE P O passes f fn caller rst rho s0 log A (.float op a b lo hi rest : Endblock D (vertragVon D fn) l Γ Λ) := by

  intro σ σ' ρ v hex M hZ hΛ hA
  have hr := hb.gleit_inv
  have hW := hZ.welt
  simp only [execEnd] at hex
  split at hex
  · rename_i w hw
    obtain ⟨M1, hs1, hZ1⟩ := w_endeGleit (P := P) (O := O) (passes := passes) hZ.1
      op a b lo hi rest ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
      (ihRest hr _ _ _ _ (endSchrumpf_zurueck hex) M1 hZ1 (heldGenau_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · cases hex

theorem endRet_floatLit {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (q : Int × Int) (lo hi : Int × Int)
    (rest : Endblock D (vertragVon D fn) l (.fl lo hi :: Γ) Λ)
    (hb : EndG A (.floatLit q lo hi rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ihRest : EndG A rest → SimRetE P O passes f fn caller rst rho s0 log A rest)
    : SimRetE P O passes f fn caller rst rho s0 log A (.floatLit q lo hi rest : Endblock D (vertragVon D fn) l Γ Λ) := by

  intro σ σ' ρ v hex M hZ hΛ hA
  have hr := hb.gleitLit_inv
  have hW := hZ.welt
  simp only [execEnd] at hex
  split at hex
  · rename_i w hw
    obtain ⟨M1, hs1, hZ1⟩ := w_endeGleitLit (P := P) (O := O) (passes := passes) hZ.1
      q lo hi rest ρ rfl w hw
    rw [hW] at hZ1
    exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
      (ihRest hr _ _ _ _ (endSchrumpf_zurueck hex) M1 hZ1 hΛ
        (hA.lauf (RufLaufG.einzeln hs1)))
  · cases hex

theorem endRet_floatOf {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 : Int} (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
    (rest : Endblock D (vertragVon D fn) l (.fl lo hi :: Γ) Λ)
    (hb : EndG A (.floatOf e lo hi rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ihRest : EndG A rest → SimRetE P O passes f fn caller rst rho s0 log A rest)
    : SimRetE P O passes f fn caller rst rho s0 log A (.floatOf e lo hi rest : Endblock D (vertragVon D fn) l Γ Λ) := by

  intro σ σ' ρ v hex M hZ hΛ hA
  have hr := hb.gleitVon_inv
  have hW := hZ.welt
  simp only [execEnd] at hex
  split at hex
  · rename_i w hw
    obtain ⟨M1, hs1, hZ1⟩ := w_endeGleitVon (P := P) (O := O) (passes := passes) hZ.1
      e lo hi rest ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
      (ihRest hr _ _ _ _ (endSchrumpf_zurueck hex) M1 hZ1 (heldGenau_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · cases hex

theorem endRet_floatNarrow {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 : Int × Int} (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int)
    (sonst : Endblock D (vertragVon D fn) l Γ Λ)
    (rest : Endblock D (vertragVon D fn) l (.fl lo hi :: Γ) Λ)
    (hb : EndG A (.floatNarrow e lo hi sonst rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ihRest : EndG A rest → SimRetE P O passes f fn caller rst rho s0 log A rest)
    (ihSonst : EndG A sonst → SimRetE P O passes f fn caller rst rho s0 log A sonst)
    : SimRetE P O passes f fn caller rst rho s0 log A (.floatNarrow e lo hi sonst rest : Endblock D (vertragVon D fn) l Γ Λ) := by

  intro σ σ' ρ v hex M hZ hΛ hA
  obtain ⟨hr, hs⟩ := hb.gleitNarrow_inv
  have hW := hZ.welt
  simp only [execEnd] at hex
  split at hex
  · rename_i w hw
    obtain ⟨M1, hs1, hZ1⟩ := w_endeGleitNarrowOk (P := P) (O := O) (passes := passes) hZ.1
      e lo hi sonst rest ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
      (ihRest hr _ _ _ _ (endSchrumpf_zurueck hex) M1 hZ1 (heldGenau_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · rename_i hn
    obtain ⟨M1, hs1, hZ1⟩ := w_endeGleitNarrowElse (P := P) (O := O) (passes := passes) hZ.1
      e lo hi sonst rest ρ rfl (by rw [hW]; exact hn)
    rw [hW] at hZ1
    exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
      (ihSonst hs _ _ _ _ hex M1 hZ1
          (heldGenau_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))


theorem alsRet_float {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 l2 h2 : Int × Int} (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2)) (lo hi : Int × Int)
    (rest : Endblock D (vertragVon D fn) l (.fl lo hi :: Γ) Λ)
    (hb : EndG A (.float op a b lo hi rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ihRest : EndG A rest → SimRetB P O passes f fn caller rst rho s0 log A rest.alsBlock.2)
    : SimRetB P O passes f fn caller rst rho s0 log A (.float op a b lo hi rest : Endblock D (vertragVon D fn) l Γ Λ).alsBlock.2 := by

  intro σ σ' ρ v hex M k hZ hΛ hA
  have hr := hb.gleit_inv
  have hW := hZ.welt
  simp only [Endblock.alsBlock, execBlock] at hex
  split at hex
  · rename_i w hw
    obtain ⟨M1, hs1, hZ1⟩ := w_gleit (P := P) (O := O) (passes := passes) hZ.1
      op a b lo hi _ k ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
      (ihRest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · cases hex

theorem alsRet_floatLit {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (q : Int × Int) (lo hi : Int × Int)
    (rest : Endblock D (vertragVon D fn) l (.fl lo hi :: Γ) Λ)
    (hb : EndG A (.floatLit q lo hi rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ihRest : EndG A rest → SimRetB P O passes f fn caller rst rho s0 log A rest.alsBlock.2)
    : SimRetB P O passes f fn caller rst rho s0 log A (.floatLit q lo hi rest : Endblock D (vertragVon D fn) l Γ Λ).alsBlock.2 := by

  intro σ σ' ρ v hex M k hZ hΛ hA
  have hr := hb.gleitLit_inv
  have hW := hZ.welt
  simp only [Endblock.alsBlock, execBlock] at hex
  split at hex
  · rename_i w hw
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitLit (P := P) (O := O) (passes := passes) hZ.1
      q lo hi _ k ρ rfl w hw
    rw [hW] at hZ1
    exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
      (ihRest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 hΛ
        (hA.lauf (RufLaufG.einzeln hs1)))
  · cases hex

theorem alsRet_floatOf {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 : Int} (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
    (rest : Endblock D (vertragVon D fn) l (.fl lo hi :: Γ) Λ)
    (hb : EndG A (.floatOf e lo hi rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ihRest : EndG A rest → SimRetB P O passes f fn caller rst rho s0 log A rest.alsBlock.2)
    : SimRetB P O passes f fn caller rst rho s0 log A (.floatOf e lo hi rest : Endblock D (vertragVon D fn) l Γ Λ).alsBlock.2 := by

  intro σ σ' ρ v hex M k hZ hΛ hA
  have hr := hb.gleitVon_inv
  have hW := hZ.welt
  simp only [Endblock.alsBlock, execBlock] at hex
  split at hex
  · rename_i w hw
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitVon (P := P) (O := O) (passes := passes) hZ.1
      e lo hi _ k ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
      (ihRest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · cases hex

theorem alsRet_floatNarrow {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 : Int × Int} (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int)
    (sonst : Endblock D (vertragVon D fn) l Γ Λ)
    (rest : Endblock D (vertragVon D fn) l (.fl lo hi :: Γ) Λ)
    (hb : EndG A (.floatNarrow e lo hi sonst rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ihRest : EndG A rest → SimRetB P O passes f fn caller rst rho s0 log A rest.alsBlock.2)
    (ihSonst : EndG A sonst → SimRetB P O passes f fn caller rst rho s0 log A sonst.alsBlock.2)
    : SimRetB P O passes f fn caller rst rho s0 log A (.floatNarrow e lo hi sonst rest : Endblock D (vertragVon D fn) l Γ Λ).alsBlock.2 := by

  intro σ σ' ρ v hex M k hZ hΛ hA
  obtain ⟨hr, hs⟩ := hb.gleitNarrow_inv
  have hW := hZ.welt
  simp only [Endblock.alsBlock, execBlock] at hex
  split at hex
  · rename_i w hw
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowOk (P := P) (O := O) (passes := passes) hZ.1
      e lo hi sonst _ k ρ rfl w (by rw [hW]; exact hw)
    rw [hW] at hZ1
    exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
      (ihRest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))
  · rename_i hn
    obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowElse (P := P) (O := O) (passes := passes) hZ.1
      e lo hi sonst _ k ρ rfl (by rw [hW]; exact hn)
    rw [hW] at hZ1
    exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
      (ihSonst hs _ _ _ _
          (by rw [Endblock.execBlock_alsBlock, zuAusgang_zurueck hex]; rfl) M1 _ hZ1
          (heldGenau_lese _ hΛ)
        (hA.lauf (RufLaufG.einzeln hs1)))



end SimRet
end Gabbro.Grammatik
