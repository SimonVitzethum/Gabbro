/- Structural entry into an if branch, on the image and machine G. -/
module
public import Stage0.Senke.Bild.Block.Wahl
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-- A conditional in block position takes exactly the branch selected by the
    sequential read world, even when machine G's trace has fewer contract reads. -/
theorem randDannGL_ite {P : Programm D} {O : Orakel D} {passes : Nat}
    {thr : Faden} {stapel : List (RufRahmenG D)} {f : D.Fn}
    {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} {cnd : Expr D Γ Λ .bool}
    {t e : Block D (vertragVon D f) l Γ Λ Λ'} {rest : Block D (vertragVon D f) l Γ Λ' Λ''}
    {k : GRest D (vertragVon D f) l Γ Λ''} {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ}
    {take : Bool} (h : RandDannGL thr stapel f rho s0 Agl (.cons (.ite cnd t e) rest) k M σ ρ)
    (hb : wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ) = take) :
    ∃ M2, RufLaufG P O passes thr M M2 ∧
      RandDannGL thr stapel f rho s0 Agl (if take then t else e) (.dann rest k) M2
        (σ.lese Λ cnd.orte) ρ := by
  obtain ⟨σm, hw, ⟨log, hZ⟩, hΛ, hA⟩ := h
  have hw' := hw.lese Λ cnd.orte
  have hbm : wahr? (eval (σm.lese Λ cnd.orte) cnd (σm.lese Λ cnd.orte) ρ) = take := by
    rw [← hw'.wert' cnd ρ]
    exact hb
  have hW := hZ.welt
  cases take with
  | true =>
    obtain ⟨M2, hs, hZ2⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ.1
      cnd t e rest k ρ rfl (by simpa only [hW] using hbm) hΛ.heldIn
    rw [hW] at hZ2
    have hl := RufLaufG.einzeln hs
    exact ⟨M2, hl, σm.lese Λ cnd.orte, hw', ⟨_, hZ2⟩, heldB_lese cnd.orte hΛ, hA.lauf hl⟩
  | false =>
    obtain ⟨M2, hs, hZ2⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ.1
      cnd t e rest k ρ rfl (by simpa only [hW] using hbm) hΛ.heldIn
    rw [hW] at hZ2
    have hl := RufLaufG.einzeln hs
    exact ⟨M2, hl, σm.lese Λ cnd.orte, hw', ⟨_, hZ2⟩, heldB_lese cnd.orte hΛ, hA.lauf hl⟩

/-- Unfold an end-block statement into the machine's block representation. This
    step executes no image instruction and changes no world or environment. -/
theorem randGL_entf {P : Programm D} {O : Orakel D} {passes : Nat}
    {thr : Faden} {stapel : List (RufRahmenG D)} {f : D.Fn}
    {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D f) l Γ Λ Λ'} {rest : Endblock D (vertragVon D f) l Γ Λ'}
    {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ}
    (h : RandGL thr stapel f rho s0 Agl (.cons s rest) M σ ρ) (hs : GEntfaltbar s = true) :
    ∃ M1, RufLaufG P O passes thr M M1 ∧
      RandDannGL thr stapel f rho s0 Agl (.cons s .nil) (.ende rest) M1 σ ρ := by
  obtain ⟨σm, hw, ⟨⟨log, hZ⟩, hΛ, hA⟩⟩ := h
  have hW := hZ.welt
  obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := P) (O := O) (passes := passes)
    hZ.1 s rest ρ hs rfl
  rw [hW] at hZ1
  have hl := RufLaufG.einzeln hs1
  exact ⟨M1, hl, σm, hw, ⟨_, hZ1⟩, hΛ, hA.lauf hl⟩

variable [Kern]

/-- A branch boundary reached from the enclosing end block. The frame's suffix
    offsets are the actual lengths of the skipped enclosing code; every other
    frame field, including depth, protected slots and pending releases, is retained. -/
theorem randL_ite_eintritt {B : BodyFrame D} (hB : B.Ok)
    {thr : Faden} {stapel : List (RufRahmenG D)} {rho : Env D (D.params B.f)}
    {s0 : World D} {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cnd : Expr D Γ Λ .bool} {t e : Block D (vertragVon D B.f) l Γ Λ Λ'}
    {rest : Endblock D (vertragVon D B.f) l Γ Λ'}
    {pc : Runner.W} {m : Runner.Mem} {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ} {take : Bool}
    (h : RandL B thr stapel rho s0 Agl (.cons (.ite cnd t e) rest) pc m M σ ρ)
    (hb : wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ) = take) :
    ∃ (n1 n2 : Nat) (pc2 : Runner.W) (m2 : Runner.Mem) (M2 : RufMaschineG D),
      Star ⟨pc, B.fp⟩ m ⟨pc2, B.fp⟩ m2 ∧ RufLaufG B.P B.O B.passes thr M M2 ∧
      RandDannL ((B.suffix n1).suffix n2) thr stapel rho s0 Agl (if take then t else e)
        (.dann .nil (.ende rest)) pc2 m2 M2 (σ.lese Λ cnd.orte) ρ := by
  obtain ⟨n1, hS⟩ := BodyFrame.randIR_stmt h.1
  obtain ⟨n2, pc2, m2, hs2, hB2⟩ := BodyFrame.randSIR_ite (hB.suffix n1) hS hb
  obtain ⟨M1, hl1, hG1⟩ := randGL_entf (P := B.P) (O := B.O) (passes := B.passes) h.2 rfl
  obtain ⟨M2, hl2, hG2⟩ := randDannGL_ite (P := B.P) (O := B.O) (passes := B.passes) hG1 hb
  exact ⟨n1, n2, pc2, m2, M2, hs2, hl1.trans hl2, hB2, hG2⟩

/-- The same structural descent at an already nested block boundary. -/
theorem randDannL_ite_eintritt {B : BodyFrame D} (hB : B.Ok)
    {thr : Faden} {stapel : List (RufRahmenG D)} {rho : Env D (D.params B.f)}
    {s0 : World D} {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    {cnd : Expr D Γ Λ .bool} {t e : Block D (vertragVon D B.f) l Γ Λ Λ'}
    {rest : Block D (vertragVon D B.f) l Γ Λ' Λ''} {k : GRest D (vertragVon D B.f) l Γ Λ''}
    {pc : Runner.W} {m : Runner.Mem} {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ} {take : Bool}
    (h : RandDannL B thr stapel rho s0 Agl (.cons (.ite cnd t e) rest) k pc m M σ ρ)
    (hb : wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ) = take) :
    ∃ (n1 n2 : Nat) (pc2 : Runner.W) (m2 : Runner.Mem) (M2 : RufMaschineG D),
      Star ⟨pc, B.fp⟩ m ⟨pc2, B.fp⟩ m2 ∧ RufLaufG B.P B.O B.passes thr M M2 ∧
      RandDannL ((B.suffix n1).suffix n2) thr stapel rho s0 Agl (if take then t else e)
        (.dann rest k) pc2 m2 M2 (σ.lese Λ cnd.orte) ρ := by
  obtain ⟨n1, hS⟩ := BodyFrame.randBIR_stmt h.1
  obtain ⟨n2, pc2, m2, hs2, hB2⟩ := BodyFrame.randSIR_ite (hB.suffix n1) hS hb
  obtain ⟨M2, hl2, hG2⟩ := randDannGL_ite (P := B.P) (O := B.O) (passes := B.passes) h.2 hb
  exact ⟨n1, n2, pc2, m2, M2, hs2, hl2, hB2, hG2⟩

#print axioms randL_ite_eintritt
#print axioms randDannL_ite_eintritt

end Gabbro.Stage0.Senke.BildLauf
