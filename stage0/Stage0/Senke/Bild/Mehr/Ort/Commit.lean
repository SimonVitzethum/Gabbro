/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Ort/Commit.lean
  Subject:   THE COMMIT of one memory statement (multi-thread image theorem, package MT2). The single-thread chain
             computes a thread's statement from the world `σ` of its boundary, in its view machine `M`. When the
             segment ends, machine G's thread takes the statement in the CURRENT machine `N` of the thread machine:
             `N` holds the thread's own frame (`N.faeden thr = M.faeden thr`) and a world `σ'` that agrees with `σ`
             on the statement's carriers `C` (other threads committed only elsewhere), and no other thread holds a
             lock the body may take. Then thread `thr` takes the statement's steps in `N` (`randG_ort`, by
             `randG_schritt` from the statement's run on `σ'`, which `ort_stmt_ok` gives), and stands at the next
             boundary with a world `σ1'` that is the thread's own result on `C` (`OrtGleich C σ1 σ1'`) and the
             current world everywhere else (`ort_rahmen`). On the thread machine over GX the steps are `lauf` steps
             of a live, non-joining thread (`fadenX_ort`), so the reachable thread machine stays reachable.
-/
module
public import Stage0.Senke.Bild.Mehr.Ort.Rahmen
public import Stage0.Senke.Bild.Mehr.Faden
public import Stage0.Senke.Bild.Korrespondenz
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildLauf

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-- The boundary of a thread in another machine that holds its frame and a world with the same trace. -/
theorem randG_umsetzen {thr : Faden} {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)}
    {s0 : World D} {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {eb : Endblock D (vertragVon D f) l Γ Λ} {M N : RufMaschineG D} {σ σ' : World D} {ρ : Env D Γ}
    (h : RandG thr stapel f rho s0 Agl eb M σ ρ) (hsp : σ.spur = σ'.spur) (hf : N.faeden thr = M.faeden thr)
    (hs : N.speicher = σ'.speicher) (hA : FreiA Agl N thr) : RandG thr stapel f rho s0 Agl eb N σ' ρ := by
  obtain ⟨⟨log, hZ⟩, hH, _⟩ := h
  refine ⟨⟨log, ?_, hs⟩, ?_, hA⟩
  · rw [hf, hZ.1, hsp]
  · rw [← hsp]
    exact hH

/-- **THE COMMIT, machine G.** -/
theorem randG_ort {P : Programm D} {O : Orakel D} {passes : Nat}
    {R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g} {Cg : D.Fn → Prop} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    (hRuf : RufOk P O passes thr Agl R Cg) {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D f) l Γ Λ Λ'} {rest : Endblock D (vertragVon D f) l Γ Λ'} {M N : RufMaschineG D}
    {C : D.Tab ⊕ D.Glob → Prop} {σ σ' σ1 : World D} {ρ ρ1 : Env D Γ} (hs : StmtR Agl Cg mr s) (hC : OrtPrem C s)
    (hex : execStmt O passes R s σ ρ = .ok σ1 ρ1) (h : RandG thr stapel f rho s0 Agl (.cons s rest) M σ ρ)
    (hσ : OrtGleich C σ σ') (hf : N.faeden thr = M.faeden thr) (hsp : N.speicher = σ'.speicher)
    (hA : FreiA Agl N thr) :
    ∃ (N' : RufMaschineG D) (σ1' : World D), RufLaufG P O passes thr N N' ∧
      RandG thr stapel f rho s0 Agl rest N' σ1' ρ1 ∧ OrtGleich C σ1 σ1' ∧
      ∀ c, ¬ C c → TraegerGleich σ1'.speicher σ'.speicher c := by
  obtain ⟨σ1', hex', hσ1⟩ := ort_stmt_ok O passes R hC hσ hex
  obtain ⟨N', hl, hR'⟩ := randG_schritt hRuf hs hex' (randG_umsetzen h hσ.spur hf hsp hA)
  exact ⟨N', σ1', hl, hR', hσ1, ort_rahmen O passes R s hC hex'⟩

/-- **THE COMMIT, thread machine over GX**: the statement's steps continue a reachable thread machine. -/
theorem fadenX_ort {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    {R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g} {Cg : D.Fn → Prop} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    (hRuf : RufOk P O passes thr Agl R Cg) {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D f) l Γ Λ Λ'} {rest : Endblock D (vertragVon D f) l Γ Λ'} {M : RufMaschineG D}
    {K0 K : FadenMaschine D} {C : D.Tab ⊕ D.Glob → Prop} {σ σ' σ1 : World D} {ρ ρ1 : Env D Γ}
    (hs : StmtR Agl Cg mr s) (hC : OrtPrem C s) (hex : execStmt O passes R s σ ρ = .ok σ1 ρ1)
    (h : RandG thr stapel f rho s0 Agl (.cons s rest) M σ ρ) (hσ : OrtGleich C σ σ')
    (hK : FadenErreichbarX P O passes Tg K0 K) (hl : K.lebt thr = true) (hw : K.wartet thr = [])
    (hf : K.m.faeden thr = M.faeden thr) (hsp : K.m.speicher = σ'.speicher) (hA : FreiA Agl K.m thr) :
    ∃ (N' : RufMaschineG D) (σ1' : World D),
      FadenErreichbarX P O passes Tg K0 ⟨N', K.lebt, K.wartet, K.rang, K.uhr⟩ ∧
      RandG thr stapel f rho s0 Agl rest N' σ1' ρ1 ∧ OrtGleich C σ1 σ1' ∧
      ∀ c, ¬ C c → TraegerGleich σ1'.speicher σ'.speicher c := by
  obtain ⟨N', σ1', hlauf, hR', hσ1, hfr⟩ := randG_ort hRuf hs hC hex h hσ hf hsp hA
  exact ⟨N', σ1', fadenErreichbarX_lauf' hlauf hl hw hK, hR', hσ1, hfr⟩

end Gabbro.Stage0.Senke.BildMehr
