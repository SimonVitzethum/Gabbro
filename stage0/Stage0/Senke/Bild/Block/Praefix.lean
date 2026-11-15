/- Realize a decomposed end-block prefix up to its final boundary. -/
module
public import Stage0.Senke.Bild.Rek.Lauf
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration} [Kern]

/-- The machine side of a finite source decomposition, independent of image
    memory. In particular, a return proof can start behind a nontrivial callee
    prefix rather than incorrectly identifying that boundary with its entry. -/
theorem randGL_zerlegung {B : BodyFrame D} (hO : Leseblind B.O)
    {Cg : D.Fn → Prop} {thr : Faden} {stapel : List (RufRahmenG D)}
    {rho : Env D (D.params B.f)} {s0 : World D} {Agl : D.Lock → Prop}
    (hRuf : RufOkGleich B.P B.O B.passes thr Agl B.R Cg) {l : Bool} {Γ Γe : Ctx}
    {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ}
    {ebe : Endblock D (vertragVon D B.f) l Γe Λe} {σ σe : World D}
    {ρ : Env D Γ} {ρe : Env D Γe} (hk : Zerlegung B Agl Cg eb σ ρ ebe σe ρe)
    {M : RufMaschineG D} (h : RandGL thr stapel B.f rho s0 Agl eb M σ ρ) :
    ∃ Me, RufLaufG B.P B.O B.passes thr M Me ∧ RandGL thr stapel B.f rho s0 Agl ebe Me σe ρe := by
  induction hk generalizing M with
  | halt eb σ ρ => exact ⟨M, RufLaufG.refl M, h⟩
  | schritt s rest ebe σ σ1 σe ρ ρ1 ρe hs hex _ ih =>
    obtain ⟨M1, hl, h1⟩ := randGL_schritt hO.rs hRuf hs hex h
    obtain ⟨Me, hl', he⟩ := ih h1
    exact ⟨Me, hl.trans hl', he⟩
  | bind e rest ebe σ σe ρ ρe _ ih =>
    obtain ⟨M1, hl, h1⟩ := randGL_bind (P := B.P) (O := B.O) (passes := B.passes) h
    obtain ⟨Me, hl', he⟩ := ih h1
    exact ⟨Me, hl.trans hl', he⟩

/-- The finite decomposition reaches its endpoint on both sides. This is useful
    when descending into the final statement rather than executing it as a whole. -/
theorem randL_zerlegung {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] [LeseblindOK B.O]
    (hB : B.Ok) {Cg : D.Fn → Prop} {thr : Faden} {stapel : List (RufRahmenG D)}
    {rho : Env D (D.params B.f)} {s0 : World D} {Agl : D.Lock → Prop}
    (hRuf : RufOkGleich B.P B.O B.passes thr Agl B.R Cg) {l : Bool} {Γ Γe : Ctx}
    {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ}
    {ebe : Endblock D (vertragVon D B.f) l Γe Λe} {σ σe : World D}
    {ρ : Env D Γ} {ρe : Env D Γe} (hk : Zerlegung B Agl Cg eb σ ρ ebe σe ρe)
    {pc : Runner.W} {m : Runner.Mem} {M : RufMaschineG D}
    (h : RandL B thr stapel rho s0 Agl eb pc m M σ ρ) :
    ∃ (pce : Runner.W) (me : Runner.Mem) (Me : RufMaschineG D),
      Star ⟨pc, B.fp⟩ m ⟨pce, B.fp⟩ me ∧ RufLaufG B.P B.O B.passes thr M Me ∧
      RandL B thr stapel rho s0 Agl ebe pce me Me σe ρe := by
  induction hk generalizing pc m M with
  | halt eb σ ρ => exact ⟨pc, m, M, Star.refl _ _, RufLaufG.refl M, h⟩
  | schritt s rest ebe σ σ1 σe ρ ρ1 ρe hs hex _ ih =>
    obtain ⟨n, m1, M1, st, _, hl, h1⟩ := randL_schritt hB hRuf hs hex h
    obtain ⟨pce, me, Me, st', hl', he⟩ := ih h1
    exact ⟨pce, me, Me, st.trans st', hl.trans hl', he⟩
  | bind e rest ebe σ σe ρ ρe _ ih =>
    obtain ⟨n, m1, M1, st, _, hl, h1⟩ := randL_bind hB h
    obtain ⟨pce, me, Me, st', hl', he⟩ := ih h1
    exact ⟨pce, me, Me, st.trans st', hl.trans hl', he⟩

end Gabbro.Stage0.Senke.BildLauf
