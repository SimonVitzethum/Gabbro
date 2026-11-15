/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Ort/Segment.lean
  Subject:   SEGMENTS (multi-thread image theorem, package MT3, first piece). A segment is the part of a thread's
             decomposed prefix between two synchronisation points: memory statements (`OrtPrem`) and bindings,
             every carrier they read or write in the segment's carriers `C`. A lock, an atomic, a call, a register
             or an outside access is not in it -- there a segment ends (the steps at the synchronisation points are
             the later packages). `Segment` is the decomposed prefix (`Zerlegung`) with these premises; forgetting
             them gives the prefix itself (`segment_zerlegung`), so the single-thread chain P0-P5 applies to a
             segment unchanged.
             THE COMMIT OF A SEGMENT (`randG_segment`): machine G's thread, standing in the CURRENT machine `N` at
             the segment's start with a world `σ'` that agrees on `C` with the world `σ` the chain ran the segment
             from, takes the whole segment by its own steps -- statement by statement (`randG_schritt` on the
             statement's run from the current world, `ort_stmt_ok`), binding by binding (`randG_bind`, the value
             is the same by `OrtGleich.wert`) -- and stands at the segment's end with the thread's own result on
             `C` and the current world everywhere else. `randG_segment_ein` starts from the view machine of the
             chain; `fadenX_segment` lifts the commit to the thread machine over GX.
-/
module
public import Stage0.Senke.Bild.Mehr.Ort.Commit
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildLauf

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-- **A segment**: a decomposed prefix of memory statements and bindings, every carrier in `C`. -/
inductive Segment (O : Orakel D) (passes : Nat) (R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g)
    (Agl : D.Lock → Prop) (Cg : D.Fn → Prop) (C : D.Tab ⊕ D.Glob → Prop) {V : Vertrag D} {l : Bool} :
    {Γ : Ctx} → {Λ : List (Res D)} → Endblock D V l Γ Λ → World D → Env D Γ →
    {Γe : Ctx} → {Λe : List (Res D)} → Endblock D V l Γe Λe → World D → Env D Γe → Prop where
  | halt {Γ : Ctx} {Λ : List (Res D)} (eb : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
      Segment O passes R Agl Cg C eb σ ρ eb σ ρ
  | schritt {Γ Γe : Ctx} {mr : Bool} {Λ Λ' Λe : List (Res D)} (s : Stmt D V l Γ Λ Λ')
      (rest : Endblock D V l Γ Λ') (ebe : Endblock D V l Γe Λe) (σ σ1 σe : World D) (ρ ρ1 : Env D Γ)
      (ρe : Env D Γe) (hs : StmtR Agl Cg mr s) (hC : OrtPrem C s) (hex : execStmt O passes R s σ ρ = .ok σ1 ρ1)
      (hk : Segment O passes R Agl Cg C rest σ1 ρ1 ebe σe ρe) :
      Segment O passes R Agl Cg C (.cons s rest) σ ρ ebe σe ρe
  | bind {Γ Γe : Ctx} {Λ Λe : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (rest : Endblock D V l (τ :: Γ) Λ)
      (ebe : Endblock D V l Γe Λe) (σ σe : World D) (ρ : Env D Γ) (ρe : Env D Γe) (hC : ∀ o ∈ e.orte, C o)
      (hk : Segment O passes R Agl Cg C rest (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) ebe σe ρe) :
      Segment O passes R Agl Cg C (.bind e rest) σ ρ ebe σe ρe

/-- **A segment is a decomposed prefix**: the single-thread chain applies to it unchanged. -/
theorem segment_zerlegung {B : BodyFrame D} {Agl : D.Lock → Prop} {Cg : D.Fn → Prop} {C : D.Tab ⊕ D.Glob → Prop}
    {l : Bool} {Γ Γe : Ctx} {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ}
    {ebe : Endblock D (vertragVon D B.f) l Γe Λe} {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe}
    (hk : Segment B.O B.passes B.R Agl Cg C eb σ ρ ebe σe ρe) : Zerlegung B Agl Cg eb σ ρ ebe σe ρe := by
  induction hk with
  | halt eb σ ρ => exact .halt eb σ ρ
  | schritt s rest ebe σ σ1 σe ρ ρ1 ρe hs _ hex _ ih => exact .schritt s rest ebe σ σ1 σe ρ ρ1 ρe hs hex ih
  | bind e rest ebe σ σe ρ ρe _ _ ih => exact .bind e rest ebe σ σe ρ ρe ih

/-- **THE COMMIT OF A SEGMENT**, from the current machine. -/
theorem randG_segment {P : Programm D} {O : Orakel D} {passes : Nat}
    {R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g} {Cg : D.Fn → Prop} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    (hRuf : RufOk P O passes thr Agl R Cg) {C : D.Tab ⊕ D.Glob → Prop} {l : Bool} {Γ Γe : Ctx}
    {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D f) l Γ Λ} {ebe : Endblock D (vertragVon D f) l Γe Λe}
    {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe} (hk : Segment O passes R Agl Cg C eb σ ρ ebe σe ρe) :
    ∀ {N : RufMaschineG D} {σ' : World D}, RandG thr stapel f rho s0 Agl eb N σ' ρ → OrtGleich C σ σ' →
      ∃ (N' : RufMaschineG D) (σe' : World D), RufLaufG P O passes thr N N' ∧
        RandG thr stapel f rho s0 Agl ebe N' σe' ρe ∧ OrtGleich C σe σe' ∧
        ∀ c, ¬ C c → TraegerGleich σe'.speicher σ'.speicher c := by
  induction hk with
  | halt eb σ ρ =>
    intro N σ' h hσ
    exact ⟨N, σ', .refl N, h, hσ, fun c _ => traegerGleich_refl _ c⟩
  | schritt s rest ebe σ σ1 σe ρ ρ1 ρe hs hC hex _ ih =>
    intro N σ' h hσ
    obtain ⟨σ1', hex', hσ1⟩ := ort_stmt_ok O passes R hC hσ hex
    obtain ⟨N1, hl1, hR1⟩ := randG_schritt hRuf hs hex' h
    obtain ⟨N', σe', hl2, hR2, hσe, hfr⟩ := ih hR1 hσ1
    exact ⟨N', σe', hl1.trans hl2, hR2, hσe,
      fun c hc => traegerGleich_trans (hfr c hc) (ort_rahmen O passes R s hC hex' c hc)⟩
  | @bind _ _ Λ _ _ e rest ebe σ σe ρ ρe hC _ ih =>
    intro N σ' h hσ
    obtain ⟨N1, hl1, hR1⟩ := randG_bind (P := P) (O := O) (passes := passes) h
    have he := (hσ.lese Λ e.orte).wert e hC ρ
    rw [← he] at hR1
    obtain ⟨N', σe', hl2, hR2, hσe, hfr⟩ := ih hR1 (hσ.lese _ e.orte)
    exact ⟨N', σe', hl1.trans hl2, hR2, hσe, fun c hc => traegerGleich_trans (hfr c hc) (traeger_lese σ' _ _ c)⟩

/-- **The commit of a segment from the chain's view machine**: the current machine holds the thread's frame, a
    world agreeing on `C`, and no other holder of a lock the body may take. -/
theorem randG_segment_ein {P : Programm D} {O : Orakel D} {passes : Nat}
    {R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g} {Cg : D.Fn → Prop} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    (hRuf : RufOk P O passes thr Agl R Cg) {C : D.Tab ⊕ D.Glob → Prop} {l : Bool} {Γ Γe : Ctx}
    {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D f) l Γ Λ} {ebe : Endblock D (vertragVon D f) l Γe Λe}
    {σ σe σ' : World D} {ρ : Env D Γ} {ρe : Env D Γe} {M N : RufMaschineG D}
    (hk : Segment O passes R Agl Cg C eb σ ρ ebe σe ρe) (h : RandG thr stapel f rho s0 Agl eb M σ ρ)
    (hσ : OrtGleich C σ σ') (hf : N.faeden thr = M.faeden thr) (hsp : N.speicher = σ'.speicher)
    (hA : FreiA Agl N thr) :
    ∃ (N' : RufMaschineG D) (σe' : World D), RufLaufG P O passes thr N N' ∧
      RandG thr stapel f rho s0 Agl ebe N' σe' ρe ∧ OrtGleich C σe σe' ∧
      ∀ c, ¬ C c → TraegerGleich σe'.speicher σ'.speicher c :=
  randG_segment hRuf hk (randG_umsetzen h hσ.spur hf hsp hA) hσ

/-- **The commit of a segment on the thread machine over GX.** -/
theorem fadenX_segment {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    {R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g} {Cg : D.Fn → Prop} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    (hRuf : RufOk P O passes thr Agl R Cg) {C : D.Tab ⊕ D.Glob → Prop} {l : Bool} {Γ Γe : Ctx}
    {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D f) l Γ Λ} {ebe : Endblock D (vertragVon D f) l Γe Λe}
    {σ σe σ' : World D} {ρ : Env D Γ} {ρe : Env D Γe} {M : RufMaschineG D} {K0 K : FadenMaschine D}
    (hk : Segment O passes R Agl Cg C eb σ ρ ebe σe ρe) (h : RandG thr stapel f rho s0 Agl eb M σ ρ)
    (hσ : OrtGleich C σ σ') (hK : FadenErreichbarX P O passes Tg K0 K) (hl : K.lebt thr = true)
    (hw : K.wartet thr = []) (hf : K.m.faeden thr = M.faeden thr) (hsp : K.m.speicher = σ'.speicher)
    (hA : FreiA Agl K.m thr) :
    ∃ (N' : RufMaschineG D) (σe' : World D),
      FadenErreichbarX P O passes Tg K0 ⟨N', K.lebt, K.wartet, K.rang, K.uhr⟩ ∧
      RandG thr stapel f rho s0 Agl ebe N' σe' ρe ∧ OrtGleich C σe σe' ∧
      ∀ c, ¬ C c → TraegerGleich σe'.speicher σ'.speicher c := by
  obtain ⟨N', σe', hl', hR, hσe, hfr⟩ := randG_segment_ein hRuf hk h hσ hf hsp hA
  exact ⟨N', σe', fadenErreichbarX_lauf' hl' hl hw hK, hR, hσe, hfr⟩

end Gabbro.Stage0.Senke.BildMehr
