/-
  File:      Grammatik/CFormenDet.lean
  Subject:   The C semantics of the emitted forms is DETERMINISTIC (given
             deterministic call meanings), so the correspondence lemmas of
             T4 -- "the C statement has a run related to the Gabbro
             outcome" -- speak about THE run: every run of the emitted C
             is that one (`stmtCorr_jeder`, `blockSem_jeder`).

  This closes the CUT "no determinism theorem for `Exec`" of
  `CFormen.lean`. The call meanings are premises: the unit's own calls
  (`CallAt`) are proved functional here by induction on the depth; a
  foreign call's meaning is an assumption and its functionality is one
  too (`CCallR.Funktional`).
-/
import Grammatik.CFormenI

namespace Gabbro.Grammatik

/-- A call meaning answers at most one way. -/
def CCallR.Funktional (CR : CCallR) : Prop :=
  ∀ f st vs st1 rv1 st2 rv2, CR f st vs st1 rv1 → CR f st vs st2 rv2 → st1 = st2 ∧ rv1 = rv2

/-- A loop body's outcome either continues the loop or ends it, never both. -/
theorem weiter_raus (m : Nat) (o : COut) (p : CSt × CLok) (o' : COut) (h1 : o.weiter m = some p)
    (h2 : o.raus m = some o') : False := by
  cases o with
  | norm s r => simp [COut.raus] at h2
  | cont s r => simp [COut.raus] at h2
  | ret s v => simp [COut.weiter] at h1
  | brk s r => simp [COut.weiter] at h1
  | jump lb s r =>
      cases lb with
      | ende m' => simp [COut.weiter] at h1
      | weiter m' =>
          simp only [COut.weiter] at h1
          simp only [COut.raus] at h2
          by_cases hm : m' = m
          · rw [if_pos hm] at h2; exact absurd h2 (by simp)
          · rw [if_neg hm] at h1; exact absurd h1 (by simp)

section Det

variable {L : CLayout} {orc : DevOrc} {fr : Nat} {CR XR : CCallR}

/-- THE STATEMENT SEMANTICS IS DETERMINISTIC. -/
theorem exec_det (hCR : CR.Funktional) (hXR : XR.Funktional) :
    ∀ {cs : CS} {st : CSt} {ρ : CLok} {o1 : COut}, Exec L orc fr CR XR cs st ρ o1 →
      ∀ {o2 : COut}, Exec L orc fr CR XR cs st ρ o2 → o1 = o2 := by
  intro cs st ρ o1 h1
  induction h1 with
  | skip => intro o2 h2; cases h2; rfl
  | seqN _ _ iha ihb =>
      intro o2 h2
      cases h2 with
      | seqN h2a h2b =>
          have e := iha h2a
          simp only [COut.norm.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          exact ihb h2b
      | seqX h2a hx =>
          have e := iha h2a
          subst e
          simp [COut.abrupt] at hx
  | seqX _ hx iha =>
      intro o2 h2
      cases h2 with
      | seqN h2a _ =>
          have e := iha h2a
          subst e
          simp [COut.abrupt] at hx
      | seqX h2a _ => exact iha h2a
  | expr h =>
      intro o2 h2
      cases h2 with
      | expr h' =>
          rw [h] at h'
          simp only [Option.some.injEq, Prod.mk.injEq] at h'
          rw [h'.2]
  | set h hc =>
      intro o2 h2
      cases h2 with
      | set h' hc' =>
          rw [h] at h'
          simp only [Option.some.injEq, Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rw [hc] at hc'
          simp only [Option.some.injEq] at hc'
          rw [hc']
  | store hp he hc hs =>
      intro o2 h2
      cases h2 with
      | store hp' he' hc' hs' =>
          rw [hp] at hp'
          simp only [Option.some.injEq, Prod.mk.injEq, CVal.ptr.injEq] at hp'
          obtain ⟨rfl, rfl⟩ := hp'
          rw [he] at he'
          simp only [Option.some.injEq, Prod.mk.injEq] at he'
          obtain ⟨rfl, rfl⟩ := he'
          rw [hc] at hc'
          simp only [Option.some.injEq] at hc'
          subst hc'
          rw [hs] at hs'
          simp only [Option.some.injEq] at hs'
          rw [hs']
  | vstore hp he hc hs =>
      intro o2 h2
      cases h2 with
      | vstore hp' he' hc' hs' =>
          rw [hp] at hp'
          simp only [Option.some.injEq, Prod.mk.injEq, CVal.ptr.injEq] at hp'
          obtain ⟨rfl, rfl⟩ := hp'
          rw [he] at he'
          simp only [Option.some.injEq, Prod.mk.injEq] at he'
          obtain ⟨rfl, rfl⟩ := he'
          rw [hc] at hc'
          simp only [Option.some.injEq, CVal.int.injEq] at hc'
          subst hc'
          rw [hs] at hs'
          simp only [Option.some.injEq] at hs'
          rw [hs']
  | astore hp he hc hs =>
      intro o2 h2
      cases h2 with
      | astore hp' he' hc' hs' =>
          rw [hp] at hp'
          simp only [Option.some.injEq, Prod.mk.injEq, CVal.ptr.injEq] at hp'
          obtain ⟨rfl, rfl⟩ := hp'
          rw [he] at he'
          simp only [Option.some.injEq, Prod.mk.injEq] at he'
          obtain ⟨rfl, rfl⟩ := he'
          rw [hc] at hc'
          simp only [Option.some.injEq, CVal.int.injEq] at hc'
          subst hc'
          rw [hs] at hs'
          simp only [Option.some.injEq] at hs'
          rw [hs']
  | acas hp hx hd hc hl ha hw =>
      intro o2 h2
      cases h2 with
      | acas hp' hx' hd' hc' hl' ha' hw' =>
          rw [hp] at hp'
          simp only [Option.some.injEq, Prod.mk.injEq, CVal.ptr.injEq] at hp'
          obtain ⟨rfl, rfl⟩ := hp'
          rw [hx] at hx'
          simp only [Option.some.injEq, Prod.mk.injEq, CVal.ptr.injEq] at hx'
          obtain ⟨rfl, rfl⟩ := hx'
          rw [hd] at hd'
          simp only [Option.some.injEq, Prod.mk.injEq] at hd'
          obtain ⟨rfl, rfl⟩ := hd'
          rw [hc] at hc'
          simp only [Option.some.injEq, CVal.int.injEq] at hc'
          subst hc'
          rw [hl] at hl'
          simp only [Option.some.injEq, CVal.int.injEq] at hl'
          subst hl'
          rw [ha] at ha'
          simp only [Option.some.injEq, Prod.mk.injEq] at ha'
          obtain ⟨rfl, rfl, rfl⟩ := ha'
          rw [hw] at hw'
          simp only [Option.some.injEq] at hw'
          rw [hw']
  | iteT hc ht _ ih =>
      intro o2 h2
      cases h2 with
      | iteT hc' _ h' =>
          rw [hc] at hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨rfl, rfl⟩ := hc'
          exact ih h'
      | iteF hc' hf' _ =>
          rw [hc] at hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨rfl, rfl⟩ := hc'
          rw [ht] at hf'
          simp at hf'
  | iteF hc hf _ ih =>
      intro o2 h2
      cases h2 with
      | iteT hc' ht' _ =>
          rw [hc] at hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨rfl, rfl⟩ := hc'
          rw [hf] at ht'
          simp at ht'
      | iteF hc' _ h' =>
          rw [hc] at hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨rfl, rfl⟩ := hc'
          exact ih h'
  | swHit he hl _ ih =>
      intro o2 h2
      cases h2 with
      | swHit he' hl' h' =>
          rw [he] at he'
          simp only [Option.some.injEq, Prod.mk.injEq, CVal.int.injEq] at he'
          obtain ⟨rfl, rfl⟩ := he'
          rw [hl] at hl'
          simp only [Option.some.injEq] at hl'
          subst hl'
          rw [ih h']
      | swMiss he' hl' =>
          rw [he] at he'
          simp only [Option.some.injEq, Prod.mk.injEq, CVal.int.injEq] at he'
          obtain ⟨rfl, rfl⟩ := he'
          rw [hl] at hl'
          simp at hl'
  | swMiss he hl =>
      intro o2 h2
      cases h2 with
      | swHit he' hl' _ =>
          rw [he] at he'
          simp only [Option.some.injEq, Prod.mk.injEq, CVal.int.injEq] at he'
          obtain ⟨rfl, rfl⟩ := he'
          rw [hl] at hl'
          simp at hl'
      | swMiss he' _ =>
          rw [he] at he'
          simp only [Option.some.injEq, Prod.mk.injEq, CVal.int.injEq] at he'
          obtain ⟨rfl, rfl⟩ := he'
          rfl
  | retN => intro o2 h2; cases h2; rfl
  | retS he hc =>
      intro o2 h2
      cases h2 with
      | retS he' hc' =>
          rw [he] at he'
          simp only [Option.some.injEq, Prod.mk.injEq] at he'
          obtain ⟨rfl, rfl⟩ := he'
          rw [hc] at hc'
          simp only [Option.some.injEq] at hc'
          rw [hc']
  | brk => intro o2 h2; cases h2; rfl
  | cont => intro o2 h2; cases h2; rfl
  | goto => intro o2 h2; cases h2; rfl
  | forDone hc hf =>
      intro o2 h2
      cases h2 with
      | forDone hc' _ =>
          rw [hc] at hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨rfl, rfl⟩ := hc'
          rfl
      | forStep hc' ht' _ _ _ _ =>
          rw [hc] at hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨rfl, rfl⟩ := hc'
          rw [hf] at ht'
          simp at ht'
      | forExit hc' ht' _ _ =>
          rw [hc] at hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨rfl, rfl⟩ := hc'
          rw [hf] at ht'
          simp at ht'
  | forStep hc ht _ hw _ _ ihb ihs ihr =>
      intro o2 h2
      cases h2 with
      | forDone hc' hf' =>
          rw [hc] at hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨rfl, rfl⟩ := hc'
          rw [ht] at hf'
          simp at hf'
      | forStep hc' _ hb' hw' hs' hr' =>
          rw [hc] at hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨rfl, rfl⟩ := hc'
          have e := ihb hb'
          subst e
          rw [hw] at hw'
          simp only [Option.some.injEq, Prod.mk.injEq] at hw'
          obtain ⟨rfl, rfl⟩ := hw'
          have e2 := ihs hs'
          simp only [COut.norm.injEq] at e2
          obtain ⟨rfl, rfl⟩ := e2
          exact ihr hr'
      | forExit hc' _ hb' hx' =>
          rw [hc] at hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨rfl, rfl⟩ := hc'
          have e := ihb hb'
          subst e
          exact (weiter_raus _ _ _ _ hw hx').elim
  | forExit hc ht _ hx ihb =>
      intro o2 h2
      cases h2 with
      | forDone hc' hf' =>
          rw [hc] at hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨rfl, rfl⟩ := hc'
          rw [ht] at hf'
          simp at hf'
      | forStep hc' _ hb' hw' _ _ =>
          rw [hc] at hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨rfl, rfl⟩ := hc'
          have e := ihb hb'
          subst e
          exact (weiter_raus _ _ _ _ hw' hx).elim
      | forExit hc' _ hb' hx' =>
          rw [hc] at hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨rfl, rfl⟩ := hc'
          have e := ihb hb'
          subst e
          rw [hx] at hx'
          simp only [Option.some.injEq] at hx'
          exact hx'
  | call ha hc hd =>
      intro o2 h2
      cases h2 with
      | call ha' hc' hd' =>
          rw [ha] at ha'
          simp only [Option.some.injEq, Prod.mk.injEq] at ha'
          obtain ⟨rfl, rfl⟩ := ha'
          obtain ⟨rfl, rfl⟩ := hCR _ _ _ _ _ _ _ hc hc'
          rw [hd] at hd'
          simp only [Option.some.injEq] at hd'
          rw [hd']
  | ext ha hc hd =>
      intro o2 h2
      cases h2 with
      | ext ha' hc' hd' =>
          rw [ha] at ha'
          simp only [Option.some.injEq, Prod.mk.injEq] at ha'
          obtain ⟨rfl, rfl⟩ := ha'
          obtain ⟨rfl, rfl⟩ := hXR _ _ _ _ _ _ _ hc hc'
          rw [hd] at hd'
          simp only [Option.some.injEq] at hd'
          rw [hd']

end Det

/-- The unit's calls are functional at every depth, given a functional
    foreign-call meaning. -/
theorem callAt_funktional (L : CLayout) (orc : DevOrc) (XR : CCallR) (hXR : XR.Funktional)
    (Pr : CProg) : ∀ n, (CallAt L orc XR Pr n).Funktional := by
  intro n
  induction n with
  | zero => intro f st vs st1 rv1 st2 rv2 h1 _; exact h1.elim
  | succ n ih =>
      intro f st vs st1 rv1 st2 rv2 h1 h2
      obtain ⟨F, ρ0, o, hF, hb, hx, s1, ho, hs⟩ := h1
      obtain ⟨F', ρ0', o', hF', hb', hx', s1', ho', hs'⟩ := h2
      rw [hF] at hF'
      simp only [Option.some.injEq] at hF'
      subst hF'
      rw [hb] at hb'
      simp only [Option.some.injEq] at hb'
      subst hb'
      have e := exec_det ih hXR hx hx'
      subst e
      subst hs
      subst hs'
      rcases ho with h | ⟨hr, ρ1, h⟩ <;> rcases ho' with h' | ⟨hr', ρ1', h'⟩
      · rw [h] at h'; simp only [COut.ret.injEq] at h'; obtain ⟨rfl, rfl⟩ := h'; exact ⟨rfl, rfl⟩
      · rw [h] at h'; simp at h'
      · rw [h] at h'; simp at h'
      · rw [h] at h'; simp only [COut.norm.injEq] at h'; obtain ⟨rfl, -⟩ := h'
        exact ⟨rfl, hr.trans hr'.symm⟩

variable {D : Deklaration}

/-- THE CORRESPONDENCE SPEAKS ABOUT EVERY RUN: with functional call
    meanings, every run of the emitted statement ends related to the
    Gabbro outcome. -/
theorem stmtCorr_jeder (X : TVCtx D) (hCR : X.CR.Funktional) (hXR : X.XR.Funktional) (m : Nat)
    {Γ : Ctx} {K : CEnvLay D Γ} {V : Vertrag D} {l : Bool} {Λ Λ' : List (Res D)}
    {s : Stmt D V l Γ Λ Λ'} {cs : CS} (h : StmtCorr X m K s cs) (σ : World D) (st : CSt)
    (ρG : Env D Γ) (ρC : CLok) (hc : corrW X.EL σ st) (hr : EnvRel X.EL K ρG ρC)
    (hnf : (execStmt X.O X.passes X.R s σ ρG).istFehler = false) (o' : COut)
    (hx : Exec X.EL.lay X.orc X.fr X.CR X.XR cs st ρC o') :
    StOut X m K (execStmt X.O X.passes X.R s σ ρG) o' := by
  obtain ⟨o, h1, h2⟩ := h σ st ρG ρC hc hr hnf
  rw [← exec_det hCR hXR h1 hx]
  exact h2

/-- The same for blocks. -/
theorem blockSem_jeder (X : TVCtx D) (hCR : X.CR.Funktional) (hXR : X.XR.Funktional) (m : Nat)
    {Γ : Ctx} {K : CEnvLay D Γ} {V : Vertrag D} {l : Bool} {Λ Λ' : List (Res D)}
    {b : Block D V l Γ Λ Λ'} {cs : CS} (h : BlockSem X m K b cs) (σ : World D) (st : CSt)
    (ρG : Env D Γ) (ρC : CLok) (hc : corrW X.EL σ st) (hr : EnvRel X.EL K ρG ρC)
    (hnf : (execBlock X.O X.passes X.R b σ ρG).istFehler = false) (o' : COut)
    (hx : Exec X.EL.lay X.orc X.fr X.CR X.XR cs st ρC o') :
    StOut X m K (execBlock X.O X.passes X.R b σ ρG) o' := by
  obtain ⟨o, h1, h2⟩ := h σ st ρG ρC hc hr hnf
  rw [← exec_det hCR hXR h1 hx]
  exact h2

#print axioms exec_det
#print axioms callAt_funktional
#print axioms stmtCorr_jeder
#print axioms blockSem_jeder

end Gabbro.Grammatik
