/-
  File:      Grammatik/ArenaErkennerBeweis.lean
  Subject:   THE RECOGNIZER IS SOUND (PLAN-DYNAMISCH.md section 8a.1, step (3)): every body `Erk` accepts keeps the
             structure invariant at EVERY exit, and a body that falls off meets the abstract state it ends in.

    `erk_erhaelt`  -- `Erk a b a'`, `StrukturOk σ` and `StrukturPasst a σ ρ` give `StrukturPost a'` of the run of `b` from `(σ, ρ)`.
    `erk_koerper`  -- the corollary a function needs: a body that knows nothing at entry (every position `offen`).

  The proof is an induction on the derivation. Each case applies the executed-form theorems of `ArenaLinkForm.lean`,
  `ArenaAllocForm.lean` and `ArenaWachs.lean`; their hypotheses (a live and unlinked slot, a member, a non-empty list)
  are exactly what the abstract state `a` says, and the guard of every `narrow`/`check` either passes (the form runs) or
  fails (the `else` branch, which `Rein` forces to be store-free, ends the run in the world the guard saw).
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaErkennerLemmas

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

section Beweis
variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (A : FreiForm D) (L : LinkFeld A) (G : LinkKopf A) {V : Vertrag D} {l : Bool}

/-- The head is a member when the list is non-empty. -/
theorem kopf_auf {σ : World D} (hl : ListOk A L G σ) (hne : G.st σ < D.count A.tab) :
    Auf (D.count A.tab) (L.wert σ) (G.st σ) (G.st σ) := by
  obtain ⟨Ls, hk, -, -⟩ := hl
  exact auf_kopf hne ⟨Ls, hk⟩

/-- **THE RECOGNIZER IS SOUND.** -/
theorem erk_erhaelt {Γ : Ctx} {Λ Λ' : List (Res D)} {a a' : Abs} {b : Block D V l Γ Λ Λ'}
    (h : Erk A L G a b a') :
    ∀ (σ : World D) (ρ : Env D Γ), StrukturOk A L G σ → StrukturPasst A L G a σ ρ →
      StrukturPost A L G a' (execBlock O passes R b σ ρ) := by
  induction h with
  | nil a =>
    intro σ ρ hS hP
    exact ⟨hS, hP⟩
  | @push Γ Λ Λ' a a' x hwT hLT hwG hLG rest hx h ih =>
    intro σ ρ hS hP
    obtain ⟨hlebt, hnot⟩ := hP.1 x hx
    obtain ⟨σ', he, hl', hok', hlebt', hg, hli, hvor, hnach⟩ :=
      liste_push_zug O passes R L G x hwT hLT hwG hLG rest σ ρ hS.2 hS.1 hlebt hnot
    rw [he]
    refine ih σ' ρ ⟨hok', hl'⟩ ⟨?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨hyx, hy'⟩ := Abs.set_frei hy (by decide)
      obtain ⟨hly, hny⟩ := hP.1 y hy'
      refine ⟨(hlebt' _).mpr hly, fun hm => ?_⟩
      rcases hvor _ hm with e | hm'
      · exact hP.2.2 y x hy' hx hyx e
      · exact hny hm'
    · intro y hy
      rcases Abs.set_glied hy with ⟨hyx, -⟩ | ⟨-, hy'⟩
      · have := Var.pos_inj y x hyx
        subst this
        have hne : (ρ.get y).n < D.count A.tab := by
          have := hlebt.2.1; have := A.stand_le σ; omega
        have h0 := kopf_auf A L G hl' (by rw [hg]; exact hne)
        rw [← hg]; exact h0
      · exact hnach _ (hP.2.1 y hy')
    · intro x' y' hx' hy' hne
      exact hP.2.2 x' y' (Abs.set_frei hx' (by decide)).2 (Abs.set_frei hy' (by decide)).2 hne
  | @pop Γ Λ Λ' a a'' hwG hLG hLT voll rest hv h ih =>
    intro σ ρ hS hP
    by_cases hne : G.st σ < D.count A.tab
    · obtain ⟨σ', k, he, hkn, hl', hok', hlebt, hnot, hlebtk, hg, hsub⟩ :=
        liste_pop_zug O passes R L G hwG hLG hLT voll rest σ ρ hS.2 hS.1 hne
      rw [he]
      apply StrukturPost.schrumpf
      have hhead := kopf_auf A L G hS.2 hne
      refine ih σ' (.cons k ρ) ⟨hok', hl'⟩ (StrukturPasst.ext_frei A L G k
        (StrukturPasst.entglied A L G hP (fun y hy => ⟨(hlebt _).mpr (hP.1 y hy).1,
          fun hm => (hP.1 y hy).2 (hsub _ hm)⟩)) hlebtk hnot ?_)
      intro y hy e
      have hy' := (Abs.entglied_frei a y.pos).mp hy
      exact (hP.1 y hy').2 (by rw [e, hkn]; exact hhead)
    · rw [linkPop_voll O passes R L G hwG hLG hLT voll rest σ ρ hne]
      exact Rein.post A L G O passes R hv _ _ ((Gleich.lese A L G σ Λ _).strukturOk A L G hS)
  | @unlink Γ Λ Λ' a a'' p hwT hLT voll rest hp hv h ih =>
    intro σ ρ hS hP
    by_cases hi : L.wert σ (ρ.get p).n < D.count A.tab
    · have hpa := hP.2.1 p hp
      obtain ⟨σ', k, he, hkn, hl', hok', hlebt, hnot, hlebtk, hnp, hsub⟩ :=
        liste_unlink_zug O passes R L G p hwT hLT voll rest σ ρ hS.2 hS.1 hpa hi
      rw [he]
      apply StrukturPost.schrumpf
      have hmem := auf_nach hpa hi
      refine ih σ' (.cons k ρ) ⟨hok', hl'⟩ (StrukturPasst.ext_frei A L G k
        (StrukturPasst.entglied A L G hP (fun y hy => ⟨(hlebt _).mpr (hP.1 y hy).1,
          fun hm => (hP.1 y hy).2 (hsub _ hm)⟩)) hlebtk hnot ?_)
      intro y hy e
      have hy' := (Abs.entglied_frei a y.pos).mp hy
      exact (hP.1 y hy').2 (by rw [e, hkn]; exact hmem)
    · rw [linkUnlink_voll O passes R L p hwT hLT voll rest σ ρ hi]
      exact Rein.post A L G O passes R hv _ _ ((Gleich.lese A L G σ Λ _).strukturOk A L G hS)
  | @kopf Γ Λ Λ' a a'' hLG voll rest hv h ih =>
    intro σ ρ hS hP
    by_cases hne : G.st σ < D.count A.tab
    · obtain ⟨k, he, hkn⟩ := linkKopfBind_ausfuehren O passes R G hLG voll rest σ ρ hne
      rw [he]
      apply StrukturPost.schrumpf
      have hgl := Gleich.lese A L G σ Λ [Sum.inr G.g]
      exact ih _ (.cons k ρ) (hgl.strukturOk A L G hS) (StrukturPasst.ext_glied A L G k (hgl.passt A L G hP)
        ((hgl.auf A L G _).mpr (by rw [hkn]; exact kopf_auf A L G hS.2 hne)))
    · rw [linkKopfBind_voll O passes R G hLG voll rest σ ρ hne]
      exact Rein.post A L G O passes R hv _ _ ((Gleich.lese A L G σ Λ _).strukturOk A L G hS)
  | @nach Γ Λ Λ' a a'' p hLT voll rest hp hv h ih =>
    intro σ ρ hS hP
    by_cases hn : L.wert σ (ρ.get p).n < D.count A.tab
    · obtain ⟨k, he, hkn⟩ := linkNachBind_ausfuehren O passes R L p hLT voll rest σ ρ hn
      rw [he]
      apply StrukturPost.schrumpf
      have hgl := Gleich.lese A L G σ Λ [Sum.inl A.tab]
      exact ih _ (.cons k ρ) (hgl.strukturOk A L G hS) (StrukturPasst.ext_glied A L G k (hgl.passt A L G hP)
        ((hgl.auf A L G _).mpr (by rw [hkn]; exact auf_nach (hP.2.1 p hp) hn)))
    · rw [linkNachBind_voll O passes R L p hLT voll rest σ ρ hn]
      exact Rein.post A L G O passes R hv _ _ ((Gleich.lese A L G σ Λ _).strukturOk A L G hS)
  | @frisch Γ Λ Λ' a a'' v hwT hLT hwG hLG voll rest hv h ih =>
    intro σ ρ hS hP
    by_cases hlt : A.stand σ < D.count A.tab
    · obtain ⟨σ', k, he, hkn, hf, hok', hmono, hnew⟩ :=
        frischAlloc_ausfuehren O passes R A v hwT hLT hwG hLG voll rest σ ρ hlt hS.1
      rw [he]
      apply StrukturPost.schrumpf
      have hnot : ¬ Auf (D.count A.tab) (L.wert σ) (G.st σ) k.n :=
        hS.2.nicht_auf (fun j => A.stand σ ≤ j) (fun j hj => by have := hj.2.1; omega) (by omega)
      exact ih σ' (.cons k ρ) ⟨hok', ListOk.fremd A L G hf hmono hS.2⟩
        (StrukturPasst.ext_frei A L G k (StrukturPasst.fremd A L G hf hmono hP) hnew
          (fun hm => hnot ((auf_fremd A L G hf _).mp hm))
          (fun y hy e => by have := (hP.1 y hy).1.2.1; omega))
    · rw [frischAlloc_voll O passes R A v hwT hLT hwG hLG voll rest σ ρ hlt]
      exact Rein.post A L G O passes R hv _ _ ((Gleich.lese A L G σ Λ _).strukturOk A L G hS)
  | @nimm Γ Λ Λ' a a'' v hwT hLT hwK hLK voll rest hv h ih =>
    intro σ ρ hS hP
    by_cases hlt : A.kopfSt σ < D.count A.tab
    · obtain ⟨σ', k, he, hkn, hf, hok', hmono, hnew, hauf⟩ :=
        nimmAlloc_ausfuehren O passes R A v hwT hLT hwK hLK voll rest σ ρ hlt hS.1
      rw [he]
      apply StrukturPost.schrumpf
      have hnot : ¬ Auf (D.count A.tab) (L.wert σ) (G.st σ) k.n :=
        hS.2.nicht_auf (fun j => A.AufListe σ j) (fun j hj => hj.2.2) hauf
      exact ih σ' (.cons k ρ) ⟨hok', ListOk.fremd A L G hf hmono hS.2⟩
        (StrukturPasst.ext_frei A L G k (StrukturPasst.fremd A L G hf hmono hP) hnew
          (fun hm => hnot ((auf_fremd A L G hf _).mp hm))
          (fun y hy e => (hP.1 y hy).1.2.2 (by rw [e]; exact hauf)))
    · rw [nimmAlloc_voll O passes R A v hwT hLT hwK hLK voll rest σ ρ hlt]
      exact Rein.post A L G O passes R hv _ _ ((Gleich.lese A L G σ Λ _).strukturOk A L G hS)
  | @frei Γ Λ Λ' a a' x hwT hLT hwK hLK rest hx h ih =>
    intro σ ρ hS hP
    obtain ⟨hlebt, hnot⟩ := hP.1 x hx
    obtain ⟨σ', he, hf, hok', hmono, hdead⟩ := freiVar_lebt O passes R A x hwT hLT hwK hLK rest σ ρ hlebt hS.1
    rw [he]
    refine ih σ' ρ ⟨hok', ListOk.fremd_frei A L G hf _ hmono hnot hS.2⟩
      (StrukturPasst.set_offen A L G x.pos hP ?_ ?_)
    · intro y hy hyx
      have hne : (ρ.get y).n ≠ (ρ.get x).n := hP.2.2 y x hy hx hyx
      exact ⟨hmono _ (hP.1 y hy).1 hne, fun hm => (hP.1 y hy).2 ((auf_fremd A L G hf _).mp hm)⟩
    · intro y hy
      exact (auf_fremd A L G hf _).mpr (hP.2.1 y hy)
  | @wachs Γ Λ Λ' a a'' n hwK hLK voll rest hv h ih =>
    intro σ ρ hS hP
    by_cases hg : 0 ≤ A.komSt σ + n ∧ A.komSt σ + n ≤ D.count A.tab
    · obtain ⟨he, -, -, -⟩ := dynGrow_commit O passes R A.toDynForm n hwK hLK voll rest σ ρ hg.1 hg.2
      obtain ⟨hk, hn, hs, hL, hG⟩ := nachGrow_gleich A L G n Λ σ hg.1 hg.2
      have hgl : Gleich A L G σ (nachGrow A.toDynForm n Λ σ hg.1 hg.2) := ⟨hk, hn, hs, hL, hG⟩
      rw [he]
      apply StrukturPost.schrumpf
      exact ih _ _ (hgl.strukturOk A L G hS) (StrukturPasst.ext_offen A L G (hgl.passt A L G hP))
    · rw [dynGrow_voll O passes R A.toDynForm n hwK hLK voll rest σ ρ hg]
      exact Rein.post A L G O passes R hv _ _ ((Gleich.lese A L G σ Λ _).strukturOk A L G hS)
  | @pruefe Γ Λ Λ' a a' c voll rest hv h ih =>
    intro σ ρ hS hP
    have hgl := Gleich.lese A L G σ Λ c.orte
    simp only [execBlock]
    split
    · exact ih _ ρ (hgl.strukturOk A L G hS) (hgl.passt A L G hP)
    · exact Rein.post A L G O passes R hv _ _ (hgl.strukturOk A L G hS)
  | @nutzlast Γ Λ Λ' a a' i e hwT hLT rest h ih =>
    intro σ ρ hS hP
    obtain ⟨σ', hex, hgl⟩ : ∃ σ' : World D,
        execStmt O passes R (Stmt.assignSlot (l := l) A.tab A.feld i e hwT hLT) σ ρ = .ok σ' ρ ∧
        Gleich A L G σ σ' :=
      ⟨_, rfl, (Gleich.lese A L G σ Λ _).trans A L G (Gleich.nutzlast A L G _ Λ _ _)⟩
    refine StrukturPost.cons_stmt A L G O passes R (a := a) ?_ ih
    rw [hex]
    exact ⟨hgl.strukturOk A L G hS, hgl.passt A L G hP⟩
  | @ite Γ Λ Λ1 Λ' a a1 a2 a3 a' c t e rest ht he h1 h2 h iht ihe ih =>
    intro σ ρ hS hP
    have hgl := Gleich.lese A L G σ Λ c.orte
    refine StrukturPost.cons_stmt A L G O passes R (a := a3) ?_ ih
    simp only [execStmt]
    split
    · exact StrukturPost.schwacher A L G h1 (iht _ ρ (hgl.strukturOk A L G hS) (hgl.passt A L G hP))
    · exact StrukturPost.schwacher A L G h2 (ihe _ ρ (hgl.strukturOk A L G hS) (hgl.passt A L G hP))

/-- **A body that knows nothing at entry** (every position `offen`, as for parameters) keeps the structure invariant at
    every exit. -/
theorem erk_koerper {Γ : Ctx} {Λ Λ' : List (Res D)} {a' : Abs} {b : Block D V l Γ Λ Λ'}
    (h : Erk A L G Abs.leer b a') (σ : World D) (ρ : Env D Γ) (hS : StrukturOk A L G σ) :
    StrukturPost A L G a' (execBlock O passes R b σ ρ) :=
  erk_erhaelt O passes R A L G h σ ρ hS
    ⟨fun _ hx => absurd hx (by simp [Abs.leer]), fun _ hx => absurd hx (by simp [Abs.leer]),
      fun _ _ hx _ _ => absurd hx (by simp [Abs.leer])⟩

end Beweis

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.erk_erhaelt
#print axioms Gabbro.Grammatik.erk_koerper
